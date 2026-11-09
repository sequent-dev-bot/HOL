structure blastRule :> blastRule =
struct

open HolKernel boolSyntax blastTerm listUtil

infix 9 $
infix |->

type hol_term = Term.term
type thm = Thm.thm
type goal = Abbrev.goal
type pterm = blastTerm.term
type var = blastTerm.var

datatype origin =
    Stored of {is_elim : bool, theorem : thm}
  | ImpIntro
  | AllIntro

type tableau_rule =
  {origin : origin,
   pattern : pterm,
   premises : pterm list list,
   hidden_assumptions : int option list}

type monitor =
  {candidate : unit -> unit,
   conversion : unit -> unit,
   checkpoint : unit -> unit}

type entry =
  {formula : pterm,
   safe : bool,
   vars : var list,
   rules : tableau_rule list,
   stamp : int}

datatype head_tag =
    HAbs
  | HBound of int
  | HConst of KernelSig.kernelname
  | HFvar of string
  | HGoal
  | HFalse
  | HSkolem of string
  | HVar

type cache_key = bool * int * head_tag

fun head_tag_rank HAbs = 0
  | head_tag_rank (HBound _) = 1
  | head_tag_rank (HConst _) = 2
  | head_tag_rank (HFvar _) = 3
  | head_tag_rank HGoal = 4
  | head_tag_rank HFalse = 5
  | head_tag_rank (HSkolem _) = 6
  | head_tag_rank HVar = 7

fun head_tag_compare (left, right) =
  case Int.compare (head_tag_rank left, head_tag_rank right) of
      EQUAL =>
        (case (left, right) of
             (HBound i, HBound j) => Int.compare (i, j)
           | (HConst a, HConst b) => KernelSig.name_compare (a, b)
           | (HFvar a, HFvar b) => String.compare (a, b)
           | (HSkolem a, HSkolem b) => String.compare (a, b)
           | _ => EQUAL)
    | order => order

fun bool_compare (false, true) = LESS
  | bool_compare (true, false) = GREATER
  | bool_compare _ = EQUAL

fun cache_key_compare
      ((safe_left, vars_left, head_left),
       (safe_right, vars_right, head_right)) =
  case bool_compare (safe_left, safe_right) of
      EQUAL =>
        (case Int.compare (vars_left, vars_right) of
             EQUAL => head_tag_compare (head_left, head_right)
           | order => order)
    | order => order

fun stable_head_tag formula =
  case head_of formula of
      Const (name, _) => HConst name
    | Skolem (name, _) => HSkolem name
    | Fvar name => HFvar name
    | Goal => HGoal
    | False => HFalse
    | Var _ => HVar
    | Bound index => HBound index
    | Abs _ => HAbs
    | _ $ _ => raise Fail "blastRule.stable_head_tag"

(* A syntactic variable head is the only head whose [aconv] class can
   change after insertion.  Its stable key remains [HVar], while this
   helper identifies the additional concrete bucket that a lookup may
   have to inspect after the variable is assigned. *)
fun resolved_head_tag formula =
  case head_of formula of
      Var variable =>
        (case !variable of
             NONE => HVar
           | SOME assigned => resolved_head_tag assigned)
    | head => stable_head_tag head

fun cache_key safe vars formula =
  (safe, length vars, stable_head_tag formula)

fun containsZeroMeasured checkpoint =
  existsMeasured checkpoint (fn i => i = 0)

datatype cache = Cache of
  {entries : (cache_key, entry list) Redblackmap.dict ref,
   conversions : int ref,
   hits : int ref,
   next_stamp : int ref}

fun newCache () =
  Cache
    {entries = ref (Redblackmap.mkDict cache_key_compare),
     conversions = ref 0, hits = ref 0, next_stamp = ref 0}

fun conversionCount (Cache {conversions, ...}) = !conversions
fun hitCount (Cache {hits, ...}) = !hits

(* Skolem identity is name identity in blastTerm.  A session-global supply
   therefore prevents separate node caches from accidentally sharing one. *)
val skolem_names = ref 0

fun freshName _ prefix =
  (skolem_names := !skolem_names + 1;
   prefix ^ Int.toString (!skolem_names))

val blast_trace = ref 0
val _ = Feedback.register_trace ("blast", blast_trace, 7)

val generic_cache :
  (KernelSig.kernelname, hol_type * hol_type list) Redblackmap.dict ref =
  ref (Redblackmap.mkDict KernelSig.name_compare)

fun generic_info (name as {Thy, Name}) =
  case Redblackmap.peek (!generic_cache, name) of
      SOME info => info
    | NONE =>
        let
          val generic = type_of (prim_mk_const {Thy = Thy, Name = Name})
          val info = (generic, Type.type_vars generic)
        in
          generic_cache :=
            Redblackmap.insert (!generic_cache, name, info);
          info
        end

fun member_term_measured checkpoint tm =
  existsMeasured checkpoint (Term.aconv tm)

fun translatorMeasured checkpoint
      {rigid_types, goal_frees, rule_vars} =
  let
    val term_map : (hol_term, pterm) Redblackmap.dict ref =
      ref (Redblackmap.mkDict Term.compare)
    val type_map : (hol_type, pterm) Redblackmap.dict ref =
      ref (Redblackmap.mkDict Type.compare)

    fun encode_type ty =
      let
        val _ = checkpoint ()
      in
        if Type.is_vartype ty then
          if rigid_types then Fvar (Type.dest_vartype ty)
          else
            (case Redblackmap.peek (!type_map, ty) of
                 SOME value => value
               | NONE =>
                   let val value = Var (ref NONE)
                   in
                     type_map :=
                       Redblackmap.insert (!type_map, ty, value);
                     value
                   end)
        else
          let
            val {Thy, Tyop, Args} = Type.dest_thy_type ty
            val head = Const ({Thy = Thy, Name = Tyop}, [])
          in
            list_comb (head, mapMeasured checkpoint encode_type Args)
          end
      end

    fun generic {Thy, Name} =
      let
        val name = {Thy = Thy, Name = Name}
        val _ = checkpoint ()
      in
        case Redblackmap.peek (!generic_cache, name) of
            SOME info => info
          | NONE =>
              let
                val _ = checkpoint ()
                val generic =
                  type_of (prim_mk_const {Thy = Thy, Name = Name})
                val _ = checkpoint ()
                val info = (generic, Type.type_vars generic)
              in
                generic_cache :=
                  Redblackmap.insert (!generic_cache, name, info);
                info
              end
      end

    fun const_args hol_const =
      let
        val _ = checkpoint ()
        val {Thy, Name, Ty} = dest_thy_const hol_const
        val (generic_type, generic_vars) = generic {Thy = Thy, Name = Name}
        val _ = checkpoint ()
        val subst = Type.match_type generic_type Ty
      in
        mapMeasured checkpoint
          (encode_type o Type.type_subst subst) generic_vars
      end

    fun fresh_variable tm make =
      (checkpoint ();
       case Redblackmap.peek (!term_map, tm) of
           SOME value => value
         | NONE =>
             let val value = make ()
             in
               term_map := Redblackmap.insert (!term_map, tm, value);
               value
             end)

    fun variable depth bounds tm =
      (checkpoint ();
       case Redblackmap.peek (bounds, tm) of
           SOME binder_depth => Bound (depth - binder_depth)
         | NONE =>
             if member_term_measured checkpoint tm rule_vars then
               fresh_variable tm (fn () => Var (ref NONE))
             else if goal_frees then
               fresh_variable tm
                 (fn () => Skolem (freshName () "*Free*", []))
             else
               let val (name, _) = dest_var tm in Fvar name end)

    fun from depth bounds tm =
      let
        val _ = checkpoint ()
      in
        if is_const tm then
          let
            val {Thy, Name, ...} = dest_thy_const tm
            val args = const_args tm
          in
            Const ({Thy = Thy, Name = Name}, args)
          end
        else if is_var tm then variable depth bounds tm
        else if is_abs tm then
          let
            val (binder, body) = dest_abs tm
            val (name, _) = dest_var binder
            val body_depth = depth + 1
            val body_bounds =
              Redblackmap.insert (bounds, binder, body_depth)
            val body' = from body_depth body_bounds body
          in
            case body' of
                f $ Bound 0 =>
                  (checkpoint ();
                   if containsZeroMeasured checkpoint
                        (loose_bnos_measured checkpoint f) then
                     Abs (name, body')
                   else incr_boundvars_measured checkpoint ~1 f)
              | _ => Abs (name, body')
          end
        else
          let
            val (rator, argument) = dest_comb tm
            val rator' = from depth bounds rator
            val argument' = from depth bounds argument
          in
            rator' $ argument'
          end
      end
  in
    fn hol_term =>
      from 0 (Redblackmap.mkDict Term.compare) hol_term
  end

fun translator fields = translatorMeasured (fn () => ()) fields

(* [IN] is a boolTheory constant, [IN = \x f. f x], so [x IN P] and [P x] are
   one proposition.  A tableau cannot re-derive the crossing the way the
   classical engine does -- it compares pterms it has already built -- so the
   membership spelling is the form blast holds: everything that becomes a
   pterm crosses on the way in, goal and rule alike, and the two then meet.
   Membership is the stable spelling under instantiation: a set inside
   [x IN A] stays inside it however [A] is instantiated, where [A x] with [A]
   a set former is an atom no rule can see.  Reconstruction replays on the
   classical engine, which crosses wherever it compares two forms. *)
(* The goal is reduced on the way in, as it is when it enters the
   classical engine: blast holds pterms it has already crossed, so a
   redex the goal carried would otherwise stay in the branch with no
   step able to see past it.  [goal_reduce_conv] is the engines' shared
   normal form for a goal, which is what lets a branch blast closes be
   replayed by the classical engine. *)
fun crossed_with is_hole tm =
  boolSyntax.rhs
    (Thm.concl
      (Conv.THENC (clasetNorm.goal_reduce_conv,
                   clasetNorm.membership_conv_with is_hole)
        tm))

(* A goal carries no holes; a rule's schematic variables are its own. *)
fun crossed tm = crossed_with (fn _ => false) tm

fun fromGoalTerm tm =
  translator
    {rigid_types = true, goal_frees = true, rule_vars = []} tm

fun initialBranchMeasured checkpoint (assumptions, conclusion) =
  let
    val from =
      translatorMeasured checkpoint
        {rigid_types = true, goal_frees = true, rule_vars = []}
    val _ = checkpoint ()
    val conclusion' = from (crossed conclusion)
  in
    mkGoal conclusion' ::
      mapMeasured checkpoint (fn formula => from (crossed formula))
        assumptions
  end

fun initialBranch goal = initialBranchMeasured (fn () => ()) goal

fun proto_imp term =
  case strip_comb term of
      (Const (name, _), [left, right]) =>
        if name = {Thy = "min", Name = "==>"}
        then SOME (left, right)
        else NONE
    | _ => NONE

fun dest_forall_body term =
  case strip_comb term of
      (Const (name, _), [predicate]) =>
        if name = {Thy = "bool", Name = "!"}
        then SOME predicate
        else NONE
    | _ => NONE

fun apply_predicate_measured checkpoint predicate argument =
  (checkpoint ();
   case predicate of
       Abs (_, body) => subst_bound_measured checkpoint (argument, body)
     | _ => predicate $ argument)

fun skoPremMeasured checkpoint cache vars term =
  (checkpoint ();
   case dest_forall_body term of
       SOME predicate =>
         let
           val skolem = Skolem (freshName cache "S", vars)
           val _ = checkpoint ()
           val body = apply_predicate_measured checkpoint predicate skolem
         in
           skoPremMeasured checkpoint cache vars body
         end
     | NONE => term)

fun convertPremMeasured checkpoint term =
  let
    fun strip formula =
      (checkpoint ();
       case proto_imp formula of
           SOME (premise, rest) =>
             let val (hypotheses, conclusion) = strip rest
             in (premise :: hypotheses, conclusion) end
         | NONE => ([], formula))
    val (hypotheses, conclusion) = strip term
  in
    mkGoal conclusion :: hypotheses
  end

exception ElimBadConcl
exception ElimBadPrem

fun is_false_var term =
  case term of
      Var v =>
        (case !v of
             SOME False => true
           | _ => false)
    | _ => false

fun compute_canonical_data checkpoint is_elim theorem =
  let
    val kind = if is_elim then clasetRules.Elim else clasetRules.Intro
    val form =
      clasetRules.canonical_form_of_measured checkpoint kind theorem
    fun outer_vars tm =
      (checkpoint ();
       case total dest_forall tm of
           NONE => []
         | SOME (variable, body) => variable :: outer_vars body)
    val outer = outer_vars (concl (#thm form))
    (* A rule variable in head position is a hole, not a set: [?P x] is how
       the tableau asks for a predicate, and a membership there would leave a
       first-order problem no instantiation can solve. *)
    fun hole variable = boolSyntax.tmem variable outer
    val cross = crossed_with hole
    val from =
      translatorMeasured checkpoint
        {rigid_types = false, goal_frees = false, rule_vars = outer}
    val premises =
      mapMeasured checkpoint (from o cross) (#prems form)
    val _ = checkpoint ()
    val conclusion = from (cross (#concl form))
  in
    {outer = outer, hol_conclusion = #concl form,
     premises = premises, conclusion = conclusion}
  end

(* The HOL side of a rule's conversion -- the canonical form, the
   membership crossing and the translation into prototerms -- is a
   function of the rule's statement, and a search meets the same rule
   again at every branch whose atom it indexes.  Isabelle rebuilds a rule
   from [Thm.prop_of] with no kernel inference (blast.ML:503); this port
   derives a canonical form and runs two conversions, which is affordable
   once for a rule and not once for an acquisition.  The memo is keyed on
   the statement because that is all the conversion reads, and every
   retrieval copies: the prototerms carry the mutable cells unification
   assigns, and the stored one must stay pristine. *)
type canonical_data =
  {outer : hol_term list,
   hol_conclusion : hol_term,
   premises : pterm list,
   conclusion : pterm}

val canonical_memo :
  (bool * hol_term, canonical_data) Redblackmap.dict ref =
  ref (Redblackmap.mkDict
         (Portable.pair_compare (bool_compare, Term.compare)))

fun copy_canonical checkpoint
      ({outer, hol_conclusion, premises, conclusion} : canonical_data) =
  let
    val copies = ref ([] : (var * var) list)

    fun copy_variable variable =
      (checkpoint ();
       case findMeasured checkpoint
              (fn (source, _) => source = variable) (!copies) of
           SOME (_, copy) => copy
         | NONE =>
             let
               val copy = ref NONE
               val _ = copies := (variable, copy) :: !copies
               val _ =
                 case !variable of
                     NONE => ()
                   | SOME term => copy := SOME (copy_term term)
             in
               copy
             end)

    and copy_term term =
      (checkpoint ();
       case term of
           Const (name, args) =>
             Const (name, mapMeasured checkpoint copy_term args)
         | Skolem (name, arguments) =>
             Skolem (name, mapMeasured checkpoint copy_variable arguments)
         | Fvar name => Fvar name
         | Goal => Goal
         | False => False
         | Var variable => Var (copy_variable variable)
         | Bound index => Bound index
         | Abs (name, body) => Abs (name, copy_term body)
         | left $ right => copy_term left $ copy_term right)
  in
    {outer = outer, hol_conclusion = hol_conclusion,
     premises = mapMeasured checkpoint copy_term premises,
     conclusion = copy_term conclusion}
  end

(* A rule carrying hypotheses is not a statement the memo can key on, and
   a claset rule never has any; it is converted afresh. *)
fun canonical_dataMeasured checkpoint is_elim theorem =
  if not (List.null (Thm.hyp theorem)) then
    compute_canonical_data checkpoint is_elim theorem
  else
    let
      val key = (is_elim, Thm.concl theorem)
      val _ = checkpoint ()
    in
      case Redblackmap.peek (!canonical_memo, key) of
          SOME data => copy_canonical checkpoint data
        | NONE =>
            let
              val data = compute_canonical_data checkpoint is_elim theorem
              val stored = copy_canonical checkpoint data
            in
              canonical_memo :=
                Redblackmap.insert (!canonical_memo, key, stored);
              data
            end
    end

fun countConversion (Cache {conversions, ...}) =
  conversions := !conversions + 1

fun convertIntroMeasured checkpoint cache vars theorem =
  let
    val _ = countConversion cache
    val {premises, conclusion, ...} =
      canonical_dataMeasured checkpoint false theorem
    fun convert premise =
      convertPremMeasured checkpoint
        (skoPremMeasured checkpoint cache vars premise)
  in
    {origin = Stored {is_elim = false, theorem = theorem},
     pattern = mkGoal conclusion,
     premises = mapMeasured checkpoint convert premises,
     hidden_assumptions = mapMeasured checkpoint (fn _ => NONE) premises}
  end

fun convertIntro cache vars theorem =
  convertIntroMeasured (fn () => ()) cache vars theorem

fun weak_warning theorem =
  if Feedback.current_trace "blast" >= 1 then
    HOL_WARNING "blastRule" "convertElim"
      ("Ignoring weak elimination rule\n" ^ Parse.thm_to_string theorem)
  else ()

fun bad_conclusion_message theorem =
  "Ignoring ill-formed elimination rule:\n" ^
  "conclusion should be a variable\n" ^ Parse.thm_to_string theorem

fun delete_concl_measured_from checkpoint _ [] =
      (checkpoint (); raise ElimBadPrem)
  | delete_concl_measured_from checkpoint assumption_index
      (formula :: formulas) =
      (checkpoint ();
       case formula of
           Goal $ value =>
             if is_false_var value then (formulas, NONE)
             else
               let
                 val (remaining, hidden) =
                   delete_concl_measured_from checkpoint
                     assumption_index formulas
               in
                 (formula :: remaining, hidden)
               end
         | Const ({Thy = "bool", Name = "~"}, _) $ value =>
             if is_false_var value then
               (formulas, SOME assumption_index)
             else
               let
                 val (remaining, hidden) =
                   delete_concl_measured_from checkpoint
                     (assumption_index + 1) formulas
               in
                 (formula :: remaining, hidden)
               end
         | _ =>
             let
               val (remaining, hidden) =
                 delete_concl_measured_from checkpoint
                   (assumption_index + 1) formulas
             in
               (formula :: remaining, hidden)
             end)

fun delete_concl_measured checkpoint formulas =
  delete_concl_measured_from checkpoint 0 formulas

fun convertElimMeasured checkpoint cache vars theorem =
  let
    val _ = countConversion cache
    val data = canonical_dataMeasured checkpoint true theorem
    val outer = #outer data
    val hol_conclusion = #hol_conclusion data
    val premises = #premises data
    val conclusion = #conclusion data
    val _ = checkpoint ()
    val formula_variable =
      is_var hol_conclusion andalso
      type_of hol_conclusion = bool andalso
      member_term_measured checkpoint hol_conclusion outer
    val _ = if formula_variable then () else raise ElimBadConcl
    val false_var =
      case conclusion of
          Var variable => variable
        | _ => raise ElimBadConcl
    val (major, minors) =
      case premises of
          premise :: rest => (premise, rest)
        | [] => raise ElimBadConcl
    val _ = false_var := SOME False
    fun convert premise =
      delete_concl_measured checkpoint
        (convertPremMeasured checkpoint
           (skoPremMeasured checkpoint cache vars premise))
  in
    let val converted = mapMeasured checkpoint convert minors
    in SOME
      {origin = Stored {is_elim = true, theorem = theorem},
       pattern = major,
       premises = mapMeasured checkpoint #1 converted,
       hidden_assumptions = mapMeasured checkpoint #2 converted}
    end
  end
  handle ElimBadPrem => (weak_warning theorem; NONE)
       | ElimBadConcl =>
           (if Feedback.current_trace "blast" >= 1 then
              Feedback.HOL_MESG (bad_conclusion_message theorem)
            else ();
            NONE)

fun convertElim cache vars theorem =
  convertElimMeasured (fn () => ()) cache vars theorem

fun bucket entries key =
  case Redblackmap.peek (entries, key) of
      NONE => []
    | SOME values => values

fun lookup_keys safe vars formula =
  let
    val count = length vars
    val stable = stable_head_tag formula
    val primary = (safe, count, stable)
    val variable = (safe, count, HVar)
  in
    case stable of
        HVar =>
          (case resolved_head_tag formula of
               HVar => (primary, NONE)
             | resolved => (primary, SOME (safe, count, resolved)))
      | _ => (primary, SOME variable)
  end

fun newest (NONE, right) = right
  | newest (left, NONE) = left
  | newest (left as SOME first, right as SOME second) =
      if #stamp first > #stamp second then left else right

fun find_cached find entries safe vars formula =
  let
    val (primary, fallback) = lookup_keys safe vars formula
    val first = find (bucket entries primary)
    val second =
      case fallback of
          NONE => NONE
        | SOME key => find (bucket entries key)
  in
    newest (first, second)
  end

fun cachedMeasured checkpoint (Cache {entries, hits, ...})
      safe vars formula =
  let
    fun same ([], []) = true
      | same (left :: lefts, right :: rights) =
          (checkpoint ();
           left = right andalso same (lefts, rights))
      | same _ = false
    fun matches entry =
      #safe entry = safe andalso
      same (#vars entry, vars) andalso
      aconvMeasured checkpoint (#formula entry, formula)
    val find = findMeasured checkpoint matches
  in
    (* Red-black lookup itself is indivisible.  Poll once for every member
       of the selected head bucket (and the variable-head fallback), rather
       than once for every entry in the whole search cache. *)
    case find_cached find (!entries) safe vars formula of
        NONE => NONE
      | SOME entry =>
          (hits := !hits + 1;
           SOME (#rules entry))
  end

fun remember (Cache {entries, next_stamp, ...}) safe vars formula rules =
  let
    val key = cache_key safe vars formula
    val stamp = !next_stamp
    val entry =
      {formula = formula, safe = safe, vars = vars, rules = rules,
       stamp = stamp}
    val values = bucket (!entries) key
  in
    next_stamp := stamp + 1;
    entries := Redblackmap.insert (!entries, key, entry :: values)
  end

fun query_skeleton_measured checkpoint formula =
  let
    val goal = isGoal formula
    val body = if goal then rand formula else formula
    val depth = if goal then 2 else 3
    val decoded = ref []
    val variables = ref []
    val qvars = ref Term.empty_tmset

    fun strip term =
      let
        fun collect (left $ right, args) =
              (checkpoint (); collect (left, right :: args))
          | collect result = (checkpoint (); result)
      in
        collect (term, [])
      end

    fun find_decoded variable entries =
      Option.map #2
        (findMeasured checkpoint (fn (key, _) => key = variable) entries)

    fun decode term =
      (checkpoint ();
       case term of
           Fvar name => Type.mk_vartype name
         | Var variable =>
             (case !variable of
                  SOME value => decode value
                | NONE =>
                    (case find_decoded variable (!decoded) of
                         SOME ty => ty
                       | NONE =>
                           let val ty = Type.gen_tyvar ()
                           in
                             decoded := (variable, ty) :: !decoded;
                             ty
                           end))
         | _ =>
             let
               val (head, args) = strip term
             in
               case head of
                   Const ({Thy, Name}, []) =>
                     Type.mk_thy_type
                       {Thy = Thy, Tyop = Name,
                        Args = mapMeasured checkpoint decode args}
                 | _ => Type.gen_tyvar ()
             end)

    fun constant (name, proto_args) =
      (checkpoint ();
       let
         val (generic, generic_vars) = generic_info name
               fun substitutions ([], []) = []
                 | substitutions (variable :: variables, arg :: args) =
                     (checkpoint ();
                      (variable |-> decode arg) ::
                        substitutions (variables, args))
                 | substitutions _ = []
               val subst = substitutions (generic_vars, proto_args)
               val _ = checkpoint ()
         in
           mk_thy_const
             {Thy = #Thy name, Name = #Name name,
              Ty = Type.type_subst subst generic}
         end)

    fun unknown track expected term =
      case #1 (strip term) of
          Var variable =>
            if not track then genvar expected
            else
              (case findMeasured checkpoint
                 (fn (key, tm) => key = variable andalso
                   type_of tm = expected) (!variables) of
                   SOME (_, tm) => tm
                 | NONE =>
                     let val tm = genvar expected
                     in
                       variables := (variable, tm) :: !variables;
                       qvars := HOLset.add (!qvars, tm);
                       tm
                     end)
        | _ => genvar expected

    fun build track expected 0 term =
          (checkpoint (); unknown track expected term)
      | build track expected level term =
          (checkpoint ();
           (case strip term of
                (Const (name, proto_args), actual_args) =>
                  let
                    fun apply (head, []) = head
                      | apply (head, arg :: args) =
                          let
                            val _ = checkpoint ()
                            val (domain, _) = Type.dom_rng (type_of head)
                            val arg' = build track domain (level - 1) arg
                            val _ = checkpoint ()
                          in
                            apply (mk_comb (head, arg'), args)
                          end
                    val result =
                      apply (constant (name, proto_args), actual_args)
                    val _ = checkpoint ()
                  in
                    if type_of result = expected then result
                    else genvar expected
                  end
              | _ => unknown track expected term)
           handle HOL_ERR _ => genvar expected)
  in
    let
      val static = build false bool depth body
      val query = build true bool depth (blastTerm.normMeasured checkpoint body)
    in
      (static, {q = query, qvars = !qvars})
    end
  end

fun pseudoRulesMeasured checkpoint cache vars formula =
  if not (isGoal formula) then []
  else
    let
      val _ = checkpoint ()
      val body = rand formula
    in
      case proto_imp body of
          SOME (premise, conclusion) =>
            [{origin = ImpIntro, pattern = formula,
              premises = [[mkGoal conclusion, premise]],
              hidden_assumptions = [NONE]}]
        | NONE =>
            (checkpoint ();
             case dest_forall_body body of
                 SOME predicate =>
                   let
                     val skolem = Skolem (freshName cache "S", vars)
                     val _ = checkpoint ()
                     val applied =
                       apply_predicate_measured checkpoint predicate skolem
                   in
                     [{origin = AllIntro, pattern = formula,
                       premises = [[mkGoal applied]],
                       hidden_assumptions = [NONE]}]
                   end
               | NONE => [])
    end

fun isVarForm (Var _) = true
  | isVarForm (Const (name, _) $ Var _) =
      name = {Thy = "bool", Name = "~"}
  | isVarForm _ = false

fun candidatesMeasured ({checkpoint, ...} : monitor) claset safe formula =
  if not (isGoal formula) andalso isVarForm formula then []
  else
    let
      val (query, distinct_query) =
        query_skeleton_measured checkpoint formula
      fun intros part =
        clasetLib.unify_intro_candidates_measured checkpoint part query
      fun elims part =
        clasetLib.unify_elim_candidates_with checkpoint part query
          distinct_query
      val tagged =
        if safe then
          if isGoal formula then
            appendMeasured checkpoint
              (intros (clasetLib.safe0_part claset))
              (intros (clasetLib.safep_part claset))
          else
            appendMeasured checkpoint
              (elims (clasetLib.safe0_part claset))
              (elims (clasetLib.safep_part claset))
        else if isGoal formula then
          intros (clasetLib.unsafe_part claset)
        else elims (clasetLib.unsafe_part claset)
    in
      clasetRules.candidate_order_measured checkpoint tagged
    end

(* Rule variables are assigned destructively and off-trail by unify.  Keep
   pristine templates in a search cache, and give every acquisition fresh
   rule variables and fresh rule-local Skolems.  Variables and Skolems from
   the branch formula remain shared with the branch. *)
fun copyRulesWith checkpoint
      cache vars formula fresh_skolems rules =
  let
    val variable_copies = ref ([] : (var * var) list)
    val skolem_copies = ref ([] : (string * string) list)

    fun string_member value =
      existsMeasured checkpoint (fn other => value = other)

    fun variable_member value =
      existsMeasured checkpoint (fn other => value = other)

    fun insert_string value values =
      if string_member value values then values else value :: values

    fun find_variable variable entries =
      Option.map #2
        (findMeasured checkpoint
           (fn (source, _) => source = variable) entries)

    fun find_skolem name entries =
      Option.map #2
        (findMeasured checkpoint (fn (source, _) => source = name) entries)

    fun add_skolems term names =
      let
        val _ = checkpoint ()
      in
        case term of
            Const (_, args) =>
              fold_terms args names
          | Skolem (name, arguments) =>
              fold_vars arguments (insert_string name names)
          | Var variable =>
              (case !variable of
                   NONE => names
                 | SOME item => add_skolems item names)
          | Abs (_, body) => add_skolems body names
          | left $ right => add_skolems left (add_skolems right names)
          | _ => names
      end

    and fold_terms items names =
      List.foldl
        (fn (item, result) =>
           (checkpoint (); add_skolems item result)) names items

    and fold_vars variables names =
      List.foldl
        (fn (variable, result) =>
           (checkpoint ();
            case !variable of
                NONE => result
              | SOME item => add_skolems item result)) names variables

    val external_skolems =
      List.foldl
        (fn (variable, names) =>
           (checkpoint ();
            case !variable of
                NONE => names
              | SOME term => add_skolems term names))
        (add_skolems formula []) vars

    fun copy_variable variable =
      (checkpoint ();
       if variable_member variable vars then variable
       else
         case find_variable variable (!variable_copies) of
             SOME copy => copy
           | NONE =>
               let
                 val copy = ref NONE
                 val _ =
                   variable_copies :=
                     (variable, copy) :: !variable_copies
                 val _ =
                   case !variable of
                       NONE => ()
                     | SOME term => copy := SOME (copy_term term)
               in
                 copy
               end)

    and copy_skolem name =
      (checkpoint ();
       if not fresh_skolems orelse
          string_member name external_skolems
       then name
       else
         case find_skolem name (!skolem_copies) of
             SOME copy => copy
           | NONE =>
               let
                 val copy = freshName cache "S"
               in
                 skolem_copies := (name, copy) :: !skolem_copies;
                 copy
               end)

    and copy_term term =
      (checkpoint ();
       case term of
           Const (name, args) => Const (name, copy_terms args)
         | Skolem (name, arguments) =>
             Skolem (copy_skolem name, copy_variables arguments)
         | Fvar name => Fvar name
         | Goal => Goal
         | False => False
         | Var variable => Var (copy_variable variable)
         | Bound index => Bound index
         | Abs (name, body) => Abs (name, copy_term body)
         | left $ right => copy_term left $ copy_term right)

    and copy_terms terms = mapMeasured checkpoint copy_term terms

    and copy_variables variables =
      mapMeasured checkpoint copy_variable variables

    fun copy_premise terms = mapMeasured checkpoint copy_term terms

    fun copy_premises premises =
      mapMeasured checkpoint copy_premise premises

    fun copy_rule
          ({origin, pattern, premises, hidden_assumptions} : tableau_rule) =
      (checkpoint ();
       {origin = origin,
        pattern = copy_term pattern,
        premises = copy_premises premises,
        hidden_assumptions = hidden_assumptions})
  in
    mapMeasured checkpoint copy_rule rules
  end

fun acquireMeasured (monitor as {candidate, conversion, checkpoint})
      cache claset safe vars formula =
  case cachedMeasured checkpoint cache safe vars formula of
      SOME rules =>
        copyRulesWith checkpoint cache vars formula true rules
    | NONE =>
        let
          val tagged = candidatesMeasured monitor claset safe formula
          val _ = appMeasured checkpoint (fn _ => candidate ()) tagged
          fun convert (_, (is_elim, theorem)) =
            let
              val _ = checkpoint ()
              val _ = conversion ()
              val result =
                if is_elim then
                  convertElimMeasured checkpoint cache vars theorem
                else
                  SOME
                    (convertIntroMeasured checkpoint cache vars theorem)
            in
              result
            end
          fun weight_at_most_one ({weight, ...} : clasetRules.tag, _) =
            weight <= 1
          val (early, late) =
            partitionMeasured checkpoint weight_at_most_one tagged
          val early_rules = mapPartialMeasured checkpoint convert early
          val late_rules = mapPartialMeasured checkpoint convert late
          val rules =
            if safe then
              appendMeasured checkpoint early_rules
                (appendMeasured checkpoint
                   (pseudoRulesMeasured checkpoint cache vars formula)
                   late_rules)
            else appendMeasured checkpoint early_rules late_rules
          val _ = checkpoint ()
          val templates =
            copyRulesWith checkpoint cache vars formula false rules
          val _ = remember cache safe vars formula templates
        in
          rules
        end

fun acquire cache claset safe vars formula =
  acquireMeasured
    {candidate = fn () => (), conversion = fn () => (),
     checkpoint = fn () => ()}
    cache claset safe vars formula

fun safeRules cache claset vars formula =
  acquire cache claset true vars formula

fun unsafeRules cache claset vars formula =
  acquire cache claset false vars formula

fun safeRulesMeasured monitor cache claset vars formula =
  acquireMeasured monitor cache claset true vars formula

fun unsafeRulesMeasured monitor cache claset vars formula =
  acquireMeasured monitor cache claset false vars formula

(* The tableau premises are the stored rule's minor premises: conversion
   takes the major premise of an elimination out of the list and leaves it
   as the rule's pattern.  A rotation of the premises therefore fixes the
   elimination's major premise and permutes the rest. *)
fun rotate index items =
  List.drop (items, index) @ List.take (items, index)

fun rotatePremises index
      (rule as {origin, pattern, premises, hidden_assumptions}
         : tableau_rule) =
  if index = 0 then SOME rule
  else
    case origin of
        Stored {is_elim, theorem} =>
          let
            val kind = if is_elim then clasetRules.Elim else clasetRules.Intro
            val minors = List.length premises
            val offset = if is_elim then 1 else 0
            val order =
              List.tabulate (offset, fn position => position) @
              map (fn position => position + offset)
                (rotate index (List.tabulate (minors, fn p => p)))
          in
            SOME
              {origin =
                 Stored
                   {is_elim = is_elim,
                    theorem =
                      clasetRules.PERMUTE_PREMISES_RULE kind order theorem},
               pattern = pattern,
               premises = rotate index premises,
               hidden_assumptions = rotate index hidden_assumptions}
          end
      | _ => NONE

fun replayTheorem
      ({origin = Stored {is_elim, theorem}, ...} : tableau_rule) dup =
      if dup andalso is_elim then
        SOME (clasetRules.REV_DUP_ELIM_RULE theorem)
      else SOME theorem
  | replayTheorem _ _ = NONE

end
