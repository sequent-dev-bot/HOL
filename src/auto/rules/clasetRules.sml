structure clasetRules :> clasetRules =
struct

open HolKernel boolSyntax

type term = Term.term
type thm = Thm.thm
type thname = KernelSig.kernelname

datatype rulekind = Intro | Elim | Dest | Forward | Norm
type rulespec = {kind : rulekind, safe : bool, prio : int option}
type tag = {weight : int, index : int}
type brl = bool * thm
type rl = thm * thm option
type info = {rl : rl, dup_rl : rl}
type decl =
  {name : string, spec : rulespec, tag : tag, info : info, orig : thm}

type canonical =
  {thm : thm, patvars : term HOLset.set, prems : term list, concl : term}

datatype spine_exemption = ExemptNone | ExemptFirst | ExemptLast

fun exemption_of (Intro | Norm) = ExemptNone
  | exemption_of (Elim | Dest) = ExemptFirst
  | exemption_of Forward = ExemptLast

fun next_exemption ExemptFirst = ExemptNone
  | next_exemption exemption = exemption

fun premise_exempt ExemptFirst _ = true
  | premise_exempt ExemptLast rest = not (is_imp_only rest)
  | premise_exempt ExemptNone _ = false

(* Keep explicit negations opaque: dest_imp also treats ~P as P ==> F. *)
fun undisch th =
  MP th (ASSUME (fst (dest_imp_only (concl th))))

(* Intro and Norm curry every premise, Elim and Dest preserve the first
   (major) premise, and Forward preserves the last.  Keeping that choice as
   data avoids a new copy of the traversal for every rule kind. *)
fun curry_spine checkpoint exemption th =
  (checkpoint ();
   case total dest_imp_only (concl th) of
       NONE => th
     | SOME (prem, rest) =>
         if premise_exempt exemption rest then
           (case exemption of
                ExemptLast => th
              | _ =>
                  DISCH prem
                    (curry_spine checkpoint (next_exemption exemption)
                       (undisch th)))
         else if is_conj prem then
           let
             val (left, right) = dest_conj prem
             val curry =
               SYM (Drule.SPECL [left, right, rest]
                      boolTheory.AND_IMP_INTRO)
           in
             curry_spine checkpoint exemption (EQ_MP curry th)
           end
         else
           DISCH prem
             (curry_spine checkpoint (next_exemption exemption)
                (undisch th)))

fun has_canonical_premises checkpoint exemption tm =
  (checkpoint ();
   case total dest_imp_only tm of
       NONE => true
     | SOME (prem, rest) =>
         (premise_exempt exemption rest orelse not (is_conj prem)) andalso
         has_canonical_premises checkpoint (next_exemption exemption) rest)

fun is_canonical checkpoint exemption th =
  let
    val _ = checkpoint ()
    val (_, body) = strip_forall (concl th)
  in
    has_canonical_premises checkpoint exemption body
  end

(* A quantified variable may also occur free in a theorem hypothesis (the
   quantifier then shadows that free variable in the conclusion).  Such a
   theorem is valid, but specializing and later generalizing with the
   stripped binder itself would make GEN reject the free hypothesis. *)
fun fresh_forall_vars_with checkpoint th vars =
  let
    val _ = checkpoint ()
    val avoids = free_varsl (hyp th)
    fun freshen _ [] = []
      | freshen avoid (v :: vs) =
          let
            val _ = checkpoint ()
            val v' = variant avoid v
          in
            v' :: freshen (v' :: avoid) vs
          end
  in
    freshen avoids vars
  end

(* Isabelle stores a rule's parameters as schematic variables; HOL4 states
   them free, and a free variable is universally quantifiable whenever no
   hypothesis pins it.  [form_of] draws its pattern variables from the outer
   binders alone, so a parameter left free is rigid: the rule then matches
   nothing but a goal spelling that parameter by the same name.  Bind them. *)
fun generalise_parameters checkpoint th =
  let
    val _ = checkpoint ()
    val (bound, body) = strip_forall (concl th)
    val pinned = bound @ free_varsl (hyp th)
    val rigid =
      List.filter (fn v => not (tmem v pinned)) (free_vars body)
    val _ = checkpoint ()
  in
    if List.null rigid then th else GENL rigid th
  end

(* An Isabelle rule never quantifies the subject its conclusion is about:
   a stored theorem is in hhf normal form, so what the source writes as a
   meta-bound conclusion variable is schematic, and the rule's index is an
   atom.  HOL4 has no meta level and states the same rule with an object
   binder -- [option_induction] is [P NONE /\ (!a. P (SOME a)) ==> !x. P x]
   against Isabelle's [option.induct], whose conclusion is [?P ?option].
   Read as a rule, the binder makes the index a universal formula, which
   the atomic goal the rule exists to close never meets.  This is not a
   normalisation the claset may apply on its own: for an ambient rule whose
   conclusion is a bare pattern application the atomised index matches every
   goal, which is precisely why Isabelle keeps such rules out of its own
   claset and passes them per call.  So the operation is offered, not
   imposed -- a caller that knows a HOL4 theorem stands for an hhf-normal
   Isabelle one asks for it by name. *)

fun undisch_spine checkpoint th =
  (checkpoint ();
   case total dest_imp_only (concl th) of
       NONE => ([], th)
     | SOME (prem, _) =>
         let val (rest, core) = undisch_spine checkpoint (undisch th)
         in (prem :: rest, core) end)

(* [th] carries no outer binder; the result is the same rule with every
   conclusion binder specialized, and the variables it took. *)
fun atomise_body checkpoint th =
  let
    fun step th taken =
      let
        val _ = checkpoint ()
        val (prems, core) = undisch_spine checkpoint th
      in
        if not (is_forall (concl core)) then (th, List.rev taken)
        else
          let
            val (bound, _) = strip_forall (concl core)
            val avoids = free_varsl (concl th :: hyp th) @ taken
            fun freshen _ [] = []
              | freshen avoid (variable :: rest) =
                  let
                    val _ = checkpoint ()
                    val variable' = variant avoid variable
                  in
                    variable' :: freshen (variable' :: avoid) rest
                  end
            val fresh = freshen avoids bound
            val atom = Drule.SPECL fresh core
            val restored =
              List.foldr (fn (prem, th') => DISCH prem th') atom prems
          in
            step restored (List.rev fresh @ taken)
          end
      end
  in
    step th []
  end

fun canonical_rule_with checkpoint exemption th0 =
  let
    val th = generalise_parameters checkpoint th0
  in
    if is_canonical checkpoint exemption th then th
    else
      let
        val _ = checkpoint ()
        val (vars, _) = strip_forall (concl th)
        val vars' = fresh_forall_vars_with checkpoint th vars
        val _ = checkpoint ()
        val body = Drule.SPECL vars' th
        val body' = curry_spine checkpoint exemption body
        val _ = checkpoint ()
      in
        GENL vars' body'
      end
  end

(* The binder belongs to the conclusion alone, so no premise mentions it,
   and taking it as one of the rule's own binders is the same rule with the
   subject a pattern variable.  A conclusion the move exposes as an
   implication becomes one more premise, as it is in the source. *)
fun atomise_conclusion_with checkpoint th =
  let
    val _ = checkpoint ()
    val (vars, _) = strip_forall (concl th)
    val vars' = fresh_forall_vars_with checkpoint th vars
    val _ = checkpoint ()
    val body = Drule.SPECL vars' th
    val (atomised, subjects) = atomise_body checkpoint body
    val _ = checkpoint ()
  in
    GENL (vars' @ subjects) atomised
  end

fun canonical_rule_of_with checkpoint kind =
  canonical_rule_with checkpoint (exemption_of kind)

fun form_of checkpoint th' =
  let
    val _ = checkpoint ()
    val (vars, body) = strip_forall (concl th')
    val _ = checkpoint ()
    val (prems, cncl) = strip_imp_only body
    val _ = checkpoint ()
  in
    {thm = th', patvars = HOLset.fromList Term.compare vars,
     prems = prems, concl = cncl}
  end

fun canonical_form_of_measured checkpoint kind th =
  form_of checkpoint (canonical_rule_of_with checkpoint kind th)

val no_checkpoint = listUtil.no_checkpoint

fun fresh_forall_vars th vars =
  fresh_forall_vars_with no_checkpoint th vars

val atomise_conclusion = atomise_conclusion_with no_checkpoint

val canonical_rule = canonical_rule_of_with no_checkpoint Intro

fun canonical_rule_of kind = canonical_rule_of_with no_checkpoint kind

fun canonical_form th = form_of no_checkpoint (canonical_rule th)

fun canonical_form_of kind th =
  canonical_form_of_measured no_checkpoint kind th

fun rule_premises_of kind th = #prems (canonical_form_of kind th)

fun kind_name Intro = "introduction"
  | kind_name Elim = "elimination"
  | kind_name Dest = "destruction"
  | kind_name Forward = "forward"
  | kind_name Norm = "normalisation"

fun illformed_rule fname kind =
  raise mk_HOL_ERR "clasetRules" fname
    ("Ill-formed " ^ kind_name kind ^ " rule")

fun rule_index_of (Intro | Norm) (form : canonical) = #concl form
  | rule_index_of (kind as (Elim | Dest)) form =
      (case #prems form of
          prem :: _ => prem
        | [] => illformed_rule "rule_index" kind)
  | rule_index_of (kind as Forward) form =
      (case #prems form of
          [] => illformed_rule "rule_index" kind
        | prems => List.last prems)

fun rule_index kind th = rule_index_of kind (canonical_form_of kind th)

(* The derived rules below operate on this outer spine only.  In
   particular, a premise such as !x. P x ==> q is always one premise. *)
fun rule_spine_with canonicalize th =
  let
    val th' = canonicalize th
    val (vars, _) = strip_forall (concl th')
    val vars' = fresh_forall_vars th' vars
    val core = Drule.SPECL vars' th'
    val (prems, cncl) = strip_imp_only (concl core)
  in
    {thm = th', vars = vars', core = core, prems = prems, concl = cncl}
  end

val rule_spine = rule_spine_with canonical_rule
val elim_rule_spine = rule_spine_with (canonical_rule_of Elim)

fun apply_assumed th prems = Drule.LIST_MP (map ASSUME prems) th

fun apply_thms th prems = Drule.LIST_MP prems th

fun discharge_prems prems th = Lib.itlist DISCH prems th

fun finish_rule vars extras prems th =
  GENL (vars @ extras) (discharge_prems prems th)

fun fresh_bool th =
  variant (free_varsl (concl th :: hyp th)) (mk_var ("r", bool))

fun false_of not_tm tm_th = MP (NOT_ELIM not_tm) tm_th

fun MAKE_ELIM_RULE th =
  let
    val {vars, core, prems, concl, ...} = elim_rule_spine th
    val r = fresh_bool core
    val br = mk_imp (concl, r)
    val bth = apply_assumed core prems
    val rth = MP (ASSUME br) bth
  in
    finish_rule vars [r] (prems @ [br]) rth
  end

fun CLASSICAL_RULE th =
  let
    val {thm, vars, core, prems, concl, ...} = elim_rule_spine th
  in
    case prems of
        [] => illformed_rule "CLASSICAL_RULE" Elim
      | major :: rest =>
          if not (is_var concl) then thm
          else
            let
              (* A premise's conclusion sits under its parameters as well
                 as under its own antecedents, and the negation adds
                 nothing to a premise that already concludes the rule's
                 conclusion or already assumes it. *)
              val negation = mk_neg concl
              fun strip_assums tm =
                case total dest_forall tm of
                    SOME (_, body) => strip_assums body
                  | NONE =>
                      (case total dest_imp_only tm of
                           SOME (antecedent, body) =>
                             let val (hyps, cncl) = strip_assums body
                             in (antecedent :: hyps, cncl) end
                         | NONE => ([], tm))
              fun needs_repair prem =
                let
                  val (hyps, cncl) = strip_assums prem
                in
                  not (Term.aconv cncl concl) andalso
                  not (tmem negation hyps)
                end
              val repairs = map needs_repair rest
              fun repair (prem, true) = mk_imp (mk_neg concl, prem)
                | repair (prem, false) = prem
              val rest' = ListPair.map repair (rest, repairs)
            in
              if not (List.exists (fn b => b) repairs) then thm
              else
                let
                  val hmajor = ASSUME major
                  val hprems = map ASSUME rest'
                  fun old_prem (h, true) = MP h (ASSUME (mk_neg concl))
                    | old_prem (h, false) = h
                  val negative' =
                    apply_thms core
                      (hmajor ::
                       ListPair.map old_prem (hprems, repairs))
                  val body =
                    DISJ_CASES (SPEC concl boolTheory.EXCLUDED_MIDDLE)
                      (ASSUME concl) negative'
                in
                  finish_rule vars [] (major :: rest') body
                end
            end
  end

fun patvars vars = HOLset.fromList Term.compare vars

fun rigid_frees pat vars =
  HOLset.fromList Term.compare
    (List.filter (fn v => not (HOLset.member (vars, v))) (free_vars pat))

fun is_instance pat vars tm =
  can (Term.raw_match [] (rigid_frees pat vars) pat tm) ([], [])

fun negation_headed tm =
  is_neg tm orelse
  (case total dest_imp tm of
       SOME (_, rhs) => Term.aconv rhs F
     | NONE => false)

fun is_negation_intro prems concl =
  case total dest_neg concl of
      NONE => false
    | SOME body =>
        List.exists (fn prem => aconv prem (mk_imp (body, F))) prems

fun SWAP_INTRO_RULE th =
  let
    val {vars, core, prems, concl, ...} = rule_spine th
    val not_concl = mk_neg concl
  in
    if not (is_negation_intro prems concl) andalso
       (negation_headed concl orelse
        is_instance concl (patvars vars) not_concl)
    then NONE
    else
      let
        val r = fresh_bool core
        val not_r = mk_neg r
        val lifted = map (fn prem => mk_imp (not_r, prem)) prems
        val hnot_concl = ASSUME not_concl
        val hprems = map ASSUME lifted
        val args = map (fn h => MP h (ASSUME not_r)) hprems
        val cth = apply_thms core args
        val body = CCONTR r (false_of hnot_concl cth)
      in
        SOME (finish_rule vars [r] (not_concl :: lifted) body)
      end
  end

fun DUP_INTRO_RULE th =
  let
    val {vars, core, prems, concl, ...} = rule_spine th
    val not_concl = mk_neg concl
    val lifted = map (fn prem => mk_imp (not_concl, prem)) prems
    val hprems = map ASSUME lifted
    val args = map (fn h => MP h (ASSUME not_concl)) hprems
    val cth = apply_thms core args
    val body = CCONTR concl (false_of (ASSUME not_concl) cth)
  in
    finish_rule vars [] lifted body
  end

fun DUP_ELIM_RULE th =
  let
    val {thm, vars, core, prems, ...} = elim_rule_spine th
  in
    case prems of
        [] => illformed_rule "DUP_ELIM_RULE" Elim
      | major :: rest =>
          let
            val lifted = map (fn prem => mk_imp (major, prem)) rest
            val hmajor = ASSUME major
            val hprems = map ASSUME lifted
            val args = map (fn h => MP h hmajor) hprems
            val body = apply_thms core (hmajor :: args)
          in
            finish_rule vars [] (major :: lifted) body
          end
  end

(* HOL goals cons each newly discharged hypothesis.  Put the duplicate at
   the inner end of the prefix an engine discharges -- a minor premise's
   outer !-prefix, then the implication chain below it -- so that it is
   first in the resulting assumption list, as required by blast's reverse
   duplication rule.  A quantifier under that chain opens a premise the
   engine leaves standing in the conclusion, so the duplicate stops above
   it rather than descending out of the assumptions altogether. *)
fun rev_dup_imp major prem =
  case total dest_imp_only prem of
      SOME (ante, rest) => mk_imp (ante, rev_dup_imp major rest)
    | NONE => mk_imp (major, prem)

fun rev_dup_prem major prem =
  case total dest_forall prem of
      SOME (v, body) =>
        let
          val v' =
            if free_in v major then
              variant (free_vars major @ free_vars body) v
            else v
          val body' =
            if Term.aconv v v' then body else subst [v |-> v'] body
        in
          mk_forall (v', rev_dup_prem major body')
        end
    | NONE => rev_dup_imp major prem

fun restore_rev_dup_imp major prem hmajor hprem =
  case total dest_imp_only prem of
      SOME (ante, rest) =>
        DISCH ante
          (restore_rev_dup_imp major rest hmajor
             (MP hprem (ASSUME ante)))
    | NONE => MP hprem hmajor

fun restore_rev_dup_prem major prem hmajor hprem =
  case total dest_forall prem of
      SOME (v, body) =>
        let
          val avoids = free_varsl (major :: concl hprem :: hyp hprem)
          val v' = variant avoids v
          val body' =
            if Term.aconv v v' then body else subst [v |-> v'] body
        in
          GEN v'
            (restore_rev_dup_prem major body' hmajor (SPEC v' hprem))
        end
    | NONE => restore_rev_dup_imp major prem hmajor hprem

fun REV_DUP_ELIM_RULE th =
  let
    val {thm, vars, core, prems, ...} = elim_rule_spine th
  in
    case prems of
        [] => illformed_rule "REV_DUP_ELIM_RULE" Elim
      | [_] => thm
      | major :: rest =>
          let
            val lifted = map (rev_dup_prem major) rest
            val hmajor = ASSUME major
            val hprems = map ASSUME lifted
            fun restore (prem, hprem) =
              restore_rev_dup_prem major prem hmajor hprem
            val args = ListPair.map restore (rest, hprems)
            val body = apply_thms core (hmajor :: args)
          in
            finish_rule vars [] (major :: lifted) body
          end
  end

fun bad_permutation () =
  raise mk_HOL_ERR "clasetRules" "PERMUTE_PREMISES_RULE"
    "the order is not a permutation of the rule's premise positions"

fun check_permutation count order =
  let
    val used = Array.array (count, false)
    fun record index =
      if index < 0 orelse index >= count orelse Array.sub (used, index)
      then bad_permutation ()
      else Array.update (used, index, true)
  in
    if length order = count then app record order else bad_permutation ()
  end

fun PERMUTE_PREMISES_RULE kind order th =
  let
    val {vars, core, prems, ...} =
      rule_spine_with (canonical_rule_of kind) th
    val _ = check_permutation (length prems) order
  in
    finish_rule vars [] (map (fn index => List.nth (prems, index)) order)
      (apply_assumed core prems)
  end

fun ext_info ({kind, safe, ...} : rulespec) th =
  let
    val th' = canonical_rule_of kind th
    fun elim_rule () =
      let
        val _ = (case rule_premises_of kind th' of
                    [] => illformed_rule "ext_info" kind
                  | _ => ())
        val elim = if kind = Dest then MAKE_ELIM_RULE th' else th'
      in
        CLASSICAL_RULE elim
      end
    fun intro_info () =
      let
        val rl = (th', SWAP_INTRO_RULE th')
      in
        if safe then {rl = rl, dup_rl = rl}
        else
          let
            val dup = DUP_INTRO_RULE th'
              handle HOL_ERR _ => illformed_rule "ext_info" Intro
          in
            {rl = rl, dup_rl = (dup, SWAP_INTRO_RULE dup)}
          end
      end
    fun elim_info () =
      let
        val elim = elim_rule ()
        val rl = (elim, NONE)
      in
        if safe then {rl = rl, dup_rl = rl}
        else
          let
            val dup = DUP_ELIM_RULE elim
              handle HOL_ERR _ => illformed_rule "ext_info" kind
          in
            {rl = rl, dup_rl = (dup, NONE)}
          end
      end
    fun forward_info () =
      let
        val _ = (case rule_premises_of kind th' of
                    [] => illformed_rule "ext_info" kind
                  | _ => ())
        val forward = MAKE_ELIM_RULE th'
        val rl = (forward, NONE)
      in
        {rl = rl, dup_rl = rl}
      end
    fun norm_info () =
      let val rl = (th', NONE)
      in {rl = rl, dup_rl = rl} end
  in
    case kind of
        Intro => intro_info ()
      | Elim => elim_info ()
      | Dest => elim_info ()
      | Forward => forward_info ()
      | Norm => norm_info ()
  end

datatype safe_class = Safe0 | SafeP

fun subgoals_of (is_elim, th) =
  let
    val kind = if is_elim then Elim else Intro
    val n = length (rule_premises_of kind th)
  in
    if is_elim then n - 1 else n
  end

fun safe_class_of ({kind, safe, ...} : rulespec) ({rl, ...} : info) =
  if kind = Forward orelse kind = Norm orelse not safe then NONE
  else if subgoals_of (kind <> Intro, #1 rl) = 0 then SOME Safe0
  else SOME SafeP

fun compare_tag ({weight = w1, index = i1} : tag,
                 {weight = w2, index = i2} : tag) =
  case Int.compare (w1, w2) of
      EQUAL => Int.compare (i1, i2)
    | ord => ord

fun candidate_order_measured checkpoint candidates =
  Listsort.sort
    (fn ((tag1, _), (tag2, _)) =>
       (checkpoint (); compare_tag (tag1, tag2)))
    candidates

fun candidate_order candidates =
  candidate_order_measured no_checkpoint candidates

fun same_kind ({kind = kind1, safe = safe1, ...} : rulespec)
              ({kind = kind2, safe = safe2, ...} : rulespec) =
  kind1 = kind2 andalso safe1 = safe2

fun is_elim (Intro | Norm) = false
  | is_elim (Elim | Dest | Forward) = true

fun decl_group ({kind, safe, ...} : rulespec) =
  case kind of
      Intro => if safe then 0 else 3
    | Elim => if safe then 1 else 4
    | Dest => if safe then 2 else 5
    | Forward => if safe then 6 else 7
    | Norm => if safe then 8 else 9

(* Match Bires.decl_ord: declarations are grouped by kind-class before
   their decreasing insertion tags establish recency within that class.
   The six classical groups retain their established order; the new
   Forward and Norm groups follow them. *)
fun decl_order (d1 : decl, d2 : decl) =
  case Int.compare (decl_group (#spec d1), decl_group (#spec d2)) of
      EQUAL => compare_tag (#tag d1, #tag d2)
    | order => order

(* This is Bires.decl_merge_ord.  Replaying an incoming claset in this
   order gives fresh decreasing indices the same canonical relative order. *)
fun decl_merge_order (d1 : decl, d2 : decl) =
  case (is_elim (#kind (#spec d1)), is_elim (#kind (#spec d2))) of
      (false, true) => LESS
    | (true, false) => GREATER
    | _ =>
        (case compare_tag (#tag d1, #tag d2) of
            LESS => GREATER
          | EQUAL => EQUAL
          | GREATER => LESS)

fun canonical_key th = concl (canonical_rule th)

datatype decls =
  Decls of {next : int, byconcl : decl list Termtab.table,
            byname : decl Symtab.table}

val empty_decls =
  Decls {next = ~1, byconcl = Termtab.empty, byname = Symtab.empty}

fun make_decl {name, spec, weight, info, orig} =
  {name = name, spec = spec, tag = {weight = weight, index = 0},
   info = info, orig = canonical_rule_of (#kind spec) orig}

fun get_decls (Decls {byconcl, ...}) th =
  case Termtab.lookup byconcl (canonical_key th) of
      NONE => []
    | SOME ds => ds

fun find_decl (Decls {byname, ...}) name = Symtab.lookup byname name

fun decl_name_member decls name = Option.isSome (find_decl decls name)

fun dest_decls (Decls {byconcl, ...}) =
  Listsort.sort decl_order
    (Termtab.fold (fn (_, ds) => fn acc => ds @ acc) byconcl [])

fun duplicate decl ds =
  List.exists (fn old => same_kind (#spec decl) (#spec old)) ds

fun rule_description ({kind, safe, ...} : rulespec) =
  (if safe then "safe " else "unsafe ") ^ kind_name kind ^ " rule"

(* [derived] marks a rule a library computed from a user declaration rather
   than one the user named.  Such a rule carries neither the duplicate and
   cross-kind diagnostics -- a rule the caller never named cannot be the
   declaration mistake those warnings are meant to report, and the
   invocation-scoped tactics would otherwise repeat them on every goal --
   nor the refusal of a rule whose conclusion duplicates an installed one.
   A derived rule belongs to the declaration that produced it, so two
   declarations deriving the same rule each own a copy: retracting one must
   leave the other's contribution in place.  Name collisions are refused
   either way, since a name identifies at most one declaration. *)
fun extend_decl_gen {derived} (decl : decl) (Decls {next, byconcl, byname}) =
  let
    val key = canonical_key (#orig decl)
    val old = Option.getOpt (Termtab.lookup byconcl key, [])
    val unchanged = Decls {next = next, byconcl = byconcl, byname = byname}
    fun warn message =
      if derived then ()
      else HOL_WARNING "clasetRules" "extend_decl" message
  in
    if (duplicate decl old andalso not derived) orelse
       Option.isSome (Symtab.lookup byname (#name decl))
    then
      (warn ("Ignoring duplicate " ^ rule_description (#spec decl));
       (NONE, unchanged))
    else
      let
        val _ =
          if List.exists (fn old => not (same_kind (#spec decl) (#spec old)))
                         old
          then warn ("Rule already declared as a different " ^
                     rule_description (#spec (hd old)))
          else ()
        val {weight, ...} = #tag decl
        val decl' =
          {name = #name decl, spec = #spec decl,
           tag = {weight = weight, index = next}, info = #info decl,
           orig = #orig decl}
      in
        (SOME decl',
         Decls {next = next - 1,
                byconcl = Termtab.update (key, decl' :: old) byconcl,
                byname = Symtab.update (#name decl', decl') byname})
      end
  end

val extend_decl = extend_decl_gen {derived = false}
val extend_derived_decl = extend_decl_gen {derived = true}

fun remove_decl name (decls as Decls {next, byconcl, byname}) =
  case Symtab.lookup byname name of
      NONE => ([], decls)
    | SOME decl =>
        let
          val key = canonical_key (#orig decl)
          val old = Option.getOpt (Termtab.lookup byconcl key, [])
          val kept = List.filter (fn d => #name d <> name) old
          val byconcl' =
            if List.null kept then Termtab.delete_safe key byconcl
            else Termtab.update (key, kept) byconcl
        in
          ([decl],
           Decls {next = next, byconcl = byconcl',
                  byname = Symtab.delete_safe name byname})
        end

fun merge_decls (left, right) =
  let
    val incoming = Listsort.sort decl_merge_order (dest_decls right)
    fun add [] decls added = (List.rev added, decls)
      | add (decl :: rest) decls added =
          (case extend_decl decl decls of
              (NONE, decls') => add rest decls' added
            | (SOME decl', decls') => add rest decls' (decl' :: added))
  in
    add incoming left []
  end

datatype cdelta = ADD of {name : thname, spec : rulespec} | RM of string

fun kind_encode Intro = ThyDataSexp.String "intro"
  | kind_encode Elim = ThyDataSexp.String "elim"
  | kind_encode Dest = ThyDataSexp.String "dest"
  | kind_encode Forward = ThyDataSexp.String "forward"
  | kind_encode Norm = ThyDataSexp.String "norm"

fun kind_decode (ThyDataSexp.String "intro") = SOME Intro
  | kind_decode (ThyDataSexp.String "elim") = SOME Elim
  | kind_decode (ThyDataSexp.String "dest") = SOME Dest
  | kind_decode (ThyDataSexp.String "forward") = SOME Forward
  | kind_decode (ThyDataSexp.String "norm") = SOME Norm
  | kind_decode _ = NONE

fun spec_encode ({kind, safe, prio} : rulespec) =
  ThyDataSexp.pair3_encode
    (kind_encode, ThyDataSexp.Bool,
     ThyDataSexp.option_encode ThyDataSexp.Int) (kind, safe, prio)

fun spec_decode sexp =
  Option.map (fn (kind, safe, prio) =>
                {kind = kind, safe = safe, prio = prio})
    (ThyDataSexp.pair3_decode
       (kind_decode, ThyDataSexp.bool_decode,
        ThyDataSexp.option_decode ThyDataSexp.int_decode) sexp)

fun encode_delta (ADD {name, spec}) =
      ThyDataSexp.tag_encode "clasetADD1"
        (ThyDataSexp.pair_encode (ThyDataSexp.KName, spec_encode))
        (name, spec)
  | encode_delta (RM name) =
      ThyDataSexp.tag_encode "clasetRM1" ThyDataSexp.String name

fun dec_add sexp =
  Option.map (fn (name, spec) => ADD {name = name, spec = spec})
    (ThyDataSexp.tag_decode "clasetADD1"
       (ThyDataSexp.pair_decode (ThyDataSexp.kname_decode, spec_decode))
       sexp)

fun dec_rm sexp =
  Option.map RM
    (ThyDataSexp.tag_decode "clasetRM1" ThyDataSexp.string_decode sexp)

fun decode_delta sexp =
  ThyDataSexp.first [dec_add, dec_rm] sexp

fun load_delta (ADD {name, spec}) =
      (SOME (name, spec, DB.fetch_knm name)
       handle HOL_ERR _ =>
         (HOL_WARNING "clasetRules" "load_delta"
            ("Bad claset add command, dropping theorem " ^
             KernelSig.name_toString name);
          NONE))
  | load_delta (RM _) = NONE

fun uptodate_delta (ADD {name, ...}) =
      (Theory.uptodate_thm (DB.fetch_knm name)
       handle HOL_ERR _ =>
         (HOL_WARNING "clasetRules" "uptodate_delta"
            ("Bad claset add command, dropping theorem " ^
             KernelSig.name_toString name);
          false))
  | uptodate_delta (RM _) = true

end
