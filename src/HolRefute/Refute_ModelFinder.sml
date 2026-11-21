(*  Title:      HolRefute/Refute_ModelFinder.sml
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009, 2010

Driver for the HOL4 Refute model finder.  The control flow is a port of
Nitpick's pick_them_nits_in_term. *)

structure Refute_ModelFinder :> Refute_ModelFinder = struct

open Portable Feedback
infix |>

structure KK = Refute_Forl
structure MFH = Refute_ModelFinder_HOL
structure MFK = Refute_ModelFinder_Kodkod
structure MFM = Refute_ModelFinder_Model
structure MFMono = Refute_ModelFinder_Mono
structure MFN = Refute_ModelFinder_Names
structure MFNT = Refute_ModelFinder_Nut
structure MFP = Refute_ModelFinder_Preproc
structure MFS = Refute_ModelFinder_Scope
structure Util = Refute_ModelFinder_Util

type term = Term.term
type hol_type = Type.hol_type
type rich_problem = MFK.rich_problem

(* Display of kodkod witnesses, through the backend's [render] hook. *)

fun unbox_display_type ty =
  if Type.is_vartype ty then ty
  else
    let val {Thy, Tyop, Args} = Type.dest_thy_type ty
    in
      if MFH.is_funbox_type ty then
        Type.-->(unbox_display_type (List.nth (Args, 0)),
          unbox_display_type (List.nth (Args, 1)))
      else if MFH.is_pairbox_type ty then
        pairSyntax.mk_prod
          (unbox_display_type (List.nth (Args, 0)),
           unbox_display_type (List.nth (Args, 1)))
      else
        Type.mk_thy_type {Thy = Thy, Tyop = Tyop,
          Args = map unbox_display_type Args}
    end

fun is_boxed_type ty = MFH.is_funbox_type ty orelse MFH.is_pairbox_type ty

(* The predicate an iterator type variable [:'<prefix>p] counts for. *)
fun iterator_scope_name ty =
  let
    fun after prefix =
      SOME (String.extract (Type.dest_vartype ty, size prefix + 1, NONE))
  in
    if MFH.is_lfp_iterator_type ty then after MFN.lfp_iterator_prefix
    else if MFH.is_gfp_iterator_type ty then after MFN.gfp_iterator_prefix
    else NONE
  end

fun format_scope_assignment (ty, card) =
  case iterator_scope_name ty of
      SOME predicate =>
        "iter " ^ predicate ^ " = " ^ Int.toString (Int.max (0, card - 1))
    | NONE =>
        if MFH.is_bisim_iterator_type ty then
          "bisim_depth = " ^ Int.toString (card - 1)
        else
          "card " ^ Refute_Core.type_name (unbox_display_type ty) ^ " = " ^
          Int.toString card

fun format_scope NONE = ""
  | format_scope (SOME assignments) =
      "\nScope: " ^ String.concatWith ", "
        (map format_scope_assignment assignments)

fun format_bool_function value =
  case Lib.total Type.dom_rng (Term.type_of value) of
      SOME (domain, range) =>
        if domain = Type.bool andalso range = Type.bool then
          let
            fun at argument = Refute_Core.boolean_value_for_display
              (Term.mk_comb (value, argument))
          in
            case (at boolSyntax.F, at boolSyntax.T) of
                (SOME at_false, SOME at_true) =>
                  let val arrow =
                    if Feedback.get_tracefn "PP.avoid_unicode" () = 1 then
                      "|->"
                    else
                      "↦"
                  in
                    SOME ("{F " ^ arrow ^ " " ^
                      Refute_Core.format_term at_false ^ ", T " ^ arrow ^
                      " " ^ Refute_Core.format_term at_true ^ "}")
                  end
              | _ => NONE
          end
        else NONE
    | NONE => NONE

val format_bindings = Refute_Core.format_pairs (fn value =>
  Option.getOpt (format_bool_function value, Refute_Core.format_term value))

fun format_named_terms title entries =
  if null entries then "" else
    "\n" ^ title ^ ":\n" ^ String.concatWith "\n"
      (map (fn (name, value) =>
        "  " ^ name ^ " = " ^ Refute_Core.format_term value) entries)

fun format_types types =
  if null types then "" else
    "\nTypes:\n" ^ String.concatWith "\n" (map
      (fn (ty, values, complete) =>
        "  " ^ Refute_Core.type_name (unbox_display_type ty) ^
        (if is_boxed_type ty then " [boxed]" else "") ^ " = {" ^
        String.concatWith ", " (map Refute_Core.format_term values) ^
        (if complete then "" else
           if null values then "..." else ", ...") ^ "}") types)

fun format_model (_ : Refute_Core.mf_config) NONE = ""
  | format_model mf
      (SOME ({skolems, consts, types} : Refute_Core.model_report)) =
      (if #show_types mf then format_types types else "") ^
      (if #show_skolems mf then
         format_named_terms "Skolem constants" skolems
       else "") ^
      (if #show_consts mf andalso not (null consts) then
         "\nConstants:\n" ^ String.concatWith "\n"
           (map (fn (name, operator, value) =>
             "  " ^ Refute_Core.format_term name ^ " " ^ operator ^ " " ^
             Refute_Core.format_term value) consts)
       else "")

fun render_witness mf (cex : Refute_Core.counterexample) =
  {scope = format_scope (#scope cex),
   bindings = if null (#bindings cex) then ""
              else "\n" ^ format_bindings (#bindings cex),
   model = format_model mf (#model cex)}

val max_unsound_delay_ms = 200
val max_unsound_delay_percent = 2

fun check_deadline deadline =
  if Time.now () >= deadline then raise Timeout.TIMEOUT Time.zeroTime
  else ()

(* Certification of a model the solver has finished must end before the
   call's own timer fires.  Both are [Timeout.apply] timers set for the
   same instant; when the outer one fires first, the inner [Timeout.apply]
   re-raises [Interrupt] instead of [Timeout.TIMEOUT], the model is lost
   and the call reports "timed out".  Replay is therefore given a deadline
   this much before the call's: a tenth of the budget, at most five seconds.
   A model whose replay does not finish by then is kept uncertified, as
   when replay runs out of its deadline at any other time. *)
fun certification_headroom deadline started =
  let val budget = Real.max (0.0, Time.toReal (Time.- (deadline, started)))
      val cap = Time.fromSeconds 5
      val tenth = Time.fromReal (budget / 10.0)
  in if Time.< (cap, tenth) then cap else tenth end

fun unsound_delay deadline =
  Int.max (0, Int.min (max_unsound_delay_ms,
    LargeInt.toInt (Time.toMilliseconds (Refute_Util.remaining deadline)) *
      max_unsound_delay_percent div 100))
  handle Interrupt => raise Interrupt | _ => 0

fun ground_types context binarize terms =
  let
    fun add ty types =
      if MFH.is_fun_type ty orelse MFH.is_pair_type ty orelse
         pred_setSyntax.is_set_type ty then
        List.foldl (fn (argument, result) => add argument result)
          types (MFS.type_arguments ty)
      else if MFH.is_boolean_type ty orelse Util.member_type ty types then
        types
      else if MFH.is_exact_carrier_type ty then
        (* A word carrier is atomic: its index type is a width, not a carrier
           the search should size, and its element type is [bool].  [:char] is
           atomic for the same reason, its size being fixed at 256. *)
        Util.add_type ty types
      else
        let
          val types = Util.add_type ty types
          val constructor_types = List.concat
            (map MFH.constructor_arg_types
              (MFH.binarized_and_boxed_data_type_constrs
                 context binarize ty))
          val nested =
            if null constructor_types then MFS.type_arguments ty
            else constructor_types
        in
          List.foldl (fn (argument, result) => add argument result)
            types nested
        end
    fun add_term term types = add (Term.type_of term) types
    (* A word or char literal is folded into the carrier atom that denotes it,
       so its [n2w] or [CHR] head must not pull the [num] carrier into the
       problem: [num] is unbounded, and the scope search would then grow it
       forever for a goal that never mentions a number. *)
    fun subterms term =
      if MFH.is_word_literal term orelse MFH.is_char_literal term then [term]
      else
        term ::
        (case Lib.total Term.dest_comb term of
             SOME (rator, rand) => subterms rator @ subterms rand
           | NONE =>
               case Lib.total Term.dest_abs term of
                   SOME (variable, body) => variable :: subterms body
                 | NONE => [])
    fun add_all_subterms term types =
      List.foldl (fn (subterm, result) => add_term subterm result)
        types (subterms term)
  in
    Listsort.sort Type.compare
      (List.foldl (fn (term, result) => add_all_subterms term result)
        [] terms)
  end

fun free_variables terms =
  Util.distinct_terms (List.concat (map Term.free_vars_lr terms))

fun none_true assignments =
  List.all (fn (_, value) => value <> SOME true) assignments

fun authenticity_reasons (mf : Refute_Core.mf_config)
      got_all_mono_user_axioms no_poly_user_axioms codatatypes_ok =
  if not no_poly_user_axioms then
    ["polymorphic axioms prevent an authenticity guarantee"]
  else
    let
      val options =
        (if got_all_mono_user_axioms then []
         else ["\"user_axioms\" set to \"true\""]) @
        (if none_true (#wf mf) then []
         else ["\"wf\" set to \"smart\" or \"false\""]) @
        (if none_true (#finitize mf) then []
         else ["\"finitize\" set to \"smart\" or \"false\""]) @
        (if #total_consts mf = SOME true then
           ["\"total_consts\" set to \"smart\" or \"false\""]
         else []) @
        (if codatatypes_ok then []
         else ["\"bisim_depth\" set to a nonnegative value"])
    in
      MFM.try_again_reasons options
    end

(* Completeness is a property of the scope: a word type on a
   value-list carrier is incomplete. *)
fun exact_totality all_types (scope : MFS.scope) =
  List.all (MFS.is_exact_type scope true) all_types

fun type_name ty = Parse.type_to_string ty

fun scope_comment (scope : MFS.scope) =
  String.concatWith ", " (map (fn (ty, card) =>
    if MFH.is_bisim_iterator_type ty then
      "bisim_depth = " ^ Int.toString (card - 1)
    else
      "card " ^ type_name ty ^ " = " ^ Int.toString card)
    (#card_assigns scope))

fun deep_data_types all_types sel_names =
  let
    fun selector_domain name =
      Option.map #1 (Lib.total Type.dom_rng (MFNT.type_of name))
    fun selected ty = List.exists (fn name =>
      case selector_domain name of
          SOME domain => Util.same_type ty domain
        | NONE => false) sel_names
  in
    List.filter (fn ty =>
      Util.same_type ty ``:unit`` orelse Util.same_type ty MFH.num_type orelse
      MFH.is_bitword_type ty orelse
      Option.isSome (MFH.word_dimension ty) orelse
      (MFH.is_data_type ty andalso selected ty)) all_types
  end

fun finitizable_data_types context finitizes kind_of_monotonic
      all_types deep_types =
  let
    val data_types = List.filter MFH.is_data_type all_types
    val (deep, shallow) = List.partition (fn ty =>
      Util.member_type ty deep_types) data_types
    fun infinite ty = not (MFH.is_finite_type context ty)
    fun forced ty =
      MFS.mono_override finitizes ty = SOME (SOME true)
    fun shallow_finitizable ty =
      case MFS.mono_override finitizes ty of
          SOME (SOME value) => value
        | _ => kind_of_monotonic ty
  in
    List.filter (fn ty => infinite ty andalso forced ty) deep @
    List.filter (fn ty => infinite ty andalso
      shallow_finitizable ty) shallow
  end

fun actual_solver incremental (mf : Refute_Core.mf_config) =
  let
    val requested = #sat_solver mf
    val configured = Refute_ForlSat.configured_sat_solvers incremental
    val solver =
      if requested = "smart" then
        Refute_ForlSat.smart_sat_solver_name incremental
      else if incremental andalso not (Lib.mem requested configured) then
        (Refute_Core.Private.say 1
           ("An incremental SAT solver is required: \"SAT4J\" will be " ^
            "used instead of " ^ Lib.quote requested ^ "\n");
         "SAT4J")
      else
        requested
    val _ = if requested <> "smart" then () else
      Refute_Core.Private.say 2
        ("Using SAT solver " ^ Lib.quote solver ^ "\nThe following" ^
         (if incremental then " incremental " else " ") ^
         "solvers are configured: " ^
         String.concatWith ", " (map Lib.quote configured) ^ "\n")
  in
    solver
  end

fun solver_arguments deadline solver =
  #2 (Refute_ForlSat.sat_solver_spec (Refute_Util.remaining deadline) solver)

(* The assembly parameters of a scope are shared
   by the check that a scope can fit and by its assembly. *)
fun assembly_params deadline (mf : Refute_Core.mf_config)
      all_types solver free_names nonsel_names nondef_us def_us need_us
      (scope : MFS.scope) : MFK.assembly_params =
  let
    val effective_total_consts =
      Option.getOpt (#total_consts mf, exact_totality all_types scope)
  in
    {debug = #debug mf,
     peephole_optim = #peephole_optim mf,
     total_consts = effective_total_consts,
     datatype_sym_break = #datatype_sym_break mf,
     kodkod_sym_break = #kodkod_sym_break mf,
     comment = scope_comment scope,
     solver = solver_arguments deadline solver,
     unsound_delay = unsound_delay deadline,
     free_names = free_names,
     nonsel_names = nonsel_names,
     nondef_us = nondef_us,
     def_us = def_us,
     need_us = need_us}
  end

(* [reject_too_large] hears of the rejections for
   size, which a larger scope would meet too; [reject_problem] of the rest. *)
fun problem_for_scope params reject_problem reject_too_large unsound scope =
  SOME (MFK.assemble_problem params unsound scope)
  handle Util.TOO_LARGE reason => (reject_too_large reason; NONE)
       | Util.TOO_SMALL reason => (reject_problem reason; NONE)

(* The reason a scope's relations cannot fit,
   found without assembling anything. *)
fun scope_too_large params scope =
  (MFK.check_scope_fits params scope; NONE)
  handle Util.TOO_LARGE reason => SOME reason

(* [bigger] has at least the cardinality of every
   type that [smaller] has.  What does not fit at [smaller] does not fit at
   [bigger]: relation arities grow with cardinalities and the arity limit
   shrinks with the universe. *)
fun scope_at_least (bigger : MFS.scope, smaller : MFS.scope) =
  List.all (fn (ty, card) =>
    case List.find (fn (other, _) => Util.same_type ty other)
           (#card_assigns bigger) of
        SOME (_, larger) => larger >= card
      | NONE => false) (#card_assigns smaller)

fun metadata (_, metadata : MFK.problem_metadata) = metadata

fun liberal_budget_after_models
      {max_potential, max_genuine, delivered, kept, promoted,
       incremental} =
  if promoted then (0, max_genuine - 1)
  else
    (max_potential - (if incremental then delivered else kept),
     max_genuine)

fun raw_problem (problem, _ : MFK.problem_metadata) = problem

(* Kodkodi's textual instance format is syntactic only.  Check the instance
   against the emitted bound schema before reconstruction: absent relations
   otherwise decode as empty relations. *)
fun valid_instance (problem : KK.problem) assignments =
  let
    (* A declared bound pairs each relation index with its printed name;
       an instance assignment carries the index alone. *)
    val expected = List.concat (map (map #1 o #1) (#bounds problem))
    fun distinct [] = true
      | distinct (value :: rest) =
          not (Lib.mem value rest) andalso distinct rest
    fun valid_assignment ((arity, relation), tuples) =
      Lib.mem (arity, relation) expected andalso
      distinct tuples andalso
      List.all (fn tuple =>
        length tuple = arity andalso
        List.all (fn atom => atom >= 0 andalso atom < #univ_card problem)
          tuple) tuples
    fun tuple_atoms (KK.Tuple atoms) = SOME atoms
      | tuple_atoms (KK.TupleIndex (arity, index)) =
          let
            fun decode 0 0 atoms = SOME atoms
              | decode 0 _ _ = NONE
              | decode count number atoms =
                  decode (count - 1) (number div #univ_card problem)
                    ((number mod #univ_card problem) :: atoms)
          in
            if arity < 0 orelse index < 0 orelse #univ_card problem <= 0
            then NONE
            else decode arity index []
          end
      | tuple_atoms _ = NONE
    fun tuple_in (KK.TupleSet tuples) tuple =
          List.exists (fn candidate =>
            case tuple_atoms candidate of
                SOME atoms => atoms = tuple
              | NONE => false) tuples
      | tuple_in (KK.TupleAtomSeq (count, first)) tuple =
          (case tuple of
               [atom] => count >= 0 andalso atom >= first andalso
                 atom < first + count
             | _ => false)
      | tuple_in (KK.TupleUnion (left, right)) tuple =
          tuple_in left tuple orelse tuple_in right tuple
      | tuple_in (KK.TupleProduct (left, right)) tuple =
          List.exists (fn split =>
            tuple_in left (List.take (tuple, split)) andalso
            tuple_in right (List.drop (tuple, split)))
            (Portable.upto 0 (length tuple))
      | tuple_in _ _ = false
    fun tuples_of (KK.TupleSet tuples) =
          Option.map (fn _ => List.mapPartial tuple_atoms tuples)
            (List.foldl (fn (tuple, result) =>
              case (tuple_atoms tuple, result) of
                  (SOME _, SOME ()) => SOME ()
                | _ => NONE) (SOME ()) tuples)
      | tuples_of (KK.TupleAtomSeq (count, first)) =
          if count < 0 then NONE
          else SOME (map (fn atom => [atom])
            (Portable.upto first (first + count - 1)))
      | tuples_of (KK.TupleUnion (left, right)) =
          (case (tuples_of left, tuples_of right) of
               (SOME left, SOME right) => SOME (left @ right)
             | _ => NONE)
      | tuples_of (KK.TupleProduct (left, right)) =
          (case (tuples_of left, tuples_of right) of
               (SOME left, SOME right) => SOME
                 (List.concat (map (fn xs => map (fn ys => xs @ ys) right)
                   left))
             | _ => NONE)
      | tuples_of _ = NONE
    (* Solver tuples and compact bound expansions can both be large.  Do not
       turn a valid-instance check into a quadratic scan of those lists. *)
    val compare_tuple = list_compare Int.compare
    fun sorted_set tuples =
      let
        fun drop_equal value (next :: rest) =
              if compare_tuple (value, next) = EQUAL then
                drop_equal value rest
              else
                next :: rest
          | drop_equal _ [] = []
        fun distinct [] = []
          | distinct (value :: rest) = value :: distinct (drop_equal value rest)
      in
        distinct (Listsort.sort compare_tuple tuples)
      end
    fun subset left right =
      let
        fun loop [] _ = true
          | loop _ [] = false
          | loop (one :: ones) (other :: others) =
              (case compare_tuple (one, other) of
                   LESS => false
                 | EQUAL => loop ones others
                 | GREATER => loop (one :: ones) others)
      in
        loop (sorted_set left) (sorted_set right)
      end
    fun assignment relation = AList.lookup (op =) assignments relation
    fun valid_bound (relations, sets) =
      let
        fun valid_relation relation =
          case (assignment relation, sets) of
              (SOME actual, [exact]) =>
                (case tuples_of exact of
                     SOME tuples =>
                       subset actual tuples andalso subset tuples actual
                   | NONE => false)
            | (SOME actual, [lower, upper]) =>
                (case tuples_of lower of
                     SOME tuples =>
                       subset tuples actual andalso
                       List.all (tuple_in upper) actual
                   | NONE => false)
            | _ => false
      in
        List.all valid_relation (map #1 relations)
      end
    val relations = map #1 assignments
  in
    length assignments = length expected andalso distinct relations andalso
    List.all (fn relation => Lib.mem relation relations) expected andalso
    List.all valid_assignment assignments andalso
    List.all valid_bound (#bounds problem)
  end

fun rich_problems_equivalent (left : rich_problem, right : rich_problem) =
  #unsound (metadata left) = #unsound (metadata right) andalso
  MFS.scopes_equivalent
    (#scope (metadata left), #scope (metadata right)) andalso
  KK.problems_equivalent (raw_problem left, raw_problem right)

fun rich_member problem = List.exists (fn other =>
  rich_problems_equivalent (problem, other))

fun distinct_ints values = Listsort.sort Int.compare (Lib.mk_set values)

fun certainty_is_genuine Refute_Core.Genuine = true
  | certainty_is_genuine _ = false

fun certainty_is_potential (Refute_Core.Potential _) = true
  | certainty_is_potential _ = false

fun replace_stats stats (cex : Refute_Core.counterexample) =
  {backend = #backend cex, substrate = #substrate cex,
   certainty = #certainty cex, bindings = #bindings cex,
   evals = #evals cex, cert = #cert cex, scope = #scope cex,
   model = #model cex, stats = stats}

(* HOL4 has no type classes or sorts, so all goal type variables occupy
   Isabelle's single default-sort equivalence class.  Keeping the
   alphabetically first variable is therefore the sortless specialization
   of Nitpick's [merged_type_var_table_for_terms]. *)
fun merge_type_vars_in_terms terms =
  let
    val tyvars = Listsort.sort (fn (left, right) =>
      String.compare (Type.dest_vartype left, Type.dest_vartype right))
      (Lib.U (map Term.type_vars_in_term terms))
  in
    case tyvars of
        [] => terms
      | canonical :: rest =>
          let
            val theta = map (fn tyvar =>
              {redex = tyvar, residue = canonical}) rest
          in
            map (Term.inst theta) terms
          end
  end

fun merge_type_vars_in_context_input
      (mf : Refute_Core.mf_config) original evals =
  if not (#merge_type_vars mf) then (mf, original, evals)
  else
    let
      val needs = #need mf
      val need_terms = Option.getOpt (needs, [])
      val merged = merge_type_vars_in_terms
        (original :: (evals @ need_terms))
      val merged_tail = tl merged
      val merged_evals = List.take (merged_tail, length evals)
      val merged_need_terms = List.drop (merged_tail, length evals)
      val merged_needs = Option.map (fn _ => merged_need_terms) needs
      val context_mf = Refute_Core.change_mf
        (Refute_Core.MfNeed merged_needs) mf
    in
      (context_mf, hd merged, merged_evals)
    end

fun prepare_instance_input (instance : Refute_Core.instance) =
  let
    val input_original = #original instance
    val (original, renaming, type_renaming) =
      MFN.rename_colliding_goal_vars
        (MFN.reserved_frees input_original) input_original
    val _ = MFN.assert_user_goal original
    val renaming_subst = map (fn (old, fresh) =>
      {redex = old, residue = fresh}) renaming
    fun rename term = term
      |> Term.subst renaming_subst
      |> Term.inst type_renaming
    fun rename_eval term =
      let
        val prepared = rename term
        (* Eval expressions introduce generated [refute$evalN] names too.
           Sanitize their own reserved frees before placeholders are made. *)
        val (renamed, _, _) = MFN.rename_colliding_goal_vars
          (MFN.reserved_frees prepared) prepared
      in
        renamed
      end
  in
    (original, map rename_eval (#evals instance))
  end

(* A quotient package type also has a kernel typedef theorem, so the raw
   morphism guard discovers both classes.  Prefer the quotient theorem; only
   if that validated harvest misses do we try the typedef bijections shape.
   Iterate because one problem may mention several previously unseen types. *)
fun harvest_guard terms =
  case MFH.first_unregistered_typedef terms of
      NONE => (NONE, false)
    | SOME ty =>
        if MFH.harvest_quotient ty orelse MFH.harvest_typedef ty then
          let val (reason, _) = harvest_guard terms
          in (reason, true) end
        else
          (MFH.unregistered_typedef_reason terms, false)

exception RESTART_AFTER_HARVEST

(* See [add_problem]. *)
exception NO_SCOPE_FITS of string * string

val scope_limit_hint =
  "scope limit reached; consider using \"mono\" or \"merge_type_vars\" " ^
  "to prevent this"

(* A monotonicity analysis is abandoned two ways: it runs out of its tactic
   budget, or the calculus hits an internal mtype mismatch and reports BAD.
   Both must read as "not monotonic".  The verdict only ever removes work --
   a monotonic type lets the scope search collapse cardinalities -- so
   answering true on no evidence would let Refute skip a scope that can hold
   a counterexample and report None unsoundly, whereas answering false costs
   nothing but scopes.  Whether a deadline is reached is a wall-clock
   question and untestable without a race; that abandonment degrades to
   false is not, so the polarity lives here, in one named place a test can
   call, rather than inline in a handler nothing can reach.  Anything else
   is re-raised: only these two are abandonment. *)
fun abandoned_mono_verdict report exn =
  case exn of
      Timeout.TIMEOUT _ => (report ("timeout", ""); false)
    | Util.BAD (location, detail) => (report (location, detail); false)
    | _ => raise exn

(* How far the model finder got, so that every [Unknown] it reports names
   the phase it reached and its counts.  One record is shared by all
   instances of a run; the counters add up over them. *)
type progress =
  {phase : string ref, definitions : int ref, emitted : int ref,
   completed : int ref, offered : int ref, finished : int ref,
   unused : int ref, starved_batches : int ref, starved_problems : int ref,
   unresolved : int ref, solver_errors : (string * int) list ref,
   dropped_msec : int ref}

fun new_progress () : progress =
  (MFH.reset_sharing_counts ();
  {phase = ref "preprocessing", definitions = ref 0, emitted = ref 0,
   completed = ref 0, offered = ref 0, finished = ref 0,
   unused = ref 0, starved_batches = ref 0, starved_problems = ref 0,
   unresolved = ref 0, solver_errors = ref [], dropped_msec = ref 0})

(* The solver's errors, counted by message over all batches. *)
fun add_solver_error (progress : progress) text count =
  let
    fun add [] = [(text, count)]
      | add ((message, n) :: rest) =
          if message = text then (message, n + count) :: rest
          else (message, n) :: add rest
  in
    #solver_errors progress := add (!(#solver_errors progress))
  end

fun solver_error_reasons (progress : progress) =
  map (fn (text, count) =>
         "solver error (" ^ Int.toString count ^ " time" ^
         (if count = 1 then "" else "s") ^ "): " ^ text)
    (!(#solver_errors progress)) @
  (if !(#unresolved progress) = 0 then []
   else [Int.toString (!(#unresolved progress)) ^ " problems ended with " ^
         "no result when the solver ended by itself with errors"])

fun enter_phase (progress : progress) name = #phase progress := name

fun bump counter n = counter := !counter + n

fun progress_reason (progress : progress) rejected =
  "phase reached: " ^ !(#phase progress) ^ "; definitions accepted " ^
  Int.toString (!(#definitions progress)) ^ "; scopes completed " ^
  Int.toString (!(#completed progress)) ^ " of " ^
  Int.toString (!(#emitted progress)) ^ " emitted; problems offered " ^
  Int.toString (!(#offered progress)) ^ ", finished " ^
  Int.toString (!(#finished progress)) ^ ", rejected " ^
  Int.toString rejected ^ "; finished but unused " ^
  Int.toString (!(#unused progress)) ^ "; batches starved " ^
  Int.toString (!(#starved_batches progress)) ^ " (problems never started " ^
  Int.toString (!(#starved_problems progress)) ^ "); solver errors " ^
  Int.toString (List.foldl (fn ((_, n), total) => n + total) 0
                  (!(#solver_errors progress))) ^
  "; time on rejected problems " ^
  Int.toString (!(#dropped_msec progress)) ^ " ms; " ^
  MFH.sharing_summary ()

(* A preprocessing pass names itself as the phase reached, with the count it
   has done, and ends the call when its deadline has passed. *)
fun preprocessing_pass (progress : progress) deadline text =
  (enter_phase progress ("preprocessing (" ^ text ^ ")");
   check_deadline deadline)

fun run_instance deadline started (config : Refute_Core.config)
      incremental solver (initial_max_potential, initial_max_genuine)
      reject_problem (progress : progress)
      (instance : Refute_Core.instance) =
  let
    val _ = enter_phase progress "preprocessing"
    val _ = check_deadline deadline
    val mf = #mf config
    val sound_finitizes = none_true (#finitize mf)
    val (prepared_original, prepared_evals) =
      prepare_instance_input instance
    val (context_mf, original, eval_terms) =
      merge_type_vars_in_context_input mf prepared_original prepared_evals
    val negated =
      if #falsify mf then boolSyntax.mk_imp (original, boolSyntax.F)
      else original
    val (_, closure, _) = Refute_Cert.closure_of original
    val (_, _, pnf) = Refute_Cert.normalize_to_pnf Conv.QCONV closure
    val prefix_origins = Refute_Skolem.mark_source_ambiguities original
      (Refute_Skolem.prefix_binders pnf)
    (* [deviation from upstream] indexed table or map in place of a list scan *)
    fun fresh_context () =
      let val context = MFH.make_context context_mf eval_terms
      in #prefix_origins context := prefix_origins; context end
    val context = fresh_context ()
    val fixpoint_refusal = MFH.first_fixpoint_refusal context original
    val _ = if Option.isSome fixpoint_refusal then
        MFH.print_wf_cache context else ()
    val _ = case fixpoint_refusal of
        SOME reason => raise Util.NOT_SUPPORTED reason
      | NONE => ()
    (* [deviation from upstream] indexed table or map in place of a list scan *)
    val preprocessed as
        (nondef_ts, def_ts, need_ts, got_all_mono_user_axioms,
         no_poly_user_axioms, binarize) =
      MFP.preprocess_formulas_noting (preprocessing_pass progress deadline)
        context [] negated
    (* [deviation from upstream] a test's check of the result *)
    val _ = (!MFP.preprocess_check) fresh_context context negated preprocessed
    val _ = check_deadline deadline
    val _ = enter_phase progress "preprocessing (scanning for typedefs)"
    (* A typedef morphism can enter through an unfolded wrapper even when it
       was absent from the surface goal.  Scan the complete preprocessed
       problem as well as the early surface-goal guard in [run]. *)
    val _ =
      case harvest_guard (nondef_ts @ def_ts) of
          (SOME reason, _) => raise Util.NOT_SUPPORTED reason
        | (NONE, true) =>
            (* The first preprocessing pass did not know the harvested
               registration and therefore did not insert its axioms or
               morphism rewrites.  Restart with a fresh context before any
               scope or solver work; the positive registry cache makes the
               second pass constant-time at this guard. *)
            raise RESTART_AFTER_HARVEST
        | (NONE, false) => ()
    val _ = bump (#definitions progress) (length def_ts)
    val _ = enter_phase progress ("preprocessing (translating " ^
      Int.toString (length nondef_ts) ^ " axioms and " ^
      Int.toString (length def_ts) ^ " definitions)")
    val _ = MFH.refresh_iterator_arg_types context (nondef_ts @ def_ts)
    val _ = MFH.print_wf_cache context
    val nondef_us = map (MFNT.nut_from_term context MFNT.Eq) nondef_ts
    val def_us = map (MFNT.nut_from_term context MFNT.DefEq) def_ts
    val need_us = map (MFNT.nut_from_term context MFNT.Eq) need_ts
    val (free_names, const_names) =
      List.foldl (fn (nut, names) =>
        MFNT.add_free_and_const_names nut names)
        ([], []) (nondef_us @ def_us @ need_us)
    val (sel_names, nonsel_names) = List.partition
      (MFN.is_sel o MFNT.nickname_of) const_names
    (* The word literals of the problem are the
       centres of its fragment word carriers' value lists. *)
    val _ = MFH.set_word_literals context (nondef_ts @ def_ts @ need_ts)
    val all_types = ground_types context binarize
      (nondef_ts @ def_ts @ need_ts)
    val unique_scope = #card_mode mf = Refute_Core.FixedBound andalso
      List.all (fn (_, values) => length values = 1) (#card mf)
    val calculus_mono_cache = ref ([] : (hol_type * bool) list)
    val _ =
      if #binary_ints mf = SOME true andalso not binarize andalso
         List.exists (fn ty => ty = MFH.num_type orelse ty = MFH.int_type)
           all_types then
        Refute_Core.Private.say 2
          ("The option \"binary_ints\" will be ignored because of the " ^
           "presence of rationals, reals, \"Suc\", \"gcd\", or \"lcm\" " ^
           "in the problem.\n")
      else ()

    fun report_mono_failure kind ty detail =
      Refute_Core.Private.say 2
        ("Refute monotonicity " ^ kind ^ " for " ^ type_name ty ^
         (if detail = "" then "" else ": " ^ detail) ^ "\n")

    fun is_type_actually_monotonic ty =
      case List.find (fn (cached_ty, _) => Util.same_type ty cached_ty)
             (!calculus_mono_cache) of
          SOME (_, result) => result
        | NONE =>
            let
              val _ = check_deadline deadline
              val result =
                (Util.apply_within_budget (#tac_timeout context)
                   (MFMono.formulas_monotonic context binarize ty)
                   (nondef_ts, def_ts)
                 handle e as Refute_RegistrationData.Invalid _ => raise e
                      | exn => abandoned_mono_verdict
                     (fn (kind, detail) =>
                        report_mono_failure kind ty detail) exn)
              val _ = check_deadline deadline
              val _ = calculus_mono_cache :=
                (ty, result) :: !calculus_mono_cache
            in
              result
            end

    (* Unlike the scope shortcut, kind-of monotonicity deliberately lets a
       user false row block the calculus but does not let a true row force
       it.  Finitization plumbing is this helper's first caller. *)
    fun is_type_kind_of_monotonic ty =
      case MFS.mono_override (#mono mf) ty of
          SOME (SOME false) => false
        | _ => is_type_actually_monotonic ty

    val _ = enter_phase progress "scope enumeration"
    val (mono_types, nonmono_types) =
      if unique_scope then (all_types, [])
      else MFS.mono_partition_with is_type_actually_monotonic
        (#mono mf) all_types
    val forced_mono_types = List.filter (fn ty =>
      MFS.mono_override (#mono mf) ty = SOME (SOME true)) mono_types
    val inferred_mono_types = rev (List.mapPartial
      (fn (ty, true) => SOME ty | _ => NONE) (!calculus_mono_cache))

    fun report_monotonic wording types =
      if null types then ()
      else
        Refute_Core.Private.say 2
          ("The following type" ^ Util.plural_s_for_list types ^ " " ^
           wording ^ ": " ^
           String.concatWith ", " (map type_name types) ^
           ". Refute might be able to skip some scopes.\n")

    val _ = report_monotonic
      (if length forced_mono_types = 1 then "is considered monotonic"
       else "are considered monotonic") forced_mono_types
    val _ = report_monotonic "passed the monotonicity test"
      inferred_mono_types
    val deep_types = deep_data_types all_types sel_names
    val finitizable_types = finitizable_data_types context (#finitize mf)
      is_type_kind_of_monotonic all_types deep_types
    val _ = if null finitizable_types then () else
      Refute_Core.Private.say 2
        ("The following type" ^ Util.plural_s_for_list finitizable_types ^
         " can use a more precise finite encoding: " ^
         String.concatWith ", " (map type_name finitizable_types) ^ "\n")
    val adaptive = #card_mode mf = Refute_Core.IterativeDeepening
    val (fixed_skipped, fixed_scopes) =
      if adaptive then (0, [])
      else MFS.all_scopes context binarize
        (#card mf) (#max mf) (#iter mf) (#bits mf) (#bisim_depth mf)
        mono_types nonmono_types deep_types finitizable_types
    val adaptive_cursor =
      if adaptive then
        SOME (MFS.new_scope_cursor context binarize
          (#card mf) (#max mf) (#iter mf) (#bits mf) (#bisim_depth mf)
          mono_types nonmono_types deep_types finitizable_types)
      else NONE
    val batch_size =
      if #debug mf then 1 else Int.max (1, #batch_size mf)
    val pending_batches = ref (Util.chunk_list batch_size fixed_scopes)
    val source_done = ref (not adaptive)
    val fully_exhausted = ref false
    val skipped = ref fixed_skipped
    val scopes_emitted = ref (length fixed_scopes)
    val _ = bump (#emitted progress) (length fixed_scopes)
    val batch_count = ref 0

    fun refill_batches () =
      case adaptive_cursor of
          NONE => ()
        | SOME cursor =>
            let
              val _ = enter_phase progress "scope enumeration"
              val {scopes, done, stopped, skipped = newly_skipped} =
                MFS.scope_cursor_batch_with_stop cursor batch_size
                  (fn () => Refute_Core.search_expired config)
              val _ = skipped := !skipped + newly_skipped
              val _ = scopes_emitted := !scopes_emitted + length scopes
              val _ = bump (#emitted progress) (length scopes)
              val _ = pending_batches := Util.chunk_list batch_size scopes
              val _ = source_done := done
              val _ =
                if not (Refute_Core.Private.enabled 2) orelse
                   null scopes then ()
                else
                  let val scope : MFS.scope = List.last scopes in
                    Refute_Core.Private.say 2
                      ("Refute model scope frontier: " ^
                       String.concatWith ", " (map (fn (ty, card) =>
                         Parse.type_to_string ty ^ " = " ^
                         Int.toString card) (#card_assigns scope)) ^ "\n")
                  end
              val _ = if stopped then check_deadline deadline else ()
            in
              ()
            end

    fun next_scope_batch () =
      case !pending_batches of
          batch :: rest =>
            (pending_batches := rest;
             SOME (batch, !source_done andalso null rest))
        | [] =>
            if !source_done then (fully_exhausted := true; NONE)
            else (check_deadline deadline; refill_batches ();
                  next_scope_batch ())
    val real_frees = free_variables [original]
    val executable = not (Option.isSome (#qc_gate instance)) andalso
      #falsify mf andalso
      not (List.exists (fn ty =>
        MFH.is_codatatype ty orelse MFH.is_quot_type ty orelse
        MFH.is_typedef ty) all_types)
    val genuine_formula = MFM.genuine_means_genuine
      {got_all_mono_user_axioms = got_all_mono_user_axioms,
       no_poly_user_axioms = no_poly_user_axioms,
       wfs = map (fn (_, value) => value = SOME true) (#wf mf),
       sound_finitizes = sound_finitizes,
       total_consts = #total_consts mf}
    val generated_problems = ref ([] : rich_problem list)
    val generated_scopes = ref ([] : MFS.scope list)
    val checked_problems = ref ([] : rich_problem list)
    val counterexamples = ref ([] : Refute_Core.counterexample list)
    val kodkod_calls = ref 0
    val met_potential = ref 0
    val last_donno = ref 0
    (* Set when a sound problem was satisfiable but its model did not
       survive reconstruction.  Such a scope is neither refuted nor
       exhausted, so the search may not end in NoCounterexample. *)
    val discarded_sound_model = ref false
    val error_reasons = ref ([] : string list)
    val original_max_potential = Int.max (0, initial_max_potential)
    val original_max_genuine = Int.max (0, initial_max_genuine)
    val latest_state = ref
      (false, original_max_potential, original_max_genuine, 0)

    fun add_error reason =
      error_reasons := Refute_Core.add_reason (reason, !error_reasons)

    fun problem_count problems scope = length (List.filter (fn problem =>
      MFS.scopes_equivalent (#scope (metadata problem), scope)) problems)

    fun scope_checked scope =
      let
        val generated = problem_count (!generated_problems) scope
        val checked = problem_count (!checked_problems) scope
      in
        generated > 0 andalso generated = checked
      end

    fun scopes_checked () =
      length (List.filter scope_checked (!generated_scopes))

    (* progress tracking.  A result arrives for
       one problem at a time, so only the scopes equivalent to that
       problem's are looked at: counting every scope for every result made
       a large batch cost more than the solver took to finish it. *)
    fun update_checked problems indices =
      List.app (fn index =>
        if index >= 0 andalso index < length problems then
          let
            val problem = List.nth (problems, index)
            val scope = #scope (metadata problem)
            val affected = List.filter
              (fn other => MFS.scopes_equivalent (scope, other))
              (!generated_scopes)
            fun completed () =
              length (List.filter scope_checked affected)
          in
            if rich_member problem (!checked_problems) then ()
            else
              let val completed_before = completed ()
              in
                checked_problems := problem :: !checked_problems;
                bump (#completed progress) (completed () - completed_before)
              end
          end
        else ()) indices

    fun make_base (problem : rich_problem) : Refute_Core.counterexample =
      {backend = "kodkod", substrate = "kodkod",
       certainty = Refute_Core.Potential [], bindings = [], evals = [],
       cert = NONE,
       scope = SOME (#card_assigns (#scope (metadata problem))),
       model = NONE, stats = []}

    fun reconstruct_model problem bounds =
      if not (valid_instance (raw_problem problem) bounds) then
        (discarded_sound_model := true;
         add_error "Kodkodi returned a malformed model instance";
         NONE)
      else
      let
        val extension = metadata problem
        val {raw = reconstructed, certification, displayed, replay_hints,
             replay_sidecar, postprocessors} =
          MFM.reconstruct_both
          {context = context, formats = #format mf,
           scope = #scope extension, atoms = #atoms mf,
           (* [deviation from upstream] indexed table or map in place of a list scan *)
           special_funs = #entries (!(#special_funs context)),
           real_frees = real_frees,
           eval_terms = eval_terms,
           free_names = #free_names extension,
           sel_names = #sel_names extension,
           nonsel_names = #nonsel_names extension,
           rel_table = #rel_table extension,
           bounds = bounds}
        val sound = not (#unsound extension)
        val scope_has_codatatype =
          List.exists #co (#data_types (#scope extension))
        val weakened = !(#whack_weakening context)
        val reasons = if sound then
            authenticity_reasons mf got_all_mono_user_axioms
              no_poly_user_axioms (#codatatypes_ok reconstructed) @
            (if weakened then
               ["formula was semantically weakened by whack"]
             else [])
          else ["model comes from the liberal, unsound-by-design problem"]
        fun discard () = if sound then discarded_sound_model := true else ()
        val cert_deadline =
          Time.- (deadline, certification_headroom deadline started)
        fun certify_by replay_deadline =
          MFM.certify
            {executable = executable andalso not scope_has_codatatype,
             original = original,
             eval_terms = eval_terms,
             reconstruction = reconstructed,
             certification = certification,
             replay_sidecar = replay_sidecar,
             replay_hints = replay_hints,
             cex = make_base problem,
             sound = sound,
             genuine_means_genuine = genuine_formula andalso not weakened,
             reasons = reasons,
             deadline = SOME replay_deadline}
        (* A replay that ran into its deadline has its interrupt
           consumed, but the call's own timer, a moment later, can still
           land before the replay returns.  Past the replay's deadline the
           model is kept without replaying it again: that attempt stops at
           once and the model is delivered, where an escaping interrupt
           would lose it. *)
        fun past_replay_deadline () =
          Time.>= (Time.now (), cert_deadline)
        fun certify () =
          certify_by cert_deadline
          handle error as Timeout.TIMEOUT _ =>
            if past_replay_deadline () then certify_by cert_deadline
            else Exn.reraise error
               | error as Interrupt =>
            if past_replay_deadline () then certify_by cert_deadline
            else Exn.reraise error
      in
        case certify () of
            MFM.Drop => (discard (); NONE)
          | MFM.Keep semantic_cex =>
              let val cex =
                MFM.display_counterexample postprocessors displayed
                  semantic_cex
              in
                if #genuine_only config andalso
                   certainty_is_potential (#certainty cex)
                then (discard (); NONE)
                else SOME cex
              end
      end

    fun reconstruct problem bounds =
      let
        val previous = !(#phase progress)
        val _ = enter_phase progress "certification"
        val result = reconstruct_model problem bounds
      in
        enter_phase progress previous; result
      end

    fun keep_counterexample cex =
      (counterexamples := cex :: !counterexamples;
       (if #falsify mf then Refute_Core.publish_counterexamples
        else Refute_Core.publish_models) (rev (!counterexamples));
       if certainty_is_potential (#certainty cex) then
         met_potential := !met_potential + 1
       else ())

    (* The search loop talks to the solver only
       through a session ([KK.submit]) and acts on each result as it
       arrives.  A model that settles the quotas stops the search and
       cancels the session; an unsatisfiable problem completes its scope
       at once, so at a deadline everything finished counts.  When the
       solver ends by itself after a model (Kodkodi stops at the first
       model unless it was asked for several), the problems without a
       result are submitted again, as upstream's loop did. *)
    fun solve_batch state first_time problems =
      let
        val (found_really_genuine, raw_max_potential,
             raw_max_genuine, donno) = state
        val _ = last_donno := donno
        val max_potential = Int.max (0, raw_max_potential)
        val max_genuine = Int.max (0, raw_max_genuine)
        val _ = latest_state :=
          (found_really_genuine, max_potential, max_genuine, donno)
        val max_solutions = max_potential + max_genuine
          |> (fn count => if incremental then count else Int.min (1, count))
      in
        if max_solutions <= 0 then
          (found_really_genuine, 0, 0, donno)
        else if null problems then
          (found_really_genuine, max_potential, max_genuine, donno)
        else
          let
            val _ = check_deadline deadline
            val _ = kodkod_calls := !kodkod_calls + 1
            val _ = enter_phase progress "solving"
            val session = KK.submit
              {debug = #debug mf, overlord = #overlord mf,
               deadline = deadline, max_threads = #max_threads mf,
               max_file_size = #max_file_size mf,
               max_solutions = max_solutions,
               problems = map raw_problem problems}
            val indices = Portable.upto 0 (length problems - 1)
            (* Problems whose result arrived, and sound problems that need
               no solving since their liberal sibling is unsatisfiable. *)
            val received = ref ([] : int list)
            val co_indices = ref ([] : int list)
            val model_handled = ref false
            val resubmitted = ref false
            val current = ref (found_really_genuine, max_potential,
                               max_genuine, donno)

            (* A liberal problem that is unsatisfiable settles its sound
               sibling too. *)
            fun note_unsat index =
              let
                val sound_index = index - 1
              in
                if sound_index >= 0 andalso
                   #unsound (metadata (List.nth (problems, index))) andalso
                   MFS.scopes_equivalent
                     (#scope (metadata (List.nth (problems, sound_index))),
                      #scope (metadata (List.nth (problems, index))))
                then co_indices := sound_index :: !co_indices
                else ()
              end

            fun on_unsat index =
              (received := index :: !received;
               bump (#finished progress) 1;
               update_checked problems [index];
               note_unsat index;
               false)

            (* [deviation from upstream] A model kept after the call's
               deadline ends the search: carrying on would only wait for
               the solver's next result with no time left to use it. *)
            fun past_deadline () = Time.>= (Time.now (), deadline)

            (* Returns true when the search is over. *)
            fun on_sat (index, bounds) =
              let
                val (found_really_genuine, max_potential,
                     max_genuine, donno) = !current
                val _ = received := index :: !received
                val _ = bump (#finished progress) 1
                val _ = model_handled := true
                val problem = List.nth (problems, index)
                val is_liberal = #unsound (metadata problem)
                val _ = if is_liberal then update_checked problems [index]
                        else ()
                fun set state = (current := state; latest_state := state)
              in
                if is_liberal then
                  let
                    (* A certification promotion is a phase boundary this
                       port adds: do not reconstruct a later liberal model
                       (which could be merely Potential), and consume
                       exactly one genuine slot before dropping the
                       remaining unsound problems.  Upstream never promotes
                       a liberal model. *)
                    val (promoted, kept) =
                      case reconstruct problem bounds of
                          SOME cex =>
                            if certainty_is_genuine (#certainty cex) then
                              (keep_counterexample cex; (true, 1))
                            else if max_potential > 0 then
                              (keep_counterexample cex; (false, 1))
                            else (false, 0)
                        | NONE => (false, 0)
                    val found = found_really_genuine orelse promoted
                    val (max_potential, max_genuine) =
                      liberal_budget_after_models
                        {max_potential = max_potential,
                         max_genuine = max_genuine,
                         delivered = kept,
                         kept = kept, promoted = promoted,
                         incremental = incremental}
                    val _ = set (found, max_potential, max_genuine, donno)
                  in
                    (max_genuine <= 0 andalso max_potential <= 0) orelse
                    past_deadline ()
                  end
                else
                  let
                    (* [max_potential] bounds models that may be spurious
                       because the encoding behind them is unsound; only
                       the liberal problems handled above spend it.  A
                       sound problem's model is a real result whatever
                       certainty reconstruction lands on (quasi-genuine
                       for an inexact encoding, potential when kernel
                       certification got stuck), so it is always reported,
                       never discarded for want of potential budget.  Only
                       a genuine model spends a [max_genuine] slot, so the
                       search for one carries on past the weaker models it
                       reported.  This diverges from upstream, whose sound
                       branch charges a slot to every sound model it prints,
                       quasi-genuine ones included; its [num_genuine]
                       belongs to the unsound branch, where it is
                       identically 0.  [reconstruct] already raises
                       [discarded_sound_model] on each of its own rejection
                       paths. *)
                    val _ = check_deadline deadline
                    val results = case reconstruct problem bounds of
                        NONE => []
                      | SOME cex => (keep_counterexample cex; [cex])
                    val genuine_results = List.filter
                      (certainty_is_genuine o #certainty) results
                    val max_genuine = max_genuine - length genuine_results
                    val found = found_really_genuine orelse
                      not (null genuine_results)
                    (* A sound model that only reconstructs as quasi does
                       not establish a theorem, so it cannot suppress the
                       later potential/unsound search. *)
                    val max_potential = if found then 0 else max_potential
                    val _ = set (found, max_potential, max_genuine, donno)
                  in
                    (* Upstream caps sound-model harvesting at two rounds
                       per batch unconditionally (its [not first_time]
                       cut-off).  Here the cap applies only in the
                       incremental case; the 1/1 path ignores
                       [first_time]. *)
                    (max_genuine <= 0 andalso max_potential <= 0) orelse
                    (incremental andalso not first_time andalso
                     max_potential <= 0) orelse
                    past_deadline ()
                  end
              end
              handle error as Timeout.TIMEOUT _ =>
                (bump (#unused progress) 1; Exn.reraise error)
                   | error as Interrupt =>
                (bump (#unused progress) 1; Exn.reraise error)

            (* The deadline passed with problems unfinished.  With a
               positive thread limit [w], the solver started the first [w]
               unfinished problems at most, so the rest never ran. *)
            fun note_starvation () =
              let
                val unfinished = length (List.filter
                  (fn index => not (Lib.mem index (!received))) indices)
                val never_started = if #max_threads mf > 0 then
                  Int.max (0, unfinished - #max_threads mf) else 0
              in
                if never_started > 0 then
                  (bump (#starved_batches progress) 1;
                   bump (#starved_problems progress) never_started)
                else ()
              end

            fun note_cut () =
              if !resubmitted then () else note_starvation ()

            fun remaining_problems (_, max_potential, _, _) =
              Util.filter_out_indices
                (distinct_ints (!received @ !co_indices)) problems
              |> (fn values =>
                if max_potential <= 0 then
                  List.filter (not o #unsound o metadata) values
                else values)

            fun finish ending message errors =
              let
                val _ = List.app (fn (text, count) =>
                  add_solver_error progress text count) errors
                val unfinished = length (List.filter
                  (fn index => not (Lib.mem index (!received))) indices)
                val state as (found, max_potential, max_genuine, donno) =
                  !current
              in
                case ending of
                    KK.Cut => raise Timeout.TIMEOUT Time.zeroTime
                  | KK.Failed text =>
                      (add_error ("Kodkod error: " ^ text);
                       last_donno := donno + 1;
                       (found, max_potential, max_genuine, donno + 1))
                  | KK.Finished =>
                      let
                        val _ = if message = "" then () else
                          Refute_Core.Private.say 1
                            ("Kodkod warning: " ^ message ^ "\n")
                        val _ = if errors = [] then () else
                          bump (#unresolved progress) unfinished
                      in
                        if not (!model_handled) then
                          if unfinished = 0 then state
                          else
                            (add_error
                               "Kodkodi returned an incomplete result";
                             (found, max_potential, max_genuine, donno + 1))
                        else
                          let val remaining = remaining_problems state
                              val _ = resubmitted := true
                          in
                            solve_batch state false remaining
                          end
                      end
              end

            (* At the deadline, what the solver had already finished still
               counts: an unsatisfiable result completes its scope.  There
               is no time left to reconstruct a model, so one that arrives
               here is counted as unused. *)
            fun use_finished () =
              (#cancel session ();
               let
                 fun drain () =
                   case #next session () of
                       KK.Unsat index => (ignore (on_unsat index); drain ())
                     | KK.Sat _ => (bump (#unused progress) 1; drain ())
                     | KK.Ended _ => ()
               in
                 drain ()
               end) handle Interrupt => raise Interrupt | _ => ()

            fun loop () =
              case #next session () of
                  KK.Unsat index => (ignore (on_unsat index); loop ())
                | KK.Sat (index, bounds) =>
                    if on_sat (index, bounds) then
                      let val (found, max_potential, max_genuine, donno) =
                        !current
                      in
                        #cancel session ();
                        (found, Int.max (0, max_potential),
                         Int.max (0, max_genuine), donno)
                      end
                    else loop ()
                | KK.Ended {ending, message, errors} =>
                    finish ending message errors
          in
            (let val result = loop ()
             in ignore (#close session ()); result end)
            handle error =>
              (* The search's own timer may fire before the solver's
                 session reports the cut (it then interrupts the search),
                 so starvation is noted here for either. *)
              ((case error of
                    Timeout.TIMEOUT _ => (note_cut (); use_finished ())
                  | Interrupt => (note_cut (); use_finished ())
                  | _ => ());
               bump (#unused progress)
                 (#close session () handle Interrupt => raise Interrupt
                                         | _ => 0);
               Exn.reraise error)
          end
      end

    (* The search stops when the first scope of
       the window cannot fit: every other scope has at least its
       cardinalities.  It is raised with the reason the first scope was
       rejected for. *)
    val scopes_tried = ref 0
    val too_large_scopes =
      ref ([] : (bool option * MFS.scope * (string * string)) list)

    fun lost_since begun =
      bump (#dropped_msec progress)
        (Int.fromLarge (Time.toMilliseconds (Time.- (Time.now (), begun))))

    (* A scope with at least the cardinalities of a scope that was rejected
       for its size is rejected for the same size, with no work. *)
    fun known_too_large flag scope =
      Option.map (fn (_, _, (location, message)) =>
        (location, "cardinalities no smaller than those of a scope that was " ^
                   "rejected: " ^ message))
        (List.find (fn (entry, rejected, _) =>
           (entry = NONE orelse entry = flag) andalso
           scope_at_least (scope, rejected)) (!too_large_scopes))

    fun remember_too_large flag scope reason =
      too_large_scopes := (flag, scope, reason) :: !too_large_scopes

    (* [problems] is newest-first. *)
    fun add_problem flags scope (problems, donno) =
      let
        val first = !scopes_tried = 0
        val _ = scopes_tried := !scopes_tried + 1
        val _ = enter_phase progress "assembly"
        val _ = check_deadline deadline
        val params = assembly_params deadline mf all_types solver
          free_names nonsel_names nondef_us def_us need_us scope
        fun add unsound (kept, unknown) =
          let
              (* progress tracking. *)
              val _ = enter_phase progress "assembly"
              val _ = check_deadline deadline
              val begun = Time.now ()
              fun rejected_for_size reason =
                (remember_too_large (SOME unsound) scope reason;
                 reject_problem reason)
          in
            case known_too_large (SOME unsound) scope of
                SOME reason =>
                  (reject_problem reason; lost_since begun;
                   (kept, unknown + 1))
              | NONE =>
            case problem_for_scope params reject_problem rejected_for_size
                   unsound scope of
                NONE => (lost_since begun; (kept, unknown + 1))
              | SOME problem =>
                  if rich_member problem (!generated_problems) then
                    (kept, unknown)
                  else
                    (case kept of
                         previous :: _ =>
                           if KK.problems_equivalent
                                (raw_problem previous, raw_problem problem)
                           then (kept, unknown)
                           else (problem :: kept, unknown)
                       | [] => ([problem], unknown))
          end
        val begun = Time.now ()
        val too_large =
          if null flags then NONE else
          case known_too_large NONE scope of
              SOME reason => SOME reason
            | NONE =>
                (case scope_too_large params scope of
                     SOME reason =>
                       (remember_too_large NONE scope reason; SOME reason)
                   | NONE => NONE)
      in
        case too_large of
            SOME reason =>
              (reject_problem reason; lost_since begun;
               if first then raise NO_SCOPE_FITS reason
               else (problems, donno + length flags))
          | NONE =>
              List.foldl (fn (flag, result) => add flag result)
                (problems, donno) flags
      end

    fun potential_only_warning () =
      let
        val (unsound, sound) = List.partition
          (#unsound o metadata) (!generated_problems)
      in
        if not (null sound) andalso
           List.all (KK.is_problem_trivially_false o raw_problem) sound andalso
           List.exists
             (not o KK.is_problem_trivially_false o raw_problem) unsound
        then
          Refute_Core.Private.say 1
            ("Refute warning: preprocessing left only potentially spurious " ^
             "model-finder problems for the given scopes\n")
        else ()
      end

    fun run_batch last scope_batch state =
      let
        val (found, max_potential, max_genuine, donno) = state
        val flags =
          (if max_genuine > 0 then [false] else []) @
          (if max_potential > 0 orelse max_genuine > 0 then [true] else [])
        val (newest_first, donno) = List.foldl (fn (scope, result) =>
          add_problem flags scope result) ([], donno) scope_batch
        val problems = rev newest_first
        val _ = bump (#offered progress) (length problems)
        val _ = last_donno := donno
        (* Order-free: only filtered, partitioned and counted. *)
        val _ = generated_problems :=
          List.revAppend (problems, !generated_problems)
        val _ = generated_scopes := !generated_scopes @ scope_batch
        val _ = if last then potential_only_warning () else ()
      in
        solve_batch
          (found, max_potential, max_genuine, donno) true problems
      end

    fun run_batches state =
      case next_scope_batch () of
          NONE => (potential_only_warning (); state)
        | SOME (batch, last) =>
            let
              val _ = batch_count := !batch_count + 1
              val next as (_, _, max_genuine, _) =
                run_batch last batch state
              val _ = if last then fully_exhausted := true else ()
            in
              if (max_genuine > 0 orelse #2 next > 0) andalso not last then
                run_batches next
              else next
            end

    (* A clean finite scope frontier proves totality only when it covers the
       actual types, not merely every scope the user requested.  A type
       variable ranges over arbitrarily large finite types.  For ground
       types, the scope metadata records both semantic completeness and
       concreteness; forced, unsound finitization is deliberately excluded.
       Empty [all_types] is the constant-formula case and is vacuously
       covered once its (empty) frontier has been checked.  A guarded
       [min$@] occurrence (Refute_ModelFinder_HOL.sml,
       [choice_guard_inserted]) additionally vetoes totality: its [unknown]
       branch reads as "no HOL witness" only when the scope actually
       checked happened to be exact for that occurrence's domain type, which
       this static, problem-wide flag cannot tell apart from a scope that
       merely truncated one -- so no scope may certify exhaustion while it
       is set.  A [refute$unknown] that reached a value position vetoes it
       for a sharper reason ([unknown_value], Refute_ModelFinder_Kodkod.sml):
       there the unsound problem is no weaker than the sound one, so the two
       go UNSAT together and exhaustion would answer NoCounterexample to a
       proposition and its negation alike. *)
    fun total_scope_search () =
      !fully_exhausted andalso
      not (!(#choice_guard_inserted context)) andalso
      not (List.exists (#unknown_value o metadata) (!generated_problems))
        andalso
      not (List.exists Type.is_vartype all_types) andalso
      List.exists (fn scope =>
        scope_checked scope andalso
        (* exactness is of the scope, as in [exact_totality] *)
        List.all (MFS.is_exact_type scope sound_finitizes)
          all_types) (!generated_scopes)

    fun stats donno =
      [("msec", Refute_Util.elapsed_msec started),
       ("card", #card instance),
       ("scopes", !scopes_emitted),
       ("scopes_skipped", !skipped),
       ("scopes_checked", scopes_checked ()),
       ("problems", length (!generated_problems)),
       ("batches", !batch_count),
       ("kodkod_calls", !kodkod_calls),
       ("donno", donno),
       ("met_potential", !met_potential)]

    (* A word operation with no table row, met at
       a fragment carrier, was an unknown value: say which. *)
    fun unknown_op_reasons () =
      map (fn name =>
             "word operation " ^ name ^ " is not encoded: it has no table " ^
             "row, so its value is unknown")
        (rev (!(#unknown_ops context)))

    fun finalize donno outcome =
      let val final_stats = stats donno
      in
        case outcome of
            Refute_Core.Counterexample cexs =>
              Refute_Core.Counterexample (map
                (replace_stats final_stats) cexs)
          (* name the operations that were unknown values *)
          | Refute_Core.Unknown reasons =>
              Refute_Core.Unknown (reasons @ unknown_op_reasons ())
          | other => other
      end

    fun accounting_reason action =
      action ^ " after checking " ^ Int.toString (scopes_checked ()) ^
      " of " ^ Int.toString (!scopes_emitted) ^ " emitted scopes"

    fun frontier_reason () =
      case rev (!generated_scopes) of
          [] => []
        | (scope : MFS.scope) :: _ =>
            ["searched up to size: " ^
             String.concatWith ", "
               (map format_scope_assignment
                 (#card_assigns scope))]

    fun skipped_reason () =
      if !skipped = 0 then []
      else
        [Int.toString (!skipped) ^
         " invalid or duplicate scope candidates skipped"]

    fun finish state =
      let
        val (_, max_potential, max_genuine, donno) = state
        val cexs = rev (!counterexamples)
        val has_genuine = List.exists
          (certainty_is_genuine o #certainty) cexs
        val outcome =
          (* An inconclusive later scope cannot retract a model already
             certified by HOL.  Potential results retain upstream's
             inconclusive-result precedence while the genuine budget is open. *)
          if donno > 0 andalso max_genuine > 0 andalso not has_genuine then
            Refute_Core.Unknown
              (accounting_reason "model search was inconclusive" ::
               !error_reasons)
          (* Whacking replaces a term by [refute$unknown], which the
             translation treats exactly like an unrepresentable value: at
             positive polarity it becomes False and at negative polarity
             True, and the liberal sibling of each problem flips that
             choice.  An UNSAT weakened formula therefore still says
             something about the original one, so this guard is
             conservative rather than necessary; it is kept only for the
             explicitly requested [whack] optimization, never for the
             faithful ersatz substitutions that are on by default.  A model
             that was found still carries the weakening in its own reasons,
             and a HOL-certified one is independent of how the search
             reached it, so neither may be retracted here. *)
          else if !(#whack_weakening context) andalso null cexs then
            Refute_Core.Unknown
              (accounting_reason
                 "formula was semantically weakened by whack" ::
               !error_reasons)
          (* An untouched budget means the search delivered nothing, except
             when a sound problem yielded a model too weak to spend a
             genuine slot.  Such a model is still a result and must be
             reported rather than read as an exhausted search. *)
          else if null cexs andalso max_genuine = original_max_genuine andalso
                  max_potential = original_max_potential then
            if not (!fully_exhausted) then
              Refute_Core.Unknown
                [accounting_reason "adaptive scope search not exhausted"]
            else if not adaptive andalso !skipped > 0 then
              Refute_Core.Unknown
                [accounting_reason scope_limit_hint]
            else if !discarded_sound_model then
              Refute_Core.Unknown
                (accounting_reason
                   "every model found was discarded" :: !error_reasons)
            else if total_scope_search () then
              Refute_Core.NoCounterexample
            else
              Refute_Core.Unknown
                (accounting_reason
                   "no counterexample within the tested scopes" ::
                 frontier_reason ())
          else if null cexs then
            Refute_Core.Unknown
              (accounting_reason "no usable model was reconstructed" ::
               !error_reasons)
          else
            Refute_Core.Counterexample cexs
      in
        finalize donno outcome
      end

    val initial =
      (false, original_max_potential, original_max_genuine, 0)
    fun remaining (_, max_potential, max_genuine, _) =
      (Int.max (0, max_potential), Int.max (0, max_genuine))
  in
    let val final_state = run_batches initial
    in
      (finish final_state, remaining final_state)
    end
    handle Timeout.TIMEOUT _ =>
      let
        val cexs = rev (!counterexamples)
        val outcome =
          if not (null cexs) then Refute_Core.Counterexample cexs
          else
            Refute_Core.Unknown
              (accounting_reason "kodkod timed out" ::
               frontier_reason () @ skipped_reason () @ !error_reasons)
      in
        (finalize (!last_donno) outcome, remaining (!latest_state))
      end
       | NO_SCOPE_FITS (location, message) =>
      (finalize (!last_donno)
         (Refute_Core.Unknown
            ["no scope in the window can fit: " ^ message ^ " (" ^
             location ^ ")"]),
       remaining (!latest_state))
  end
  handle RESTART_AFTER_HARVEST =>
    run_instance deadline started config incremental solver
      (initial_max_potential, initial_max_genuine) reject_problem progress
      instance

fun kodkod_certainty_ceiling (config : Refute_Core.config) instances =
  let
    val mf = #mf config
    val certification_reachable =
      #falsify mf andalso
      List.exists Refute_Core.instance_is_executable instances
    (* MFM.genuine_means_genuine also demands the two user-axiom conjuncts,
       and both are functions of the theory ancestry alone, so the ceiling
       can test them here rather than overestimating past them.  An
       overestimate only costs an early stop, but here it costs every one:
       a ceiling of Genuine that the fallback path can never reach leaves
       Refute_Core.decisive permanently false. *)
    val nondefs = MFH.all_nondefs_of ()
    val (poly_nondefs, mono_nondefs) =
      List.partition MFH.is_poly_term nondefs
    val genuine_fallback_reachable =
      none_true (#wf mf) andalso none_true (#finitize mf) andalso
      #total_consts mf <> SOME true andalso
      (#user_axioms mf = SOME true orelse null mono_nondefs) andalso
      null poly_nondefs
  in
    if certification_reachable orelse genuine_fallback_reachable then
      Refute_Core.Genuine
    else
      Refute_Core.QuasiGenuine
        ["model-finder configuration precludes Genuine results"]
  end

fun run_body config instances =
  let
    val search_context = Refute_Core.search_context_for config
    val started = #started search_context
    val deadline = #deadline search_context
    val ordered = Listsort.sort (fn (left, right) =>
      Int.compare (#card left, #card right)) instances
    val mf = #mf config
    val initial_max_potential =
      if #genuine_only config then 0
      else Int.max (0, #max_potential mf)
    val initial_max_genuine = Int.max (0, #max_genuine mf)
    val incremental =
      Int.max (initial_max_potential, initial_max_genuine) >= 2
    val solver = actual_solver incremental mf
    val progress = new_progress ()
    val rejections = ref ([] : ((string * string) * int) list)
    (* Only the first [max_rejection_reasons] distinct reasons are kept; the
       rest are counted. A size rejection names the universe size, so a long
       search has one reason per scope, and keeping them all made counting
       and reporting quadratic: a search with tens of thousands of
       rejections overran its deadline by seconds. *)
    val max_rejection_reasons = 64
    val other_rejections = ref 0

    fun reject_problem reason =
      let
        fun count [] = [(reason, 1)]
          | count ((previous, n) :: rest) =
              if previous = reason then (previous, n + 1) :: rest
              else (previous, n) :: count rest
        val seen = List.exists (fn (previous, _) => previous = reason)
          (!rejections)
      in
        if seen orelse length (!rejections) < max_rejection_reasons
        then rejections := count (!rejections)
        else other_rejections := !other_rejections + 1
      end

    fun rejection_reasons () = map (fn ((location, message), count) =>
      Int.toString count ^ " problem" ^ (if count = 1 then "" else "s") ^
      " rejected: " ^ message ^ " (" ^ location ^ ")") (!rejections) @
      (if !other_rejections = 0 then []
       else [Int.toString (!other_rejections) ^
             " further problems rejected for other reasons"])

    fun report_rejections result =
      let
        val count = List.foldl (fn ((_, n), total) => total + n)
          (!other_rejections) (!rejections)
        val reasons = rejection_reasons ()
        (* Every [Unknown] starts with the phase reached and the counts, so
           that a consumer that cuts a long reason list still has them. *)
        val progress_first = progress_reason progress count
        fun with_rejections (cex : Refute_Core.counterexample) =
          replace_stats (#stats cex @ [("problems_rejected", count)]) cex
      in
        case result of
            Refute_Core.Unknown more =>
              Refute_Core.Unknown
                (progress_first ::
                 List.foldl Refute_Core.add_reason
                   (solver_error_reasons progress @ more) reasons)
          | Refute_Core.Counterexample cexs =>
              Refute_Core.Counterexample (map with_rejections cexs)
          | Refute_Core.Model models =>
              Refute_Core.Model (map with_rejections models)
          | other => other
      end
    val _ = Refute_Core.set_backend_diagnostics rejection_reasons
      report_rejections
    val typedef_reason = #1 (harvest_guard
      (List.concat (map (fn (instance : Refute_Core.instance) =>
        #original instance :: #evals instance) ordered)))

    fun search [] cexs reasons all_none _ =
          if not (null cexs) then Refute_Core.Counterexample cexs
          else if all_none then Refute_Core.NoCounterexample
          else Refute_Core.Unknown
            (if null reasons then ["model search was inconclusive"]
             else reasons)
      | search (instance :: rest) cexs reasons all_none budget =
          if Time.now () >= deadline then
            if null cexs then
              Refute_Core.Unknown ("kodkod timed out" :: reasons)
            else Refute_Core.Counterexample cexs
          else
            let
              val (result, next_budget) =
                run_instance deadline started config incremental solver
                  budget reject_problem progress instance
                handle Util.NOT_SUPPORTED reason =>
                  (Refute_Core.Unknown [reason], budget)
                     | Timeout.TIMEOUT _ =>
                  (Refute_Core.Unknown ["kodkod timed out"], budget)
              val (max_potential, max_genuine) = next_budget
            in
              case result of
                  Refute_Core.Counterexample more =>
                    let val combined = cexs @ more
                    in
                      if (max_genuine <= 0 andalso max_potential <= 0) orelse
                         #abort_potential config then
                        Refute_Core.Counterexample combined
                      else
                        search rest combined reasons false next_budget
                    end
                | Refute_Core.NoCounterexample =>
                    search rest cexs reasons all_none next_budget
                | Refute_Core.Model _ =>
                    raise Fail "internal model result before classification"
                | Refute_Core.NoModel =>
                    raise Fail "internal no-model result before classification"
                | Refute_Core.Unknown more =>
                    search rest cexs (reasons @ more) false next_budget
            end
  in
    report_rejections (case typedef_reason of
        SOME reason => Refute_Core.Unknown [reason]
      | NONE => search ordered [] [] (not (null ordered))
          (initial_max_potential, initial_max_genuine))
  end

fun run config instances =
  let
    val result =
      Refute_Core.with_search_context config (run_body config) instances
  in
    if #falsify (#mf config) then result
    else
      case result of
          Refute_Core.Counterexample models => Refute_Core.Model models
        | Refute_Core.NoCounterexample => Refute_Core.NoModel
        | other => other
  end

val kodkod_backend : Refute_Core.backend =
  {name = "kodkod", family = Refute_Core.ModelFinderFamily, weight = 50,
   configured = Refute_Forl.is_configured,
   requires = Refute_Core.AnyGoal,
   input = Refute_Core.PolyOriginal,
   certainty_ceiling = kodkod_certainty_ceiling,
   run = run,
   render = SOME render_witness}

fun register_backends () =
  Refute_Core.register_backend kodkod_backend

end
