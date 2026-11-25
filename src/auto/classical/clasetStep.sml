structure clasetStep :> clasetStep =
struct

open Abbrev HolKernel boolSyntax

val Fld = FunctionalRecordUpdate.U
val $$ = FunctionalRecordUpdate.$$

type node = clasetGoal.node
type goalpos = int

datatype rule_variant = datatype clasetReplay.rule_variant
datatype step_kind = datatype clasetReplay.step_kind
datatype hyp_subst_side = datatype clasetReplay.hyp_subst_side

type created = clasetReplay.created
val no_created : created = {terms = [], types = []}

type step_record = clasetReplay.step_record
type step = node * goalpos -> (step_record * node) seq.seq

val kind_of = clasetReplay.kind_of
val consumed_of = clasetReplay.consumed_of
val created_of = clasetReplay.created_of
val eigenvariables_of = clasetReplay.eigenvariables_of
val validation_of = clasetReplay.validation_of

fun normalize_term store tm = clasetMeta.norm store tm

fun closing_equal_normalized store left right =
  aconv left (normalize_term store right)

fun closing_equal store left =
  closing_equal_normalized store (normalize_term store left)

val normalize_rule_thm = clasetNorm.normalize_rule_thm

fun split_imp_prefix function_name arity tm =
  clasetNorm.split_imp_prefix ("clasetStep", function_name) arity tm

val normalize_assumption_thm = clasetNorm.normalize_assumption_thm
val normalize_assumption = clasetNorm.normalize_assumption

val align_conclusion = clasetNorm.align_conclusion

fun assumption_thm asm target =
  let
    val (_, theorem) = normalize_assumption asm
  in
    align_conclusion target theorem
      handle HOL_ERR _ =>
        raise mk_HOL_ERR "clasetStep" "assumption_thm"
          "the assumption does not close the target"
  end

fun supplied_major_thm store (type_substitution, term_substitution)
      major target =
  let
    val instantiated =
      Drule.INST_TY_TERM
        (term_substitution, type_substitution) (ASSUME major)
    val (_, theorem) = normalize_assumption_thm instantiated
  in
    case total (align_conclusion target) theorem of
        SOME result => result
      | NONE =>
          let
            val major' = normalize_term store major
            val (_, theorem') = normalize_assumption major'
          in
            align_conclusion target theorem'
              handle HOL_ERR _ =>
                raise mk_HOL_ERR "clasetStep" "supplied_major_thm"
                  "the selected assumption misses the major premise"
          end
  end

val nth1 = clasetNorm.nth1 ("clasetStep", "nth1")
val delete_nth = clasetNorm.delete_nth ("clasetStep", "delete_nth")

fun numbered values =
  let
    fun recurse _ [] = []
      | recurse pos (value :: rest) =
          (pos, value) :: recurse (pos + 1) rest
  in
    recurse 1 values
  end

(* Scan failed occurrences in one pull and suspend only after a result. *)
fun map_numbered_results try values =
  let
    fun next pos [] = seq.empty
      | next pos (value :: rest) =
          case try (pos, value) of
              NONE => next (pos + 1) rest
            | SOME result =>
                seq.cons result (seq.delay (fn () => next (pos + 1) rest))
  in
    seq.delay (fn () => next 1 values)
  end

datatype direct =
  Direct of
    {kind : step_kind,
     consumed : int option,
     created : created,
     eigenvariables : string list list,
     result : goal list * validation,
     children : clasetGoal.cgoal list option,
     action : clasetReplay.replay_action,
     closed : direct option list,
     store : clasetMeta.store}

fun upd_direct z =
  let
    fun from kind consumed created eigenvariables result children action
             closed store =
      {kind = kind, consumed = consumed, created = created,
       eigenvariables = eigenvariables, result = result,
       children = children, action = action, closed = closed,
       store = store}
    fun from' store closed action children result eigenvariables created
              consumed kind =
      from kind consumed created eigenvariables result children action
        closed store
    fun to f
          {kind, consumed, created, eigenvariables, result, children,
           action, closed, store} =
      f kind consumed created eigenvariables result children action closed
        store
  in
    FunctionalRecordUpdate.makeUpdate9 (from, from', to)
  end z

fun direct_with_action action (Direct fields) =
  Direct (upd_direct fields (Fld #action action) $$)

fun direct_result (Direct {result, ...}) = result
fun direct_store (Direct {store, ...}) = store
fun direct_kind (Direct {kind, ...}) = kind
fun direct_consumed (Direct {consumed, ...}) = consumed
fun direct_created (Direct {created, ...}) = created
fun direct_eigens (Direct {eigenvariables, ...}) = eigenvariables
fun direct_children (Direct {children, ...}) = children
fun direct_action (Direct {action, ...}) = action
fun direct_closed (Direct {closed, ...}) = closed

(* A step's children are stated by the tactic that returned them, and the
   engine renders every goal reduced, so a child carrying a redex is proved
   in the reduced spelling and not in the one the tactic's validation was
   built on.  This is the boundary back: each child theorem is restated in
   the tactic's own spelling, mirroring [align_conclusion], which carries a
   step's result forward to the goal the caller posed. *)
fun aligned_result (goals, validation) =
  let
    fun aligned theorems =
      if length theorems <> length goals then validation theorems
      else
        validation
          (ListPair.map
            (fn (goal, theorem) => clasetNorm.align_goal goal theorem)
            (goals, theorems))
  in
    (goals, aligned)
  end

fun tactic_direct_in ctxt kind consumed node pos tactic =
  let
    val rendered = clasetGoal.render node pos
    val result as (goals, _) =
      aligned_result (tactic rendered ctxt)
    val eigens = clasetReplay.new_free_names rendered goals
  in
    SOME
      (Direct
        {kind = kind, consumed = consumed, created = no_created,
         eigenvariables = eigens, result = result, children = NONE,
         action = clasetReplay.fixed_action_on rendered result,
         closed = map (fn _ => NONE) goals,
         store = clasetGoal.store node})
  end
  handle HOL_ERR _ => NONE

fun first_nonempty [] _ = seq.empty
  | first_nonempty (step :: rest) input =
      seq.delay
        (fn () =>
          case seq.cases (step input) of
              NONE => first_nonempty rest input
            | SOME (value, tail) => seq.cons value tail)

fun list_seq thunk = seq.delay (fn () => seq.fromList (thunk ()))

type closing_goal =
  {input : node * goalpos, asl : term list, store : clasetMeta.store,
   normalized_w : term, positioned : (int * term * term) list}

(* Normalize assumptions in positional order. Once an assumption closes
   the goal, neither the caller taking just that result nor the remaining
   assumption alternatives need the full list for a fallback method. *)
fun assumption_results store normalized_w asl fallback =
  let
    fun result (asm_pos, asm) =
      let
        fun validation [] =
              assumption_thm asm normalized_w
          | validation _ =
              raise mk_HOL_ERR "clasetStep" "assumption_results"
                "assumption validation received child theorems"
      in
        Direct
          {kind = Assumption asm_pos,
           consumed = SOME asm_pos, created = no_created,
           eigenvariables = [], result = ([], validation),
           children = SOME [],
           action = clasetReplay.assumption_action asm_pos,
           closed = [], store = store}
      end
    fun alternatives _ [] = seq.empty
      | alternatives pos (asm :: rest) =
          if aconv (normalize_term store asm) normalized_w then
            matched pos asm rest
          else alternatives (pos + 1) rest
    and matched pos asm rest =
      seq.cons (result (pos, asm))
        (seq.delay (fn () => alternatives (pos + 1) rest))

    fun scan _ [] missed = fallback (List.rev missed)
      | scan pos (asm :: rest) missed =
          let val normalized = normalize_term store asm
          in
            if aconv normalized normalized_w then
              matched pos asm rest
            else
              scan (pos + 1) rest ((pos, asm, normalized) :: missed)
          end
  in
    scan 1 asl []
  end

fun assumption_lookup positioned (_ :: _ :: _) =
      let
        val index =
          List.foldr
            (fn ((pos, asm, normalized), table) =>
              Termtab.cons_list (normalized, (pos, asm)) table)
            Termtab.empty positioned
      in
        Termtab.lookup_list index
      end
  | assumption_lookup positioned _ =
      fn term =>
        List.mapPartial
          (fn (pos, asm, normalized) =>
            if aconv normalized term then SOME (pos, asm) else NONE)
          positioned

fun contradiction_results
      ({store, normalized_w, positioned, ...} : closing_goal) =
  seq.delay
    (fn () =>
      let
        val negatives =
          List.filter (fn (_, _, normalized) => is_neg normalized)
            positioned
        val lookup = assumption_lookup positioned negatives

        fun results (neg_pos, neg_tm, normalized_neg) =
          let
            val positive = dest_neg normalized_neg
            fun make (pos_pos, pos_tm) =
              let
                fun validation [] =
                      let
                        val nthm = assumption_thm neg_tm normalized_neg
                        val pthm = assumption_thm pos_tm positive
                        val false_thm = MP (NOT_ELIM nthm) pthm
                      in
                        Drule.CONTR normalized_w false_thm
                      end
                  | validation _ =
                      raise mk_HOL_ERR "clasetStep"
                        "contradiction_results"
                        "contradiction validation has children"
              in
                Direct
                  {kind = Contradiction (neg_pos, pos_pos),
                   consumed = SOME neg_pos, created = no_created,
                   eigenvariables = [], result = ([], validation),
                   children = SOME [],
                   action =
                     clasetReplay.contradiction_action
                       (neg_pos, pos_pos),
                   closed = [], store = store}
              end
          in
            seq.map make (seq.fromList (lookup positive))
          end
      in
        seq.bind (seq.fromList negatives) results
      end)

fun mp_results
      ({input = (node, pos), asl, store, normalized_w, positioned}
       : closing_goal) =
  seq.delay
    (fn () =>
      let
        val {params, ...} = clasetGoal.goal_at node pos
        val implications =
          List.mapPartial
            (fn (imp_pos, imp_tm, normalized_imp) =>
              Option.map
                (fn sides => (imp_pos, imp_tm, normalized_imp, sides))
                (total dest_imp_only normalized_imp))
            positioned
        val lookup = assumption_lookup positioned implications

        fun results
            (imp_pos, imp_tm, normalized_imp, (antecedent, consequent)) =
          let
            fun make_matches [] = seq.empty
              | make_matches matches =
                  let
                    val child_asl = consequent :: delete_nth asl imp_pos
                    val child = (child_asl, normalized_w)
                    val child_cgoal =
                      {params = params, asl = child_asl, w = normalized_w}
                    fun make (ante_pos, ante_tm) =
                      let
                        fun validation [child_thm] =
                              let
                                val ithm =
                                  assumption_thm imp_tm normalized_imp
                                val athm =
                                  assumption_thm ante_tm antecedent
                                val consequent_thm = MP ithm athm
                                val result =
                                  Drule.PROVE_HYP
                                    consequent_thm child_thm
                              in
                                EQ_MP
                                  (ALPHA (concl result) normalized_w)
                                  result
                              end
                          | validation _ =
                              raise mk_HOL_ERR "clasetStep" "mp_results"
                                "modus ponens validation arity"
                      in
                        Direct
                          {kind =
                             ModusPonens
                               {implication = imp_pos,
                                antecedent = ante_pos},
                           consumed = SOME imp_pos,
                           created = no_created,
                           eigenvariables = [[]],
                           result = ([child], validation),
                           children = SOME [child_cgoal],
                           action =
                             clasetReplay.mp_action
                               {implication = imp_pos,
                                antecedent = ante_pos},
                           closed = [NONE], store = store}
                      end
                  in
                    seq.map make (seq.fromList matches)
                  end
          in
            make_matches (lookup antecedent)
          end
      in
        seq.bind (seq.fromList implications) results
      end)

fun closing_results methods (input as (node, pos)) =
  seq.delay
    (fn () =>
      let
        val (asl, w) = clasetGoal.render node pos
      in
        if null asl then seq.empty
        else
          let
            val store = clasetGoal.store node
            val normalized_w = normalize_term store w
            fun fallback positioned =
              first_nonempty methods
                {input = input, asl = asl, store = store,
                 normalized_w = normalized_w, positioned = positioned}
          in
            assumption_results store normalized_w asl fallback
          end
      end)

val assume_or_contradiction =
  closing_results [contradiction_results]

val assume_or_eq_mp =
  closing_results [contradiction_results, mp_results]

fun tag_equal
  ({weight = weight1, index = index1} : clasetLib.tag,
   {weight = weight2, index = index2} : clasetLib.tag) =
  weight1 = weight2 andalso index1 = index2

fun dedup_tagged [] = []
  | dedup_tagged (entry :: rest) =
      let
        fun drop_same [] = []
          | drop_same (next :: tail) =
              if tag_equal (#1 entry, #1 next) then drop_same tail
              else next :: tail
      in
        entry :: dedup_tagged (drop_same rest)
      end

(* The index is keyed on the rules as stated, and [x IN P] and [P x] are
   one proposition indexed two ways: a rule stated about [IN] sits under
   that constant, where an applied goal atom never reaches it, and a rule
   stated applied sits under its own head, where a membership goal atom
   never reaches it.  So each lookup is made in both spellings as well as
   as posed; the unifier decides what actually matches, and
   [candidate_order] sorts the answers together.  A rule that mixes the
   two spellings in one conclusion is still reached only as it is
   written.

   The crossing answers only where the spelling is forced, an
   application of a variable, so over a compound set -- [x IN f p]
   against [f p x] -- it leaves both forms alone and neither of them
   reaches the other.  [crossed_conv] and [applied_conv] are the two
   total spellings; asking for both is what makes "both spellings" true
   there.  [clasetGoal.lookup_spellings] supplies the forms. *)
fun candidates derive store mode part forms =
  dedup_tagged
    (clasetLib.classical_candidates
      {unify = mode = clasetUnify.Unify, derive = derive,
       query_metas = HOLset.fromList Term.compare o clasetMeta.metas_of store,
       flexible_type = clasetMeta.is_tymeta} part forms)

fun type_variables th =
  HOLset.listItems
    (HOLset.fromList Type.compare
      (List.concat (map type_vars_in_term (concl th :: hyp th))))

fun freshen_prepared node pos (canonical, types) =
  let
    val store0 = clasetGoal.store node
    val params = #params (clasetGoal.goal_at node pos)

    fun add_type (ty, (substitution, metas, store)) =
      let val (meta, store') = clasetMeta.new_tymeta store
      in
        ({redex = ty, residue = meta} :: substitution,
         meta :: metas, store')
      end

    val (type_substitution, rev_types, store1) =
      List.foldl add_type ([], [], store0) types
    val typed = INST_TYPE type_substitution canonical
    val (variables, _) = strip_forall (concl typed)

    fun add_term (variable, (metas, store)) =
      let
        val (meta, store') =
          clasetMeta.new_meta
            {allow = params, ty = type_of variable} store
      in
        (meta :: metas, store')
      end

    val (rev_terms, store2) =
      List.foldl add_term ([], store1) variables
    val terms = List.rev rev_terms
    val core = Drule.SPECL terms typed
    val (premises, conclusion) = strip_imp_only (concl core)
  in
    {core = core, premises = premises, conclusion = conclusion,
     metas = {terms = terms, types = List.rev rev_types},
     store = store2}
  end

(* Preparation is shared across major premises. Each application still
   gets fresh rule metavariables and starts with the parent store. *)
fun prepare_rule is_elim theorem =
  Portable.HOLSusp.delay
    (fn () =>
      let
        val kind = if is_elim then clasetRules.Elim else clasetRules.Intro
        val canonical = clasetRules.canonical_rule_of kind theorem
      in
        (canonical, type_variables canonical)
      end)

fun same_term_meta left right =
  is_var left andalso is_var right andalso
  fst (dest_var left) = fst (dest_var right)

fun unresolved_in_premises store
  ({terms, types} : clasetUnify.rule_metas) premises =
  let
    fun created_term meta =
      List.exists (fn created => same_term_meta created meta) terms
    fun created_type ty =
      List.exists (fn created => clasetMeta.same_tymeta created ty) types
    fun unresolved premise =
      let val normalized = normalize_term store premise
      in
        (not (null terms) andalso
         List.exists created_term
           (clasetMeta.metas_of_normalized store normalized)) orelse
        (not (null types) andalso
         List.exists created_type (type_vars_in_term normalized))
      end
  in
    not (null terms andalso null types) andalso List.exists unresolved premises
  end

fun ground_created store
  ({terms, types} : clasetUnify.rule_metas) =
  let
    fun ground_type (meta, current) =
      let val normalized = clasetMeta.norm_type current meta
      in
        if clasetMeta.same_tymeta meta normalized then
          (case clasetMeta.bind_ty (meta, Type.bool) current of
               SOME next => next
             | NONE => current)
        else current
      end
    val typed_store = List.foldl ground_type store types

    fun ground_term (meta, current) =
      let val normalized = clasetMeta.walk current meta
      in
        if same_term_meta meta normalized then
          let
            val arbitrary =
              mk_arb (clasetMeta.norm_type current (type_of meta))
          in
            case clasetMeta.bind (meta, arbitrary) current of
                SOME next => next
              | NONE => current
          end
        else current
      end
  in
    List.foldl ground_term typed_store terms
  end

(* The backward and the forward rule paths finish an application the same
   way: refuse a safe step that left premise variables unfixed, ground what
   the match created, instantiate the rule and discharge the hypotheses it
   carries against the goal's assumptions.  Keeping it here is what stops
   the two grounding policies from drifting apart.  [note_skip] is their
   only difference -- only the backward path traces the refusal. *)
fun settle_rule mode (core : thm) metas asl note_skip residual_terms store =
  let
    val _ =
      case mode of
          clasetUnify.Match =>
            if unresolved_in_premises store metas residual_terms
            then (note_skip (); raise Match)
            else ()
        | clasetUnify.Unify => ()
    val final_store =
      case mode of
          clasetUnify.Match => ground_created store metas
        | clasetUnify.Unify => store
    val substitutions as (type_substitution, term_substitution) =
      clasetMeta.collapse final_store
    val instantiated =
      Drule.INST_TY_TERM (term_substitution, type_substitution) core
    val normalized_rule0 = normalize_rule_thm instantiated

    fun matching_assumption _ [] = NONE
      | matching_assumption hypothesis assumptions =
          List.find (closing_equal final_store hypothesis) assumptions

    fun align_hypothesis (hypothesis, current) =
      case matching_assumption hypothesis asl of
          NONE => raise Match
        | SOME assumption =>
            Drule.PROVE_HYP
              (assumption_thm assumption hypothesis) current
  in
    (final_store,
     List.foldl align_hypothesis normalized_rule0 (hyp normalized_rule0),
     substitutions)
  end

fun cgoal_render store ({asl, w, ...} : clasetGoal.cgoal) =
  (map (normalize_term store) asl, normalize_term store w)

fun rule_validation normalized_rule supplied rebuilds target child_thms =
  if length child_thms <> length rebuilds then
    raise mk_HOL_ERR "clasetStep" "rule_validation"
      "rule validation arity"
  else
    let
      val premise_thms =
        ListPair.map
          (fn (data, theorem) =>
            clasetReplay.rebuild_exact_prefix data theorem)
          (rebuilds, child_thms)
      val result =
        Drule.LIST_MP (supplied @ premise_thms) normalized_rule
    in
      align_conclusion target result
    end

(* The rebuild of a child that took its premise's whole prefix: the child's
   last parameters are the premise's bound variables. *)
fun full_prefix_rebuild (({params, ...} : clasetGoal.cgoal), premise) =
  let
    val (bounds, body) = strip_forall premise
    val fresh = List.drop (params, length params - length bounds)
    val substitution =
      ListPair.map (fn (bound, variable) =>
        {redex = bound, residue = variable}) (bounds, fresh)
    val (antecedents, _) = strip_imp_only (Term.subst substitution body)
  in
    {fresh = fresh, assumptions = antecedents, premise = premise}
  end

fun replay_theorem normalized_rule store =
  let
    val (type_substitution, term_substitution) = clasetMeta.collapse store
  in
    Drule.INST_TY_TERM
      (term_substitution, type_substitution) normalized_rule
  end

fun theorem_equal left right =
  aconv (concl left) (concl right) andalso
  Lib.list_eq aconv (hyp left) (hyp right)

(* The derived-conclusion index supplies declarations in claset order.
   Replay needs the first matching hypotheses and variant. *)
fun rule_origin cs duplicated theorem =
  let
    fun inspect ({spec, thm = original, info, ...} : clasetLib.aesop_rule) =
      let
        val {rl = (plain, swapped), dup_rl = (duplicate, dup_swapped)} = info
        val made =
          case #kind spec of clasetRules.Dest => MakeElim | _ => Plain
      in
        if theorem_equal theorem plain andalso not duplicated then
          SOME (original, made)
        else if Option.getOpt
                  (Option.map (theorem_equal theorem) swapped, false)
                andalso not duplicated
        then SOME (original, Swapped)
        else if theorem_equal theorem duplicate then
          SOME (original, Duplicate)
        else if Option.getOpt
                  (Option.map (theorem_equal theorem) dup_swapped, false)
        then SOME (original, Duplicate)
        else if theorem_equal theorem plain then SOME (original, made)
        else NONE
      end
    fun search [] = (theorem, if duplicated then Duplicate else Plain)
      | search (rule :: rest) =
          (case inspect rule of
               SOME result => result
             | NONE => search rest)
  in
    search (clasetLib.rules_for_derived_concl cs (concl theorem))
  end

datatype prefix_policy = FullPrefixes | ExactBlastPrefixes

fun minor_prefixes policy is_elim premises =
  case policy of
      FullPrefixes => NONE
    | ExactBlastPrefixes =>
        let val minors = if is_elim then tl premises else premises
        in SOME (map clasetReplay.exact_prefix_descriptor minors) end

(* A Match step that would leave premise variables unfixed is refused, and
   the refusal is noted at the trace level given.  The safe cascades, which
   run in a context, read classical.trace only when a refusal is noted, off
   the cascade's path.  Rules supplied by aesop note it at aesop.trace.
   Unify steps never refuse; the forward path refuses silently, noting
   nothing. *)
fun refusal_message () = "skipping safe rule with unfixed premise variables"

fun level_note level () = traceUtil.trace level 1 refusal_message

fun skip_note ctxt () =
  level_note (traceUtil.level_of clasetReplay.tracer ctxt) ()

fun no_note () = ()

fun try_rule note_skip policy mode cs duplicated node pos
    (tag, (is_elim, theorem)) prepared assumption =
  let
    val (asl, w) = clasetGoal.render node pos
    val fresh = freshen_prepared node pos (Portable.HOLSusp.force prepared)
    val prefixes = minor_prefixes policy is_elim (#premises fresh)
    val config = {mode = mode, rule_metas = #metas fresh}
    val store1 =
      case clasetUnify.unify (#store fresh) config
        (#conclusion fresh, w)
      of
          NONE => raise Match
        | SOME store => store
    val (consumed, supplied, remaining, store2) =
      if is_elim then
        let
          val (assumption_pos, major) = valOf assumption
          val rule_major = hd (#premises fresh)
          val store =
            case clasetUnify.unify store1 config (rule_major, major) of
                NONE => raise Match
              | SOME result => result
        in
          (SOME assumption_pos, [major], tl (#premises fresh), store)
        end
      else (NONE, [], #premises fresh, store1)
    val residual_terms = remaining @ hyp (#core fresh)
    val (final_store, normalized_rule, substitutions) =
      settle_rule mode (#core fresh) (#metas fresh) asl note_skip
        residual_terms store2
    val (all_premises, _) =
      split_imp_prefix "try_rule" (length (#premises fresh))
        (concl normalized_rule)
    val normalized_premises =
      if is_elim then
        (case all_premises of
             _ :: premises => premises
           | [] =>
               raise mk_HOL_ERR "clasetStep" "try_rule"
                 "an elimination rule has no major premise")
      else all_premises
    val working = clasetGoal.set_store final_store node
    val (children, child_store, rebuilds) =
      case prefixes of
          NONE =>
            let
              val (children, child_store) =
                clasetGoal.children working
                  {pos = pos, premises = normalized_premises,
                   consumed = consumed}
            in
              (children, child_store, NONE)
            end
        | SOME descriptors =>
            let
              val (children, child_store, data) =
                clasetGoal.exact_blast_children working
                  {pos = pos, premises = normalized_premises,
                   prefixes = descriptors, consumed = consumed}
            in
              (children, child_store, SOME data)
            end
    val child_goals = map (cgoal_render child_store) children
    val supplied_thms =
      case (is_elim, assumption) of
          (true, SOME (_, major)) =>
            [supplied_major_thm final_store substitutions major
               (hd all_premises)]
        | _ => []
    val target = normalize_term child_store w
    val validation =
      case rebuilds of
          NONE =>
            (fn child_thms =>
              rule_validation normalized_rule supplied_thms
                (ListPair.map full_prefix_rebuild
                  (children, normalized_premises))
                target child_thms)
        | SOME data =>
            rule_validation normalized_rule supplied_thms data target
    val old_params = #params (clasetGoal.goal_at node pos)
    fun child_eigens ({params, ...} : clasetGoal.cgoal) =
      map (fst o dest_var)
        (List.filter
          (fn parameter =>
            not (tmem parameter old_params))
          params)
    val new_eigens = map child_eigens children
    val created = #metas fresh
    val (original, variant) = rule_origin cs duplicated theorem

    fun replay_instance store =
      {theorem = replay_theorem normalized_rule store, elim = is_elim,
       consumed = consumed, parameters = old_params,
       eigenvariables = new_eigens}
    fun blast_replay_instance descriptors store =
      {theorem = replay_theorem normalized_rule store, elim = is_elim,
       consumed = consumed, parameters = old_params,
       eigenvariables = new_eigens, prefixes = descriptors}
    val action =
      case prefixes of
          NONE => clasetReplay.rule_action replay_instance
        | SOME descriptors =>
            clasetReplay.blast_rule_action
              (blast_replay_instance descriptors)
  in
    Direct
      {kind =
         RuleApplication
           {original = original, theorem = theorem,
            variant = variant, elim = is_elim},
       consumed = consumed, created = created,
       eigenvariables = new_eigens,
       result = (child_goals, validation), children = SOME children,
       action = action,
       closed = map (fn _ => NONE) children, store = child_store}
  end
  handle Match => raise Match
       | HOL_ERR _ => raise Match
       | Empty => raise Match

(* The major premise is the last immediate one and comes fixed from the
   caller; the earlier premises are resolved against the assumptions here.
   Committing to their first unifier would hide every conclusion but one of
   a rule with several premises, so each earlier premise contributes all of
   its choices and the combinations are enumerated lazily: a caller that
   inspects only the leading alternatives pays for those alone.  Each
   result carries the assumption it adds, for the duplicate filter in
   [forward_rule_results]. *)
fun try_forward charge mode {source, prepared} immediate positioned node pos
    (major_pos, major) =
  let
    val (asl, w) = clasetGoal.render node pos
    val fresh = freshen_prepared node pos (Portable.HOLSusp.force prepared)
    val all_premises = #premises fresh
    val _ =
      if immediate > 0 andalso immediate <= length all_premises then ()
      else raise Match
    val immediate_premises = List.take (all_premises, immediate)
    val major_premise = List.last immediate_premises
    val config = {mode = mode, rule_metas = #metas fresh}
    val _ = charge ()
    val major_store =
      case clasetUnify.unify (#store fresh) config
        (major_premise, major)
      of
          NONE => raise Match
        | SOME store => store
    val earlier = List.take (immediate_premises, immediate - 1)
    val residual_terms =
      List.drop (all_premises, immediate) @
      [#conclusion fresh] @ hyp (#core fresh)

    fun build (positions, matched_store) =
      let
        val (final_store, normalized_rule, substitutions) =
          settle_rule mode (#core fresh) (#metas fresh) asl no_note
            residual_terms matched_store
        val (normalized_premises, _) =
          strip_imp_only (concl normalized_rule)
        val supplied =
          ListPair.map
            (fn (premise, position) =>
              supplied_major_thm final_store substitutions
                (nth1 asl position) premise)
            (List.take (normalized_premises, immediate), positions)
        val forward = Drule.LIST_MP supplied normalized_rule
        val added = concl forward
        val parent = clasetGoal.goal_at node pos
        val child = clasetGoal.cons_assumption added parent
        val child_goal = cgoal_render final_store child
        val target = normalize_term final_store w

        fun validation [child_thm] =
              let val result = Drule.PROVE_HYP forward child_thm
              in align_conclusion target result end
          | validation _ =
              raise mk_HOL_ERR "clasetStep" "try_forward"
                "forward validation arity"

        fun replay_instance store =
          {theorem = replay_theorem normalized_rule store,
           immediate = immediate,
           assumptions = positions}
      in
        (added,
         Direct
           {kind =
              RuleApplication
                {original = source, theorem = source,
                 variant = MakeElim, elim = true},
            consumed = NONE, created = #metas fresh,
            eigenvariables = [[]],
            result = ([child_goal], validation),
            children = SOME [child],
            action = clasetReplay.forward_rule_action replay_instance,
            closed = [NONE], store = final_store})
      end
    (* The stack is the multi-premise cursor.  Charge before removing a
       candidate from its frame, so a cutoff resumes at that comparison.
       Exact matches precede unification matches as in the old sequence. *)
    datatype work =
        Expand of term list * int list * clasetMeta.store
      | CheckExact of
          term * term Portable.HOLSusp.susp *
          term list * int list * clasetMeta.store *
          (int * term) list * (int * term) list
      | CheckUnify of
          term * term list * int list * clasetMeta.store *
          (int * term) list
    val pending = ref [Expand (earlier, [], major_store)]

    fun next_assignment () =
      case !pending of
          [] => NONE
        | Expand ([], positions, store) :: rest =>
            (pending := rest;
             SOME (List.rev positions @ [major_pos], store))
        | Expand (premise :: later, positions, store) :: rest =>
            let
              (* The store is fixed throughout this exact scan. Delay
                 normalization until its first charged comparison. *)
              val normalized = Portable.HOLSusp.delay
                (fn () => normalize_term store premise)
            in
              pending :=
                CheckExact
                  (premise, normalized, later, positions, store,
                   Portable.HOLSusp.force positioned, []) :: rest;
              next_assignment ()
            end
        | CheckExact
            (premise, _, later, positions, store, [], mismatched) ::
            rest =>
            (pending :=
               CheckUnify
                 (premise, later, positions, store,
                  List.rev mismatched) :: rest;
             next_assignment ())
        | CheckExact
            (premise, normalized, later, positions, store,
             (position, assumption) :: remaining, mismatched) :: rest =>
            let
              val _ = charge ()
              val equal = closing_equal_normalized store
                (Portable.HOLSusp.force normalized) assumption
              val tail =
                CheckExact
                  (premise, normalized, later, positions, store, remaining,
                   if equal then mismatched
                   else (position, assumption) :: mismatched) :: rest
            in
              pending :=
                if equal then
                  Expand (later, position :: positions, store) :: tail
                else tail;
              next_assignment ()
            end
        | CheckUnify (_, _, _, _, []) :: rest =>
            (pending := rest; next_assignment ())
        | CheckUnify
            (premise, later, positions, store,
             (position, assumption) :: remaining) :: rest =>
            let
              val _ = charge ()
              val next =
                clasetUnify.unify store config (premise, assumption)
              val tail =
                CheckUnify
                  (premise, later, positions, store, remaining) :: rest
            in
              pending :=
                (case next of
                     NONE => tail
                   | SOME next_store =>
                       Expand
                         (later, position :: positions, next_store) ::
                       tail);
              next_assignment ()
            end

    fun next_result () =
      case next_assignment () of
          NONE => NONE
        | SOME assignment =>
            (case total build assignment of
                 NONE => next_result ()
               | SOME result => SOME result)
  in
    seq.fresult next_result
  end
  handle Match => raise Match
       | HOL_ERR _ => raise Match
       | Empty => raise Match

fun forward_rule_results charge mode rule immediate (node, pos) =
  let
    val assumptions = #asl (clasetGoal.goal_at node pos)
    val parent_store = clasetGoal.store node
    (* Only the earlier immediate premises scan the rendered assumptions. *)
    val positioned = Portable.HOLSusp.delay
      (fn () => numbered (#1 (clasetGoal.render node pos)))

    val remaining =
      ref (numbered assumptions)
    val current = ref (NONE : (term * direct) seq.seq option)

    fun attempts () =
      case !current of
          SOME candidates =>
            (case seq.cases candidates of
                 SOME (candidate, rest) =>
                   (current := SOME rest; SOME candidate)
               | NONE =>
                   (current := NONE; attempts ()))
        | NONE =>
            (case !remaining of
                 [] => NONE
               | (position, major) :: rest =>
                   let
                     val next =
                       (SOME
                         (try_forward charge mode rule immediate positioned
                           node pos (position, major))
                        handle Match => NONE)
                   in
                     remaining := rest;
                     current := next;
                     attempts ()
                   end)

    (* Rule-local metas are fresh for every alternative.  Only bindings
       of pre-existing metas change the search state seen by the parent. *)
    type effect =
      {terms : (term * term) list,
       types : (hol_type * hol_type) list}

    fun effect_of store
        ({terms = created_terms, types = created_types} :
           clasetUnify.rule_metas) : effect =
      let
        val {terms, types} = clasetMeta.bindings store
        fun original_term (meta, _) =
          not (List.exists (clasetMeta.same_meta meta) created_terms)
        fun original_type (tymeta, _) =
          not (List.exists (clasetMeta.same_tymeta tymeta)
            created_types)
      in
        {terms =
           map (fn (meta, value) =>
             (meta, normalize_term store value))
             (List.filter original_term terms),
         types =
           map (fn (tymeta, value) =>
             (tymeta, clasetMeta.norm_type store value))
             (List.filter original_type types)}
      end

    fun same_effect (left : effect) (right : effect) =
      ListPair.allEq
        (fn ((left_meta, left_value),
             (right_meta, right_value)) =>
          clasetMeta.same_meta left_meta right_meta andalso
          aconv left_value right_value)
        (#terms left, #terms right) andalso
      ListPair.allEq
        (fn ((left_meta, left_value),
             (right_meta, right_value)) =>
          clasetMeta.same_tymeta left_meta right_meta andalso
          Type.compare (left_value, right_value) = EQUAL)
        (#types left, #types right)

    (* Index conclusions in the parent store. Delay insertion until the
       next comparison so a single result never needs a normalized key. *)
    val seen = ref (Portable.HOLSusp.delay (fn () => Termtab.empty))

    fun remember added store created =
      let
        val index = Portable.HOLSusp.force (!seen)
        val effect = Portable.HOLSusp.delay (fn () => effect_of store created)
        val normalized =
          Portable.HOLSusp.delay (fn () => normalize_term parent_store added)
        fun conclusion () = Portable.HOLSusp.force normalized
        fun duplicate prior =
          same_effect (Portable.HOLSusp.force effect)
            (Portable.HOLSusp.force prior)
      in
        if Termtab.is_empty index orelse
           not (List.exists duplicate
                  (Termtab.lookup_list index (conclusion ())))
        then
          (seen := Portable.HOLSusp.delay
             (fn () => Termtab.cons_list (conclusion (), effect) index);
           true)
        else false
      end

    (* Hold a produced candidate across a cutoff. *)
    val candidate_pending = ref (NONE : (term * direct) option)

    fun already_assumed _ _ [] = false
      | already_assumed store added assumptions =
          List.exists (closing_equal store added) assumptions

    fun distinct () =
      case !candidate_pending of
          NONE =>
            (case attempts () of
                 NONE => NONE
               | SOME candidate =>
                   (candidate_pending := SOME candidate;
                    distinct ()))
        | SOME (added, direct) =>
            (charge ();
             candidate_pending := NONE;
             let
               val store = direct_store direct
             in
               if not (already_assumed store added assumptions) andalso
                  remember added store (direct_created direct)
               then SOME direct
               else distinct ()
             end)
  in
    seq.fresult distinct
  end

(* [derive] runs before each lazy constructor pair a Unify lookup derives
   afresh; see [clasetLib.classical_candidates]. *)
fun rule_candidates derive mode part (node, pos) =
  candidates derive (clasetGoal.store node) mode part
    (clasetGoal.lookup_spellings node pos)

fun rule_applications note_skip mode cs duplicated get_tagged (node, pos) =
  seq.delay
    (fn () =>
      let
        val (asl, _) = clasetGoal.render node pos
        val tagged = get_tagged ()
        val majors = Portable.HOLSusp.delay (fn () => numbered asl)

        fun applications (entry as (_, (is_elim, theorem))) =
          let
            val prepared = prepare_rule is_elim theorem
            val attempt = total
              (try_rule note_skip FullPrefixes mode cs duplicated
                node pos entry prepared)
            fun eliminations [] = seq.empty
              | eliminations (major :: rest) =
                  seq.delay
                    (fn () =>
                      case attempt (SOME major) of
                          SOME result => seq.cons result (eliminations rest)
                        | NONE => eliminations rest)
          in
            if is_elim then
              eliminations (Portable.HOLSusp.force majors)
            else
              seq.delay
                (fn () =>
                  case attempt NONE of
                      SOME result => seq.result result
                    | NONE => seq.empty)
          end

        fun entries [] = seq.empty
          | entries (entry :: rest) =
              seq.delay
                (fn () =>
                  case seq.cases (applications entry) of
                      NONE => entries rest
                    | SOME (result, tail) =>
                        seq.cons result (seq.append tail (entries rest)))
      in
        entries tagged
      end)

fun rule_results_with derive note_skip mode cs duplicated part weight_filter
      input =
  rule_applications note_skip mode cs duplicated
    (fn () => List.filter (weight_filter o #1)
      (rule_candidates derive mode part input)) input

fun rule_results note_skip =
  rule_results_with listUtil.no_checkpoint note_skip

datatype exact_major_selector = AllMajors | ExactMajor of int option

(* Keep the legacy exact-rule path just as lazy as it was before selectors:
   introductions do not inspect the goal until their delayed attempt is
   pulled, and eliminations walk the original assumption list incrementally.
   Only the additive exact selector indexes an assumption eagerly. *)
fun exact_rule_attempts attempt selector elim node pos =
  case (selector, elim) of
      (AllMajors, false) => attempt NONE
    | (AllMajors, true) =>
        let
          fun eliminations _ [] = seq.empty
            | eliminations assumption_pos (major :: rest) =
                seq.append
                  (attempt (SOME (assumption_pos, major)))
                  (seq.delay
                    (fn () =>
                      eliminations (assumption_pos + 1) rest))
        in
          eliminations 1 (#asl (clasetGoal.goal_at node pos))
        end
    | (ExactMajor NONE, false) => attempt NONE
    | (ExactMajor (SOME major), true) =>
        let val assumptions = #asl (clasetGoal.goal_at node pos)
        in
          if major > 0 andalso major <= length assumptions then
            attempt (SOME (major, nth1 assumptions major))
          else seq.empty
        end
    | _ => seq.empty

fun supplied_rule_results_with charge note_skip selector policy mode cs
    {theorem, elim} (node, pos) =
  let
    val tag : clasetLib.tag = {weight = 0, index = 0}
    val entry = (tag, (elim, theorem))
    val prepared = prepare_rule elim theorem

    fun attempt assumption =
      seq.delay
        (fn () =>
          (charge ();
           case total
            (fn () =>
              try_rule note_skip policy mode cs false node pos entry prepared
                assumption) ()
          of
              SOME direct => seq.result direct
            | NONE => seq.empty))

  in
    exact_rule_attempts attempt selector elim node pos
  end

fun exact_rule_results_with selector cs specification =
  supplied_rule_results_with (fn () => ()) no_note
    selector ExactBlastPrefixes
    clasetUnify.Unify cs specification

fun exact_rule_results cs specification =
  exact_rule_results_with AllMajors cs specification

fun all_weights _ = true
fun weight_is expected ({weight, ...} : clasetLib.tag) = weight = expected

fun is_product_type ty =
  case total Type.dest_type ty of
      SOME ("prod", [_, _]) => true
    | _ => false

(* Isabelle splits the whole parameter prefix of a subgoal at once, so the
   test looks through the leading universals and not only at the first. *)
fun paired_forall term =
  case total dest_forall term of
      SOME (bound, body) =>
        is_product_type (type_of bound) orelse paired_forall body
    | NONE => false

(* Isabelle splits the subgoal's parameters, and a HOL4 subgoal's free
   variables are exactly those: the goal claims its conclusion for all of
   them.  Reading the step off the engine's own parameter list instead
   would not survive the tactics built on it -- CLARIFY re-enters from a
   plain goal at each step, so the variable a rule stripped out of its
   premise is an ordinary free variable by the time the next step looks.
   Metavariables are excluded: they stand for the schematic variables
   Isabelle's parameter split never touches, and taking one apart would
   commit the search to a pair before it has chosen the witness. *)
fun splittable_variable (asl, w) =
  let
    fun splittable variable =
      is_product_type (type_of variable) andalso
      not (clasetMeta.is_meta variable)
  in
    List.find splittable (free_varsl (w :: asl))
  end

fun builtin_results_in ctxt (node, pos) =
  let
    val rendered as (_, w) = clasetGoal.render node pos

    fun make initial_store kind action tactic =
      case total (fn () => tactic rendered ctxt) () of
          NONE => seq.empty
        | SOME (result as (goals, _)) =>
            let
              val lifted = clasetGoal.lift_children node pos goals
              val children = map #1 lifted
              val child_params = map #2 lifted
              val store =
                case clasetGoal.register_eigens
                       (List.concat child_params) initial_store of
                    SOME registered => registered
                  | NONE =>
                      raise mk_HOL_ERR "clasetStep" "builtin_results"
                        "a generated parameter is not fresh"
            in
              seq.result
                (Direct
                  {kind = kind, consumed = NONE, created = no_created,
                   eigenvariables =
                     map (map (fst o dest_var)) child_params,
                   result = result, children = SOME children,
                   action = action,
                   closed = map (fn _ => NONE) children,
                   store = store})
            end
  in
    if is_imp_only w then
      make (clasetGoal.store node) Disch clasetReplay.disch_action
        Tactic.DISCH_TAC
    else if paired_forall w then
      make (clasetGoal.store node) SplitPaired
        clasetReplay.split_paired_action clasetReplay.SPLIT_PAIRED_TAC
    else if Option.isSome (splittable_variable rendered) then
      let
        val target = valOf (splittable_variable rendered)
        val base = fst (dest_var target)
        val (first_type, second_type) =
          pairSyntax.dest_prod (type_of target)
        val (left, store) =
          clasetGoal.fresh_eigen node (mk_var (base ^ "_1", first_type))
        val (right, _) =
          clasetGoal.fresh_eigen node (mk_var (base ^ "_2", second_type))
        val names =
          {variable = base, left = fst (dest_var left),
           right = fst (dest_var right)}
      in
        make store SplitPaired (clasetReplay.split_paired_var_action names)
          (clasetReplay.SPLIT_PAIRED_VAR_TAC names)
      end
    else if is_forall w then
      let
        val (bound, _) = dest_forall w
        val (fresh, store) = clasetGoal.fresh_eigen node bound
        val name = fst (dest_var fresh)
      in
        make store Gen (clasetReplay.gen_action name)
          (clasetReplay.GEN_NAMED_TAC name)
      end
    else seq.empty
  end

fun swapped_builtin_results_in ctxt (node, pos) =
  list_seq
    (fn () =>
      let
        val (asl, _) = clasetGoal.render node pos
        val store = clasetGoal.store node

        fun attempt (asm_pos, assumption) =
          let
            val positive = total dest_neg assumption
            val supported =
              case positive of
                  SOME tm =>
                    can dest_imp_only tm orelse can dest_forall tm
                | NONE => false
          in
            if supported then
              case tactic_direct_in ctxt (SwappedBuiltin asm_pos)
                (SOME asm_pos) node pos
                (clasetReplay.SWAPPED_BUILTIN_TAC store asm_pos)
              of
                  NONE => NONE
                | SOME direct =>
                    SOME
                      (direct_with_action
                        (clasetReplay.swapped_builtin_action asm_pos)
                        direct)
            else NONE
          end
      in
        List.mapPartial attempt (numbered asl)
      end)

fun has_metavariables node pos =
  let
    val (asl, w) = clasetGoal.render node pos
  in
    List.exists clasetMeta.is_meta (free_varsl (w :: asl)) orelse
    List.exists clasetMeta.is_tymeta
      (List.concat (map type_vars_in_term (w :: asl)))
  end

fun internal_hyp_subst_results_in ctxt (node, pos) =
  let
    val rendered = clasetGoal.render node pos
    val initial_params = #params (clasetGoal.goal_at node pos)
  in
    case total
           (clasetReplay.COMPUTE_CLASET_HYP_SUBST_TAC_IN ctxt)
           rendered of
        NONE => seq.empty
      | SOME (eliminations, computed) =>
          (case aligned_result computed of
               result as ([(child_asl, child_w)], _) =>
                 let
                   val child =
                     {params = initial_params, asl = child_asl, w = child_w}
                 in
                   seq.result
                     (Direct
                       {kind = HypSubst, consumed = NONE,
                        created = no_created, eigenvariables = [[]],
                        result = result, children = SOME [child],
                        action =
                          clasetReplay.claset_hyp_subst_action_at
                            eliminations,
                        closed = [NONE], store = clasetGoal.store node})
                 end
             | _ => seq.empty)
  end

fun materialized_hyp_subst_results_in ctxt (node, pos) =
  let
    val {hyp_subst_tac, ...} = clasetLib.claset_config
    val repeated =
      Tactical.THEN
        (hyp_subst_tac, Tactical.REPEAT hyp_subst_tac)
  in
    case tactic_direct_in ctxt HypSubst NONE node pos repeated of
        SOME result => seq.result result
      | NONE => seq.empty
  end

fun hyp_subst_results_in ctxt (input as (node, pos)) =
  if has_metavariables node pos then
    internal_hyp_subst_results_in ctxt input
  else materialized_hyp_subst_results_in ctxt input

fun plain_tactic_results_in ctxt kind action tactic (node, pos) =
  seq.delay
    (fn () =>
      let
        val rendered = clasetGoal.render node pos
        val {params, ...} = clasetGoal.goal_at node pos
      in
        case Option.map aligned_result
               (total (fn () => tactic rendered ctxt) ()) of
            NONE => seq.empty
          | SOME (result as (goals, _)) =>
              let
                fun child (asl, w) =
                  {params = params, asl = asl, w = w}
              in
                seq.result
                  (Direct
                    {kind = kind, consumed = NONE,
                     created = no_created,
                     eigenvariables = map (fn _ => []) goals,
                     result = result, children = SOME (map child goals),
                     action = action,
                     closed = map (fn _ => NONE) goals,
                     store = clasetGoal.store node})
              end
      end)

(* T1 affectedness is computed on the branch syntax, before beta/eta
   normalization.  Instantiate engine bindings structurally, but preserve
   those redexes so this transition agrees with
   blastSearch.equalTrackedSubstMeasured. *)
fun instantiate_without_reduction store tm =
  clasetMeta.instantiate store tm

type blast_hyp_subst_context =
  {store : clasetMeta.store,
   params : term list,
   assumption_count : int,
   goal : term list * term}

fun prepare_blast_hyp_subst node pos : blast_hyp_subst_context =
  let
    val store = clasetGoal.store node
    val {params, asl, w} = clasetGoal.goal_at node pos
    val instantiate = instantiate_without_reduction store
    val goal = (map instantiate asl, instantiate w)
  in
    {store = store, params = params, assumption_count = length asl,
     goal = goal}
  end

fun blast_hyp_subst_in ctxt
      ({store, params, assumption_count, goal} :
        blast_hyp_subst_context) {position, recorded} =
  if position <= 0 orelse position > assumption_count then NONE
  else
    case total
      (fn () =>
        case recorded of
            NONE =>
              clasetReplay.COMPUTE_BLAST_HYP_SUBST_TAC_AT_IN
                ctxt position goal
          | SOME (fields as {changed, side}) =>
              (fields,
               clasetReplay.BLAST_HYP_SUBST_TAC_AT
                 {position = position, changed = changed, side = side}
                 goal ctxt)) () of
        NONE => NONE
      | SOME ({changed, side}, unaligned) =>
          let
            val result as (goals, _) = aligned_result unaligned
            fun child (child_asl, child_w) =
              {params = params, asl = child_asl, w = child_w}
          in
            SOME
              (Direct
                {kind = HypSubst, consumed = NONE,
                 created = no_created,
                 eigenvariables = map (fn _ => []) goals,
                 result = result, children = SOME (map child goals),
                 action =
                   clasetReplay.blast_hyp_subst_action_at
                     {position = position, changed = changed,
                      side = side},
                 closed = map (fn _ => NONE) goals, store = store})
          end

fun blast_hyp_subst_results_in ctxt (node, pos) =
  list_seq
    (fn () =>
      let
        val prepared = prepare_blast_hyp_subst node pos
        val positions =
          List.tabulate
            (#assumption_count prepared, fn index => index + 1)
      in
        List.mapPartial
          (fn position =>
            blast_hyp_subst_in ctxt prepared
              {position = position, recorded = NONE}) positions
      end)

fun blast_hyp_subst_results_at_in ctxt
      {equality, changed, side} (node, pos) =
  list_seq
    (fn () =>
      case blast_hyp_subst_in ctxt (prepare_blast_hyp_subst node pos)
        {position = equality,
         recorded = SOME {changed = changed, side = side}} of
          NONE => []
        | SOME direct => [direct])

fun ccontr_results_in ctxt =
  plain_tactic_results_in ctxt CContr
    clasetReplay.goal_negation_action
    clasetReplay.GOAL_NEGATION_TAC

fun move_back_results_in ctxt position =
  plain_tactic_results_in ctxt (MoveAssumptionToBack position)
    (clasetReplay.move_assumption_to_back_action position)
    (clasetReplay.MOVE_ASSUMPTION_TO_BACK_TAC position)

fun rendered_conclusion node pos = #2 (clasetGoal.render node pos)

fun forall_bound tm =
  case total dest_forall tm of
      SOME (bound, _) => SOME bound
    | NONE => Option.map #1 (clasetReplay.eta_forall_predicate tm)

fun disch_results_in ctxt (input as (node, pos)) =
  if is_imp_only (rendered_conclusion node pos) then
    builtin_results_in ctxt input
  else seq.empty

fun gen_results_in ctxt (input as (node, pos)) =
  case forall_bound (rendered_conclusion node pos) of
      SOME bound =>
        let
          val (fresh, store) = clasetGoal.fresh_eigen node bound
          val name = fst (dest_var fresh)
          val rendered = clasetGoal.render node pos
        in
      case total
             (fn () =>
                clasetReplay.GEN_NAMED_TAC name rendered
                  ctxt) () of
              NONE => seq.empty
            | SOME (result as (goals, validation)) =>
                let
                  val {params, ...} = clasetGoal.goal_at node pos
                  fun child (asl, w) =
                    {params = params @ [fresh], asl = asl, w = w}
                  val children = map child goals
                  val action = clasetReplay.gen_action name
                in
                  seq.result
                    (Direct
                      {kind = Gen, consumed = NONE, created = no_created,
                       eigenvariables = map (fn _ => [name]) goals,
                       result = result, children = SOME children,
                       action = action,
                       closed = map (fn _ => NONE) children,
                       store = store})
                end
        end
    | NONE => seq.empty

fun safe_cascade_in ctxt cs input =
  let val note_skip = skip_note ctxt
  in
    first_nonempty
      [assume_or_eq_mp,
       rule_results note_skip clasetUnify.Match cs false
         (clasetLib.safe0_part cs) all_weights,
       builtin_results_in ctxt,
       swapped_builtin_results_in ctxt,
       hyp_subst_results_in ctxt,
       rule_results note_skip clasetUnify.Match cs false
         (clasetLib.safep_part cs) all_weights]
      input
  end

fun close_plain goal =
  let
    val node = clasetGoal.from_goal goal
  in
    case seq.cases (assume_or_contradiction (node, 1)) of
        NONE => NONE
      | SOME (result, _) => SOME result
  end

fun close_one_child direct =
  let
    val Direct
      (fields as
       {result = (goals, validation), children, closed, ...}) = direct

    fun close_side index =
      let
        val other = 1 - index
      in
        case close_plain (List.nth (goals, index)) of
            SOME
              (close_direct as
               Direct {result = ([], close_validation), ...}) =>
              let
                fun combined [remaining_thm] =
                      validation
                        (if index = 0 then
                           [close_validation [], remaining_thm]
                         else [remaining_thm, close_validation []])
                  | combined _ =
                      raise mk_HOL_ERR "clasetStep" "close_one_child"
                        "close validation arity"
                val remaining = List.nth (goals, other)
                val child =
                  Option.map (fn values => [List.nth (values, other)])
                    children
                val closed' =
                  if index = 0 then
                    [SOME close_direct, List.nth (closed, other)]
                  else [List.nth (closed, other), SOME close_direct]
              in
                SOME
                  (Direct
                    (upd_direct fields
                      (Fld #result ([remaining], combined))
                      (Fld #children child)
                      (Fld #closed closed') $$))
              end
          | _ => NONE
      end
  in
    case goals of
        [_, _] =>
          (case close_side 0 of
               SOME result => SOME result
             | NONE => close_side 1)
      | _ => NONE
  end

fun clarify_cascade_in ctxt cs input =
  let
    val note_skip = skip_note ctxt
    (* The one- and two-child phases filter the same ordered candidates. *)
    val safep_candidates = Portable.HOLSusp.delay
      (fn () =>
        rule_candidates listUtil.no_checkpoint clasetUnify.Match
          (clasetLib.safep_part cs) input)
    fun safep_results weight goal =
      rule_applications note_skip clasetUnify.Match cs false
        (fn () => List.filter (weight_is weight o #1)
          (Portable.HOLSusp.force safep_candidates)) goal
  in
    first_nonempty
      [assume_or_contradiction,
       rule_results note_skip clasetUnify.Match cs false
         (clasetLib.safe0_part cs) all_weights,
       builtin_results_in ctxt,
       swapped_builtin_results_in ctxt,
       hyp_subst_results_in ctxt,
       safep_results 1,
       seq.mapPartial close_one_child o safep_results 2]
      input
  end

fun append_results left right input =
  seq.append (left input) (seq.delay (fn () => right input))

fun append_many [] _ = seq.empty
  | append_many [operation] input = operation input
  | append_many (operation :: rest) input =
      seq.append (operation input)
        (seq.delay (fn () => append_many rest input))

val empty_rule_metas : clasetUnify.rule_metas = {terms = [], types = []}
val unify_config =
  {mode = clasetUnify.Unify, rule_metas = empty_rule_metas}

type unifying_assumption_context =
  {asl : term list, w : term, store : clasetMeta.store}

fun prepare_unifying_assumption node pos : unifying_assumption_context =
  let
    val (asl, w) = clasetGoal.render node pos
  in
    {asl = asl, w = w, store = clasetGoal.store node}
  end

fun unifying_assumption_candidate_with action_of
      ({w, store = initial_store, ...} : unifying_assumption_context)
      (asm_pos, asm) =
  case clasetUnify.unify initial_store unify_config (w, asm) of
          NONE => NONE
        | SOME store =>
            let
              fun validation [] =
                    assumption_thm (normalize_term store asm)
                      (normalize_term store w)
                | validation _ =
                    raise mk_HOL_ERR "clasetStep"
                      "unifying_assumption_results"
                      "assumption validation has children"
            in
              SOME
                (Direct
                  {kind = Assumption asm_pos,
                   consumed = SOME asm_pos, created = no_created,
                   eigenvariables = [], result = ([], validation),
                   children = SOME [],
                   action = action_of asm_pos,
                   closed = [], store = store})
            end

fun unifying_assumption_candidate prepared positioned =
  unifying_assumption_candidate_with clasetReplay.assumption_action
    prepared positioned

fun unifying_assumption_in
      action_of (prepared as {asl, ...} : unifying_assumption_context)
      asm_pos =
  if asm_pos <= 0 orelse asm_pos > length asl then NONE
  else
    unifying_assumption_candidate_with action_of prepared
      (asm_pos, nth1 asl asm_pos)

fun unifying_assumption_results (node, pos) =
  seq.delay
    (fn () =>
      let
        val prepared = prepare_unifying_assumption node pos
      in
        map_numbered_results (unifying_assumption_candidate prepared)
          (#asl prepared)
      end)

fun unifying_assumption_results_at asm_pos (node, pos) =
  list_seq
    (fn () =>
      case unifying_assumption_in
        clasetReplay.strict_assumption_action
        (prepare_unifying_assumption node pos) asm_pos of
          NONE => []
        | SOME direct => [direct])

type unifying_contradiction_context =
  {asl : term list,
   w : term,
   params : term list,
   store : clasetMeta.store}

fun prepare_unifying_contradiction node pos :
      unifying_contradiction_context =
  let
    val (asl, w) = clasetGoal.render node pos
    val params = #params (clasetGoal.goal_at node pos)
  in
    {asl = asl, w = w, params = params, store = clasetGoal.store node}
  end

(* Both entry points below reach the same closure once unification has
   settled the negative and positive assumptions, so the node they emit
   is built here: a change to the CONTR reconstruction or to the replay
   action must not be able to reach only one of them.  [caller] is the
   reporting function name, the sole difference between the two. *)
fun contradiction_direct caller {w, major, positive, candidate, created}
      (negative_pos, positive_pos) store =
  let
    fun validation [] =
          let
            val normalized_major = normalize_term store major
            val normalized_positive = normalize_term store positive
            val negative_thm = assumption_thm major normalized_major
            val positive_thm =
              assumption_thm candidate normalized_positive
            val false_thm = MP (NOT_ELIM negative_thm) positive_thm
          in
            Drule.CONTR (normalize_term store w) false_thm
          end
      | validation _ =
          raise mk_HOL_ERR "clasetStep" caller
            "contradiction validation has children"
  in
    Direct
      {kind = Contradiction (negative_pos, positive_pos),
       consumed = SOME negative_pos, created = created,
       eigenvariables = [], result = ([], validation),
       children = SOME [],
       action =
         clasetReplay.contradiction_action (negative_pos, positive_pos),
       closed = [], store = store}
  end

(* Allocate the shared formula/result metavariables and settle the negative
   assumption once.  The positioned and enumerating entry points differ only
   in how they choose a positive assumption after this setup. *)
fun prepare_contradiction_major
      {w, params, store = initial_store} major =
  let
    val (positive, store1) =
      clasetMeta.new_meta {allow = params, ty = Type.bool} initial_store
    val (result, fresh_store) =
      clasetMeta.new_meta {allow = params, ty = Type.bool} store1
    val created = {terms = [positive, result], types = []}
    val config = {mode = clasetUnify.Unify, rule_metas = created}
  in
    case clasetUnify.unify fresh_store config (result, w) of
        NONE => NONE
      | SOME result_store =>
          Option.map
            (fn store =>
              {positive = positive, created = created, store = store})
            (clasetUnify.unify result_store config
              (mk_neg positive, major))
  end

fun unifying_contradiction_in
      ({asl, w, params, store = initial_store} :
        unifying_contradiction_context)
      {negative = negative_pos, positive = positive_pos} =
  if negative_pos <= 0 orelse positive_pos <= 0 orelse
     negative_pos > length asl orelse positive_pos > length asl orelse
     negative_pos = positive_pos
  then NONE
  else
    let
        val major = nth1 asl negative_pos
        val candidate = nth1 asl positive_pos
      in
        case prepare_contradiction_major
          {w = w, params = params, store = initial_store} major of
            NONE => NONE
          | SOME {positive, created, store = major_store} =>
              let
                val selected_store =
                  if closing_equal major_store positive candidate then
                    SOME major_store
                  else
                    clasetUnify.unify major_store unify_config
                      (positive, candidate)
              in
                Option.map
                  (contradiction_direct "unifying_contradiction_at"
                     {w = w, major = major, positive = positive,
                      candidate = candidate, created = created}
                     (negative_pos, positive_pos))
                  selected_store
              end
    end

fun unifying_contradiction_results_at positions (node, pos) =
  list_seq
    (fn () =>
      case unifying_contradiction_in
        (prepare_unifying_contradiction node pos) positions of
          NONE => []
        | SOME direct => [direct])

fun unifying_contradiction_results (node, pos) =
  seq.delay
    (fn () =>
      let
        val prepared = prepare_unifying_contradiction node pos
        val {asl, w, params, store = initial_store} = prepared

        fun major_alternatives (major_pos, major) =
          case prepare_contradiction_major
            {w = w, params = params, store = initial_store} major of
                NONE => NONE
              | SOME {positive, created, store = major_store} =>
                  let
                    val normalized_positive =
                      normalize_term major_store positive
                    (* An exact match takes precedence over all unifying
                       matches, including those at earlier positions. *)
                    fun find_exact _ [] = NONE
                      | find_exact candidate_pos (candidate :: rest) =
                          if candidate_pos <> major_pos andalso
                             aconv normalized_positive
                               (normalize_term major_store candidate)
                          then SOME (candidate_pos, candidate)
                          else find_exact (candidate_pos + 1) rest
                    val stores =
                      case find_exact 1 asl of
                          SOME (positive_pos, candidate) =>
                            seq.result (positive_pos, candidate, major_store)
                        | NONE =>
                            map_numbered_results
                              (fn (positive_pos, candidate) =>
                                if positive_pos = major_pos then NONE
                                else
                                  Option.map
                                    (fn store =>
                                      (positive_pos, candidate, store))
                                    (clasetUnify.unify major_store
                                      unify_config (positive, candidate)))
                              asl

                    fun make (positive_pos, candidate, store) =
                      contradiction_direct
                        "unifying_contradiction_results"
                        {w = w, major = major, positive = positive,
                         candidate = candidate, created = created}
                        (major_pos, positive_pos) store
                  in
                    SOME (seq.map make stores)
                  end
      in
        seq.flatten (map_numbered_results major_alternatives asl)
      end)

(* Only safe0 carries the lazy constructor pairs, so only its lookup
   takes [derive]. *)
fun inst0_cascade derive cs input =
  append_many
    [unifying_assumption_results,
     unifying_contradiction_results,
     rule_results_with derive no_note clasetUnify.Unify cs false
       (clasetLib.safe0_part cs) all_weights]
    input

fun instp_cascade cs =
  rule_results no_note clasetUnify.Unify cs false
    (clasetLib.safep_part cs) all_weights

fun inst_cascade derive cs input =
  append_results (inst0_cascade derive cs) (instp_cascade cs) input

fun unsafe_candidates cs =
  rule_candidates listUtil.no_checkpoint clasetUnify.Unify
    (clasetLib.unsafe_part cs)

fun unsafe_applications cs =
  rule_applications no_note clasetUnify.Unify cs false

fun unsafe_cascade cs input =
  unsafe_applications cs (fn () => unsafe_candidates cs input) input

fun depth_cascade part cs input =
  append_results (instp_cascade cs)
    (rule_results no_note clasetUnify.Unify cs false part all_weights) input

fun selected_direct goals validation available =
  case List.find
    (fn (identity, _) => Portable.pointer_eq (identity, validation))
    available
  of
      NONE => NONE
    | SOME (_, direct) =>
        if boolSyntax.goals_eq (#1 (direct_result direct)) goals then
          SOME direct
        else NONE

fun make_record target validation direct =
  let
    fun nested _ [] = []
      | nested index (child :: rest) =
          Option.map
            (fn selected =>
              make_record (target + index - 1)
                (#2 (direct_result selected)) selected)
            child :: nested (index + 1) rest
  in
    clasetReplay.make_record
      {kind = direct_kind direct,
       target = target,
       consumed = direct_consumed direct,
       created = direct_created direct,
       eigenvariables = direct_eigens direct,
       validation = validation,
       action = direct_action direct,
       children = nested 1 (direct_closed direct)}
  end

fun direct_step results (node, pos) =
  seq.map
    (fn direct =>
      let
        val (_, validation) = direct_result direct
        val stored = clasetGoal.set_store (direct_store direct) node
        val children =
          case direct_children direct of
              SOME values => values
            | NONE =>
                raise mk_HOL_ERR "clasetStep" "direct_step"
                  "an exact engine transition has no internal children"
        val next =
          clasetGoal.replace_goal stored
            {pos = pos, children = children,
             store = direct_store direct}
        val record = make_record pos validation direct
      in
        (record, clasetGoal.record_step record next)
      end)
    (results (node, pos))

val blast_assumption_step = direct_step unifying_assumption_results
val blast_contradiction_step =
  direct_step unifying_contradiction_results
fun rule_step level {theorem, elim, mode} =
  direct_step
    (supplied_rule_results_with (fn () => ()) (level_note level)
      AllMajors FullPrefixes mode
      clasetLib.empty_cs {theorem = theorem, elim = elim})
fun rule_step_budgeted level budget {theorem, elim, mode} =
  direct_step
    (supplied_rule_results_with
      (fn () => searchBudget.charge budget searchBudget.Candidate)
      (level_note level)
      AllMajors FullPrefixes mode
      clasetLib.empty_cs {theorem = theorem, elim = elim})
fun forward_rule_step_with charge {theorem, immediate, mode} =
  let
    (* Canonicalizing here serves both the range check and every later
       application, so the rule is put in canonical form exactly once. *)
    val form = clasetRules.canonical_form_of clasetRules.Forward theorem
    val prepared = Portable.HOLSusp.delay
      (fn () => (#thm form, type_variables (#thm form)))
    val premise_count = length (#prems form)
    val count = Option.getOpt (immediate, premise_count)
    val _ =
      if count > 0 andalso count <= premise_count then ()
      else
        raise mk_HOL_ERR "clasetStep" "forward_rule_step"
          "the immediate-premise count is out of range"
  in
    direct_step
      (forward_rule_results charge mode
        {source = theorem, prepared = prepared} count)
  end
fun forward_rule_step specification =
  forward_rule_step_with (fn () => ()) specification
fun forward_rule_step_budgeted budget specification =
  forward_rule_step_with
    (fn () => searchBudget.charge budget searchBudget.Candidate)
    specification
type forward_cursor = (step_record * node) seq.seq
datatype forward_scan =
    ForwardYield of
      {result : step_record * node, rest : forward_cursor}
  | ForwardExhausted
  | ForwardScanLimit of
      {kind : searchBudget.kind, usage : searchBudget.usage,
       cursor : forward_cursor}
fun next_forward cursor =
  (case seq.cases cursor of
       NONE => ForwardExhausted
     | SOME (result, rest) =>
         ForwardYield {result = result, rest = rest})
  handle searchBudget.LimitReached (kind, usage) =>
    ForwardScanLimit
      {kind = kind, usage = usage, cursor = cursor}
fun blast_assumption_step_at position =
  direct_step (unifying_assumption_results_at position)
fun blast_contradiction_step_at positions =
  direct_step (unifying_contradiction_results_at positions)
fun blast_rule_step cs specification =
  direct_step (exact_rule_results cs specification)
fun blast_rule_step_at cs {theorem, elim, major} =
  direct_step
    (exact_rule_results_with (ExactMajor major) cs
      {theorem = theorem, elim = elim})

fun blast_disch_step_in ctxt = direct_step (disch_results_in ctxt)
fun blast_gen_step_in ctxt = direct_step (gen_results_in ctxt)
fun blast_ccontr_step_in ctxt = direct_step (ccontr_results_in ctxt)
fun blast_hyp_subst_step_in ctxt =
  direct_step (blast_hyp_subst_results_in ctxt)
fun blast_hyp_subst_step_at_in ctxt fields =
  direct_step (blast_hyp_subst_results_at_in ctxt fields)
fun blast_move_back_step_in ctxt position =
  direct_step (move_back_results_in ctxt position)

fun wrapper_direct rendered goals validation store =
  let val result = aligned_result (goals, validation)
  in
    Direct
      {kind = Wrapper, consumed = NONE, created = no_created,
       eigenvariables = clasetReplay.new_free_names rendered goals,
       result = result, children = NONE,
       action = clasetReplay.fixed_action_on rendered result,
       closed = map (fn _ => NONE) goals, store = store}
  end

fun wrapped_step_in ctxt apply_wrappers cascade cs (node, pos) =
  seq.delay
    (fn () =>
      let
        val rendered = clasetGoal.render node pos
        val available = ref ([] : (validation * direct) list)

        (* A wrapper may reorder equal rendered results.  Give each direct
           result an opaque closure identity so its engine store and replay
           action follow the result selected by the wrapper. *)
        fun remember direct =
          let
            val (goals, validation) = direct_result direct
            fun identity theorems = validation theorems
          in
            available := (identity, direct) :: !available;
            (goals, identity)
          end

        fun base goal _ =
          if boolSyntax.goal_eq goal rendered then
            seq.map remember (cascade cs (node, pos))
          else
            let
              val temporary = clasetGoal.from_goal goal
            in
              seq.map direct_result (cascade cs (temporary, 1))
            end

        val wrapped =
          apply_wrappers cs base rendered ctxt

        fun lift sequence =
          seq.delay
            (fn () =>
              case seq.cases sequence of
                  NONE => seq.empty
                | SOME (result as (goals, validation), rest) =>
                    let
                      val (direct, exact) =
                        case selected_direct goals validation (!available) of
                            SOME found => (found, true)
                          | NONE =>
                              (wrapper_direct rendered goals validation
                                 (clasetGoal.store node), false)
                      val stored =
                        clasetGoal.set_store (direct_store direct) node
                      val lifted =
                        if exact then
                          case direct_children direct of
                              SOME children =>
                                SOME
                                  (clasetGoal.replace_goal stored
                                    {pos = pos, children = children,
                                     store = direct_store direct})
                            | NONE =>
                                clasetGoal.unrender stored pos result
                        else clasetGoal.unrender stored pos result
                    in
                      case lifted of
                          NONE => lift rest
                        | SOME next =>
                            let
                              val record =
                                make_record pos validation direct
                              val recorded =
                                if clasetGoal.replay_length next >
                                   clasetGoal.replay_length stored
                                then next
                                else clasetGoal.record_step record next
                            in
                              seq.cons (record, recorded) (lift rest)
                            end
                    end)
      in
        lift wrapped
      end)

fun wrapped_step apply_wrappers cascade cs input =
  wrapped_step_in (Context.snapshot ()) apply_wrappers cascade cs input

fun safe_step_in ctxt cs =
  wrapped_step_in ctxt clasetLib.app_safe_wrappers
    (safe_cascade_in ctxt) cs

fun clarify_step_in ctxt cs =
  wrapped_step_in ctxt clasetLib.app_safe_wrappers
    (clarify_cascade_in ctxt) cs

(* Unsafe steps carry no wrappers: the claset's safe wrappers apply only
   to safe and clarify cascades. *)
fun no_wrappers _ tactic = tactic

fun inst0_step_with derive cs =
  wrapped_step no_wrappers (inst0_cascade derive) cs

fun inst0_step cs = inst0_step_with listUtil.no_checkpoint cs

fun inst_step_in ctxt cs =
  wrapped_step_in ctxt no_wrappers (inst_cascade listUtil.no_checkpoint) cs

fun unsafe_step cs = wrapped_step no_wrappers unsafe_cascade cs

fun first_result sequence =
  case seq.cases sequence of
      NONE => NONE
    | SOME (result, _) => SOME result

fun safe_steps_at_with charge step collect cs node pos initial =
  let
    val initial_count = clasetGoal.goal_count node

    fun next current =
      (charge searchBudget.Candidate;
       case first_result (step cs (current, pos)) of
           NONE => NONE
         | SOME result =>
             (charge searchBudget.Application; SOME result))

    fun repeat (record, current) acc =
      let val collected = collect ((pos, record, current), acc)
      in
        if clasetGoal.goal_count current < initial_count then
          (collected, current)
        else
          case next current of
              NONE => (collected, current)
            | SOME result => repeat result collected
      end
  in
    case next node of
        NONE => NONE
      | SOME result => SOME (repeat result initial)
  end

fun keep_last ((_, record, next), _) = SOME (record, next)

fun safe_saturation_with steps cs node initial =
  let
    fun first_goal current acc =
      let
        val count = clasetGoal.goal_count current
        fun inspect pos =
          if pos > count then NONE
          else
            case steps cs current pos acc of
                NONE => inspect (pos + 1)
              | result => result
      in
        inspect 1
      end

    fun saturate current acc =
      case first_goal current acc of
          NONE => acc
        | SOME (collected, next) => saturate next collected
  in
    saturate node initial
  end

fun fold_safe_saturation charge ctxt cs node collect initial =
  safe_saturation_with
    (safe_steps_at_with charge (safe_step_in ctxt) collect)
    cs node initial

fun safe_saturation_in_with charge ctxt cs node =
  List.rev (fold_safe_saturation charge ctxt cs node
    op:: [])

fun safe_saturation_in ctxt cs node =
  safe_saturation_in_with (fn _ => ()) ctxt cs node

fun safe_steps_at_in ctxt cs node pos =
  Option.mapPartial #1
    (safe_steps_at_with (fn _ => ()) (safe_step_in ctxt) keep_last
      cs node pos NONE)

fun safe_saturate_all_in ctxt cs node =
  fold_safe_saturation (fn _ => ()) ctxt cs node
    keep_last NONE

(* The unknowns the node's goals still stand on.  A metavariable the store
   has bound since is no longer one of them, and one reachable only through
   such a binding is, so surface occurrences are read through the store. *)
fun undetermined_metas node =
  let val store = clasetGoal.store node
  in
    if clasetMeta.has_term_metas store then
      let
        fun goal_terms ({asl, w, ...} : clasetGoal.cgoal) = w :: asl
        val surface =
          clasetGoal.marked_terms
            (List.concat (map goal_terms (clasetGoal.goals node)))
      in
        Lib.op_U clasetMeta.same_meta
          (map (clasetMeta.metas_of store) surface)
      end
    else []
  end

(* Isabelle names the unsafe steps for what they may do: instantiate
   variables.  A step guesses when it leaves an unknown undetermined, and
   there are two ways to do that: it can leave an unknown the goal already
   carries standing for a term built out of the rule's own new
   metavariables, and it can leave one of those new metavariables standing
   in the children with nothing there to fix it.  Either way the guess can
   be guessed again at the next expansion, so a depth-first search can
   follow one indefinitely, while a step whose new metavariables the goal
   settles as it applies them has guessed nothing.  Isabelle is spared the
   first way by its rule set rather than by its search -- the membership
   rules whose premise unifies with a flexible argument are simplification
   rules there and elimination rules here -- so it is the search that has to
   keep the two apart. *)
fun guessed_meta metas direct =
  case #terms (direct_created direct) of
      [] => false
    | created =>
        let
          val store = direct_store direct
          fun created_meta meta =
            List.exists (fn made => clasetMeta.same_meta made meta) created
          fun refines meta =
            List.exists created_meta (clasetMeta.metas_of store meta)
          fun children_carry_created () =
            let
              val children =
                List.concat
                  (map (fn (asl, w) => w :: asl) (#1 (direct_result direct)))
            in
              List.exists created_meta (clasetGoal.marked_terms children)
            end
        in
          List.exists refines metas orelse children_carry_created ()
        end

fun sift keep metas sequence =
  let
    fun sifted current =
      seq.delay
        (fn () =>
          case seq.cases current of
              NONE => seq.empty
            | SOME (direct, rest) =>
                if keep (guessed_meta metas direct) then
                  seq.cons direct (sifted rest)
                else sifted rest)
  in
    sifted sequence
  end

fun guess_free metas = sift not metas
fun guessing metas = sift (fn guessed => guessed) metas

(* Stable: the deferred alternatives keep their order among themselves,
   and reaching the first guess-free one costs only the guesses it passes
   -- the very alternatives the search would otherwise have expanded
   first. *)
fun guesses_last metas sequence =
  if List.null metas then sequence
  else
    let
      fun ordered deferred current =
        seq.delay
          (fn () =>
            case seq.cases current of
                NONE => seq.fromList (List.rev deferred)
              | SOME (direct, rest) =>
                  if guessed_meta metas direct then
                    ordered (direct :: deferred) rest
                  else seq.cons direct (ordered deferred rest))
    in
      ordered [] sequence
    end

fun guess_free_first cascade cs (input as (node, _)) =
  guesses_last (undetermined_metas node) (cascade cs input)

fun lazy_append left right =
  seq.append left (seq.delay right)

(* Isabelle's [inst_step_tac ORELSE' unsafe_step_tac]: the unifying steps,
   and the unsafe rules only where no unifying step applies.  The cut is
   what the guess-free order has to reach past.  The rules whose premise
   unifies with a flexible argument -- the seeded membership eliminations
   -- are safe rules read in Unify mode, so they are unifying steps, and a
   goal whose every unifying step guesses an unknown never sees an unsafe
   step that guesses none.  So where the unifying steps guess without
   exception, the unsafe steps that guess nothing are offered first and the
   guesses are kept behind them: strictly the alternatives the cut offered
   before, reordered, with the guess-free unsafe steps added in front. *)
fun unsafe_rung derive fast cs (input as (node, _)) =
  if not fast then
    guesses_last (undetermined_metas node)
      (append_results (inst_cascade derive cs) (unsafe_cascade cs) input)
  else
    let
      val metas = undetermined_metas node
    in
      if List.null metas then
        first_nonempty [inst_cascade derive cs, unsafe_cascade cs] input
      else
        seq.delay
          (fn () =>
            case seq.cases
                   (guesses_last metas (inst_cascade derive cs input)) of
                NONE => guesses_last metas (unsafe_cascade cs input)
              | SOME (first, rest) =>
                  if guessed_meta metas first then
                    let
                      (* The two passes use the same unsafe rule order.
                         Share lookup while keeping attempts independent. *)
                      val tagged = Portable.HOLSusp.delay
                        (fn () => unsafe_candidates cs input)
                      fun unsafe () =
                        unsafe_applications cs
                          (fn () => Portable.HOLSusp.force tagged) input
                    in
                      lazy_append (guess_free metas (unsafe ()))
                        (fn () =>
                          lazy_append (seq.cons first rest)
                            (fn () => guessing metas (unsafe ())))
                    end
                  else seq.cons first rest)
    end

fun general_step_in derive ctxt fast cs (input as (node, _)) =
  case safe_saturate_all_in ctxt cs node of
      SOME result => seq.result result
    | NONE =>
        wrapped_step_in ctxt clasetLib.app_unsafe_wrappers
          (unsafe_rung derive fast) cs input

fun step_in_with derive ctxt cs = general_step_in derive ctxt true cs
fun step_in ctxt cs = step_in_with listUtil.no_checkpoint ctxt cs
fun slow_step_in ctxt cs =
  general_step_in listUtil.no_checkpoint ctxt false cs

(* The children an inference leaves are solved one at a time, and the
   one taken first is the first whose conclusion does not stand on an
   unknown.  Nothing in such a conclusion constrains the unknown, so the
   child is closed only by a step that guesses it, where a sibling's
   proof may settle it outright: a rule whose conclusion carries an
   unknown its remaining premises do not fix leaves exactly that pair,
   and solving the premise first abandons a conjunction that is
   solvable, which made the rule unusable at any bound.  Isabelle's
   depth_tac (src/Provers/classical.ML:715 @ Isabelle2025-2) always
   takes the first child and reaches those states through higher-order
   unification instead, enumerating instances of the undetermined
   premise until one happens to fit a sibling.  Every child is solved
   either way and each is offered all of its solutions, so this is an
   order and not a choice. *)
fun depth_step_in_with derive ctxt cs part bound (node, pos) =
  let
    fun solve_many _ _ 0 result = seq.result result
      | solve_many m target count (record, current) =
          let
            (* The children occupy [target] upwards, and solving one
               moves the rest down into its place, so the offset is
               taken afresh against the children that are left. *)
            fun settled offset =
              if offset >= count then 0
              else if clasetGoal.stands_on_unknown current (target + offset)
              then settled (offset + 1)
              else offset
          in
            seq.bind (solve_one m (current, target + settled 0))
              (solve_many m target (count - 1))
          end

    and solve_one m (current, target) =
      case safe_steps_at_in ctxt cs current target of
          SOME (result as (_, safe_node)) =>
            solve_many m target
              (clasetGoal.child_count current safe_node) result
        | NONE =>
            let
              val closers = inst0_step_with derive cs (current, target)
              val branching =
                if m <= 0 then seq.empty
                else
                  seq.bind
                    (wrapped_step_in ctxt
                      clasetLib.app_unsafe_wrappers
                      (guess_free_first (depth_cascade part)) cs
                      (current, target))
                    (fn result as (_, next) =>
                      solve_many (m - 1) target
                        (clasetGoal.child_count current next) result)
            in
              seq.append closers branching
            end
  in
    if bound < 0 then seq.empty else solve_one bound (node, pos)
  end

fun depth_step_in ctxt =
  depth_step_in_with listUtil.no_checkpoint ctxt

end
