signature clasetReplay =
sig
  include Abbrev

  datatype rule_variant = Plain | Swapped | Duplicate | MakeElim

  (* Which side of an equality a blast substitution eliminates.  A replay
     prefers the recorded side over choosing afresh: instantiating a
     metavariable can make the other side substitutable too. *)
  datatype hyp_subst_side = EliminateLeft | EliminateRight

  (* What one classical hyp-subst step eliminated, in the order it did.
     A step saturates, so it is a list; positions are those of the state
     the step was recorded against. *)
  datatype hyp_subst_elimination =
      DeleteReflexive of int
    | SubstituteAt of {position : int, side : hyp_subst_side}

  datatype step_kind =
      Assumption of int
    | Contradiction of int * int
    | ModusPonens of {implication : int, antecedent : int}
    | RuleApplication of
        {original : thm, theorem : thm, variant : rule_variant,
         elim : bool}
    | Disch
    | Gen
      (* A universal over a product type replaced by one over each
         component, ahead of the universal's own introduction. *)
    | SplitPaired
    | HypSubst
    | CContr
    | SwappedBuiltin of int
    | MoveAssumptionToBack of int
    | Wrapper

  type created =
    {terms : clasetMeta.meta list, types : clasetMeta.tymeta list}
  type exact_prefix_descriptor = {foralls : int, implications : int}
  type exact_prefix_rebuild =
    {fresh : term list, assumptions : term list, premise : term}
  type replay_action = clasetMeta.store -> tactic
  type step_record
  type script
  type grounded_script

  (* classical.trace.  The engines are given its level, which the tactics
     read from their context with traceUtil.level_of. *)
  val tracer : traceUtil.tracer

  datatype replay_failure =
    ReplayFailure of
      {goal : goal, step : step_kind option, message : string,
       script : string}
  datatype replay_outcome =
      Replayed of goal list * validation
    | ReplayFailed of replay_failure

  val make_record :
    {kind : step_kind, target : int, consumed : int option,
     created : created, eigenvariables : string list list,
     validation : validation, action : replay_action,
     children : step_record option list} -> step_record
  (* Per child goal, the names of its free variables the parent lacks:
     a record's eigenvariables. *)
  val new_free_names : goal -> goal list -> string list list

  val kind_of : step_record -> step_kind
  val target_of : step_record -> int
  val consumed_of : step_record -> int option
  val created_of : step_record -> created
  val eigenvariables_of : step_record -> string list
  val validation_of : step_record -> validation
  val children_of : step_record -> step_record option list

  val empty : int -> script
  val append : script -> step_record -> script
  val length : script -> int
  val to_string : script -> string

  (* Grounding is deterministic: type metavariables become bool before
     remaining term metavariables become ARB at their grounded types. *)
  val ground : clasetMeta.store -> script -> grounded_script
  val grounded_store : grounded_script -> clasetMeta.store
  val grounded_to_string : grounded_script -> string

  (* [replay_in] reports malformed scripts as data.  [REPLAY_TAC] is the
     classical-driver policy: it raises a diagnostic HOL_ERR.  Both use
     the supplied proof context for every action. *)
  val replay_in : Context.t -> grounded_script -> goal -> replay_outcome
  val REPLAY_TAC : grounded_script -> tactic

  (* Shared, position-directed replay vocabulary.  None of these tactics
     performs claset lookup or unification. *)
  val ASSUMPTION_TAC : clasetMeta.store -> int -> tactic
  val CONTRADICTION_TAC : clasetMeta.store -> int * int -> tactic
  val MP_TAC : clasetMeta.store ->
               {implication : int, antecedent : int} -> tactic
  val RULE_TAC :
    {theorem : thm, elim : bool, consumed : int option,
     parameters : term list, eigenvariables : string list list} -> tactic
  (* Apply the first [immediate] premises using the recorded assumptions,
     retain those assumptions, and add the residual theorem as a new head
     assumption. *)
  val FORWARD_RULE_TAC :
    {theorem : thm, immediate : int, assumptions : int list} -> tactic
  val BLAST_RULE_TAC :
    {theorem : thm, elim : bool, consumed : int option,
     parameters : term list, eigenvariables : string list list,
     prefixes : exact_prefix_descriptor list} -> tactic
  val exact_prefix_descriptor : term -> exact_prefix_descriptor
  val exact_prefix_bounds : exact_prefix_descriptor -> term -> term list
  val split_exact_prefix :
    {descriptor : exact_prefix_descriptor, premise : term,
     fresh : term list} ->
    {assumptions : term list, residual : term,
     rebuild : exact_prefix_rebuild}
  val rebuild_exact_prefix : exact_prefix_rebuild -> thm -> thm
  val CLASET_HYP_SUBST_TAC_AT : hyp_subst_elimination list -> tactic
  val COMPUTE_CLASET_HYP_SUBST_TAC_IN :
    Context.t -> goal ->
    hyp_subst_elimination list * (goal list * validation)
  val BLAST_HYP_SUBST_TAC : tactic
  val BLAST_HYP_SUBST_TAC_AT :
    {position : int, changed : bool list, side : hyp_subst_side} -> tactic
  val COMPUTE_BLAST_HYP_SUBST_TAC_AT_IN :
    Context.t -> int -> goal ->
    {changed : bool list, side : hyp_subst_side} * (goal list * validation)
  (* A genvar of [P]'s domain and [P], for a contracted [$! P]. *)
  val eta_forall_predicate : term -> (term * term) option
  val GEN_NAMED_TAC : string -> tactic
  val SPLIT_PAIRED_TAC : tactic
  val SPLIT_PAIRED_VAR_TAC :
    {variable : string, left : string, right : string} -> tactic
  val GOAL_NEGATION_TAC : tactic
  val SWAPPED_BUILTIN_TAC : clasetMeta.store -> int -> tactic
  val MOVE_ASSUMPTION_TO_BACK_TAC : int -> tactic

  val assumption_action : int -> replay_action
  (* Unlike [assumption_action], this exact-replay action never scans for a
     different closing assumption when the recorded occurrence has drifted. *)
  val strict_assumption_action : int -> replay_action
  val contradiction_action : int * int -> replay_action
  val mp_action : {implication : int, antecedent : int} -> replay_action
  val rule_action :
    (clasetMeta.store ->
      {theorem : thm, elim : bool, consumed : int option,
       parameters : term list,
       eigenvariables : string list list}) -> replay_action
  val forward_rule_action :
    (clasetMeta.store ->
      {theorem : thm, immediate : int,
       assumptions : int list}) -> replay_action
  val blast_rule_action :
    (clasetMeta.store ->
      {theorem : thm, elim : bool, consumed : int option,
       parameters : term list, eigenvariables : string list list,
       prefixes : exact_prefix_descriptor list}) -> replay_action
  val claset_hyp_subst_action_at :
    hyp_subst_elimination list -> replay_action
  val blast_hyp_subst_action_at :
    {position : int, changed : bool list, side : hyp_subst_side} ->
    replay_action
  val disch_action : replay_action
  val gen_action : string -> replay_action
  val split_paired_action : replay_action
  val split_paired_var_action :
    {variable : string, left : string, right : string} -> replay_action
  val goal_negation_action : replay_action
  val swapped_builtin_action : int -> replay_action
  val move_assumption_to_back_action : int -> replay_action
  val fixed_action_on : goal -> goal list * validation -> replay_action
end
