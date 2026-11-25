signature clasetStep =
sig
  include Abbrev

  type node = clasetGoal.node
  type goalpos = int

  datatype rule_variant = datatype clasetReplay.rule_variant
  datatype step_kind = datatype clasetReplay.step_kind
  datatype hyp_subst_side = datatype clasetReplay.hyp_subst_side

  type created = clasetReplay.created
  type step_record = clasetReplay.step_record
  type step = node * goalpos -> (step_record * node) seq.seq

  val kind_of : step_record -> step_kind
  val consumed_of : step_record -> int option
  val created_of : step_record -> created
  val eigenvariables_of : step_record -> string list
  val validation_of : step_record -> validation

  (* The declaration an applied theorem came from, and which of that
     declaration's derived forms the theorem is -- the origin and variant a
     RuleApplication record reports.  The boolean says the application came
     from a duplicating net, which is what tells a rule's duplicated form
     from its plain one where the two coincide.  A theorem no declaration
     derived is its own origin. *)
  val rule_origin :
    clasetLib.claset -> bool -> thm -> thm * rule_variant

  (* [_in] carries the tactic's proof context through lazy wrapper and
     built-in tactic calls.  A step without it snapshots the context at
     its invocation boundary. *)
  val safe_step_in : Context.t -> clasetLib.claset -> step
  val clarify_step_in : Context.t -> clasetLib.claset -> step
  val inst0_step : clasetLib.claset -> step
  val inst_step_in : Context.t -> clasetLib.claset -> step
  val unsafe_step : clasetLib.claset -> step
  val step_in : Context.t -> clasetLib.claset -> step
  (* [step_in_with derive] runs [derive] before each lazy constructor pair
     its safe0 lookup derives afresh, so a budget can meter it. *)
  val step_in_with :
    (unit -> unit) -> Context.t -> clasetLib.claset -> step
  val slow_step_in : Context.t -> clasetLib.claset -> step

  (* Fold each transition of a complete safe fixed point in replay order. *)
  val fold_safe_saturation :
    (searchBudget.kind -> unit) -> Context.t -> clasetLib.claset -> node ->
    ((goalpos * step_record * node) * 'a -> 'a) -> 'a -> 'a

  (* Every transition in a complete safe fixed point, in replay order. *)
  val safe_saturation_in :
    Context.t -> clasetLib.claset -> node ->
    (goalpos * step_record * node) list
  (* Charges each candidate safe step and each accepted transition.
     A one-shot caller restarts this fixed point after a work cutoff. *)
  val safe_saturation_in_with :
    (searchBudget.kind -> unit) -> Context.t -> clasetLib.claset ->
    node -> (goalpos * step_record * node) list

  (* Wrapper-free application of one supplied rule through the ordinary
     child policy.  Each sequence result is one application alternative.
     In Match mode a rule that would leave premise variables unfixed is
     refused; the refusal is traced at the given level, at threshold 1. *)
  val rule_step :
    traceUtil.level ->
    {theorem : thm, elim : bool, mode : clasetUnify.mode} -> step
  (* Charge before each introduction or elimination-major attempt.  The
     lazy sequence keeps the unexamined attempt on a budget cutoff. *)
  val rule_step_budgeted :
    traceUtil.level -> searchBudget.budget ->
    {theorem : thm, elim : bool, mode : clasetUnify.mode} -> step

  (* Engine-native forward application.  The first [immediate] premises are
     discharged from assumptions without consuming them; the residual
     theorem is added as a new head assumption of the sole child.  NONE
     asks for every premise of the canonical rule, which is the count the
     step derives anyway: the theorem is canonicalized once here and reused
     by every application, so no caller needs to canonicalize it to supply
     that count.  Every combination of assumptions that discharges the
     immediate premises is an alternative, except that no result repeats
     an assumption the goal already has or an earlier result added. *)
  val forward_rule_step :
    {theorem : thm, immediate : int option,
     mode : clasetUnify.mode} -> step
  (* The budgeted form charges each premise/major examination and each
     raw result inspection before work.  LimitReached propagates to the
     caller; the legacy form keeps its existing unbounded sequence API. *)
  val forward_rule_step_budgeted :
    searchBudget.budget ->
    {theorem : thm, immediate : int option,
     mode : clasetUnify.mode} -> step

  type forward_cursor = (step_record * node) seq.seq
  datatype forward_scan =
      ForwardYield of
        {result : step_record * node, rest : forward_cursor}
    | ForwardExhausted
    | ForwardScanLimit of
        {kind : searchBudget.kind, usage : searchBudget.usage,
         cursor : forward_cursor}
  (* Keep the same cursor on cutoff; extending its budget can resume it. *)
  val next_forward : forward_cursor -> forward_scan

  (* Exact, wrapper-free engine transitions used by blast reconstruction.
     Rule application uses the supplied canonical source rather than doing
     another claset lookup. *)
  val blast_assumption_step : step
  val blast_contradiction_step : step
  val blast_rule_step :
    clasetLib.claset -> {theorem : thm, elim : bool} -> step
  (* The additive [_at] forms select assumption occurrences before applying
     theorem/tactic logic.  Rule selectors use NONE only for introductions
     and a positive, in-range SOME position only for eliminations; a shape,
     range, polarity or matching error is clean nonapplication.  Internally
     all diagnostic families share this same singleton selection layer. *)
  val blast_assumption_step_at : int -> step
  val blast_contradiction_step_at :
    {negative : int, positive : int} -> step
  val blast_rule_step_at :
    clasetLib.claset ->
    {theorem : thm, elim : bool, major : int option} -> step

  val blast_disch_step_in : Context.t -> step
  val blast_gen_step_in : Context.t -> step
  val blast_ccontr_step_in : Context.t -> step
  val blast_hyp_subst_step_in : Context.t -> step
  val blast_hyp_subst_step_at_in :
    Context.t ->
    {equality : int, changed : bool list,
     side : hyp_subst_side} -> step
  val blast_move_back_step_in : Context.t -> int -> step

  (* [depth_step_in ctxt cs part m] selects the duplicating or
     non-duplicating unsafe net through [part].  Safe and inst0 inferences
     cost nothing; an instp/part inference costs one unit. *)
  val depth_step_in :
    Context.t -> clasetLib.claset -> clasetLib.claset_part ->
    int -> step
  (* As [depth_step_in], running [derive] as [step_in_with] does. *)
  val depth_step_in_with :
    (unit -> unit) -> Context.t -> clasetLib.claset ->
    clasetLib.claset_part -> int -> step
end
