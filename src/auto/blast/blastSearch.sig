signature blastSearch =
sig
  type pterm = blastTerm.term
  type var = blastTerm.var
  type goal = Abbrev.goal
  type claset = clasetLib.claset
  type tableau_rule = blastRule.tableau_rule

  type level =
    (pterm * bool) list * (pterm * bool) list

  type branch =
    {pairs : level list,
     lits : pterm list,
     vars : var list,
     lim : int}

  (* T1--T6 of the blast report.  Rule steps always rotate their new
     material; this is implicit because the search has no other mode. *)
  datatype script_step =
      HypSubst of
        {equality : int, changed : bool list,
         side : clasetStep.hyp_subst_side}
    | CloseAssume of {assumption : int}
    | CloseContradiction of {negative : int, positive : int}
    | SafeRule of
        {rule : tableau_rule, updated : bool, major : int option}
    | DeferGoal
    | UnsafeRule of
        {rule : tableau_rule, updated : bool, duplicate : bool,
         major : int option}

  type script = script_step list

  type proof =
    {script : script,
     trace : branch list list,
     depth : int,
     branches_created : int,
     branches_closed : int,
     choices_pruned : int}

  type phase_statistics =
    {emergency_cleanup_assignments : int,
     cooperative_checkpoints : int,
     candidate_rules_enumerated : int,
     candidate_conversions_attempted : int,
     safe_rule_attempts : int,
     unsafe_rule_attempts : int,
     rule_unification_attempts : int,
     rule_unification_successes : int,
     equality_substitution_attempts : int,
     equality_substitution_successes : int,
     literal_close_attempts : int,
     literal_close_successes : int}

  type statistics =
    {configured_depth : int,
     maximum_resource_cost : int,
     inferences_performed : int,
     branches_created : int,
     branches_closed : int,
     choices_pruned : int,
     rule_cache_hits : int,
     rule_conversions : int,
     remaining_trail_assignments : int,
     phase : phase_statistics}

  datatype completion = Completed | Interrupted

  type 'a measured_result =
    {completion : completion,
     fullTrace : branch list list,
     result : 'a option,
     statistics : statistics}

  datatype 'a budget_outcome =
      BudgetFinished of {result : 'a option, statistics : statistics}
    | BudgetYielded of
        {kind : searchBudget.kind, usage : searchBudget.usage,
         trail_assignments : int,
         resume : unit -> 'a budget_outcome}
    | BudgetLimitReached of
        {kind : searchBudget.kind, usage : searchBudget.usage}

  type debug_result =
    {fullTrace : branch list list,
     result : proof option}

  val depth_limit : int ref

  (* Raising this exception in the continuation re-enters the newest
     surviving choice point in prv. *)
  exception PROOF_FAILED

  (* Initial formulae all receive md = true, as in blast.ML:1180-1184. *)
  val initBranch : pterm list * int -> branch

  (* Each search runs at the blast.trace level of the context it is
     given. *)
  val searchGoal :
    Context.t -> claset -> int -> goal -> (proof -> 'a) -> 'a option
  (* This and the measured/debug entry points enable internal
     instrumentation.  The legacy searchGoal, tryGoal and deepenGoal entry
     points do not poll a stop predicate; they do maintain the
     inference/resource counters below, and every fixed-depth run reports
     its depth, branch and inference counts to searchWork.

     Statistics cover the complete fixed-depth run, including work before
     failed reconstruction or final search failure.  configured_depth is
     the supplied bound.  maximum_resource_cost is the largest admitted
     lim charge: configured_depth - lim after a safe or unsafe rule
     application.  It is not ML recursion depth, a formula count, or an
     inference count.  md controls gamma requeueing, but is not itself a
     depth charge.  A closing rule can be admitted with a negative successor
     lim, so the maximum can exceed a nonnegative configured_depth.

     inferences_performed counts committed search transitions: successful
     equality substitutions, literal closures, and safe or unsafe rule
     applications admitted by search control.  Candidate unification failures,
     candidates that unify but are killed by the bound, branch creation,
     queue manipulation and reconstruction are not inferences under this
     counter.  branches_created separately counts tableau branches.

     The phase counters are measured-search diagnostics.  Candidate counts
     exclude pseudo-rules and cache hits; conversion attempts include
     elimination rules rejected during conversion.  Rule-unification counts
     exclude literal closing, which has its own counters.  Equality success
     means a complete substituted branch was produced.  Literal-close
     success means unification found a closer, whether or not later
     backtracking retains it.  cooperative_checkpoints is exactly the number
     of stop-predicate calls.  searchGoalWithStats and ordinary search report
     zero for these measured-only fields.  An attempt is recorded only after
     its immediately preceding cooperative poll succeeds, just before the
     candidate conversion, rule unification, equality substitution, or
     literal-close operation starts.

     These are internal search-engine metrics.  For comparison with
     Isabelle's published Table 1, only configured_depth and the
     branches_created value from one completed, fixed-depth run correspond
     to its depth and ntried columns.  maximum_resource_cost and
     inferences_performed, all phase counters, and values accumulated across
     iterative-deepening runs are not published Isabelle/Blast statistics. *)
  val searchGoalWithStats :
    Context.t -> claset -> int -> goal -> (proof -> 'a) ->
    {result : 'a option, statistics : statistics}

  (* For reconstruction: the continuation receives the script, depth and
     branch counts of the proof, with an empty trace field. *)
  val searchGoalForReplay :
    Context.t -> claset -> int -> goal -> (proof -> 'a) ->
    {result : 'a option, statistics : statistics}

  (* Cooperative fixed-depth search.  stop is polled while translating and
     collecting variables from the initial goal, at every prv entry, and
     between recursive items in normalization, premise construction, gamma
     requeueing, pruning/clash checks, literal insertion and closing, equality
     substitution, rule iteration/unification, net edge/result traversal,
     candidate ordering/conversion, and cached-rule copying.  Measured theorem
     conversion also polls its HOL/type translation, canonical free-variable
     walk, each quantified SPEC/GEN stage, and blast-term bound-variable walks.
     A true result ends the run with completion = Interrupted and returns a
     coherent partial snapshot.  A completed exhaustion has completion =
     Completed and result = NONE.  If debug is false, fullTrace is empty.
     Exceptions raised by stop propagate unchanged; they are never interpreted
     as search-control exceptions.  searchGoalMeasured translates the HOL goal
     into fresh engine-owned prototerms.  On the explicit Interrupted path
     only, it abandons those
     engine-owned assignments instead of traversing their trail.  With debug
     enabled, fullTrace can expose those prototerms as part of the returned
     snapshot; their cutoff-time bindings are intentionally left intact, but
     no caller-supplied reference is involved.  Predicate and continuation
     exceptions still restore before they propagate unchanged.
     emergency_cleanup_assignments records assignments traversed by exception
     cleanup; normal search backtracking is excluded.
     remaining_trail_assignments records the engine-local trail size when the
     snapshot is assembled.  It is zero after a restored interruption, but
     may be nonzero after an owned interruption or successful continuation.

     This is cooperative timing, not a hard real-time bound.  Polling excludes
     time spent in the arbitrary caller-supplied stop predicate, the arbitrary
     successful continuation and proof reconstruction it may invoke, one
     indivisible HOL kernel or other primitive operation between checkpoints,
     and emergency rollback cleanup.  Consequently none of those
     intervals has a latency bound supplied by this API.  Goal-owned explicit
     interruption has no trail-cleanup interval, so once its checkpoint is
     reached the coherent snapshot is assembled without a trail traversal.
     Ordinary and statistics-only search select the original unmeasured worker
     families and do not construct measured local workers. *)
  val searchGoalMeasured :
    Context.t -> {debug : bool, stop : unit -> bool} ->
    claset -> int -> goal -> (proof -> 'a) -> 'a measured_result
  (* General scan checkpoints charge candidate work, while term
     normalization and equality substitution checkpoints charge
     normalization work.  Successful transitions charge applications.
     A limit restores mutable search state and is distinct from exhaustive
     failure.  This fixed-depth adapter does not retain a tableau cursor. *)
  val searchGoalBudgeted :
    Context.t -> searchBudget.budget -> claset -> int -> goal ->
    (proof -> 'a) -> 'a budget_outcome
  (* Retains the tableau's owned trail, rule cache, script, branches and
     backtracking handlers across bounded turns.  A yielded outcome reports
     the live owned-trail length for diagnostics; no caller-owned cells
     are reachable through it. The caller extends the same budget before
     invoking its one-shot continuation. *)
  val searchGoalResumable :
    Context.t -> searchBudget.budget -> claset -> int -> goal ->
    (proof -> 'a) -> 'a budget_outcome
  (* The corresponding replay entry points return an empty proof trace. *)
  val searchGoalBudgetedForReplay :
    Context.t -> searchBudget.budget -> claset -> int -> goal ->
    (proof -> 'a) -> 'a budget_outcome
  val searchGoalResumableForReplay :
    Context.t -> searchBudget.budget -> claset -> int -> goal ->
    (proof -> 'a) -> 'a budget_outcome
  val tryGoal : Context.t -> claset -> int -> goal -> proof option
  val debugGoal : Context.t -> claset -> int -> goal -> debug_result

  (* Bounds 0, 1, ... through !depth_limit, as DEEPEN (1, limit). *)
  val deepenGoal :
    Context.t -> claset -> goal -> (proof -> 'a) -> 'a option

  (* Focused observations of the port's search heuristics. *)
  val instantiationPenalty : int -> int
  (* True when a step's assignments, those outside the rule's own
     variables, left a branch unknown bound to a term with a rigid
     head: a shape chosen for the formula, which costs a level. *)
  val guessedShape :
    {assigned : var list, rule_vars : var list} -> bool
  val recursivePremise : pterm -> pterm list -> bool
  val requeueGamma :
    pterm * bool -> (pterm * bool) list -> bool ->
    (pterm * bool) list
  val killsAllAlternatives : int -> pterm list list -> bool
  val mayUndo :
    {other_rules : bool, updated : bool,
     old_vars : var list, new_vars : var list} -> bool
  val clashVar : var list -> int * var list -> bool
  val prunePlan :
    {branches : int,
     next_vars : var list,
     trail_mark : int,
     trail : var list,
     choices : (int * int) list} -> (int * int) list
end
