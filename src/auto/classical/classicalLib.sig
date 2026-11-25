signature classicalLib =
sig
  include Abbrev

  val SAFE_TAC : thm list -> tactic
  val CLARIFY_TAC : thm list -> tactic
  val SAFE_STEP_TAC : thm list -> tactic
  val CLARIFY_STEP_TAC : thm list -> tactic
  val STEP_TAC : thm list -> tactic
  val SLOW_STEP_TAC : thm list -> tactic
  val INST_STEP_TAC : thm list -> tactic

  val FAST_TAC : thm list -> tactic
  val SLOW_TAC : thm list -> tactic
  val BEST_TAC : thm list -> tactic
  val SLOW_BEST_TAC : thm list -> tactic
  val FIRST_BEST_TAC : thm list -> tactic
  val ASTAR_TAC : thm list -> tactic
  val SLOW_ASTAR_TAC : thm list -> tactic
  val DEEPEN_TAC : thm list -> tactic

  val CS_SAFE_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_CLARIFY_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_SAFE_STEP_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_CLARIFY_STEP_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_STEP_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_SLOW_STEP_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_INST_STEP_TAC : clasetLib.claset -> NTactical.ntactic

  val CS_FAST_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_SLOW_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_BEST_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_SLOW_BEST_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_FIRST_BEST_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_ASTAR_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_SLOW_ASTAR_TAC : clasetLib.claset -> NTactical.ntactic
  (* [CS_FIRST_BEST_TAC] given a bounded turn: the search runs under a
     bound of [expansions] admitted expansions and reports failure if it
     reaches it, so a caller can hand the goal to another engine rather
     than let one search spend a whole invocation.  A tactic: it keeps the
     first solution.  [expansions] is at least one: the search reads a
     limit of zero as no limit. *)
  val CS_BOUNDED_FIRST_BEST_TAC : clasetLib.claset -> int -> tactic

  type budget_session
  datatype budget_outcome =
      BudgetProved of
        {result : goal list * validation, session : budget_session}
    | BudgetExhausted
    | BudgetYielded of
        {kind : searchBudget.kind, usage : searchBudget.usage,
         session : budget_session}
    | BudgetLimitReached of
        {kind : searchBudget.kind, usage : searchBudget.usage}

  (* Additive detailed result for the first-best engine.  A yielded
     frontier or pending replay stays in this invocation.  The heap also
     survives a candidate result, so a failed reconstruction can advance
     to another candidate.  A successful result has passed Tactical.VALID
     in the supplied proof context.  Each replay attempt admits one
     normalization work unit before that validation. *)
  val CS_FIRST_BEST_SESSION :
    searchBudget.budget -> clasetLib.claset -> goal -> Context.t ->
    budget_session
  val RESUME_FIRST_BEST_SESSION : budget_session -> budget_outcome

  val CS_DEPTH_SOLVE_TAC :
    {dup : bool} -> int -> clasetLib.claset -> NTactical.ntactic
  (* A one-shot depth stage. Repeating it after a limit restarts its
     frontier, and the repeated scans charge the same invocation budget. *)
  val CS_DEPTH_SOLVE_TAC_BUDGETED :
    searchBudget.budget -> {dup : bool} -> int ->
    clasetLib.claset -> tactic
  type depth_session
  datatype depth_outcome =
      DepthProved of
        {result : goal list * validation, session : depth_session}
    | DepthExhausted
    | DepthYielded of
        {kind : searchBudget.kind, usage : searchBudget.usage,
         session : depth_session}
  (* The lazy depth cursor and a candidate awaiting replay survive a
     yield. Initial safe saturation may repeat if it yields mid-pass. *)
  val CS_DEPTH_SESSION :
    searchBudget.budget -> {dup : bool} -> int ->
    clasetLib.claset -> goal -> Context.t -> depth_session
  val RESUME_DEPTH_SESSION : depth_session -> depth_outcome
  val CS_DEEPEN_TAC : clasetLib.claset ->
                      {start : int} -> NTactical.ntactic
end
