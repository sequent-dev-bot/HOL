signature clasetSearch =
sig
  type node = clasetGoal.node
  type expansion = node -> node seq.seq

  (* Zero or a negative value disables the frontier-search bound. *)
  val node_limit : int ref
  val node_count : unit -> int
  val pruning_count : unit -> int

  (* Each driver's first argument is the classical.trace level it reports
     at; a tactic reads it from its context with traceUtil.level_of
     clasetReplay.tracer. *)
  val DEPTH_FIRST : traceUtil.level -> (node -> bool) -> expansion -> expansion
  val DEPTH_SOLVE : traceUtil.level -> expansion -> expansion
  val BEST_FIRST : traceUtil.level -> (node -> bool) -> expansion -> expansion
  (* [BEST_FIRST] with its own bound, given first, in place of
     [node_limit]. *)
  val BOUNDED_BEST_FIRST :
    int -> traceUtil.level -> (node -> bool) -> expansion -> expansion
  val ASTAR : traceUtil.level -> (node -> bool) -> expansion -> expansion

  type frontier_session
  datatype frontier_outcome =
      FrontierResult of {node : node, session : frontier_session}
    | FrontierExhausted
    | FrontierYielded of
        {kind : searchBudget.kind, usage : searchBudget.usage,
         session : frontier_session}
    | FrontierLimitReached of
        {kind : searchBudget.kind, usage : searchBudget.usage}

  (* The budgeted frontier keeps the heap, visited set, and a partially
     consumed child sequence across candidate/application yields.  It does
     not read the legacy node_limit.  A cutoff raised inside a supplied
     expansion is explicit but terminal until that expansion itself offers
     a resumable cursor.  Extend the same budget before resuming a yield. *)
  val new_best_session :
    traceUtil.level -> searchBudget.budget -> (node -> bool) -> expansion ->
    node -> frontier_session
  val new_astar_session :
    traceUtil.level -> searchBudget.budget -> (node -> bool) -> expansion ->
    node -> frontier_session
  val resume_frontier : frontier_session -> frontier_outcome

  (* Restart [bounded] at start, start + inc, ... .  Once one bound has
     a result, all of that bound's results are retained and no later bound
     is attempted. *)
  val DEEPEN :
    traceUtil.level -> int * int -> (int -> expansion) -> int -> expansion
end
