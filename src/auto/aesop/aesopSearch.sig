signature aesopSearch =
sig
  type cgoal = clasetGoal.cgoal
  type store = clasetMeta.store
  type tree = aesopTree.tree
  type gid = aesopTree.gid
  type tactic = Abbrev.tactic

  type aesop_config = {max_rapps : int, max_depth : int}
  val default_config : aesop_config

  type rule_source =
    {mode : clasetUnify.mode, cgoal : cgoal, store : store} ->
    aesopRule.ruleset

  datatype next_outcome =
      QueueEmpty of tree
    | ReadyForUnsafe of {goal : gid, tree : tree}
    | DepthLimit of {goal : gid, tree : tree}
    | NormalisationLimit of
        {goal : gid, tree : tree, iterations : int, rule : string}

  datatype safe_outcome =
      SafeSaturated of tree
    | SafeDepthLimit of {goal : gid, tree : tree}
    | SafeNormalisationLimit of
        {goal : gid, tree : tree, iterations : int, rule : string}

  datatype failure_reason =
      SearchExhausted
    | RappLimitReached
    | DepthLimitReached

  datatype search_outcome =
      SearchProved of tree
    | SearchFailed of
        {tree : tree, safe_goals : unit -> (gid * cgoal) list,
         reason : failure_reason}

  type budget_session
  datatype resume_outcome =
      ResumedFinished of search_outcome
    | ResumedYielded of
        {kind : searchBudget.kind, usage : searchBudget.usage,
         session : budget_session}
    | ResumedLimitReached of
        {kind : searchBudget.kind, usage : searchBudget.usage}

  (* Deterministic normalisation-and-safe saturation.  The [_in] forms
     carry the caller's proof context to rendered tactic rules, including
     lazy alternatives and resumed sessions; [new_budget_session]
     snapshots once at its entry.  [safe_frontier] returns the residual
     goals. *)
  val safe_saturate_in :
    Context.t ->
    {max_depth : int, rules : rule_source} -> tree -> safe_outcome
  val safe_frontier : tree -> (gid * cgoal) list

  (* Best-first normalisation/safe/unsafe search.  [safe_goals] runs a
     fresh safe-only saturation of the original goal and returns its exact
     residual frontier, as [safe_frontier] would.  That is a second search,
     so it is deferred: a caller that only needs to know the search failed
     never pays for it.  Not memoised -- each application recomputes. *)
  val search_in :
    Context.t -> aesop_config -> rule_source -> tree -> search_outcome
  (* A candidate yield retains the goal/rule generation and the next
     unexamined alternative.  Extend the same budget, then resume this
     session.  Other limits remain explicit terminal outcomes for now. *)
  val new_budget_session :
    searchBudget.budget -> aesop_config ->
    (searchBudget.budget -> rule_source) -> tree -> budget_session
  val new_budget_session_in :
    Context.t -> searchBudget.budget -> aesop_config ->
    (searchBudget.budget -> rule_source) -> tree -> budget_session
  val resume_budget_session : budget_session -> resume_outcome

  (* Select the winning forest of a proved tree and merge its final stores.
     Replay is exact: a failure after search success is an engine error. *)
  val extract : tree -> clasetReplay.grounded_script
  val REPLAY_TAC : tree -> tactic
end
