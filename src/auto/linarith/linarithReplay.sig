signature linarithReplay =
sig
  type config = linarithData.linarith_config

  (* Replays one certificate; the theorem list is what its Asm nodes
     index.  This, refute and refute_budgeted take first the
     linarith.trace level to report at; the tactics they return and the
     forward entries read it from their context. *)
  val mkthm :
    traceUtil.level -> Thm.thm list -> linarithSolve.injust -> Thm.thm

  (* refute config assumptions conclusion searches for a certificate
     refuting those terms and returns the tactic that replays it, so
     the tactic must be applied to the goal they were taken from.  The
     terms are used as given: preprocessing is the caller's.  NONE is
     "no certificate", which for a caller that can still split the goal
     is not yet a failure; a genuine error is raised. *)
  val refute :
    traceUtil.level -> config -> Term.term list -> Term.term ->
    Abbrev.tactic option

  datatype refutation_outcome =
      RefutationReady of Abbrev.tactic
    | RefutationExhausted
    | RefutationLimitReached of
        {kind : searchBudget.kind, usage : searchBudget.usage}

  (* A ready tactic is a certificate awaiting replay, not a proof.  It
     charges the same budget while reconstructing the justification. *)
  val refute_budgeted :
    traceUtil.level -> searchBudget.budget -> config -> Term.term list ->
    Term.term -> refutation_outcome

  val fwd_prove_in :
    Context.t -> config -> Thm.thm list -> Term.term -> Thm.thm

  datatype budget_outcome =
      ReplayProved of Thm.thm
    | ReplayExhausted
    | ReplayLimitReached of
        {kind : searchBudget.kind, usage : searchBudget.usage}

  (* Shares the caller's budget with certificate search.  A result is
     proved only after kernel replay and support discharge complete.  A
     nested side proof uses the enclosing tactic's context directly. *)
  val fwd_prove_budgeted_in :
    Context.t -> searchBudget.budget -> config -> Thm.thm list ->
    Term.term -> budget_outcome
end
