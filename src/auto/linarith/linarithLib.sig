signature linarithLib =
sig
  include Abbrev

  type linarith_config = linarithData.linarith_config
  val default_config : linarith_config

  type search_stats =
    {nodes : int,
     refutations : int,
     disjunction_splits : int,
     operator_splits : int,
     augmentations : int}
  val last_search_stats : unit -> search_stats

  val LINARITH_TAC : thm list -> tactic
  val SIMPLE_LINARITH_TAC : thm list -> tactic
  val CFG_LINARITH_TAC : linarith_config -> thm list -> tactic
  (* These share the caller's budget through splitting and replay.
     A work cutoff raises searchBudget.LimitReached with its usage;
     callers may extend the budget and retry the one-shot tactic. *)
  val LINARITH_TAC_BUDGETED :
    searchBudget.budget -> thm list -> tactic
  val SIMPLE_LINARITH_TAC_BUDGETED :
    searchBudget.budget -> thm list -> tactic
  val CFG_LINARITH_TAC_BUDGETED :
    searchBudget.budget -> linarith_config -> thm list -> tactic

  val LINARITH_PROVE : term -> thm
  val LINARITH_CONV : conv

  datatype budget_outcome =
      LinarithProved of thm
    | LinarithExhausted
    | LinarithLimitReached of
        {kind : searchBudget.kind, usage : searchBudget.usage}

  (* The full splitting search shares one invocation budget with every
     nested certificate search and guard proof.  A proof is returned
     only after replay and reconstruction validate the original term. *)
  (* The explicit context composes inside another proof without
     installing an ambient context override. *)
  val LINARITH_PROVE_BUDGETED_IN :
    Context.t -> searchBudget.budget -> term -> budget_outcome

  (* Name of the merged fragment the LINARITH_ss constructors install. *)
  val linarith_fragment_name : string
  (* Name of the solver linarith_solver and its variants carry. *)
  val linarith_solver_name : string
  val CACHED_LINARITH : thm list -> conv
  val LINARITH_REDUCER : Traverse.reducer
  val LINARITH_ss : simpLib.ssfrag
  val LINARITH_ext_ss : simpLib.ssfrag
  val LINARITH_ext_ss_with : thm list -> simpLib.ssfrag
  val linarith_solver : Traverse.ssolver
  val linarith_solver_with_facts : thm list -> Traverse.ssolver
  (* These closures charge the owning invocation for arithmetic search and
     replay inside simplification.  The values above are unbudgeted and
     share the process-wide result cache. *)
  val LINARITH_REDUCER_BUDGETED :
    Context.t -> searchBudget.budget -> Traverse.reducer
  val LINARITH_ss_budgeted :
    Context.t -> searchBudget.budget -> simpLib.ssfrag
  val LINARITH_ext_ss_budgeted :
    Context.t -> searchBudget.budget -> simpLib.ssfrag
  val linarith_solver_budgeted :
    Context.t -> searchBudget.budget -> Traverse.ssolver
  val clear_linarith_caches : unit -> unit
end
