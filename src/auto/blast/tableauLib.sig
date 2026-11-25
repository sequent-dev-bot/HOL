signature tableauLib =
sig
  include Abbrev

  type proof = blastSearch.proof
  type branch = blastSearch.branch
  type try_result =
    {fullTrace : branch list list,
     result : proof option}

  (* Plain facts retain literal premise use.  Facts with schematic type
     parameters also have an invocation-local introduction view, so a
     type exposed during tableau search can still use the citation. *)
  val BLAST_TAC : thm list -> tactic
  val BLAST_DEPTH_TAC : int -> thm list -> tactic
  (* Searches with the given claset extended by the safe elimination rules
     the tableau engine needs to decompose a negated implication or a
     negated universal; a caller supplies only its own rules. *)
  val CS_BLAST_DEPTH_TAC : clasetLib.claset -> int -> tactic
  (* Fixed-depth search with an invocation-owned budget.  The successful
     result has completed kernel replay in the supplied context. *)
  val CS_BLAST_DEPTH_BUDGETED :
    searchBudget.budget -> clasetLib.claset -> int ->
    goal -> Context.t ->
    (goal list * validation) blastSearch.budget_outcome
  (* A yielded turn retains the fixed-depth tableau frontier and its
     reconstruction continuation. The same budget is extended to resume. *)
  val CS_BLAST_DEPTH_RESUMABLE :
    searchBudget.budget -> clasetLib.claset -> int ->
    goal -> Context.t ->
    (goal list * validation) blastSearch.budget_outcome

  val depth_limit : int ref

  (* Run tableau search only.  The result contains the recorded script and
     the full sequence of branch states; no reconstruction is attempted. *)
  val tryIt : int -> thm list -> goal -> try_result
end
