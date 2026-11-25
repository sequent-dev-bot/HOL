signature aesopNorm =
sig
  type tree = aesopTree.tree
  type gid = aesopTree.gid
  type rule = aesopRule.rule

  datatype outcome =
      Complete of {tree : tree, iterations : int}
    | IterationLimit of
        {tree : tree, iterations : int, rule : string}

  (* Successful rules are counted against [max_depth].  The fixpoint is
     installed atomically; an iteration-limit result retains the input tree
     so callers can stop the branch without exposing a partial norm chain. *)
  (* Each rule attempt is charged to the budget, when one is given. *)
  val normalise_in :
    Context.t -> searchBudget.budget option ->
    {max_depth : int, rules : rule list} -> gid -> tree -> outcome
end
