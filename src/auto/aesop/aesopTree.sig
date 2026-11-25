signature aesopTree =
sig
  type term = Term.term
  type cgoal = clasetGoal.cgoal
  type store = clasetMeta.store
  type step_record = clasetReplay.step_record
  type rule = aesopRule.rule

  type gid = int
  type rid = int
  type cid = int

  datatype node_state = Unknown | Proved | Stuck

  type dependencies =
    {terms : clasetMeta.meta HOLset.set,
     types : clasetMeta.tymeta HOLset.set}

  datatype norm_state =
      Unnormalised
    | Normalised of
        {records : step_record list, cgoal : cgoal, store : store}
    | NormProved of {records : step_record list, store : store}

  type rapp_data =
    {rule : string, phase : aesopRule.rphase,
     records : step_record list, node : clasetGoal.node,
     forwarded : term option}

  type goal =
    {id : gid, cgoal : cgoal, store : store, level : int,
     prio : real, deps : dependencies, copy_of : gid option,
     parent : rid option, cluster : cid, norm : norm_state,
     safe_done : bool, unsafe_cursor : rule list,
     postponed : rapp_data list, forwarded : term list,
     state : node_state}

  type rapp =
    {id : rid, parent : gid, rule : string, prob : int,
     records : step_record list, store : store,
     created : dependencies, assigned : dependencies,
     clusters : cid list, state : node_state}

  type cluster =
    {id : cid, parent : rid, goals : gid list, state : node_state}

  type tree

  val dependencies_of : store -> cgoal -> dependencies
  val dependencies_empty : dependencies -> bool
  val assigned_between : store -> store -> dependencies

  (* Priorities are log probabilities.  Norm and safe rules have cost zero. *)
  val extend_priority : real -> aesopRule.rphase -> real

  (* The initial node must contain exactly one goal. *)
  val create :
    {node : clasetGoal.node, unsafe_cursor : rule list} -> tree

  val root : tree -> gid
  val goal : tree -> gid -> goal
  val rapp : tree -> rid -> rapp
  val cluster : tree -> cid -> cluster
  val goals : tree -> goal list
  val rapps : tree -> rapp list
  val clusters : tree -> cluster list
  (* The number of installed rule applications, without building the list
     of them: the search consults it once per expansion to police its
     global rapp budget. *)
  val rapp_count : tree -> int

  val child_rapps : tree -> gid -> rid list
  val has_child_rapps : tree -> gid -> bool
  val independently_proved : tree -> goal -> bool
  val active_cgoal : goal -> cgoal
  val active_store : goal -> store
  val is_normalised : goal -> bool
  (* Action-emitted children of a rule application, excluding the copied
     obligations, which replay discharges through their originals. *)
  val direct_children : tree -> rid -> gid list

  (* Select one mutually compatible proved-copy path per obligation.
     Candidate choice backtracks when a later obligation conflicts. *)
  val select_copy_supports :
    tree -> gid list -> (gid * rid) list -> (gid * rid) list option
  val select_copy_supports_map :
    tree -> gid list -> (gid, rid) Redblackmap.dict ->
    (gid, rid) Redblackmap.dict option

  (* The goal's engine node.  Normalisation rewrites a goal in place and
     uses [goal_node]; a rule application descends, so it uses
     [child_node]. *)
  val goal_node : goal -> clasetGoal.node
  val child_node : goal -> clasetGoal.node
  (* An application makes progress when it closes the node or leaves a
     different one. *)
  val changed : clasetGoal.node -> clasetGoal.node -> bool
  val cgoal_under : store -> cgoal -> cgoal

  (* Every alternative one rule offers on a node, as the replay records and
     the node each of them produces.  Normalisation and search read the same
     alternatives under different determinism requirements, so the reading
     lives here, beside the rendered-result lifting it needs. *)
  val rule_results_in :
    Context.t -> rule -> clasetGoal.node ->
    (step_record list * clasetGoal.node) seq.seq
  (* The one alternative of a deterministic rule; NONE when the rule offers
     none, or offers a choice.  Looking at two results decides that without
     forcing the tail of an otherwise lazy sequence. *)
  val unique_rule_result_in :
    Context.t -> rule -> clasetGoal.node ->
    (step_record list * clasetGoal.node) option

  (* Installation creates ordinary children.  Copying extends this single
     boundary in aesopTree without requiring search clients to change.
     Sibling alternatives may still be installed after one has proved the
     parent; a stuck parent cannot be extended. *)
  val install_rapp :
    gid -> rapp_data -> tree ->
    {rapp : rid, goals : gid list, tree : tree}

  val set_normalised :
    gid -> {records : step_record list, cgoal : cgoal, store : store} ->
    tree -> tree
  val set_norm_proved :
    gid -> {records : step_record list, store : store} -> tree -> tree
  val set_safe_done : gid -> bool -> tree -> tree
  val set_unsafe_cursor : gid -> rule list -> tree -> tree
  (* The safe phase's whole outcome for a goal, applied as one update. *)
  val set_search_state :
    gid ->
    {safe_done : bool, unsafe_cursor : rule list,
     postponed : rapp_data list} -> tree -> tree

  (* Marks every search phase complete without asserting a state directly.
     The ordinary state equations then decide whether the goal is stuck. *)
  val exhaust_goal : gid -> tree -> tree

  val enqueue_goal : gid -> tree -> tree
  val pop_goal : tree -> gid option * tree
  (* Safe-goal completion must drain siblings even after another sibling
     makes their common unsafe search branch irrelevant. *)
  val pop_goal_including_irrelevant : tree -> gid option * tree

  val goal_irrelevant : tree -> gid -> bool
  val rapp_irrelevant : tree -> rid -> bool
  val cluster_irrelevant : tree -> cid -> bool
end
