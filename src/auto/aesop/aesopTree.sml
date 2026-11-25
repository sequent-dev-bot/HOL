structure aesopTree :> aesopTree =
struct

open HolKernel

val Fld = FunctionalRecordUpdate.U
val $$ = FunctionalRecordUpdate.$$

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

fun upd_goal z =
  let
    fun from id cgoal store level prio deps copy_of parent cluster norm
             safe_done unsafe_cursor postponed forwarded state =
      {id = id, cgoal = cgoal, store = store, level = level, prio = prio,
       deps = deps, copy_of = copy_of, parent = parent, cluster = cluster,
       norm = norm, safe_done = safe_done, unsafe_cursor = unsafe_cursor,
       postponed = postponed, forwarded = forwarded, state = state}
    fun from' state forwarded postponed unsafe_cursor safe_done norm cluster
              parent copy_of deps prio level store cgoal id =
      from id cgoal store level prio deps copy_of parent cluster norm
        safe_done unsafe_cursor postponed forwarded state
    fun to f
          {id, cgoal, store, level, prio, deps, copy_of, parent, cluster,
           norm, safe_done, unsafe_cursor, postponed, forwarded, state} =
      f id cgoal store level prio deps copy_of parent cluster norm safe_done
        unsafe_cursor postponed forwarded state
  in
    FunctionalRecordUpdate.makeUpdate15 (from, from', to)
  end z

type rapp =
  {id : rid, parent : gid, rule : string, prob : int,
   records : step_record list, store : store,
   created : dependencies, assigned : dependencies,
   clusters : cid list, state : node_state}

type cluster =
  {id : cid, parent : rid, goals : gid list, state : node_state}

type queue_entry = {goal : gid, prio : real, insertion : int}

(* The parent links of goals and rapps, inverted, plus the copy links of
   goals inverted alongside them: [copy_children] sends an original goal to
   the copies of it installed elsewhere in the tree. Rule applications
   and copies are prepended as they arrive. Readers choosing a witness
   recover ascending id order. Goal children are inserted in that order.
   [derive_goal] reads the inverted copy links during every refresh round.
   Scanning the goal table for [copy_of] there would make each round
   quadratic in trees that routinely reach hundreds of goals. *)
type parent_index =
  {rapp_children : (gid, rid list) Redblackmap.dict,
   goal_children : (rid, gid list) Redblackmap.dict,
   copy_children : (gid, gid list) Redblackmap.dict}

type tree_fields =
  {root : gid,
   goals : (gid, goal) Redblackmap.dict,
   rapps : (rid, rapp) Redblackmap.dict,
   clusters : (cid, cluster) Redblackmap.dict,
   index : parent_index,
   queue : queue_entry searchHeap.heap,
   next_gid : int, next_rid : int, next_cid : int,
   next_insertion : int}

datatype tree = Tree of tree_fields

fun upd_tree z =
  let
    fun from root goals rapps clusters index queue next_gid next_rid
             next_cid next_insertion =
      {root = root, goals = goals, rapps = rapps, clusters = clusters,
       index = index, queue = queue, next_gid = next_gid,
       next_rid = next_rid, next_cid = next_cid,
       next_insertion = next_insertion}
    fun from' next_insertion next_cid next_rid next_gid queue index
              clusters rapps goals root =
      from root goals rapps clusters index queue next_gid next_rid
        next_cid next_insertion
    fun to f
          {root, goals, rapps, clusters, index, queue, next_gid, next_rid,
           next_cid, next_insertion} =
      f root goals rapps clusters index queue next_gid next_rid next_cid
        next_insertion
  in
    FunctionalRecordUpdate.makeUpdate10 (from, from', to)
  end z

val ERR = mk_HOL_ERR "aesopTree"
val root_cluster = 0

(* Dependency sets are keyed on metavariable identity, not on the term
   spelling: the same metavariable reaches them both as [clasetMeta.bindings]
   created it and as a normalized goal now spells it, and those differ once a
   type metavariable inside its type is bound.  Under [Term.compare] the two
   spellings do not meet, and every intersection below silently reports no
   dependency at all. *)
fun empty_dependencies () =
  {terms = HOLset.empty clasetMeta.meta_compare,
   types = HOLset.empty Type.compare}

(* [clasetMeta.norm] follows both term and type bindings transitively.
   Taking free metavariables after that walk therefore caches precisely the
   unassigned dependency frontier of the goal. *)
fun dependencies_with store normalize_formula normalize_type
      ({params, asl, w} : cgoal) =
  let
    fun formula (tm, {terms, types} : dependencies) =
      let val normalized = normalize_formula tm
      in
        {terms =
           HOLset.addList
             (terms, clasetMeta.metas_of_normalized store normalized),
         types =
           HOLset.addList
             (types, List.filter clasetMeta.is_tymeta
                       (type_vars_in_term normalized))}
      end
    val {terms, types = formula_types} =
      formula (w, List.foldl formula (empty_dependencies ()) asl)
    fun parameter_type (parameter, types) =
      HOLset.addList
        (types,
         List.filter clasetMeta.is_tymeta
           (Type.type_vars
             (normalize_type (type_of parameter))))
    val types = List.foldl parameter_type formula_types params
  in
    {terms = terms, types = types}
  end

fun dependencies_of store =
  dependencies_with store (clasetMeta.norm store) (clasetMeta.norm_type store)

fun sets_overlap (left, right) =
  let
    val (smaller, larger) =
      if HOLset.numItems left <= HOLset.numItems right then (left, right)
      else (right, left)
  in
    Option.isSome
      (HOLset.find (fn item => HOLset.member (larger, item)) smaller)
  end

fun dependencies_overlap
      ({terms = left_terms, types = left_types} : dependencies)
      ({terms = right_terms, types = right_types} : dependencies) =
  sets_overlap (left_terms, right_terms) orelse
  sets_overlap (left_types, right_types)

fun dependencies_union
      ({terms = left_terms, types = left_types} : dependencies)
      ({terms = right_terms, types = right_types} : dependencies) =
  {terms = HOLset.union (left_terms, right_terms),
   types = HOLset.union (left_types, right_types)}

fun dependencies_intersection
      ({terms = left_terms, types = left_types} : dependencies)
      ({terms = right_terms, types = right_types} : dependencies) =
  {terms = HOLset.intersection (left_terms, right_terms),
   types = HOLset.intersection (left_types, right_types)}

fun dependencies_difference
      ({terms = left_terms, types = left_types} : dependencies)
      ({terms = right_terms, types = right_types} : dependencies) =
  {terms = HOLset.difference (left_terms, right_terms),
   types = HOLset.difference (left_types, right_types)}

fun dependencies_empty ({terms, types} : dependencies) =
  HOLset.isEmpty terms andalso HOLset.isEmpty types

fun extend_priority priority aesopRule.RSafe = priority
  | extend_priority priority (aesopRule.RNorm _) = priority
  | extend_priority priority (aesopRule.RUnsafe percent) =
      if 1 <= percent andalso percent <= 100 then
        priority + Math.ln (Real.fromInt percent / 100.0)
      else
        raise ERR "extend_priority"
          "an unsafe rule percentage must be in the range 1--100"

fun queue_compare
      ({prio = left, insertion = left_count, ...} : queue_entry,
       {prio = right, insertion = right_count, ...} : queue_entry) =
  case Real.compare (right, left) of
      EQUAL => Int.compare (left_count, right_count)
    | result => result

fun root (Tree {root, ...}) = root

fun goal (Tree {goals, ...}) id =
  case Redblackmap.peek (goals, id) of
      SOME value => value
    | NONE => raise ERR "goal" ("unknown goal id " ^ Int.toString id)

fun rapp (Tree {rapps, ...}) id =
  case Redblackmap.peek (rapps, id) of
      SOME value => value
    | NONE => raise ERR "rapp" ("unknown rapp id " ^ Int.toString id)

fun cluster (Tree {clusters, ...}) id =
  case Redblackmap.peek (clusters, id) of
      SOME value => value
    | NONE =>
        raise ERR "cluster" ("unknown cluster id " ^ Int.toString id)

fun goals (Tree {goals, ...}) = Redblackmap.listItems' goals
fun rapps (Tree {rapps, ...}) = Redblackmap.listItems' rapps
fun clusters (Tree {clusters, ...}) = Redblackmap.listItems' clusters

fun rapp_count (Tree {rapps, ...}) = Redblackmap.numItems rapps

fun empty_index () : parent_index =
  {rapp_children = Redblackmap.mkDict Int.compare,
   goal_children = Redblackmap.mkDict Int.compare,
   copy_children = Redblackmap.mkDict Int.compare}

fun index_lookup table key =
  case Redblackmap.peek (table, key) of
      NONE => []
    | SOME entries => entries

fun index_copy ((original, copy), table) =
  Redblackmap.insert
    (table, original, copy :: index_lookup table original)

fun index_install {parent, rid, children, copies}
      ({rapp_children, goal_children, copy_children} : parent_index)
      : parent_index =
  {rapp_children =
     Redblackmap.insert
       (rapp_children, parent, rid :: index_lookup rapp_children parent),
   goal_children = Redblackmap.insert (goal_children, rid, children),
   copy_children = List.foldl index_copy copy_children copies}

fun reverse_child_rapps (Tree {index, ...}) parent =
  index_lookup (#rapp_children index) parent

fun child_rapps tree parent = List.rev (reverse_child_rapps tree parent)

fun has_child_rapps tree parent = not (null (reverse_child_rapps tree parent))

fun rapp_goals (Tree {index, ...}) parent =
  index_lookup (#goal_children index) parent

(* The copies of [original] installed anywhere in the tree.  [install_rapp]
   canonicalises the key through [original_goal], so a copy never keys
   copies of its own and this relation is one level deep. *)
fun reverse_copy_goals (Tree {index, ...}) original =
  index_lookup (#copy_children index) original

fun active_cgoal ({cgoal, norm, ...} : goal) =
  case norm of
      Unnormalised => cgoal
    | Normalised {cgoal = result, ...} => result
    | NormProved _ =>
        raise ERR "active_cgoal" "a norm-proved goal has no open cgoal"

fun active_store ({store, norm, ...} : goal) =
  case norm of
      Unnormalised => store
    | Normalised {store = result, ...} => result
    | NormProved {store = result, ...} => result

fun is_normalised ({norm = Unnormalised, ...} : goal) = false
  | is_normalised _ = true

(* Normalisation rewrites a goal in place, so its node keeps the goal's
   level; a rule application descends one level. *)
fun node_at level (goal : goal) =
  clasetGoal.create
    {goals = [active_cgoal goal], store = active_store goal,
     level = level}

fun goal_node (goal : goal) = node_at (#level goal) goal
fun child_node (goal : goal) = node_at (#level goal + 1) goal

fun changed node next =
  null (clasetGoal.goals next) orelse
  not (clasetGoal.equal (node, next))

(* One rendered-tactic alternative, as the single-goal replay record that
   reproduces it.  [rendered] is the parent goal the tactic ran on. *)
fun rendered_record node rendered (result as (goals, validation)) =
  Option.map
    (fn next =>
      (clasetReplay.make_record
         {kind = clasetReplay.Wrapper, target = 1, consumed = NONE,
          created = {terms = [], types = []},
          eigenvariables = clasetReplay.new_free_names rendered goals,
          validation = validation,
          action = clasetReplay.fixed_action_on rendered result,
          children = map (fn _ => NONE) goals},
       next))
    (clasetGoal.unrender node 1 result)

fun engine_results step node =
  seq.map
    (fn (record, next) => ([record], next))
    (step (node, 1))

fun rendered_results ctxt tactic node =
  let
    val rendered = clasetGoal.render node 1
  in
    seq.mapPartial
      (fn result =>
        Option.map
          (fn (record, next) => ([record], next))
          (rendered_record node rendered result))
      (tactic rendered ctxt)
  end

(* One reading of a rule's alternatives for both engine phases: [aesopNorm]
   takes the unique one, the safe phase of [aesopSearch] commits to one and
   its unsafe phase installs them all. *)
fun rule_results_in ctxt ({apply, ...} : rule) node =
  case apply of
      aesopRule.EngineStep step => engine_results step node
    | aesopRule.ContextualStep make_step =>
        seq.delay (fn () => engine_results (make_step ctxt) node)
    | aesopRule.RenderedTactic tactic =>
        rendered_results ctxt tactic node
    | aesopRule.MultiStep make_steps =>
        seq.flatten
          (seq.fromList
            (map
              (fn make_step =>
                seq.delay (fn () => engine_results (make_step ctxt) node))
              make_steps))

fun unique_rule_result_in ctxt rule node =
  case seq.take 2 (rule_results_in ctxt rule node) of
      [result] => SOME result
    | _ => NONE

(* A copied goal discharges its original sibling but is not a child the
   rule action emitted, so replay never descends into one. *)
fun direct_children tree rid =
  List.filter
    (fn id => not (Option.isSome (#copy_of (goal tree id))))
    (rapp_goals tree rid)

fun goal_with_state state (goal : goal) : goal =
  upd_goal goal (Fld #state state) $$

fun rapp_with_state state
      ({id, parent, rule, prob, records, store, created, assigned,
        clusters, ...} : rapp) : rapp =
  {id = id, parent = parent, rule = rule, prob = prob,
   records = records, store = store, created = created,
   assigned = assigned, clusters = clusters, state = state}

fun cluster_with_state state
      ({id, parent, goals, ...} : cluster) : cluster =
  {id = id, parent = parent, goals = goals, state = state}

(* A copy is useful to its original only through the proved applications
   connecting it to the application that emitted the original.  The latter
   application is excluded: its state is what the copy helps derive.  Each
   pair records the goal and the exact child application extraction must
   choose to retain that path. *)
fun copy_support tree original_parent record_path copy =
  case original_parent of
      NONE => NONE
    | SOME target =>
        let
          fun walk current path =
            case #parent (current : goal) of
                NONE => NONE
              | SOME rid =>
                  if rid = target then SOME path
                  else
                    let val application = rapp tree rid
                    in
                      if #state application <> Proved then NONE
                      else
                        walk (goal tree (#parent application))
                          (if record_path then
                             (#parent application, rid) :: path
                           else path)
                    end
          val current = goal tree copy
        in
          if #state current = Proved then walk current []
          else NONE
        end

fun copy_support_path tree original copy =
  Option.map List.rev
    (copy_support tree (#parent (goal tree original)) true copy)

fun independently_proved tree (current : goal) =
  case #norm current of
      NormProved _ => true
    | _ =>
        List.exists
          (fn rid => #state (rapp tree rid) = Proved)
          (reverse_child_rapps tree (#id current))

fun has_copy_support tree (current : goal) =
  List.exists
    (Option.isSome o copy_support tree (#parent current) false)
    (reverse_copy_goals tree (#id current))

fun add_support_path lookup insert path required =
  let
    fun add [] required = SOME required
      | add ((id, rid) :: rest) required =
          case lookup required id of
              NONE => add rest (insert required (id, rid))
            | SOME rid' =>
                if rid = rid' then add rest required else NONE
  in
    add path required
  end

fun select_copy_supports_with add_path tree goals initial_required =
  let
    fun choose paths support required =
      case seq.cases paths of
          NONE => NONE
        | SOME (path, rest) =>
            (case add_path path required of
                 NONE => choose rest support required
               | SOME required' =>
                   (case support required' of
                        SOME result => SOME result
                      | NONE => choose rest support required))

    (* Backtracking changes the required applications. The available
       paths depend only on the tree, so share each lazy path sequence and
       its continuation across retries. *)
    fun prepare [] = SOME
      | prepare (id :: rest) =
          if independently_proved tree (goal tree id) then prepare rest
          else
            let
              val paths = seq.mapPartial (copy_support_path tree id)
                (seq.fromList (List.rev (reverse_copy_goals tree id)))
              val support = Portable.HOLSusp.delay (fn () => prepare rest)
            in
              choose paths
                (fn required => Portable.HOLSusp.force support required)
            end
  in
    prepare goals initial_required
  end

fun select_copy_supports tree =
  let
    fun lookup required id =
      Option.map #2 (List.find (fn (key, _) => key = id) required)
    fun insert required entry = entry :: required
  in
    select_copy_supports_with (add_support_path lookup insert) tree
  end

fun select_copy_supports_map tree =
  let
    fun lookup required id = Redblackmap.peek (required, id)
    fun insert required (id, rid) = Redblackmap.insert (required, id, rid)
  in
    select_copy_supports_with (add_support_path lookup insert) tree
  end

fun compatible_copy_supports tree goals =
  Option.isSome
    (select_copy_supports_map tree goals (Redblackmap.mkDict Int.compare))

fun has_copies (Tree {index, ...}) =
  Redblackmap.numItems (#copy_children index) <> 0

(* The goals of a cluster are conjunctive, and copy-derived proofs must also
   admit one compatible selection of all applications on their support
   paths.  Without copies, every proved member already has its own proof.
   Sticking stays conservative: a stuck member may yet be discharged by a
   copy the search is still working on. *)
fun derive_cluster tree ({goals, ...} : cluster) =
  case goals of
      [] => Proved
    | id :: rest =>
        let
          val current = goal tree id
          val state = #state current
          (* A refresh can retract a proof before changing the goal state.
             Recheck support, but one path needs no compatibility search. *)
          fun compatible () =
            case rest of
                [] => independently_proved tree current orelse
                      has_copy_support tree current
              | _ => compatible_copy_supports tree goals
        in
          if state <> Unknown andalso
             List.all (fn id => #state (goal tree id) = state) rest andalso
             (state = Stuck orelse not (has_copies tree) orelse compatible ())
          then state
          else Unknown
        end

fun derive_rapp tree ({clusters, ...} : rapp) =
  let
    fun scan state [] = state
      | scan state (id :: rest) =
          case #state (cluster tree id) of
              Proved => scan state rest
            | Stuck => Stuck
            | Unknown => scan Unknown rest
  in
    scan Proved clusters
  end

fun search_exhausted (current : goal) =
  is_normalised current andalso #safe_done current andalso
  null (#unsafe_cursor current) andalso null (#postponed current)

(* A copy carries the very obligation of its original under a store that
   has assigned more, so proving the copy proves the original.  Reading
   that back here is what lets a cluster be the plain conjunction its
   subgoals are: the branch that assigns the shared metavariables proves
   the copies it made, and the originals become proved with them.
   Sticking deliberately ignores copies -- a goal whose own alternatives
   are exhausted is stuck until some copy of it is actually proved, and
   the copy's branch may still be under search. *)
fun derive_goal tree (current : goal) =
  let
    val id = #id current
    fun scan [] all_stuck =
          if has_copy_support tree current then Proved
          else if all_stuck then Stuck
          else Unknown
      | scan (rid :: rest) all_stuck =
          case #state (rapp tree rid) of
              Proved => Proved
            | Stuck => scan rest all_stuck
            | Unknown => scan rest false
  in
    case #norm current of
        NormProved _ => Proved
      | _ => scan (reverse_child_rapps tree id) (search_exhausted current)
  end

fun refresh_once (tree as Tree (fields as {goals, rapps, clusters, ...})) =
  let
    val changed = ref false
    (* A single local update usually changes only a few states per sweep.
       Fold the snapshot and share the unchanged parts of each map. *)
    fun refresh_state id state old rebuild current table =
      if state = old then table
      else
        (changed := true;
         Redblackmap.insert (table, id, rebuild state current))
    fun rebuild (new_goals, new_rapps, new_clusters) =
      Tree
        (upd_tree fields (Fld #goals new_goals) (Fld #rapps new_rapps)
           (Fld #clusters new_clusters) $$)
    val clusters' =
      Redblackmap.foldl
        (fn (id, current : cluster, table) =>
          refresh_state id (derive_cluster tree current) (#state current)
            cluster_with_state current table)
        clusters clusters
    val with_clusters = rebuild (goals, rapps, clusters')
    val rapps' =
      Redblackmap.foldl
        (fn (id, current : rapp, table) =>
          refresh_state id (derive_rapp with_clusters current) (#state current)
            rapp_with_state current table)
        rapps rapps
    val with_rapps = rebuild (goals, rapps', clusters')
    val goals' =
      Redblackmap.foldl
        (fn (id, current : goal, table) =>
          refresh_state id (derive_goal with_rapps current) (#state current)
            goal_with_state current table)
        goals goals
  in
    if !changed then SOME (rebuild (goals', rapps', clusters'))
    else NONE
  end

fun refresh tree =
  case refresh_once tree of
      NONE => tree
    | SOME next => refresh next

(* Without copies, only the unique parent can depend on a changed state.
   Stop at the first unchanged node.  Copy support can also depend on the
   applications elsewhere in the tree, so those trees use the fixpoint. *)
fun refresh_goal_ancestors id (tree as Tree fields) =
  let
    val current = goal tree id
    val state = derive_goal tree current
  in
    if state = #state current then tree
    else
      let
        val goals =
          Redblackmap.insert
            (#goals fields, id, goal_with_state state current)
        val next = Tree (upd_tree fields (Fld #goals goals) $$)
      in
        case #parent current of
            NONE => next
          | SOME _ => refresh_cluster_ancestors (#cluster current) next
      end
  end
and refresh_cluster_ancestors id (tree as Tree fields) =
  let
    val current = cluster tree id
    val state = derive_cluster tree current
  in
    if state = #state current then tree
    else
      let
        val clusters =
          Redblackmap.insert
            (#clusters fields, id, cluster_with_state state current)
      in
        refresh_rapp_ancestors (#parent current)
          (Tree (upd_tree fields (Fld #clusters clusters) $$))
      end
  end
and refresh_rapp_ancestors id (tree as Tree fields) =
  let
    val current = rapp tree id
    val state = derive_rapp tree current
  in
    if state = #state current then tree
    else
      let
        val rapps =
          Redblackmap.insert
            (#rapps fields, id, rapp_with_state state current)
      in
        refresh_goal_ancestors (#parent current)
          (Tree (upd_tree fields (Fld #rapps rapps) $$))
      end
  end

(* Adding an independent proof is monotone in the state order
   Stuck < Unknown < Proved. Seed the fixed point by propagating along the
   parent path, then let the global sweeps resolve any off-path copies. *)
fun refresh_after_proof propagate tree =
  let val next = propagate tree
  in if has_copies next then refresh next else next
  end

fun refresh_goal id proof_retracted tree =
  if not (has_copies tree) then refresh_goal_ancestors id tree
  else
    let val current = goal tree id
    in
      if proof_retracted orelse
         derive_goal tree current <> #state current
      then refresh tree
      else tree
    end

fun queue_goal id prio (queue, insertion) =
  (searchHeap.add {goal = id, prio = prio, insertion = insertion} queue,
   insertion + 1)

fun enqueue_goal id
      (tree as Tree (fields as {queue, next_insertion, ...})) =
  let
    val (queue', next_insertion') =
      queue_goal id (#prio (goal tree id)) (queue, next_insertion)
  in
    Tree
      (upd_tree fields (Fld #queue queue')
         (Fld #next_insertion next_insertion') $$)
  end

fun create {node, unsafe_cursor} =
  case clasetGoal.goals node of
      [cgoal] =>
        let
          val store = clasetGoal.store node
          val initial : goal =
            {id = 1, cgoal = cgoal, store = store,
             level = clasetGoal.level node, prio = 0.0,
             deps = dependencies_of store cgoal, copy_of = NONE,
             parent = NONE, cluster = root_cluster,
             norm = Unnormalised, safe_done = false,
             unsafe_cursor = unsafe_cursor, postponed = [],
             forwarded = [], state = Unknown}
          val queue =
            searchHeap.add
              {goal = 1, prio = 0.0, insertion = 0}
              (searchHeap.empty queue_compare)
        in
          Tree
            {root = 1,
             goals =
               Redblackmap.insert
                 (Redblackmap.mkDict Int.compare, 1, initial),
             rapps = Redblackmap.mkDict Int.compare,
             clusters = Redblackmap.mkDict Int.compare,
             index = empty_index (),
             queue = queue, next_gid = 2, next_rid = 1,
             next_cid = 1, next_insertion = 1}
        end
    | _ =>
        raise ERR "create" "the initial node must contain exactly one goal"

fun add_created
      (record, {terms, types} : dependencies) =
  let
    val created = clasetReplay.created_of record
  in
    {terms = HOLset.addList (terms, #terms created),
     types = HOLset.addList (types, #types created)}
  end

fun created_of records =
  List.foldl add_created (empty_dependencies ()) records

fun cgoal_under store ({params, asl, w} : cgoal) : cgoal =
  {params = map (clasetMeta.norm store) params,
   asl = map (clasetMeta.norm store) asl,
   w = clasetMeta.norm store w}

fun assigned_between parent_store child_store =
  let val {terms, types} = clasetMeta.new_bindings parent_store child_store
  in
    {terms = HOLset.fromList clasetMeta.meta_compare terms,
     types = HOLset.fromList Type.compare types}
  end

fun components children =
  let
    fun dependent (child : goal) = not (dependencies_empty (#deps child))
    fun singleton_groups children = map (fn child => [child]) children
    fun indexed children =
      let
        val vertices = map (fn child => (child, ref false)) children
        val shared = ref false
        fun add_to_index vertex (dependency, table) =
          case Redblackmap.peek (table, dependency) of
              NONE => Redblackmap.insert (table, dependency, ref [vertex])
            | SOME bucket =>
                (shared := true; bucket := vertex :: !bucket; table)
        fun index_child (vertex as (child : goal, _), (terms, types)) =
          (HOLset.foldl (add_to_index vertex) terms (#terms (#deps child)),
           HOLset.foldl (add_to_index vertex) types (#types (#deps child)))
        val (terms, types) =
          List.foldl index_child
            (Redblackmap.mkDict clasetMeta.meta_compare,
             Redblackmap.mkDict Type.compare) vertices

        fun discover ((child, reached), layer) =
          if !reached then layer else (reached := true; child :: layer)
        fun consume index (dependency, layer) =
          case Redblackmap.peek (index, dependency) of
              NONE => layer
            | SOME bucket =>
                let
                  val neighbours = !bucket
                  val _ = bucket := []
                in
                  List.foldl discover layer neighbours
                end
        fun expand (child : goal, layer) =
          HOLset.foldl (consume types)
            (HOLset.foldl (consume terms) layer (#terms (#deps child)))
            (#types (#deps child))

        (* Process each metavariable's bucket once. Fresh goal IDs ascend
           in insertion order, so sorting each new layer by ID preserves
           the order in which the goals were installed. *)
        fun compare_ids (left : goal, right : goal) =
          Int.compare (#id left, #id right)
        fun close [] selected = List.rev selected
          | close layer selected =
              close
                (Listsort.sort compare_ids (List.foldl expand [] layer))
                (List.revAppend (layer, selected))
        fun partition [] groups = List.rev groups
          | partition ((child : goal, reached) :: rest) groups =
              if not (dependent child) then
                partition rest ([child] :: groups)
              else if !reached then partition rest groups
              else
                (reached := true;
                 partition rest (close [child] [] :: groups))
      in
        if !shared then partition vertices []
        else singleton_groups children
      end

    (* Zero or one dependent child cannot share a metavariable. *)
    fun can_share [] = false
      | can_share (child :: rest) =
          if dependent child then List.exists dependent rest
          else can_share rest
  in
    if can_share children then indexed children
    else singleton_groups children
  end

fun goal_with_cluster cluster_id (goal : goal) : goal =
  upd_goal goal (Fld #cluster cluster_id) $$

fun phase_probability aesopRule.RSafe = 100
  | phase_probability (aesopRule.RUnsafe percent) =
      if 1 <= percent andalso percent <= 100 then percent
      else
        raise ERR "install_rapp"
          "an unsafe rule percentage must be in the range 1--100"
  | phase_probability (aesopRule.RNorm _) =
      raise ERR "install_rapp" "normalisation does not create rapp nodes"

(* A rule application installs fresh goals with ids greater than its
   parent goal's id.  The same check also prevents ancestry cycles. *)
fun checked_ancestor id ancestor =
  if ancestor < id then ancestor
  else raise ERR "ancestry" "non-decreasing goal ids in ancestry"

fun ancestry tree start =
  let
    fun walk id =
      case #parent (goal tree id) of
          NONE => []
        | SOME parent =>
            (id, parent) ::
            walk (checked_ancestor id (#parent (rapp tree parent)))
  in
    walk start
  end

(* Installation records the original goal even when copying a copy. *)
fun original_goal tree id = Option.getOpt (#copy_of (goal tree id), id)

fun take_through_rapp wanted [] = []
  | take_through_rapp wanted (entry :: rest) =
      let val (_, current) = entry
      in
        entry ::
        (if current = wanted then []
         else take_through_rapp wanted rest)
      end

fun copying_sources_on_path tree parent_id relevant_assigned
      dropped_candidates =
  let
    val path = ancestry tree parent_id
    (* HOL types are inhabited, so a dropped metavariable needs no
       synthesis goal.  It still drives copying exactly like an
       assignment if it was created along this path. Every creator of
       an assigned or dropped candidate can therefore bound the search. *)
    val candidates = dependencies_union relevant_assigned dropped_candidates
    fun creator ((_, rid), result as (missing, _)) =
      let val created = #created (rapp tree rid)
      in
        if dependencies_overlap candidates created then
          (dependencies_difference missing created, SOME rid)
        else result
      end
    val (missing, topmost) = List.foldl creator (candidates, NONE) path
    val copying =
      dependencies_union relevant_assigned
        (dependencies_difference dropped_candidates missing)
    val bounded_path =
      if dependencies_empty copying then []
      else if dependencies_overlap relevant_assigned missing then path
      else
        case topmost of
            NONE => path
          | SOME rid => take_through_rapp rid path
    val path_originals =
      List.foldl
        (fn ((id, _), origins) => HOLset.add (origins, original_goal tree id))
        (HOLset.empty Int.compare) bounded_path

    fun add_source path_goal (id, result as (seen, sources)) =
      if id = path_goal orelse
         not (dependencies_overlap copying (#deps (goal tree id)))
      then result
      else
        let val original = original_goal tree id
        in
          (* Canonical origins both skip copies of path goals and collapse
             multiple candidates copied from the same goal. *)
          if HOLset.member (seen, original) then result
          else (HOLset.add (seen, original), (id, original) :: sources)
        end

    val (_, reversed_sources) =
      List.foldl
        (fn ((path_goal, parent_rapp), result) =>
          List.foldl (add_source path_goal) result
            (rapp_goals tree parent_rapp))
        (path_originals, []) bounded_path
  in
    List.rev reversed_sources
  end

fun copying_sources tree parent_id assigned child_specs =
  let
    val parent = goal tree parent_id
    val relevant_assigned =
      dependencies_intersection assigned (#deps parent)
    val unassigned = dependencies_difference (#deps parent) relevant_assigned
    fun retains_all (_, deps : dependencies, _, _) =
      HOLset.isSubset (#terms unassigned, #terms deps) andalso
      HOLset.isSubset (#types unassigned, #types deps)
    val dropped_candidates =
      if dependencies_empty unassigned then unassigned
      else
        case child_specs of
            [] => unassigned
          | [(_, deps, _, _)] => dependencies_difference unassigned deps
          | _ =>
              (* One child can retain every dependency of the parent. *)
              if List.exists retains_all child_specs then
                empty_dependencies ()
              else
                let
                  val child_dependencies =
                    List.foldl
                      (fn ((_, deps, _, _), dependencies) =>
                        dependencies_union dependencies deps)
                      (empty_dependencies ()) child_specs
                in
                  dependencies_difference unassigned child_dependencies
                end
  in
    if dependencies_empty relevant_assigned andalso
       dependencies_empty dropped_candidates then []
    else
      copying_sources_on_path tree parent_id relevant_assigned
        dropped_candidates
  end

fun install_rapp parent_id
      ({rule, phase, records, node, forwarded} : rapp_data)
      (tree as
       Tree
         (fields as
          {goals, rapps, clusters, index, queue, next_gid, next_rid, next_cid,
           next_insertion, ...})) =
  let
    val parent = goal tree parent_id
    val _ =
      if #state parent <> Stuck then ()
      else
        raise ERR "install_rapp"
          "a rapp cannot be installed below a stuck goal"
    val rid = next_rid
    val child_store = clasetGoal.store node
    val child_priority = extend_priority (#prio parent) phase
    val child_cgoals = clasetGoal.goals node
    val assigned =
      assigned_between (active_store parent) child_store
    val child_specs =
      map
        (fn cgoal =>
          (cgoal, dependencies_of child_store cgoal, NONE,
           case forwarded of
               NONE => #forwarded parent
             | SOME hypothesis => hypothesis :: #forwarded parent))
        child_cgoals
    val copy_sources =
      if not (Option.isSome (#parent parent)) orelse
         dependencies_empty (#deps parent)
      then []
      else copying_sources tree parent_id assigned child_specs
    val copy_specs =
      map
        (fn (source, original) =>
          let
            val source_goal = goal tree source
            val cgoal = cgoal_under child_store (#cgoal source_goal)
            (* This already normalized both the formulas and each
               parameter's type in the child store. *)
            val deps = dependencies_with child_store Lib.I Lib.I cgoal
          in
            (cgoal, deps, SOME original, #forwarded source_goal)
          end)
        copy_sources
    fun make_child
          ((cgoal, deps, copy_of, forwarded), (id, children)) =
      let
        val child : goal =
          {id = id, cgoal = cgoal, store = child_store,
           level = clasetGoal.level node, prio = child_priority,
           deps = deps, copy_of = copy_of,
           parent = SOME rid, cluster = root_cluster,
           norm = Unnormalised, safe_done = false,
           unsafe_cursor = [], postponed = [],
           forwarded = forwarded, state = Unknown}
      in
        (id + 1, child :: children)
      end

    val (next_gid', reversed_children) =
      List.foldl make_child
        (List.foldl make_child (next_gid, []) child_specs) copy_specs
    val ordered_children = List.rev reversed_children
    val child_ids = map #id ordered_children
    (* The copy links this application adds, for the inverted index.  This
       is the only place a copy is ever created, so the index needs no
       other maintenance. *)
    val copy_links =
      List.mapPartial
        (fn ({id, copy_of, ...} : goal) =>
          Option.map (fn source => (source, id)) copy_of)
        ordered_children
    val groups = components ordered_children

    fun make_cluster
          (members, (id, cluster_entries, goal_map, ids)) =
      let
        val current : cluster =
          {id = id, parent = rid, goals = map #id members, state = Unknown}
        val goal_map' =
          List.foldl
            (fn (child, map) =>
              Redblackmap.insert
                (map, #id child, goal_with_cluster id child))
            goal_map members
      in
        (id + 1, (id, current) :: cluster_entries, goal_map',
         id :: ids)
      end

    val (next_cid', cluster_entries, clustered_goals,
         reversed_cluster_ids) =
      List.foldl make_cluster
        (next_cid, [], goals, []) groups
    val cluster_ids = List.rev reversed_cluster_ids
    val current_rapp : rapp =
      {id = rid, parent = parent_id, rule = rule,
       prob = phase_probability phase, records = records,
       store = child_store, created = created_of records,
       assigned = assigned,
       clusters = cluster_ids, state = Unknown}
    val (queue', next_insertion') =
      List.foldl (fn (id, pending) => queue_goal id child_priority pending)
        (queue, next_insertion) child_ids
    val installed =
      Tree
        (upd_tree fields
           (Fld #goals clustered_goals)
           (Fld #rapps (Redblackmap.insert (rapps, rid, current_rapp)))
           (Fld #clusters
              (Redblackmap.insertList
                 (clusters, List.rev cluster_entries)))
           (Fld #index
              (index_install
                 {parent = parent_id, rid = rid, children = child_ids,
                  copies = copy_links}
                 index))
           (Fld #next_gid next_gid')
           (Fld #next_rid (next_rid + 1))
           (Fld #next_cid next_cid')
           (Fld #queue queue')
           (Fld #next_insertion next_insertion') $$)
  in
    (* A nonclosing application starts Unknown, as do all its children
       and copies.  Its parent is not Stuck, so adding the alternative
       and the new copy links cannot change an existing state. *)
    {rapp = rid, goals = child_ids,
     tree =
       if not (null child_ids) then installed
       else refresh_after_proof (refresh_rapp_ancestors rid) installed}
  end

(* The goal's identity and parent link are unchanged, so the index stands. *)
fun store_goal (current : goal) (Tree (fields as {goals, ...})) =
  Tree
    (upd_tree fields
       (Fld #goals (Redblackmap.insert (goals, #id current, current))) $$)

fun replace_norm norm deps (goal : goal) : goal =
  upd_goal goal (Fld #norm norm) (Fld #deps deps) $$

fun set_normalised id {records, cgoal, store} tree =
  let
    val current = goal tree id
    val was_proved =
      case #norm current of NormProved _ => true | _ => false
    val deps =
      if not was_proved andalso
         Portable.pointer_eq (cgoal, active_cgoal current) andalso
         Portable.pointer_eq (store, active_store current)
      then #deps current
      else dependencies_of store cgoal
  in
    refresh_goal id was_proved
      (store_goal
        (replace_norm
          (Normalised {records = records, cgoal = cgoal, store = store})
          deps current)
        tree)
  end

fun set_norm_proved id {records, store} tree =
  let val current = goal tree id
  in
    refresh_after_proof (refresh_goal_ancestors id)
      (store_goal
        (replace_norm
          (NormProved {records = records, store = store})
          (#deps current) current)
        tree)
  end

fun replace_search_state {safe_done, unsafe_cursor, postponed}
      (goal : goal) : goal =
  upd_goal goal
    (Fld #safe_done safe_done)
    (Fld #unsafe_cursor unsafe_cursor)
    (Fld #postponed postponed) $$

(* These fields enter the state equations only through exhaustion.
   Advancing a cursor that still has candidates leaves the equations
   unchanged, including those for goals with copies. *)
fun set_search_state id fields tree =
  let
    val current = goal tree id
    val updated = replace_search_state fields current
    val next = store_goal updated tree
  in
    if search_exhausted current = search_exhausted updated then next
    else refresh_goal id false next
  end

fun set_safe_done id value tree =
  let val {unsafe_cursor, postponed, ...} = goal tree id
  in
    set_search_state id
      {safe_done = value, unsafe_cursor = unsafe_cursor,
       postponed = postponed} tree
  end

fun set_unsafe_cursor id value tree =
  let val {safe_done, postponed, ...} = goal tree id
  in
    set_search_state id
      {safe_done = safe_done, unsafe_cursor = value,
       postponed = postponed} tree
  end

fun exhaust_goal id tree =
  let
    val current = goal tree id
    val tree' =
      if is_normalised current then tree
      else
        set_normalised id
          {records = [], cgoal = #cgoal current, store = #store current}
          tree
  in
    set_search_state id
      {safe_done = true, unsafe_cursor = [], postponed = []} tree'
  end

fun nonterminal state = state = Unknown

fun goal_irrelevant tree id =
  let
    fun goal_path gid =
      let val current = goal tree gid
      in
        not (nonterminal (#state current)) orelse
        (case #parent current of
             NONE => false
           | SOME rid =>
               let val application = rapp tree rid
               in
                 not (nonterminal (#state application)) orelse
                 goal_path (checked_ancestor gid (#parent application))
               end)
      end
  in
    goal_path id
  end

fun rapp_irrelevant tree id =
  let val current = rapp tree id
  in
    not (nonterminal (#state current)) orelse
    goal_irrelevant tree (#parent current)
  end

fun cluster_irrelevant tree id =
  let val current = cluster tree id
  in
    not (nonterminal (#state current)) orelse
    rapp_irrelevant tree (#parent current)
  end

fun pop_goal_with skip tree =
  let
    (* Insertion counters are unique, so [queue_compare] is total. *)
    fun pop (current as Tree (fields as {queue, ...})) =
      if searchHeap.is_empty queue then (NONE, current)
      else
        let
          val (entry, queue') = searchHeap.delete_min queue
          val rest = Tree (upd_tree fields (Fld #queue queue') $$)
          val id = #goal entry
        in
          if skip rest id then pop rest
          else (SOME id, rest)
        end
  in
    pop tree
  end

fun pop_goal tree = pop_goal_with goal_irrelevant tree

fun pop_goal_including_irrelevant tree =
  pop_goal_with (fn _ => fn _ => false) tree

end
