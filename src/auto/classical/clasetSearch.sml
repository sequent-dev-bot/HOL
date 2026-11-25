(*
  Search drivers for the classical reasoner.

  DEPTH_FIRST and DEPTH_SOLVE follow Pure/search.ML lines 38--75:
  an explicit stack of lazy child sequences and duplicate-solution
  suppression.  BEST_FIRST follows lines 180--199, including eager child
  enumeration and deletion of all equal minima.  ASTAR follows lines
  226--249, using the same heap frontier but removing one minimum at a time.
  DEEPEN follows lines 147--154 and restarts the bounded search until its
  first successful bound.

  DEPTH_SOLVE additionally implements dynamic, lossless commitment.  A node
  carries the bindings made while solving its first open goal.  When that
  goal disappears, alternatives in its subtree are discarded exactly when
  no such binding occurs in a remaining goal or in a binding reachable from
  one.  This is the persistent-store counterpart of blast's trail-based
  clashVar/prune test.  Frontier searches do not make per-goal commitments,
  so BEST_FIRST and ASTAR deliberately do not prune.

  This dynamic test supersedes the old static safe_depth_tac DETERM test.
  Isabelle 2005 made rigid goals deterministic, as its comment says.  A 2009
  refactoring inverted that branch and releases since then have cut choices
  precisely for goals containing shared schematic variables.  Keeping the
  actual binding dependency is both stronger and more selective: rigid
  subtrees commit, while shared metavariables retain the needed choices.

  The "classical.trace" trace is registered by clasetReplay, and each
  driver takes the level to report at as its first argument.  Level 1
  reports exhausted/bounded searches, level 2 reports expansions, bounds,
  and pruning, and level 3 prints complete candidate nodes.
*)
structure clasetSearch :> clasetSearch =
struct

open HolKernel

type node = clasetGoal.node
type expansion = node -> node seq.seq

val node_limit = ref 100000
val last_node_count = ref 0
val last_pruning_count = ref 0

fun node_count () = !last_node_count
fun pruning_count () = !last_pruning_count

fun show_node node =
  Parse.term_to_string (clasetGoal.canonical_rendering node)

(* Every driver reports an admitted expansion here, so this is also where
   the shared work meter is charged. *)
fun expansion_trace level driver count node =
  (searchWork.note_expansion ();
   traceUtil.trace level 2
     (fn () =>
       driver ^ " expansion " ^ Int.toString count ^
       ", goals=" ^ Int.toString (clasetGoal.goal_count node) ^
       ", size=" ^ Int.toString (clasetGoal.size node));
   traceUtil.trace level 3
     (fn () => driver ^ " candidate: " ^ show_node node))

fun member_node node = List.exists (fn old => clasetGoal.equal (node, old))

datatype node_set =
    NodeList of int * node list
  | NodeSet of node Binaryset.set

val empty_node_set = NodeList (0, [])

fun compare_node (left, right) =
  case Int.compare (clasetGoal.goal_count left, clasetGoal.goal_count right) of
      EQUAL => clasetGoal.compare (left, right)
    | order => order

fun node_set_size (NodeList (count, _)) = count
  | node_set_size (NodeSet nodes) = Binaryset.numItems nodes

fun node_set_member current (NodeList (_, nodes)) = member_node current nodes
  | node_set_member current (NodeSet nodes) =
      Binaryset.member (nodes, current)

(* Keep the first few entries on a list to avoid computing ordering keys. *)
fun node_set_add node (NodeList (count, nodes)) =
      if count < 8 then NodeList (count + 1, node :: nodes)
      else
        NodeSet
          (List.foldl (fn (old, set) => Binaryset.add (set, old))
             (Binaryset.empty compare_node) (node :: nodes))
  | node_set_add node (NodeSet nodes) =
      NodeSet (Binaryset.add (nodes, node))

fun DEPTH_FIRST level satisfied expand initial =
  let
    fun depth _ [] = seq.empty
      | depth used (states :: rest) =
          seq.delay
            (fn () =>
              case seq.cases states of
                  NONE => depth used rest
                | SOME (current, siblings) =>
                    if satisfied current andalso
                       not (node_set_member current used)
                    then
                      seq.cons current
                        (depth (node_set_add current used)
                           (siblings :: rest))
                    else
                      (expansion_trace level "depth-first"
                         (node_set_size used + 1) current;
                       depth used
                         (expand current :: siblings :: rest)))
  in
    depth empty_node_set [seq.result initial]
  end

val same_meta = clasetMeta.same_meta
val same_tymeta = clasetMeta.same_tymeta

fun add_meta (meta, metas) = Lib.op_insert same_meta meta metas
fun add_tymeta (meta, metas) = Lib.op_insert same_tymeta meta metas

fun union_metas left right = List.foldl add_meta right left
fun union_tymetas left right = List.foldl add_tymeta right left

fun binding_diff parent child =
  clasetMeta.new_bindings (clasetGoal.store parent) (clasetGoal.store child)

fun add_mark
      ({terms = more_terms, types = more_types} : clasetGoal.binding_mark)
      ({terms, types} : clasetGoal.binding_mark) =
  {terms = union_metas more_terms terms,
   types = union_tymetas more_types types}

fun replicate count value = List.tabulate (count, fn _ => value)

(* Pruned depth search expands the first open goal.  A one-child transition
   stays in the same subtree and accumulates its bindings.  Branch children
   start fresh marks: bindings made by their parent inference belong to the
   enclosing choice point, whose store diff is checked separately. *)
fun note_transition parent child =
  let
    val child_count = clasetGoal.child_count parent child
    val inherited = clasetGoal.binding_marks child
    val marks =
      if child_count = 1 then
        (case inherited of
             [] => []
           | mark :: rest => add_mark (binding_diff parent child) mark :: rest)
      else if child_count > 1 then
        replicate child_count clasetGoal.empty_mark @
        List.drop (inherited, child_count)
      else inherited
  in
    clasetGoal.set_binding_marks marks
      (clasetGoal.set_level (clasetGoal.level parent + 1) child)
  end

fun goal_terms ({params, asl, w} : clasetGoal.cgoal) =
  params @ (w :: asl)

val marked_terms = clasetGoal.marked_terms
val marked_types = clasetGoal.marked_types

fun dependency_closure store goals =
  let
    val all_terms = List.concat (map goal_terms goals)
    (* Follow raw residues so the closure includes intermediate bindings. *)
    fun follow_terms [] seen types = (seen, types)
      | follow_terms (meta :: rest) seen types =
          if HOLset.member (seen, meta) then follow_terms rest seen types
          else
            let val seen' = HOLset.add (seen, meta)
            in
              case clasetMeta.term_residue store meta of
                  NONE => follow_terms rest seen' types
                | SOME residue =>
                    follow_terms (marked_terms [residue] @ rest) seen'
                      (marked_types [residue] @ types)
            end

    fun follow_types [] seen = seen
      | follow_types (meta :: rest) seen =
          if HOLset.member (seen, meta) then follow_types rest seen
          else
            let val seen' = HOLset.add (seen, meta)
            in
              case clasetMeta.type_residue store meta of
                  NONE => follow_types rest seen'
                | SOME residue =>
                    follow_types
                      (List.filter clasetMeta.is_tymeta (type_vars residue) @
                       rest) seen'
            end

    val (terms, types) =
      follow_terms (marked_terms all_terms)
        (HOLset.empty clasetMeta.meta_compare) (marked_types all_terms)
  in
    (terms, follow_types types (HOLset.empty Type.compare))
  end

fun mark_clashes visible
      ({terms, types} : clasetGoal.binding_mark) =
  if List.null terms andalso List.null types then false
  else
    let val (visible_terms, visible_types) = Portable.HOLSusp.force visible
    in
      List.exists (fn meta => HOLset.member (visible_terms, meta)) terms
      orelse
      List.exists (fn meta => HOLset.member (visible_types, meta)) types
    end

type frame =
  {source : node option, states : node seq.seq, ancestors : node_set}

(* Compare as paths, treating the active subtree as one interval. *)
fun compare_active_path [] _ = EQUAL
  | compare_active_path _ [] = GREATER
  | compare_active_path (part :: path) (other :: candidate) =
      case Int.compare (part, other) of
          EQUAL => compare_active_path path candidate
        | order => order

fun active_completed source child =
  case clasetGoal.goal_paths source of
      [] => false
    | active :: _ =>
        let
          (* Goal paths start ordered and replacing a goal splices its
             children in path order. Earlier goals may still be present
             when an expansion constructs a fresh frontier. *)
          fun completed [] = true
            | completed (candidate :: rest) =
                case compare_active_path active candidate of
                    LESS => true
                  | EQUAL => false
                  | GREATER => completed rest
        in
          completed (clasetGoal.goal_paths child)
        end

fun discard_subtree child frames =
  let
    val visible =
      Portable.HOLSusp.delay
        (fn () =>
          dependency_closure (clasetGoal.store child) (clasetGoal.goals child))
    fun discard count [] = (count, [])
      | discard count (frame :: rest) =
          (case #source frame of
               NONE => (count, frame :: rest)
             | SOME source =>
                 if not (active_completed source child) then
                   (count, frame :: rest)
                 else
                   if mark_clashes visible (binding_diff source child) then
                     (count, frame :: rest)
                   else discard (count + 1) rest)
  in
    discard 0 frames
  end

(* A state identical to one of its own ancestors adds nothing: [expand] is a
   function of the node, so the subtree below the repetition is the subtree
   below the ancestor, which the same search reaches there by a shorter path.
   Without this an unsafe wrapper and the rule it undoes alternate for ever.
   Each frame keeps its source and the ancestors still on the stack beneath
   it. Pruning restores the set from the nearest surviving frame. *)
fun DEPTH_SOLVE level expand initial =
  let
    val no_ancestors = empty_node_set
    fun ancestors_of [] = no_ancestors
      | ancestors_of ((frame : frame) :: _) = #ancestors frame
    fun frame_for source frames =
      {source = SOME source,
       states = seq.map (note_transition source) (expand source),
       ancestors = node_set_add source (ancestors_of frames)}

    fun depth _ [] = seq.empty
      | depth used ((frame : frame) :: rest) =
          seq.delay
            (fn () =>
              case seq.cases (#states frame) of
                  NONE => depth used rest
                | SOME (current, siblings) =>
                    let
                      val rest0 =
                        {source = #source frame, states = siblings,
                         ancestors = #ancestors frame} :: rest
                      val completed =
                        case #source frame of
                            NONE => false
                          | SOME source => active_completed source current
                      val rest1 =
                        if completed then
                          let
                            val (discarded, kept) =
                              discard_subtree current rest0
                            val _ =
                              last_pruning_count :=
                                !last_pruning_count + discarded
                            val _ =
                              if discarded = 0 then ()
                              else
                                traceUtil.trace level 2
                                  (fn () =>
                                    "dynamic pruning discarded " ^
                                    Int.toString discarded ^
                                    " choice points")
                          in
                            kept
                          end
                        else rest0
                    in
                      if List.null (clasetGoal.goals current) andalso
                         not (member_node current used)
                      then
                        seq.cons current
                          (depth (current :: used) rest1)
                      else if node_set_member current (#ancestors frame) then
                        (traceUtil.trace level 2
                           (fn () =>
                             "depth-solve dropped a state repeating an \
                             \ancestor");
                         depth used rest1)
                      else
                        (expansion_trace level "depth-solve"
                           (length used + 1) current;
                         depth used (frame_for current rest1 :: rest1))
                    end)
  in
    seq.delay
      (fn () =>
        (last_pruning_count := 0;
         depth []
           [{source = NONE, states = seq.result initial,
             ancestors = no_ancestors}]))
  end

val split_satisfied = Lib.partition

val check_period = 100

fun limit_reached limit count =
  limit > 0 andalso count >= limit andalso
  (count = limit orelse count mod check_period = 0)

fun allow_expansion level driver limit count node =
  if limit_reached (limit ()) count then
    (last_node_count := count;
     traceUtil.trace level 1
       (fn () =>
         driver ^ " stopped at node limit " ^ Int.toString (limit ()));
     false)
  else
    (last_node_count := count + 1;
     expansion_trace level driver (count + 1) node;
     true)

fun add_nodes values heap =
  List.foldr (fn (node, current) => searchHeap.add node current)
    heap values

(* A state's provability does not depend on the path that reached it, and
   a frontier driver enumerates all of a state's children when it expands
   it, so expanding the same state again can only repeat that enumeration.
   Without the test the drivers do repeat it: a universal assumption whose
   elimination consumes it is re-derived on a sibling branch, the instance
   takes a fresh metavariable each round, and the cycle reaches the
   frontier at an unchanged size -- three states, alternating, for as long
   as the caller waits.  The key is the state as it stands, metavariable
   names included, so the instances differ round to round; the states
   that precede them do not, and cutting those cuts the cycle.
   DEPTH_SOLVE needs no such set: it commits and backtracks, and its
   ancestor test already covers its own paths.

   Isabelle's BEST_FIRST (src/Pure/search.ML @ Isabelle2025-2) carries no
   closed set.  This is deliberately past it: the suppressed expansion is
   one the driver has already made. *)
fun frontier_search {driver, compare, remove_minimum, limit}
      level satisfied expand initial =
  let
    fun classify (news, heap, count, seen) =
      let val (solutions, pending) = split_satisfied satisfied news
      in
        if List.null solutions then
          next (add_nodes pending heap, count, seen)
        else seq.fromList solutions
      end

    and next (heap, count, seen) =
      if searchHeap.is_empty heap then
        (last_node_count := count;
         traceUtil.trace level 1 (fn () => driver ^ " search exhausted");
         seq.empty)
      else
        let
          val (current, remaining) = remove_minimum heap
        in
          if Binaryset.member (seen, current) then
            (last_pruning_count := !last_pruning_count + 1;
             traceUtil.trace level 2
               (fn () =>
                 driver ^ " dropped a state it has already expanded");
             next (remaining, count, seen))
          else if not (allow_expansion level driver limit count current)
          then
            seq.empty
          else
            classify
              (seqUtil.list_of
                 (seq.map (note_transition current) (expand current)),
               remaining, count + 1, Binaryset.add (seen, current))
        end

    fun start () =
      (last_node_count := 0;
       last_pruning_count := 0;
       classify
         ([clasetGoal.set_level 0 initial],
          searchHeap.empty compare, 0,
          Binaryset.empty clasetGoal.compare))
  in
    seq.delay start
  end

(* Equal minima represent the same search state, so expand the first of
   them and discard its duplicates. *)
val best_minimum = searchHeap.delete_min_class

fun best_first limit =
  frontier_search
    {driver = "best-first", compare = clasetGoal.compare,
     remove_minimum = best_minimum, limit = limit}

fun BEST_FIRST level = best_first (fn () => !node_limit) level

fun BOUNDED_BEST_FIRST bound = best_first (fn () => bound)

fun astar_cost node =
  clasetGoal.size node + 5 * clasetGoal.level node

fun astar_compare (left, right) =
  Int.compare (astar_cost left, astar_cost right)

fun ASTAR level =
  frontier_search
    {driver = "A*", compare = astar_compare,
     remove_minimum = searchHeap.delete_min,
     limit = fn () => !node_limit}
    level

datatype frontier_state =
    Ready of
      {heap : node searchHeap.heap, seen : node Binaryset.set,
       count : int}
  | Selected of
      {current : node, remaining : node searchHeap.heap,
       seen : node Binaryset.set, count : int}
  | Scanning of
      {cursor : node seq.seq, reversed : node list,
       remaining : node searchHeap.heap,
       seen : node Binaryset.set, count : int, paid : bool}
  | Answers of
      {results : node list, heap : node searchHeap.heap,
       seen : node Binaryset.set, count : int}
  | Done

datatype frontier_session = FrontierSession of (unit -> frontier_step)
and frontier_step =
    StepResult of node
  | StepExhausted
  | StepYielded of searchBudget.kind * searchBudget.usage
  | StepLimitReached of searchBudget.kind * searchBudget.usage

datatype frontier_outcome =
    FrontierResult of {node : node, session : frontier_session}
  | FrontierExhausted
  | FrontierYielded of
      {kind : searchBudget.kind, usage : searchBudget.usage,
       session : frontier_session}
  | FrontierLimitReached of
      {kind : searchBudget.kind, usage : searchBudget.usage}

fun new_frontier_session
      {driver, compare, remove_minimum}
      level budget satisfied expand initial =
  let
    exception Yield of searchBudget.kind * searchBudget.usage
    val root = clasetGoal.set_level 0 initial
    val state =
      ref (Ready
        {heap = searchHeap.add root (searchHeap.empty compare),
         seen = Binaryset.empty clasetGoal.compare, count = 0})

    fun admit kind =
      searchBudget.charge budget kind
      handle searchBudget.LimitReached (limited, usage) =>
        raise Yield (limited, usage)

    fun advance () =
      let
        fun loop () =
          case !state of
              Done => StepExhausted
            | Answers {results = [], heap, seen, count} =>
                (state := Ready
                   {heap = heap, seen = seen, count = count};
                 loop ())
            | Answers
                {results = answer :: rest, heap, seen, count} =>
                (state := Answers
                   {results = rest, heap = heap,
                    seen = seen, count = count};
                 StepResult answer)
            | Ready {heap, seen, count} =>
                if searchHeap.is_empty heap then
                  (state := Done;
                   last_node_count := count;
                   traceUtil.trace level 1
                     (fn () => driver ^ " search exhausted");
                   StepExhausted)
                else
                  let
                    val _ = admit searchBudget.Candidate
                    val (current, remaining) = remove_minimum heap
                  in
                    if Binaryset.member (seen, current) then
                      (last_pruning_count := !last_pruning_count + 1;
                       traceUtil.trace level 2
                         (fn () =>
                           driver ^
                           " dropped a state it has already expanded");
                       state := Ready
                         {heap = remaining, seen = seen, count = count};
                       loop ())
                    else if satisfied current then
                      (state := Answers
                         {results = [current], heap = remaining,
                          seen = seen, count = count};
                       loop ())
                    else
                      (state := Selected
                         {current = current, remaining = remaining,
                          seen = seen, count = count};
                       loop ())
                  end
            | Selected {current, remaining, seen, count} =>
                let
                  val _ = admit searchBudget.Application
                  val _ = last_node_count := count + 1
                  val _ = expansion_trace level driver (count + 1) current
                  val cursor =
                    seq.map (note_transition current) (expand current)
                in
                  state := Scanning
                    {cursor = cursor, reversed = [],
                     remaining = remaining,
                     seen = Binaryset.add (seen, current),
                     count = count + 1, paid = false};
                  loop ()
                end
            | Scanning {cursor, reversed, remaining, seen, count, paid} =>
                let
                  (* A pull cut off inside [cursor] has been paid for:
                     its retry must not charge again. *)
                  val _ =
                    if paid then ()
                    else
                      (admit searchBudget.Candidate;
                       state := Scanning
                         {cursor = cursor, reversed = reversed,
                          remaining = remaining, seen = seen,
                          count = count, paid = true})
                in
                  case seq.cases cursor of
                      SOME (child, rest) =>
                        (state := Scanning
                           {cursor = rest, reversed = child :: reversed,
                            remaining = remaining, seen = seen,
                            count = count, paid = false};
                         loop ())
                    | NONE =>
                        let
                          val (solutions, pending) =
                            split_satisfied satisfied (rev reversed)
                        in
                          if null solutions then
                            state := Ready
                              {heap = add_nodes pending remaining,
                               seen = seen, count = count}
                          else
                            state := Answers
                              {results = solutions,
                               heap = add_nodes pending remaining,
                               seen = seen, count = count};
                          loop ()
                        end
                end
      in
        loop ()
        handle Yield (kind, usage) => StepYielded (kind, usage)
             | searchBudget.LimitReached (kind, usage) =>
                 StepYielded (kind, usage)
             | exn => (state := Done; raise exn)
      end
  in
    FrontierSession advance
  end

val new_best_session =
  new_frontier_session
    {driver = "best-first", compare = clasetGoal.compare,
     remove_minimum = best_minimum}

val new_astar_session =
  new_frontier_session
    {driver = "A*", compare = astar_compare,
     remove_minimum = searchHeap.delete_min}

fun resume_frontier
      (session as FrontierSession advance) =
  case advance () of
      StepResult node => FrontierResult {node = node, session = session}
    | StepExhausted => FrontierExhausted
    | StepYielded (kind, usage) =>
        FrontierYielded
          {kind = kind, usage = usage, session = session}
    | StepLimitReached (kind, usage) =>
        FrontierLimitReached {kind = kind, usage = usage}

fun DEEPEN level (increment, limit) bounded start initial =
  let
    val _ =
      if increment > 0 then ()
      else
        raise mk_HOL_ERR "clasetSearch" "DEEPEN"
          "the increment must be positive"

    fun deepen bound =
      seq.delay
        (fn () =>
          if List.null (clasetGoal.goals initial) then seq.empty
          else if bound > limit then
            (traceUtil.trace level 1
               (fn () =>
                 "deepening exhausted at bound " ^ Int.toString limit);
             seq.empty)
          else
            let
              val _ =
                traceUtil.trace level 2
                  (fn () => "trying depth bound " ^ Int.toString bound)
            in
              case seq.cases (bounded bound initial) of
                  NONE => deepen (bound + increment)
                | SOME (result, rest) => seq.cons result rest
            end)
  in
    deepen start
  end

end
