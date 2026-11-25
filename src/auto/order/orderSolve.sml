structure orderSolve :> orderSolve =
struct

open HolKernel boolLib orderRulesTheory

val node_limit = ref 50

type work = {meter : orderData.meter, max_nodes : int option}

fun capped_work () : work =
  {meter = searchBudget.free_charger, max_nodes = SOME (!node_limit)}

fun budget_work budget : work =
  {meter = searchBudget.charger budget, max_nodes = NONE}

fun candidate (work : work) = #candidate (#meter work) ()
fun application (work : work) = #application (#meter work) ()
fun normalization (work : work) = #normalization (#meter work) ()

(* A strict step is taken apart on the way in: [STRORD R x y] is [R x y]
   together with [x <> y], and nothing else about it is used.  So the
   graph carries weak edges only, chaining is transitivity alone, and the
   single closing rule is antisymmetry against a distinction.  That is
   complete for the usual refutation -- a cycle with a strict edge in it
   gives both directions between that edge's ends, so antisymmetry
   identifies them and the edge's own distinction denies it -- and it
   spares the procedure three further chaining cases. *)

datatype path =
    Proved of thm
  | Pending of thm Portable.HOLSusp.susp

fun path_theorem (Proved theorem) = theorem
  | path_theorem (Pending pending) = Portable.HOLSusp.force pending

(* Ordinary graph searches need proofs only along the selected paths.
   Metered calls construct them at the original charged operations. *)
fun derive_path (work : work) derive =
  case #max_nodes work of
      NONE => Proved (derive ())
    | SOME _ => Pending (Portable.HOLSusp.delay derive)

type edge = {source : term, target : term, path : path}

fun search work f [] = NONE
  | search work f (x :: xs) =
      (candidate work;
       case f x of NONE => search work f xs | found => found)

fun expand work (context : orderData.context) facts =
  let
    val {reflexive, ...} = #axioms context
    val intro =
      Option.map
        (fn theorem => Portable.HOLSusp.delay
          (fn () => MATCH_MP order_weak_of_equal theorem))
        reflexive
    fun weak_of_equal introduce equality =
      derive_path work
        (fn () =>
          let val theorem = equality () in
            application work;
            MATCH_MP (Portable.HOLSusp.force introduce) theorem
          end)
    fun edge (x, y) path = {source = x, target = y, path = path}
    fun one (fact : orderData.fact, (edges, equalities, distinctions)) =
      let
        val _ = candidate work
        val theorem = #theorem fact
      in
        case #literal fact of
            orderData.Weak (x, y) =>
              (edge (x, y) (Proved theorem) :: edges, equalities, distinctions)
          | orderData.Strict (x, y) =>
              let
                val _ = application work
                val weak =
                  derive_path work (fn () => MATCH_MP order_strict_weak theorem)
                val distinct =
                  derive_path work
                    (fn () => MATCH_MP order_strict_distinct theorem)
              in
                (edge (x, y) weak :: edges, equalities,
                 (x, y, distinct) :: distinctions)
              end
          | orderData.Equal (x, y) =>
              let
                val edges' =
                  case intro of
                      NONE => edges
                    | SOME r =>
                        let
                          val forward = weak_of_equal r (fn () => theorem)
                          val backward =
                            weak_of_equal r (fn () => SYM theorem)
                        in
                          edge (y, x) backward :: edge (x, y) forward :: edges
                        end
              in
                (edges', (x, y, theorem) :: equalities, distinctions)
              end
          | orderData.Distinct (x, y) =>
              (edges, equalities, (x, y, Proved theorem) :: distinctions)
      end
    val (edges, equalities, distinctions) =
      List.foldl one ([], [], []) facts
  in
    (List.rev edges, List.rev equalities, List.rev distinctions)
  end

fun bounded_nodes maximum initial edges =
  let
    fun add tm (state as (count, seen)) =
      if HOLset.member (seen, tm) then state
      else (count + 1, HOLset.add (seen, tm))
    fun scan (state as (count, _)) edges =
      if count > maximum then NONE
      else
        case edges of
            [] => SOME state
          | (e : edge) :: rest =>
              scan (add (#target e) (add (#source e) state)) rest
  in
    scan initial edges
  end

datatype reachability =
    ReachedList of (term * path) list
  | ReachedIndex of path Termtab.table

fun reached work (ReachedList reached_nodes) tm =
      Option.map snd
        (search work
          (fn pair as (n, _) =>
            if aconv n tm then SOME pair else NONE)
          reached_nodes)
  | reached _ (ReachedIndex table) tm = Termtab.lookup table tm

fun settle target path (ReachedList reached_nodes) =
      ReachedList ((target, path) :: reached_nodes)
  | settle target path (ReachedIndex table) =
      ReachedIndex (Termtab.update (target, path) table)

fun outgoing_edges edges =
  let
    fun add (edge : edge, (index, outgoing)) =
      (index + 1, Termtab.cons_list (#source edge, (index, edge)) outgoing)
  in
    #2 (List.foldl add (0, Termtab.empty) edges)
  end

structure TermGraph = Graph(
  type key = term
  val ord = Term.compare
  val pp = Parse.pp_term
)

fun cyclic_components edges =
  let
    fun add ({source, target, ...} : edge, graph) =
      graph
      |> TermGraph.default_node (source, ())
      |> TermGraph.default_node (target, ())
      |> TermGraph.add_edge (source, target)
    val graph = List.foldl add TermGraph.empty edges
    fun index (nodes, (i, table)) =
      case nodes of
          _ :: _ :: _ =>
            (i + 1, List.foldl
              (fn (node, acc) => Termtab.update (node, i) acc) table nodes)
        | _ => (i, table)
  in
    #2 (List.foldl index (0, Termtab.empty) (TermGraph.strong_conn graph))
  end

(* A scan can use a newly reached node at later edges in the same round.
   Earlier edges must wait for the next round. Schedule just the edges
   that can relax, in the same (round, original position) order, so that
   a node still gets the same first path. Edges from a source reached
   in the initial scans are eligible from round zero. *)
fun indexed_rounds work relax outgoing source nodes =
  let
    val empty =
      Redblackmap.mkDict (Lib.pair_compare (Int.compare, Int.compare))
    (* Settled targets keep their first path and cannot relax again. *)
    fun schedule known round (index, edge : edge) pending =
      if aconv (#target edge) source orelse
         Option.isSome (reached work known (#target edge)) then pending
      else Redblackmap.insert (pending, (round, index), edge)
    fun outgoing_from from =
      Option.getOpt (Termtab.lookup outgoing from, [])
    val initial = ReachedIndex nodes
    fun seed from pending =
      List.foldl
        (fn (entry, pending) => schedule initial 0 entry pending)
        pending (outgoing_from from)
    val pending =
      Termtab.fold (fn (from, _) => seed from) nodes (seed source empty)
    fun run known pending =
      case Redblackmap.firsti pending of
          NONE => known
        | SOME (key as (round, last), edge) =>
            let
              val (rest, _) = Redblackmap.remove (pending, key)
              val (known', changed) = relax (edge, (known, false))
              val next =
                if changed then
                  let
                    fun add (entry as (position, _), pending) =
                      schedule known'
                        (if position > last then round else round + 1)
                        entry pending
                  in
                    List.foldl add rest (outgoing_from (#target edge))
                  end
                else rest
            in
              run known' next
            end
  in
    run initial pending
  end

(* Everything the source reaches, one path per node. A node is settled
   the first time it is reached. Ordinary calls construct proofs only
   along the paths a caller actually needs. *)
fun reachable work transitivity edges outgoing observe source =
  case transitivity of
      NONE =>
        (case #max_nodes work of
             NONE =>
               ReachedList
                 (List.map (fn e => (#target e, #path e))
                   (List.filter
                     (fn e => (candidate work; aconv (#source e) source))
                     edges))
           | SOME _ =>
               let
                 val bucket = Option.getOpt
                   (Termtab.lookup (Portable.HOLSusp.force outgoing) source,
                    [])
                 (* The bucket is reversed. Put the first original edge
                    first so it still supplies the proof. *)
                 fun add ((_, e : edge), nodes) = (#target e, #path e) :: nodes
               in
                 ReachedList (List.foldl add [] bucket)
               end)
    | SOME instantiate =>
        let
          val step = instantiate ()
          (* Keep the same settlement and comparison order for metered
             calls.  Ordinary calls can index by alpha-equivalence. *)
          val empty =
            case #max_nodes work of
                NONE => ReachedList []
              | SOME _ => ReachedIndex Termtab.empty
          fun chain first (edge : edge) =
            let
              fun derive () =
                let
                  (* The graph already supplies the three endpoints of
                     the relation-instantiated transitivity rule. *)
                  val rule =
                    SPECL [source, #source edge, #target edge]
                      (path_theorem step)
                in
                  MP (MP rule (path_theorem first)) (path_theorem (#path edge))
                end
            in
              application work;
              derive_path work derive
            end
          fun settle_edge target path known =
            (observe (target, path); (settle target path known, true))
          fun relax (e, (known, changed)) =
            (candidate work;
             if aconv (#target e) source orelse
               Option.isSome (reached work known (#target e))
             then (known, changed)
             else if aconv (#source e) source then
               settle_edge (#target e) (#path e) known
             else
               (case reached work known (#source e) of
                    SOME path =>
                      settle_edge (#target e) (chain path e) known
                  | NONE => (known, changed)))
          (* A changing round settles a new target from the finite
             edge list. *)
          fun rounds left reached =
            let
              val (reached', changed) =
                List.foldl relax (reached, false) edges
            in
              if not changed then reached'
              else
                case reached' of
                    ReachedIndex nodes =>
                      if left = 1 then
                        indexed_rounds work relax
                          (Portable.HOLSusp.force outgoing) source nodes
                      else rounds (left - 1) reached'
                  | ReachedList _ => rounds 0 reached'
            end
        in
          (* Small or forward chains often finish before an index pays
             for itself. Metered searches keep the complete scans. *)
          rounds (if Option.isSome (#max_nodes work) then 2 else 0) empty
        end

fun reach_from work transitive distinctions edges =
  let
    (* Share the index across traversals and repeated crossing checks. *)
    val outgoing = Portable.HOLSusp.delay (fn () => outgoing_edges edges)
    (* Share the rule across ordinary traversals, and instantiate it only
       when a composed path is used. Metered traversals keep the original
       eager instantiation for each source. *)
    fun transitivity theorem =
      let
        fun derive () = MATCH_MP order_weak_trans theorem
      in
        case #max_nodes work of
            NONE => (fn () => Proved (derive ()))
          | SOME _ =>
              let val step = derive_path work derive
              in fn () => step end
      end
    val step = Option.map transitivity transitive
    fun traverse observe source =
      reachable work step edges outgoing observe source
    val compute = traverse (fn _ => ())
    (* Crossing can use two sources. Limit retained reachability tables
       and keep each metered traversal observable. *)
    val from =
      case #max_nodes work of
          NONE => compute
        | SOME _ => memoUtil.bounded_memo 2 aconv compute
    fun reach source =
      let val known = from source
      in reached work known
      end
    val may_cross =
      case #max_nodes work of
          NONE => (fn _ => true)
        | SOME _ =>
            let
              val first = ref true
              val attempts = ref 3
              (* A bounded scan is enough to detect when building the
                 index can pay for itself over many crossing checks. *)
              fun many_distinctions () =
                (ignore (List.drop (distinctions, 16)); true)
                handle Subscript => false
              val components =
                Portable.HOLSusp.delay (fn () =>
                  if many_distinctions () then SOME (cyclic_components edges)
                  else NONE)
              fun has_edges tm =
                Option.isSome
                  (Termtab.lookup (Portable.HOLSusp.force outgoing) tm)
              fun same_cycle source target =
                case Portable.HOLSusp.force components of
                    NONE => true
                  | SOME table =>
                      (case Termtab.lookup table source of
                           NONE => false
                         | SOME index =>
                             Termtab.lookup table target = SOME index)
            in
              fn (source, target) =>
                (* Keep the first crossing cheap. Check for outgoing
                   edges before counting a pair toward the SCC scan. *)
                if !first then
                  (first := false; true)
                else
                  has_edges source andalso has_edges target andalso
                  (if !attempts > 0 then (attempts := !attempts - 1; true)
                   else same_cycle source target)
            end
    fun reach_one source target =
      case (#max_nodes work, step) of
          (SOME _, SOME _) =>
            let
              (* A weak literal needs only its first path. Scheduling and
                 settlement are the same as for a full traversal. *)
              exception Found of path
              fun observe (node, path) =
                if aconv node target then raise Found path else ()
            in
              (ignore (traverse observe source); NONE)
              handle Found path => SOME path
            end
        | (SOME _, NONE) =>
            search work
              (fn edge =>
                if aconv (#source edge) source andalso
                   aconv (#target edge) target
                then SOME (#path edge) else NONE)
              edges
        | (NONE, _) => reach source target
    (* With at most one crossing, each source has just one destination.
       A full traversal pays off only when multiple distinctions can
       reuse its reachability table. *)
    val reach_crossing_from =
      case distinctions of
          _ :: _ :: _ => reach
        | _ => reach_one
    fun reach_crossing (x, y) =
      if may_cross (x, y) then
        Option.mapPartial
          (fn up =>
            Option.map (fn down => (up, down)) (reach_crossing_from y x))
          (reach_crossing_from x y)
      else NONE
  in
    {reach_crossing = reach_crossing, reach_one = reach_one}
  end

(* The two chains that meet on a distinction. *)
fun crossing work (context : orderData.context) reach pair =
  let
    val {antisymmetric, ...} = #axioms context
  in
    case antisymmetric of
        NONE => NONE
      | SOME antisymmetric =>
          (case reach pair of
               NONE => NONE
             | SOME (up, down) =>
                 let
                   val up_theorem = path_theorem up
                   val down_theorem = path_theorem down
                 in
                   SOME
                     (application work;
                      MATCH_MP
                        (MATCH_MP
                           (MATCH_MP order_weak_antisymmetric antisymmetric)
                           up_theorem)
                        down_theorem)
                 end)
  end

fun stated work equalities (x, y) =
  search work
    (fn (a, b, theorem) =>
       if aconv a x andalso aconv b y then SOME theorem
       else if aconv a y andalso aconv b x then SOME (SYM theorem)
       else NONE)
    equalities

fun equality_lookup (work : work) equalities =
  case (#max_nodes work, equalities) of
      (SOME _, _ :: _ :: _ :: _ :: _) =>
        let
          fun key (x, y) =
            if Term.compare (x, y) = GREATER then ((y, x), true)
            else ((x, y), false)
          val compare = Lib.pair_compare (Term.compare, Term.compare)
          fun build () =
            let
              fun add ((x, y, theorem), index) =
                let val (pair, reversed) = key (x, y)
                in Redblackmap.insert (index, pair, (theorem, reversed)) end
            in
              List.foldl add (Redblackmap.mkDict compare)
                (List.rev equalities)
            end
          val index = Portable.HOLSusp.delay build
          val scans = ref 8
        in
          fn endpoints =>
            (* Keep early lookups cheap. Repeated misses pay for a
               shared index. The first equality in either direction
               wins, and symmetry is applied only to the chosen proof. *)
            if !scans > 0 then
              (scans := !scans - 1; stated work equalities endpoints)
            else
              let val (pair, reversed) = key endpoints
              in
                Option.map
                  (fn (theorem, orientation) =>
                    if orientation = reversed then theorem else SYM theorem)
                  (Redblackmap.peek (Portable.HOLSusp.force index, pair))
              end
        end
    | _ => stated work equalities

fun close _ _ _ [] = NONE
  | close work (context : orderData.context) (edges, equalities) distinctions =
  let
    val {reach_crossing, ...} =
      reach_from work (#transitive (#axioms context)) distinctions edges
    val lookup = equality_lookup work equalities
    fun one (x, y, distinction) =
      let
        fun contradiction equality =
          (application work;
           MP (NOT_ELIM (path_theorem distinction)) equality)
      in
        if aconv x y then SOME (contradiction (REFL x))
        else
          case lookup (x, y) of
              SOME equality => SOME (contradiction equality)
            | NONE =>
                Option.map contradiction
                  (crossing work context reach_crossing (x, y))
      end
  in
    search work one distinctions
  end

fun refute_graph work context (edges, equalities, distinctions) =
  close work context (edges, equalities) distinctions

(* Proving a literal outright is the other half of the procedure.  A
   refutation reads the negated goal as a literal, and a relational atom
   has a negative reading only under totality, so a chain asked for by a
   goal that carries no totality -- [transitive R] and two steps -- is
   reachable this way and no other. *)
fun prove_literal work context
      (edges, equalities, distinctions) target =
  let
    val {reflexive, transitive, ...} = #axioms (context : orderData.context)
    val {reach_crossing, reach_one} =
      reach_from work transitive [] edges
    fun weak (x, y) =
      if aconv x y then
        Option.map
          (fn r => Proved (MATCH_MP (MATCH_MP order_weak_of_equal r) (REFL x)))
          reflexive
      else reach_one x y
  in
    case target of
        orderData.Weak pair => Option.map path_theorem (weak pair)
      | orderData.Equal pair => crossing work context reach_crossing pair
      | orderData.Strict (x, y) =>
          (* An added equation cannot supply the missing distinction. *)
          if null distinctions andalso Option.isSome (#max_nodes work) then
            NONE
          else
            (case weak (x, y) of
                 NONE => NONE
               | SOME path =>
                   (case refute_equation work context
                           (edges, equalities, distinctions) (x, y) of
                        NONE => NONE
                      | SOME apart =>
                          let val step = path_theorem path
                          in
                            application work;
                            SOME (MATCH_MP
                              (MATCH_MP order_strict_intro step) apart)
                          end))
      | orderData.Distinct pair =>
          refute_equation work context
            (edges, equalities, distinctions) pair
  end

(* [x <> y] is proved by adding the equation and refuting the graph.
   Adding it does not create a distinction, so ordinary calls can skip
   the expansion when there are none. *)
and refute_equation work context
      (edges, equalities, distinctions) (x, y) =
  if null distinctions andalso Option.isSome (#max_nodes work) then NONE
  else
    let
      val equation = mk_eq (x, y)
      val assumed = ASSUME equation
      val facts = [{literal = orderData.Equal (x, y), theorem = assumed}]
      val (extra_edges, extra_equalities, _) =
        expand work context facts
      val closed =
        close work context
          (edges @ extra_edges, extra_equalities @ equalities)
          distinctions
    in
      Option.map (fn refutation => NOT_INTRO (DISCH equation refutation))
        closed
    end

fun prepare (work : work) context theorems =
  let
    val read = orderData.facts_of (#meter work) context
    val supplied = List.concat (List.map read theorems)
    val parts = expand work context supplied
    (* Only metered refutation expands the supplied facts again. *)
    val retained = if Option.isSome (#max_nodes work) then [] else supplied
  in
    {read = read, supplied = retained, parts = parts}
  end

fun count_nodes limit (edges, _, _) =
  let val initial = (0, HOLset.empty Term.compare)
  in
    case limit of
        SOME maximum => bounded_nodes maximum initial edges
      | NONE => SOME initial
  end

(* The goal is proved outright where it can be and refuted otherwise.  A
   goal that is already a negation is discharged rather than doubly
   negated, so [~R x y] is a goal this decides and not an atom it fails
   to read. *)
fun attempt (work : work) context base term =
  let
    val _ = normalization work
    val equation = orderData.reduce context term
    val target = rhs (concl equation)
    val ({read, supplied, parts}, nodes) = base ()
    val (edges, equalities, distinctions) = parts
    fun carry theorem = EQ_MP (SYM equation) theorem
  in
    case nodes of
        NONE => NONE
      | SOME nodes =>
          (case Option.mapPartial (prove_literal work context parts)
                  (orderData.literal_of_term context target) of
               SOME theorem => SOME (carry theorem)
             | NONE =>
                 let
                   val (assumption, restore) =
                     case Lib.total dest_neg target of
                         SOME body =>
                           (body, fn r => NOT_INTRO (DISCH body r))
                       | NONE => (mk_neg target, fn r => CCONTR target r)
                   val negated = read (ASSUME assumption)
                   val refutation_graph =
                     case #max_nodes work of
                         (* Keep the order of charges in the metered path. *)
                         NONE =>
                           SOME (expand work context (negated @ supplied))
                       | SOME maximum =>
                           let
                             val (extra_edges, extra_equalities,
                                  extra_distinctions) =
                               expand work context negated
                             val extended =
                               (extra_edges @ edges,
                                extra_equalities @ equalities,
                                extra_distinctions @ distinctions)
                           in
                             Option.map (fn _ => extended)
                               (bounded_nodes maximum nodes extra_edges)
                           end
                 in
                   Option.map (carry o restore)
                     (Option.mapPartial (refute_graph work context)
                        refutation_graph)
                 end)
  end

fun prove_using_with work contexts theorems term =
  let
    fun one context =
      attempt work context
        (fn () =>
          let val prepared = prepare work context theorems
          in (prepared, count_nodes (#max_nodes work) (#parts prepared)) end)
        term
  in
    search work one contexts
  end

fun require_proof result =
  case result of
      SOME theorem => theorem
    | NONE =>
        raise mk_HOL_ERR "orderSolve" "prove_using"
          "no order in the assumptions decides the goal"

fun prove_using contexts theorems term =
  require_proof (prove_using_with (capped_work ()) contexts theorems term)

fun prepare_using contexts theorems =
  let
    (* Each relation has its own fact reader and graph. The target and
       any facts it adds are specific to the query. *)
    fun cache context =
      let
        val prepared = Portable.HOLSusp.delay
          (fn () => prepare (capped_work ()) context theorems)
        fun count limit =
          count_nodes limit (#parts (Portable.HOLSusp.force prepared))
        val nodes = memoUtil.keyed_memo (fn a => fn b => a = b) count
        fun base limit = (Portable.HOLSusp.force prepared, nodes limit)
      in
        (context, base)
      end
    val cached = List.map cache contexts
  in
    fn term =>
      let
        val work = capped_work ()
        fun one (context, base) =
          attempt work context (fn () => base (#max_nodes work)) term
      in
        require_proof (search work one cached)
      end
  end

fun prove_with theorems term =
  prove_using (orderData.contexts_unmetered theorems)
    theorems term

datatype budget_outcome =
    OrderProved of thm
  | OrderExhausted
  | OrderLimitReached of
      {kind : searchBudget.kind, usage : searchBudget.usage}

fun prove_using_budgeted budget =
  prove_using_with (budget_work budget)

fun prove_with_budget budget theorems term =
  (case prove_using_budgeted budget
          (orderData.contexts (searchBudget.charger budget) theorems)
          theorems term of
       SOME theorem => OrderProved theorem
     | NONE => OrderExhausted)
  handle searchBudget.LimitReached (kind, usage) =>
    OrderLimitReached {kind = kind, usage = usage}

end
