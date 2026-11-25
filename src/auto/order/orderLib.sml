structure orderLib :> orderLib =
struct

open HolKernel boolLib

val ERR = mk_HOL_ERR "orderLib"

(* An order axiom or edge may carry schematic type parameters even when
   the initial goal uses a concrete relation.  Match the theorem-backed
   invocation view at each relation head actually present in the goal.
   The matcher keeps support and genuinely fixed parameters rigid. *)
fun relation_of (_, term) =
  if is_comb term then
    let val left = rator term
    in if is_comb left then SOME (rator left) else NONE
    end
  else NONE

fun relation_sites terms =
  let
    val candidates = List.concat (map (gen_find_terms relation_of) terms)
  in
    listUtil.distinct_by Term.compare I candidates
  end

(* Hypotheses are listed sorted and without repeats, so the key compares
   them as sets. *)
fun distinct_theorems theorems =
  listUtil.distinct_by
    (Lib.pair_compare (Term.compare, Lib.list_compare Term.compare))
    (fn theorem => (Thm.concl theorem, Thm.hyp theorem)) theorems

(* Antisymmetry can close an equality whose conclusion contains no
   relation application. Concrete edges in the context then supply
   the carrier. *)
fun concrete_relation_sites theorems =
  List.filter (null o type_vars_in_term)
    (relation_sites (map Thm.concl theorems))

fun constant_spine term =
  let
    fun peel arity term =
      if is_comb term then peel (arity + 1) (rator term)
      else if is_const term then
        SOME (#Name (dest_thy_constid term), arity)
      else NONE
  in
    peel 0 term
  end

fun select_relation_sites sites =
  let
    fun exceeds 0 rest = not (null rest)
      | exceeds _ [] = false
      | exceeds n (_ :: rest) = exceeds (n - 1) rest
  in
    if exceeds 8 sites then
      let
        val compare = Lib.pair_compare (KernelSig.id_compare, Int.compare)
        fun add (site, index) =
          case constant_spine site of
              NONE => index
            | SOME key =>
                Redblackmap.update
                  (index, key, fn bucket => site :: Option.getOpt (bucket, []))
        val index = Portable.HOLSusp.delay
          (fn () => List.foldr add (Redblackmap.mkDict compare) sites)
      in
        (* A first-order match must preserve a constant head and its
           arity. Heads that can be instantiated keep the full scan. *)
        fn pattern =>
          case constant_spine pattern of
              NONE => sites
            | SOME key =>
                Option.getOpt
                  (Redblackmap.peek (Portable.HOLSusp.force index, key), [])
      end
    else fn _ => sites
  end

fun order_fact_views_with _ _ _ [] = []
  | order_fact_views_with budget get_sites goal theorems =
  let
    val charge =
      case budget of
          NONE => (fn _ => ())
        | SOME owned => searchBudget.charge owned
    val environment =
      clasetFacts.create_with_charge charge goal theorems
    (* A merged list may mention the same relation on both sides.
       Matching an alpha-equivalent pair produces an equivalent view;
       keep the first, as the final theorem deduplication would. *)
    val distinct_sites =
      case budget of
          NONE => listUtil.distinct_by Term.compare I
        | SOME _ => I
    val sites =
      case get_sites () of
          ([], concrete) => concrete
        | (goal_sites, []) => goal_sites
        | (goal_sites, concrete) => distinct_sites (goal_sites @ concrete)
    val sites_for =
      case budget of
          NONE => select_relation_sites sites
        | SOME _ => (fn _ => sites)
    fun views entry =
      let
        val schematic = #theorem (clasetFacts.schematic_view entry)
        val contexts =
          orderData.contexts_unmetered [schematic]
        val heads = relation_sites [Thm.concl schematic]
        val patterns =
          case contexts of
              [] => heads
            | _ => distinct_sites (heads @ map #relation contexts)
        val instances =
          List.concat
            (map
              (fn pattern =>
                List.mapPartial
                  (fn site =>
                    (charge searchBudget.Candidate;
                     Option.map #theorem
                       (clasetFacts.match_view entry pattern site)))
                  (sites_for pattern))
              patterns)
      in
        clasetFacts.source entry :: instances
      end
  in
    distinct_theorems
      (List.concat (map views (clasetFacts.facts environment)))
  end

fun order_fact_views (goal as (asl, w)) theorems =
  order_fact_views_with NONE
    (fn () => (relation_sites (w :: asl), concrete_relation_sites theorems))
    goal theorems

(* The goal's own assumptions are the context: an order arrives as a
   premise, so a tactic that ignored them would decide nothing.  The
   prefix is stripped first, which is what puts the axioms of a goal
   stated as [!R. transitive R ==> ...] into the assumptions. *)
fun solve theorems (goal as (asl, w)) _ =
  let
    val facts = List.map ASSUME asl @ order_fact_views goal theorems
  in
    ([], fn _ => orderSolve.prove_with facts w)
  end

fun ORDER_TAC theorems =
  REPEAT GEN_TAC THEN
  REPEAT (DISCH_THEN STRIP_ASSUME_TAC) THEN
  solve theorems

fun ORDER_PROVE tm =
  let
    val (goals, validation) =
      Tactical.VALID (ORDER_TAC []) ([], tm) (Context.snapshot())
  in
    if null goals then validation []
    else raise ERR "ORDER_PROVE" "unsolved goals"
  end

fun ORDER_CONV tm = EQT_INTRO (ORDER_PROVE tm)

(* Ground contexts are derived once per addition to the simplifier's
   context.  A citation with schematic types gets an extra view only
   when the current atom has a matching relation head.  That view is
   cached under the whole atom and discarded when the context changes;
   an assumed theorem cannot escape its fixed support types. *)
fun make_order_reducer budget =
  let
    val contexts_of =
      case budget of
          NONE => orderData.contexts_unmetered
        | SOME owned => orderData.contexts (searchBudget.charger owned)
    fun prove_once contexts theorems tm =
      case budget of
          NONE => orderSolve.prove_using contexts theorems tm
        | SOME owned =>
            (case orderSolve.prove_using_budgeted
                    owned contexts theorems tm of
                 SOME theorem => theorem
               | NONE => raise ERR "ORDER_DP" "no order proof")
    (* Each simplifier context can answer several direct atom queries.
       Prepare lazily since many contexts never reach an order atom. *)
    fun prover contexts theorems =
      case budget of
          NONE =>
            let
              val prepared = Portable.HOLSusp.delay
                (fn () => orderSolve.prepare_using contexts theorems)
            in
              fn tm => Portable.HOLSusp.force prepared tm
            end
        | SOME _ => prove_once contexts theorems
    exception CTXT of
      {theorems : thm list,
       contexts : orderData.context list,
       prove : term -> thm,
       concrete_sites : term list Portable.HOLSusp.susp,
       sites :
         (term * (thm list * orderData.context list)) list ref}
    fun get_context e = (raise e) handle CTXT value => value
    fun addcontext (context, newtheorems) =
      let
        val {theorems, contexts, ...} = get_context context
        val added = List.concat (List.map CONJUNCTS newtheorems)
        val theorems = added @ theorems
        val contexts =
          if orderData.has_order_axiom added then
            contexts_of theorems
          else contexts
      in
        (* A context is derived from order axioms alone, so the
           derivation is repeated only when one arrives.  The
           simplifier adds to its context at every assumption it
           passes, and rewriting each of those with the order
           definitions to find nothing is the cost this avoids. *)
        CTXT {theorems = theorems, contexts = contexts,
              prove = prover contexts theorems,
              concrete_sites =
                Portable.HOLSusp.delay (fn () =>
                  concrete_relation_sites theorems),
              sites = ref []}
      end
    fun apply args tm =
      let
        val {theorems, contexts, prove, concrete_sites, sites} =
          get_context (#context args)
        fun concrete () = Portable.HOLSusp.force concrete_sites
        fun not_literal () =
          raise ERR "ORDER_DP" "not a literal of an order in the context"
        fun equality_domain term =
          case Lib.total dest_eq term of
              SOME (left, _) => SOME (type_of left)
            | NONE =>
                (case Lib.total dest_neg term of
                     SOME body => equality_domain body
                   | NONE => NONE)
        fun context_site_for_equality () =
          (* Only an equality of the order's carrier may borrow a site
             from a concrete context edge.  Matching the theorem view
             still enforces its fixed parameters and support. *)
          case equality_domain tm of
              NONE => []
            | SOME domain =>
                if List.exists
                     (fn context =>
                       let
                         val (pattern, _) =
                           Type.dom_rng
                             (type_of (#relation context))
                       in
                         Lib.can (Type.match_type pattern) domain
                       end)
                     contexts
                then concrete ()
                else []
        fun matching_site site =
          List.exists
            (fn context =>
              Lib.can (Term.match_term (#relation context)) site)
            contexts
        fun at_atom atom_sites =
          case List.find (fn (key, _) => aconv key tm) (!sites) of
              SOME (_, result) => result
            | NONE =>
                let
                  val views =
                    order_fact_views_with budget
                      (fn () => (atom_sites, concrete ())) ([], tm) theorems
                  val result = (views, contexts_of views)
                  val previous = !sites
                in
                  sites :=
                    (tm, result) ::
                    List.take (previous, Int.min (length previous, 127));
                  result
                end
      in
        if null contexts then not_literal ()
        else if List.exists (fn c => orderData.is_literal c tm) contexts then
          EQT_INTRO (prove tm)
        else
          let val atom_sites = relation_sites [tm]
          in
            if List.exists matching_site atom_sites orelse
               List.exists matching_site (context_site_for_equality ())
            then
              let val (views, derived) = at_atom atom_sites
              in
                if List.exists (fn c => orderData.is_literal c tm) derived
                then EQT_INTRO (prove_once derived views tm)
                else not_literal ()
              end
            else not_literal ()
          end
      end
  in
    Traverse.REDUCER
      {name = SOME "ORDER_DP",
       addcontext = addcontext,
       apply = apply,
       initial =
         CTXT {theorems = [], contexts = [], prove = prover [] [],
               concrete_sites = Portable.HOLSusp.delay (fn () => []),
               sites = ref []}}
  end

fun order_ss reducer =
  simpLib.named_merge_ss "ORDER"
    [simpLib.SSFRAG
       {name = SOME "ORDER_DP",
        convs = [], rewrs = [], congs = [], filter = NONE,
        ac = [], dprocs = [reducer]}]

(* Both boundaries use the same ordinary collector and apply closure. *)
fun order_ext_ss reducer =
  simpLib.named_merge_ss "ORDER"
    [simpLib.SSFRAG
       {name = SOME "ORDER_DP",
        convs = [], rewrs = [], congs = [], filter = NONE,
        ac = [], dprocs = [reducer]}]

val order_reducer = make_order_reducer NONE
val ORDER_ss = order_ss order_reducer
val ORDER_ext_ss = order_ext_ss order_reducer

fun ORDER_ss_budgeted budget =
  order_ss (make_order_reducer (SOME budget))

fun ORDER_ext_ss_budgeted budget =
  order_ext_ss (make_order_reducer (SOME budget))

end
