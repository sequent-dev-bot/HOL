open HolKernel testutils autoSeedTheory simpLib

(* Ordinary collections and their tests below stay ordinary.  Callers of
   extension-facing clasimp APIs use the lifted default. *)
fun lifted_default () = (BasicProvers.srw_ss ())

val _ = intLinarith.instance
val _ = Theory.new_theory "seedCollectionSelftest"

fun check (name, predicate) =
  (tprint name;
   if predicate () then OK () else die "failed")

val seed_bottom_up_rule = new_definition
  ("seed_decl_g_def", ``seed_decl_g (p:bool) = p``)

val _ =
  check
    ("bottom-up declarations and retractions rewind with the context",
     fn () =>
       let
         val saved = Context.snapshot ()
         fun run () =
           let
             val name = "seed_bottom_up_context"
             val _ = boolLib.save_thm
               (name ^ "[simp_bottom_up]", seed_bottom_up_rule)
             val declared = Context.snapshot ()
             fun reduces () = aconv
               (boolSyntax.rhs (concl
                 (Conv.QCONV (simpLib.SIMP_CONV (lifted_default ()) [])
                    ``seed_decl_g p``))) ``p:bool``
             val added = reduces ()
             val _ = clasimpLib.remove_simp_bottom_up name
             val removed = not (reduces ())
             val _ = Context.restore declared
             val restored = reduces ()
           in added andalso removed andalso restored andalso reduces () end
       in Portable.finally (fn () => Context.restore saved) run () end)

val _ =
  check
    ("Phase-8 named seed collections are registered",
     fn () =>
       List.all
         (fn name =>
           List.exists (equal name) (ThmSetData.all_set_types ()) andalso
           ThmAttribute.is_attribute name)
         ["algebra_simps", "field_simps"])

val _ =
  check
    ("seed collections expose usable stateful fragments",
     fn () =>
       not (null (seedCollections.algebra_rewrites ())) andalso
       (ignore (seedCollections.algebra_ss ()); true) andalso
       (ignore (seedCollections.field_ss ()); true))

val audit_spec =
  {kind = clasetRules.Intro, safe = true, prio = NONE}

val audit_good_cs =
  clasetLib.add_rule audit_spec
    ("audit_good", boolTheory.AND_INTRO_THM) clasetLib.empty_cs

val audit_bad_cs =
  clasetLib.add_rule audit_spec
    ("audit_bad", boolTheory.OR_INTRO_THM1) clasetLib.empty_cs

val audit_waiver =
  {rule = "audit_bad", reason = "selftest exercises waiver plumbing",
   date = "2026-08-10"}

fun failed_result (seedAudit.Failed _) = true
  | failed_result _ = false

fun waived_result (seedAudit.Waived _) = true
  | waived_result _ = false

val _ =
  check
    ("seed audit proves an invertible safe introduction rule",
     fn () =>
       let
         val report =
           seedAudit.audit_with
             {claset = audit_good_cs,
              budget = Time.fromSeconds 5, waivers = []}
       in
         #checked report = #proved report andalso
         List.exists
           (fn seedAudit.Proved {rule, ...} => rule = "audit_good"
             | _ => false)
           (#results report)
       end)

val _ =
  check
    ("seed audit reports an unwaivered non-invertible safe rule",
     fn () =>
       let
         val report =
           seedAudit.inspect
             {claset = audit_bad_cs,
              budget = Time.fromSeconds 1, waivers = []}
       in
         List.exists failed_result (#results report)
       end)

val slow_variables =
  List.tabulate
    (24, fn i =>
       Term.mk_var ("audit_slow_" ^ Int.toString i, Type.bool))
val slow_premise = hd slow_variables
val slow_conclusion =
  List.foldl
    (fn (alternative, conclusion) =>
      boolSyntax.mk_disj (conclusion, alternative))
    slow_premise (tl slow_variables)
val slow_theorem =
  DISCH slow_premise
    (List.foldl
       (fn (alternative, theorem) => DISJ1 theorem alternative)
       (ASSUME slow_premise) (tl slow_variables))
val slow_audit_cs =
  clasetLib.add_rule audit_spec
    ("audit_budget", slow_theorem) clasetLib.empty_cs

val _ =
  check
    ("seed audit interrupts a prover at the obligation budget",
     fn () =>
       let
         val timer = Timer.startRealTimer ()
         val report =
           seedAudit.inspect
             {claset = slow_audit_cs,
              budget = Time.fromReal 0.01, waivers = []}
         val elapsed = Timer.checkRealTimer timer
       in
         List.exists failed_result (#results report) andalso
         Time.< (elapsed, Time.fromReal 0.5)
       end)

val _ =
  check
    ("seed audit consumes a dated waiver",
     fn () =>
       let
         val report =
           seedAudit.audit_with
             {claset = audit_bad_cs,
              budget = Time.fromSeconds 1, waivers = [audit_waiver]}
       in
         length (#waivers report) = 1 andalso
         List.exists waived_result (#results report)
       end)

val _ =
  check
    ("seed audit rejects stale waivers in the passing direction",
     fn () =>
       let
         val stale =
           {rule = "audit_good", reason = "must be stale",
            date = "2026-08-10"}
         val report =
           seedAudit.inspect
             {claset = audit_good_cs,
              budget = Time.fromSeconds 5, waivers = [stale]}
       in
         List.exists failed_result (#results report)
       end)

val _ =
  check
    ("assembled Phase-8 seed and TypeBase safe corpus passes the audit",
     fn () =>
       let
         val report = seedAudit.audit {waivers = []}
       in
         #checked report = #proved report andalso null (#waivers report)
       end)

val expected_seeds =
  ["clasetSeed", "pairAutoSeed", "sumAutoSeed", "optionAutoSeed",
   "listAutoSeed", "pred_setAutoSeed", "arithmeticAutoSeed",
   "finite_mapAutoSeed", "integerAutoSeed", "realAutoSeed",
   "stringAutoSeed", "rich_listAutoSeed", "sortingAutoSeed"]

val _ =
  check
    ("autoSeed umbrella contains every per-theory seed",
     fn () =>
       let val ancestry = Theory.ancestry "autoSeed"
       in List.all (fn name => List.exists (equal name) ancestry)
            expected_seeds
       end)

fun starts_with prefix text =
  size text >= size prefix andalso
  String.substring (text, 0, size prefix) = prefix

fun is_seed name =
  String.isSubstring "AutoSeed$" name orelse
  starts_with "clasetSeed$" name

fun is_typebase name = starts_with "__claset_tyinfo_" name

fun same_decl
      ({spec = left_spec, thm = left_thm, ...} : clasetLib.aesop_rule)
      ({spec = right_spec, thm = right_thm, ...} : clasetLib.aesop_rule) =
  #kind left_spec = #kind right_spec andalso
  #safe left_spec = #safe right_spec andalso
  aconv (concl left_thm) (concl right_thm)

val _ =
  check
    ("seed declarations do not duplicate TypeBase contributions",
     fn () =>
       let
         val rules = clasetLib.all_rules (clasetLib.the_claset ())
         val seeds = List.filter (is_seed o #name) rules
         val typebase = List.filter (is_typebase o #name) rules
       in
         not
           (List.exists
             (fn seed => List.exists (same_decl seed) typebase)
             seeds)
       end)

fun rule_names () =
  map #name (clasetLib.all_rules (clasetLib.the_claset ()))

val _ =
  check
    ("loading the autoSeed umbrella twice is delta-idempotent",
     fn () =>
       let
         val rules_before = rule_names ()
         val algebra_before = length (seedCollections.algebra_rewrites ())
         val field_before = length (seedCollections.field_rewrites ())
         val split_before = length (splitLib.split_thms ())
         val _ = Theory.load_complete "autoSeed"
         val _ = Theory.load_complete "autoSeed"
       in
         rules_before = rule_names () andalso
         algebra_before = length (seedCollections.algebra_rewrites ()) andalso
         field_before = length (seedCollections.field_rewrites ()) andalso
         split_before = length (splitLib.split_thms ())
       end)

fun solved tactic goal =
  case Tactical.VALID tactic ([], goal) (Context.snapshot()) of
      ([], validation) => (ignore (validation []); true)
    | _ => false

val _ =
  check
    ("representative pair/list/set/map/string seed views are usable",
     fn () =>
       List.all
         (solved (clasimpLib.AUTO_TAC []))
         [``UNCURRY c p <=> !x y. p = (x,y) ==> c x y``,
          ``LIST_REL R [] ys <=> ys = []``,
          ``start <= finish ==>
            GENLIST (\offset. start + offset) (SUC finish - start) =
            GENLIST (\offset. start + offset) (finish - start) ++ [finish]``,
          ``x IN (s UNION t) <=> x IN s \/ x IN t``,
          ``INJ (\x : 'a. x) s UNIV``,
          ``FLOOKUP (FUNION n m) k = NONE <=>
            FLOOKUP n k = NONE /\ FLOOKUP m k = NONE``,
          ``ALL_DISTINCT (MAP FST association) ==>
            MEM (key, value) association ==>
            ALOOKUP association key = SOME value``,
          ``ALL_DISTINCT (MAP FST association) ==>
            (ALOOKUP association key = SOME value <=>
             MEM (key, value) association)``,
          ``STRLEN text = 0 <=> text = ""``])

val _ =
  check
    ("representative arithmetic and sorting seed views are usable",
     fn () =>
       solved (linarithLib.LINARITH_TAC [])
         ``(x : int) < y ==> x - y < 0`` andalso
       solved (clasimpLib.AUTO_TAC [])
         ``PERM ([] : 'a list) xs <=> xs = []``)

val seed_inj_marker_def =
  new_definition
    ("seed_inj_marker_def",
     ``seed_inj_marker (f:'a -> 'b) s t <=> INJ f s t``)
val seed_inj_client_rule =
  Tactical.prove
    (``!f s t. INJ (f:'a -> 'b) s t ==>
               seed_inj_marker f s t``,
     Rewrite.REWRITE_TAC [seed_inj_marker_def])

val _ =
  check
    ("an INJ client marker needs its supplied rule",
     fn () =>
       not (solved (clasimpLib.AUTO_TAC [])
              ``INJ (f:'a -> 'b) s t ==>
                seed_inj_marker f s t``))

val _ =
  check
    ("an INJ client rule survives the seed's definition normal form",
     fn () =>
       null
         (#1
           (Tactical.VALID
             (clasimpLib.AUTO_TAC
                [clasetLib.Dest seed_inj_client_rule])
             ([``INJ (f:'a -> 'b) s t``],
              ``seed_inj_marker f s t``)
             (Context.snapshot ()))))

(* src/HOL/Product_Type.thy:520,524 @ f7e02b7e.  Isabelle decides
   [split_paired_All] and [split_paired_Ex] ambiently: a quantifier over
   a pair is the pair of quantifiers over its components.  Neither goal
   below is a corpus entry and neither is the rule itself; each states a
   consequence about the components, and without the seed both are left
   with the pair quantifier unopened. *)
val _ =
  check
    ("the pair-quantifier seed views are usable",
     fn () =>
       List.all
         (solved (clasimpLib.AUTO_TAC []))
         [``!Q. (!p : 'a # 'b. Q (FST p) (SND p)) <=> (!x y. Q x y)``,
          ``!Q. (?p : 'a # 'b. Q (FST p) (SND p)) <=> (?x y. Q x y)``])

(* src/HOL/Product_Type.thy:600,607 @ f7e02b7e.  Isabelle decides
   [case_prodI2'] and [case_prodE'] ambiently: a paired abstraction
   applied to further arguments is still read at the components of the
   pair.  Neither goal below is a corpus entry and neither is the rule
   itself -- one carries a conjunct across the application and the other
   reads a nested application at the swapped components -- and the pair
   is left free in both, as the corpus leaves what Isabelle binds with a
   meta-quantifier.  That is what the seed is for: a bound pair is taken
   apart by [FORALL_PROD_AUTO] and needs none of this. *)
val _ =
  check
    ("the applied paired-abstraction seed view is usable",
     fn () =>
       List.all
         (solved (clasimpLib.AUTO_TAC []))
         [``(\(a,b). \n. qa a /\ qb b /\ qn n) p k ==>
            (\(a,b). \n. qn n /\ qb b) p k``,
          ``(\(a,b). \n. (\(c,d). \m. qq c d m) (b,a) n) p k ==>
            (\(a,b). \n. qq b a n) p k``])

(* src/HOL/List.thy:3231 @ f7e02b7e.  Isabelle decides [fold_append]
   ambiently: a fold across an append is the two folds in sequence.
   Neither goal below is a corpus entry, and neither is [fold_append]
   itself -- one folds across two appends and the other across a snoc
   -- and excluding the seed leaves both with the fold unsplit. *)
val _ =
  check
    ("the fold-across-append seed view is usable",
     fn () =>
       List.all
         (solved (clasimpLib.AUTO_TAC []))
         [``!f a xs ys zs.
              FOLDL f a (xs ++ ys ++ zs) =
              FOLDL f (FOLDL f (FOLDL f a xs) ys) zs``,
          ``!f a xs item.
              FOLDL f a (xs ++ [item]) = f (FOLDL f a xs) item``])

(* src/HOL/List.thy:1956 @ f7e02b7e.  Isabelle decides [nth_mem]
   ambiently: an index below the length makes the element a member.
   None of the goals below is a corpus entry, and none of them is
   [nth_mem] itself -- each carries the membership on into an append, a
   reverse, a cons or a subset -- and excluding the seed leaves every
   one of them with the residual [MEM (EL index xs) xs]. *)
val _ =
  check
    ("the indexed-membership seed view is usable",
     fn () =>
       List.all
         (solved (clasimpLib.AUTO_TAC []))
         [``!xs ys index.
              index < LENGTH xs ==> MEM (EL index xs) (xs ++ ys)``,
          ``!xs index.
              index < LENGTH xs ==> MEM (EL index xs) (REVERSE xs)``,
          ``!xs item index.
              index < LENGTH xs ==> MEM (EL index xs) (item::xs)``,
          ``!s xs index.
              index < LENGTH xs ==> set xs SUBSET s ==> EL index xs IN s``])

(* src/HOL/List.thy:1381,1222-1228,2826-2827,6208 @ f7e02b7e.  Isabelle
   decides these ambiently: set_upt turns an interval list into the
   interval set, map_fst_zip, map_snd_zip and nth_zip project a zip whose
   sides have equal length, and sorted_upt sorts an interval.  None of
   the goals below is a corpus entry; each is a consequence reached by a
   seed and then arithmetic, and excluding the five seeds leaves every
   one of them with a residual.  The last is the third eta-expanded,
   which meets its rule only because the simpset matches modulo eta. *)
val _ =
  check
    ("interval and zip seed views are usable",
     fn () =>
       List.all
         (solved (clasimpLib.AUTO_TAC []))
         [``!n item. MEM item (GENLIST (\offset. offset) (SUC n)) <=>
                     item <= n``,
          ``!lower upper item.
              lower <= item /\ item < upper ==>
              MEM item (GENLIST ($+ lower) (upper - lower))``,
          ``!start xs item.
              MEM item xs ==>
              MEM item (MAP SND (ZIP (GENLIST ($+ start) (LENGTH xs),
                                      xs)))``,
          ``!start xs index.
              index < LENGTH xs ==>
              MEM (FST (EL index (ZIP (GENLIST ($+ start) (LENGTH xs),
                                       xs))))
                  (GENLIST ($+ start) (LENGTH xs))``,
          ``!start count.
              SORTED $<= (GENLIST ($+ start) count ++ [start + count])``,
          ``!start xs item.
              MEM item xs ==>
              MEM item
                (MAP SND (ZIP (GENLIST (\offset. start + offset)
                                 (LENGTH xs),
                               xs)))``])

val _ =
  check
    ("universal image membership simplifies through an implication",
     fn () =>
       solved
         (simpLib.FULL_SIMP_TAC (clasimpLib.clasimp_ss ()) [])
         ``(!y. y IN IMAGE (f : 'a -> 'b) source ==> property y) ==>
           !x. x IN source ==> property (f x)``)

val _ =
  check
    ("collection local add/remove round-trips update both fragments",
     fn () =>
       let
         val theory = Theory.current_theory ()
         fun roundtrip attribute rewrites remove suffix theorem =
           let
             val prior_count = length (rewrites ())
             val _ =
               ThmAttribute.local_attribute
                 {name = suffix, attrname = attribute, args = [],
                  thm = theorem}
             val added = length (rewrites ()) = prior_count + 1
             val _ = remove (theory ^ "." ^ suffix)
           in
             added andalso length (rewrites ()) = prior_count
           end
       in
         roundtrip "algebra_simps" seedCollections.algebra_rewrites
           seedCollections.remove_algebra_simps
           "ALGEBRA_COLLECTION_ROUNDTRIP" boolTheory.AND_CLAUSES andalso
         roundtrip "field_simps" seedCollections.field_rewrites
           seedCollections.remove_field_simps
           "FIELD_COLLECTION_ROUNDTRIP" boolTheory.OR_CLAUSES
       end)

val _ =
  check
    ("Excl suppresses a named field collection member",
     fn () =>
       let
         val redex = ``inv (x : real)``
         val fragment = simpLib.empty_ss ++ seedCollections.field_ss ()
         fun result controls =
           boolSyntax.rhs
             (concl (Conv.QCONV (SIMP_CONV fragment controls) redex))
         val normal = result []
         val excluded =
           result
             [markerLib.Excl
                "realAutoSeed.REAL_INV_1OVER_FIELD"]
       in
         if not (aconv normal ``1 / (x : real)``) then
           raise Fail
             ("unexpected field rewrite: " ^ Parse.term_to_string normal)
         else if not (aconv excluded redex) then
           raise Fail
             ("Excl left rewrite active: " ^
              Parse.term_to_string excluded)
         else true
       end)

val _ =
  check
    ("collection removal updates both stateful fragments",
     fn () =>
       let
         val algebra_before = length (seedCollections.algebra_rewrites ())
         val field_before = length (seedCollections.field_rewrites ())
         val _ = seedCollections.remove_algebra_simps
           "arithmeticAutoSeed.ADD_ASSOC_ALGEBRA"
         val _ = seedCollections.remove_field_simps
           "realAutoSeed.REAL_INV_1OVER_FIELD"
         val algebra_after = length (seedCollections.algebra_rewrites ())
         val field_after = length (seedCollections.field_rewrites ())
       in
         algebra_after + 1 = algebra_before andalso
         field_after + 1 = field_before andalso
         (ignore (seedCollections.algebra_ss ()); true) andalso
         (ignore (seedCollections.field_ss ()); true)
       end)

(* A set written as an abstraction is a membership only after beta.  This
   is the shape a set-of-keys obligation has when the set former was
   unfolded before the goal reached the engine; the names are this file's
   own.  The bound is here because the failure this pins is a search that
   does not come back, not one that reports no proof. *)
val abstraction_subset_goal : Abbrev.goal =
  ([],
   ``(!seed_dom_key seed_dom_value.
        seed_dom_left seed_dom_key = SOME seed_dom_value ==>
        seed_dom_right seed_dom_key = SOME seed_dom_value) ==>
     (\seed_dom_key. seed_dom_left seed_dom_key <> NONE) SUBSET
     (\seed_dom_key. seed_dom_right seed_dom_key <> NONE)``)

(* A tactic that reports no proof has come back, which is what the bound is
   about; only the timeout distinguishes the two outcomes below. *)
fun within seconds interpret tactic goal =
  interpret
    (Timeout.apply (Time.fromSeconds seconds)
      (fn () =>
        SOME (Tactical.VALID tactic goal (Context.snapshot()))
          handle HOL_ERR _ => NONE) ())
  handle Timeout.TIMEOUT _ => false

fun closes_within seconds =
  within seconds
    (fn SOME (remaining, _) => List.null remaining | NONE => false)

fun terminates_within seconds = within seconds (fn _ => true)

val _ =
  check
    ("FASTFORCE closes a subset between two abstractions",
     fn () =>
       closes_within 20 (clasimpLib.FASTFORCE_TAC []) abstraction_subset_goal)

(* The state the search above reaches once it has a witness: a negated
   equation to prove against a stored implication and a contradicting
   value.  A depth-first search used not to come back from here at all --
   the unsafe simp wrapper rebuilt the negation that the classical [~]
   introduction had just taken apart, and the two alternated for ever.
   Whether FAST search closes it is a question of strength and is left a
   pass either way; that it terminates and reports what it found is not. *)
val negated_equation_goal : Abbrev.goal =
  ([``!seed_neg_key seed_neg_value.
        seed_neg_left seed_neg_key = SOME seed_neg_value ==>
        seed_neg_right seed_neg_key = SOME seed_neg_value``,
    ``seed_neg_right seed_neg_x = NONE``],
   ``seed_neg_left seed_neg_x <> SOME seed_neg_y``)

val _ =
  check
    ("FASTFORCE terminates on a negated equation with a stored implication",
     fn () =>
       terminates_within 20 (clasimpLib.FASTFORCE_TAC [])
         negated_equation_goal)

(* src/HOL/Set.thy:566-569 @ f7e02b7e.  Neither goal is a corpus entry.
   The tableau leg has no simpset, so a membership in the empty set is
   just another literal there; without the safe elimination derived from
   NOT_IN_EMPTY_AUTO the branch carrying it stays open and neither goal
   closes. *)
val _ =
  check
    ("a membership in the empty set closes a tableau branch",
     fn () =>
       List.all
         (closes_within 20 (tableauLib.BLAST_TAC []))
         [([], ``(seed_emptyE_s : 'a set) SUBSET {} ==>
                 seed_emptyE_s SUBSET seed_emptyE_t``),
          ([], ``(!item. item IN (seed_emptyE_s : 'a set) ==> item IN {}) ==>
                 seed_emptyE_s = {}``)])

(* src/HOL/Set.thy:1192-1195 @ f7e02b7e.  Neither goal is a corpus
   entry.  An emptiness claim reached by unfolding arrives as an equation
   between set formers, and SET_EQ_EMPTY_AUTO is what turns it into
   membership form; withheld, neither goal closes. *)
val _ =
  check
    ("an emptiness claim between set formers is first-order",
     fn () =>
       List.all
         (closes_within 20 (clasimpLib.AUTO_TAC []))
         [([], ``{item | seed_empty_p item} = {} ==>
                 {item | seed_empty_p item /\ seed_empty_q item} = {}``),
          ([], ``{item | seed_empty_p item /\ seed_empty_q item} = {} ==>
                 (!item. seed_empty_r item ==> seed_empty_p item) ==>
                 {item | seed_empty_r item /\ seed_empty_q item} = {}``)])

(* src/HOL/Set.thy:551 @ f7e02b7e.  Neither goal is a corpus entry.  The
   claset's set equality was introduction-only, so a search that had to
   read an equality out of the hypotheses reported no proof without
   engaging at all; withholding SET_EQUALITY_CASES_AUTO leaves both of
   these unproved. *)
val _ =
  check
    ("a set equality among the hypotheses is usable by the search",
     fn () =>
       List.all
         (closes_within 20 (tableauLib.BLAST_TAC []))
         [([], ``(left : 'a set) UNION right = {} ==> left = {}``),
          ([], ``(left : 'a set) INTER right = left ==> left SUBSET right``)])

(* src/HOL/Set.thy:598-601 @ f7e02b7e.  Neither goal is a corpus entry.
   Isabelle states UNIV_I as [simp] and declares the classical half on a
   line of its own as an unsafe [intro] -- "unsafe makes it less likely
   to cause problems".  Safe, it fires on any [item IN unknown] and
   settles the unknown on the universe before the branch's other goals
   are looked at, which is search the safe layer is not entitled to do;
   so the membership survives SAFE_TAC and the search still closes it. *)
val seed_univ_goal : Abbrev.goal =
  ([], ``(seed_univ_item : 'a) IN univ(:'a)``)

val _ =
  check
    ("the universe membership is a search step and not a safe one",
     fn () =>
       not (closes_within 20 (classicalLib.SAFE_TAC []) seed_univ_goal)
       andalso closes_within 20 (tableauLib.BLAST_TAC []) seed_univ_goal)

(* src/HOL/Orderings.thy:620-658 @ f7e02b7e.  Isabelle's order solver
   takes the axioms off the linorder class; the translation states them
   as a premise about the relation instead, and a conditional rewrite
   whose side condition is [transitive R] is then offered a condition it
   cannot discharge from the premise sitting beside it.  What the seed
   reaches is the simplifier's own condition solver, which has the simp
   rules and no classical search, so the check goes through SIMP_CONV: a
   check through AUTO_TAC says nothing, the search proving the
   decomposition outright with the seed withheld.  Neither the rule nor
   the goal is a corpus entry, and the rule is assumed rather than
   proved because its content is irrelevant -- only its side condition
   is under test. *)
val order_side_condition_rule =
  Thm.ASSUME
    ``!R : 'a -> 'a -> bool.
        relation$transitive R ==> (order_seed_p R <=> order_seed_q R)``

val order_side_condition_goal =
  ``!R : 'a -> 'a -> bool.
      relation$WeakLinearOrder R ==> (order_seed_p R <=> order_seed_q R)``

val _ =
  check
    ("an order premise discharges an order side condition",
     fn () =>
       let
         val rewritten =
           simpLib.SIMP_CONV (clasimpLib.clasimp_ss ())
             [order_side_condition_rule] order_side_condition_goal
       in
         Term.aconv (boolSyntax.rhs (Thm.concl rewritten)) boolSyntax.T
       end
       handle Conv.UNCHANGED => false)

(* src/HOL/Orderings.thy:620-658 @ f7e02b7e.  The check above is the
   rewrite route, where the simplifier's own condition solver discharges
   a side condition.  This is the other route the components' [dest]
   declaration is for: a rule the search applies asks for the component
   as a premise of its own, and a premise is not a subterm of the goal,
   so no rewrite of the assumptions reaches it.  With the components
   declared to the simpset alone the goal below stays open.  Neither the
   rule nor the goal is a corpus entry, and as above the rule's content
   is irrelevant -- only its order premise is under test -- so the two
   predicates it is stated over are defined here and declared nowhere. *)
val order_seed_carried_def =
  Definition.new_definition
    ("order_seed_carried_def",
     ``order_seed_carried (R : 'a -> 'a -> bool) (x : 'a) = T``)

val order_seed_targeted_def =
  Definition.new_definition
    ("order_seed_targeted_def",
     ``order_seed_targeted (R : 'a -> 'a -> bool) (x : 'a) = T``)

val order_premise_rule =
  Tactical.prove
    (``!R : 'a -> 'a -> bool. !x : 'a.
         relation$transitive R ==>
         order_seed_carried R x ==> order_seed_targeted R x``,
     Rewrite.REWRITE_TAC [order_seed_targeted_def])

val order_premise_goal : Abbrev.goal =
  ([``relation$WeakLinearOrder (order_seed_le : 'a -> 'a -> bool)``,
    ``order_seed_carried (order_seed_le : 'a -> 'a -> bool)
        order_seed_a``],
   ``order_seed_targeted (order_seed_le : 'a -> 'a -> bool)
       order_seed_a``)

val _ =
  check
    ("an order premise reaches a rule's own premise",
     fn () =>
       let
         val spec =
           {kind = clasetRules.Dest, safe = false, prio = NONE}
         val () =
           clasetLib.temp_add_rule spec
             ("order_seed_premise_rule", order_premise_rule)
         val closed =
           closes_within 20 (clasimpLib.FASTFORCE_TAC [])
             order_premise_goal
         val () = clasetLib.temp_delrule "order_seed_premise_rule"
       in
         closed
       end)

(* A datatype and relation introduced by a client theory use the same
   declaration path as the bundled seeds.  The definition stays opaque to
   search; only the temporary destination rule exposes its consequence. *)
val _ = Datatype.Datatype `extension_node =
  ExtensionStart | ExtensionEnd`

val extension_edge_def =
  Definition.new_definition
    ("extension_edge_def",
     ``extension_edge (x : extension_node) y <=>
         x = ExtensionStart /\ y = ExtensionEnd``)

val extension_edge_dest =
  Tactical.prove
    (``!x y : extension_node.
         extension_edge x y ==> y = ExtensionEnd``,
     simpLib.SIMP_TAC boolSimps.bool_ss [extension_edge_def])

val extension_edge_goal : Abbrev.goal =
  ([``extension_edge (a : extension_node) b``],
   ``(b : extension_node) = ExtensionEnd``)

val _ =
  check
    ("a client datatype and relation use temporary search declarations",
     fn () =>
       let
         val tactic = clasimpLib.FASTFORCE_TAC []
         val opaque = not (closes_within 20 tactic extension_edge_goal)
         val spec =
           {kind = clasetRules.Dest, safe = false, prio = NONE}
         val () =
           clasetLib.temp_add_rule spec
             ("extension_edge_dest", extension_edge_dest)
         val declared = closes_within 20 tactic extension_edge_goal
         val () = clasetLib.temp_delrule "extension_edge_dest"
       in
         opaque andalso declared andalso
         not (closes_within 20 tactic extension_edge_goal)
       end)

(* src/HOL/List.thy:1830,1966-1969,2328,2337,1824 @ f7e02b7e.  None
   of the goals below is a corpus entry, and none is one of the rules:
   each indexes a list built by a constructor the seeds now push an
   index through, and then asks something the arithmetic settles.
   Excluding the seeds leaves every one of them with the index and the
   constructor side by side. *)
val _ =
  check
    ("the indexing seed views are usable",
     fn () =>
       List.all
         (closes_within 20 (clasimpLib.AUTO_TAC []))
         [([], ``!f xs index. index < LENGTH xs ==>
                  EL index (MAP f (MAP f xs)) = f (f (EL index xs))``),
          ([], ``!xs item index.
                  index < LENGTH xs ==>
                  EL index (LUPDATE item index xs) = item``),
          ([], ``!xs count index.
                  index < count ==> count <= LENGTH xs ==>
                  EL index (TAKE count xs) = EL index xs``),
          ([], ``!xs count index.
                  index + count < LENGTH xs ==>
                  EL index (DROP count xs) = EL (index + count) xs``),
          ([], ``!xs item ys.
                  EL (LENGTH xs) (xs ++ item::ys) = item``)])

(* src/HOL/List.thy @ f7e02b7e, [take_append] and [drop_append].
   Neither goal is a corpus entry and neither is one of the rules: each
   cuts an append at exactly the left list's length and maps over what
   is left, and pushing the cut through the append is what the two do.
   The halves the push leaves are already ambient -- TAKE_LENGTH_ID and
   DROP_LENGTH_NIL are simp -- so these two goals pin these two rules
   and nothing else. *)
val _ =
  check
    ("take and drop reach through an append",
     fn () =>
       List.all
         (closes_within 20 (clasimpLib.AUTO_TAC []))
         [([], ``!f xs ys. MAP f (TAKE (LENGTH xs) (xs ++ ys)) = MAP f xs``),
          ([], ``!f xs ys. MAP f (DROP (LENGTH xs) (xs ++ ys)) = MAP f ys``)])

(* src/HOL/List.thy @ f7e02b7e, the takeWhile primrec.  Neither goal is
   a corpus entry and neither is the rule: each walks a list past a
   prefix its predicate accepts.  The second states both halves of the
   decomposition, and only the takeWhile half is missing without the
   seed -- dropWhile_def is ambient either way. *)
val _ =
  check
    ("the prefix a predicate accepts reduces like the suffix",
     fn () =>
       List.all
         (closes_within 20 (clasimpLib.AUTO_TAC []))
         [([], ``!P x y zs. P x /\ ~P y ==>
                  takeWhile P (x::y::zs) = [x]``),
          ([], ``!P x ys. P x ==>
                  takeWhile P (x::ys) ++ dropWhile P (x::ys) =
                  x::(takeWhile P ys ++ dropWhile P ys)``)])

(* src/HOL/List.thy @ f7e02b7e, [take_all] and [drop_all]: the same cut
   where the bound is a length comparison rather than the length
   itself, which is where the ambient unconditional forms stop.  Both
   goals put the cut under a function, so the reduction has to happen
   as a rewrite: DROP_EQ_NIL is ambient and would settle [DROP n xs =
   []] posed as a goal, but it cannot rewrite the drop under a fold. *)
val _ =
  check
    ("a length bound cuts a take and a drop short",
     fn () =>
       List.all
         (closes_within 20 (clasimpLib.AUTO_TAC []))
         [([], ``!f xs n. LENGTH xs <= n ==> MAP f (TAKE n xs) = MAP f xs``),
          ([], ``!f a xs n. LENGTH xs <= n ==> FOLDL f a (DROP n xs) = a``)])

(* src/HOL/List.thy @ f7e02b7e, the declared results about the two
   walks: a dropWhile crosses an append by which half stops it, a
   takeWhile and a dropWhile put the list back together, and each walk
   reaching its own end reads as a statement about every element.  None
   of the five goals is a corpus entry, and each is stated over one of
   the five rules. *)
val _ =
  check
    ("a walk down a list survives an append and reads back",
     fn () =>
       List.all
         (closes_within 20 (clasimpLib.AUTO_TAC []))
         [([], ``!P xs ys. EVERY P xs ==>
                  LENGTH (dropWhile P (xs ++ ys)) =
                  LENGTH (dropWhile P ys)``),
          ([], ``!P xs (f:'a list -> 'b).
                  f (takeWhile P xs ++ dropWhile P xs) = f xs``),
          ([], ``!P xs ys. EXISTS ($~ o P) xs ==>
                  LENGTH (dropWhile P (xs ++ ys)) =
                  LENGTH (dropWhile P xs) + LENGTH ys``),
          ([], ``!P x xs. takeWhile P (x::xs) = x::xs ==> P x``),
          ([], ``!P xs. dropWhile P xs <> [] ==>
                  ?e. MEM e xs /\ ~P e``)])

(* src/HOL/List.thy @ f7e02b7e, [hd_in_set].  None of the three goals is
   a corpus entry and none is the rule: each carries a fact about every
   element of a list and has to read it off at the head, which is the
   step the declaration supplies -- the simplifier's condition solver
   discharges [MEM (HD l) l] from the list being non-empty and the
   element fact then applies.  The middle goal reaches the same place
   through a disjunction, where the non-emptiness is what the other
   disjunct denies. *)
val _ =
  check
    ("a fact about every element reaches the head",
     fn () =>
       List.all
         (closes_within 20 (clasimpLib.AUTO_TAC []))
         [([], ``!P xs. (!e. MEM e (xs:'a list) ==> ~P e) ==> xs <> [] ==>
                   ~P (HD xs)``),
          ([], ``!P xs. (!e. MEM e (xs:'a list) ==> ~P e) ==>
                   xs = [] \/ ~P (HD xs)``),
          ([], ``!P xs. EVERY P (xs:'a list) /\ xs <> [] ==> P (HD xs)``)])

(* src/HOL/List.thy @ f7e02b7e, [hd_replicate].  The goal is not a corpus
   entry and is not the rule: the walk stops at the first element its
   predicate rejects, which the given characterisation reads as the list
   being empty or its head being rejected.  The count is a variable, so
   no REPLICATE clause reduces and only the declaration says what that
   head is. *)
val _ =
  check
    ("the head of a replicate is the element it repeats",
     fn () =>
       closes_within 20 (clasimpLib.AUTO_TAC [listTheory.takeWhile_eq_nil])
         ([], ``!P n x. n <> 0 /\ ~P x ==>
                  takeWhile P (REPLICATE n (x:'a)) = []``))

(* src/HOL/List.thy:2559 @ f7e02b7e, [set_takeWhileD]'s second half.
   Neither goal is the rule: the first carries the predicate across a
   monotone implication, the second meets it with a FILTER against the
   negation, and both stop at [MEM y (takeWhile P xs)] with the
   predicate out of reach.  The rule's companion, membership in the
   list, is not needed by either. *)
val _ =
  check
    ("what a walk kept satisfies the predicate it walked by",
     fn () =>
       List.all
         (closes_within 20 (clasimpLib.AUTO_TAC []))
         [([], ``!P Q xs y.
                   (!z. P z ==> Q z) /\ MEM y (takeWhile P (xs:'a list)) ==>
                   Q y``),
          ([], ``!P xs y.
                   MEM y (takeWhile P (xs:'a list)) /\
                   MEM y (FILTER ($~ o P) xs) ==> F``)])

(* src/HOL/List.thy:1616,1635,1638 @ f7e02b7e, [filter_append] with
   [filter_False] and [filter_True].  Neither goal is a corpus entry and
   neither is a rule: each splits a filter at an append and then has to
   settle one half from what the context says about its elements, which
   is the step the collapse rules supply.  The first reads the left half
   away, the second keeps the right half whole. *)
val _ =
  check
    ("a filter splits at an append and each half is settled",
     fn () =>
       List.all
         (closes_within 20 (clasimpLib.AUTO_TAC []))
         [([], ``!P xs ys. (!e. MEM e (xs:'a list) ==> ~P e) ==>
                   FILTER P (xs ++ ys) = FILTER P ys``),
          ([], ``!P xs ys. EVERY P (ys:'a list) ==>
                   FILTER P (xs ++ ys) = FILTER P xs ++ ys``)])

(* src/HOL/List.thy:2247 @ f7e02b7e, [take_take], with the [min]
   absorptions of src/HOL/Lattices.thy:556.  The goal is not a corpus
   entry and is not a rule: two takes in a row have to become one, and
   the length that decides which one needs the comparison between them
   settled. *)
val _ =
  check
    ("a take of a take is the shorter take",
     fn () =>
       closes_within 20 (clasimpLib.AUTO_TAC [])
         ([], ``!n m l. TAKE n (TAKE (n + m) (l : 'a list)) = TAKE n l``))

(* src/HOL/Nat.thy:2632 @ f7e02b7e, [diff_diff_left].  The goal is not
   a corpus entry and is not the rule: the same two subtrahends are
   taken off in the two orders, under a list operation that no
   arithmetic decision procedure sees into, so the subtractions have to
   be combined before the AC rule the source method names can reach
   them. *)
val _ =
  check
    ("two subtractions are one and their order stops mattering",
     fn () =>
       closes_within 20
         (clasimpLib.AUTO_TAC [arithmeticTheory.ADD_COMM])
         ([], ``!n l. TAKE (LENGTH (l : 'a list) - n - 1) l =
                        TAKE (LENGTH l - 1 - n) l``))

(* src/HOL/List.thy:2209 @ f7e02b7e, [length_take], with
   [min_less_iff_conj] of src/HOL/Lattices.thy:573.  The goal is not a
   corpus entry and is not a rule: an index known only to be inside a
   take has to be read as inside both the list and the take's length
   before the rule that pushes the index through the take can fire. *)
val _ =
  check
    ("an index inside a take reaches the list it was taken from",
     fn () =>
       closes_within 20 (clasimpLib.AUTO_TAC [])
         ([], ``!n index l.
                  index < LENGTH (TAKE n (l : 'a list)) ==>
                  EL index (TAKE n l) = EL index l``))

(* src/HOL/List.thy:2256 @ f7e02b7e, [drop_drop].  The goal is not a
   corpus entry and is not the rule: two drops in a row are one drop of
   the sum, and only then does the order they were taken in stop
   mattering. *)
val _ =
  check
    ("a drop of a drop does not depend on the order",
     fn () =>
       closes_within 20
         (clasimpLib.AUTO_TAC [arithmeticTheory.ADD_COMM])
         ([], ``!n m l. DROP n (DROP m (l : 'a list)) =
                          DROP m (DROP n l)``))

(* src/HOL/List.thy:1348 @ f7e02b7e, [set_map].  The goal is not a
   corpus entry and is not the rule: what is known about the mapped
   list's elements is a property of the image, which is reached only
   once the element the image came from has been named. *)
val _ =
  check
    ("an element of a mapped list is the image of one of its own",
     fn () =>
       closes_within 20 (clasimpLib.AUTO_TAC [])
         ([], ``!(xs : num list) y. MEM y (MAP SUC xs) ==> y <> 0``))

(* src/HOL/List.thy:1521 @ f7e02b7e, [set_concat].  The goal is not a
   corpus entry and is not the rule: a claim about every inner list is
   read off one about the flattened one, which needs the inner list an
   element sits in to be named. *)
val _ =
  check
    ("what the flattened list omits every inner list omits",
     fn () =>
       closes_within 20 (clasimpLib.AUTO_TAC [])
         ([], ``!(xss : num list list).
                  ~MEM 0 (FLAT xss) ==> EVERY (\ys. ~MEM 0 ys) xss``))

(* src/HOL/List.thy:1521 @ f7e02b7e, [set_concat] where what it reads is
   a set rather than a membership.  The goal is not a corpus entry and
   is not the rule: the flattened list stands under a function of sets,
   with no membership around it, so the two sides meet only once the
   flattened list is read as the union it is.  The tactic is
   simplification alone, the rule being a rewrite. *)
val _ =
  check
    ("a flattened list standing as a set is read as a union",
     fn () =>
       closes_within 20
         (clasimpLib.asm_full_simp (lifted_default ()) [])
         ([], ``!(xss : 'a list list) (measure : 'a set -> num).
                  measure (set (FLAT xss)) =
                  measure (BIGUNION (IMAGE set (set xss)))``))

(* src/HOL/List.thy:2749 @ f7e02b7e, [zip_append].  The goal is not a
   corpus entry and is not the rule: two lists sharing a prefix are
   zipped and the pairs read off, and a pair is one of the shared
   prefix's or one of the tails' only once the zip comes apart there.
   The tactic is simplification alone, the rule being a rewrite.  It is
   read at the pairs rather than at the length: a length reduces
   through MIN without the zip ever coming apart. *)
val _ =
  check
    ("a zip of two appends with equal prefixes comes apart",
     fn () =>
       closes_within 20
         (clasimpLib.asm_full_simp (lifted_default ()) [])
         ([], ``!(xs : 'a list) ys zs pair.
                  MEM pair (ZIP (xs ++ ys, xs ++ zs)) <=>
                  MEM pair (ZIP (xs, xs)) \/ MEM pair (ZIP (ys, zs))``))

(* src/HOL/List.thy:1348,1521 @ f7e02b7e, the two together.  The goal is
   not a corpus entry and is not either rule: the pair has to be placed
   in the inner list its first component builds, and that list in the
   flattened one. *)
val _ =
  check
    ("a pair of elements sits in the list of their pairings",
     fn () =>
       closes_within 20 (clasimpLib.AUTO_TAC [])
         ([], ``!(xs : 'a list) (ys : 'b list) a b.
                  MEM a xs /\ MEM b ys ==>
                  MEM (a, b) (FLAT (MAP (\x. MAP (\y. (x, y)) ys) xs))``))

(* src/HOL/List.thy:1351 @ f7e02b7e, [set_filter].  The goal is not a
   corpus entry and is not the rule: what the context states about the
   list's own elements is stated the source's way round, and only a
   filtered membership read the same way round meets it.  The tactic is
   simplification alone, a search being free to reorder the conjunction
   the check is about. *)
val _ =
  check
    ("a filtered membership is read the way the source states it",
     fn () =>
       closes_within 20
         (clasimpLib.asm_full_simp (lifted_default ()) [])
         ([], ``!(xs : num list) P Q.
                  (!x. MEM x xs /\ P x <=> Q x) ==>
                  !y. MEM y (FILTER P xs) ==> Q y``))

(* src/HOL/List.thy:1106,1115 @ f7e02b7e, [map_map] and [map_eq_conv].
   The goal is not a corpus entry and is not either rule: the two sides
   walk the list a different number of times, so the fusion has to
   happen before the mapped functions can be compared, and comparing
   them is a step of its own -- as whole functions they are two
   different lambdas.  The pair is there because the elements the
   functions are compared on have to be taken apart before either
   lambda evaluates. *)
val _ =
  check
    ("a map of a map meets a single map through its elements",
     fn () =>
       closes_within 20 (clasimpLib.AUTO_TAC [])
         ([], ``!(xs : ('a # 'b) list) (f : 'c -> 'd) (g : 'a -> 'c).
                  MAP (\(a, b). f a) (MAP (\(a, b). (g a, b)) xs) =
                  MAP (\(a, b). f (g a)) xs``))

(* The predecessor's two spellings.  The goal is not a corpus entry and
   is not the rule: it is the split of a list at one index, written
   [PRE n] on the side a HOL4 rule would write it and [n - 1] on the
   side a translated goal would, and the rule that puts the halves back
   together needs the two indices to be one term. *)
val _ =
  check
    ("a list splits at an index written both ways",
     fn () =>
       closes_within 20 (clasimpLib.AUTO_TAC [])
         ([], ``!(xs : 'a list) n.
                  TAKE (PRE n) xs ++ DROP (n - 1) xs = xs``))

(* src/HOL/List.thy:1807 @ f7e02b7e, [nth_Cons_pos].  The goal is not a
   corpus entry and is not the rule: the list is a singleton appended
   to the rest, so the append has to be walked into a cons before the
   rule can reach the index at all, and the index is then read on the
   source's side in the spelling the rule does not use. *)
val _ =
  check
    ("an index reaches past a singleton appended to a list",
     fn () =>
       closes_within 20 (clasimpLib.AUTO_TAC [])
         ([], ``!(xs : 'a list) x n.
                  0 < n ==> EL n ([x] ++ xs) = EL (n - 1) xs``))

(* src/HOL/List.thy:1222 @ f7e02b7e, [rev_append].  Neither goal is a
   corpus entry and neither is the rule: the first needs the reversal
   moved past the append before the supplied fold law reaches the
   append underneath it, the second before the ambient involution
   reaches the reversal.  The tactic is the simplifier alone, which is
   what the source declares the rule to: the search closes both
   without it, by an induction no simplifier takes. *)
val _ =
  let
    val simplify =
      clasimpLib.asm_full_simp (clasimpLib.clasimp_ss ())
        [rich_listTheory.FOLDL_APPEND]
  in
    check
      ("a reversal is moved past an append",
       fn () =>
         List.all
           (closes_within 20 simplify)
           [([], ``!(xs : 'a list) ys f e.
                     FOLDL f e (REVERSE (xs ++ ys)) =
                     FOLDL f (FOLDL f e (REVERSE ys)) (REVERSE xs)``),
            ([], ``!(xs : 'a list) ys.
                     REVERSE (REVERSE xs ++ ys) = REVERSE ys ++ xs``)])
  end

(* src/HOL/List.thy:2045,2085 @ f7e02b7e, [butlast_snoc] and
   [append_butlast_last_id].  Neither goal is a corpus entry and
   neither is a rule: the first reads a front off under a REVERSE, the
   second puts a list back together under a further append.  HOL4
   states the pair on SNOC and keeps [SNOC_APPEND] out of the simpset,
   so a front of an append reduces only once the append spelling is
   declared. *)
val _ =
  check
    ("a front and a last are read off an append",
     fn () =>
       List.all
         (closes_within 20 (clasimpLib.AUTO_TAC []))
         [([], ``!(xs : 'a list) x. REVERSE (FRONT (xs ++ [x])) = REVERSE xs``),
          ([], ``!(ys : 'a list) x.
                   ys <> [] ==> FRONT ys ++ [LAST ys] ++ [x] = ys ++ [x]``)])

(* src/HOL/List.thy:5882 @ f7e02b7e, [sorted_wrt_take] and
   [sorted_wrt_drop].  Neither goal is a corpus entry and neither is a
   rule: the first takes a segment of a segment, so it needs both rules
   composed, and the second has to strip a head off the sorted list
   before either rule reaches it. *)
val _ =
  check
    ("a segment of a sorted list is sorted",
     fn () =>
       List.all
         (closes_within 20 (clasimpLib.AUTO_TAC []))
         [([], ``!le (xs : 'a list) count.
                   SORTED le xs ==> SORTED le (TAKE count (DROP count xs))``),
          ([], ``!le (xs : 'a list) x count.
                   SORTED le (x::xs) ==> SORTED le (DROP count xs)``)])

(* [adjacent_thm] settles a pair that is the head of the list, and
   [adjacent_iff] is what walks one further in.  The goal below asks for
   a pair one place beyond the head of a list with an arbitrary tail, so
   it needs the walk and not the head equation. *)
val _ =
  check
    ("an adjacent pair one place past the head of a list is found",
     fn () =>
       closes_within 20 (clasimpLib.AUTO_TAC [])
         ([], ``!(xs : 'a list) x y z. adjacent (x::y::z::xs) y z``))

(* A null and an empty list are one thing to Isabelle's simpset and
   were two to HOL4's.  The goal below states a hypothesis with one
   spelling and its conclusion with the other, so it closes only if the
   step between them is declared. *)
val _ =
  check
    ("a null list meets a list stated empty",
     fn () =>
       closes_within 20 (clasimpLib.AUTO_TAC [])
         ([], ``!(xs : 'a list) (ys : 'a list).
                  NULL xs /\ LENGTH ys = LENGTH xs ==> ys = []``))

(* src/HOL/List.thy:1348,1521 and src/HOL/Set.thy:893 @ f7e02b7e.
   Neither goal is a corpus entry.  A membership in a flattened map is
   two decompositions deep, and MEM_MAP_CASES_AUTO is declared safe
   there, as Isabelle declares [imageE] [elim!]: the decompositions are
   taken in the safe cascade and spend no stage of the classical leg,
   so the two stages the method runs it to are still there for the
   implication beyond them.  Declared an ordinary dest rule each
   decomposition spends a stage instead, the bound is out before the
   implication is reached, and the second goal is left open -- which is
   the half of [list_L7054_set_trans_list_step_subset_trancl] of the
   list/map corpus this rule answers for, the closure the decomposition
   uncovers being set_relationAutoSeed's.  The first goal asks for
   nothing past the decompositions and closes under either class; it is
   here to put the boundary where the measurement found it. *)
val _ =
  check
    ("a flattened mapped membership decomposes without spending a stage",
     fn () =>
       List.all
         (closes_within 20 (clasimpLib.AUTO_TAC []))
         [([], ``!(seed_flat_lists : 'a list list)
                   (seed_flat_f : 'a -> 'b) seed_flat_p seed_flat_y.
                   (!xs x. MEM xs seed_flat_lists /\ MEM x xs ==>
                           seed_flat_p (seed_flat_f x)) /\
                   MEM seed_flat_y
                     (FLAT (MAP (MAP seed_flat_f) seed_flat_lists)) ==>
                   seed_flat_p seed_flat_y``),
          ([], ``!(seed_flat_lists : 'a list list)
                   (seed_flat_f : 'a -> 'b) seed_flat_p seed_flat_q
                   seed_flat_y.
                   (!b. seed_flat_p b ==> seed_flat_q b) /\
                   (!xs x. MEM xs seed_flat_lists /\ MEM x xs ==>
                           seed_flat_p (seed_flat_f x)) /\
                   MEM seed_flat_y
                     (FLAT (MAP (MAP seed_flat_f) seed_flat_lists)) ==>
                   seed_flat_q seed_flat_y``)])

(* src/HOL/Complete_Lattices.thy:1052 and src/HOL/Set.thy:1663
   @ f7e02b7e.  Neither goal is a corpus entry.  [UN_iff] and the image
   clause of [bex_simps] are simp there, and what they buy is applying
   the function: a membership in a union of an image names the element
   the outer list holds and puts the inner list in its place, where
   reading IN_BIGUNION and IN_IMAGE separately leaves a set standing
   that only an equation under a further existential fixes -- and
   neither simplifier eliminates a quantifier so fixed.  One flatten
   deep that costs nothing, which is what the second goal here records;
   two deep the layer beneath is never exposed at all, and the first
   goal is left open with the list it names unguessed. *)
val _ =
  check
    ("a pair is placed two flattened maps deep",
     fn () =>
       closes_within 25 (clasimpLib.AUTO_TAC [])
         ([], ``!(seed_image_rows : ('a # 'b) list)
                  (seed_image_cols : ('b # 'c) list) seed_image_test
                  (seed_image_a : 'a) (seed_image_b : 'b)
                  (seed_image_c : 'c).
                  MEM (seed_image_a,seed_image_b) seed_image_rows /\
                  MEM (seed_image_b,seed_image_c) seed_image_cols /\
                  seed_image_test (seed_image_a,seed_image_b)
                    (seed_image_b,seed_image_c) ==>
                  MEM (seed_image_a,seed_image_c)
                    (FLAT
                       (MAP
                          (\seed_row.
                             FLAT
                               (MAP
                                  (\seed_col.
                                     if seed_image_test seed_row seed_col
                                     then [(FST seed_row,SND seed_col)]
                                     else []) seed_image_cols))
                          seed_image_rows))``))

val _ =
  check
    ("a pair is placed one flattened map deep",
     fn () =>
       closes_within 25 (clasimpLib.AUTO_TAC [])
         ([], ``!(seed_image_cols : ('b # 'c) list) seed_image_test
                  (seed_image_a : 'a) (seed_image_b : 'b)
                  (seed_image_c : 'c).
                  MEM (seed_image_b,seed_image_c) seed_image_cols /\
                  seed_image_test (seed_image_b,seed_image_c) ==>
                  MEM (seed_image_a,seed_image_c)
                    (FLAT
                       (MAP
                          (\seed_col.
                             if seed_image_test seed_col then
                               [(seed_image_a,SND seed_col)]
                             else []) seed_image_cols))``))

(* src/HOL/Set.thy:883-884 @ f7e02b7e.  Isabelle's [image_def] states
   the bounded-domain premise before the value equality, and pred_set's
   IN_IMAGE states it after.  The simplifier carries a conjunct's left
   siblings into it as context, so only the source's order has the
   membership in hand when the equality's right-hand side is rewritten,
   which is what an equation conditional on that membership needs.
   Neither the rule nor the goal is a corpus entry, and the rule is
   assumed because only the shape of its condition is under test.  The
   check goes through SIMP_CONV for the reason the order side condition
   above does: what the order decides is the rewriter's reach, and a
   check through AUTO_TAC says nothing, the search stripping the
   existential into assumptions where both conjuncts stand side by side
   and the order cannot matter. *)
val image_domain_rule =
  Thm.ASSUME
    ``!seed_cong_x : 'a.
        seed_cong_x IN seed_cong_set ==>
        (seed_cong_f seed_cong_x : 'b) = seed_cong_g seed_cong_x``

val image_domain_goal =
  ``!seed_cong_value : 'b.
      seed_cong_value IN IMAGE seed_cong_f seed_cong_set <=>
      seed_cong_value IN IMAGE seed_cong_g (seed_cong_set : 'a -> bool)``

val _ =
  check
    ("an image membership rewrites under its domain premise",
     fn () =>
       let
         val rewritten =
           simpLib.SIMP_CONV (clasimpLib.clasimp_ss ())
             [image_domain_rule] image_domain_goal
       in
         Term.aconv (boolSyntax.rhs (Thm.concl rewritten)) boolSyntax.T
       end
       handle Conv.UNCHANGED => false)

(* src/HOL/Set.thy:1650,1660 @ f7e02b7e.  Neither goal is a corpus
   entry, and neither is the clause: each asks for it twice over, at a
   list of two whose tail is still a variable, so the head splits off
   and the clause must meet what it left behind.  The insert clauses of
   [ball_simps] and [bex_simps] are simp in the source, and a bounded
   quantifier over a cons meets them because Isabelle reads
   [set (x # xs)] as an insert.  HOL4 states list membership as MEM,
   and outermost-first a quantified membership descends into MEM's own
   cons equation instead, leaving a disjunctive bound that no rule
   about the quantifier matches again -- and what that leaves is not
   closed by the ambient simpset, measured. *)
val _ =
  check
    ("a bounded quantifier over a cons splits off the head",
     fn () =>
       List.all
         (fn goal =>
            Term.aconv
              (boolSyntax.rhs
                 (Thm.concl
                    (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) [] goal)))
              boolSyntax.T
            handle Conv.UNCHANGED => false)
         [``(!e. MEM e (seed_cons_a::seed_cons_b::seed_cons_xs) ==>
                 seed_cons_p e) <=>
             seed_cons_p seed_cons_a /\ seed_cons_p seed_cons_b /\
             !e. MEM e seed_cons_xs ==> seed_cons_p e``,
          ``(?e. MEM e (seed_cons_a::seed_cons_b::seed_cons_xs) /\
                 seed_cons_p e) <=>
             seed_cons_p seed_cons_a \/ seed_cons_p seed_cons_b \/
             ?e. MEM e seed_cons_xs /\ seed_cons_p e``])

(* src/HOL/Set.thy:824-825 @ f7e02b7e.  Not a corpus entry.  The
   witness is a singleton and nothing in the goal names it.  The safe
   introduction the iff derives, [x = y ==> x IN {y}], settles the set
   on a singleton and leaves the equation that names the element
   standing; the branch denying the other membership is then offered a
   set the equation has not fixed, and the arithmetic that would decide
   the denial is handed a literal carrying an unsolved variable.  Where
   the denial is an assumption rather than a consequence the branch
   closes either way -- measured -- which is why the premise here is an
   order and not a disequality.  [singletonI] closes its branch where
   it settles the set, so the denial meets a determined one; that is
   what Isabelle's own comment on the rule says it is for. *)
val _ =
  check
    ("a singleton witness is settled by the membership alone",
     fn () =>
       closes_within 20 (clasimpLib.AUTO_TAC [])
         ([], ``!seed_sing_a seed_sing_b : int.
                  seed_sing_a < seed_sing_b ==>
                  ?seed_sing_set.
                    seed_sing_a NOTIN seed_sing_set /\
                    seed_sing_b IN seed_sing_set``))

(* src/HOL/Nat.thy:1470-1472 @ f7e02b7e.  Not a corpus entry, and not
   the rule: what the successor clause buys is the outermost
   application, exposed so that a fact about the iterated function
   reaches it.  Here that fact is the assumption, and without the
   clause the iteration at a successor is one inert term the
   assumption does not match. *)
val _ =
  check
    ("a fact about the iterated function reaches the step a successor adds",
     fn () =>
       closes_within 20 (clasimpLib.AUTO_TAC [])
         ([], ``!seed_funpow_step seed_funpow_xs seed_funpow_times.
                  (!ys. NULL (seed_funpow_step ys) <=> NULL ys) ==>
                  (NULL
                     (FUNPOW seed_funpow_step (SUC seed_funpow_times)
                        (seed_funpow_xs : 'a list)) <=>
                   NULL
                     (FUNPOW seed_funpow_step seed_funpow_times
                        seed_funpow_xs))``))

(* src/HOL/Fun.thy:143,155-156 @ f7e02b7e.  Not a corpus entry, and
   not the rule: what the bridge buys is that a surjectivity reaches
   the ambient image membership, on the goal side and on the
   assumption side alike.  Without it SURJ is an atom the search
   carries along whole. *)
val _ =
  check
    ("a surjectivity is read through the image membership",
     fn () =>
       closes_within 20 (clasimpLib.AUTO_TAC [])
         ([], ``!seed_surj_f seed_surj_s seed_surj_t.
                  SURJ seed_surj_f (seed_surj_s : 'a set)
                       (seed_surj_t : 'b set) ==>
                  SURJ seed_surj_f seed_surj_s
                       (IMAGE seed_surj_f seed_surj_s) /\
                  !y. y IN seed_surj_t ==>
                      ?x. x IN seed_surj_s /\ seed_surj_f x = y``))

(* src/HOL/Set.thy:484,493,501 @ f7e02b7e.  Neither goal is a corpus
   entry.  Isabelle settles a relation inclusion with the same three
   rules it settles a set inclusion with, a relation being a set of
   pairs there; HOL4's curried inclusion is a separate constant, and
   without the three declared on RSUBSET the search has nothing to take
   one apart with and neither goal closes. *)
val _ =
  check
    ("a curried relation inclusion is settled classically",
     fn () =>
       List.all
         (closes_within 20 (tableauLib.BLAST_TAC []))
         [([], ``(!x y. seed_rsub_left x y ==> seed_rsub_right x y) ==>
                 seed_rsub_left RSUBSET seed_rsub_right``),
          ([], ``seed_rsub_left RSUBSET seed_rsub_middle ==>
                 seed_rsub_middle RSUBSET seed_rsub_right ==>
                 seed_rsub_left RSUBSET seed_rsub_right``)])

(* src/HOL/HOL.thy:1396-1414,1442-1443 @ f7e02b7e.  The twelve
   miniscoping laws.  Neither the readings below nor the two goals are
   corpus entries: the readings ask for each law outright, and the
   goals ask for what declaring them buys -- a rule stated of the
   narrower scope meets a body the goal quantifies over whole. *)
val miniscoping_readings =
  [(``!b. seed_mini_p (b:'a) /\ seed_mini_q``,
    ``(!b. seed_mini_p (b:'a)) /\ seed_mini_q``),
   (``!b. seed_mini_q /\ seed_mini_p (b:'a)``,
    ``seed_mini_q /\ !b. seed_mini_p (b:'a)``),
   (``!b. seed_mini_p (b:'a) \/ seed_mini_q``,
    ``(!b. seed_mini_p (b:'a)) \/ seed_mini_q``),
   (``!b. seed_mini_q \/ seed_mini_p (b:'a)``,
    ``seed_mini_q \/ !b. seed_mini_p (b:'a)``),
   (``!b. seed_mini_p (b:'a) ==> seed_mini_q``,
    ``(?b. seed_mini_p (b:'a)) ==> seed_mini_q``),
   (``!b. seed_mini_q ==> seed_mini_p (b:'a)``,
    ``seed_mini_q ==> !b. seed_mini_p (b:'a)``),
   (``?b. seed_mini_p (b:'a) /\ seed_mini_q``,
    ``(?b. seed_mini_p (b:'a)) /\ seed_mini_q``),
   (``?b. seed_mini_q /\ seed_mini_p (b:'a)``,
    ``seed_mini_q /\ ?b. seed_mini_p (b:'a)``),
   (``?b. seed_mini_p (b:'a) \/ seed_mini_q``,
    ``(?b. seed_mini_p (b:'a)) \/ seed_mini_q``),
   (``?b. seed_mini_q \/ seed_mini_p (b:'a)``,
    ``seed_mini_q \/ ?b. seed_mini_p (b:'a)``),
   (``?b. seed_mini_p (b:'a) ==> seed_mini_q``,
    ``(!b. seed_mini_p (b:'a)) ==> seed_mini_q``),
   (``?b. seed_mini_q ==> seed_mini_p (b:'a)``,
    ``seed_mini_q ==> ?b. seed_mini_p (b:'a)``)]

val _ =
  check
    ("the miniscoping laws are ambient",
     fn () =>
       List.all
         (fn (redex, reduct) =>
            Term.aconv
              (boolSyntax.rhs
                 (Thm.concl
                    (Conv.QCONV
                       (simpLib.SIMP_CONV (BasicProvers.srw_ss ()) [])
                       redex)))
              reduct)
         miniscoping_readings)

val miniscoping_rule =
  Thm.ASSUME ``(?b. seed_mini_r (b:'a)) <=> seed_mini_s``

val _ =
  check
    ("a rule stated of the narrower scope meets a quantified body",
     fn () =>
       List.all
         (fn goal =>
            (Term.aconv
               (boolSyntax.rhs
                  (Thm.concl
                     (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ())
                        [miniscoping_rule] goal)))
               boolSyntax.T
             handle Conv.UNCHANGED => false))
         [``(!b. seed_mini_r (b:'a) ==> seed_mini_q) <=>
              (seed_mini_s ==> seed_mini_q)``,
          ``(?b. seed_mini_r (b:'a) /\ seed_mini_q) <=>
              (seed_mini_s /\ seed_mini_q)``])
