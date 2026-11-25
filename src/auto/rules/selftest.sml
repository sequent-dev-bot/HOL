open HolKernel Parse Tactic testutils boolSyntax
open NTactical clasetNet clasetRules clasetLib clasetSeedTheory

fun test (name, check) =
  (tprint name;
   if check () then OK () else die "failed")

(* A selftest binary starts with no theory segment open, so a datatype
   has nowhere to be declared until one is. *)
val _ = Theory.new_theory "clasetHookSelftest"

(* This deliberately precedes the first [the_claset] demand below. *)
val _ = Datatype.Datatype
  `claset_hook_before_demand = ClasetHookA | ClasetHookB num`

(* Payload and pure-enum datatypes exercise both case-definition forms. *)
val _ = Datatype.Datatype
  `claset_hook_wide =
     ClasetWide0 | ClasetWide1 | ClasetWide2 | ClasetWide3 | ClasetWide4
   | ClasetWide5 | ClasetWide6 | ClasetWide7 | ClasetWide8 | ClasetWide9
   | ClasetWide10 | ClasetWide11 | ClasetWide12 | ClasetWide13
   | ClasetWide14 | ClasetWide15 num`

val _ = Datatype.Datatype
  `claset_hook_enum = Enum0 | Enum1 | Enum2 | Enum3 | Enum4 | Enum5
   | Enum6 | Enum7 | Enum8 | Enum9 | Enum10 | Enum11 | Enum12 | Enum13
   | Enum14 | Enum15`

val _ = Datatype.Datatype
  `claset_hook_poly = PolyLeft 'a | PolyRight 'a`

(* Global removal of a TypeBase-derived rule is refused, so it cannot depend
   on whether the claset has been forced.  These calls precede the first
   demand; the tests after it repeat them on the forced claset. *)
val tyinfo_reserved_stem =
  "__claset_tyinfo_clasetHookSelftest_claset_hook_before_demand_"
val tyinfo_reserved_names =
  [tyinfo_reserved_stem ^ "inject_0_intro", tyinfo_reserved_stem ^ "distinct"]

fun capture_warnings f =
  let
    val output = ref ([] : string list)
    fun collect text = output := text :: !output
  in
    Lib.with_flag (Feedback.WARNING_outstream, collect) f ();
    List.rev (!output)
  end

(* Each name yields one warning per call, naming it. *)
fun delete_reserved_names () =
  map (fn name =>
         (name, capture_warnings (fn () => (temp_delrule name; delrule name))))
    tyinfo_reserved_names

fun warned_per_call results =
  List.all
    (fn (name, warnings) =>
       length warnings = 2 andalso
       List.all (String.isSubstring name) warnings)
    results

val unforced_reserved_deletions = delete_reserved_names ()

(* An ancestor theory's recorded removal replays as remove_rule of the
   qualified name it was recorded under, through the same update queue
   that augment_claset uses. *)
fun replay_reserved_removals () =
  List.app
    (fn name => augment_claset (remove_rule (normalise_rule_name name)))
    tyinfo_reserved_names

val _ = replay_reserved_removals ()

fun same_seed_spec
  ({kind = kind1, safe = safe1, prio = prio1} : rulespec)
  ({kind = kind2, safe = safe2, prio = prio2} : rulespec) =
  kind1 = kind2 andalso safe1 = safe2 andalso prio1 = prio2

val seed_initialisation_start = Time.now ()
val seed_claset = the_claset ()
val seed_initialisation_time =
  Time.- (Time.now (), seed_initialisation_start)

val seed_sintro_spec =
  {kind = clasetRules.Intro, safe = true, prio = NONE}
val seed_intro_spec =
  {kind = clasetRules.Intro, safe = false, prio = NONE}
val seed_selim_spec =
  {kind = clasetRules.Elim, safe = true, prio = NONE}
val seed_elim_spec =
  {kind = clasetRules.Elim, safe = false, prio = SOME 75}

val seed_expected_rules =
  [(seed_sintro_spec, "bool$TRUTH"),
   (seed_sintro_spec, "bool$EQ_REFL"),
   (seed_sintro_spec, "clasetSeed$DISJ_CINTRO_THM"),
   (seed_sintro_spec, "bool$IMP_F"),
   (seed_sintro_spec, "clasetSeed$EX_EX1_INTRO_THM"),
   (seed_sintro_spec, "bool$AND_INTRO_THM"),
   (seed_sintro_spec, "bool$IMP_ANTISYM_AX"),
   (seed_selim_spec, "bool$FALSITY"),
   (seed_selim_spec, "clasetSeed$EX1_ELIM_THM"),
   (seed_selim_spec, "clasetSeed$EXISTS_ELIM_THM"),
   (seed_selim_spec, "clasetSeed$CONJ_ELIM_THM"),
   (seed_selim_spec, "clasetSeed$IFF_CELIM_THM"),
   (seed_selim_spec, "clasetSeed$IMP_CELIM_THM"),
   (seed_selim_spec, "bool$OR_ELIM_THM"),
   (seed_intro_spec, "clasetSeed$EXISTS_INTRO_THM"),
   (seed_intro_spec, "bool$EQ_EXT"),
   (seed_intro_spec, "clasetSeed$EX1_INTRO_THM"),
   (seed_elim_spec, "clasetSeed$FORALL_ELIM_THM")]

val seed_theory_name = "clasetSeed"

fun seed_export_identity name = seed_theory_name ^ "$" ^ name

val seed_programmatic_schemas =
  map seed_export_identity
    ["NOT_IMP_CELIM_THM", "NOT_FORALL_CELIM_THM", "NOT_ELIM_THM"]

fun untagged_theorems
  {theorem_names, persistent_rule_names, permitted} =
  let
    fun classified name =
      List.exists
        (fn rule_name => rule_name = name) persistent_rule_names orelse
      List.exists (fn permitted_name => permitted_name = name) permitted
  in
    List.filter (not o classified) theorem_names
  end

val _ =
  test
    ("seed classification requires fully qualified persistent rule names",
     fn () =>
       untagged_theorems
         {theorem_names =
            map seed_export_identity ["TAGGED", "NOT_ELIM_THM", "UNTAGGED"],
          persistent_rule_names =
            [seed_export_identity "TAGGED", "foreign$UNTAGGED"],
          permitted = seed_programmatic_schemas} =
       [seed_export_identity "UNTAGGED"])

val persisted_seed_claset =
  case persistent_claset_of_theory {thyname = seed_theory_name} of
      SOME cs => cs
    | NONE => raise Fail "clasetSeed has no persisted claset data"

val untagged_seed_theorems =
  untagged_theorems
    {theorem_names =
       map (seed_export_identity o #1) (DB.theorems seed_theory_name),
     persistent_rule_names = map (#1 o #2) (rules_of persisted_seed_claset),
     permitted = seed_programmatic_schemas}

val _ =
  (tprint "every seed theorem is a claset rule or permitted schema";
   case untagged_seed_theorems of
       [] => OK ()
     | names =>
         die ("untagged clasetSeed theorem(s): " ^
              String.concatWith ", " names))

fun is_seed_rule (_, (name, _)) =
  List.exists (fn (_, expected_name) => name = expected_name)
    seed_expected_rules

val _ =
  test
    ("seed claset contains the HOL.thy rules in canonical order",
     fn () =>
       ListPair.allEq
         (fn ((spec, (name, _)), (expected_spec, expected_name)) =>
            name = expected_name andalso same_seed_spec spec expected_spec)
         (List.filter is_seed_rule (rules_of seed_claset), seed_expected_rules)
       andalso
       not (List.exists
              (fn (_, (name, _)) => name = "clasetSeed$NOT_ELIM_THM")
              (rules_of seed_claset)))

val _ =
  test
    ("seed claset initialisation stays within its load-time budget",
     fn () => Time.< (seed_initialisation_time, Time.fromMilliseconds 750))

fun same_terms ts1 ts2 =
  ListPair.allEq (fn (tm1, tm2) => Term.aconv tm1 tm2) (ts1, ts2)

fun labelled tm _ _ =
  seq.result ([([], tm)], fn _ => ASSUME tm)

fun labels tac goal =
  map
    (fn (gs, _) =>
       case gs of
           [(_, tm)] => tm
         | _ => raise Fail "labelled tactic did not return one goal")
    (seq.take 10 (tac goal (Context.snapshot())))

val p = ``p : bool``
val q = ``q : bool``
val r = ``r : bool``
val label_goal = ([], p)

val _ =
  test
    ("NORELSE is associative",
     fn () =>
       same_terms
         (labels (NORELSE (NORELSE (labelled p, labelled q), labelled r))
            label_goal)
         (labels (NORELSE (labelled p, NORELSE (labelled q, labelled r)))
            label_goal))

val _ =
  test
    ("NAPPEND is associative",
     fn () =>
       same_terms
         (labels (NAPPEND (NAPPEND (labelled p, labelled q), labelled r))
            label_goal)
         (labels (NAPPEND (labelled p, NAPPEND (labelled q, labelled r)))
            label_goal))

val choice_goal = ([p], p)
val close = LIFT (Tactical.FIRST_ASSUM ACCEPT_TAC)

val _ =
  test
    ("NORELSE does not backtrack after later failure",
     fn () =>
       seq.null
         (NTHEN (NORELSE (NALL_TAC, close), NNO_TAC)
            choice_goal (Context.snapshot())))

val _ =
  test
    ("NAPPEND backtracks after later failure",
     fn () =>
       not
         (seq.null
            (NTHEN (NAPPEND (NALL_TAC, close), NNO_TAC)
               choice_goal (Context.snapshot()))))

val _ =
  let
    fun diverging_branch _ _ =
      let fun loop () = loop () in loop () end
    val _ =
      seq.hd (NORELSE (NALL_TAC, diverging_branch)
                choice_goal (Context.snapshot()))
  in
    test ("NORELSE leaves a diverging second branch unforced", fn () => true)
  end

val validation_goal = ([p, q], ``p /\ q``)
val validation_tac =
  DETERM
    (NTHEN (LIFT CONJ_TAC, LIFT (Tactical.FIRST_ASSUM ACCEPT_TAC)))

val _ =
  test
    ("NTHEN composed validations satisfy Tactical.VALID",
     fn () =>
       let
         val (gs, _) =
           Tactical.VALID validation_tac validation_goal (Context.snapshot())
       in
         List.null gs
       end)

val repeat_goal : Abbrev.goal = ([], ``p ==> p``)

val _ =
  test
    ("NREPEAT keeps only the first result at every iteration",
     fn () =>
       let
         val (gs, _) =
           Tactical.VALID (DETERM (NREPEAT (LIFT DISCH_TAC))) repeat_goal
             (Context.snapshot())
       in
         case gs of
             [([asm], tm)] => Term.aconv asm p andalso Term.aconv tm p
           | _ => false
       end)

fun tmset ts = HOLset.fromList Term.compare ts

fun mem x xs = List.exists (fn y => x = y) xs

fun rigid_frees pat patvars =
  tmset (List.filter (fn v => not (HOLset.member (patvars, v)))
                     (free_vars pat))

fun really_matches pat patvars query =
  can (Term.raw_match [] (rigid_frees pat patvars) pat query) ([], [])

(* Either directional match is a brute-force witness to unifiability. *)
fun really_unifies pat patvars query qvars =
  really_matches pat patvars query orelse really_matches query qvars pat

val x = ``x : bool``
val y = ``y : bool``
val f = ``f : bool -> bool``
val g = ``g : bool -> bool``
val small_terms =
  [p, q, r, ``~p``, ``p /\ q``, ``p ==> q``,
   ``(f : bool -> bool) p``,
   ``\z : bool. z``, ``\z : bool. p /\ z``]

val small_patterns =
  [(x, tmset [x]),
   (``x /\ y``, tmset [x, y]),
   (``x ==> y``, tmset [x, y]),
   (``~x``, tmset [x]),
   (``(f : bool -> bool) x``, tmset [x]),
   (``\z : bool. x /\ z``, tmset [x]),
   (``\z : bool. z``, tmset [])]

fun random_pairs n =
  let
    val plen = length small_patterns
    val qlen = length small_terms
    fun loop 0 _ acc = acc
      | loop k seed acc =
          let
            val seed' = (seed * 37 + 17) mod 997
            val pat = List.nth (small_patterns, seed' mod plen)
            val query = List.nth (small_terms, (seed' div plen) mod qlen)
          in
            loop (k - 1) seed' ((pat, query) :: acc)
          end
  in
    loop n 19 []
  end

val net_entries =
  ListPair.zip (List.tabulate (length small_patterns, fn i => i),
                small_patterns)

val small_net =
  List.foldl
    (fn ((i, (pat, patvars)), net) =>
        insert ({pat = pat, patvars = patvars}, i) net)
    empty net_entries

val _ =
  test
    ("clasetNet match retrieves every brute-force random match",
     fn () =>
       List.all
         (fn (((pat, patvars), query)) =>
            List.all
              (fn (i, (stored, storedvars)) =>
                 not (really_matches stored storedvars query) orelse
                 mem i (match query small_net))
              net_entries)
         (random_pairs 80))

val query_var_sets = [tmset [], tmset [p], tmset [q], tmset [p, q]]

val _ =
  test
    ("clasetNet unify retrieves every brute-force random unifier",
     fn () =>
       List.all
         (fn (((_, _), query)) =>
            List.all
              (fn qvars =>
                 List.all
                   (fn (i, (stored, storedvars)) =>
                      not (really_unifies stored storedvars query qvars) orelse
                      mem i (unify {q = query, qvars = qvars} small_net))
                   net_entries)
              query_var_sets)
         (random_pairs 80))

fun one pat patvars = insert ({pat = pat, patvars = patvars}, 1) empty

val _ =
  test
    ("clasetNet all-free queries preserve hits and checkpoint counts",
     fn () =>
       let
         val patterns =
           [``\z:bool. z /\ T``, ``\z:bool. T /\ T``,
            ``\z:bool. (\u:bool. u /\ T) (z /\ T)``,
            ``\z:bool. (\u:bool. T /\ T) (z /\ T)``,
            ``(T, \z:bool. z /\ T)``, ``(T, \z:bool. T /\ T)``]
         val net =
           List.foldl
             (fn ((i, pat), net) =>
               insert ({pat = pat, patvars = Term.empty_tmset}, i) net)
             small_net (Lib.enumerate 10 patterns)
         val no_checkpoint = listUtil.no_checkpoint
         fun check (q, hit, miss) =
           let
             val old_query = {q = q, qvars = Term.FVL [q] Term.empty_tmset}
             val old_polls = ref 0
             val new_polls = ref 0
             fun poll count () = count := !count + 1
             val ordinary = unify old_query net
             val old_measured = unifyMeasured (poll old_polls) old_query net
             val new_measured = unifyFreesMeasured (poll new_polls) q net
           in
             mem hit ordinary andalso not (mem miss ordinary) andalso
             unifyFreesMeasured no_checkpoint q net = ordinary andalso
             old_measured = ordinary andalso new_measured = ordinary andalso
             !old_polls > 0 andalso !old_polls = !new_polls
           end
       in
         List.all check
           [(``\z:bool. z /\ p``, 10, 11),
            (``\z:bool. (\z:bool. z /\ p) (z /\ q)``, 12, 13),
            (``(z, \z:bool. z /\ p)``, 14, 15),
            (``\z:bool. (f:bool -> bool) z``, 11, ~1)]
       end)

val _ =
  test
    ("clasetNet retrieves an abstraction key and follows Cmb rators",
     fn () =>
     mem 1
       (match ``\a : bool. p /\ a``
          (one ``\z : bool. x /\ z`` (tmset [x])))
     andalso mem 1
       (match ``(f : bool -> bool) p``
          (one ``(f : bool -> bool) x`` (tmset [x])))
     andalso not
       (mem 1
          (match ``(g : bool -> bool) p``
             (one ``(f : bool -> bool) x`` (tmset [x])))))

val _ =
  test
    ("clasetNet unification harvests abstraction and Cmb subnets",
     fn () =>
       mem 1
         (unify {q = x, qvars = tmset [x]}
            (one ``\z : bool. z`` (tmset [])))
       andalso mem 1
         (unify {q = x, qvars = tmset [x]}
            (one ``(f : bool -> bool) p`` (tmset [])))
       andalso mem 1
         (unify {q = ``\z : bool. z``, qvars = tmset []}
            (one x (tmset [x]))))

val _ =
  test
    ("clasetNet wildcard traversal preserves edge and tip order",
     fn () =>
       let
         val f = ``f : bool -> bool -> bool``
         fun pair a b = list_mk_comb (f, [a, b])
         val entries =
           [(p, q, [], 1), (x, q, [x], 2),
            (``!z : bool. z /\ p``, q, [], 3), (p, q, [], 4),
            (``p /\ q``, p, [], 5)]
         val net =
           List.foldl
             (fn ((a, b, vars, i), net) =>
               insert ({pat = pair a b, patvars = tmset vars}, i) net)
             empty entries
         val query = {q = pair x q, qvars = tmset [x]}
         val expected = [4, 1, 2, 3]
       in
         unify query net = expected andalso
         unifyMeasured (fn () => ()) query net = expected
       end)

val _ =
  test
    ("clasetNet returns exact matches before wildcard matches at every level",
     fn () =>
       let
         val f = mk_var ("f", bool --> bool)
         val patvars = tmset [x]
         fun apply t = mk_comb (f, t)
         val net = List.foldl
           (fn ((pat, i), net) => insert ({pat = pat, patvars = patvars}, i) net)
           empty [(x, 1), (apply x, 2), (apply (apply x), 3), (apply x, 4)]
         val query = apply (apply boolSyntax.T)
         val unification = {q = query, qvars = tmset []}
         val expected = [3, 4, 2, 1]
       in
         match query net = expected andalso
         unify unification net = expected andalso
         unifyMeasured (fn () => ()) unification net = expected
       end)

(* Isabelle keys an abstraction as a wildcard in [Pure/net.ML] "to cover
   eta-conversion", and the engines here need the same rule: blast's
   [wkNorm] contracts [!z. p /\ z] to [$! ($/\ p)], and the stored
   [!y. P y] of an elimination has to be offered for that shape. *)
val _ =
  test
    ("clasetNet offers an abstraction key to an eta-contracted query",
     fn () =>
       let
         val predicate = ``P : bool -> bool``
         val net = one ``!z : bool. (P : bool -> bool) z`` (tmset [predicate])
         val contracted =
           rhs (concl (Conv.RAND_CONV Drule.ETA_CONV ``!z : bool. p /\ z``))
       in
         mem 1 (match contracted net) andalso
         mem 1 (unify {q = contracted, qvars = tmset []} net)
       end)

val _ =
  test
    ("clasetNet keeps non-pattern free variables rigid",
     fn () =>
       mem 1 (match x (one x (tmset [])))
       andalso not (mem 1 (match p (one x (tmset [])))))

val _ =
  test
    ("clasetNet vfilter deletes values from every subnet",
     fn () =>
       let
         val net =
           insert ({pat = p, patvars = tmset []}, 1)
             (insert ({pat = q, patvars = tmset []}, 2) empty)
         val net' = vfilter (fn i => i <> 1) net
       in
         List.null (match p net') andalso listItems net' = [2]
       end)

(* clasetRules: normalize only the implication spine. *)
fun aconv_thm th1 th2 = Term.aconv (concl th1) (concl th2)

fun thm_prem_conj () =
  let val pq = ``p /\ q``
  in DISCH pq (DISCH r (CONJUNCT1 (ASSUME pq))) end

fun thm_nested_conj () =
  let val pqr = ``(p /\ q) /\ r``
  in DISCH pqr (CONJUNCT1 (CONJUNCT1 (ASSUME pqr))) end

(* A rule whose parameter is stated free, as HOL4 states one and Isabelle
   does not.  Without generalisation the parameter is rigid and the rule
   matches only a goal that spells it [R]. *)
fun thm_free_parameter () =
  let val rxy = ``(R : num -> num -> bool) x y``
  in DISCH rxy (ASSUME rxy) end

val _ =
  test
    ("canonical_rule binds a rule's free parameters",
     fn () =>
       let
         val rule = canonical_rule (thm_free_parameter ())
       in
         List.null (Term.free_vars (concl rule)) andalso
         Term.aconv (concl (Drule.SPEC_ALL rule))
           ``(R : num -> num -> bool) x y ==> R x y``
       end)

val _ =
  test
    ("a free parameter matches a goal that names it otherwise",
     fn () =>
       let
         val {concl = pattern, patvars, ...} =
           canonical_form (thm_free_parameter ())
         val net = insert ({pat = pattern, patvars = patvars}, 1) empty
       in
         match ``(relation : num -> num -> bool) a b`` net = [1]
       end)

val _ =
  test
    ("canonical_rule curries top-level conjunction premises",
     fn () =>
       Term.aconv (concl (Drule.SPEC_ALL (canonical_rule (thm_prem_conj ()))))
         ``p ==> q ==> r ==> p``)

val _ =
  test
    ("canonical_rule recursively curries nested conjunctions",
     fn () =>
       Term.aconv
         (concl (Drule.SPEC_ALL (canonical_rule (thm_nested_conj ()))))
         ``p ==> q ==> r ==> p``)

val _ =
  test
    ("canonical_rule leaves premise-internal binders intact",
     fn () =>
       let
         val P = ``P : bool -> bool``
         val z = ``z : bool``
         val internal = ``!z : bool. P z ==> q``
         val th = DISCH internal (ASSUME internal)
       in
         Term.aconv (concl (Drule.SPEC_ALL (canonical_rule th)))
           ``(!z : bool. P z ==> q) ==> (!z : bool. P z ==> q)``
       end)

(* A rule that quantifies the subject its conclusion is about, which is how
   HOL4 states an induction rule and Isabelle does not. *)
fun thm_universal_conclusion () =
  let
    val y = ``y : bool``
    val universal = ``!z : bool. P z``
  in
    DISCH universal (GEN y (SPEC y (ASSUME universal)))
  end

val _ =
  test
    ("canonical_rule keeps a conclusion's binders",
     fn () =>
       Term.aconv
         (concl (Drule.SPEC_ALL (canonical_rule (thm_universal_conclusion ()))))
         ``(!z : bool. P z) ==> !z. P z``)

val _ =
  test
    ("atomise_conclusion takes a conclusion's binders as the rule's own",
     fn () =>
       Term.aconv
         (concl
            (Drule.SPEC_ALL
               (atomise_conclusion (thm_universal_conclusion ()))))
         ``(!z : bool. P z) ==> P y``)

val _ =
  test
    ("an atomised conclusion matches an atomic goal",
     fn () =>
       let
         val {concl = pattern, patvars, ...} =
           canonical_form (atomise_conclusion (thm_universal_conclusion ()))
         val net = insert ({pat = pattern, patvars = patvars}, 1) empty
       in
         match ``(Q : bool -> bool) a`` net = [1]
       end)

(* The binder the atomisation removes is one the rule's premises never
   mention, so specializing it leaves them where they were: a conclusion
   the move uncovers as an implication is one more premise, and premises
   already there keep their own binders. *)
val _ =
  test
    ("atomise_conclusion leaves the premises alone",
     fn () =>
       let
         val prem = ``!z : bool. P z ==> q``
         val cncl = ``!w : bool. R w``
         val th = DISCH cncl (DISCH prem (ASSUME cncl))
       in
         Term.aconv
           (concl (Drule.SPEC_ALL (atomise_conclusion th)))
           ``(!w : bool. R w) ==> (!z : bool. P z ==> q) ==> R w``
       end)

fun shadowed_outer_rule () =
  let
    val x = ``x : bool``
    val pq = ``p /\ q``
    val quantified = GEN x (DISCH pq (CONJUNCT1 (ASSUME pq)))
  in
    Drule.ADD_ASSUM x quantified
  end

fun shadowed_canonical_rule () =
  let
    val x = ``x : bool``
    val quantified = GEN x (DISCH p (ASSUME p))
  in
    Drule.ADD_ASSUM x quantified
  end

fun shadowed_canonical_elim () =
  let
    val x = ``x : bool``
    val major = ``p /\ q``
    val quantified = GEN x (DISCH major (DISCH r (ASSUME r)))
  in
    Drule.ADD_ASSUM x quantified
  end

(* A forward rule's major premise is its last one, so this rule is already
   canonical even though a premise is a conjunction. *)
fun shadowed_canonical_forward () =
  let
    val x = ``x : bool``
    val major = ``p /\ q``
    val quantified = GEN x (DISCH r (DISCH major (ASSUME major)))
  in
    Drule.ADD_ASSUM x quantified
  end

val _ =
  test
    ("rule preprocessing freshens outer binders away from hypotheses",
     fn () =>
       let
         val th = shadowed_outer_rule ()
         val th' = canonical_rule th
         val spec = {kind = clasetRules.Intro, safe = true, prio = NONE}
       in
         Term.aconv (concl (Drule.SPEC_ALL th')) ``p ==> q ==> p`` andalso
         List.exists (Term.aconv ``x : bool``) (hyp th') andalso
         can (ext_info spec) th andalso
         can (ext_info spec) (shadowed_canonical_rule ())
       end)

val _ =
  test
    ("repeated canonicalization avoids kernel rebuilding for each kind",
     fn () =>
       let
         fun unchanged canonicalize source =
           let
             (* Measured from an already-canonical rule: the first pass
                over a source theorem binds its free parameters. *)
             val th = canonicalize source
             val once = canonicalize th
             val twice = canonicalize once
             fun binder_names theorem =
               map (fst o dest_var) (fst (strip_forall (concl theorem)))
           in
             binder_names once = binder_names th andalso
             binder_names twice = binder_names once andalso
             Term.aconv (concl twice) (concl th) andalso
             same_terms (hyp twice) (hyp th)
           end
       in
         unchanged canonical_rule (shadowed_canonical_rule ()) andalso
         unchanged (canonical_rule_of clasetRules.Elim)
           (shadowed_canonical_elim ()) andalso
         unchanged (canonical_rule_of clasetRules.Forward)
           (shadowed_canonical_forward ())
       end)

val _ =
  test
    ("canonical_form records outer quantified variables as patvars",
     fn () =>
       let
         val z = ``z : bool``
         val P = ``P : bool -> bool``
         val Pz = mk_comb (P, z)
         val th = GEN z (DISCH Pz (ASSUME Pz))
         val form = canonical_form th
       in
         HOLset.member (#patvars form, z) andalso
         Term.aconv (#concl form) Pz
       end)

val _ =
  test
    ("elimination canonicalization preserves a conjunctive major premise",
     fn () =>
       let
         val spec =
           {kind = clasetRules.Elim, safe = true, prio = NONE}
         val theorem = clasetSeedTheory.CONJ_ELIM_THM
         val processed = #1 (#rl (ext_info spec theorem))
       in
         Term.aconv
           (rule_index clasetRules.Elim processed) ``p /\ q`` andalso
         subgoals_of (true, processed) = 1
       end)

val _ =
  test
    ("elimination canonicalization still curries conjunctive side premises",
     fn () =>
       let
         val major = ``p /\ q``
         val side = ``q /\ r``
         val theorem =
           DISCH major
             (DISCH side (CONJUNCT1 (ASSUME major)))
       in
         Term.aconv
           (concl
             (Drule.SPEC_ALL (canonical_rule_of clasetRules.Elim theorem)))
           ``p /\ q ==> q ==> r ==> p``
       end)

val _ =
  test
    ("rule_index rejects premise-free elimination rules",
     fn () =>
       not (can (rule_index clasetRules.Elim) boolTheory.TRUTH))

val _ =
  test
    ("forward rules index their last immediate premise",
     fn () =>
       let
         val theorem =
           DISCH p
             (DISCH q
               (CONJ (ASSUME p) (ASSUME q)))
       in
         Term.aconv
           (rule_index clasetRules.Forward theorem) q
       end)

(* The major premise a forward rule keeps intact is the last one, so a
   conjunctive earlier premise must still be curried: the safe phase has
   already split such an assumption apart. *)
val _ =
  test
    ("forward canonicalization curries every non-major premise",
     fn () =>
       let
         val major = ``q /\ r``
         val side = ``p /\ q``
         val theorem =
           DISCH side (DISCH major (CONJUNCT1 (ASSUME major)))
         val processed = canonical_rule_of clasetRules.Forward theorem
         val form = canonical_form_of clasetRules.Forward theorem
         val measured =
           canonical_form_of_measured (fn () => ())
             clasetRules.Forward theorem
       in
         Term.aconv (concl (Drule.SPEC_ALL processed))
           ``p ==> q ==> q /\ r ==> q`` andalso
         same_terms (#prems form) [p, q, major] andalso
         Term.aconv (rule_index clasetRules.Forward theorem) major
           andalso
         Term.aconv (concl (#thm measured)) (concl processed) andalso
         same_terms (#prems measured) (#prems form)
       end)

fun info_of th = {rl = (th, NONE), dup_rl = (th, NONE)}
val safe_intro = {kind = clasetRules.Intro, safe = true, prio = NONE}
val safe_elim = {kind = clasetRules.Elim, safe = true, prio = NONE}

fun decl name spec th =
  make_decl {name = name, spec = spec, weight = 1,
             info = info_of th, orig = th}

fun add d ds =
  case extend_decl d ds of
      (SOME _, ds') => ds'
    | (NONE, _) => raise Fail "test declaration unexpectedly rejected"

(* Four distinct propositions.  Rules differing only in the name of a
   parameter are the same rule once the parameter is bound. *)
val decl_a = decl "a" safe_intro (DISCH p (ASSUME p))
val decl_b = decl "b" safe_intro (DISCH p (DISCH q (ASSUME p)))
val decl_c =
  decl "c" safe_elim
    (DISCH ``p /\ q`` (CONJUNCT1 (ASSUME ``p /\ q``)))
val decl_d = decl "d" safe_intro (DISCH ``p /\ q`` (ASSUME ``p /\ q``))

val _ =
  test
    ("decls use decreasing indices and remove by declaration name",
     fn () =>
       let
         val ds = add decl_b (add decl_a empty_decls)
         val names = map #name (dest_decls ds)
         val (removed, ds') = remove_decl "a" ds
       in
         names = ["b", "a"] andalso map #name removed = ["a"] andalso
         map #name (dest_decls ds') = ["b"]
       end)

val _ =
  test
    ("merge_decls replays Bires merge order by kind-class and reverse index",
     fn () =>
       let
         val left = add decl_a empty_decls
         val right = add decl_d (add decl_c (add decl_b empty_decls))
         val (fresh, merged) = merge_decls (left, right)
         val fresh_names = map #name fresh
         val merged_names = map #name (dest_decls merged)
       in
         fresh_names = ["b", "d", "c"] andalso
         merged_names = ["d", "b", "a", "c"]
       end)

val _ =
  test
    ("merge_decls preserves kind order when a reservation reuses an index",
     Feedback.quiet_warnings (fn () =>
       let
         val unsafe = {kind = clasetRules.Intro, safe = false, prio = NONE}
         val other = decl "unsafe_a" unsafe (#orig decl_a)
         val (_, reused) = reserve_decl_indices ~1 (add decl_a empty_decls)
         val right = add other reused
         val (fresh, _) = merge_decls (empty_decls, right)
       in
         map #name fresh = ["a", "unsafe_a"]
       end))

val _ =
  test
    ("dest_decls appends Forward and Norm after classical rule groups",
     fn () =>
       let
         fun order_decl (name, kind, safe) =
           let val theorem = ASSUME (mk_var (name, bool))
           in
             decl name {kind = kind, safe = safe, prio = NONE} theorem
           end
         val declarations =
           [("safe_intro", clasetRules.Intro, true),
            ("safe_elim", clasetRules.Elim, true),
            ("safe_dest", clasetRules.Dest, true),
            ("unsafe_intro", clasetRules.Intro, false),
            ("unsafe_elim", clasetRules.Elim, false),
            ("unsafe_dest", clasetRules.Dest, false),
            ("safe_forward_old", clasetRules.Forward, true),
            ("safe_forward_new", clasetRules.Forward, true),
            ("unsafe_forward", clasetRules.Forward, false),
            ("safe_norm", clasetRules.Norm, true),
            ("unsafe_norm_old", clasetRules.Norm, false),
            ("unsafe_norm_new", clasetRules.Norm, false)]
         val ds =
           List.foldl
             (fn (entry, acc) => add (order_decl entry) acc)
             empty_decls declarations
       in
         map #name (dest_decls ds) =
           ["safe_intro", "safe_elim", "safe_dest",
            "unsafe_intro", "unsafe_elim", "unsafe_dest",
            "safe_forward_new", "safe_forward_old", "unsafe_forward",
            "safe_norm", "unsafe_norm_new", "unsafe_norm_old"]
       end)

val _ =
  test
    ("safe rule classes agree with canonical premise counts",
     fn () =>
       let
         fun check (kind, term) =
           let
             val theorem = ASSUME term
             val rl = (theorem, NONE)
             val elim = kind <> clasetRules.Intro
             val expected =
               if subgoals_of (elim, theorem) = 0 then Safe0 else SafeP
           in
             safe_class_of {kind = kind, safe = true, prio = NONE}
               {rl = rl, dup_rl = rl} = SOME expected
           end
         val terms =
           [``p : bool``, ``~p``, ``!x. P x ==> ~Q x``,
            ``p /\ q ==> r``, ``p /\ q ==> r /\ s ==> t``,
            ``!x. P x ==> !y. Q x y``]
       in
         List.all
           (fn kind => List.all (fn term => check (kind, term)) terms)
           [clasetRules.Intro, clasetRules.Elim, clasetRules.Dest]
       end)

val _ =
  test
    ("candidate_order prefers fewer subgoals, then recent declarations",
     fn () =>
       let
         val th = thm_prem_conj ()
         val ordered = candidate_order
           [({weight = 2, index = ~1}, (false, th)),
            ({weight = 1, index = ~1}, (false, th)),
            ({weight = 1, index = ~3}, (false, th))]
       in
         map (fn ({index, ...}, _) => index) ordered = [~3, ~1, ~1]
       end)

fun same_spec ({kind = kind1, safe = safe1, prio = prio1} : rulespec)
              ({kind = kind2, safe = safe2, prio = prio2} : rulespec) =
  kind1 = kind2 andalso safe1 = safe2 andalso prio1 = prio2

val _ =
  test
    ("claset delta codec round-trips every rule kind",
     fn () =>
       let
         val name = {Thy = "bool", Name = "AND_IMP_INTRO"}
         val specs =
           [{kind = clasetRules.Intro, safe = false, prio = SOME 100},
            {kind = clasetRules.Elim, safe = false, prio = SOME 50},
            {kind = clasetRules.Dest, safe = false, prio = SOME 1},
            {kind = clasetRules.Forward, safe = false, prio = SOME 75},
            {kind = clasetRules.Norm, safe = false, prio = SOME ~17},
            {kind = clasetRules.Norm, safe = true, prio = SOME 23}]
         fun round_trip spec =
           case decode_delta
                  (encode_delta
                     (ADD (look_up {name = name, spec = spec}))) of
               SOME (ADD (Found (name', spec', _))) =>
                 name = name' andalso same_spec spec spec'
             | _ => false
         val missing_name = {Thy = "bool", Name = "no_such_theorem_c2"}
         fun missing_round_trip spec =
           case decode_delta
                  (encode_delta (ADD (Missing (missing_name, spec)))) of
               SOME (ADD (Missing (name', spec'))) =>
                 name' = missing_name andalso same_spec spec spec'
             | _ => false
       in
         List.all round_trip specs andalso
         List.all missing_round_trip specs andalso
         (case decode_delta (encode_delta (RM "gone")) of
             SOME (RM "gone") => true
           | _ => false)
       end)

val _ =
  test
    ("claset ADD deltas load their theorem by name and check liveness",
     fn () =>
       let
         val name = {Thy = "bool", Name = "AND_IMP_INTRO"}
         val spec = {kind = clasetRules.Intro, safe = true, prio = NONE}
       in
         (case take_looked_up (look_up {name = name, spec = spec}) of
             SOME (name', spec', th) =>
               name = name' andalso same_spec spec spec' andalso
               aconv_thm th boolTheory.AND_IMP_INTRO
           | NONE => false)
         andalso
         uptodate_delta (ADD (look_up {name = name, spec = spec}))
       end)

(* The missing-theorem warning fires when the addition is applied, never
   when the delta is decoded. *)
val _ =
  test
    ("a claset ADD naming no theorem warns when applied, not at decode",
     fn () =>
       let
         val name = {Thy = "bool", Name = "no_such_theorem_c2"}
         val spec = {kind = clasetRules.Intro, safe = false, prio = NONE}
         val sexp =
           encode_delta (ADD (look_up {name = name, spec = spec}))
         val decoded = ref NONE
         val decode_warnings =
           capture_warnings (fn () => decoded := decode_delta sexp)
         val taken = ref (SOME ())
         val apply_warnings =
           capture_warnings
             (fn () =>
                taken :=
                  (case !decoded of
                       SOME (ADD addition) =>
                         Option.map (fn _ => ()) (take_looked_up addition)
                     | _ => SOME ()))
       in
         null decode_warnings andalso not (Option.isSome (!taken)) andalso
         length apply_warnings = 1 andalso
         String.isSubstring "load_delta" (hd apply_warnings) andalso
         String.isSubstring "Bad claset add command, dropping theorem"
           (hd apply_warnings) andalso
         String.isSubstring "no_such_theorem_c2" (hd apply_warnings)
       end)


(* clasetRules: primitive preprocessing derived rules. *)
fun same_thm th1 th2 = Term.aconv (concl th1) (concl th2)

val _ =
  test
    ("Forward and Norm ext_info retain only their canonical core forms",
     fn () =>
       let
         val forward = DISCH p (ASSUME p)
         val forward_expected =
           MAKE_ELIM_RULE
             (canonical_rule_of clasetRules.Forward forward)
         val norm = boolTheory.AND_INTRO_THM
         val norm_expected = canonical_rule_of clasetRules.Norm norm
         val forward_specs =
           [{kind = clasetRules.Forward, safe = true, prio = NONE},
            {kind = clasetRules.Forward, safe = false, prio = SOME 75}]
         val norm_specs =
           [{kind = clasetRules.Norm, safe = true, prio = SOME ~1},
            {kind = clasetRules.Norm, safe = false, prio = SOME 2}]
         fun plain_info expected spec =
           let
             val info = ext_info spec
               (if #kind spec = clasetRules.Forward then forward else norm)
             val (main, swapped) = #rl info
             val (dup, dup_swapped) = #dup_rl info
           in
             aconv_thm main expected andalso aconv_thm dup expected andalso
             not (Option.isSome swapped) andalso
             not (Option.isSome dup_swapped) andalso
             safe_class_of spec info = NONE
           end
       in
         List.all (plain_info forward_expected) forward_specs andalso
         List.all (plain_info norm_expected) norm_specs
       end)

fun specs [] th = th
  | specs (tm :: tms) th = specs tms (SPEC tm th)

fun contradiction not_tm tm_th = MP (NOT_ELIM not_tm) tm_th

fun injD_analogue () =
  let
    val inj = ``\f : bool -> bool. !x : bool y : bool.
                 f x = f y ==> x = y``
    val f = ``f : bool -> bool``
    val x = ``x : bool``
    val y = ``y : bool``
    val injf = mk_comb (inj, f)
    val injf_th = EQ_MP (BETA_CONV injf) (ASSUME injf)
    val inst = specs [x, y] injf_th
    val (fxy, xeqy) = dest_imp (concl inst)
    val xeqy_th = MP inst (ASSUME fxy)
  in
    GENL [f, x, y] (DISCH injf (DISCH fxy xeqy_th))
  end

fun repaired_inj_elim () =
  let
    val f = ``f : bool -> bool``
    val x = ``x : bool``
    val y = ``y : bool``
    val r = ``r : bool``
    val source = specs [f, x, y] (injD_analogue ())
    val (injf, tail) = dest_imp (concl source)
    val (fxy, xeqy) = dest_imp tail
    val notr = mk_neg r
    val hfxy = ASSUME (mk_imp (notr, fxy))
    val hkr = ASSUME (mk_imp (xeqy, r))
    val negative =
      MP hkr
        (MP (MP source (ASSUME injf)) (MP hfxy (ASSUME notr)))
    val body =
      DISJ_CASES (SPEC r boolTheory.EXCLUDED_MIDDLE) (ASSUME r) negative
  in
    GENL [f, x, y, r]
      (DISCH injf (DISCH (mk_imp (notr, fxy))
        (DISCH (mk_imp (xeqy, r)) body)))
  end

val _ = test ("injD analogue is locally proved", fn () =>
  (injD_analogue (); true))

val _ =
  test
    ("dest declarations make and classically repair the injD analogue",
     fn () =>
       let
         val spec = {kind = clasetRules.Dest, safe = true, prio = NONE}
         val expected = repaired_inj_elim ()
         val info = ext_info spec (injD_analogue ())
       in
         same_thm (#1 (#rl info)) expected
       end)

fun hand_swap_and () =
  let
    val p = ``p : bool``
    val q = ``q : bool``
    val r = ``r : bool``
    val pq = mk_conj (p, q)
    val notpq = mk_neg pq
    val notr = mk_neg r
    val hp = ASSUME (mk_imp (notr, p))
    val hq = ASSUME (mk_imp (notr, q))
    val body =
      CCONTR r (contradiction (ASSUME notpq)
        (CONJ (MP hp (ASSUME notr)) (MP hq (ASSUME notr))))
  in
    GENL [p, q, r]
      (DISCH notpq (DISCH (mk_imp (notr, p))
        (DISCH (mk_imp (notr, q)) body)))
  end

fun hand_dup_and () =
  let
    val p = ``p : bool``
    val q = ``q : bool``
    val pq = mk_conj (p, q)
    val notpq = mk_neg pq
    val hp = ASSUME (mk_imp (notpq, p))
    val hq = ASSUME (mk_imp (notpq, q))
    val negative =
      CONJ (MP hp (ASSUME notpq)) (MP hq (ASSUME notpq))
    val body =
      DISJ_CASES (SPEC pq boolTheory.EXCLUDED_MIDDLE) (ASSUME pq) negative
  in
    GENL [p, q]
      (DISCH (mk_imp (notpq, p)) (DISCH (mk_imp (notpq, q)) body))
  end

fun cdisj_intro () =
  let
    val p = ``p : bool``
    val q = ``q : bool``
    val notq = mk_neg q
    val h = ASSUME (mk_imp (notq, p))
    val body =
      DISJ_CASES (SPEC q boolTheory.EXCLUDED_MIDDLE)
        (DISJ2 p (ASSUME q)) (DISJ1 (MP h (ASSUME notq)) q)
  in
    GENL [p, q] (DISCH (mk_imp (notq, p)) body)
  end

fun cdisj_from h =
  let
    val p = ``p : bool``
    val q = ``q : bool``
    val notq = mk_neg q
  in
    DISJ_CASES (SPEC q boolTheory.EXCLUDED_MIDDLE)
      (DISJ2 p (ASSUME q)) (DISJ1 (MP h (ASSUME notq)) q)
  end

fun hand_swap_cdisj () =
  let
    val p = ``p : bool``
    val q = ``q : bool``
    val r = ``r : bool``
    val c = mk_disj (p, q)
    val notc = mk_neg c
    val notr = mk_neg r
    val h = ASSUME (mk_imp (notr, mk_imp (mk_neg q, p)))
    val body =
      CCONTR r (contradiction (ASSUME notc)
        (cdisj_from (MP h (ASSUME notr))))
  in
    GENL [p, q, r]
      (DISCH notc (DISCH (mk_imp (notr, mk_imp (mk_neg q, p))) body))
  end

fun hand_dup_cdisj () =
  let
    val p = ``p : bool``
    val q = ``q : bool``
    val c = mk_disj (p, q)
    val notc = mk_neg c
    val h = ASSUME (mk_imp (notc, mk_imp (mk_neg q, p)))
    val negative = cdisj_from (MP h (ASSUME notc))
    val body =
      DISJ_CASES (SPEC c boolTheory.EXCLUDED_MIDDLE) (ASSUME c) negative
  in
    GENL [p, q] (DISCH (mk_imp (notc, mk_imp (mk_neg q, p))) body)
  end

fun exists_intro () =
  let
    val P = ``P : bool -> bool``
    val x = ``x : bool``
    val px = mk_comb (P, x)
    val ex = mk_exists (x, px)
  in
    GENL [P, x] (DISCH px (EXISTS (ex, x) (ASSUME px)))
  end

fun hand_swap_exists () =
  let
    val P = ``P : bool -> bool``
    val x = ``x : bool``
    val r = ``r : bool``
    val px = mk_comb (P, x)
    val ex = mk_exists (x, px)
    val notex = mk_neg ex
    val notr = mk_neg r
    val hp = ASSUME (mk_imp (notr, px))
    val body =
      CCONTR r (contradiction (ASSUME notex)
        (EXISTS (ex, x) (MP hp (ASSUME notr))))
  in
    GENL [P, x, r]
      (DISCH notex (DISCH (mk_imp (notr, px)) body))
  end

fun hand_dup_exists () =
  let
    val P = ``P : bool -> bool``
    val x = ``x : bool``
    val px = mk_comb (P, x)
    val ex = mk_exists (x, px)
    val notex = mk_neg ex
    val hp = ASSUME (mk_imp (notex, px))
    val negative = EXISTS (ex, x) (MP hp (ASSUME notex))
    val body =
      DISJ_CASES (SPEC ex boolTheory.EXCLUDED_MIDDLE) (ASSUME ex) negative
  in
    GENL [P, x] (DISCH (mk_imp (notex, px)) body)
  end

val _ =
  test
    ("swap and duplication rules agree with hand proofs for seed intros",
     fn () =>
       let
         val and_intro = boolTheory.AND_INTRO_THM
         val disj_intro = cdisj_intro ()
         val ex_intro = exists_intro ()
       in
         Option.isSome (SWAP_INTRO_RULE and_intro) andalso
         same_thm (Option.valOf (SWAP_INTRO_RULE and_intro))
           (hand_swap_and ()) andalso
         same_thm (DUP_INTRO_RULE and_intro) (hand_dup_and ()) andalso
         Option.isSome (SWAP_INTRO_RULE disj_intro) andalso
         same_thm (Option.valOf (SWAP_INTRO_RULE disj_intro))
           (hand_swap_cdisj ()) andalso
         same_thm (DUP_INTRO_RULE disj_intro) (hand_dup_cdisj ()) andalso
         Option.isSome (SWAP_INTRO_RULE ex_intro) andalso
         same_thm (Option.valOf (SWAP_INTRO_RULE ex_intro))
           (hand_swap_exists ()) andalso
         same_thm (DUP_INTRO_RULE ex_intro) (hand_dup_exists ())
       end)

fun no_swap NONE = true
  | no_swap _ = false

val _ =
  test
    ("swap declines negation-headed conclusions",
     fn () =>
       let
         val negp = mk_neg p
         val neg_intro = GEN p (DISCH negp (ASSUME negp))
       in
         no_swap (SWAP_INTRO_RULE neg_intro)
       end)

val _ =
  test
    ("swap retains the classical form of negation introduction",
     fn () =>
       case SWAP_INTRO_RULE boolTheory.IMP_F of
           NONE => false
         | SOME theorem =>
             case strip_forall (concl theorem) of
                 ([t, r], body) =>
                   (case strip_imp_only body of
                        ([double_neg_t, lifted], result) =>
                          aconv double_neg_t (mk_neg (mk_neg t)) andalso
                          aconv lifted
                            (mk_imp
                              (mk_neg r, mk_imp (t, boolSyntax.F))) andalso
                          aconv result r
                      | _ => false)
               | _ => false)

val _ =
  test
    ("swap declines variable-headed conclusions",
     fn () =>
       let val var_intro = GEN p (DISCH p (ASSUME p))
       in no_swap (SWAP_INTRO_RULE var_intro) end)

fun simple_elim () =
  let
    val p = ``p : bool``
    val q = ``q : bool``
    val hp = ASSUME p
    val hpq = ASSUME (mk_imp (p, q))
  in
    GENL [p, q] (DISCH p (DISCH (mk_imp (p, q)) (MP hpq hp)))
  end

fun hand_dup_elim () =
  let
    val p = ``p : bool``
    val q = ``q : bool``
    val hp = ASSUME p
    val h = ASSUME (mk_imp (p, mk_imp (p, q)))
  in
    GENL [p, q]
      (DISCH p (DISCH (mk_imp (p, mk_imp (p, q))) (MP (MP h hp) hp)))
  end

val _ =
  test
    ("DUP_ELIM_RULE retains the major premise in every side premise",
     fn () => same_thm (DUP_ELIM_RULE (simple_elim ())) (hand_dup_elim ()))

fun hand_rev_conj_elim () =
  let
    val p = ``p : bool``
    val q = ``q : bool``
    val r = ``r : bool``
    val major = mk_conj (p, q)
    val hmajor = ASSUME major
    val minor =
      mk_imp (p, mk_imp (q, mk_imp (major, r)))
    val hminor = ASSUME minor
    val body =
      MP (MP (MP hminor (CONJUNCT1 hmajor)) (CONJUNCT2 hmajor))
        hmajor
  in
    GENL [p, q, r] (DISCH major (DISCH minor body))
  end

fun hand_rev_disj_elim () =
  let
    val p = ``p : bool``
    val q = ``q : bool``
    val r = ``r : bool``
    val major = mk_disj (p, q)
    val hmajor = ASSUME major
    val left = mk_imp (p, mk_imp (major, r))
    val right = mk_imp (q, mk_imp (major, r))
    val hleft = ASSUME left
    val hright = ASSUME right
    val body =
      DISJ_CASES hmajor
        (MP (MP hleft (ASSUME p)) hmajor)
        (MP (MP hright (ASSUME q)) hmajor)
  in
    GENL [r, p, q]
      (DISCH major (DISCH left (DISCH right body)))
  end

fun hand_rev_exists_elim () =
  let
    val P = ``P : bool -> bool``
    val x = ``x : bool``
    val q = ``q : bool``
    val px = mk_comb (P, x)
    val major = mk_exists (x, px)
    val hmajor = ASSUME major
    val minor =
      mk_forall (x, mk_imp (px, mk_imp (major, q)))
    val hminor = ASSUME minor
    val branch = MP (MP (SPEC x hminor) (ASSUME px)) hmajor
    val body = CHOOSE (x, hmajor) branch
  in
    (* [P] is a free parameter of the specialised input, so the rule binds
       it ahead of the theorem's own binders. *)
    GENL [P, q] (DISCH major (DISCH minor body))
  end

val _ =
  test
    ("REV_DUP_ELIM_RULE has the exact conjunction-elim output",
     fn () =>
       same_thm (REV_DUP_ELIM_RULE clasetSeedTheory.CONJ_ELIM_THM)
         (hand_rev_conj_elim ()))

val _ =
  test
    ("REV_DUP_ELIM_RULE has the exact disjunction-elim output",
     fn () =>
       same_thm (REV_DUP_ELIM_RULE boolTheory.OR_ELIM_THM)
         (hand_rev_disj_elim ()))

val _ =
  test
    ("REV_DUP_ELIM_RULE has the exact exists-elim output",
     fn () =>
       let
         val P = ``P : bool -> bool``
         val exists_elim =
           Drule.ISPEC P clasetSeedTheory.EXISTS_ELIM_THM
       in
         same_thm (REV_DUP_ELIM_RULE exists_elim)
           (hand_rev_exists_elim ())
       end)

fun shadowed_minor_elim () =
  let
    val P = ``P : bool -> bool``
    val x = ``x : bool``
    val r = ``r : bool``
    val major = mk_comb (P, x)
    val minor = mk_forall (x, mk_imp (mk_comb (P, x), r))
    val body = MP (SPEC x (ASSUME minor)) (ASSUME major)
  in
    GENL [P, x, r] (DISCH major (DISCH minor body))
  end

val _ =
  test
    ("reverse elim duplication avoids capturing the major premise",
     fn () =>
       let
         val theorem = REV_DUP_ELIM_RULE (shadowed_minor_elim ())
       in
         case rule_premises_of clasetRules.Elim theorem of
             [major, minor] =>
               let
                 val (bound, body) = dest_forall minor
                 val (added, _) = strip_imp_only body
               in
                 not (free_in bound major) andalso
                 length added = 2 andalso
                 Term.aconv (List.last added) major
               end
           | _ => false
       end)

(* An engine discharges a minor premise's outer !-prefix and the
   implication chain below it, and leaves any further quantified premise
   standing in the conclusion.  The duplicate belongs at the end of that
   discharged prefix: pushed inside the standing premise it never reaches
   the assumptions at all. *)
fun inner_quantifier_elim () =
  let
    val P = ``P : 'a -> bool``
    val r = ``r : bool``
    val x = ``x : 'a``
    val universal = mk_forall (x, mk_comb (P, x))
    val major = mk_neg universal
    val minor = mk_imp (mk_neg r, universal)
    val witness =
      MP (NOT_ELIM (ASSUME major)) (MP (ASSUME minor) (ASSUME (mk_neg r)))
  in
    GENL [P, r] (DISCH major (DISCH minor (CCONTR r witness)))
  end

val _ =
  test
    ("reverse elim duplication stops above a premise's inner quantifier",
     fn () =>
       let
         val P = ``P : 'a -> bool``
         val r = ``r : bool``
         val x = ``x : 'a``
         val universal = mk_forall (x, mk_comb (P, x))
         val major = mk_neg universal
         val expected = mk_imp (mk_neg r, mk_imp (major, universal))
       in
         same_terms
           (rule_premises_of clasetRules.Elim
             (REV_DUP_ELIM_RULE (inner_quantifier_elim ())))
           [major, expected]
       end)

val _ =
  test
    ("reverse and ordinary elim duplication order hypotheses differently",
     fn () =>
       let
         val p = ``p : bool``
         val q = ``q : bool``
         val r = ``r : bool``
         val major = mk_conj (p, q)
         val rev_minor =
           mk_imp (p, mk_imp (q, mk_imp (major, r)))
         val dup_minor =
           mk_imp (major, mk_imp (p, mk_imp (q, r)))
         val rev_prems =
           rule_premises_of clasetRules.Elim
             (REV_DUP_ELIM_RULE clasetSeedTheory.CONJ_ELIM_THM)
         val dup_prems =
           rule_premises_of clasetRules.Elim
             (DUP_ELIM_RULE clasetSeedTheory.CONJ_ELIM_THM)
       in
         same_terms rev_prems [major, rev_minor] andalso
         same_terms dup_prems [major, dup_minor] andalso
         not (same_terms rev_prems dup_prems)
       end)

fun hol_err_msg f =
  (f (); NONE) handle HOL_ERR e => SOME (Feedback.message_of e)

val _ =
  test
    ("reverse elim duplication handles no-op and failure edges",
     fn () =>
       let
         val false_elim = canonical_rule_of clasetRules.Elim
           boolTheory.FALSITY
         val once = REV_DUP_ELIM_RULE boolTheory.FALSITY
       in
         same_thm once false_elim andalso
         same_thm (REV_DUP_ELIM_RULE once) once andalso
         hol_err_msg
           (fn () => (REV_DUP_ELIM_RULE boolTheory.TRUTH; ())) =
           SOME "Ill-formed elimination rule"
       end)

(* The classical form adds the negated conclusion to a minor premise only
   where it adds something, and a premise that already concludes the rule's
   conclusion gets nothing.  That conclusion sits under the premise's
   parameters as well as under its own antecedents, so [!x. P x ==> q]
   concludes [q]; reading it as concluding itself decorates every rule with
   an eigenvariable, and each such step then puts one more copy of the
   negated goal among the assumptions for the search to carry. *)
val _ =
  test
    ("the classical form leaves a parameterised minor premise alone",
     fn () =>
       let
         val transfer =
           let
             val (a, b, w) =
               (mk_var ("a", bool), mk_var ("b", bool), mk_var ("w", bool))
             val hb = EQ_MP (ASSUME (mk_eq (a, b))) (ASSUME a)
             val body = MP (ASSUME (mk_imp (b, w))) hb
           in
             GENL [a, b, w]
               (DISCH (mk_eq (a, b))
                 (DISCH a (DISCH (mk_imp (b, w)) body)))
           end
         fun adds_negation th =
           List.exists
             (fn prem =>
               case total dest_imp_only prem of
                   SOME (ante, _) => is_neg ante
                 | NONE => false)
             (rule_premises_of clasetRules.Elim (CLASSICAL_RULE th))
       in
         not (adds_negation EXISTS_ELIM_THM) andalso
         same_thm (CLASSICAL_RULE EXISTS_ELIM_THM)
           (canonical_rule_of clasetRules.Elim EXISTS_ELIM_THM) andalso
         adds_negation transfer
       end)

val _ =
  test
    ("ext_info rejects premise-free eliminations and classifies safe rules",
     fn () =>
       let
         val safe_elim = {kind = clasetRules.Elim, safe = true, prio = NONE}
         val safe0 = ext_info safe_elim boolTheory.FALSITY
         val safep = ext_info safe_elim boolTheory.OR_ELIM_THM
       in
         same_thm (CLASSICAL_RULE boolTheory.FALSITY)
           (canonical_rule boolTheory.FALSITY) andalso
         hol_err_msg (fn () => (ext_info safe_elim boolTheory.TRUTH; ())) =
           SOME "Ill-formed elimination rule" andalso
         safe_class_of safe_elim safe0 = SOME Safe0 andalso
         safe_class_of safe_elim safep = SOME SafeP
       end)

val _ =
  test
    ("duplicate and cross-kind declarations warn as appropriate",
     fn () =>
       let
         val th = DISCH p (ASSUME p)
         val first = decl "duplicate-one" safe_intro th
         val second = decl "duplicate-two" safe_intro th
         val other = decl "cross-kind" safe_elim th
         val (one, ds) = extend_decl first empty_decls
         val (two, ds') = extend_decl second ds
         val (three, ds'') = extend_decl other ds'
       in
         Option.isSome one andalso not (Option.isSome two) andalso
         Option.isSome three andalso length (dest_decls ds'') = 2
       end)


(* clasetLib: value operations and netpair lookup. *)
fun has_thm th = List.exists (fn (_, (_, th')) => same_thm th th')

val _ =
  test
    ("rules_of preserves a conjunctive elimination major premise",
     fn () =>
       let
         val cs =
           add_selims
             [("conjunction-elim", clasetSeedTheory.CONJ_ELIM_THM)]
             empty_cs
       in
         case rules_of cs of
             [({kind = clasetRules.Elim, ...}, (_, theorem))] =>
               Term.aconv
                 (rule_index clasetRules.Elim theorem) ``p /\ q``
           | _ => false
       end)

val _ =
  test
    ("clasetLib routes safe zero- and positive-subgoal rules",
     fn () =>
       let
         val cs =
           add_selims [("falseE", boolTheory.FALSITY)]
             (add_sintros [("truthI", boolTheory.TRUTH)]
                (add_selims [("orE", boolTheory.OR_ELIM_THM)]
                   (add_sintros [("andI", boolTheory.AND_INTRO_THM)]
                      empty_cs)))
         val safe0_intro =
           match_intro_candidates (safe0_part cs) ``T``
         val safe0_elim =
           match_elim_candidates (safe0_part cs) ``F``
         val safep_intro =
           match_intro_candidates (safep_part cs) ``p /\ q``
         val safep_elim =
           match_elim_candidates (safep_part cs) ``p \/ q``
       in
         has_thm boolTheory.TRUTH safe0_intro andalso
         has_thm boolTheory.FALSITY safe0_elim andalso
         has_thm boolTheory.AND_INTRO_THM safep_intro andalso
         has_thm boolTheory.OR_ELIM_THM safep_elim
       end)

fun refl_intro vars tm = GENL vars (DISCH tm (ASSUME tm))

(* Six pairwise distinct two-premise intro rules whose conclusion matches
   [p /\ p].  They cannot differ by variable name alone: binding a rule's
   parameters makes name-only variants one rule. *)
val p_imp_q = mk_imp (p, q)
val q_imp_p = mk_imp (q, p)

val intro_pp = DISCH p (DISCH p (CONJ (ASSUME p) (ASSUME p)))
val intro_pq = DISCH p (DISCH q (CONJ (ASSUME p) (ASSUME q)))
val intro_p_then_imp =
  DISCH p (DISCH p_imp_q (CONJ (ASSUME p) (MP (ASSUME p_imp_q) (ASSUME p))))
val intro_imp_then_p =
  DISCH p_imp_q (DISCH p (CONJ (ASSUME p) (MP (ASSUME p_imp_q) (ASSUME p))))
val intro_q_then_imp =
  DISCH q (DISCH q_imp_p (CONJ (MP (ASSUME q_imp_p) (ASSUME q)) (ASSUME q)))
val intro_imp_then_q =
  DISCH q_imp_p (DISCH q (CONJ (MP (ASSUME q_imp_p) (ASSUME q)) (ASSUME q)))

fun candidate_indices candidates =
  map (fn (({index, ...} : tag), _) => index) candidates

fun candidate_weights candidates =
  map (fn (({weight, ...} : tag), _) => weight) candidates

val _ =
  test
    ("clasetLib orders six matching rules by subgoals then recency",
     fn () =>
       let
         val rules =
           [("one", intro_pp),
            ("two", intro_pq),
            ("three", intro_p_then_imp),
            ("four", intro_imp_then_p),
            ("five", intro_q_then_imp),
            ("six", intro_imp_then_q)]
         val cs = add_intros rules empty_cs
         val candidates =
           match_intro_candidates (unsafe_part cs) ``p /\ p``
       in
         candidate_weights candidates = [2, 2, 2, 2, 2, 2] andalso
         candidate_indices candidates = [~11, ~9, ~7, ~5, ~3, ~1]
       end)

val _ =
  test
    ("clasetLib routes swapped intros to elimination lookup",
     fn () =>
       let
         val cs = add_intros [("andI", boolTheory.AND_INTRO_THM)] empty_cs
         val swapped = Option.valOf (SWAP_INTRO_RULE boolTheory.AND_INTRO_THM)
         val query = ``~(p /\ q)``
         val intros = match_intro_candidates (unsafe_part cs) query
         val elims = match_elim_candidates (unsafe_part cs) query
       in
         List.null intros andalso
         has_thm swapped elims andalso
         List.exists (fn (tag, (is_elim, th)) =>
           is_elim andalso #index tag = ~2 andalso same_thm th swapped) elims
       end)

fun indexed_term (is_elim, th) =
  rule_index (if is_elim then clasetRules.Elim else clasetRules.Intro) th

fun exactly_matches (is_elim, th) query =
  let val {patvars, ...} = canonical_form th
  in really_matches (indexed_term (is_elim, th)) patvars query end

fun same_candidates (cs1 : (tag * brl) list) (cs2 : (tag * brl) list) =
  ListPair.allEq
    (fn ((tag1, brl1), (tag2, brl2)) =>
       #weight tag1 = #weight tag2 andalso #index tag1 = #index tag2 andalso
       #1 brl1 = #1 brl2 andalso same_thm (#2 brl1) (#2 brl2))
    (cs1, cs2)

val _ =
  test
    ("Forward and Norm declarations leave all classical netpairs unchanged",
     fn () =>
       let
         val baseline =
           add_elims [("baseline_elim", boolTheory.OR_ELIM_THM)]
             (add_intros [("baseline_intro", boolTheory.AND_INTRO_THM)]
               (add_selims [("baseline_selim", boolTheory.FALSITY)]
                 (add_sintros [("baseline_sintro", boolTheory.TRUTH)]
                   empty_cs)))
         val additions =
           [({kind = clasetRules.Forward, safe = true, prio = NONE},
             ("routing_sforward", DISCH p (ASSUME p))),
            ({kind = clasetRules.Forward, safe = false, prio = SOME 67},
             ("routing_forward", DISCH q (ASSUME q))),
            ({kind = clasetRules.Norm, safe = true, prio = SOME ~4},
             ("routing_snorm", boolTheory.EQ_REFL)),
            ({kind = clasetRules.Norm, safe = false, prio = SOME 9},
             ("routing_norm", boolTheory.IMP_ANTISYM_AX))]
         val extended =
           List.foldl
             (fn ((spec, named_th), cs) => add_rule spec named_th cs)
             baseline additions
         fun observe cs =
           List.concat
             (map
                (fn part =>
                   unify_intro_candidates part x @
                   unify_elim_candidates part x)
                [safe0_part cs, safep_part cs, unsafe_part cs, dup_part cs])
         fun named name (_, (name', _)) = name = name'
       in
         same_candidates (observe baseline) (observe extended) andalso
         List.all
           (fn name => List.exists (named name) (rules_of extended))
           ["routing_sforward", "routing_forward",
            "routing_snorm", "routing_norm"]
       end)

(* The aesop retrievals return declarations with their stored
   canonicalisation; these helpers look only at the identifying fields. *)
fun aesop_pair ({spec, name, thm, ...} : aesop_rule) = (spec, (name, thm))

fun aesop_names rules = map (fn {name, ...} : aesop_rule => name) rules

fun has_aesop_name name rules =
  List.exists (fn {name = name', ...} : aesop_rule => name = name') rules

fun has_aesop_entry expected_spec (expected_name, expected_th) rules =
  List.exists
    (fn {spec, name, thm, ...} : aesop_rule =>
       same_spec spec expected_spec andalso name = expected_name andalso
       same_thm thm expected_th)
    rules

val _ =
  test
    ("aesop index retrieves every indexed rule kind from its designated \
     \side",
     fn () =>
       let
         (* Declared closed, so what the index stores is what was given. *)
         val forward = GEN p (DISCH p (ASSUME p))
         val declarations =
           [({kind = clasetRules.Intro, safe = true, prio = NONE},
             ("aesop_intro", boolTheory.AND_INTRO_THM)),
            ({kind = clasetRules.Elim, safe = false, prio = SOME 60},
             ("aesop_elim", boolTheory.OR_ELIM_THM)),
            ({kind = clasetRules.Dest, safe = true, prio = NONE},
             ("aesop_dest", clasetSeedTheory.CONJ_ELIM_THM)),
            ({kind = clasetRules.Forward, safe = false, prio = SOME 70},
             ("aesop_forward", forward)),
            ({kind = clasetRules.Norm, safe = false, prio = SOME ~2},
             ("aesop_norm", boolTheory.IMP_ANTISYM_AX))]
         val cs =
           List.foldl
             (fn ((spec, named_th), acc) => add_rule spec named_th acc)
             empty_cs declarations
         val empty_vars = tmset []
         val target =
           aesop_target_rules cs
             {q = ``p /\ q``, qvars = empty_vars}
         (* The Norm rule's conclusion; it would be retrieved here if Norm
            were indexed at all. *)
         val norm_shaped =
           aesop_target_rules cs
             {q = ``p = q``, qvars = empty_vars}
         val elim =
           aesop_hyp_rules cs
             {q = ``p \/ q``, qvars = empty_vars}
         val dest =
           aesop_hyp_rules cs
             {q = ``p /\ q``, qvars = empty_vars}
         val forward_candidates =
           aesop_hyp_rules cs {q = p, qvars = empty_vars}
       in
         has_aesop_name "aesop_intro" target andalso
         not (has_aesop_name "aesop_elim" target) andalso
         not (has_aesop_name "aesop_norm" target) andalso
         not (has_aesop_name "aesop_norm" norm_shaped) andalso
         has_aesop_name "aesop_elim" elim andalso
         has_aesop_name "aesop_dest" dest andalso
         has_aesop_entry
           {kind = clasetRules.Forward, safe = false, prio = SOME 70}
           ("aesop_forward", forward) forward_candidates
       end)

val _ =
  test
    ("aesop index treats query metavariables as unification wildcards",
     fn () =>
       let
         val target_cs =
           add_sintros
             [("meta_intro", boolTheory.AND_INTRO_THM)] empty_cs
         val cs =
           add_rule
             {kind = clasetRules.Forward, safe = true, prio = NONE}
             ("meta_forward", DISCH p (ASSUME p))
             (add_elims [("meta_elim", boolTheory.OR_ELIM_THM)] target_cs)
         val query = {q = x, qvars = tmset [x]}
         val targets = aesop_names (aesop_target_rules cs query)
         val hyps = aesop_names (aesop_hyp_rules cs query)
       in
         List.all (fn name => mem name targets) ["meta_intro"] andalso
         List.all (fn name => mem name hyps) ["meta_elim", "meta_forward"]
       end)

fun disj_intro vars left right =
  GENL vars
    (DISCH left
      (DISCH right (DISJ1 (ASSUME left) right)))

(* Distinct single-premise introductions whose conclusion matches
   [p \/ p].  Variants differing only in a variable's name would now be
   one rule. *)
val disj_from_right = DISCH q (DISJ2 p (ASSUME q))
val disj_from_left = DISCH p (DISJ1 (ASSUME p) q)

val _ =
  test
    ("aesop unsafe candidates use percent, weight, and recency order",
     fn () =>
       let
         val high_old = refl_intro [q] ``p \/ q``
         val high_heavy = disj_intro [q] q p
         val high_new = disj_from_right
         val default = disj_from_left
         val declarations =
           [({kind = clasetRules.Intro, safe = false, prio = SOME 25},
             ("low", refl_intro [] ``p \/ p``)),
            ({kind = clasetRules.Intro, safe = false, prio = SOME 75},
             ("high_old", high_old)),
            ({kind = clasetRules.Intro, safe = false, prio = SOME 75},
             ("high_heavy", high_heavy)),
            ({kind = clasetRules.Intro, safe = false, prio = SOME 75},
             ("high_new", high_new)),
            ({kind = clasetRules.Intro, safe = false, prio = NONE},
             ("default", default))]
         val cs =
           List.foldl
             (fn ((spec, named_th), acc) => add_rule spec named_th acc)
             empty_cs declarations
         val names =
           aesop_names
             (aesop_target_rules cs
                {q = ``p \/ p``, qvars = tmset []})
       in
         names =
           ["high_new", "high_old", "high_heavy", "default", "low"]
       end)

val _ =
  test
    ("aesop safe candidates retain their phase order",
     fn () =>
       let
         val safe_declarations =
           [({kind = clasetRules.Intro, safe = true, prio = SOME 100},
             ("safe_heavy", disj_intro [q] q p)),
            ({kind = clasetRules.Intro, safe = true, prio = SOME 1},
             ("safe_old", refl_intro [q] ``p \/ q``)),
            ({kind = clasetRules.Intro, safe = true, prio = NONE},
             ("safe_new", disj_from_right))]
         val cs =
           List.foldl
             (fn ((spec, named_th), acc) => add_rule spec named_th acc)
             empty_cs safe_declarations
         val safe_query = {q = ``p \/ p``, qvars = tmset []}
       in
         aesop_names (aesop_target_rules cs safe_query) =
           ["safe_new", "safe_old", "safe_heavy"]
       end)

(* [norm_rules] is the precomputed equivalent of filtering [rules_of],
   so pin the agreement rather than a hardcoded order: the penalty sort in
   the normalisation phase relies on that incoming order as its tiebreak. *)
val _ =
  test
    ("claset norm declarations agree with filtering rules_of",
     fn () =>
       let
         val norm_declarations =
           [({kind = clasetRules.Norm, safe = false, prio = SOME 4},
             ("norm_late", refl_intro [] ``p /\ p``)),
            ({kind = clasetRules.Norm, safe = false, prio = NONE},
             ("norm_zero", refl_intro [q] ``p /\ q``)),
            ({kind = clasetRules.Norm, safe = false, prio = SOME ~3},
             ("norm_early", intro_pq))]
         fun install cs =
           List.foldl
             (fn ((spec, named_th), acc) => add_rule spec named_th acc)
             cs norm_declarations
         fun expected cs =
           List.filter
             (fn ({kind, ...} : clasetRules.rulespec, _) =>
               kind = clasetRules.Norm)
             (rules_of cs)
         fun agrees cs =
           aesop_names (norm_rules cs) =
           map (fn (_, (name, _)) => name) (expected cs)
         val incremental = install empty_cs
         val merged = merge_cs (empty_cs, incremental)
         val removed = remove_rule "norm_zero" incremental
       in
         agrees incremental andalso agrees merged andalso
         agrees removed andalso
         not (has_aesop_name "norm_zero" (norm_rules removed))
       end)

val _ =
  test
    ("measured candidate FVL preserves a free variable beside its shadow",
     fn () =>
       let
         val rigid =
           ``(P : bool -> (bool -> bool) -> bool) T (\x : bool. x)``
         val rule = ASSUME rigid
         val cs = add_intros [("rigid", rule)] empty_cs
         val query =
           ``(P : bool -> (bool -> bool) -> bool) (x : bool)
               (\x : bool. x)``
         val ordinary = unify_intro_candidates (unsafe_part cs) query
         val polls = ref 0
         val measured =
           unify_intro_candidates_measured
             (fn () => polls := !polls + 1) (unsafe_part cs) query
       in
         !polls > 0 andalso has_thm rule ordinary andalso
         same_candidates ordinary measured
       end)

fun rule_entries index kind (th, swapped) =
  let
    fun entry is_elim index th =
      ({weight = subgoals_of (is_elim, th), index = index},
       (is_elim, th))
  in
    entry (kind <> clasetRules.Intro) (2 * index + 1) th ::
    (case swapped of
         NONE => []
       | SOME th' => [entry true (2 * index) th'])
  end

fun brute_unsafe_entries declarations =
  let
    fun add ((kind, th), (index, entries)) =
      let
        val spec = {kind = kind, safe = false, prio = NONE}
        val info = ext_info spec th
      in
        (index - 1, rule_entries index kind (#rl info) @ entries)
      end
  in
    candidate_order (#2 (List.foldl add (~1, []) declarations))
  end

fun exactly_unifies (is_elim, th) query =
  let
    val {patvars, ...} = canonical_form th
  in
    really_unifies (indexed_term (is_elim, th)) patvars query
      (tmset (free_vars query))
  end

val _ =
  test
    ("clasetLib match introduction candidates agree with brute filtering",
     fn () =>
       let
         val declarations =
           [(clasetRules.Elim, boolTheory.OR_ELIM_THM),
            (clasetRules.Intro, boolTheory.AND_INTRO_THM)]
         val cs =
           add_intros [("andI", boolTheory.AND_INTRO_THM)]
             (add_elims [("orE", boolTheory.OR_ELIM_THM)] empty_cs)
         val entries = brute_unsafe_entries declarations
         val iq = ``p /\ q``
         val eq = ``p \/ q``
         fun matching is_elim query = candidate_order
           (List.filter
             (fn (_, brl) => #1 brl = is_elim andalso
                             exactly_matches brl query) entries)
       in
         same_candidates
           (match_intro_candidates (unsafe_part cs) iq) (matching false iq)
       end)

val _ =
  test
    ("clasetLib match elimination candidates agree with brute filtering",
     fn () =>
       let
         val cs =
           add_intros [("andI", boolTheory.AND_INTRO_THM)]
             (add_elims [("orE", boolTheory.OR_ELIM_THM)] empty_cs)
         val entries = brute_unsafe_entries
           [(clasetRules.Elim, boolTheory.OR_ELIM_THM),
            (clasetRules.Intro, boolTheory.AND_INTRO_THM)]
         val query = ``p \/ q``
         val expected = candidate_order
           (List.filter
             (fn (_, brl) => #1 brl andalso exactly_matches brl query)
             entries)
       in
         same_candidates (match_elim_candidates (unsafe_part cs) query)
           expected
       end)

val _ =
  test
    ("clasetLib unify introduction candidates agree with brute filtering",
     fn () =>
       let
         val cs =
           add_intros [("andI", boolTheory.AND_INTRO_THM)]
             (add_elims [("orE", boolTheory.OR_ELIM_THM)] empty_cs)
         val entries = brute_unsafe_entries
           [(clasetRules.Elim, boolTheory.OR_ELIM_THM),
            (clasetRules.Intro, boolTheory.AND_INTRO_THM)]
         val query = ``p /\ q``
       in
         same_candidates (unify_intro_candidates (unsafe_part cs) query)
           (candidate_order
             (List.filter
               (fn (_, brl) => not (#1 brl) andalso
                               exactly_unifies brl query) entries))
       end)

val _ =
  test
    ("clasetLib unify elimination candidates agree with brute filtering",
     fn () =>
       let
         val cs =
           add_intros [("andI", boolTheory.AND_INTRO_THM)]
             (add_elims [("orE", boolTheory.OR_ELIM_THM)] empty_cs)
         val entries = brute_unsafe_entries
           [(clasetRules.Elim, boolTheory.OR_ELIM_THM),
            (clasetRules.Intro, boolTheory.AND_INTRO_THM)]
         val query = ``p \/ q``
       in
         same_candidates (unify_elim_candidates (unsafe_part cs) query)
           (candidate_order
             (List.filter
               (fn (_, brl) => #1 brl andalso exactly_unifies brl query)
               entries))
       end)

fun same_rules xs ys =
  ListPair.allEq
    (fn ((spec1, (name1, th1)), (spec2, (name2, th2))) =>
       same_spec spec1 spec2 andalso name1 = name2 andalso same_thm th1 th2)
    (xs, ys)

(* The same comparison on the info-carrying retrievals: the stored
   canonicalisation is a function of these fields, so agreeing on them is
   agreeing on the declaration. *)
fun same_aesop_rules xs ys =
  same_rules (map aesop_pair xs) (map aesop_pair ys)

val _ =
  test
    ("clasetLib add, remove, and merge preserve canonical rule order",
     fn () =>
       let
         val a = ("a", DISCH p (ASSUME p))
         val b = ("b", DISCH q (ASSUME q))
         val left =
           add_intros [("andI", boolTheory.AND_INTRO_THM)]
             (add_selims [("falseE", boolTheory.FALSITY)] empty_cs)
         val right =
           add_sintros [a, b]
             (add_selims [("orE", boolTheory.OR_ELIM_THM)] empty_cs)
         val merged = merge_cs (left, right)
         val incremented =
           add_sintros [a, b]
             (add_selims [("orE", boolTheory.OR_ELIM_THM)] left)
         val removed = remove_rule "b" merged
       in
         same_rules (rules_of merged) (rules_of incremented) andalso
         map (fn (_, (name, _)) => name) (rules_of removed) =
           ["a", "falseE", "orE", "andI"]
       end)

val _ =
  test
    ("aesop index follows add, remove, and merge maintenance",
     fn () =>
       let
         val intro =
           ({kind = clasetRules.Intro, safe = false, prio = SOME 40},
            ("maintenance_intro", boolTheory.AND_INTRO_THM))
         val norm =
           ({kind = clasetRules.Norm, safe = false, prio = SOME 2},
            ("maintenance_norm", boolTheory.IMP_ANTISYM_AX))
         val forward =
           ({kind = clasetRules.Forward, safe = true, prio = NONE},
            ("maintenance_forward", DISCH p (ASSUME p)))
         fun install (spec, named_th) cs = add_rule spec named_th cs
         val left = install intro empty_cs
         val right = install forward (install norm empty_cs)
         val merged = merge_cs (left, right)
         val incremented = install forward (install norm left)
         val target_query = {q = x, qvars = tmset [x]}
         val hyp_query = {q = x, qvars = tmset [x]}
         val removed = remove_rule "maintenance_forward" merged
         val target_removed =
           remove_rule "maintenance_norm" removed
       in
         same_aesop_rules
           (aesop_target_rules merged target_query)
           (aesop_target_rules incremented target_query) andalso
         same_aesop_rules
           (aesop_hyp_rules merged hyp_query)
           (aesop_hyp_rules incremented hyp_query) andalso
         (* Norm is kept beside the index, not inside it, so its
            maintenance is observed through [norm_rules]. *)
         same_aesop_rules (norm_rules merged) (norm_rules incremented)
           andalso
         not (has_aesop_name "maintenance_norm"
                (aesop_target_rules merged target_query)) andalso
         not (has_aesop_name "maintenance_norm"
                (aesop_hyp_rules merged hyp_query)) andalso
         has_aesop_name "maintenance_forward"
           (aesop_hyp_rules merged hyp_query) andalso
         not
           (has_aesop_name "maintenance_forward"
              (aesop_hyp_rules removed hyp_query)) andalso
         has_aesop_name "maintenance_intro"
           (aesop_target_rules removed target_query) andalso
         has_aesop_name "maintenance_norm" (norm_rules removed) andalso
         not
           (has_aesop_name "maintenance_norm"
              (norm_rules target_removed)) andalso
         has_aesop_name "maintenance_intro"
           (aesop_target_rules target_removed target_query)
       end)

val _ =
  test
    ("clasetLib removes tagged rules from every netpair",
     fn () =>
       let
         val cs =
           add_elims [("orE", boolTheory.OR_ELIM_THM)]
             (add_intros [("andI", boolTheory.AND_INTRO_THM)]
               (add_selims [("orES", boolTheory.OR_ELIM_THM)]
                 (add_sintros [("andIS", boolTheory.AND_INTRO_THM)]
                   (add_selims [("falseE", boolTheory.FALSITY)]
                     (add_sintros [("truthI", boolTheory.TRUTH)] empty_cs)))))
         val cs' =
           List.foldl (fn (name, acc) => remove_rule name acc) cs
             ["truthI", "falseE", "andIS", "orES", "andI", "orE"]
         val variable = ``z : bool``
         fun has_intro part =
           not (List.null (unify_intro_candidates part variable))
         fun has_elim part =
           not (List.null (unify_elim_candidates part variable))
         fun no_intro part =
           List.null (unify_intro_candidates part variable)
         fun no_elim part =
           List.null (unify_elim_candidates part variable)
       in
         has_intro (safe0_part cs) andalso has_elim (safe0_part cs) andalso
         has_intro (safep_part cs) andalso has_elim (safep_part cs) andalso
         has_intro (unsafe_part cs) andalso has_elim (unsafe_part cs) andalso
         has_intro (dup_part cs) andalso has_elim (dup_part cs) andalso
         no_intro (safe0_part cs') andalso no_elim (safe0_part cs') andalso
         no_intro (safep_part cs') andalso no_elim (safep_part cs') andalso
         no_intro (unsafe_part cs') andalso no_elim (unsafe_part cs') andalso
         no_intro (dup_part cs') andalso no_elim (dup_part cs')
       end)

val _ =
  test
    ("clasetLib removes and re-adds one rule on shared index paths",
     fn () =>
       let
         val spec = {kind = clasetRules.Intro, safe = false, prio = NONE}
         val norm = {kind = clasetRules.Norm, safe = false, prio = NONE}
         fun add name = add_derived_rule spec (name, intro_pq)
         fun check padding =
           let
             fun pad (i, cs) =
               add_derived_rule norm
                 ("padding" ^ Int.toString i, boolTheory.TRUTH) cs
             val base = List.foldl pad empty_cs
               (List.tabulate (padding, Lib.I))
             val original = add "third" (add "second" (add "first" base))
             val removed = remove_rule "second" original
             val readded = add "second" removed
             fun classical select cs =
               let
                 val part = select cs
                 fun indices entries =
                   map (fn i => i + 2 * padding) (candidate_indices entries)
               in
                 (indices (match_intro_candidates part ``p /\ q``),
                  indices (match_elim_candidates part ``~(p /\ q)``))
               end
             fun aesop cs =
               map #name (aesop_target_rules cs {q = x, qvars = tmset [x]})
             fun shared_paths part =
               classical part original = ([~5, ~3, ~1], [~6, ~4, ~2])
               andalso classical part removed = ([~5, ~1], [~6, ~2])
               andalso classical part readded = ([~7, ~5, ~1], [~8, ~6, ~2])
           in
             shared_paths unsafe_part andalso shared_paths dup_part andalso
             aesop original = ["third", "second", "first"] andalso
             aesop removed = ["third", "first"] andalso
             aesop readded = ["second", "third", "first"]
           end
       in
         check 0 andalso check 128
       end)

val _ =
  test
    ("clasetLib wrappers update by name and preserve choice semantics",
     fn () =>
       let
         fun safe_first tac = NORELSE (labelled p, tac)
         fun safe_second tac = NORELSE (labelled q, tac)
         fun unsafe_first tac = NAPPEND (labelled p, tac)
         fun unsafe_second tac = NAPPEND (labelled q, tac)
         val safe_cs =
           add_safe_wrapper ("one", safe_first)
             (add_safe_wrapper ("two", safe_second) empty_cs)
         val unsafe_cs =
           add_unsafe_wrapper ("one", unsafe_first)
             (add_unsafe_wrapper ("two", unsafe_second) empty_cs)
         val safe_cs' = del_safe_wrapper "two"
           (add_safe_wrapper ("one", safe_second) safe_cs)
         val unsafe_cs' = del_unsafe_wrapper "two"
           (add_unsafe_wrapper ("one", unsafe_second) unsafe_cs)
       in
         same_terms
           (labels (app_safe_wrappers safe_cs (labelled r)) label_goal) [q]
         andalso
         same_terms
           (labels (app_unsafe_wrappers unsafe_cs (labelled r)) label_goal)
           [q, p, r]
         andalso
         same_terms
           (labels (app_safe_wrappers safe_cs' (labelled r)) label_goal) [q]
         andalso
         same_terms
           (labels (app_unsafe_wrappers unsafe_cs' (labelled r)) label_goal)
           [q, r]
       end)

val _ =
  test
    ("clasetLib config uses VAR_EQ_TAC and Isabelle term sizes",
     fn () =>
       let
         val {hyp_subst_tac, size_of} = claset_config
         val variable_goal = ([``x : bool = p``], ``x : bool``)
       in
         size_of variable_goal = 4 andalso
         size_of ([], ``(\x : bool. x) p``) = 3 andalso
         (case #1 (hyp_subst_tac variable_goal (Context.snapshot())) of
             [(_, goal)] => Term.aconv goal p
           | _ => false)
       end)


(* clasetLib: persistent state and theorem attributes. *)
fun has_named_rule name cs =
  List.exists (fn (_, (name', _)) => name = name') (rules_of cs)

(* Pairwise distinct propositions: two rules that differ only in the name
   of a parameter are one rule once the parameter is bound. *)
val state_rule = DISCH p (ASSUME p)
val state_intro_rule = DISCH p (DISCH q (ASSUME p))
val state_export_rule = DISCH p (DISJ1 (ASSUME p) p)
val state_temp_rule = DISCH ``p /\ q`` (ASSUME ``p /\ q``)
val state_elim_rule = DISCH ``p \/ q`` (ASSUME ``p \/ q``)
val state_dest_rule = DISCH ``~p`` (ASSUME ``~p``)
val state_forward_rule = DISCH ``p ==> q`` (ASSUME ``p ==> q``)
val state_sforward_rule =
  let
    val p_q = ``p ==> q``
    val q_r = ``q ==> r``
  in
    DISCH p_q
      (DISCH q_r
        (DISCH p (MP (ASSUME q_r) (MP (ASSUME p_q) (ASSUME p)))))
  end
val state_norm_rule = ASSUME ``p <=> q``
val state_pending_name = "claset_state_pending"
val state_sintro_name = "claset_state_sintro"
val state_intro_name = "claset_state_intro"
val state_export_name = "claset_state_export"
val state_temp_name = "claset_state_temp"
val state_spec = {kind = clasetRules.Intro, safe = true, prio = NONE}

fun persistent_rule_name name =
  KernelSig.name_toString (ThmSetData.toKName name)

(* [normalise_rule_name] is the one normalisation of a user-written name
   to a theorem-set table's key, shared with linarithData's tables.  A
   name that already spells a key, and a name that can spell no key at
   all, must both come back unchanged rather than being re-qualified or
   raising. *)
val _ =
  let
    val thy = Theory.current_theory ()
    fun check (input, expected) =
      test ("normalise_rule_name " ^ Lib.quote input,
            fn () => normalise_rule_name input = expected)
  in
    List.app check
      [("thm", thy ^ "$thm"),
       ("bool.T", "bool$T"),
       ("bool$T", "bool$T"),
       ("a$b$c", "a$b$c"),
       ("a.b.c", "a.b.c")]
  end

val _ =
  test
    ("claset replays temporary updates in order at first demand",
     fn () =>
       let
         val _ = boolLib.save_thm (state_pending_name, state_rule)
         val _ = export_rule state_spec state_pending_name
         val _ = temp_delrule state_pending_name
       in
         not (has_named_rule (persistent_rule_name state_pending_name)
                (the_claset ()))
       end)

val state_attribute_cases =
  [("intro", {kind = clasetRules.Intro, safe = false, prio = NONE},
    state_rule),
   ("sintro", {kind = clasetRules.Intro, safe = true, prio = NONE},
    state_intro_rule),
   ("elim", {kind = clasetRules.Elim, safe = false, prio = NONE},
    state_export_rule),
   ("selim", {kind = clasetRules.Elim, safe = true, prio = NONE},
    state_temp_rule),
   ("dest", {kind = clasetRules.Dest, safe = false, prio = NONE},
    state_elim_rule),
   ("sdest", {kind = clasetRules.Dest, safe = true, prio = NONE},
    state_dest_rule),
   ("forward", {kind = clasetRules.Forward, safe = false, prio = NONE},
    state_forward_rule),
   ("sforward", {kind = clasetRules.Forward, safe = true, prio = NONE},
    state_sforward_rule),
   ("norm", {kind = clasetRules.Norm, safe = false, prio = NONE},
    state_norm_rule)]

val _ =
  test
    ("claset attributes register and update the global state",
     fn () =>
       let
         fun add_attribute (attr, _, th) =
           let val name = state_sintro_name ^ "_" ^ attr
           in
             boolLib.save_thm (name ^ "[" ^ attr ^ "]", th);
             ()
           end
         fun has_attribute (_, spec, th) =
           List.exists
             (fn (spec', (_, th')) =>
                same_spec spec spec' andalso
                same_thm (canonical_rule_of (#kind spec) th) th')
             (rules_of (the_claset ()))
       in
         List.app add_attribute state_attribute_cases;
         List.all (fn (attr, _, _) => ThmAttribute.is_attribute attr)
           state_attribute_cases andalso
         List.all has_attribute state_attribute_cases
       end)

val _ =
  test
    ("claset local attributes and temporary additions are not persisted",
     fn () =>
       let
         val _ = boolLib.save_thm
           (state_intro_name ^ "[intro,local]", state_intro_rule)
         val _ = temp_add_rule state_spec (state_temp_name, state_temp_rule)
         val cs_before = the_claset ()
         val persisted = Option.valOf (merge_clasets ["min"])
         val _ = temp_delrule state_temp_name
         val cs_after = the_claset ()
       in
         has_named_rule state_intro_name cs_before andalso
         has_named_rule state_temp_name cs_before andalso
         not (has_named_rule state_intro_name persisted) andalso
         not (has_named_rule state_temp_name persisted) andalso
         has_named_rule state_intro_name cs_after andalso
         not (has_named_rule state_temp_name cs_after)
       end)

(* A tactic reads the claset of the context it is applied in, and reading
   it there consults no other context: not the ambient one, which during a
   proof may belong to someone else. *)
val _ =
  test
    ("the_claset_of reads the claset of the context given",
     fn () =>
       let
         val name = "claset_context_rule"
         val saved = Context.snapshot ()
         val with_rule =
           Portable.finally (fn () => Context.restore saved)
             (fn () =>
                (temp_add_rule state_spec
                   (name, DISCH ``p /\ q /\ r`` (ASSUME ``p /\ q /\ r``));
                 Context.snapshot ())) ()
         val warnings = ref ([] : string list)
         fun read () =
           (Context.set_ambient_report_level 2;
            Lib.with_flag
              (Feedback.WARNING_outstream,
               fn s => warnings := s :: !warnings)
              (Context.in_proof (fn () => the_claset_of with_rule)) ())
         val cs =
           Portable.finally (fn () => Context.set_ambient_report_level 1)
             read ()
       in
         has_named_rule name cs andalso
         not (has_named_rule name (the_claset ())) andalso
         null (!warnings)
       end)

val _ =
  test
    ("claset persistent API updates state correctly",
     fn () =>
       let
         val _ = boolLib.save_thm (state_export_name, state_export_rule)
         val _ = export_rule state_spec state_export_name
         val exported = the_claset ()
         val merged = merge_clasets ["min"]
         val by_theory = claset_of_theory {thyname = "min"}
         val only_local = add_sintros [("local-only", state_rule)] empty_cs
         val scoped = with_claset only_local
           (fn () => has_named_rule "local-only" (the_claset ())) ()
         val _ = delrule (persistent_rule_name state_export_name)
       in
         has_named_rule (persistent_rule_name state_export_name) exported andalso
         Option.isSome merged andalso Option.isSome by_theory andalso
         scoped andalso
         not (has_named_rule (persistent_rule_name state_export_name)
                (the_claset ()))
       end)

val _ =
  test
    ("claset unsafe attributes reject invalid priorities cleanly",
     fn () =>
       let
         (* The oversized numeral overflows a fixed-width Int rather than
            failing to parse, so it must be rejected on its shape. *)
         val cases =
           [("intro", ["0"]), ("elim", ["101"]), ("dest", ["75x"]),
            ("intro", ["25", "50"]), ("elim", [""]), ("dest", ["~1"]),
            ("intro", ["99999999999999999999999999"])]
         fun rejected (attrname, args) =
           hol_err_msg
             (fn () =>
               ThmAttribute.local_attribute
                 {attrname = attrname, name = "bad-priority", args = args,
                  thm = state_rule}) =
           SOME
             ("Invalid priority for attribute " ^ attrname ^
              "; expected one integer from 1 to 100")
       in
         List.all rejected cases
       end)

val _ =
  test
    ("claset safe attributes reject priorities",
     fn () =>
       let
         fun rejected attrname =
           hol_err_msg
             (fn () =>
               ThmAttribute.local_attribute
                 {attrname = attrname, name = "bad-safe-priority",
                  args = ["10"], thm = state_rule}) =
           SOME
             ("Arguments not allowed for attribute " ^ attrname ^
              "; safe-rule priorities are not supported")
       in
         List.all rejected ["sintro", "selim", "sdest"]
       end)

val _ =
  test
    ("new claset attributes accept percentages and integer penalties",
     fn () =>
       let
         fun mk_rule clasetRules.Forward stem =
               let val tm = mk_var (stem, bool)
               in DISCH tm (ASSUME tm) end
           | mk_rule _ stem = ASSUME (mk_var (stem, bool))
         val cases =
           [("forward", [], clasetRules.Forward, false, NONE),
            ("forward", ["1"], clasetRules.Forward, false, SOME 1),
            ("forward", ["100"], clasetRules.Forward, false, SOME 100),
            ("sforward", [], clasetRules.Forward, true, NONE),
            ("norm", [], clasetRules.Norm, false, NONE),
            ("norm", ["0"], clasetRules.Norm, false, SOME 0),
            ("norm", ["~11"], clasetRules.Norm, false, SOME ~11),
            ("norm", ["23"], clasetRules.Norm, false, SOME 23)]
         fun check (index, (attrname, args, kind, safe, prio)) =
           let
             val stem = "new_attribute_" ^ Int.toString index
             val name = stem ^ "_" ^ attrname
             val th = mk_rule kind stem
             val _ =
               ThmAttribute.local_attribute
                 {attrname = attrname, name = name, args = args, thm = th}
             val found =
               List.find (fn (_, (name', _)) => name = name')
                 (rules_of (the_claset ()))
             val _ = temp_delrule name
           in
             case found of
                 SOME (spec, (_, th')) =>
                   same_spec spec
                     {kind = kind, safe = safe, prio = prio} andalso
                   same_thm (canonical_rule_of kind th) th'
               | NONE => false
           end
       in
         List.all check (ListPair.zip (List.tabulate (length cases, I), cases))
       end)

val _ =
  test
    ("new claset attributes reject malformed arguments cleanly",
     fn () =>
       let
         val priority_message =
           "Invalid priority for attribute forward; expected one integer " ^
           "from 1 to 100"
         val penalty_message =
           "Invalid penalty for attribute norm; expected one integer"
         val safe_message =
           "Arguments not allowed for attribute sforward; safe-rule " ^
           "priorities are not supported"
         fun rejected attrname args message =
           hol_err_msg
             (fn () =>
               ThmAttribute.local_attribute
                 {attrname = attrname, name = "bad-new-attribute",
                  args = args, thm = state_forward_rule}) =
           SOME message
         (* A numeral too large for a fixed-width Int overflows inside
            Int.fromString instead of failing to parse.  Every penalty an
            Int can hold is legitimate, so the outcome is either a clean
            acceptance or the documented error -- never a foreign
            exception escaping the attribute. *)
         val oversized = "99999999999999999999999999"
         fun clean_penalty args =
           let
             val name = "oversized-penalty"
             fun apply () =
               ThmAttribute.local_attribute
                 {attrname = "norm", name = name, args = args,
                  thm = ASSUME ``r <=> q``}
           in
             (apply (); temp_delrule name; true)
             handle Interrupt => raise Interrupt
                  | HOL_ERR e => Feedback.message_of e = penalty_message
                  | _ => false
           end
       in
         List.all
           (fn args => rejected "forward" args priority_message)
           [["0"], ["101"], ["75x"], ["25", "50"], [oversized]] andalso
         List.all
           (fn args => rejected "norm" args penalty_message)
           [[""], ["~"], ["1x"], ["1", "2"], ["~1x"], [" 1"]] andalso
         List.all clean_penalty [[oversized], ["~" ^ oversized]] andalso
         rejected "sforward" ["10"] safe_message
       end)


(* clasetLib: TypeBase hook and contribution registry. *)
fun legacy_fresh_outer_vars th vars =
  let
    fun freshen avoids [] = []
      | freshen avoids (v :: vs) =
          let val v' = variant avoids v
          in v' :: freshen (v' :: avoids) vs end
  in
    freshen (free_varsl (hyp th)) vars
  end

fun legacy_iff_dest_rule th =
  let
    val th' = canonical_rule th
    val (vars, _) = strip_forall (concl th')
    val vars' = legacy_fresh_outer_vars th' vars
  in
    GENL vars' (#1 (EQ_IMP_RULE (Drule.SPECL vars' th')))
  end

fun derived_iff_dest th =
  case List.filter
    (fn ({kind, ...}, _) => kind = clasetRules.Dest)
    (iff_rules "claset-selftest-iff" th) of
      [(_, (_, dest))] => dest
    | _ => raise Fail "missing derived iff dest rule"

fun typebase_tyinfo tyop =
  case List.filter
    (fn tyi => #2 (TypeBasePure.ty_name_of tyi) = tyop)
    (TypeBase.elts ()) of
      [tyi] => tyi
    | _ => raise Fail ("missing TypeBase selftest datatype " ^ tyop)

fun typebase_hook_tyinfo () = typebase_tyinfo "claset_hook_before_demand"

fun has_typebase_rule spec th =
  List.exists
    (fn (spec', (_, th')) =>
       same_spec spec spec' andalso
       same_thm (canonical_rule_of (#kind spec) th) th')
    (rules_of (the_claset ()))

val typebase_sdest_spec =
  {kind = clasetRules.Dest, safe = true, prio = NONE}
val typebase_sintro_spec =
  {kind = clasetRules.Intro, safe = true, prio = NONE}

val _ =
  test
    ("moved iff derivation agrees with legacy TypeBase injectivity dests",
     fn () =>
       let
         fun agrees tyi =
           case Lib.total TypeBasePure.one_one_of tyi of
               SOME (SOME theorem) =>
                 List.all
                   (fn conjunct =>
                     let
                       val legacy =
                         canonical_rule (legacy_iff_dest_rule conjunct)
                       val moved =
                         canonical_rule (derived_iff_dest conjunct)
                     in
                       if same_thm legacy moved then true
                       else
                         (print
                            ("legacy iff dest: " ^
                             Parse.thm_to_string legacy ^
                             "\nmoved iff dest: " ^
                             Parse.thm_to_string moved ^ "\n");
                          false)
                     end)
                   (Drule.CONJUNCTS theorem)
             | _ => true
       in
         List.all agrees (TypeBase.elts ())
       end)

fun distinct_handle tyop =
  let val (thy, name) = TypeBasePure.ty_name_of (typebase_tyinfo tyop)
  in "__claset_tyinfo_" ^ thy ^ "_" ^ name ^ "_distinct" end

fun clash_candidates cs tyop query =
  List.filter
    (fn {name, ...} => String.isPrefix (distinct_handle tyop ^ "_") name)
    (aesop_hyp_rules cs query)

fun clash_query q vars =
  {q = q, qvars = HOLset.fromList Term.compare vars}

fun schematic_query q vars =
  {q = q, qvars = HOLset.fromList Term.compare vars, flexible_type = K true}

val unmetered =
  {checkpoint = listUtil.no_checkpoint, derive = listUtil.no_checkpoint}

fun clash_valid cs tyop equality =
  case clash_candidates cs tyop (clash_query equality []) of
      [rule] =>
        let
          val theorem = Drule.PART_MATCH (fst o dest_imp) (#thm rule) equality
          val result = snd (dest_imp (concl theorem))
          val proof = MP (INST [result |-> p] theorem) (ASSUME equality)
          val (residues, validation) = Tactical.VALID (ACCEPT_TAC proof)
            ([equality], p) (Context.snapshot())
        in
          null residues andalso aconv (concl (validation [])) p
        end
    | _ => false

val _ =
  test
    ("TypeBase keeps injectivity and one lazy distinctness handle",
     fn () =>
       let
         fun check tyop =
           let
             val tyi = typebase_tyinfo tyop
             val injective = Option.valOf (TypeBasePure.one_one_of tyi)
             val rules = List.concat
               (map (iff_rules "claset-selftest-injectivity")
                 (Drule.CONJUNCTS injective))
           in
             List.exists (fn name => name = distinct_handle tyop)
               (distinct_rule_names seed_claset) andalso
             not (List.exists
               (String.isPrefix (distinct_handle tyop) o #1 o #2)
               (rules_of seed_claset)) andalso
             List.all (fn (spec, (_, th)) => has_typebase_rule spec th) rules
           end
       in
         check "claset_hook_before_demand" andalso check "claset_hook_wide"
       end)

val _ =
  test
    ("lazy clashes prove both orientations, payloads and wide pure enums",
     fn () => List.all (fn (tyop, equality) =>
       clash_valid seed_claset tyop equality)
       [("claset_hook_before_demand", ``ClasetHookA = ClasetHookB n``),
        ("claset_hook_before_demand", ``ClasetHookB 0 = ClasetHookA``),
        ("claset_hook_wide", ``ClasetWide0 = ClasetWide15 n``),
        ("claset_hook_wide", ``ClasetWide15 0 = ClasetWide14``),
        ("claset_hook_enum", ``Enum0 = Enum15``)])

val _ =
  test
    ("clash cache retains generic payloads and polymorphic type instances",
     fn () => List.all (clash_valid seed_claset "claset_hook_poly")
       [``PolyLeft 0 = PolyRight 1``,
        ``PolyLeft (x:num) = PolyRight y``,
        ``PolyLeft T = PolyRight F``,
        ``PolyLeft (x:'a) = PolyRight y``])

val _ =
  test
    ("clash retrieval distinguishes rigid variables from genuine metas",
     fn () =>
       let
         val tyop = "claset_hook_wide"
         fun count query = length (clash_candidates seed_claset tyop query)
         val x = ``x:claset_hook_wide``
         val y = ``y:claset_hook_wide``
         val one = mk_eq (``ClasetWide0``, x)
         val both = mk_eq (x, y)
         val candidates = clash_candidates seed_claset tyop
           (clash_query both [x, y])
         val names = map #name candidates
         val tagged = unify_elim_candidates_with unmetered
           (safe0_part seed_claset) both (schematic_query both [x, y])
         val polls = ref 0
         val measured = unify_elim_candidates_with
           {checkpoint = fn () => polls := !polls + 1,
            derive = listUtil.no_checkpoint}
           (safe0_part seed_claset) both (schematic_query both [x, y])
         val indices = map (#index o #1) tagged
       in
         count (clash_query one []) = 0 andalso
         count (clash_query both []) = 0 andalso
         count (clash_query one [x]) = 15 andalso
         length candidates = 16 * 15 andalso
         length (Lib.mk_set names) = length names andalso
         length (Lib.mk_set indices) = length indices andalso
         !polls > 0 andalso same_candidates tagged measured andalso
         count (clash_query ``ClasetWide15 n = ClasetWide15 m`` []) = 0
       end)

val _ =
  test
    ("classical lookup shares ordering and collects metas only for clashes",
     fn () =>
       let
         val x = ``x:claset_hook_wide``
         val y = ``y:claset_hook_wide``
         val equality = mk_eq (x, y)
         val plain = ``p:bool``
         val unindexed_type = ``(x:num -> num) = y``
         val globals = safe0_part seed_claset
         val without_distinct = safep_part seed_claset
         val assumptions = [[plain, unindexed_type],
           [``ClasetWide0 = ClasetWide15 n``, equality], [plain]]
         val conclusion = [plain, plain]
         val forms = {conclusion = conclusion, assumptions = assumptions}
         val inspected = ref []
         fun qvars q =
           if aconv q equality then HOLset.fromList Term.compare [x, y]
           else Term.empty_tmset
         fun actual unify part =
           classical_candidates
             {unify = unify, derive = listUtil.no_checkpoint,
              query_metas = fn q => (inspected := q :: !inspected; qvars q),
              flexible_type = K true} part forms
         fun expected intros elims part =
           clasetRules.candidate_order
             (List.concat (map (intros part) conclusion) @
              List.concat (map (List.concat o map (elims part)) assumptions))
         val matched = actual false globals
         val unified = actual true globals
         val eager_inspections = ref 0
         fun unify_elims part q =
           (eager_inspections := !eager_inspections + 1;
            unify_elim_candidates_with unmetered part q
              {q = q, qvars = qvars q, flexible_type = K true})
         val no_distinct = actual true without_distinct
       in
         same_candidates matched
           (expected match_intro_candidates match_elim_candidates globals)
         andalso
         same_candidates unified
           (expected unify_intro_candidates unify_elims globals)
         andalso
         same_candidates no_distinct
           (expected unify_intro_candidates unify_elims without_distinct)
         andalso !eager_inspections = 10 andalso
         (case !inspected of [q] => aconv q equality | _ => false)
       end)

val _ =
  test
    ("deleting a lazy handle suppresses it without changing the snapshot",
     fn () =>
       let
         val tyop = "claset_hook_wide"
         val query = clash_query ``ClasetWide0 = ClasetWide15 n`` []
         val removed = remove_rule (distinct_handle tyop) seed_claset
       in
         null (clash_candidates removed tyop query) andalso
         length (clash_candidates seed_claset tyop query) = 1 andalso
         null (distinct_rule_names persisted_seed_claset)
       end)

val _ =
  test
    ("schematic clash enumeration observes candidate checkpoints",
     fn () =>
       let
         val only_distinct = List.foldl
           (fn ((_, (name, _)), cs) => remove_rule name cs)
           seed_claset (rules_of seed_claset)
         val x = ``x:claset_hook_wide``
         val y = ``y:claset_hook_wide``
         val equality = mk_eq (x, y)
         val polls = ref 0
         exception ClashLimit
         fun checkpoint () =
           (polls := !polls + 1;
            if !polls = 50 then raise ClashLimit else ())
       in
         ((ignore (unify_elim_candidates_with
              {checkpoint = checkpoint, derive = listUtil.no_checkpoint}
              (safe0_part only_distinct) equality
              (schematic_query equality [x, y])); false)
          handle ClashLimit => !polls = 50)
       end)

fun has_named_spec_rule spec name =
  List.exists
    (fn (spec', (name', _)) => name = name' andalso same_spec spec spec')
    (rules_of (the_claset ()))

(* The names are the handle a proof uses to suppress a contributed rule with
   Del, so they are part of the interface and not free to drift. *)
val _ =
  test
    ("TypeBase injectivity contributes named safe intro and dest rules",
     fn () =>
       let
         val tyi = typebase_hook_tyinfo ()
         val (thy, tyop) = TypeBasePure.ty_name_of tyi
         val stem = "__claset_tyinfo_" ^ thy ^ "_" ^ tyop ^ "_inject_"
         val injective = Option.valOf (TypeBasePure.one_one_of tyi)
         fun named index =
           let val name = stem ^ Int.toString index
           in
             has_named_spec_rule typebase_sintro_spec (name ^ "_intro")
               andalso
             has_named_spec_rule typebase_sdest_spec (name ^ "_dest")
           end
       in
         List.all named
           (List.tabulate (length (Drule.CONJUNCTS injective), Lib.I))
       end)

val tyinfo_idempotence_p = ``claset_tyinfo_idempotence_p : bool``
val tyinfo_idempotence_rule =
  DISCH tyinfo_idempotence_p
    (CONJ (ASSUME tyinfo_idempotence_p) (ASSUME tyinfo_idempotence_p))
val tyinfo_idempotence_spec =
  {kind = clasetRules.Intro, safe = true, prio = NONE}

fun tyinfo_idempotence_contribution _ =
  [(tyinfo_idempotence_spec,
    ("claset-tyinfo-idempotence", tyinfo_idempotence_rule))]

val tyinfo_idempotence_key = "claset-selftest-idempotence"

fun count_typebase_rules th =
  length
    (List.filter
       (fn (_, (_, th')) => same_thm (canonical_rule th) th')
       (rules_of (the_claset ())))

val _ =
  test
    ("claset TypeBase contributions silently deduplicate reprocessing",
     fn () =>
       let
         val _ = register_tyinfo_contribution
           (tyinfo_idempotence_key, tyinfo_idempotence_contribution)
         val _ = register_tyinfo_contribution
           (tyinfo_idempotence_key, tyinfo_idempotence_contribution)
       in
         count_typebase_rules tyinfo_idempotence_rule = 1
       end)

val ambient_seed_spoof_name = seed_export_identity "AMBIENT_ONLY"
val ambient_seed_spoof_rule = REFL ``ClasetHookA``

fun ambient_seed_spoof_contribution _ =
  [(tyinfo_idempotence_spec,
    (ambient_seed_spoof_name, ambient_seed_spoof_rule))]

val _ =
  test
    ("persistent theory clasets exclude ambient same-name rules",
     fn () =>
       let
         val body_exception = ref (NONE : exn option)

         fun restore_original_provider () =
           (register_tyinfo_contribution
              (tyinfo_idempotence_key, tyinfo_idempotence_contribution);
            if has_named_rule ambient_seed_spoof_name (the_claset ()) then
              raise Fail "ambient seed spoof survived provider restoration"
            else
              ())

         fun cleanup () =
           restore_original_provider ()
           handle cleanup_exception =>
             case !body_exception of
                 SOME _ =>
                   (* The body exception takes precedence when both fail.
                      Reporting the cleanup failure is therefore best-effort:
                      even WARNINGs_as_ERRs must not replace the body error. *)
                   (HOL_WARNING "rules selftest" "cleanup"
                      ("Failed to restore the temporary ambient spoof " ^
                       "contributor after the test body raised; preserving " ^
                       "the original body exception. Cleanup exception: " ^
                       General.exnMessage cleanup_exception)
                    handle _ => ())
               | NONE => raise cleanup_exception

         fun check () =
           let
             val _ = register_tyinfo_contribution
               (tyinfo_idempotence_key, ambient_seed_spoof_contribution)
             val persistent =
               Option.valOf
                 (persistent_claset_of_theory {thyname = seed_theory_name})
             val effective =
               Option.valOf (claset_of_theory {thyname = seed_theory_name})
             val persistent_names = map (#1 o #2) (rules_of persistent)
             val effective_names = map (#1 o #2) (rules_of effective)
             val untagged =
               untagged_theorems
                 {theorem_names = [ambient_seed_spoof_name],
                  persistent_rule_names = persistent_names,
                  permitted = []}
             fun named name = List.exists (fn name' => name = name')
           in
             not (named ambient_seed_spoof_name persistent_names) andalso
             named ambient_seed_spoof_name effective_names andalso
             untagged = [ambient_seed_spoof_name]
           end

         fun record_body_exception () =
           check ()
           handle body_exn =>
             (body_exception := SOME body_exn;
              raise body_exn)
       in
         Portable.finally cleanup record_body_exception ()
       end)

val tyinfo_multispec_p = ``claset_tyinfo_multispec_p : bool``
(* A dedicated variable name no longer isolates a fixture: the parameter is
   bound, so the proposition itself has to be distinct. *)
val tyinfo_multispec_conj =
  boolSyntax.mk_conj (tyinfo_multispec_p, tyinfo_multispec_p)
val tyinfo_multispec_rule =
  DISCH tyinfo_multispec_conj (CONJUNCT1 (ASSUME tyinfo_multispec_conj))
val tyinfo_multispec_intro =
  {kind = clasetRules.Intro, safe = true, prio = NONE}
val tyinfo_multispec_elim =
  {kind = clasetRules.Elim, safe = true, prio = NONE}

fun tyinfo_multispec_contribution _ =
  [(tyinfo_multispec_intro,
    ("claset-tyinfo-multispec-intro", tyinfo_multispec_rule)),
   (tyinfo_multispec_elim,
    ("claset-tyinfo-multispec-elim", tyinfo_multispec_rule))]

val _ =
  test
    ("claset TypeBase contributions keep cross-kind specifications",
     fn () =>
       let
         val _ = register_tyinfo_contribution
           ("claset-selftest-multispec", tyinfo_multispec_contribution)
         val rules = rules_of (the_claset ())
         fun present spec name =
           List.exists
             (fn (spec', (name', th')) =>
                name = name' andalso same_spec spec spec' andalso
                same_thm
                  (canonical_rule_of (#kind spec) tyinfo_multispec_rule)
                  th')
             rules
       in
         present tyinfo_multispec_intro "claset-tyinfo-multispec-intro"
           andalso
         present tyinfo_multispec_elim "claset-tyinfo-multispec-elim"
       end)

val tyinfo_replace_p = ``claset_tyinfo_replace_p : bool``
val tyinfo_replace_q = ``claset_tyinfo_replace_q : bool``
val tyinfo_replace_old_rule =
  DISCH tyinfo_replace_p
    (DISJ1 (ASSUME tyinfo_replace_p) tyinfo_replace_q)
val tyinfo_replace_new_rule =
  DISCH tyinfo_replace_q
    (DISJ2 tyinfo_replace_p (ASSUME tyinfo_replace_q))

fun tyinfo_replacement name th _ =
  [(tyinfo_idempotence_spec, (name, th))]

val _ =
  test
    ("replacing a TypeBase contribution removes its stale rules",
     fn () =>
       let
         val key = "claset-selftest-replacement"
         val old_name = "claset-tyinfo-replacement-old"
         val new_name = "claset-tyinfo-replacement-new"
         val _ = register_tyinfo_contribution
           (key, tyinfo_replacement old_name tyinfo_replace_old_rule)
         val _ = register_tyinfo_contribution
           (key, tyinfo_replacement new_name tyinfo_replace_new_rule)
         val rules = rules_of (the_claset ())
         fun named name = List.exists (fn (_, (name', _)) => name = name') rules
       in
         not (named old_name) andalso named new_name
       end)

val tyinfo_collision_p = ``claset_tyinfo_collision_p : bool``
val tyinfo_collision_q = ``claset_tyinfo_collision_q : bool``
val tyinfo_collision_rule =
  DISCH tyinfo_collision_p
    (DISJ1 (ASSUME tyinfo_collision_p) tyinfo_collision_q)

val _ =
  test
    ("replacing a TypeBase provider preserves an ambient duplicate",
     fn () =>
       let
         val key = "claset-selftest-unowned-provider"
         val name = "claset-tyinfo-unowned-provider"
         fun provider _ =
           [(tyinfo_idempotence_spec, (name, tyinfo_collision_rule))]
         fun empty_provider _ = []
         fun cleanup () =
           (register_tyinfo_contribution (key, empty_provider);
            temp_delrule name)
         fun check () =
           let
             val _ = temp_add_rule tyinfo_idempotence_spec
               (name, tyinfo_collision_rule)
             val _ = register_tyinfo_contribution (key, provider)
             val _ = register_tyinfo_contribution (key, empty_provider)
           in
             has_named_rule name (the_claset ())
           end
       in
         Portable.finally cleanup check ()
       end)

val _ =
  test
    ("replacing a TypeBase entry reconciles its derived claset rules",
     fn () =>
       let
         val original = typebase_hook_tyinfo ()
         val ty = TypeBasePure.ty_of original
         val (thy, tyop) = TypeBasePure.ty_name_of original
         val stem = "__claset_tyinfo_" ^ thy ^ "_" ^ tyop ^ "_"
         val replacement =
           TypeBasePure.mk_nondatatype_info
             (ty,
              {nchotomy = NONE, induction = NONE, size = NONE,
               encode = NONE})
         fun contributed_names () =
           List.filter (String.isPrefix stem)
             (map (#1 o #2) (rules_of (the_claset ())) @
              distinct_rule_names (the_claset ()))
         fun restore () = TypeBase.write [original]
         fun check () =
           let
             val original_names = contributed_names ()
             val _ = TypeBase.write [replacement]
             val removed = null (contributed_names ())
             val _ = restore ()
           in
             not (null original_names) andalso removed andalso
             not (null (contributed_names ()))
           end
       in
         Portable.finally restore check ()
       end)


(* Global removal of TypeBase-derived rules: refused with a warning in both
   states, never recorded, and per-call or local removal still works. *)
fun has_reserved_rules cs =
  has_named_rule (tyinfo_reserved_stem ^ "inject_0_intro") cs andalso
  List.exists (fn name => name = tyinfo_reserved_stem ^ "distinct")
    (distinct_rule_names cs)

fun lacks_reserved_rules cs =
  not (has_named_rule (tyinfo_reserved_stem ^ "inject_0_intro") cs) andalso
  not (List.exists (fn name => name = tyinfo_reserved_stem ^ "distinct")
         (distinct_rule_names cs))

val _ =
  test
    ("claset refuses global removal of TypeBase rules before the first demand",
     fn () =>
       warned_per_call unforced_reserved_deletions andalso
       has_reserved_rules (the_claset ()))

val _ =
  test
    ("claset refuses global removal of TypeBase rules after the first demand",
     fn () =>
       let
         val key = "claset-selftest-reserved-catch-up"
         fun cleanup () = register_tyinfo_contribution (key, fn _ => [])
         fun check () =
           let
             val deletions = delete_reserved_names ()
             val kept = has_reserved_rules (the_claset ())
             (* A catch-up must find nothing to restore. *)
             val _ = cleanup ()
           in
             warned_per_call deletions andalso kept andalso
             has_reserved_rules (the_claset ())
           end
       in
         Portable.finally cleanup check ()
       end)

val _ =
  test
    ("claset replays a recorded TypeBase rule removal alike in both orders",
     fn () =>
       has_reserved_rules seed_claset andalso
       (replay_reserved_removals (); has_reserved_rules (the_claset ())))

fun claset_deltas () =
  Theory.LoadableThyData.segment_data_string
    {thy = Theory.current_theory (), thydataty = "claset.deltas"}

val _ =
  test
    ("claset records no delta for a refused TypeBase rule removal",
     fn () =>
       let val before = claset_deltas ()
       in ignore (delete_reserved_names ()); claset_deltas () = before end)

val _ =
  test
    ("Del and with_claset still remove TypeBase rules locally",
     fn () =>
       let
         val (by_del, _) =
           invocation_claset (the_claset ()) (map Del tyinfo_reserved_names)
         val local_cs =
           List.foldl (fn (name, cs) => remove_rule name cs) (the_claset ())
             tyinfo_reserved_names
         val scoped =
           with_claset local_cs
             (fn () => lacks_reserved_rules (the_claset ())) ()
       in
         lacks_reserved_rules by_del andalso scoped andalso
         has_reserved_rules (the_claset ())
       end)


(* clasetLib: per-invocation markers. *)
fun has_marker_rule spec th cs =
  List.exists
    (fn (spec', (_, th')) =>
       same_spec spec spec' andalso
       same_thm (canonical_rule_of (#kind spec) th) th')
    (rules_of cs)

val marker_sintro_spec =
  {kind = clasetRules.Intro, safe = true, prio = NONE}
val marker_intro_spec =
  {kind = clasetRules.Intro, safe = false, prio = NONE}
val marker_selim_spec =
  {kind = clasetRules.Elim, safe = true, prio = NONE}
val marker_elim_spec =
  {kind = clasetRules.Elim, safe = false, prio = NONE}
val marker_sdest_spec =
  {kind = clasetRules.Dest, safe = true, prio = NONE}
val marker_dest_spec =
  {kind = clasetRules.Dest, safe = false, prio = NONE}

val marker_cases =
  [("SIntro", SIntro, destSIntro, marker_sintro_spec,
    boolTheory.AND_INTRO_THM),
   ("Intro", Intro, destIntro, marker_intro_spec, boolTheory.AND_INTRO_THM),
   ("SElim", SElim, destSElim, marker_selim_spec, boolTheory.OR_ELIM_THM),
   ("Elim", Elim, destElim, marker_elim_spec, boolTheory.OR_ELIM_THM),
   ("SDest", SDest, destSDest, marker_sdest_spec, boolTheory.OR_ELIM_THM),
   ("Dest", Dest, destDest, marker_dest_spec, boolTheory.OR_ELIM_THM)]

val simpset_marker_cases =
  [("Simp", Simp, destSimp, boolTheory.AND_CLAUSES),
   ("Iff", Iff, destIff, boolTheory.IMP_CLAUSES)]

val aesop_marker_cases =
  [("Norm", Norm, destNorm, boolTheory.AND_CLAUSES),
   ("Forward", Forward, destForward, boolTheory.OR_ELIM_THM),
   ("SForward", SForward, destSForward, boolTheory.OR_ELIM_THM)]

val claset_marker_theorems =
  [SIntro boolTheory.AND_INTRO_THM,
   Intro boolTheory.AND_INTRO_THM,
   SElim boolTheory.OR_ELIM_THM,
   Elim boolTheory.OR_ELIM_THM,
   SDest boolTheory.OR_ELIM_THM,
   Dest boolTheory.OR_ELIM_THM,
   Simp boolTheory.AND_CLAUSES,
   Iff boolTheory.IMP_CLAUSES,
   Norm boolTheory.AND_CLAUSES,
   Forward boolTheory.OR_ELIM_THM,
   SForward boolTheory.OR_ELIM_THM,
   Del "claset-selftest"]

val marker_prefix = "__claset_marker_"

fun named_marker_is name th cs =
  case List.find (fn (_, (name', _)) => name = name') (rules_of cs) of
      SOME (_, (_, th')) => same_thm (canonical_rule th) th'
    | NONE => false

val _ =
  test
    ("claset markers round-trip and add their temporary rules",
     fn () =>
       List.all
         (fn (_, mark, dest, spec, th) =>
            let
              val marked = mark th
              val (cs, rest) = process_claset_tags [marked] empty_cs
            in
              (case dest marked of
                   SOME th' => same_thm th th'
                 | NONE => false) andalso
              List.null rest andalso has_marker_rule spec th cs
            end)
         marker_cases)

val _ =
  test
    ("simpset markers round-trip without becoming claset rules",
     fn () =>
       List.all
         (fn (_, mark, dest, th) =>
            let
              val marked = mark th
              val (cs, rest) = process_claset_tags [marked] empty_cs
            in
              (case dest marked of
                   SOME th' => same_thm th th'
                 | NONE => false) andalso
              List.null (rules_of cs) andalso
              ListPair.allEq
                (fn (left, right) => same_thm left right)
                (rest, [marked])
            end)
         simpset_marker_cases)

val _ =
  test
    ("aesop markers round-trip through the classical pass-through",
     fn () =>
       List.all
         (fn (_, mark, dest, th) =>
            let
              val marked = mark th
              val (cs, rest) = process_claset_tags [marked] empty_cs
            in
              (case dest marked of
                   SOME th' => same_thm th th'
                 | NONE => false) andalso
              List.null (rules_of cs) andalso
              ListPair.allEq
                (fn (left, right) => same_thm left right)
                (rest, [marked])
            end)
         aesop_marker_cases)

(* A marker whose rule class this tactic cannot install must be reported,
   not assumed as a fact: the marked theorem is not a usable assumption. *)
val _ =
  test
    ("markers for other engines are refused as invocation facts",
     fn () =>
       let
         val cases =
           [(Simp boolTheory.AND_CLAUSES,
             "Simp marker requires a tactic with a simpset"),
            (Iff boolTheory.IMP_CLAUSES,
             "Iff marker requires a tactic with a simpset"),
            (Norm boolTheory.AND_CLAUSES,
             "Norm marker requires an Aesop-aware tactic"),
            (Forward boolTheory.OR_ELIM_THM,
             "Forward marker requires an Aesop-aware tactic"),
            (SForward boolTheory.OR_ELIM_THM,
             "SForward marker requires an Aesop-aware tactic")]
         fun refused (marked, message) =
           hol_err_msg
             (fn () => (invocation_claset empty_cs [marked]; ())) =
           SOME message
         (* Tactics with a simpset bucket Simp and Iff away themselves,
            but they insert the remaining arguments directly. *)
         fun not_inserted (marked, message) =
           hol_err_msg (fn () => (INSERT_FACTS_TAC [marked]; ())) =
           SOME message
       in
         List.all refused cases andalso
         List.all not_inserted (List.drop (cases, 2))
       end)

val _ =
  test
    ("simp argument classifier preserves every bucket's input order",
     fn () =>
       let
         val simp1 = boolTheory.AND_CLAUSES
         val simp2 = boolTheory.OR_CLAUSES
         val iff1 = boolTheory.IMP_CLAUSES
         val iff2 = boolTheory.NOT_CLAUSES
         val control1 = markerLib.Excl "claset-selftest-one"
         val control2 = BoundedRewrites.Once boolTheory.TRUTH
         val control3 = markerLib.Split boolTheory.OR_CLAUSES
         val control4 = markerLib.ExclX "rule:claset-selftest"
         val fact1 = boolTheory.EQ_REFL
         val fact2 = boolTheory.FORALL_SIMP
         val {simp_rules, iff_rules, simp_controls, rest} =
           classify_simp_args
             [Simp simp1, control1, fact1, Iff iff1,
              control3, Simp simp2, control2, Iff iff2, fact2, control4]
         fun same_list left right =
           ListPair.allEq
             (fn (theorem1, theorem2) => same_thm theorem1 theorem2)
             (left, right)
       in
         same_list simp_rules [simp1, simp2] andalso
         same_list iff_rules [iff1, iff2] andalso
         same_list simp_controls
           [control1, control3, control2, control4] andalso
         same_list rest [fact1, fact2]
       end)

val _ =
  test
    ("directive recognition excludes every claset marker",
     fn () =>
       List.all
         (not o markerLib.is_directive)
         claset_marker_theorems andalso
       List.all
         (not o markerLib.is_directive)
         claset_marker_theorems)

val _ =
  test
    ("Del removes a rule from the invocation claset only",
     fn () =>
       let
         val name = "claset-marker-deleted"
         val base = add_sintros [(name, boolTheory.AND_INTRO_THM)] empty_cs
         val marked = Del name
         val (cs, rest) = process_claset_tags [marked] base
       in
         destDel marked = SOME name andalso List.null rest andalso
         has_named_rule name base andalso not (has_named_rule name cs)
       end)

val _ =
  test
    ("Del dispatch accepts a concrete type and rejects a non-variable",
     fn () =>
       let
         val name = "claset-marker-typed"
         val base = add_sintros [(name, boolTheory.AND_INTRO_THM)] empty_cs
         fun wrap term =
           Drule.EQT_ELIM (Drule.ISPEC term clasetMarkerTheory.Del_def)
         val marked = wrap (mk_var (name, bool))
         val malformed = wrap boolSyntax.T
         val (cs, rest) = process_claset_tags [malformed, marked] base
       in
         not (has_named_rule name cs) andalso
         ListPair.allEq (fn (left, right) => same_thm left right)
           (rest, [malformed])
       end)

val _ =
  test
    ("claset markers receive contiguous lowest-unused names",
     fn () =>
       let
         val ths = [boolTheory.TRUTH, boolTheory.AND_INTRO_THM,
                    boolTheory.IMP_ANTISYM_AX]
         val (cs, rest) = process_claset_tags (map SIntro ths) empty_cs
       in
         List.null rest andalso
         ListPair.allEq
           (fn (index, th) =>
              named_marker_is (marker_prefix ^ Int.toString index) th cs)
           ([0, 1, 2], ths)
       end)

val _ =
  test
    ("claset marker allocation fills a name gap without dropping rules",
     fn () =>
       let
         val base =
           add_sintros
             [(marker_prefix ^ "1", boolTheory.TRUTH)] empty_cs
         val ths = [boolTheory.AND_INTRO_THM, boolTheory.IMP_ANTISYM_AX]
         val (cs, rest) = process_claset_tags (map SIntro ths) base
       in
         List.null rest andalso length (rules_of cs) = 3 andalso
         named_marker_is (marker_prefix ^ "0") (hd ths) cs andalso
         named_marker_is (marker_prefix ^ "1") boolTheory.TRUTH cs andalso
         named_marker_is (marker_prefix ^ "2") (List.last ths) cs
       end)

val _ =
  test
    ("a rejected duplicate marker does not consume its name",
     fn () =>
       let
         val first = boolTheory.AND_INTRO_THM
         val second = boolTheory.IMP_ANTISYM_AX
         val input = [SIntro first, SIntro first, SIntro second]
         val (cs, rest) = process_claset_tags input empty_cs
       in
         List.null rest andalso length (rules_of cs) = 2 andalso
         named_marker_is (marker_prefix ^ "0") first cs andalso
         named_marker_is (marker_prefix ^ "1") second cs
       end)

val _ =
  test
    ("deleting a marker makes its lowest name reusable",
     fn () =>
       let
         val first = boolTheory.AND_INTRO_THM
         val second = boolTheory.IMP_ANTISYM_AX
         val input = [SIntro first, Del (marker_prefix ^ "0"), SIntro second]
         val (cs, rest) = process_claset_tags input empty_cs
       in
         List.null rest andalso length (rules_of cs) = 1 andalso
         named_marker_is (marker_prefix ^ "0") second cs
       end)

val _ =
  test
    ("claset marker processing passes other markers and plain theorems through",
     fn () =>
       let
         val plain = boolTheory.TRUTH
         val cong = markerLib.Cong (ASSUME p)
         val excl = markerLib.Excl "simp-only"
         val input = [cong, excl, plain]
         val (cs, rest) = process_claset_tags input empty_cs
       in
         List.null (rules_of cs) andalso
         ListPair.allEq (fn (th1, th2) => same_thm th1 th2) (input, rest)
       end)


val _ =
  test
    ("claset marker processing preserves mixed leftovers in input order",
     fn () =>
       let
         val plain1 = boolTheory.TRUTH
         val plain2 = boolTheory.IMP_F
         val cong = markerLib.Cong (ASSUME p)
         val input =
           [plain1, SIntro boolTheory.AND_INTRO_THM, cong,
            Del (marker_prefix ^ "0"), plain2,
            SIntro boolTheory.IMP_ANTISYM_AX]
         val (cs, rest) = process_claset_tags input empty_cs
       in
         named_marker_is (marker_prefix ^ "0") boolTheory.IMP_ANTISYM_AX cs
           andalso
         ListPair.allEq (fn (th1, th2) => same_thm th1 th2)
           (rest, [plain1, cong, plain2])
       end)

val _ =
  test
    ("inert generic and extension controls do not change invocation facts",
     fn () =>
       let
         val plain = boolTheory.TRUTH
         val markers =
           [markerLib.AC boolTheory.AND_CLAUSES boolTheory.OR_CLAUSES,
            markerLib.Cong boolTheory.AND_CLAUSES,
            markerLib.Split boolTheory.OR_CLAUSES,
            markerLib.ExclX "rule:claset-selftest",
            markerLib.mk_Req0
              (markerLib.Split boolTheory.OR_CLAUSES),
            markerLib.mk_ReqD
              (markerLib.ExclX "rule:claset-wrapped"),
            markerLib.Excl "claset-selftest",
            markerLib.ExclSF "claset-selftest",
            markerLib.FRAG "claset-selftest",
            markerLib.NoAsms,
            markerLib.IgnAsm [QUOTE "claset_ignored"],
            markerLib.Abbr [QUOTE "claset_abbreviation"]]
         val (baseline_cs, baseline_facts) =
           invocation_claset empty_cs [plain]
         val (with_markers_cs, with_markers_facts) =
           invocation_claset empty_cs
             (List.take (markers, 4) @ [plain] @
              List.drop (markers, 4))
       in
         List.all markerLib.is_directive markers andalso
         same_rules (rules_of baseline_cs) (rules_of with_markers_cs)
           andalso
         null (rules_of with_markers_cs) andalso
         ListPair.allEq (fn (left, right) => same_thm left right)
           (baseline_facts, with_markers_facts) andalso
         ListPair.allEq (fn (left, right) => same_thm left right)
           (with_markers_facts, [plain])
       end)

val _ =
  test
    ("content-bearing simp wrappers become invocation facts",
     fn () =>
       let
         val payload = boolTheory.IMP_CLAUSES
         val wrapped =
           markerLib.mk_Req0
             (markerLib.mk_ReqD (BoundedRewrites.Once payload))
         val (cs, facts) = invocation_claset empty_cs [wrapped]
       in
         markerLib.is_directive wrapped andalso
         null (rules_of cs) andalso
         ListPair.allEq (fn (left, right) => same_thm left right)
           (facts, [payload])
       end)

val _ =
  test
    ("mixed simp controls forward unchanged once, outside the facts",
     fn () =>
       let
         val plain = boolTheory.TRUTH
         val controls =
           [markerLib.Excl "claset-forward",
            markerLib.Split boolTheory.OR_CLAUSES,
            markerLib.ExclX "rule:claset-forward",
            markerLib.mk_Req0
              (markerLib.ExclX "rule:claset-forward"),
            BoundedRewrites.Once boolTheory.TRUTH]
         val extended = ref 0
         val called = ref 0
         val observed = ref false
         fun extend {simp_rules, iff_rules, claset, simpset, iff_prefix,
                     ...} =
           (extended := !extended + 1;
            observed :=
              (ListPair.allEq (fn (a, b) => same_thm a b)
                 (simp_rules, [boolTheory.AND_CLAUSES]) andalso
               ListPair.allEq (fn (a, b) => same_thm a b)
                 (iff_rules, [boolTheory.IMP_CLAUSES]));
            (claset, simpset))
         fun body cs ss forwarded environment =
           (called := !called + 1;
            observed := (!observed andalso Option.isSome ss andalso
              null (rules_of cs) andalso
              ListPair.allEq
                (fn (a, b) => same_thm a b andalso
                              Portable.pointer_eq (a, b))
                (forwarded, controls) andalso
              ListPair.allEq (fn (a, b) => same_thm a b)
                (map clasetFacts.source (clasetFacts.facts environment),
                 [plain]));
            Tactical.ALL_TAC)
         val tactic =
           with_invocation_fact_env
             {iff_prefix = "__selftest_controls_",
              extra_markers = fn ths => fn cs => (cs, ths),
              consumer = SafeFacts}
             body empty_cs (SOME {base = (), extend = extend})
             (hd controls :: Simp boolTheory.AND_CLAUSES :: plain ::
              Iff boolTheory.IMP_CLAUSES :: tl controls)
         val _ = tactic ([], boolSyntax.T) (Context.snapshot ())
       in
         !extended = 1 andalso !called = 1 andalso !observed
       end)

(* Assumption order is observable: it is the recency tie-break the search
   engines use, and what FIRST_ASSUM sees in a residue. *)
val _ =
  test
    ("inserted facts reach the assumptions in the order supplied",
     fn () =>
       let
         val facts =
           [boolTheory.IMP_F, boolTheory.EXCLUDED_MIDDLE,
            boolTheory.IMP_ANTISYM_AX]
         val goal = ([] : term list, boolSyntax.T)
       in
         case #1
                (Tactical.VALID (INSERT_FACTS_TAC facts) goal
                   (Context.snapshot())) of
             [(asl, _)] =>
               ListPair.allEq (fn (left, right) => Term.aconv left right)
                 (asl, map concl facts)
           | _ => false
       end)

(* An assumption's type variables are fixed, where Isabelle's [using]
   leaves a fact's schematic: a fact the goal cannot be read at is a
   fact the engines cannot use at all. *)
val pointwise_reflexivity =
  Tactical.prove
    (``!(f : 'a -> 'b) (x : 'a). f x = f x``,
     Tactical.THEN (Tactical.REPEAT Tactic.GEN_TAC, Tactic.REFL_TAC))

val _ =
  test
    ("a fact is inserted at the types the goal determines for it",
     fn () =>
       let
         val goal =
           ([] : term list, ``FST (p : 'c # 'd) = FST p``)
         val expected =
           concl
             (Thm.INST_TYPE
                [alpha |-> ``:'c # 'd``, beta |-> ``:'c``]
                pointwise_reflexivity)
       in
         case #1
                (Tactical.VALID
                   (INSERT_FACTS_TAC [pointwise_reflexivity]) goal
                   (Context.snapshot())) of
             [([assumption], _)] => Term.aconv assumption expected
           | _ => false
       end)

val _ =
  test
    ("fact insertion keeps the first match across reordered type bindings",
     fn () =>
       let
         val x = mk_var ("x", Type.alpha)
         val y = mk_var ("y", Type.beta)
         val fact =
           GENL [x, y]
             (CONJ (REFL (pairSyntax.mk_pair (x, y)))
                   (REFL (pairSyntax.mk_pair (y, x))))
         val goal = ([``(0, T) = (0, T)``, ``(T, 0) = (T, 0)``], T)
         fun inserted (build : thm list -> tactic) =
           case #1 (build [fact] goal (Context.snapshot ())) of
               [(assumptions, _)] => List.take
                 (assumptions, length assumptions - length (#1 goal))
             | _ => raise Fail "expected one goal after fact insertion"
         val ordinary = inserted INSERT_FACTS_TAC
         val measured =
           inserted (INSERT_FACTS_TAC_BUDGETED (searchBudget.unbounded ()))
       in
         length ordinary = 2 andalso
         ListPair.allEq (fn (left, right) => aconv left right)
           (ordinary, measured)
       end)

val _ =
  test
    ("rule origins preserve declaration order across claset edits",
     fn () =>
       let
         val theorem = boolTheory.TRUTH
         val key = concl theorem
         val spec = {kind = clasetRules.Intro, safe = true, prio = NONE}
         fun add name = add_derived_rule spec (name, theorem)
         fun origins cs = map #name (rules_for_derived_concl cs key)
         val first = add "origin_first" empty_cs
         val before_add = origins first
         val second = add "origin_second" first
         val before_remove = origins second
         val removed = remove_rule "origin_first" second
       in
         before_add = ["origin_first"] andalso
         before_remove = ["origin_second", "origin_first"] andalso
         origins removed = ["origin_second"] andalso
         origins first = before_add andalso origins second = before_remove
       end)

val _ =
  test
    ("budgeted literal insertion charges matching and admitted facts",
     fn () =>
       let
         val goal =
           ([] : term list, ``FST (p : 'c # 'd) = FST p``)
         val facts = [pointwise_reflexivity]
         val funded = searchBudget.unbounded ()
         fun assumptions tactic =
           case #1 (Tactical.VALID tactic goal (Context.snapshot())) of
               [(items, _)] => SOME items
             | _ => NONE
         val baseline = assumptions (INSERT_FACTS_TAC facts)
         val charged =
           assumptions (INSERT_FACTS_TAC_BUDGETED funded facts)
         val used = searchBudget.usage funded
         fun cut kind limits =
           let
             val budget = searchBudget.create limits
           in
             (ignore
                (assumptions
                   (INSERT_FACTS_TAC_BUDGETED budget facts));
              false)
             handle searchBudget.LimitReached (actual, usage) =>
               actual = kind andalso usage = searchBudget.usage budget
           end
       in
         (case (baseline, charged) of
              (SOME left, SOME right) =>
                ListPair.allEq
                  (fn (first, second) => Term.aconv first second)
                  (left, right)
            | _ => false) andalso
         #candidates used > 0 andalso #applications used > 0 andalso
         #normalization used > 0 andalso
         cut searchBudget.Candidate
           {candidates = SOME 0, applications = NONE,
            normalization = NONE} andalso
         cut searchBudget.Application
           {candidates = NONE, applications = SOME 0,
            normalization = NONE} andalso
         cut searchBudget.Normalization
           {candidates = NONE, applications = NONE,
            normalization = SOME 0}
       end)

(* A fact the goal's own type variables cover is usable as it stands,
   and which of its atoms happens to match where is no evidence of the
   instance wanted: the citation itself is one of the instances, so it
   stands among the assumptions and a match is offered beside it
   rather than in its place. *)
val _ =
  test
    ("a fact the goal's type variables cover is inserted as written",
     fn () =>
       let
         val goal =
           ([] : term list, ``FST (p : 'a # 'b) = FST p``)
       in
         case #1
                (Tactical.VALID
                   (INSERT_FACTS_TAC [pointwise_reflexivity]) goal
                   (Context.snapshot())) of
             [(assumptions, _)] =>
               List.exists
                 (fn assumption =>
                   Term.aconv assumption (concl pointwise_reflexivity))
                 assumptions
           | _ => false
       end)

(* Cover is by name and what decides the fact is where the goal
   applies it.  A fact at one type variable meeting a goal that
   mentions two, and states the fact at the second, was left assumed
   at the first alone, where nothing the goal states could meet it:
   [source_sorted_all_distinct_unique] at [:'a] against a goal about
   sorted mapped lists is the shape it was found on.  Neither the fact
   nor the goal below is a corpus entry. *)
val pair_projection = Thm.REFL ``FST ((x, x) : 'a # 'a)``

val _ =
  test
    ("a fact is inserted at a type the goal mentions elsewhere too",
     fn () =>
       let
         val goal =
           ([] : term list,
            ``FST (((g : 'a -> 'b) z, g z) : 'b # 'b) = FST (g z, g z)``)
         val instance =
           concl (Thm.INST_TYPE [alpha |-> beta] pair_projection)
       in
         case #1
                (Tactical.VALID
                   (INSERT_FACTS_TAC [pair_projection]) goal
                   (Context.snapshot())) of
             [(assumptions, _)] =>
               List.exists
                 (fn assumption => Term.aconv assumption instance)
                 assumptions andalso
               List.exists
                 (fn assumption =>
                   Term.aconv assumption (concl pair_projection))
                 assumptions
           | _ => false
       end)

(* A free variable the fact shares with the goal ties the fact to it:
   instantiating that variable's type would leave the fact speaking of
   a different variable, so such a match contributes nothing and the
   fact goes in as it is written. *)
val _ =
  test
    ("a fact tied to the goal by a shared variable keeps its types",
     fn () =>
       let
         val shared = Thm.REFL ``v : 'a``
         val goal = ([``(v : 'a) = v``], ``(3 : num) = 3``)
       in
         case #1
                (Tactical.VALID (INSERT_FACTS_TAC [shared]) goal
                   (Context.snapshot())) of
             [([assumption, _], _)] =>
               Term.aconv assumption (concl shared)
           | _ => false (* one inserted assumption: no instance is offered *)
       end)

(* Quantified variables are schematic even when their spelling matches a
   free goal parameter.  Compare the semantic instance sets, since a
   redundant citation of the original theorem is not significant. *)
val hygiene_x = ``x:'a``
val hygiene_z = ``z:'a``
val hygiene_fact_x = GEN hygiene_x
  (REFL ``FST ((x,x):'a#'a)``)
val hygiene_fact_z = GEN hygiene_z
  (REFL ``FST ((z,z):'a#'a)``)
val hygiene_goal : Abbrev.goal =
  ([], ``(FST ((u,u):'b#'b) = u) /\ ((x:'a) = x)``)

fun hygiene_inserted fact =
  case #1
    (Tactical.VALID (INSERT_FACTS_TAC [fact]) hygiene_goal
       (Context.snapshot())) of
      [(assumptions, _)] => assumptions
    | _ => raise Fail "hygiene_inserted: one goal expected"

val _ =
  test
    ("bound-variable spelling preserves fact type instances",
     fn () =>
       let
         val left = hygiene_inserted hygiene_fact_x
         val right = hygiene_inserted hygiene_fact_z
         val at_b =
           concl (Thm.INST_TYPE [alpha |-> beta] hygiene_fact_x)
         fun same_set xs ys =
           List.all
             (fn x => List.exists (Term.aconv x) ys) xs
       in
         same_set left right andalso same_set right left andalso
         List.exists (fn x => Term.aconv x at_b) left
       end)

val hygiene_fact_c =
  Thm.INST_TYPE
    [alpha |-> Type.mk_vartype "'hygiene_carrier"] hygiene_fact_z

val _ =
  test
    ("renaming a schematic carrier preserves the useful instance",
     fn () =>
       let
         val expected =
           concl (Thm.INST_TYPE [alpha |-> beta] hygiene_fact_x)
       in
         List.exists (fn assumption => Term.aconv assumption expected)
           (hygiene_inserted hygiene_fact_c)
       end)

val hygiene_p_def =
  new_definition ("hygiene_p_def", ``hygiene_p (v:'a) <=> T``)
val hygiene_behavior_fact =
  GEN hygiene_x
    (Tactical.prove
      (``hygiene_p (x:'a)``, Rewrite.REWRITE_TAC [hygiene_p_def]))
val hygiene_behavior_fact_z =
  GEN hygiene_z
    (Tactical.prove
      (``hygiene_p (z:'a)``, Rewrite.REWRITE_TAC [hygiene_p_def]))

val _ =
  test
    ("fact insertion checks scope at sites under an abstraction",
     fn () =>
       let
         val bound = REFL ``\x:'a. hygiene_p x``
         val free = REFL ``\x:'a. hygiene_p (y:'a)``
         val goal = ([], ``hygiene_p T``)
         val instantiated = Thm.INST_TYPE [alpha |-> Type.bool] free
         fun inserts insert fact expected =
           case Tactical.VALID (insert [fact]) goal (Context.snapshot ()) of
               ([([assumption], target)], _) =>
                 aconv assumption (concl expected) andalso
                 aconv target (#2 goal)
             | _ => false
       in
         List.all
           (fn insert =>
             inserts insert bound bound andalso
             inserts insert free instantiated)
           [INSERT_FACTS_TAC,
            INSERT_FACTS_TAC_BUDGETED (searchBudget.unbounded ())]
       end)

val _ =
  test
    ("the second carrier remains usable after binder collision",
     fn () =>
       let
         val goal : Abbrev.goal =
           ([], ``hygiene_p (u:'b) /\ ((x:'a) = x)``)
         val tactic =
           Tactical.THEN
             (INSERT_FACTS_TAC [hygiene_behavior_fact],
              Rewrite.ASM_REWRITE_TAC [])
       in
         case Tactical.VALID tactic goal (Context.snapshot()) of
             ([], validation) =>
               (ignore (validation []); true)
           | _ => false
       end)

(* The fixture is fixed before running any variant: two binder spellings,
   two schematic carrier spellings, and two goal carriers.  The extra
   reflexive conjunct deliberately shares the first binder's spelling. *)
val _ =
  test
    ("fact insertion is invariant across a small rename/carrier matrix",
     fn () =>
       let
         val source_carrier = Type.mk_vartype "'hygiene_matrix"
         val facts =
           [hygiene_behavior_fact, hygiene_behavior_fact_z,
            Thm.INST_TYPE [alpha |-> source_carrier]
              hygiene_behavior_fact,
            Thm.INST_TYPE [alpha |-> source_carrier]
              hygiene_behavior_fact_z]
         val goals : Abbrev.goal list =
           [([], ``hygiene_p (u:'b) /\ ((x:'a) = x)``),
            ([], ``hygiene_p (u:'c) /\ ((x:'a) = x)``)]
         fun closes tactic goal =
           case Lib.total
                  (fn () =>
                    Tactical.VALID tactic goal
                      (Context.snapshot ())) () of
               SOME ([], validation) =>
                 (ignore (validation []); true)
             | _ => false
         fun with_fact fact =
           Tactical.THEN
             (INSERT_FACTS_TAC [fact], Rewrite.ASM_REWRITE_TAC [])
       in
         List.all
           (fn goal =>
             not (closes (Rewrite.ASM_REWRITE_TAC []) goal)) goals
         andalso
         List.all
           (fn fact => List.all (closes (with_fact fact)) goals) facts
       end)

val hygiene_support = ``hygiene_support (v:'a):bool``
val hygiene_supported_fact =
  GEN hygiene_x
    (Drule.ADD_ASSUM hygiene_support
      (REFL ``FST ((x,x):'a#'a)``))

val _ =
  test
    ("support types remain fixed during literal insertion",
     fn () =>
       let
         val target = ``FST ((u,u):'b#'b) = u``
         val goal : Abbrev.goal = ([hygiene_support], target)
         val missing_support : Abbrev.goal = ([], target)
         val refused =
           (ignore
             (Tactical.VALID
               (INSERT_FACTS_TAC [hygiene_supported_fact])
               missing_support (Context.snapshot()));
            false) handle HOL_ERR _ => true
       in
         case #1
           (Tactical.VALID
             (INSERT_FACTS_TAC [hygiene_supported_fact]) goal
             (Context.snapshot())) of
             [([assumption, supported], _)] =>
               refused andalso
               Term.aconv assumption (concl hygiene_supported_fact) andalso
               Term.aconv supported hygiene_support
           | _ => false
       end)

val _ =
  test
    ("invocation facts keep provenance and freshen separate citations",
     fn () =>
       let
         val source = Thm.REFL ``citation_v:'a``
         val environment =
           clasetFacts.create
             ([], ``citation_target:'b = citation_target``)
             [source, source]
       in
         case clasetFacts.facts environment of
             [left, right] =>
               clasetFacts.source_id left = 0 andalso
               clasetFacts.source_id right = 1 andalso
               Term.aconv
                 (concl (clasetFacts.source left)) (concl source) andalso
               Term.aconv
                 (concl (clasetFacts.source right)) (concl source) andalso
               not
                 (Term.aconv
                   (concl (#theorem (clasetFacts.schematic_view left)))
                   (concl (#theorem (clasetFacts.schematic_view right))))
           | _ => false
       end)

val _ =
  test
    ("fact views preserve literal order and select equations for norm",
     fn () =>
       let
         val condition = ``citation_condition:bool``
         val equation = Thm.REFL ``citation_subject:'a``
         val conditional = Thm.DISCH condition equation
         val proposition = Thm.ASSUME condition
         val implication =
           Thm.DISCH condition (Thm.ASSUME condition)
         val environment =
           clasetFacts.create ([], boolSyntax.T)
             [equation, conditional, proposition, implication]
         val literals = clasetFacts.literal_views environment
         val equations = clasetFacts.equational_views environment
         fun ids views =
           map (fn ({source_id, ...} : clasetFacts.view) => source_id)
             views
       in
         ids literals = [0, 1, 2, 3] andalso
         ids equations = [0, 1] andalso
         ListPair.allEq
           (fn (view, source) =>
             Term.aconv (Thm.concl (#theorem view))
               (Thm.concl source))
           (literals,
            [equation, conditional, proposition, implication]) andalso
         ListPair.allEq
           (fn (view, source) =>
             Term.aconv (Thm.concl (#source view))
               (Thm.concl source))
           (equations, [equation, conditional])
       end)

val _ =
  test
    ("equational views retain a conjunct's source and support",
     fn () =>
       let
         val support = ``citation_conj_support:bool``
         val equation = Thm.REFL ``citation_conj_subject:'a``
         val conjunctive =
           Thm.CONJ equation (Thm.ASSUME support)
         val environment =
           clasetFacts.create ([], boolSyntax.T) [conjunctive]
       in
         case clasetFacts.equational_views environment of
             [{source_id, source, theorem, support = hypotheses}] =>
               source_id = 0 andalso
               Term.aconv (Thm.concl source)
                 (Thm.concl conjunctive) andalso
               can (Term.match_term (Thm.concl equation))
                 (Thm.concl theorem) andalso
               List.exists (Term.aconv support) hypotheses
           | _ => false
       end)

val _ =
  test
    ("equational views preserve selection order and normalization charges",
     fn () =>
       let
         val premise = ``citation_select_support:bool``
         val proposition = Thm.ASSUME premise
         val first = Thm.REFL ``citation_select_subject:'a``
         val second = Thm.REFL ``SUC citation_select_number``
         val source =
           Thm.CONJ (Thm.CONJ first proposition)
             (Thm.CONJ (Thm.CONJ proposition proposition) second)
         val charges = ref []
         val environment =
           clasetFacts.create_with_charge
             (fn kind => charges := kind :: !charges)
             ([], boolSyntax.T) [Thm.CONJ proposition proposition, source]
         val selected = clasetFacts.equational_views environment
         val selected_again = clasetFacts.equational_views environment
         val expected =
           case clasetFacts.facts environment of
               [_, entry] =>
                 let val {theorem, ...} = clasetFacts.schematic_view entry
                 in
                   [Thm.CONJUNCT1 (Thm.CONJUNCT1 theorem),
                    Thm.CONJUNCT2 (Thm.CONJUNCT2 theorem)]
                 end
             | _ => []
         fun check ({source_id, source = original, theorem, support} :
                      clasetFacts.view, piece) =
           source_id = 1 andalso
           Term.aconv (Thm.concl original) (Thm.concl source) andalso
           Term.aconv (Thm.concl theorem) (Thm.concl piece) andalso
           (case support of [hyp] => Term.aconv premise hyp | _ => false)
       in
         List.rev (!charges) =
           [searchBudget.Candidate, searchBudget.Candidate,
            searchBudget.Normalization] andalso
         ListPair.allEq check (selected, expected) andalso
         ListPair.allEq check (selected_again, expected)
       end)

val _ =
  test
    ("implication rule views preserve source identity and support",
     fn () =>
       let
         val premise = ``citation_rule_p (x:'a):bool``
         val support = ``citation_rule_q (x:'a):bool``
         val source = Thm.DISCH premise (Thm.ASSUME support)
         val environment =
           clasetFacts.create ([], boolSyntax.T)
             [source, Thm.REFL ``citation_rule_subject:'a``]
       in
         case map clasetFacts.implication_rule_view
                    (clasetFacts.facts environment) of
             [SOME view, NONE] =>
               #source_id view = 0 andalso
               Term.aconv (Thm.concl (#source view))
                 (Thm.concl source) andalso
               List.exists (Term.aconv support) (#support view) andalso
               can (Term.match_term (Thm.concl source))
                 (Thm.concl (#theorem view))
           | _ => false
       end)

val _ =
  test
    ("fact classification splits outer conjunctions before quantifiers",
     fn () =>
       let
         val x = ``citation_quantified:num``
         val equation = Thm.GEN x (Thm.REFL x)
         val condition = ``citation_condition:bool``
         val conditional = Thm.GEN x (Thm.DISCH condition (Thm.REFL x))
         val hidden = Thm.GEN x (Thm.CONJ (Thm.REFL x) (Thm.REFL x))
         val mixed = Thm.CONJ equation (Thm.CONJ hidden conditional)
         val environment =
           clasetFacts.create ([condition], boolSyntax.T) [mixed, conditional]
         val equations = clasetFacts.equational_views environment
       in
         map #source_id equations = [0, 0, 1] andalso
         ListPair.allEq
           (fn (view, expected) =>
             Term.aconv (Thm.concl (#theorem view)) (Thm.concl expected))
           (equations, [equation, conditional, conditional]) andalso
         map (Option.isSome o clasetFacts.implication_rule_view)
           (clasetFacts.facts environment) = [false, true]
       end)

val _ =
  test
    ("invocation fact support and shared free parameters stay fixed",
     fn () =>
       let
         val shared = Thm.REFL ``citation_shared:'a``
         val environment =
           clasetFacts.create
             ([``citation_shared:'a = citation_shared``],
              ``citation_target:'b = citation_target``)
             [shared, hygiene_supported_fact]
       in
         case clasetFacts.facts environment of
             [shared_fact, supported_fact] =>
               Term.aconv
                 (concl (#theorem
                   (clasetFacts.schematic_view shared_fact)))
                 (concl shared) andalso
               List.exists
                 (Term.aconv ``citation_shared:'a``)
                 (clasetFacts.fixed_terms shared_fact) andalso
               List.exists
                 (fn ty => Type.compare (ty, alpha) = EQUAL)
                 (clasetFacts.fixed_types supported_fact) andalso
               List.exists
                 (Term.aconv hygiene_support)
                 (#support
                   (clasetFacts.schematic_view supported_fact))
           | _ => false
       end)

val _ =
  test
    ("fact-site matching instantiates only schematic parameters",
     fn () =>
       let
         val loose =
           hd (clasetFacts.facts
             (clasetFacts.create ([], boolSyntax.T) [hygiene_fact_x]))
         val supported =
           hd (clasetFacts.facts
             (clasetFacts.create ([], boolSyntax.T)
               [hygiene_supported_fact]))
         val shared = Thm.REFL ``citation_shared:'a``
         val fixed =
           hd (clasetFacts.facts
             (clasetFacts.create
               ([``citation_shared:'a = citation_shared``],
                boolSyntax.T) [shared]))
         fun pattern entry =
           concl (#theorem (clasetFacts.schematic_view entry))
         val other = Thm.REFL ``citation_other:'a``
       in
         (case
            clasetFacts.match_view loose (pattern loose)
              (concl (Thm.INST_TYPE [alpha |-> beta] hygiene_fact_x))
          of
              SOME view =>
                Term.aconv (concl (#theorem view))
                  (concl (Thm.INST_TYPE [alpha |-> beta]
                    hygiene_fact_x))
            | NONE => false) andalso
         not (Option.isSome
           (clasetFacts.match_view supported (pattern supported)
             (concl (Thm.INST_TYPE [alpha |-> beta]
               hygiene_supported_fact)))) andalso
         not (Option.isSome
           (clasetFacts.match_view fixed (pattern fixed) (concl other)))
         andalso
         (case clasetFacts.match_view fixed (pattern fixed) (concl shared) of
              SOME view => Term.aconv (concl (#theorem view)) (concl shared)
            | NONE => false)
       end)

(* An invocation's facts are routed: a citation that is an implication
   becomes a rule of the invocation claset, where the search can
   instantiate it per use and resolve its premises, and is kept out of
   the assumptions, where a second copy of it only widens the search;
   one that is not an implication states at its own shape what the
   assumption already offers, so nothing is declared for it and it is
   assumed as before.  What the search receives is read off the body,
   which is handed the claset the invocation built, and what the goal
   receives is read off the residual goal.  Neither theorem below is a
   corpus entry. *)
fun invocation_run facts =
  let
    val seen = ref ([] : (rulespec * (string * thm)) list)
    fun body cs _ _ =
      (seen := rules_of cs; Tactical.ALL_TAC)
    val tactic =
      with_invocation_args
        {iff_prefix = "__selftest_invocation_iff_",
         extra_markers = fn theorems => fn cs => (cs, theorems)}
        body empty_cs NONE facts
    val (residual, _) =
      tactic ([] : term list, boolSyntax.T) (Context.snapshot())
  in
    (!seen, residual)
  end

fun invocation_claset_rules facts = #1 (invocation_run facts)

fun invocation_assumptions facts =
  case #2 (invocation_run facts) of
      [(asl, _)] => asl
    | _ => raise Fail "invocation_assumptions: one residual goal expected"

val invocation_implication =
  Thm.DISCH ``p : bool`` (Thm.ASSUME ``p : bool``)

val invocation_equation = Thm.REFL ``FST ((x, y) : 'a # 'b)``

val _ =
  test
    ("a supplied implication is a rule for the invocation too",
     fn () =>
       case invocation_claset_rules [invocation_implication] of
           [({kind = Dest, safe = false, ...}, (_, rule))] =>
             (* The search view has fresh schematic parameters, and
                canonicalization binds them for each application. *)
             let
               val supplied =
                 concl (Drule.SPEC_ALL invocation_implication)
               val declared = concl (Drule.SPEC_ALL rule)
             in
               can (Term.match_term supplied) declared andalso
               can (Term.match_term declared) supplied
             end
         | _ => false)

val _ =
  test
    ("invocation facts use the first free names across existing gaps",
     fn () =>
       let
         val prefix = "__invocation_fact_"
         val spec = {kind = clasetRules.Intro, safe = true, prio = NONE}
         val base = add_derived_rule spec (prefix ^ "0", boolTheory.TRUTH)
           (add_derived_rule spec (prefix ^ "2", boolTheory.TRUTH) empty_cs)
         val installed = ref ([] : string list)
         val tactic =
           with_invocation_args
             {iff_prefix = "__selftest_invocation_iff_",
              extra_markers = no_extra_markers}
             (fn cs => fn _ => fn _ =>
               (installed := List.mapPartial
                  (fn ({kind = clasetRules.Dest, ...}, (name, _)) => SOME name
                    | _ => NONE) (rules_of cs);
                Tactical.ALL_TAC))
             base NONE
             [invocation_implication, boolTheory.TRUTH,
              invocation_implication, invocation_implication]
         val (residual, _) =
           tactic ([], boolSyntax.T) (Context.snapshot ())
       in
         !installed = map (fn suffix => prefix ^ suffix) ["4", "3", "1"]
         andalso
         (case residual of [([truth], _)] => aconv truth boolSyntax.T
                          | _ => false)
       end)

val _ =
  test
    ("a supplied implication is not assumed as well",
     fn () => List.null (invocation_assumptions [invocation_implication]))

val _ =
  test
    ("safe consumer keeps an implication literally without a rule",
     fn () =>
       let
         val seen = ref ([] : (rulespec * (string * thm)) list)
         val tactic =
           with_invocation_fact_env
             {iff_prefix = "__selftest_safe_iff_",
              extra_markers = fn theorems => fn cs => (cs, theorems),
              consumer = SafeFacts}
             (fn cs => fn _ => fn _ => fn _ =>
               (seen := rules_of cs; Tactical.ALL_TAC))
             empty_cs NONE [invocation_implication]
         val (residual, _) =
           tactic ([] : term list, boolSyntax.T) (Context.snapshot())
       in
         List.null (!seen) andalso
         (case residual of
              [(assumptions, _)] =>
                (case assumptions of
                     [assumption] =>
                       Term.aconv assumption
                         (concl invocation_implication)
                   | _ => false)
            | _ => false)
       end)

val _ =
  test
    ("budgeted fact environment charges classification and lazy views",
     fn () =>
       let
         fun run budget consumer =
           with_invocation_fact_env_budgeted budget
             {iff_prefix = "__selftest_budget_iff_",
              extra_markers = fn theorems => fn cs => (cs, theorems),
              consumer = consumer}
             (fn _ => fn _ => fn _ => fn _ => Tactical.ALL_TAC)
             empty_cs NONE [invocation_implication]
             ([], boolSyntax.T) (Context.snapshot ())
         fun cutoff kind limits =
           let
             val budget = searchBudget.create limits
           in
             (ignore (run budget SearchFacts); false)
             handle searchBudget.LimitReached (actual, used) =>
               actual = kind andalso
               used = searchBudget.usage budget
           end
       in
         cutoff searchBudget.Candidate
           {candidates = SOME 0, applications = NONE,
            normalization = NONE} andalso
         cutoff searchBudget.Normalization
           {candidates = NONE, applications = NONE,
            normalization = SOME 0} andalso
         cutoff searchBudget.Application
           {candidates = NONE, applications = SOME 0,
            normalization = NONE}
       end)

val _ =
  test
    ("certified fact transport keeps source identity and support",
     fn () =>
       let
         val source =
           Thm.ASSUME ``(\value : bool. value) T``
         val environment =
           clasetFacts.create ([], boolSyntax.T) [source]
         val view = hd (clasetFacts.schematic_views environment)
         val transported =
           clasetFacts.transport_view
             (Conv.REDEPTH_CONV BETA_CONV) view
       in
         #source_id transported = #source_id view andalso
         same_thm (#source transported) (#source view) andalso
         ListPair.allEq (fn (left, right) => Term.aconv left right)
           (#support transported, #support view) andalso
         Term.aconv (concl (#theorem transported)) boolSyntax.T
       end)

val _ =
  test
    ("transported support includes a conditional rewrite obligation",
     fn () =>
       let
         val premise = ``transport_source_p:bool``
         val bridge =
           ``transport_source_p <=> transport_target_q``
         val source = Thm.ASSUME premise
         val view =
           clasetFacts.literal_view
             (hd (clasetFacts.facts
               (clasetFacts.create ([], premise) [source])))
         val transported =
           clasetFacts.transport_view
             (Conv.REWR_CONV (Thm.ASSUME bridge)) view
         val support = #support transported
       in
         Term.aconv (concl (#theorem transported))
           ``transport_target_q:bool`` andalso
         List.exists (Term.aconv premise) support andalso
         List.exists (Term.aconv bridge) support andalso
         ListPair.allEq
           (fn (left, right) => Term.aconv left right)
           (support, Thm.hyp (#theorem transported))
       end)

val _ =
  test
    ("a supplied fact that is not an implication declares nothing",
     fn () => List.null (invocation_claset_rules [invocation_equation]))

val _ =
  test
    ("a supplied fact that is not an implication is still assumed",
     fn () =>
       case invocation_assumptions [invocation_equation] of
           [assumption] =>
             Term.aconv assumption (concl invocation_equation)
         | _ => false)

(* The shared work meter is what lets a caller ask how much search a
   proof did.  Nesting must not lose the enclosing measurement. *)
val _ =
  test
    ("invocation budget separates candidate and application work",
     fn () =>
       let
         val budget =
           searchBudget.create
             {candidates = SOME 2, applications = SOME 1,
              normalization = SOME 0}
         fun nested () = searchBudget.charge budget searchBudget.Candidate
         val _ = nested ()
         val _ = nested ()
         val _ =
           searchBudget.charge budget searchBudget.Application
         val candidate_limit =
           (searchBudget.charge budget searchBudget.Candidate; false)
           handle searchBudget.LimitReached
             (searchBudget.Candidate, used) =>
               #candidates used = 2 andalso #applications used = 1
         val norm_limit =
           (searchBudget.charge budget searchBudget.Normalization; false)
           handle searchBudget.LimitReached
             (searchBudget.Normalization, used) =>
               #normalization used = 0
         val invalid =
           (ignore
              (searchBudget.create
                {candidates = SOME ~1, applications = NONE,
                 normalization = NONE});
            false) handle HOL_ERR _ => true
         val _ = searchBudget.extend budget searchBudget.Candidate 1
         val _ = searchBudget.extend budget searchBudget.Normalization 1
         val _ = searchBudget.charge budget searchBudget.Candidate
         val _ = searchBudget.charge budget searchBudget.Normalization
         val invalid_extension =
           (searchBudget.extend budget searchBudget.Application ~1;
            false) handle HOL_ERR _ => true
       in
         candidate_limit andalso norm_limit andalso invalid andalso
         invalid_extension andalso
         #candidates (searchBudget.usage budget) = 3 andalso
         #normalization (searchBudget.usage budget) = 1
       end)

val _ =
  test
    ("child turns retain usage and charge the invocation once",
     fn () =>
       let
         val invocation =
           searchBudget.create
             {candidates = SOME 2, applications = NONE,
              normalization = NONE}
         val turn =
           searchBudget.child invocation
             {candidates = SOME 1, applications = NONE,
              normalization = NONE}
         val _ = searchBudget.charge turn searchBudget.Candidate
         val local_limit =
           (searchBudget.charge turn searchBudget.Candidate; false)
           handle searchBudget.LimitReached
                    (searchBudget.Candidate, used) =>
                    #candidates used = 1
                | _ => false
         val _ = searchBudget.extend turn searchBudget.Candidate 2
         val _ = searchBudget.charge turn searchBudget.Candidate
         val parent_limit =
           (searchBudget.charge turn searchBudget.Candidate; false)
           handle searchBudget.LimitReached
                    (searchBudget.Candidate, used) =>
                    #candidates used = 2
                | _ => false
       in
         local_limit andalso parent_limit andalso
         not (searchBudget.available invocation
                searchBudget.Candidate) andalso
         #candidates (searchBudget.usage turn) = 2 andalso
         #candidates (searchBudget.usage invocation) = 2
       end)

val _ =
  test
    ("nested budget rejection leaves every counter unchanged",
     fn () =>
       let
         fun limits n =
           {candidates = SOME n, applications = NONE, normalization = NONE}
         val root = searchBudget.create (limits 1)
         val middle = searchBudget.child root (limits 1)
         val leaf = searchBudget.child middle (limits 2)
         fun charge budget = searchBudget.charge budget searchBudget.Candidate
         fun counts () =
           map (#candidates o searchBudget.usage) [root, middle, leaf]
         fun refuses expected =
           (charge leaf; false)
           handle searchBudget.LimitReached (searchBudget.Candidate, used) =>
             #candidates used = expected
         val _ = charge root
         val root_rejected = refuses 1 andalso counts () = [1, 0, 0]
         val _ = searchBudget.extend root searchBudget.Candidate 1
         val _ = charge leaf
       in
         root_rejected andalso refuses 1 andalso counts () = [2, 1, 1]
       end)

val _ =
  test
    ("the search-work meter reports each run and keeps the enclosing one",
     fn () =>
       let
         val (inner, outer) =
           searchWork.measure
             (fn () =>
               (searchWork.note_expansion ();
                #2 (searchWork.measure
                     (fn () =>
                       (searchWork.note_expansion ();
                        searchWork.note_expansion ())))))
       in
         #expansions inner = 2 andalso #expansions outer = 3
       end)

val _ =
  test
    ("the search-work meter restores the enclosing run after an exception",
     fn () =>
       let
         val (_, outer) =
           searchWork.measure
             (fn () =>
               (searchWork.note_expansion ();
                (searchWork.measure
                   (fn () =>
                     (searchWork.note_expansion ();
                      raise Fail "work meter selftest"))
                 handle Fail _ => ((), searchWork.zero))))
       in
         #expansions outer = 2
       end)

(* Disjoint sites need a single compatible type instance of the fact. *)
fun joined_fact_fixture body =
  let
    open boolLib arithmeticTheory listTheory
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = Theory.new_theory "joinedFactFixture"
        val p_def =
          new_definition ("join_p_def", ``join_p (x:'a) = T``)
        val q_def =
          new_definition ("join_q_def", ``join_q (x:'a) = T``)
        val r_def =
          new_definition ("join_r_def", ``join_r (x:'a) = T``)
        val target_def =
          new_definition ("join_target_def", ``join_target = T``)
        val fact =
          GENL [``x:'a``, ``y:'b``, ``z:'c``]
            (CONJ (EQT_ELIM (ISPEC ``x:'a`` p_def))
               (CONJ (EQT_ELIM (ISPEC ``y:'b`` q_def))
                  (EQT_ELIM (ISPEC ``z:'c`` r_def))))
        val target = lhs (concl target_def)
        fun inserted insert fact assumptions =
          let
            val (remaining, validate) =
              Tactical.VALID
                (insert [fact])
                (assumptions, target) (Context.snapshot ())
            val theorem = validate [EQT_ELIM target_def]
            val _ =
              if aconv (concl theorem) target andalso null (hyp theorem)
              then () else raise Fail "fact insertion validation"
          in
            case remaining of
                [(current, _)] =>
                  List.filter
                    (fn tm => length (fst (strip_forall tm)) = 3) current
              | _ => raise Fail "one insertion goal expected"
          end
        fun shapes facts =
          map
            (map
               (fn v =>
                 let val ty = type_of v in
                   if Type.is_vartype ty then "fresh"
                   else if ty = numSyntax.num then "num"
                   else if ty = Type.bool then "bool"
                   else if ty = listSyntax.mk_list_type numSyntax.num
                   then "num list"
                   else Parse.type_to_string ty
                 end) o fst o strip_forall) facts
        fun inspect label assumptions =
          let
            val insert =
              clasetLib.INSERT_FACTS_TAC_BUDGETED (searchBudget.unbounded ())
            val result = shapes (inserted insert fact assumptions)
          in result end
      in
        body (fact, inserted, shapes, inspect)
      end
  in
    Portable.finally (fn () => Context.restore saved) run ()
  end;

val joined_fixture_result =
  joined_fact_fixture
    (fn (fact, inserted, shapes, inspect) =>
      let
        val two = inspect "TWO_SITES" [``join_p (0:num)``, ``join_q T``]
        val three =
          inspect "THREE_SITES"
            [``join_p (0:num)``, ``join_q T``, ``join_r ([]:num list)``]
        val repeated_sites =
          [``join_p (0:num) /\ join_p (1:num)``, ``join_q T /\ join_q F``,
           ``join_r ([]:num list)``]
        val repeated_measured = inspect "REPEATED_SITES" repeated_sites
        val repeated_ordinary =
          shapes (inserted clasetLib.INSERT_FACTS_TAC fact repeated_sites)
        val alternative_sites =
          [``join_p (0:num)``, ``join_p T``, ``join_q T``,
           ``join_r ([]:num list)``]
        val alternatives = inspect "ALTERNATIVES" alternative_sites
        val alternatives_ordinary =
          shapes (inserted clasetLib.INSERT_FACTS_TAC fact alternative_sites)
        val conflict =
          inspect "CONFLICT" [``join_p (0:num)``, ``join_p T``]
        val binders = fst (strip_forall (concl fact))
        val renamed_binders =
          ListPair.map
            (fn (name, binder) => mk_var (name, type_of binder))
            (["renamed_x", "renamed_y", "renamed_z"], binders)
        val renamed = GENL renamed_binders (Drule.SPECL renamed_binders fact)
        val renamed_two =
          shapes
            (inserted
               (clasetLib.INSERT_FACTS_TAC_BUDGETED (searchBudget.unbounded ()))
               renamed
               [``join_p (0:num)``, ``join_q T``])
        val budget =
          searchBudget.create
            {candidates = SOME 0, applications = NONE,
             normalization = NONE}
        val cutoff =
          ((inserted (clasetLib.INSERT_FACTS_TAC_BUDGETED budget)
              fact [``join_p (0:num)``]; false)
           handle searchBudget.LimitReached
                    (searchBudget.Candidate, _) => true)
      in
        two = [["fresh", "bool", "fresh"],
                  ["num", "fresh", "fresh"],
                  ["num", "bool", "fresh"]] andalso
           three = [["fresh", "fresh", "num list"],
                    ["fresh", "bool", "fresh"],
                    ["num", "fresh", "fresh"],
                    ["num", "bool", "num list"]] andalso
           conflict = [["num", "fresh", "fresh"],
                       ["bool", "fresh", "fresh"]] andalso
           alternatives =
             [["fresh", "fresh", "num list"],
              ["fresh", "bool", "fresh"],
              ["num", "fresh", "fresh"],
              ["bool", "fresh", "fresh"],
              ["num", "bool", "num list"],
              ["bool", "bool", "num list"]] andalso
           alternatives_ordinary = alternatives andalso
           repeated_ordinary = three andalso repeated_measured = three andalso
           two = renamed_two andalso cutoff
      end);

val _ =
  (tprint "compatible partial fact types admit only maximal joins";
   if joined_fixture_result then OK () else die "compatible join missing");

val _ =
  test
    ("wide partial fact types give the same ordered joins under a meter",
     fn () =>
       joined_fact_fixture
         (fn (fact, inserted, _, _) =>
           let
             val binders =
               [``x:'a # 'b # 'c # 'd``, ``y:'a # 'b # 'c # 'e``,
                ``z:'f``]
             val wide = GENL binders (Drule.ISPECL binders fact)
             val compatible =
               [``join_p (0:num, T, []:num list, SOME T)``,
                ``join_q (0:num, T, []:num list, SOME 0)``,
                ``join_r T``]
             val conflicting =
               ``join_q (T, T, []:num list, SOME 0)`` :: compatible
             fun shape tm =
               map (fn binder =>
                 let val ty = type_of binder in
                   case Type.type_vars ty of
                       [] => (0, SOME ty)
                     | vars => (length vars, NONE)
                 end) (fst (strip_forall tm))
             val full =
               [(0, SOME (type_of ``(0:num, T, []:num list, SOME T)``)),
                (0, SOME (type_of ``(0:num, T, []:num list, SOME 0)``)),
                (0, SOME Type.bool)]
             fun same_joins assumptions =
               let
                 val ordinary = map shape
                   (inserted clasetLib.INSERT_FACTS_TAC wide assumptions)
                 val metered = map shape
                   (inserted
                     (clasetLib.INSERT_FACTS_TAC_BUDGETED
                       (searchBudget.unbounded ())) wide assumptions)
               in
                 ordinary = metered andalso List.exists (equal full) ordinary
               end
           in
             same_joins compatible andalso same_joins conflicting
           end))

(* bounded_memo keeps the values of the most recently asked-for keys.
   The counter records every call of the computation. *)
val _ =
  test ("bounded_memo answers recent keys without recomputing",
   fn () =>
      let
        val computed = ref 0
        val memo = memoUtil.bounded_memo 2 (Lib.curry (op =))
                     (fn k : int => (computed := !computed + 1; k * 10))
        val first = memo 1
        val second = memo 2
        val back = memo 1       (* within 2 entries: a hit *)
        val after_hits = !computed
        val _ = memo 3          (* evicts 2, the least recently asked for *)
        val kept = memo 1       (* the hit moved 1 to the front: kept *)
        val kept_count = !computed
        val _ = memo 2          (* evicted, so recomputed *)
      in
        first = 10 andalso second = 20 andalso back = 10 andalso
        after_hits = 2 andalso kept = 10 andalso kept_count = 3 andalso
        !computed = 4
      end)

val _ =
  test ("bounded_memo with a bound of 1 is a single-entry memo",
   fn () =>
      let
        val computed = ref 0
        val memo = memoUtil.bounded_memo 1 (Lib.curry (op =))
                     (fn k : int => (computed := !computed + 1; k))
        val _ = (memo 1; memo 1)
        val one = !computed
        val _ = (memo 2; memo 1)
      in
        one = 1 andalso !computed = 3
      end)

val _ =
  test ("bounded_memo with a bound below 1 keeps no entry",
   fn () =>
      let
        fun recomputes n =
          let
            val computed = ref 0
            val memo = memoUtil.bounded_memo n (Lib.curry (op =))
                         (fn k : int => (computed := !computed + 1; k))
            val _ = (memo 1; memo 1; memo 2; memo 1)
          in !computed end
      in
        recomputes 0 = 4 andalso recomputes ~3 = 4
      end)

(* The trace level is read from the context it is asked in, not from
   the global flag. *)
local
  val emitted = ref ([] : string list)
  val tracer =
    traceUtil.create {group = "traceUtil_test", max = 3,
                      emit = fn m => emitted := m :: !emitted}
  fun shown level k =
    (emitted := [];
     traceUtil.trace level k (fn () => "message");
     not (null (!emitted)))
  fun level_in n =
    traceUtil.level_of tracer
      (HOLFlags.set_flagC (traceUtil.flag tracer, n) (Context.snapshot ()))
  val global = traceUtil.level_of tracer (Context.snapshot ())
  (* A level whose context says n while the global flag says 3. *)
  fun level_under_global n =
    HOLFlags.with_flags [(traceUtil.flag tracer, 3)] (fn () => level_in n) ()
  val levels = [global, level_in 2, level_in 3, traceUtil.silent]
in
  val _ = test ("traceUtil reads the level from the given context",
                fn () =>
                  not (shown global 1) andalso
                  shown (level_in 2) 2 andalso
                  not (shown (level_in 2) 3) andalso
                  shown (level_in 3) 3 andalso
                  not (shown (level_in 0) 1))
  val _ = test ("traceUtil ignores a higher global flag",
                fn () =>
                  let
                    val off = level_under_global 0
                    val one = level_under_global 1
                  in
                    not (shown off 1) andalso not (shown off 3) andalso
                    shown one 1 andalso not (shown one 2)
                  end)
  val _ = test ("traceUtil.silent shows nothing and forces nothing",
                fn () =>
                  let
                    val forced = ref false
                    val _ = emitted := []
                    val _ = traceUtil.trace traceUtil.silent 0
                              (fn () => (forced := true; "message"))
                  in
                    null (!emitted) andalso not (!forced) andalso
                    not (traceUtil.enabled traceUtil.silent 1)
                  end)
  val _ = test ("traceUtil.enabled agrees with trace",
                fn () =>
                  List.all
                    (fn level =>
                       List.all (fn k => traceUtil.enabled level k =
                                         shown level k)
                                [0, 1, 2, 3])
                    levels)
end

val _ =
  test
    ("invocation facts retain fixed variable order with overlapping support",
     fn () =>
       let
         val premise = ``fact_fixed_p /\ fact_fixed_q``
         val body = ``(fact_fixed_p /\ fact_loose) /\ fact_shared``
         val theorem = Drule.ADD_ASSUM premise (Thm.REFL body)
         val shared = ``fact_shared:bool``
         val supported = Term.free_varsl [premise]
         fun check_fixed goal_variables =
           let
             val entry = hd
               (clasetFacts.facts
                 (clasetFacts.create (goal_variables, boolSyntax.T) [theorem]))
             val shared_variables = List.filter
               (fn tm => Lib.op_mem Term.aconv tm goal_variables)
               (Term.free_vars (concl theorem))
             val expected = Lib.op_union Term.aconv supported shared_variables
             val view = clasetFacts.schematic_view entry
             val pattern = concl (#theorem view)
             val site = concl (Thm.REFL
               ``(fact_fixed_p /\ replacement) /\ fact_shared``)
             val bad_site = concl (Thm.REFL
               ``(replacement_p /\ replacement) /\ fact_shared``)
           in
             same_terms (clasetFacts.fixed_terms entry) expected andalso
             Option.isSome (clasetFacts.match_view entry pattern site) andalso
             not (Option.isSome
               (clasetFacts.match_view entry pattern bad_site))
           end
       in
         check_fixed [] andalso check_fixed [shared] andalso
         check_fixed [shared, ``fact_fixed_p:bool``]
       end)
