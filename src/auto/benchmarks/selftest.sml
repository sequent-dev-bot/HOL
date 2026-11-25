open HolKernel testutils

(* Preserve the historical convenience shape used by these checks while
   the tactic kernel carries an explicit context. *)
structure SelfTestTactical = Tactical
structure Tactical =
struct
  open SelfTestTactical
  fun VALID tactic goal =
    SelfTestTactical.VALID tactic goal (Context.snapshot())
  fun TAC_PROOF (goal, tactic) =
    let
      val (goals, validation) =
        SelfTestTactical.VALID tactic goal (Context.snapshot())
    in
      if null goals then validation []
      else raise Fail "unsolved goals"
    end
  fun prove (term, tactic) = TAC_PROOF (([], term), tactic)
end

fun check (name, predicate) =
  (tprint name;
   if predicate () then OK () else die "failed")

fun raises thunk =
  ((thunk (); false)
   handle Portable.Interrupt => raise Portable.Interrupt
        | HOL_ERR _ => true)

fun raises_with fragments thunk =
  ((thunk (); false)
   handle Portable.Interrupt => raise Portable.Interrupt
        | HOL_ERR error =>
            List.all
              (fn fragment =>
                String.isSubstring fragment (Feedback.message_of error))
              fragments)

val provenance =
  {file = "src/HOL/HOL.thy", line = 1, commit = "f7e02b7e"}

val p = mk_var ("bench_unit_p", bool)
val q = mk_var ("bench_unit_q", bool)

val solved_goal : benchLib.corpus_goal =
  {id = "unit-solved", goal = boolSyntax.mk_eq (p, p),
   source_method = "simp", recipe = benchLib.Invoke (benchLib.Simp, []),
   excl = [],
   provenance = provenance, representative = true}

(* A hand-built fixture names its own recipe, which is what makes it a
   fixture: the corpus reaches [benchLib.prepare_goal] only through
   [benchDerive.prepare], where the recipe is derived. *)
fun prepared ({id, goal, source_method, recipe, provenance,
               representative, ...} : benchLib.corpus_goal) =
  benchLib.prepare_goal recipe
    {id = id, goal = goal, source_method = source_method,
     provenance = provenance, representative = representative}

(* ---- the time budget has to preempt, not merely label it --------- *)

(* A budget that merely labels an overrun would let one goal run
   without bound, so assert that the payload is interrupted before it
   completes, not just that the verdict labels an overrun. Scheduling
   pauses must not impose a separate wall-clock acceptance deadline.
   [Timeout.apply] runs its payload under the caller's thread
   attributes; those are observed here to admit the timer's interrupt,
   which is what makes the cut-off real.

   The payload stops itself after ten seconds so that a regression here
   fails rather than hanging the suite. *)
val _ =
  check
    ("a runaway computation is cut off at its budget",
     fn () =>
       let
         val completed = ref false
         fun spin deadline =
           if Time.> (Time.now (), deadline) then completed := true
           else spin deadline
         val outcome =
           benchLib.within_budget (Time.fromSeconds 1)
             (fn () => spin (Time.+ (Time.now (), Time.fromSeconds 10)))
       in
         not (isSome outcome) andalso not (!completed)
       end)

val failed_goal : benchLib.corpus_goal =
  {id = "unit-failed", goal = p,
   source_method = "simp", recipe = benchLib.Invoke (benchLib.Simp, []),
   excl = [],
   provenance = provenance, representative = true}

val failed_shortfall : benchLib.shortfall =
  {id = "unit-failed", cause = benchLib.UnderIteration,
   date = "2026-08-10", note = "unit-test accounting sentinel"}

val translation_gap : benchLib.shortfall =
  {id = "unit-untranslatable", cause = benchLib.TranslationGap,
   date = "2026-08-10", note = "unit-test translation sentinel"}

val _ =
  check
    ("benchmark harness records a mapped-tactic success",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (benchLib.Invoke (benchLib.Simp, [])) solved_goal))

(* On the fake clock, simpset preparation alone exceeds the budget.
   The real tactic runs with the normal timeout and reports one tick. *)
val _ =
  check
    ("the time reported for a goal is not the time spent preparing it",
     fn () =>
       let
         val clock = ref Time.zeroTime
         val tick = Time.fromSeconds 1
         fun now () =
           let val reading = !clock
           in clock := Time.+ (reading, tick); reading end
         fun prepare build =
           let val simpset = build ()
           in clock := Time.+ (!clock, Time.fromSeconds 10); simpset end
         val outcome =
           benchLib.run_goal_with_timing {now = now, prepare = prepare}
             (Time.fromSeconds 5)
             (benchLib.Invoke (benchLib.Simp, [])) solved_goal
       in
         case outcome of
             benchLib.SOLVED reported =>
               Time.compare (reported, tick) = EQUAL andalso
               Time.compare (!clock, Time.fromSeconds 12) = EQUAL
           | _ => false
       end)

val _ =
  check
    ("benchmark harness enforces a zero time budget",
     fn () =>
       case benchLib.run_goal Time.zeroTime
              (benchLib.Invoke (benchLib.Simp, [])) solved_goal of
           benchLib.TIMEOUT => true
         | _ => false)

val _ =
  check
    ("benchmark harness accepts exact solved and shortfall sets",
     fn () =>
       let
         val result =
           benchLib.run_family
             {family = "unit",
              goals = map prepared [solved_goal, failed_goal],
              shortfalls = [failed_shortfall],
              budget = Time.fromSeconds 5, battery = [], level = 1}
       in
         length (#gated result) = 2 andalso null (#battery result)
       end)

(* HOLBENCHSHORTFALLSONLY and HOLBENCHFAMILY with HOLBENCHGOAL restrict
   a debugging run to part of the corpus.  They were read inside
   [run_family], which measures the hand-built families above as well:
   with the first set, the family two checks up lost the goal it
   asserts an exact set for and the suite failed on a switch that is
   supposed to select goals.  The restriction is an argument now, so
   what it selects is checkable here without an environment. *)
val restriction_family =
  {family = "unit", goals = map prepared [solved_goal, failed_goal],
   shortfalls = [failed_shortfall]}

fun restricted_ids restriction =
  map #id (benchLib.restrict restriction restriction_family)

val _ =
  check
    ("an unrestricted corpus run keeps every goal of the family",
     fn () =>
       restricted_ids {shortfalls_only = false, goals_wanted = NONE} =
         ["unit-solved", "unit-failed"])

val _ =
  check
    ("a shortfalls-only run keeps the goals with a record and no others",
     fn () =>
       restricted_ids {shortfalls_only = true, goals_wanted = NONE} =
         ["unit-failed"])

val _ =
  check
    ("a named-goal restriction selects within its own family",
     fn () =>
       restricted_ids
         {shortfalls_only = false,
          goals_wanted = SOME ("unit", ["unit-failed"])} =
         ["unit-failed"])

val _ =
  check
    ("a named-goal restriction leaves another family whole",
     fn () =>
       restricted_ids
         {shortfalls_only = false,
          goals_wanted = SOME ("listmap", ["unit-failed"])} =
         ["unit-solved", "unit-failed"])

val _ =
  check
    ("benchmark accounting rejects a newly solved registered shortfall",
     fn () =>
       raises
         (fn () =>
           benchLib.assert_accounting
             {family = "unit-improvement", goals = [failed_goal],
              shortfalls = [failed_shortfall],
              gated = [("unit-failed", benchLib.SOLVED Time.zeroTime)]}))

val _ =
  check
    ("benchmark accounting rejects an unregistered failure",
     fn () =>
       raises
         (fn () =>
           benchLib.assert_accounting
             {family = "unit-regression", goals = [solved_goal],
             shortfalls = [],
             gated = [("unit-solved", benchLib.FAILED "sentinel")]}))

val _ =
  check
    ("benchmark accounting accepts a goal-free translation gap",
     fn () =>
       (benchLib.assert_accounting
          {family = "unit-translation", goals = [solved_goal],
           shortfalls = [translation_gap],
           gated = [("unit-solved", benchLib.SOLVED Time.zeroTime)]};
        true))

val _ =
  check
    ("benchmark accounting rejects a goal-free non-translation gap",
     fn () =>
       raises
         (fn () =>
           benchLib.assert_accounting
             {family = "unit-unknown", goals = [solved_goal],
              shortfalls = [failed_shortfall],
              gated = [("unit-solved", benchLib.SOLVED Time.zeroTime)]}))

val _ =
  check
    ("benchmark accounting reports all aconv pairs in corpus order",
     fn () =>
       let
         fun entry id variable body : benchLib.corpus_goal =
           {id = id, goal = boolSyntax.mk_forall (variable, body),
            source_method = "simp",
            recipe = benchLib.Invoke (benchLib.Simp, []), excl = [],
            provenance = provenance, representative = true}
         val r = mk_var ("bench_unit_r", bool)
         val goals =
           [entry "a" p p, entry "b" p (boolSyntax.mk_neg p),
            entry "c" q q, entry "d" q (boolSyntax.mk_neg q), entry "e" r r]
       in
         raises_with ["aconv corpus goals: a=c, a=e, b=d, c=e"]
           (fn () =>
             benchLib.assert_accounting
               {family = "unit-aconv", goals = goals, shortfalls = [],
                gated = []})
       end)

val analogue = Drule.SPECL [p, q] boolTheory.OR_INTRO_THM1
val analogue_spec =
  {kind = clasetRules.Intro, safe = false, prio = NONE}
val analogue_cs =
  clasetLib.add_rule analogue_spec
    ("unit$self_analogue", analogue) clasetLib.empty_cs
val excluded_goal : benchLib.corpus_goal =
  {id = "unit-exclusion", goal = boolSyntax.mk_disj (p, q),
   source_method = "blast", recipe = benchLib.Invoke (benchLib.Blast, []),
   excl = [{name = "unit$self_analogue", theorem = analogue}],
   provenance = provenance, representative = true}

val _ =
  check
    ("self-analogue exclusion removes every aconv claset copy",
     fn () =>
       let
         val name = "unit$self_analogue"
         val aliases =
           [".__clasimp_iff_intro", ".__clasimp_iff_dest",
            ".__clasimp_iff_elim"]
         fun add suffix claset =
           clasetLib.add_derived_rule analogue_spec
             (name ^ suffix, analogue) claset
         val with_aliases =
           List.foldl (fn (suffix, claset) => add suffix claset)
             analogue_cs aliases
       in
         benchLib.exclusions_effective with_aliases excluded_goal andalso
         not
           (benchLib.exclusions_effective
              (add ".__clasimp_iff_intro_extra" with_aliases) excluded_goal)
       end)

val _ =
  check
    ("level-2 battery outcomes are recorded but not gated",
     fn () =>
       let
         val result =
           benchLib.run_family
             {family = "unit-battery",
              goals = map prepared [solved_goal],
              shortfalls = [], budget = Time.fromSeconds 5,
              battery = [benchLib.Auto, benchLib.Aesop], level = 2}
       in
         length (#gated result) = 1 andalso
         length (#battery result) =
           (if OS.Process.getEnv "HOLBENCHNOBATTERY" = SOME "1"
            then 0 else 2)
       end)

fun recipe_goal id recipe goal : benchLib.corpus_goal =
  {id = id, goal = goal, source_method = "recipe selftest",
   recipe = recipe, excl = [], provenance = provenance,
   representative = true}

fun recipe_solves recipe goal =
  let
    val entry = recipe_goal "unit-recipe" recipe goal
    val outcome = benchLib.run_goal (Time.fromSeconds 5) recipe entry
    fun outcome_text (benchLib.SOLVED elapsed) =
          "solved:" ^ Time.toString elapsed
      | outcome_text benchLib.TIMEOUT = "timeout"
      | outcome_text (benchLib.FAILED message) = "failed:" ^ message
    val _ =
      if benchLib.outcome_solved outcome orelse
          OS.Process.getEnv "HOLBENCHRECIPEFAIL" <> SOME "1"
      then ()
      else TextIO.print ("recipe failure: " ^ outcome_text outcome ^
                         "\n")
  in
    benchLib.outcome_solved outcome
  end

(* Claset-derived names need not name any simpset entry. Their kernel
   spelling must still cross the legacy Excl parser without becoming an
   ExclX target lookup, or changing the name passed to claset deletion. *)
val _ =
  check
    ("kernel-spelled claset-only exclusions stay silent in simp and auto",
     fn () =>
       List.all
         (fn tactic =>
           let
             val recipe = benchLib.Invoke (tactic, [])
             val entry : benchLib.corpus_goal =
               {id = "unit-derived-exclusion", goal = #goal solved_goal,
                source_method = "exclusion selftest", recipe = recipe,
                excl = [{name = "bool$bench_absent.__clasimp_iff_intro",
                         theorem = REFL p}],
                provenance = provenance, representative = true}
           in
             benchLib.outcome_solved
               (benchLib.run_goal (Time.fromSeconds 5) recipe entry)
           end)
         [benchLib.Simp, benchLib.Auto])

val _ =
  check
    ("kernel-spelled rewrite deletions stay literal in simp and auto",
     fn () =>
       List.all
         (fn tactic =>
           recipe_solves
             (benchLib.Invoke
                (tactic,
                 [benchLib.RewriteDelete
                    "bool$bench_absent.__clasimp_iff_intro"]))
             (#goal solved_goal))
         [benchLib.Simp, benchLib.Auto])

val conjunction_commute = boolTheory.CONJ_COMM
val disjunction_commute = boolTheory.DISJ_COMM
val r = mk_var ("bench_unit_r", bool)
val s = mk_var ("bench_unit_s", bool)

(* An instance measuring what a recipe-local schema adds has to be one
   the ambient simpset cannot close by itself.  A permutation is no
   longer such an instance: an equivalence between a term and a
   permutation of itself is decided ambiently.  So the schemas measured
   here distribute rather than commute, and each instance nests one
   distributed operand so that it is an instance of the schema and not
   the schema's own statement. *)
val conjunction_over_disjunction = boolTheory.LEFT_AND_OVER_OR
val disjunction_over_conjunction = boolTheory.LEFT_OR_OVER_AND
val nested_conjunction_distribute =
  boolSyntax.mk_eq
    (boolSyntax.mk_conj (p, boolSyntax.mk_disj (boolSyntax.mk_conj (q, s), r)),
     boolSyntax.mk_disj
       (boolSyntax.mk_conj (p, boolSyntax.mk_conj (q, s)),
        boolSyntax.mk_conj (p, r)))
val nested_disjunction_distribute =
  boolSyntax.mk_eq
    (boolSyntax.mk_disj (p, boolSyntax.mk_conj (boolSyntax.mk_disj (q, s), r)),
     boolSyntax.mk_conj
       (boolSyntax.mk_disj (p, boolSyntax.mk_disj (q, s)),
        boolSyntax.mk_disj (p, r)))

val rewrite_recipe =
  benchLib.Invoke
    (benchLib.Simp,
     [benchLib.RewriteAdd
        {name = "unit$conjunction_commute",
         theorem = conjunction_commute}])
val definition_recipe =
  benchLib.Invoke
    (benchLib.Simp,
     [benchLib.DefinitionAdd
        {name = "unit$disjunction_commute",
         theorem = disjunction_commute}])
val mislabeled_definition_recipe =
  benchLib.Invoke
    (benchLib.Simp,
     [benchLib.DefinitionAdd
        {name = "unit$not_a_definition",
         theorem = conjunction_commute}])

val _ =
  check
    ("an empty exclusion list cannot admit the measured theorem",
     fn () =>
       not
         (recipe_solves rewrite_recipe (Thm.concl conjunction_commute)))

val _ =
  check
    ("a definition label cannot admit the measured theorem",
     fn () =>
       not
         (recipe_solves mislabeled_definition_recipe
            (Thm.concl conjunction_commute)))

val truth_wrapped_recipe =
  benchLib.Invoke
    (benchLib.Simp,
     [benchLib.RewriteAdd
        {name = "unit$conjunction_commute_as_truth",
         theorem = Drule.EQT_INTRO conjunction_commute}])

val _ =
  check
    ("a goal-as-truth wrapper cannot admit the measured theorem",
     fn () =>
       benchLib.theorem_is_goal
         (Thm.concl conjunction_commute)
         (Drule.EQT_INTRO conjunction_commute) andalso
       not
         (recipe_solves truth_wrapped_recipe
            (Thm.concl conjunction_commute)))

(* The ambient bridge rewrites a goal from the translation's
   [source_sorted_wrt] into SORTED wherever transitivity is
   dischargeable, which leaves a rule cited in the translation's
   spelling on the wrong side of it.  The crossing offers that rule in
   the goal's spelling too, with the bridge's own condition last so a
   destruction rule's major premise stays first. *)
val sorted_wrt_drop_rule =
  {name = "parityTranslation$source_sorted_wrt_drop",
   theorem = DB.fetch "parityTranslation" "source_sorted_wrt_drop"}

(* Two drops, so the goal is not the rule with its premises in another
   order -- which is a self-analogue A1 withholds, and would leave this
   check asserting the crossing on a rule the measurement never
   offers. *)
val crossing_goal =
  ``relation$transitive bench_cross_le ==>
    sorting$SORTED bench_cross_le bench_cross_xs ==>
    sorting$SORTED bench_cross_le (DROP bench_cross_n bench_cross_xs) /\
    sorting$SORTED bench_cross_le (DROP bench_cross_m bench_cross_xs)``

val crossing_recipe =
  benchLib.Invoke
    (benchLib.Auto,
     [benchLib.DestAdd (benchLib.UnsafeRule, sorted_wrt_drop_rule)])

val _ =
  check
    ("a supplied rule is offered across the ambient correspondence",
     fn () =>
       let
         val entry = recipe_goal "unit-crossing" crossing_recipe crossing_goal
         val crossings =
           List.filter
             (fn benchLib.DestAdd (_, {name, ...}) =>
                   name = "parityTranslation$source_sorted_wrt_drop[bridged]"
               | _ => false)
             (benchLib.across_correspondence entry
               [benchLib.DestAdd (benchLib.UnsafeRule, sorted_wrt_drop_rule)])
       in
         case crossings of
             [benchLib.DestAdd (_, {theorem, ...})] =>
               let
                 fun mentions name term =
                   List.exists
                     (fn constant => #1 (Term.dest_const constant) = name)
                     (find_terms Term.is_const term)
                 val (premises, conclusion) =
                   boolSyntax.strip_imp_only
                     (snd (boolSyntax.strip_forall (Thm.concl theorem)))
               in
                 List.length premises = 2 andalso
                 mentions "SORTED" (List.hd premises) andalso
                 mentions "transitive" (List.nth (premises, 1)) andalso
                 mentions "SORTED" conclusion
               end
           | _ => false
       end)

val _ =
  check
    ("the crossed rule is what closes a goal on the far side",
     fn () => recipe_solves crossing_recipe crossing_goal)

val implication_recipe =
  benchLib.Invoke
    (benchLib.Simp,
     [benchLib.FactAdd
        {name = "unit$conjunction_commute_under_assumption",
         theorem = DISCH p conjunction_commute}])

val nested_then_recipe =
  benchLib.Then
    (benchLib.Invoke (benchLib.Safe, []), rewrite_recipe)

val nested_all_goals_recipe =
  benchLib.AllGoals
    (benchLib.Invoke (benchLib.Safe, []), truth_wrapped_recipe)

fun raw_recipe_rejected id argument_name recipe =
  raises_with [id, argument_name]
    (fn () =>
      benchLib.validate_raw_goal
        (recipe_goal id recipe (Thm.concl conjunction_commute)))

val _ =
  check
    ("raw validation rejects a direct measured theorem with diagnostics",
     fn () =>
       raw_recipe_rejected
         "unit-raw-direct" "unit$conjunction_commute" rewrite_recipe)

val _ =
  check
    ("raw validation rejects a truth-wrapped measured theorem",
     fn () =>
       raw_recipe_rejected
         "unit-raw-truth" "unit$conjunction_commute_as_truth"
         truth_wrapped_recipe)

val _ =
  check
    ("raw validation rejects an implication with the measured conclusion",
     fn () =>
       raw_recipe_rejected
         "unit-raw-implication"
         "unit$conjunction_commute_under_assumption" implication_recipe)

val _ =
  check
    ("statement comparison reaches quantified conjuncts with their premises",
     fn () =>
       let
         val z = mk_var ("bench_nested_z", numSyntax.num)
         val inner = boolSyntax.mk_eq (z, numSyntax.zero_tm)
         val leaf = boolSyntax.mk_eq (numSyntax.mk_suc z, z)
         val quantified =
           boolSyntax.mk_forall (z, boolSyntax.mk_imp (inner,leaf))
         fun nest 0 = boolSyntax.mk_imp (p,quantified)
           | nest n =
               boolSyntax.mk_imp (p, boolSyntax.mk_conj (q, nest (n - 1)))
         val citation = ASSUME (nest 12)
         val measured = boolSyntax.mk_imp (p, boolSyntax.mk_imp (inner,leaf))
       in
         benchLib.theorem_is_goal measured citation andalso
         not (benchLib.theorem_is_goal (boolSyntax.mk_imp (p,leaf)) citation)
       end)

val _ =
  check
    ("raw validation rejects a theorem falsely labelled as a definition",
     fn () =>
       raw_recipe_rejected
         "unit-raw-definition" "unit$not_a_definition"
         mislabeled_definition_recipe)

val _ =
  check
    ("raw validation descends through Then recipes",
     fn () =>
       raw_recipe_rejected
         "unit-raw-then" "unit$conjunction_commute"
         nested_then_recipe)

val _ =
  check
    ("raw validation descends through AllGoals recipes",
     fn () =>
       raw_recipe_rejected
         "unit-raw-all-goals" "unit$conjunction_commute_as_truth"
         nested_all_goals_recipe)

val _ =
  check
    ("preparation rejects rather than deleting a forbidden raw argument",
     fn () =>
       raises_with ["unit-raw-prepare", "unit$conjunction_commute"]
         (fn () =>
           ignore
             (prepared
               (recipe_goal "unit-raw-prepare" rewrite_recipe
                  (Thm.concl conjunction_commute)))))

val distribution_rewrite_recipe =
  benchLib.Invoke
    (benchLib.Simp,
     [benchLib.RewriteAdd
        {name = "unit$conjunction_over_disjunction",
         theorem = conjunction_over_disjunction}])
val distribution_definition_recipe =
  benchLib.Invoke
    (benchLib.Simp,
     [benchLib.DefinitionAdd
        {name = "unit$disjunction_over_conjunction",
         theorem = disjunction_over_conjunction}])

val _ =
  check
    ("recipe-local schemas still close non-analogue instances",
     fn () =>
       recipe_solves distribution_rewrite_recipe
         nested_conjunction_distribute andalso
       recipe_solves distribution_definition_recipe
         nested_disjunction_distribute andalso
       not
         (recipe_solves (benchLib.Invoke (benchLib.Simp, []))
            nested_conjunction_distribute) andalso
       not
         (recipe_solves (benchLib.Invoke (benchLib.Simp, []))
            nested_disjunction_distribute))

val length_reverse =
  {name = "list$LENGTH_REVERSE", theorem = listTheory.LENGTH_REVERSE}
val length_reverse_goal =
  Thm.concl
    (SPEC ``[T]``
      (INST_TYPE [Type.alpha |-> Type.bool] listTheory.LENGTH_REVERSE))
val fact_recipe =
  benchLib.Invoke
    (benchLib.Safe, [benchLib.FactAdd length_reverse])
val intro_recipe =
  benchLib.Invoke
    (benchLib.Safe,
     [benchLib.IntroAdd (benchLib.SafeRule, length_reverse)])

val _ =
  check
    ("recipe-local fact closes a goal that bare safe leaves",
     fn () =>
       recipe_solves fact_recipe length_reverse_goal andalso
       not
         (recipe_solves (benchLib.Invoke (benchLib.Safe, []))
            length_reverse_goal))

val _ =
  check
    ("recipe-local safe introduction closes a goal when omitted does not",
     fn () =>
       recipe_solves intro_recipe length_reverse_goal andalso
       not
         (recipe_solves (benchLib.Invoke (benchLib.Safe, []))
            length_reverse_goal))

val _ =
  check
    ("classical recipe phases ignore simpset-only arguments",
     fn () =>
       recipe_solves
         (benchLib.Invoke
            (benchLib.Safe,
             [benchLib.RewriteAdd length_reverse,
              benchLib.IntroAdd
                (benchLib.SafeRule, length_reverse)]))
         length_reverse_goal)

val _ =
  check
    ("recipe compilation does not mutate the persistent tactic context",
     fn () =>
       let
         val rules_before = map (#1 o #2) (clasetLib.rules_of
           (clasetLib.the_claset ()))
         val fragments_before = simpLib.all_named_frags ()
         val ordinary_fragments_before = simpLib.all_named_frags ()
         val _ = recipe_solves intro_recipe length_reverse_goal
         val _ = recipe_solves rewrite_recipe
           (Thm.concl conjunction_commute)
         val rules_after = map (#1 o #2) (clasetLib.rules_of
           (clasetLib.the_claset ()))
         val fragments_after = simpLib.all_named_frags ()
         val ordinary_fragments_after = simpLib.all_named_frags ()
       in
         rules_before = rules_after andalso
         fragments_before = fragments_after andalso
         ordinary_fragments_before = ordinary_fragments_after
       end)

val paired_length_reverse =
  boolSyntax.mk_conj (length_reverse_goal, length_reverse_goal)
val split_safe = benchLib.Invoke (benchLib.Safe, [])
val solve_length =
  benchLib.Invoke
    (benchLib.Safe,
     [benchLib.IntroAdd (benchLib.SafeRule, length_reverse)])

val _ =
  check
    ("Then continues only the first residual goal",
     fn () =>
       not
         (recipe_solves
           (benchLib.Then (split_safe, solve_length))
           paired_length_reverse))

val _ =
  check
    ("AllGoals continues every residual goal",
     fn () =>
       recipe_solves
         (benchLib.AllGoals (split_safe, solve_length))
         paired_length_reverse andalso
       not
         (recipe_solves
           (benchLib.AllGoals
             (split_safe, benchLib.Invoke (benchLib.Safe, [])))
           paired_length_reverse))

(* A recipe is derived at the Isabelle line its goal was proved on,
   because the ambient context is cut by Isabelle's theory order.  The
   goals below are not corpus entries, so they are stated at the line
   of the source file the corpus draws their kind of goal from. *)
val classical_source = "src/HOL/ex/Classical.thy:1"

val recipe_constructor_names =
  benchLib.recipe_name
    (benchLib.Invoke
      (benchLib.Auto,
       [benchLib.RewriteDelete "unit$delete",
        benchLib.SplitAdd length_reverse,
        benchLib.IntroAdd (benchLib.UnsafeRule, length_reverse),
        benchLib.ElimAdd (benchLib.SafeRule, length_reverse),
        benchLib.DestAdd (benchLib.UnsafeRule, length_reverse),
        benchLib.CongruenceAdd length_reverse]))

val _ =
  check
    ("every remaining recipe constructor has a stable diagnostic",
     fn () =>
       List.all
         (fn text => String.isSubstring text recipe_constructor_names)
         ["rewrite-delete(unit$delete)", "split(list$LENGTH_REVERSE)",
          "intro-unsafe(list$LENGTH_REVERSE)",
          "elim-safe(list$LENGTH_REVERSE)",
          "dest-unsafe(list$LENGTH_REVERSE)",
          "cong(list$LENGTH_REVERSE)"])

(* ---- The ambient set --------------------------------------------- *)

(* Isabelle's simpset carries a [fun]'s equations and not a plain
   [definition]'s, and the corpus is measured under the definitions that
   line leaves.  A mined table draws it and is also what supplies the
   ambient set, so what the translation theory records has to be
   covered: a definition added with no row would otherwise be measured
   under neither side, silently absent from every goal's context. *)
val _ =
  check
    ("every translated definition has a mined introduction",
     fn () =>
       let
         val recorded =
           map #1
             (List.filter (benchAmbient.equational o concl o #2)
               (DB.definitions "parityTranslation"))
         val mined =
           map (fn (name, _, _) => name)
             benchIsabelleAmbient.introductions
       in
         List.all (fn name => List.exists (equal name) mined) recorded
       end)

val _ =
  check
    ("the ambient set is a proper part of the definitions",
     fn () =>
       let
         val ambient = map #name benchAmbient.ambient_definitions
         val defined = map #name benchAmbient.definitions
         val _ =
           TextIO.print
             (" [ambient " ^ Int.toString (length ambient) ^ " of " ^
              Int.toString (length defined) ^ "] ")
       in
         not (null ambient) andalso
         length ambient < length defined andalso
         List.all (fn name => List.exists (equal name) defined) ambient
       end)

(* The set is a context rather than a list, so what has to hold is that
   a method consulting a simpset is handed the mined definitions and
   stops at the line: [sorted_wrt] is Isabelle's [fun], [map_filter] its
   plain [definition] whose recursive equations it declares separately
   and the translation does not carry. *)
val _ =
  check
    ("the ambient set reaches a simp method and stops at the line",
     fn () =>
       let
         val recipe =
           benchDerive.recipe_of "src/HOL/List.thy:9999"
             ``!xs : 'a list. xs = xs`` "by simp"
         val names =
           List.mapPartial
             (fn benchLib.RewriteAdd {name, ...} => SOME name
               | _ => NONE)
             (benchLib.recipe_arguments recipe)
       in
         List.exists (equal "source_sorted_wrt_def") names andalso
         not (List.exists (equal "source_map_filter_def") names)
       end)

(* Isabelle's simpset carries a [function]'s equations from the point
   its termination is proved.  Two of the three the translation has are
   withheld anyway: [upto]'s by the source's own [simp del], and
   [transpose]'s because the translation states that constant by its
   index reading and not by the source's equations, so the two sides
   have no equation in common.  The goal below is no corpus entry -- it
   is Isabelle's illustration at List.thy:355 cut to one element a side
   -- and it needs all three equations rather than any one of them: the
   cons equation splits the two interleavings and the two nil equations
   close them. *)
val _ =
  check
    ("the ambient set carries a function's equations",
     fn () =>
       let
         val ambient =
           List.mapPartial
             (fn benchLib.RewriteAdd named => SOME named | _ => NONE)
             benchAmbient.arguments
         fun carried name =
           List.exists
             (fn {name = entry, ...} : benchLib.named_thm => entry = name)
             ambient
         val equations =
           List.find
             (fn {name, ...} : benchLib.named_thm =>
               name = "source_shuffles_def")
             ambient
         val interleaved =
           ``!left right : 'a.
               [left; right] IN
                 parityTranslation$source_shuffles [left] [right] /\
               [right; left] IN
                 parityTranslation$source_shuffles [left] [right]``
         fun closes rules =
           Lib.can Tactical.TAC_PROOF
             (([], interleaved),
              simpLib.SIMP_TAC (BasicProvers.srw_ss ()) rules)
       in
         not (carried "source_upto_def") andalso
         not (carried "source_transpose_def") andalso
         (case equations of
              NONE => false
            | SOME {theorem, ...} =>
                closes [theorem] andalso not (closes []))
       end)

(* A declared result is tried against a goal the ambient set has
   already rewritten, so it has to be stated the way that leaves it.
   [source_code_roundtrip] is Isabelle's [of_char_of], stated on
   [source_of_char], which is an alias the ambient set unfolds to ORD:
   as the translation states it the rule reaches no residual, and the
   goal it should close is [n MOD 256 = ORD (source_char_of n)]. *)
val _ =
  check
    ("a declared result is read through the ambient aliases",
     fn () =>
       let
         val ambient =
           List.mapPartial
             (fn benchLib.RewriteAdd named => SOME named | _ => NONE)
             benchAmbient.arguments
         val roundtrip =
           List.find
             (fn {name, ...} : benchLib.named_thm =>
               name = "parityTranslation$source_code_roundtrip")
             ambient
         val residual =
           ``!n. n MOD 256 = ORD (parityTranslation$source_char_of n)``
       in
         case roundtrip of
             NONE => false
           | SOME {theorem, ...} =>
               Lib.can Tactical.TAC_PROOF
                 (([], residual),
                  simpLib.SIMP_TAC boolSimps.bool_ss [theorem])
       end)

(* Isabelle declares [nth_zip] simp, so its simpset takes an index
   through a zip with nothing named.  HOL4's [EL_ZIP] asks for equal
   lengths, which a truncating ZIP does not give, and the goal below --
   no corpus entry -- is the shape that leaves: two bounds in the
   premises and a projection of the indexed pair in the conclusion. *)
val _ =
  check
    ("the ambient set takes an index through a zip",
     fn () =>
       let
         val ambient =
           List.mapPartial
             (fn benchLib.RewriteAdd named => SOME named | _ => NONE)
             benchAmbient.arguments
         val indexed =
           List.find
             (fn {name, ...} : benchLib.named_thm =>
               name = "parityTranslation$source_nth_zip")
             ambient
         val goal =
           ``!xs ys index.
               index < LENGTH xs ==> index < LENGTH ys ==>
               FST (EL index (ZIP (xs, ys))) = EL index xs``
       in
         case indexed of
             NONE => false
           | SOME {theorem, ...} =>
               Lib.can Tactical.TAC_PROOF
                 (([], goal),
                  simpLib.SIMP_TAC (simpLib.++ (boolSimps.bool_ss,
                    pairSimps.PAIR_ss)) [theorem])
       end)

(* [map_add] is a plain Isabelle definition, so the ambient set does
   not carry it and a goal that never names [map_add_def] sees the
   constant and nothing else.  What Isabelle gives such a goal instead
   is [map_add_find_right], declared [simp].  The check below asks for
   a nested instance rather than for the rule itself, and confirms the
   same goal is out of reach without it. *)
val _ =
  check
    ("the ambient set reads a value out of the right-hand map",
     fn () =>
       let
         val ambient =
           List.mapPartial
             (fn benchLib.RewriteAdd named => SOME named | _ => NONE)
             benchAmbient.arguments
         val found =
           List.find
             (fn {name, ...} : benchLib.named_thm =>
               name = "parityTranslation$source_map_add_find_right")
             ambient
         val goal =
           ``!left middle right key value.
               right key = SOME value ==>
               parityTranslation$source_map_add left
                 (parityTranslation$source_map_add middle right) key =
               SOME value``
         fun closes rules =
           Lib.can Tactical.TAC_PROOF
             (([], goal),
              Tactical.THEN
                (Tactical.REPEAT Tactic.STRIP_TAC,
                 simpLib.ASM_SIMP_TAC boolSimps.bool_ss rules))
       in
         case found of
             NONE => false
           | SOME {theorem, ...} => closes [theorem] andalso not (closes [])
       end)

(* Isabelle declares [map_add_SomeD] [dest!] -- in its claset, not in
   its simpset -- and no rewrite stands in for it: the ambient rewrites
   match a map sum under [= NONE] or build one from a value, and this
   is what takes one apart under [= SOME].  The goal below asks for two
   nested instances rather than for the rule itself, and is not a corpus
   entry.  The ablation is the gating: [simp] reads no claset, so the
   same goal under [by simp] is the same measurement with the claset
   half removed, and it must not close. *)
val ambient_claset_goal =
  ``!left middle right key value.
      parityTranslation$source_map_add left
        (parityTranslation$source_map_add middle right) key = SOME value ==>
      right key = SOME value \/ middle key = SOME value \/
      left key = SOME value``

val _ =
  check
    ("the ambient claset takes a map sum apart under a witness",
     fn () =>
       let
         fun closes method =
           let
             val recipe =
               benchDerive.recipe_of "src/HOL/Map.thy:9999"
                 ambient_claset_goal method
           in
             benchLib.outcome_solved
               (benchLib.run_goal (Time.fromSeconds 5) recipe
                 (recipe_goal "unit-ambient-claset" recipe
                    ambient_claset_goal))
           end
       in
         closes "by force" andalso not (closes "by simp")
       end)

(* Isabelle reads a theory in order and sees only the theories it
   imports, so the ambient context is cut by where the goal sits.
   [Sigma] is introduced at Product_Type.thy:1005 and its two classical
   rules at :1027 and :1030; Product_Type imports Fun and Fun imports
   Set, so a Set.thy proof had none of them, and a List.thy proof had
   nothing [Map] declares.  Both halves are cut: an out-of-scope rewrite
   is a fact the source proof did not have, and an out-of-scope rule is
   one its search was not paying for. *)
val _ =
  check
    ("the ambient context stops at the goal's place in the theory order",
     fn () =>
       let
         fun named source =
           map benchLib.argument_name (benchAmbient.arguments_at source)
         fun carries source name =
           List.exists (equal name) (named source)
         val sigma = "parityTranslation$source_SigmaE"
         val map_add = "parityTranslation$source_map_add_SomeD"
         val fold_append = "parityTranslation$source_fold_append"
       in
         (* Later in the same theory sees it; earlier does not. *)
         carries "src/HOL/Product_Type.thy:1082" sigma andalso
         not (carries "src/HOL/Product_Type.thy:1020" sigma) andalso
         (* A theory the declaring one imports does not. *)
         not (carries "src/HOL/Set.thy:1610" sigma) andalso
         not (carries "src/HOL/List.thy:9999" map_add) andalso
         not (carries "src/HOL/Set.thy:9999" fold_append) andalso
         (* A theory that imports the declaring one does. *)
         carries "src/HOL/String.thy:1" map_add andalso
         carries "src/HOL/Map.thy:1" fold_append
       end)

(* The cut is what a method reads, not just what a table says.  The
   goal below is not a corpus entry: it takes a Sigma apart and builds
   another one over a wider fibre, which needs both declared rules and
   which no ambient rewrite reaches, [Sigma] being a plain definition
   Isabelle's simpset leaves folded.  Stated at a Product_Type line
   after :1030 the assigned [blast] closes it; stated at the Set.thy
   line [Pow_Compl] is proved on it must not, the rules not yet
   existing there. *)
val ambient_order_goal =
  ``!pair left fibre other.
      pair IN parityTranslation$source_Sigma left fibre ==>
      pair IN
        parityTranslation$source_Sigma left (\item. fibre item UNION other)``

val _ =
  check
    ("a rule out of scope where the goal sits does not reach it",
     fn () =>
       let
         fun closes source =
           let
             val recipe =
               benchDerive.recipe_of source ambient_order_goal "by blast"
           in
             benchLib.outcome_solved
               (benchLib.run_goal (Time.fromSeconds 5) recipe
                 (recipe_goal "unit-ambient-order" recipe
                    ambient_order_goal))
           end
       in
         closes "src/HOL/Product_Type.thy:1082" andalso
         not (closes "src/HOL/Set.thy:1610")
       end)

(* Isabelle's [iff] is one attribute with two effects, and a method
   reading no simpset still has the rules the declaration derived: the
   goal below is [safe], which never simplifies, over two relational
   images of singletons.  [Image_singleton_iff] is what takes them
   apart, and it is declared [iff] and nothing else -- no [dest] states
   it -- so without the claset half of the declaration both conjuncts
   are left open.  Stated at a List.thy line, which imports
   Relation.thy, so the declaration is in scope there. *)
val ambient_iff_goal =
  ``!relation left right second.
      right IN parityTranslation$source_rel_image relation {left} /\
      second IN parityTranslation$source_rel_image relation {right} ==>
      relation left right /\ relation right second``

val _ =
  check
    ("an ambient [iff] reaches a method that reads no simpset",
     fn () =>
       let
         val recipe =
           benchDerive.recipe_of "src/HOL/List.thy:9999" ambient_iff_goal
             "by safe"
       in
         benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 5) recipe
             (recipe_goal "unit-ambient-iff" recipe ambient_iff_goal))
       end)

(* A primitive set operation is carried by its membership rewrite, not
   by the equation defining it, and unfolding the definition costs the
   operator every rule that keys on it.  The goal below is [blast],
   which reads no simpset, so the difference has to reach the search
   intact for the claset's rules about it to meet it -- and it sits in
   the domain argument of [source_Sigma], where no membership rewrite
   would put it back.  It is a set equality, which is what makes the
   pre-pass run at all.  Stated at a Product_Type.thy line, so [SigmaI]
   and [SigmaE] are in scope. *)
val withheld_definition_goal =
  ``parityTranslation$source_Sigma (v_A0 DIFF (v_B0 DIFF v_A0)) v_C0 =
    parityTranslation$source_Sigma v_A0 v_C0``

val _ =
  check
    ("a set operation the goal does not state survives the blast pre-pass",
     fn () =>
       let
         val recipe =
           benchDerive.recipe_of "src/HOL/Product_Type.thy:9999"
             withheld_definition_goal "by blast"
       in
         benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 5) recipe
             (recipe_goal "unit-withheld-definition" recipe
                withheld_definition_goal))
       end)

(* Isabelle's [blast] never simplifies, so the harness simplifies a
   blast goal for the [unfolding] the method asked for and for nothing
   else.  The goal below is one the simpset closes and the tableau does
   not, which is what makes the last two rows mean anything: the
   recipe must leave it open when what it carries is a classical rule
   -- and the ambient claset is a classical rule every blast goal now
   carries -- and must still close it when what it carries is the
   rewrite an [unfolding] resolves to.  The first two rows keep the
   others honest: a tableau that closed the goal itself, or a simpset
   that did not, would let them pass. *)
val blast_gate_goal = ``LENGTH [bench_gate_a; bench_gate_b; bench_gate_c] = 3``

val blast_gate_rule =
  benchLib.DestAdd
    (benchLib.UnsafeRule,
     {name = "parityTranslation$source_map_add_SomeD",
      theorem = DB.fetch "parityTranslation" "source_map_add_SomeD"})

val blast_gate_rewrite =
  benchLib.RewriteAdd {name = "list$LENGTH", theorem = listTheory.LENGTH}

fun blast_gate_solves recipe =
  benchLib.outcome_solved
    (benchLib.run_goal (Time.fromSeconds 5) recipe
      (recipe_goal "unit-blast-gate" recipe blast_gate_goal))

val _ =
  check
    ("the tableau alone leaves the blast gate goal open",
     fn () => not (blast_gate_solves (benchLib.Invoke (benchLib.Blast, []))))

val _ =
  check
    ("the simpset alone closes the blast gate goal",
     fn () => blast_gate_solves (benchLib.Invoke (benchLib.Simp, [])))

val _ =
  check
    ("a blast recipe does not simplify for a rule it was handed",
     fn () =>
       not (blast_gate_solves
              (benchLib.Invoke (benchLib.Blast, [blast_gate_rule]))))

val _ =
  check
    ("a blast recipe still simplifies for an unfolding",
     fn () =>
       blast_gate_solves
         (benchLib.Invoke (benchLib.Blast, [blast_gate_rewrite])))

(* A rule the method supplies is stated in the vocabulary the method's
   own goal had, so the pass above has to carry it along: the goal
   below is handed [subset_imageE], whose major premise is
   [source SUBSET IMAGE function target], and the pass leaves the goal
   with no [SUBSET] in it at all.  Left behind, the rule matches
   nothing and the search guesses the set it would have named.

   That is what the row was written for, and it no longer measures
   it.  Ablated -- rules never carried -- the goal below still closes
   and the row stays green, at HEAD as well as here, so the 30.3s
   against 3.9s this comment used to quote has rotted: the ambient
   claset now closes the membership reading without the carried rule.
   The row is kept as the weaker guard it has become, that the goal
   closes within its budget at all, and the mechanism above is for
   the moment untested.  Restating the goal does not recover it: an
   intersection keeps the pass on but puts the goal out of reach
   altogether, failing at a 60s budget, and an empty union or a
   singleton closes without the rule just as the variable does. *)
val stranded_rule_goal =
  ``v_B0 SUBSET IMAGE v_f0 v_A0 <=>
    ?b_AA. b_AA SUBSET v_A0 /\ v_B0 = IMAGE v_f0 b_AA``

val _ =
  check
    ("a supplied rule goes through the blast pre-pass with the goal",
     fn () =>
       let
         val recipe =
           benchDerive.recipe_of "src/HOL/Set.thy:9999"
             stranded_rule_goal "by (blast elim: subset_imageE)"
       in
         benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 10) recipe
             (recipe_goal "unit-stranded-rule" recipe stranded_rule_goal))
       end)

(* The pass takes an equation to its membership form; an equation with
   a variable on a side is one the search eliminates by substituting
   it instead, which is what [blastSearch]'s [HypSubst] is for.
   Dissolving the hypothesis below spends that step and takes the
   [SUBSET] the supplied [subset_imageE] is stated under with it,
   leaving the rule nothing to match anywhere in the goal.  Neither
   the goal nor the rule is a corpus entry. *)
val substituted_hypothesis_goal =
  ``IMAGE v_h0 v_source0 = v_target0 ==>
    v_part0 SUBSET v_target0 ==>
    ?b_piece. b_piece SUBSET v_source0 /\ v_part0 = IMAGE v_h0 b_piece``

val _ =
  check
    ("a hypothesis the search substitutes survives the blast pre-pass",
     fn () =>
       let
         val recipe =
           benchDerive.recipe_of "src/HOL/Set.thy:9998"
             substituted_hypothesis_goal "by (blast elim: subset_imageE)"
       in
         benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 10) recipe
             (recipe_goal "unit-substituted-hypothesis" recipe
                substituted_hypothesis_goal))
       end)

(* ---- Phase A detectors ------------------------------------------- *)

fun guard_entry id method arguments goal : benchLib.corpus_goal =
  {id = id, goal = goal, source_method = method,
   recipe = benchLib.Invoke (benchLib.Simp, arguments),
   excl = [], provenance = provenance, representative = true}

val subset_goal = Thm.concl (Drule.SPEC_ALL pred_setTheory.SUBSET_DEF)
val subset_flipped = Conv.GSYM pred_setTheory.SUBSET_DEF

val _ =
  check
    ("a statement's normal form reduces raw beta and eta redexes",
     fn () =>
       Term.aconv
         (benchLib.statement_normal_form
            ``(\f : bool -> bool. \x : bool. f x) p``)
         (benchLib.statement_normal_form ``p : bool -> bool``))

val _ =
  check
    ("A1 catches a supplied theorem that is the goal with a flipped iff",
     fn () =>
       benchLib.theorem_is_goal subset_goal subset_flipped andalso
       benchGuards.recognition_route subset_goal subset_flipped =
       SOME "syntactic")

(* The shape that made this necessary: a translation lemma stating a
   membership characterisation with its conjuncts in the other order
   and its equation the other way round is the goal it would be handed
   to, and comparing the terms as written does not see it. *)
val member_goal =
  ``MEM (x : num) xs <=> ?i. i < LENGTH xs /\ EL i xs = x``

val member_commuted =
  Rewrite.PURE_ONCE_REWRITE_RULE [boolTheory.CONJ_COMM]
    (Drule.SPEC_ALL
      (Thm.INST_TYPE [Type.alpha |-> numSyntax.num] listTheory.MEM_EL))

val _ =
  check
    ("A1 catches a supplied theorem that is the goal reordered",
     fn () => benchLib.theorem_is_goal member_goal member_commuted)

val _ =
  check
    ("A1 catches a supplied theorem under nested truth equivalences",
     fn () =>
       let
         val theorem = Thm.REFL boolSyntax.F
         fun wrap term = boolSyntax.mk_eq (term, boolSyntax.T)
       in
         benchLib.theorem_is_goal (wrap (wrap (Thm.concl theorem))) theorem
       end)

val _ =
  check
    ("A1 leaves a supplied theorem that states something else alone",
     fn () =>
       not
         (benchLib.theorem_is_goal member_goal
            (Thm.INST_TYPE [Type.alpha |-> numSyntax.num]
              listTheory.MEM_APPEND)))

(* A citation can be the goal and still carry premises, and a
   comparison that strips only the citation puts its conclusion beside
   the whole goal and never sees it.  The quantifier prefix is where
   the two drift apart: the same statement written with the bound
   variables in another order is not alpha-equivalent to it, which is
   how a translation stated as its own goal went unnoticed. *)
val premised_goal =
  ``!l1 l2 n. n < LENGTH (l1 : 'a list) ==> EL n (l1 ++ l2) = EL n l1``

val _ =
  check
    ("A1 catches a supplied theorem that is a goal carrying premises",
     fn () =>
       benchLib.theorem_is_goal premised_goal rich_listTheory.EL_APPEND1)

val _ =
  check
    ("A1 leaves a theorem whose premise the goal does not carry alone",
     fn () =>
       not
         (benchLib.theorem_is_goal premised_goal
            rich_listTheory.EL_APPEND2))

(* [clean_simpset] filters whole theorems, and the simpset then splits
   what survives into one rewrite per conjunct.  So a conjunctive rule
   carrying the goal among its conjuncts reaches the goal as a rewrite
   that is it, and each conjunct has to be read on its own. *)
val _ =
  check
    ("A1 catches a conjunct of a supplied theorem that is the goal",
     fn () =>
       benchLib.theorem_is_goal ``!l. [] ++ l = l`` listTheory.APPEND)

val _ =
  check
    ("A1 leaves a conjunctive theorem no conjunct of which is the goal",
     fn () =>
       not
         (benchLib.theorem_is_goal
            ``!l1 l2. LENGTH (l1 ++ l2) = LENGTH l1 + LENGTH l2``
            listTheory.APPEND))

val _ =
  check
    ("A1 reads a beta-headed conjunct after rejecting rigid heads",
     fn () =>
       benchLib.theorem_is_goal ``n < SUC n``
         (Thm.ASSUME ``!n. ~(n = 0) /\ (\m. m < SUC m) n``))

(* A rule need not put its whole prefix in one place.  It can quantify
   what its premise speaks about, discharge it, and quantify again over
   what the conclusion adds -- [DIVISION] binds the divisor, asks it to
   be positive, and only then binds the dividend.  Taking the prefix off
   once leaves the second one standing in the conclusion, where it is
   nothing the goal says, and the rule reads as no reading of the goal
   at all.  Two corpus goals that are such a rule were measured with
   their own statement left in the simpset. *)
val _ =
  check
    ("A1 catches a theorem that quantifies again after its premise",
     fn () =>
       benchLib.theorem_is_goal ``!n k. 0 < n ==> k MOD n < n``
         arithmeticTheory.DIVISION)

val _ =
  check
    ("A1 leaves such a theorem alone where the conclusion is not the goal",
     fn () =>
       not
         (benchLib.theorem_is_goal ``!n k. 0 < n ==> k MOD n < SUC n``
            arithmeticTheory.DIVISION))

(* The same index has two spellings, and which one a statement wears
   says where it was written rather than what it says: a translated
   goal spells it [n - 1], because Isabelle has no predecessor
   constant, and a HOL4 rule spells it [PRE n].  The layer's simpset
   carries the step between them, so a rule that is the goal in one
   spelling is the goal in the other, and A1 has to read past the
   difference. *)
val _ =
  check
    ("A1 reads past the two spellings of a predecessor",
     fn () =>
       benchLib.theorem_is_goal ``!n. 0 < n <=> SUC (n - 1) = n``
         arithmeticTheory.SUC_PRE)

val _ =
  check
    ("A1 leaves a predecessor statement that is not the goal alone",
     fn () =>
       not
         (benchLib.theorem_is_goal ``!n. 0 < n <=> SUC (n - 1) = SUC n``
            arithmeticTheory.SUC_PRE))

val _ =
  check
    ("A1 catches a goal-as-truth wrapper through the cheap pre-filter",
     fn () =>
       benchGuards.recognition_route subset_goal
         (Drule.EQT_INTRO (Drule.SPEC_ALL pred_setTheory.SUBSET_DEF)) =
       SOME "syntactic")

val _ =
  check
    ("A1 reads a truth wrapper around a goal with a different head",
     fn () =>
       benchLib.theorem_is_goal ``n < SUC n``
         (Thm.ASSUME ``(n < SUC n) = T``))

val guarded_length_reverse =
  Drule.GEN_ALL
    (Thm.DISCH boolSyntax.T (Drule.SPEC_ALL listTheory.LENGTH_REVERSE))

val _ =
  check
    ("A1 catches a supplied theorem behind a dischargeable hypothesis",
     fn () =>
       not
         (benchLib.theorem_is_goal length_reverse_goal
            guarded_length_reverse) andalso
       Option.isSome
         (benchGuards.recognition_route length_reverse_goal
            guarded_length_reverse))

val _ =
  check
    ("A1 does not call an unrelated supplied theorem recognition",
     fn () =>
       benchGuards.recognition_route length_reverse_goal
         boolTheory.CONJ_COMM = NONE)

val _ =
  check
    ("A1 does not credit a theorem for a goal the ambient route closes",
     fn () =>
       benchGuards.recognition_route
         (boolSyntax.mk_disj (p, boolSyntax.mk_neg p))
         boolTheory.CONJ_COMM = NONE)

(* ---- the comparison reads through a translation wrapper --------- *)

(* A corpus goal wears the translation's constant while an ambient rule
   wears HOL4's, and [source_lexord] *is* [LLEX] by definition.  A
   comparison of the two terms as written cannot see the analogy, so a
   rule that states such a goal would be handed to it undetected.  Both
   statements here are synthetic; neither is a corpus goal. *)
val wrapped_goal =
  ``!R xs ys.
      source_lexord R xs ys /\ source_lexord R ys xs ==>
      source_lexord R xs ys``

val unwrapped_rule =
  Tactical.prove
    (``!R xs ys. LLEX R xs ys /\ LLEX R ys xs ==> LLEX R xs ys``,
     bossLib.metis_tac [])

fun without_definitions body =
  let
    val installed = benchLib.definitional_theorems ()
    val value = body () handle exception_raised =>
      (benchLib.set_definitional_context installed; raise exception_raised)
  in
    benchLib.set_definitional_context installed; value
  end

val _ =
  check
    ("A1 catches an ambient rule that is the goal under its wrapper",
     fn () =>
       let
         val plain =
           without_definitions
             (fn () =>
               (benchLib.set_definitional_context [];
                benchLib.theorem_is_goal wrapped_goal unwrapped_rule))
       in
         not plain andalso
         benchLib.theorem_is_goal wrapped_goal unwrapped_rule
       end)

val _ =
  check
    ("A1 compares the same goal under replacement definitions",
     fn () =>
       without_definitions
         (fn () =>
           benchLib.theorem_is_goal wrapped_goal unwrapped_rule andalso
           (benchLib.set_definitional_context
              [parityTranslationTheory.source_of_char_def];
            not (benchLib.theorem_is_goal wrapped_goal unwrapped_rule))))

val _ =
  check
    ("ambient exclusions follow definition and claset changes",
     fn () =>
       without_definitions
         (fn () =>
           let
             val name = "unit$wrapped_ambient"
             val theorem = Tactical.prove (wrapped_goal, bossLib.metis_tac [])
             val claset = clasetLib.add_rule analogue_spec
               (name, theorem) clasetLib.empty_cs
             (* The declaration may curry the theorem's conjunctive
                premise. Unfold the form the ambient sweep reads. *)
             val declaration =
               case clasetLib.rules_of claset of
                   [(_, (_, stored))] => stored
                 | _ => raise Fail "expected one ambient test declaration"
             val goal = Thm.concl
               (Rewrite.PURE_REWRITE_RULE
                 [parityTranslationTheory.source_lexord_def] declaration)
             val entry : benchLib.corpus_goal =
               {id = "unit-wrapped-ambient", goal = goal,
                source_method = "simp", recipe = #recipe solved_goal,
                excl = [], provenance = provenance, representative = true}
             fun has_exclusion () =
               List.exists (equal name o #name) (#excl (prepared entry))
             fun check_sources () =
               (benchLib.set_definitional_context
                  [parityTranslationTheory.source_of_char_def];
                not (has_exclusion ()) andalso
                (benchLib.set_definitional_context
                   [parityTranslationTheory.source_lexord_def];
                 has_exclusion () andalso
                 (benchLib.set_definitional_context
                    [Thm.REFL ``source_lexord R (xs:'a list) ys``];
                  not (has_exclusion ())) andalso
                 (benchLib.set_definitional_context
                    [parityTranslationTheory.source_lexord_def];
                  has_exclusion ()) andalso
                 not (clasetLib.with_claset clasetLib.empty_cs
                   has_exclusion ()) andalso
                 has_exclusion ()))
           in
             clasetLib.with_claset claset check_sources ()
           end))

val _ =
  check
    ("ambient citation expansions follow implicit rewrite changes",
     fn () =>
       without_definitions
         (fn () =>
           let
             val wrapped = ``source_lexord R (xs:'a list) ys``
             val goal = ``LLEX R (xs:'a list) ys``
             val citation = boolSyntax.mk_cond (boolSyntax.T, wrapped, p)
             val name = "unit$conditional_ambient"
             val claset = clasetLib.add_rule analogue_spec
               (name, Thm.ASSUME citation) clasetLib.empty_cs
             val entry : benchLib.corpus_goal =
               {id = "unit-conditional-ambient", goal = goal,
                source_method = "simp", recipe = #recipe solved_goal,
                excl = [], provenance = provenance, representative = true}
             val saved = Rewrite.implicit_rewrites ()
             fun has_exclusion rewrites =
               (Rewrite.set_implicit_rewrites rewrites;
                List.exists (equal name o #name) (#excl (prepared entry)))
             fun check_rewrites () =
               (benchLib.set_definitional_context
                  [parityTranslationTheory.source_lexord_def];
                not (has_exclusion Rewrite.empty_rewrites) andalso
                has_exclusion Rewrite.bool_rewrites andalso
                not (has_exclusion Rewrite.empty_rewrites))
             val result =
               clasetLib.with_claset claset check_rewrites ()
               handle exn => (Rewrite.set_implicit_rewrites saved; raise exn)
           in
             Rewrite.set_implicit_rewrites saved; result
           end))

val _ =
  check
    ("definition unfolding refreshes explicit and implicit rewrites",
     fn () =>
       without_definitions
         (fn () =>
           let
             val wrapped = ``source_lexord R (xs:'a list) ys``
             val unwrapped = ``LLEX R (xs:'a list) ys``
             val input = boolSyntax.mk_conj (wrapped, boolSyntax.T)
             val plain = boolSyntax.mk_conj (unwrapped, boolSyntax.T)
             val saved = Rewrite.implicit_rewrites ()
             fun check_unfolding () =
               let
                 val _ = benchLib.set_definitional_context
                   [parityTranslationTheory.source_lexord_def]
                 val _ = Rewrite.set_implicit_rewrites Rewrite.empty_rewrites
                 val pure = Term.aconv (benchLib.unfolded input) plain
                 val _ = Rewrite.set_implicit_rewrites Rewrite.bool_rewrites
                 val with_implicit =
                   Term.aconv (benchLib.unfolded input) unwrapped andalso
                   Term.aconv (benchLib.unfolded plain) plain
                 val _ = benchLib.set_definitional_context [Thm.REFL wrapped]
               in
                 pure andalso with_implicit andalso
                 Term.aconv (benchLib.unfolded input) wrapped
               end
             val result = check_unfolding () handle exn =>
               (Rewrite.set_implicit_rewrites saved; raise exn)
           in
             Rewrite.set_implicit_rewrites saved; result
           end))

val _ =
  check
    ("A1 leaves an ambient rule about the same constant alone",
     fn () =>
       not
         (benchLib.theorem_is_goal wrapped_goal listTheory.LLEX_NIL2))

(* Unfolding a definition against itself leaves [t = t], which matches
   every other vacuous statement.  The wrapper's own definition must not
   be read as stating an arbitrary goal. *)
val _ =
  check
    ("A1 does not read a wrapper definition as stating the goal",
     fn () =>
       not
         (benchLib.theorem_is_goal wrapped_goal
            parityTranslationTheory.source_lexord_def))

val _ =
  check
    ("same goal comparison follows implicit rewrite changes",
     fn () =>
       without_definitions
         (fn () =>
           let
             val wrapped = ``source_lexord R (xs:'a list) ys``
             val unwrapped = ``LLEX R (xs:'a list) ys``
             val goal = boolSyntax.mk_conj (wrapped, boolSyntax.T)
             val theorem = Thm.ASSUME unwrapped
             val saved = Rewrite.implicit_rewrites ()
             fun compares () = benchLib.theorem_is_goal goal theorem
             fun check_reading () =
               (benchLib.set_definitional_context
                  [parityTranslationTheory.source_lexord_def];
                Rewrite.set_implicit_rewrites Rewrite.empty_rewrites;
                not (compares ()) andalso
                (Rewrite.set_implicit_rewrites Rewrite.bool_rewrites;
                 compares () andalso
                 (Rewrite.set_implicit_rewrites Rewrite.empty_rewrites;
                  not (compares ()))))
             val result = check_reading () handle exn =>
               (Rewrite.set_implicit_rewrites saved; raise exn)
           in
             Rewrite.set_implicit_rewrites saved; result
           end))

val _ =
  check
    ("ambient citation names can also carry a different theorem",
     fn () =>
       let
         val name = "parityTranslation$source_map_add_None"
         val theorem = boolTheory.CONJ_COMM
         val argument = benchLib.RewriteAdd {name = name, theorem = theorem}
       in
         not (benchLib.permitted_for (Thm.concl theorem) argument)
       end)

(* A [define_new_type_bijections] theorem is registered as a definition
   and is equational, so it reaches the ambient rewrite set; reading it
   as an unfolding would make [source_literal_implode_valid] and the
   round-trip goal the same term. *)
val _ =
  check
    ("A1 does not read a type-bijection characterisation as an unfolding",
     fn () =>
       not
         (benchLib.theorem_is_goal
            (Thm.concl
               parityTranslationTheory.source_literal_explode_implode)
            parityTranslationTheory.source_literal_implode_valid))

val _ =
  check
    ("the ambient sweep collects the definitions the goal's wrapper needs",
     fn () =>
       List.exists
         (fn theorem =>
           Term.aconv (Thm.concl theorem)
             (Thm.concl parityTranslationTheory.source_lexord_def))
         (benchGuards.relevant_definitions wrapped_goal))

(* Collecting the candidates is not the same as consulting them: A1 has
   to run the sweep, or a rule the corpus declares for every goal is
   never judged at all.  The witness is taken from the live claset --
   the set the sweep reads -- so the test does not depend on which
   rules the seeds happen to declare. *)
val ambient_rule =
  let
    val logical =
      ["/\\", "\\/", "~", "==>", "=", "!", "?", "?!", "T", "F",
       "COND", "@"]
    fun ordinary constant =
      not (List.exists (equal (#1 (Term.dest_const constant))) logical)
    fun translated constant =
      String.isPrefix "source_" (#1 (Term.dest_const constant))
    (* A rule in the translation's own constants would be filtered out
       of the candidates by the goal's unfolded reading, so the witness
       is one written in HOL4's. *)
    fun substantial ({thm, ...} : clasetLib.aesop_rule) =
      let val constants = find_terms Term.is_const (Thm.concl thm)
      in
        List.exists ordinary constants andalso
        not (List.exists translated constants)
      end
  in
    case List.filter substantial
           (clasetLib.all_rules (clasetLib.the_claset ())) of
        [] => raise Fail "the benchmark claset declares no ordinary rule"
      | rule :: _ => #thm rule
  end

val _ =
  check
    ("A1 reports an ambient rule that states the goal",
     fn () =>
       List.exists
         (fn ({detector, detail, ...} : benchGuards.finding) =>
           detector = "A1" andalso String.isPrefix "ambient " detail)
         (benchGuards.recognition_findings
            [guard_entry "unit-a1-ambient" "by simp" []
               (Thm.concl ambient_rule)]))

val translation_fact =
  benchLib.FactAdd
    {name = "parityTranslation$source_widget_iff",
     theorem = boolTheory.TRUTH}

val _ =
  check
    ("A2 rejects a translation lemma the Isabelle method never names",
     fn () =>
       benchGuards.provenance_violations
         (guard_entry "unit-a2-unnamed" "by blast" [translation_fact]
            subset_goal) =
       ["parityTranslation$source_widget_iff"])

val _ =
  check
    ("A2 accepts a translation lemma named modulo a documented suffix",
     fn () =>
       null
         (benchGuards.provenance_violations
            (guard_entry "unit-a2-named" "by (blast intro: widget)"
               [translation_fact] subset_goal)))

val _ =
  check
    ("A2 accepts a registered definition of a constant of the goal",
     fn () =>
       null
         (benchGuards.provenance_violations
            (guard_entry "unit-a2-definition" "by blast"
               [benchLib.DefinitionAdd
                  {name = "parityTranslation$source_subset_def",
                   theorem = pred_setTheory.SUBSET_DEF}]
               subset_goal)))

val _ =
  check
    ("A2 ignores arguments that are not translation lemmas",
     fn () =>
       null
         (benchGuards.provenance_violations
            (guard_entry "unit-a2-library" "by blast"
               [benchLib.RewriteAdd
                  {name = "pred_set$SUBSET_DEF",
                   theorem = pred_setTheory.SUBSET_DEF}]
               subset_goal)))

val _ =
  check
    ("A3 classifies Isabelle methods by their head",
     fn () =>
       List.all benchGuards.is_search_method
         ["by blast", "by (auto simp: dom_def)", "by force",
          "using takeWhile_eq_Nil_iff by fastforce", "by(clarsimp)"]
       andalso
       not
         (List.exists benchGuards.is_search_method
            ["by simp", "by (simp add: fun_eq_iff)", "by linarith"]))

val a3_budget = Time.fromSeconds 10

val _ =
  check
    ("A3 reports a search-method goal closed with no search work",
     fn () =>
       length
         (benchGuards.search_work_findings a3_budget
            [guard_entry "unit-a3-idle" "by blast"
               [benchLib.RewriteAdd length_reverse] length_reverse_goal]) = 1)

val a3_search_goal =
  boolSyntax.mk_imp
    (boolSyntax.mk_imp (p, q),
     boolSyntax.mk_imp (boolSyntax.mk_neg q, boolSyntax.mk_neg p))

val a3_search_entry : benchLib.corpus_goal =
  {id = "unit-a3-search", goal = a3_search_goal,
   source_method = "by blast",
   recipe = benchLib.Invoke (benchLib.Blast, []),
   excl = [], provenance = provenance, representative = true}

val _ =
  check
    ("A3 accepts a search-method goal that the engine actually searched",
     fn () =>
       let
         val (outcome, work) =
           benchGuards.measured_run a3_budget a3_search_entry
       in
         benchLib.outcome_solved outcome andalso
         searchWork.total work >= benchGuards.work_floor andalso
         null (benchGuards.search_work_findings a3_budget [a3_search_entry])
       end)

val _ =
  check
    ("A3 leaves goals whose method is not a search method alone",
     fn () =>
       null
         (benchGuards.search_work_findings a3_budget
            [guard_entry "unit-a3-simp" "by simp"
               [benchLib.RewriteAdd length_reverse] length_reverse_goal]))

val a4_goals =
  [guard_entry "unit-a4-one" "by blast" [translation_fact] subset_goal,
   guard_entry "unit-a4-two" "by auto" [] length_reverse_goal]

val _ =
  check
    ("A4 reports a translation lemma used by one goal that never names it",
     fn () =>
       map #id (benchGuards.single_use_findings a4_goals) = ["unit-a4-one"])

val _ =
  check
    ("A4 leaves a translation lemma shared by two goals alone",
     fn () =>
       null
         (benchGuards.single_use_findings
            [guard_entry "unit-a4-shared-one" "by blast"
               [translation_fact] subset_goal,
             guard_entry "unit-a4-shared-two" "by auto"
               [translation_fact] length_reverse_goal]))

val _ =
  check
    ("A4 orders lemmas by last use and lists distinct goals by first use",
     fn () =>
       let
         val other = "parityTranslation$source_gadget_iff"
         val other_fact = benchLib.FactAdd
           {name = other, theorem = boolTheory.TRUTH}
         fun entry id facts = guard_entry id "by blast" facts subset_goal
       in
         benchGuards.translation_uses
           [entry "first" [translation_fact, other_fact],
            entry "second" [translation_fact],
            entry "first" [translation_fact]] =
         [("parityTranslation$source_widget_iff", ["first", "second"]),
          (other, ["first"])]
       end)

val alias_audit = benchGuards.alias_findings ()

val _ =
  check
    ("A5 reports every goal-shaped display alias",
     fn () =>
       List.all
         (fn name => List.exists (fn item => #id item = name) alias_audit)
         ["list$nub_set_for_card_set",
          "list$ALL_DISTINCT_CARD_LIST_TO_SET_for_nub"])

val _ =
  check
    ("A5 leaves an Isabelle attribute rendering alone",
     fn () =>
       not
         (List.exists
            (fn item => #id item = "list$SNOC_APPEND[symmetric]")
            alias_audit))

val _ =
  check
    ("A5 reports a display name mapped to a different theorem",
     fn () =>
       List.exists
         (fn item =>
           #id item = "list$LIST_REL_NIL" andalso
           String.isSubstring "different theorem" (#detail item))
         alias_audit)

val bound_x = ``!bench_guard_x. bench_guard_x = bench_guard_x``
val bound_y = ``!bench_guard_y. bench_guard_y = bench_guard_y``

val _ =
  check
    ("A6 signatures ignore bound variable names",
     fn () =>
       benchGuards.goal_signature bound_x =
       benchGuards.goal_signature bound_y)

val _ =
  check
    ("A6 signatures separate different statements",
     fn () =>
       benchGuards.goal_signature subset_goal <>
       benchGuards.goal_signature length_reverse_goal andalso
       benchGuards.goal_signature p <> benchGuards.goal_signature q)

(* ---- Phase B: the method parser ---------------------------------- *)

fun parses text = benchRecipe.parse text

fun parse_fails text =
  ((parses text; false)
   handle Portable.Interrupt => raise Portable.Interrupt
        | benchRecipe.Unparseable _ => true)

val _ =
  check
    ("the parser reads a bare method",
     fn () =>
       let val {facts, unfolded, methods} = parses "by blast"
       in
         null facts andalso null unfolded andalso
         map #name methods = ["blast"] andalso
         List.all (null o #modifiers) methods
       end)

val _ =
  check
    ("the parser reads simp add: and its one-token spelling alike",
     fn () =>
       benchRecipe.render (parses "by (auto simp add: dom_def fun_eq_iff)") =
       benchRecipe.render (parses "by(auto simp: dom_def fun_eq_iff)"))

fun modifiers_of text = #modifiers (hd (#methods (parses text)))

val _ =
  check
    ("the parser separates safe and unsafe rule modifiers",
     fn () =>
       modifiers_of
         "by (auto intro!: inj_onI dest: inj_onD elim: split_list)"
       = [benchRecipe.Intro (benchLib.SafeRule, ["inj_onI"]),
          benchRecipe.Dest (benchLib.UnsafeRule, ["inj_onD"]),
          benchRecipe.Elim (benchLib.UnsafeRule, ["split_list"])])

val _ =
  check
    ("the parser keeps deletions and additions apart",
     fn () =>
       modifiers_of
         ("by (auto simp del: map_of_eq_Some_iff " ^
          "simp: map_of_eq_Some_iff [symmetric])")
       = [benchRecipe.SimpDelete ["map_of_eq_Some_iff"],
          benchRecipe.SimpAdd ["map_of_eq_Some_iff[symmetric]"]])

val _ =
  check
    ("simp flip: reads its names right to left",
     fn () =>
       modifiers_of "by (auto simp flip: sorted_key_list_of_set_unique)"
       = [benchRecipe.SimpAdd
            ["sorted_key_list_of_set_unique[symmetric]"]])

val _ =
  check
    ("the parser attaches an attribute to the name it qualifies",
     fn () =>
       benchRecipe.cited_names
         (parses "by (blast dest!: set_update_subset_insert [THEN subsetD])")
       = ["set_update_subset_insert[THEN subsetD]"])

val _ =
  check
    ("the parser keeps a quoted term inside its attribute",
     fn () =>
       benchRecipe.cited_names
         (parses "by (blast intro: image_eqI [where ?x = \"u - {a}\" for u])")
       = ["image_eqI[where ?x = \"u - {a}\" for u]"])

val _ =
  check
    ("the parser reads using premises",
     fn () =>
       let
         val {facts, methods, ...} =
           parses "using takeWhile_eq_Nil_iff by fastforce"
       in
         facts = ["takeWhile_eq_Nil_iff"] andalso
         map #name methods = ["fastforce"]
       end)

(* [OF assms] cites the fact resolved against the enclosing lemma's
   assumptions, which the translation states as the goal's leading
   antecedents.  The goals below are not corpus entries: the corpus
   states this citation about a list and a predicate the translation
   names after Isabelle's, and these name their own. *)
local
  val list_source = "src/HOL/List.thy:1"
  val resolved_goal =
    ``(?b_item. MEM b_item (v_ys0 : num list) /\ v_Q0 b_item) ==>
      v_result0``
  val citation = "using split_list_prop [OF assms] by blast"
  fun supplied goal =
    List.mapPartial benchLib.named_theorem
      (benchLib.recipe_arguments (benchDerive.recipe_of list_source goal
                                    citation))
in
val _ =
  check
    ("a citation resolved against the assumptions is supplied at their " ^
     "instance",
     fn () =>
       let
         val (antecedent, _) = boolSyntax.dest_imp resolved_goal
         fun premise_of ({theorem, ...} : benchLib.named_thm) =
           Lib.total (fst o boolSyntax.dest_imp) (Thm.concl theorem)
       in
         List.exists
           (fn fact =>
             case premise_of fact of
                 SOME premise => aconv premise antecedent
               | NONE => false)
           (supplied resolved_goal)
       end)

val _ =
  check
    ("a citation no assumption of the goal matches is an error",
     fn () =>
       ((supplied ``v_result0 : bool``; false)
        handle Portable.Interrupt => raise Portable.Interrupt
             | benchRecipe.Unparseable _ => true))
end

val _ =
  check
    ("the parser reads unfolding names",
     fn () =>
       let
         val {unfolded, methods, ...} =
           parses "unfolding rel_fun_def rel_set_def set_Cons_def by fastforce"
       in
         unfolded = ["rel_fun_def", "rel_set_def", "set_Cons_def"] andalso
         map #name methods = ["fastforce"]
       end)

val _ =
  check
    ("the parser reads a terminal method after the first",
     fn () =>
       map #name (#methods (parses "by auto (auto elim!: le_funE)"))
       = ["auto", "auto"])

(* Isabelle's [+] repeats the method it follows.  The corpus records the
   source method verbatim, so the grammar has to carry the combinator
   rather than the transcription dropping it. *)
val _ =
  check
    ("the parser reads the + repetition combinator",
     fn () =>
       let
         val {methods, ...} =
           parses "unfolding listrel1_def by auto (blast intro: le_funE)+"
       in
         map #name methods = ["auto", "blast"] andalso
         map #repeated methods = [false, true]
       end)

val _ =
  check
    ("+ survives the render round trip",
     fn () =>
       benchRecipe.render (parses "by auto (blast intro: le_funE)+")
       = "by auto (blast intro: le_funE)+")

val _ =
  check
    ("a repeated method becomes a repeated recipe",
     fn () =>
       let
         val once =
           benchLib.recipe_name
             (benchDerive.recipe_of classical_source ``!x : bool. x \/ ~x``
                "by blast")
         val repeated =
           benchLib.recipe_name
             (benchDerive.recipe_of classical_source ``!x : bool. x \/ ~x``
                "by blast+")
       in
         repeated = "repeat(" ^ once ^ ")"
       end)

(* [metis] takes its facts unkeyed, so a bare name run inside a method
   is that method's fact list rather than a parse error. *)
val _ =
  check
    ("the parser reads an unkeyed fact list",
     fn () =>
       modifiers_of "by (metis in_set_conv_decomp)"
       = [benchRecipe.Facts ["in_set_conv_decomp"]] andalso
       benchRecipe.render (parses "by (metis in_set_conv_decomp)")
       = "by (metis in_set_conv_decomp)")

(* [list.distinct(1)] names one equation of a multi-clause fact.  The
   index belongs to the name; [by(auto ...)] still opens a method. *)
val _ =
  check
    ("the parser reads an indexed fact name",
     fn () =>
       modifiers_of "by (metis dropWhile_eq_Nil_conv list.distinct(1))"
       = [benchRecipe.Facts ["dropWhile_eq_Nil_conv", "list.distinct(1)"]]
       andalso
       map #name (#methods (parses "by(auto simp: dom_def)")) = ["auto"])

val _ =
  check
    ("the parser drops an Isabelle comment",
     fn () =>
       benchRecipe.render (parses "by blast (* somewhat slow *)")
       = "by blast")

val _ =
  check
    ("add: is a simpset entry",
     fn () =>
       modifiers_of "by (simp add: sq_def)"
       = [benchRecipe.SimpAdd ["sq_def"]])

val _ =
  check
    ("an uncovered method string is an error, not a bare tactic",
     fn () =>
       parse_fails "apply (induct xs) apply simp done" andalso
       parse_fails "by (auto frobnicate: x)" andalso
       parse_fails "by (auto simp add:)")

val _ =
  check
    ("rendering a parsed method is idempotent",
     fn () =>
       let
         fun stable text =
           let val once = benchRecipe.render (parses text)
               val twice = benchRecipe.render (parses once)
           in
             once = twice orelse
             (print ("\n  " ^ text ^ "\n  -> " ^ once ^ "\n  -> " ^
                     twice ^ "\n"); false)
           end
       in
         List.all stable
           ["by blast", "by (simp add: dom_def)", "by(auto simp: Pow_def)",
            "using assms by (simp add: collinear_def)",
            "unfolding mono_def by auto",
            "by auto (auto elim!: le_funE)",
            "by (auto simp del: X simp: X [symmetric])"]
       end)

(* Every Isabelle method string in the corpus parses.  This is the
   coverage claim B1 makes: no fallback, no hand-written override. *)
fun from_isabelle (entry : benchLib.corpus_goal) =
  String.isPrefix "src/HOL/" (#file (#provenance entry))

val corpus_goals =
  List.concat (map #goals parityLib.families)

val corpus_methods =
  let
    val seen = ref ([] : string list)
    fun note method =
      if List.exists (equal method) (!seen) then ()
      else seen := method :: !seen
  in
    app (note o #source_method) corpus_goals;
    List.rev (!seen)
  end

val unparseable_methods =
  List.filter
    (fn method =>
      ((benchRecipe.parse method; false)
       handle Portable.Interrupt => raise Portable.Interrupt
            | benchRecipe.Unparseable _ => true))
    corpus_methods

val _ =
  check
    ("every Isabelle method string in the corpus parses",
     fn () =>
       (if null unparseable_methods then ()
        else
          print
            ("\nunparseable: " ^
             String.concatWith "\n             " unparseable_methods ^ "\n");
        null unparseable_methods))

(* ---- Phase B: the name table ------------------------------------- *)

(* Every name an Isabelle method cites has to resolve, or the recipe
   cannot be derived from the method. *)
val cited_by_corpus =
  let
    val seen = ref ([] : string list)
    fun note name =
      if List.exists (equal name) (!seen) then () else seen := name :: !seen
  in
    app (fn method => app note (benchRecipe.cited_names
                                  (benchRecipe.parse method)))
      corpus_methods;
    List.rev (!seen)
  end

val unresolved_names =
  List.filter (fn name => not (isSome (benchNames.lookup name)))
    cited_by_corpus

val _ =
  check
    ("the name table covers every name the corpus cites",
     fn () =>
       (if null unresolved_names then ()
        else
          print
            ("\nunresolved (" ^ Int.toString (length unresolved_names) ^
             " of " ^ Int.toString (length cited_by_corpus) ^ "):\n" ^
             String.concatWith "\n" unresolved_names ^ "\n");
        null unresolved_names))

(* A citation that names no theorem has to say why.  [Native] is the
   one kind an agent could abuse to make a shortfall disappear, so the
   table's whole native set is pinned here by name. *)
val native_citations =
  List.filter
    (fn name =>
      case benchNames.resolve name of
          benchNames.Native => true
        | _ => false)
    benchNames.names

val _ =
  check
    ("only the documented citations resolve as engine-native",
     fn () =>
       Portable.sort (fn a => fn b => String.<= (a, b)) native_citations =
       ["arg_cong2[where f=nths, OF refl]", "classical",
        "exI[where ?x = \"- u\" for u]", "if_split_asm", "if_splits",
        "nat_less_le", "pairwiseI"])

(* The ambient context carries a few results Isabelle declares simp
   about a translated constant, which its simp step has and a context
   of definitions alone does not.  That is the source's own context and
   never a goal's answer.  Two Isabelle facts can translate onto one
   HOL4 theorem, so a declared result can be a corpus goal's statement
   -- [map_add_find_right] is map_L887 once [map_le] is unfolded -- and
   what has to hold is that the goal is then measured without it, the
   same test rule A1 applies to a supplied fact. *)
val _ =
  check
    ("a declared result that states a corpus goal is withheld there",
     fn () =>
       let
         val goals =
           benchClassical.goals @ benchSets.goals @ benchListMap.goals @
           benchLinarith.goals
         fun states ({theorem, ...} : benchLib.named_thm)
                    ({goal, ...} : benchLib.corpus_goal) =
           benchLib.theorem_is_goal goal theorem
         fun offered ({goal, ...} : benchLib.corpus_goal) argument =
           benchLib.permitted_for goal argument
         val ambient =
           List.mapPartial
             (fn benchLib.RewriteAdd named =>
                   SOME (named, benchLib.RewriteAdd named)
               | _ => NONE)
             benchAmbient.arguments
         fun declared (named : benchLib.named_thm) =
           List.exists
             (fn other : benchLib.named_thm => #name other = #name named)
             benchAmbient.declared_results
         val declarations =
           List.filter (fn (named, _) => declared named) ambient
         fun withheld_where_it_states (named, argument) =
           List.all
             (fn entry =>
               not (states named entry) orelse not (offered entry argument))
             goals
         fun states_some (named, _) =
           List.exists (states named) goals
         fun offered_somewhere (_, argument) =
           List.exists (fn entry => offered entry argument) goals
         val conflicting = List.filter states_some declarations
       in
         not (null conflicting) andalso
         List.all withheld_where_it_states declarations andalso
         List.all offered_somewhere conflicting
       end)

(* A goal identifier in the table would make it a per-goal hint table. *)
val _ =
  check
    ("no corpus goal identifier appears in the name table",
     fn () =>
       let
         val identifiers = map #id corpus_goals
       in
         List.all
           (fn name =>
             List.all (fn id => not (String.isSubstring id name)) identifiers)
           benchNames.names
       end)

(* An entry nothing cites is somewhere to park a convenient lemma
   against a goal that does not exist yet -- the channel A2 closes,
   left open from the other end.  The table covers the corpus exactly. *)
val uncited_entries =
  List.filter
    (fn name => not (List.exists (equal name) cited_by_corpus))
    benchNames.names

val _ =
  check
    ("the name table carries no entry the corpus does not cite",
     fn () =>
       (if null uncited_entries then ()
        else
          print
            ("\nuncited (" ^ Int.toString (length uncited_entries) ^
             " of " ^ Int.toString (length benchNames.names) ^ "):\n" ^
             String.concatWith "\n" uncited_entries ^ "\n");
        null uncited_entries))

(* Two entries under one citation is two answers to one question, and
   [lookup] silently takes the first: the second is unreachable and can
   contradict the one that wins.  Five did -- three calling a citation
   unrepresented that the winning entry resolves to a translation
   lemma, two naming a different translation lemma for it. *)
val repeated_entries =
  let
    fun repeats [] = []
      | repeats (name :: rest) =
          (if List.exists (equal name) rest then [name] else []) @
          repeats (List.filter (not o equal name) rest)
  in
    repeats benchNames.names
  end

val _ =
  check
    ("the name table answers each citation once",
     fn () =>
       (if null repeated_entries then ()
        else
          print
            ("\nrepeated:\n" ^ String.concatWith "\n" repeated_entries ^
             "\n");
        null repeated_entries))

(* The deferral table names citations, so an entry that names nothing
   the table answers is a rule that moved or was renamed, and its
   deferral silently stops applying.  The fragment rewrites with
   REWR_CONV, which a conditional statement does not reach: a deferred
   citation whose theorem is not an unconditional equation would be
   installed and never fire, and the goal would look as it does with
   the rule absent.  What the table decides is also checked where it
   lands: a goal citing [set_zip] is handed it as the bottom-up
   argument and not as a plain rewrite. *)
val _ =
  check
    ("every deferred citation is one the name table answers",
     fn () =>
       let
         fun equation theorem =
           let
             val statement = snd (boolSyntax.strip_forall (concl theorem))
           in
             Lib.can boolSyntax.dest_eq statement
           end
         fun answered citation =
           List.exists (equal citation) benchNames.names andalso
           not (null (benchNames.theorems citation)) andalso
           List.all (equation o #theorem) (benchNames.theorems citation)
       in
         List.all answered benchNames.normalised_subjects
       end)

val _ =
  check
    ("a deferred citation reaches its goal deferred",
     fn () =>
       let
         val recipe =
           benchDerive.recipe_of "src/HOL/List.thy:9999"
             ``!xs : 'a list. xs = xs``
             "by (auto simp add: set_zip)"
         val arguments = benchLib.recipe_arguments recipe
         fun deferred (benchLib.RewriteAddBottomUp {name, ...}) = SOME name
           | deferred _ = NONE
         fun plain (benchLib.RewriteAdd {name, ...}) = SOME name
           | plain _ = NONE
         val zip_name = "parityTranslation$source_set_zip"
       in
         List.exists (equal zip_name) (List.mapPartial deferred arguments)
         andalso
         not (List.exists (equal zip_name) (List.mapPartial plain arguments))
       end)

(* src/HOL/List.thy @ f7e02b7e: split_list is the implication and
   in_set_conv_decomp the equivalence, and only the equivalence builds a
   member back out of a decomposition.  The goal below is not a corpus
   entry and is not either rule -- it asks for that direction alone --
   and the first-order step is given nothing but what the citation
   resolves to. *)
val decomposition_membership_goal : Abbrev.goal =
  ([], ``!(value:'a) prefix suffix xs.
           xs = prefix ++ value::suffix ==> MEM value xs``)

fun metis_closes theorems =
  (case Tactical.VALID (metisLib.METIS_TAC theorems)
          decomposition_membership_goal of
       ([], _) => true
     | _ => false)
  handle Portable.Interrupt => raise Portable.Interrupt
       | HOL_ERR _ => false

val _ =
  check
    ("the decomposition citation resolves to the equivalence",
     fn () =>
       not (metis_closes [parityTranslationTheory.source_split_list]) andalso
       metis_closes
         (map #theorem (benchNames.theorems "in_set_conv_decomp")))

(* [source_takeWhile] names HOL4's [takeWhile] rather than restating its
   clauses, which is what lets a library result about that walk meet a
   goal posed over the source constant.  The goal below is not a corpus
   entry and is no translated result's statement, and the fact it is
   given is one the translation does not carry: with a second copy of
   the equations the constant is opaque to it and the goal needs an
   induction instead. *)
val translated_walk_goal : Abbrev.goal =
  ([], ``!P xs.
           LENGTH (parityTranslation$source_takeWhile P xs) <=
           LENGTH (xs:'a list)``)

val _ =
  check
    ("a library result reaches the translated walk",
     fn () =>
       (case Tactical.VALID
               (clasimpLib.AUTO_TAC
                  [parityTranslationTheory.source_takeWhile_def,
                   listTheory.LENGTH_takeWhile_LESS_EQ])
               translated_walk_goal of
            ([], _) => true
          | _ => false)
       handle Portable.Interrupt => raise Portable.Interrupt
            | HOL_ERR _ => false)

(* src/HOL/Relation.thy:456 @ Isabelle2025-2: [sym_def] states symmetry
   as an implication, where HOL4's [symmetric_def] states it as an
   equivalence.  Rewriting with the equivalence leaves the two sides of
   one statement facing each other under two spellings of a bound, and
   no simplifier reads one side of an equivalence as context for the
   other.  The goal below is not a corpus entry and is neither
   statement: it is symmetry of a relation characterised by an equation
   and a bound that the equation moves. *)
val symmetry_through_a_moved_bound : Abbrev.goal =
  ([], ``!(measure : 'a -> num) (relation : num -> num -> bool).
           relation$symmetric
             (\left right.
                measure left = measure right /\
                !index. index < measure left ==> relation index index)``)

fun simp_closes theorems =
  (case Tactical.VALID
          (simpLib.SIMP_TAC (clasimpLib.clasimp_ss ()) theorems)
          symmetry_through_a_moved_bound of
       ([], _) => true
     | _ => false)
  handle Portable.Interrupt => raise Portable.Interrupt
       | HOL_ERR _ => false

val _ =
  check
    ("the symmetry citation resolves to the implication",
     fn () =>
       not (simp_closes [relationTheory.symmetric_def]) andalso
       simp_closes (map #theorem (benchNames.theorems "sym_def")))

(* [source_dropWhile_eq_self_iff] reads the walk stopping where it
   started as the list being empty or its head being kept, and states
   that head as HOL4's HD, the way its [takeWhile] counterpart does.
   The empty disjunct covers the one list on which the source's own [hd]
   and HD differ, so nothing of the source reading is given up, and a
   library result about a head -- here the ambient [hd_replicate]
   analogue -- can meet the other disjunct.  The goal below is not a
   corpus entry and is no translated result's statement: stated over the
   translation's own [source_hd] the head of the replicate is opaque and
   the goal does not close. *)
val translated_head_goal : Abbrev.goal =
  ([], ``!P n x. n <> 0 /\ P x ==>
           dropWhile P (REPLICATE n (x:'a)) <> REPLICATE n x``)

val _ =
  check
    ("the source's stopped walk reads its head as the library's",
     fn () =>
       (case Tactical.VALID
               (clasimpLib.AUTO_TAC
                  [parityTranslationTheory.source_dropWhile_eq_self_iff])
               translated_head_goal of
            ([], _) => true
          | _ => false)
       handle Portable.Interrupt => raise Portable.Interrupt
            | HOL_ERR _ => false)

(* An [of ...] attribute fills the source lemma's schematic positions,
   and the translation does not preserve their order: HOL4 states
   [dropWhile_append1] with its predicate first where Isabelle's
   statement reaches the list first, so an instance counted off the
   method's positions would put the list where the predicate belongs and
   name a fact about neither.  The instances below are the ones the two
   methods wrote, at the variables the translated goals carry; the
   position the method leaves open stays quantified. *)
val cited_instances =
  [("dropWhile_append1[of _ xs P ys]",
    ``!item.
        MEM item v_xs0 ==> ~v_P0 item ==>
        dropWhile v_P0 (v_xs0 ++ v_ys0) = dropWhile v_P0 v_xs0 ++ v_ys0``),
   ("takeWhile_eq_Nil_iff[of P xs]",
    ``takeWhile v_P0 v_xs0 = [] <=> v_xs0 = [] \/ ~v_P0 (HD v_xs0)``)]

val _ =
  check
    ("an instantiating citation resolves to the instance it names",
     fn () =>
       List.all
         (fn (citation, expected) =>
            case map #theorem (benchNames.theorems citation) of
                [theorem] => aconv (concl theorem) expected
              | _ => false)
         cited_instances)

(* ---- Phase B: the method dispatcher ------------------------------- *)

val corpus_method_heads =
  let
    val seen = ref ([] : string list)
    fun note name =
      if List.exists (equal name) (!seen) then () else seen := name :: !seen
  in
    app (fn method => app note (benchRecipe.method_heads
                                  (benchRecipe.parse method)))
      corpus_methods;
    List.rev (!seen)
  end

val uncovered_heads =
  List.filter
    (fn head => not (List.exists (equal head) benchTactics.methods))
    corpus_method_heads

val _ =
  check
    ("the dispatcher covers every method head the corpus uses",
     fn () =>
       (if null uncovered_heads then ()
        else
          print
            ("\nuncovered heads: " ^
             String.concatWith ", " uncovered_heads ^ "\n");
        null uncovered_heads))

val _ =
  check
    ("an uncovered Isabelle method is an error, not a default tactic",
     fn () =>
       raises_with ["no HOL4 tactic", "sledgehammer"]
         (fn () => benchTactics.tactic "sledgehammer"))

(* ---- Phase B: recipes derived from the source method -------------- *)

(* The end-to-end claim Phase B makes: what the harness runs on a
   translated goal follows from the method string and the goal alone.
   A corpus entry has no recipe field to write, so this cannot be
   satisfied by editing entries; it fails if a goal reaches the harness
   by any route other than [benchDerive.prepare]. *)
fun derivation_mismatch (entry : benchLib.corpus_goal) =
  let
    val derived =
      benchDerive.recipe_of
        (#file (#provenance entry) ^ ":" ^
         Int.toString (#line (#provenance entry)))
        (#goal entry) (#source_method entry)
  in
    if benchLib.recipe_name derived = benchLib.recipe_name (#recipe entry)
    then NONE
    else
      SOME (#id entry ^ ":\n    run     " ^
            benchLib.recipe_name (#recipe entry) ^ "\n    derived " ^
            benchLib.recipe_name derived)
  end
  handle Portable.Interrupt => raise Portable.Interrupt
       | exn => SOME (#id entry ^ ": " ^ Feedback.exn_to_string exn)

val mismatched = List.mapPartial derivation_mismatch corpus_goals

val _ =
  check
    ("every translated goal runs the recipe its source method denotes",
     fn () =>
       (if null mismatched then ()
        else
          print
            ("\n  " ^
             String.concatWith "\n  " (List.take (mismatched, 10)) ^
             "\n  (" ^ Int.toString (length mismatched) ^ " in all)\n");
        null mismatched))

(* A recipe is derived from an Isabelle method, so a goal from anywhere
   else has nothing to be measured against. *)
val _ =
  check
    ("every corpus goal comes from Isabelle",
     fn () => List.all from_isabelle corpus_goals)

fun registered_definition theorem =
  List.exists
    (fn location =>
      let
        val name =
          case location of
              DB.Local local_name => local_name
            | DB.Stored stored_name => KernelSig.name_toString stored_name
      in
        String.isSuffix "_def" name orelse String.isSuffix "_DEF" name
      end)
    (DB.revlookup theorem)

fun argument_theorem (benchLib.RewriteAdd {theorem, ...}) = SOME theorem
  | argument_theorem (benchLib.RewriteAddBottomUp {theorem, ...}) =
      SOME theorem
  | argument_theorem (benchLib.SplitAdd {theorem, ...}) = SOME theorem
  | argument_theorem (benchLib.IntroAdd (_, {theorem, ...})) = SOME theorem
  | argument_theorem (benchLib.ElimAdd (_, {theorem, ...})) = SOME theorem
  | argument_theorem (benchLib.DestAdd (_, {theorem, ...})) = SOME theorem
  | argument_theorem (benchLib.CongruenceAdd {theorem, ...}) = SOME theorem
  | argument_theorem (benchLib.FactAdd {theorem, ...}) = SOME theorem
  | argument_theorem (benchLib.DefinitionAdd {theorem, ...}) =
      if registered_definition theorem then NONE else SOME theorem
  | argument_theorem (benchLib.IffAdd {theorem, ...}) = SOME theorem
  | argument_theorem (benchLib.RewriteDelete _) = NONE

fun argument_name (benchLib.RewriteAdd {name, ...}) = SOME name
  | argument_name (benchLib.RewriteAddBottomUp {name, ...}) = SOME name
  | argument_name (benchLib.SplitAdd {name, ...}) = SOME name
  | argument_name (benchLib.IntroAdd (_, {name, ...})) = SOME name
  | argument_name (benchLib.ElimAdd (_, {name, ...})) = SOME name
  | argument_name (benchLib.DestAdd (_, {name, ...})) = SOME name
  | argument_name (benchLib.CongruenceAdd {name, ...}) = SOME name
  | argument_name (benchLib.FactAdd {name, ...}) = SOME name
  | argument_name (benchLib.DefinitionAdd {name, ...}) = SOME name
  | argument_name (benchLib.IffAdd {name, ...}) = SOME name
  | argument_name (benchLib.RewriteDelete _) = NONE

fun recipe_theorems (benchLib.Invoke (_, arguments)) =
      List.mapPartial argument_theorem arguments
  | recipe_theorems (benchLib.Then (left, right)) =
      recipe_theorems left @ recipe_theorems right
  | recipe_theorems (benchLib.AllGoals (left, right)) =
      recipe_theorems left @ recipe_theorems right
  | recipe_theorems (benchLib.Repeat inner) = recipe_theorems inner

fun recipe_argument_names (benchLib.Invoke (_, arguments)) =
      List.mapPartial argument_name arguments
  | recipe_argument_names (benchLib.Then (left, right)) =
      recipe_argument_names left @ recipe_argument_names right
  | recipe_argument_names (benchLib.AllGoals (left, right)) =
      recipe_argument_names left @ recipe_argument_names right
  | recipe_argument_names (benchLib.Repeat inner) =
      recipe_argument_names inner

fun first_recipe_arguments (benchLib.Invoke (_, arguments)) = arguments
  | first_recipe_arguments (benchLib.Then (left, _)) =
      first_recipe_arguments left
  | first_recipe_arguments (benchLib.AllGoals (left, _)) =
      first_recipe_arguments left
  | first_recipe_arguments (benchLib.Repeat inner) =
      first_recipe_arguments inner

fun last_recipe_arguments (benchLib.Invoke (_, arguments)) = arguments
  | last_recipe_arguments (benchLib.Then (_, right)) =
      last_recipe_arguments right
  | last_recipe_arguments (benchLib.AllGoals (_, right)) =
      last_recipe_arguments right
  | last_recipe_arguments (benchLib.Repeat inner) =
      last_recipe_arguments inner

fun without_argument_names names arguments =
  List.filter
    (fn argument =>
      case argument_name argument of
          SOME name => not (List.exists (equal name) names)
        | NONE => true)
    arguments

val every_corpus_goal =
  benchClassical.goals @ benchSets.goals @ benchListMap.goals @
  benchLinarith.goals

(* A [split:] element the splitter cannot analyse is dropped with a
   warning, and the goal is then measured under a method it was not
   given.  Isabelle's [t.split] is the datatype package's rule and HOL4's
   counterpart is derived from TypeBase; the [t_case_eq] theorems are
   equations about a case term -- [list_CASE x v f = v' <=> ...] -- and
   are not split rules at all. *)
fun split_argument (benchLib.SplitAdd {name, theorem}) = SOME (name, theorem)
  | split_argument _ = NONE

fun recipe_splits (benchLib.Invoke (_, arguments)) =
      List.mapPartial split_argument arguments
  | recipe_splits (benchLib.Then (left, right)) =
      recipe_splits left @ recipe_splits right
  | recipe_splits (benchLib.AllGoals (left, right)) =
      recipe_splits left @ recipe_splits right
  | recipe_splits (benchLib.Repeat inner) = recipe_splits inner

val corpus_split_arguments =
  List.concat
    (map (fn ({recipe, ...} : benchLib.corpus_goal) => recipe_splits recipe)
       every_corpus_goal)

val unusable_split_arguments =
  List.filter
    (fn (_, theorem) => not (can splitLib.split_forms theorem))
    corpus_split_arguments

val _ =
  check
    ("every recipe split rule is one the splitter applies",
     fn () =>
       (if null unusable_split_arguments then ()
        else
          print
            ("\nunusable splits: " ^
             String.concatWith ", " (map #1 unusable_split_arguments) ^ "\n");
        not (null corpus_split_arguments) andalso
        null unusable_split_arguments))

val direct_recipe_goals =
  List.filter
    (fn ({goal, recipe, ...} : benchLib.corpus_goal) =>
      List.exists (benchLib.theorem_is_goal goal) (recipe_theorems recipe))
    every_corpus_goal

val _ =
  check
    ("no benchmark recipe supplies its measured theorem",
     fn () =>
       if null direct_recipe_goals then true
       else
         (print
            ("\ncircular recipes: " ^
             String.concatWith ", "
               (map
                 (fn ({id, goal, recipe, ...} : benchLib.corpus_goal) =>
                   id ^ "=[" ^
                   String.concatWith ", "
                     (List.mapPartial argument_name
                       (List.filter
                         (fn argument =>
                           case argument_theorem argument of
                               SOME theorem =>
                                 benchLib.theorem_is_goal goal theorem
                             | NONE => false)
                         (let
                            fun arguments (benchLib.Invoke (_, args)) = args
                              | arguments (benchLib.Then (left, right)) =
                                  arguments left @ arguments right
                              | arguments
                                  (benchLib.AllGoals (left, right)) =
                                  arguments left @ arguments right
                              | arguments (benchLib.Repeat inner) =
                                  arguments inner
                          in
                            arguments recipe
                          end))) ^ "]")
                 direct_recipe_goals) ^ "\n");
          false))

(* A rule argument only reaches the search if the claset accepts the
   mapped theorem in the role the method gives it.  clasetRules rejects a
   shape it cannot canonicalise -- an equivalence offered as an
   elimination, say -- and the goal then fails before any search, which a
   shortfall record would misread as an engine limitation.  Auditing
   every corpus recipe keeps that a name-table error. *)
fun classical_rule_spec argument =
  let
    fun spec kind strength =
      SOME {kind = kind, safe = strength = benchLib.SafeRule, prio = NONE}
  in
    case argument of
        benchLib.IntroAdd (strength, _) => spec clasetRules.Intro strength
      | benchLib.ElimAdd (strength, _) => spec clasetRules.Elim strength
      | benchLib.DestAdd (strength, _) => spec clasetRules.Dest strength
      | _ => NONE
  end

fun recipe_arguments (benchLib.Invoke (_, arguments)) = arguments
  | recipe_arguments (benchLib.Then (left, right)) =
      recipe_arguments left @ recipe_arguments right
  | recipe_arguments (benchLib.AllGoals (left, right)) =
      recipe_arguments left @ recipe_arguments right
  | recipe_arguments (benchLib.Repeat inner) = recipe_arguments inner

fun uninstallable_rule_arguments recipe =
  List.mapPartial
    (fn argument =>
      case (classical_rule_spec argument, argument_name argument,
            argument_theorem argument) of
          (SOME spec, SOME name, SOME theorem) =>
            if can (clasetLib.add_rule spec (name, theorem))
                 clasetLib.empty_cs
            then NONE
            else SOME name
        | _ => NONE)
    (recipe_arguments recipe)

val goals_with_uninstallable_rules =
  List.mapPartial
    (fn ({id, recipe, ...} : benchLib.corpus_goal) =>
      case uninstallable_rule_arguments recipe of
          [] => NONE
        | names => SOME (id ^ "=[" ^ String.concatWith ", " names ^ "]"))
    every_corpus_goal

val _ =
  check
    ("every corpus rule argument is installable in its declared role",
     fn () =>
       if null goals_with_uninstallable_rules then true
       else
         (print
            ("\nrules the claset refuses: " ^
             String.concatWith ", " goals_with_uninstallable_rules ^ "\n");
          false))

fun goal_named id goals =
  case List.filter
         (fn ({id = candidate, ...} : benchLib.corpus_goal) =>
           candidate = id) goals of
      [goal] => goal
    | _ => raise mk_HOL_ERR "selftest" "goal_named" id

(* The engine tests below name their own recipe.  A corpus entry's
   recipe is derived from its Isabelle method string, so reading one
   here would make an engine test change meaning whenever the
   derivation does; what is under test is the tactic, not the
   derivation. *)
val linarith_recipe = benchLib.Invoke (benchLib.Linarith, [])
val blast_recipe = benchLib.Invoke (benchLib.Blast, [])
val auto_recipe = benchLib.Invoke (benchLib.Auto, [])

val absolute_recurrence_goal =
  recipe_goal "unit-absolute-recurrence" linarith_recipe
    (#goal (goal_named "presburger_L102" benchLinarith.goals))

val _ =
  check
    ("absolute recurrence uses the deterministic pruned split tree",
     fn () =>
       let
         val outcome =
           benchLib.run_goal (Time.fromSeconds 5)
             linarith_recipe absolute_recurrence_goal
         val {nodes, refutations, disjunction_splits,
              operator_splits, augmentations} =
           linarithLib.last_search_stats ()
       in
         benchLib.outcome_solved outcome andalso
         nodes = 363 andalso refutations = 243 andalso
         disjunction_splits = 121 andalso operator_splits = 120 andalso
         operator_splits < 511 andalso augmentations = 0
       end)

val satisfiable_absolute_value_goal : benchLib.corpus_goal =
  {id = "unit-satisfiable-absolute-value",
   goal = ``ABS (x : int) = x``, source_method = "arith soundness",
   recipe = benchLib.Invoke (benchLib.Linarith, []), excl = [],
   provenance = provenance, representative = true}

val _ =
  check
    ("interleaved sign splitting rejects a satisfiable sign system",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 5)
             (#recipe satisfiable_absolute_value_goal)
             satisfiable_absolute_value_goal)))

(* The recipe's set-equality pass reads an equation as a membership,
   which is the reading HOL4 states its set and list facts on and the
   wrong one where a side is a predicate short of an argument:
   [source_superset] is defined applied to both its arguments, so
   [element IN source_superset xs] meets neither its definition nor
   anything else, and no rewrite brings the two readings back
   together.  The method's own [fun_eq_iff] is what says which reading
   is meant, so the pass stands down for it.  Read as an application
   instead, both sides unfold and the goal is a membership fact about
   two appended lists.  A constant the ambient simpset unfolds --
   [EVERY] is one -- recovers from the membership reading and shows
   nothing here.  The goal is not a corpus entry, and every rewrite is
   cited by the recipe rather than ambient. *)
val supplied_reading_recipe =
  benchLib.Invoke
    (benchLib.Auto,
     [benchLib.RewriteAdd
        {name = "fun_eq_iff", theorem = boolTheory.FUN_EQ_THM},
      benchLib.RewriteAdd
        {name = "list_all_iff", theorem = listTheory.EVERY_MEM},
      benchLib.RewriteAdd
        {name = "superset_def",
         theorem = parityTranslationTheory.source_superset_def},
      benchLib.RewriteAdd
        {name = "list_all_def",
         theorem = parityTranslationTheory.source_list_all_def}])

val _ =
  check
    ("a rewrite the method named decides the reading of an equation",
     fn () =>
       recipe_solves supplied_reading_recipe
         ``!bench_unit_xs bench_unit_zs.
             parityTranslation$source_superset
               (bench_unit_xs ++ bench_unit_zs) =
             \bench_unit_ys.
               parityTranslation$source_list_all
                 (\bench_unit_v.
                    MEM bench_unit_v bench_unit_xs \/
                    MEM bench_unit_v bench_unit_zs)
                 bench_unit_ys``)

(* The pair rule is support for the translation's spelling of a set of
   pairs, and a goal with no pair in it neither needs it nor can afford
   it: it goes in as an assumption, and a universal assumption is
   instantiated afresh on every branch the search opens.  This goal
   closes in a third of a second when the rule is withheld and does not
   return inside the budget when it is not.  It is not a corpus entry. *)
val _ =
  check
    ("the pair rule is withheld from a goal with no pair in it",
     fn () =>
       recipe_solves (benchLib.Invoke (benchLib.Blast, []))
         ``(!s t. bench_apart s t <=> !x. x IN s ==> x NOTIN t) ==>
           bench_apart (A : 'a -> bool) B ==> bench_apart B A``)

val _ =
  check
    ("mapped BLAST distributes BIGINTER over pointwise intersection",
     fn () =>
       recipe_solves (benchLib.Invoke (benchLib.Blast, []))
         ``BIGINTER
             (IMAGE
               (\x : 'i.
                  (biginter_left : 'i -> 'a set) x INTER
                  (biginter_right : 'i -> 'a set) x)
               (biginter_family : 'i set)) =
           BIGINTER
             (IMAGE (biginter_left : 'i -> 'a set)
                (biginter_family : 'i set)) INTER
           BIGINTER
             (IMAGE (biginter_right : 'i -> 'a set)
                (biginter_family : 'i set))``)

val _ =
  check
    ("predicate abstraction handles a non-numeric datatype",
     fn () =>
       recipe_solves auto_recipe
         ``((!aset : bool set.
              T IN aset /\
              (!value. value IN aset ==> ~value IN aset) ==>
              F IN aset) /\
            (property : bool -> bool) T /\
            (!value. property value ==> property (~value))) ==>
           property F``)

val _ =
  check
    ("predicate abstraction instantiates a closure set comprehension",
     fn () =>
       recipe_solves auto_recipe
         ``((!aset : bool option set.
              NONE IN aset /\
              (!value. value IN aset ==> SOME T IN aset) ==>
              SOME T IN aset) /\
            (property : bool option -> bool) NONE /\
            (!value. property value ==> property (SOME T))) ==>
           property (SOME T)``)

(* What survives of the lfp-witness coverage is the soundness half.
   [lfp_witness_tac] reduces [?x. x = body x] to a monotonicity
   subgoal, and BLAST does not discharge that subgoal from general
   inputs: the positive cases here used to be closed by the fixed-point
   lemmas the corpus supplied, which is what A2 rejects.  The gap is
   recorded in the Phase C ledger against [set_theory_L79], and the
   positive cases belong with the fix. *)
val _ =
  check
    ("lfp witness rejects an antitone complement transformer",
     fn () =>
       not
         (recipe_solves blast_recipe
            ``?fixed : bool set. fixed = COMPL fixed``))

val _ =
  check
    ("predicate abstraction rejects an unsupported open pattern",
     fn () =>
       not
         (recipe_solves auto_recipe
            ``(!aset : bool set. T IN aset ==> T IN aset) ==>
              (property : bool -> bool) T``))

val _ =
  check
    ("predicate abstraction rejects a scope-escaping candidate",
     fn () =>
       let
         val recipe = auto_recipe
         (* Verify rejection after complete ambient preparation; allow
            shared-machine pauses without imposing a performance gate. *)
         val rejection_budget = Time.fromSeconds 60
         val target =
           ``(!aset : bool set.
                !hidden. hidden IN aset ==> hidden IN aset) ==>
             (property : bool -> bool) T``
       in
         case benchLib.run_goal rejection_budget recipe
                (recipe_goal "unit-scope-escape" recipe target) of
             benchLib.FAILED _ => true
           | _ => false
       end)

val _ =
  check
    ("predicate abstraction fairly tries competing set assumptions",
     fn () =>
       recipe_solves auto_recipe
         ``((!aset : bool set. T IN aset ==> T IN aset) /\
            (!aset : bool set. T IN aset ==> F IN aset) /\
            (property : bool -> bool) T) ==>
           property F``)

val sorted_wrt_distinction_goal =
  ``sorting$SORTED
      (\left right : num. right = SUC left) [0; 1; 2] /\
    ~parityTranslation$source_sorted_wrt
      (\left right : num. right = SUC left) [0; 1; 2]``

val _ =
  check
    ("source sorted_wrt is stronger than adjacent SORTED without transitivity",
     fn () =>
       aconv
         (Thm.concl
           parityTranslationTheory.source_sorted_wrt_not_adjacent)
         sorted_wrt_distinction_goal)

val fold_representation_distinction_goal =
  ``parityTranslation$source_fold CONS [0 : num; 1] [] =
      REVERSE [0; 1] /\
    REVERSE [0; 1] <> FOLDR CONS [] [0; 1]``

val _ =
  check
    ("source fold is not HOL4 FOLDR",
     fn () =>
       recipe_solves
         (benchLib.Invoke
            (benchLib.Simp,
             [benchLib.DefinitionAdd
                {name = "parityTranslation$source_fold_def",
                 theorem = parityTranslationTheory.source_fold_def}]))
         fold_representation_distinction_goal)

(* src/HOL/List.thy:226-231 @ f7e02b7e.  The source defines extract by
   dropWhile and takeWhile and proves every result about it by rewriting
   with those two, whose equations are ambient.  The goal below is not a
   corpus entry -- it walks two constructors and reads off the prefix --
   and the definition reaches it only when it is stated over the same
   decomposition; a paraphrase over some other one states the same
   function and leaves the walk with nothing to reduce it. *)
val extract_decomposition_goal =
  ``!predicate first second rest.
      ~predicate first ==> predicate second ==>
      parityTranslation$source_extract predicate (first::second::rest) =
        SOME ([first], second, rest)``

val _ =
  check
    ("the extract definition walks a list by the ambient equations",
     fn () =>
       recipe_solves
         (benchLib.Invoke
            (benchLib.Auto,
             [benchLib.DefinitionAdd
                {name = "parityTranslation$source_extract_def",
                 theorem = parityTranslationTheory.source_extract_def}]))
         extract_decomposition_goal)

(* src/HOL/List.thy @ f7e02b7e, dropWhile_eq_Cons_conv.  HOL4 states
   dropWhile_eq_nil for the empty result and dropWhile_eq_DROP for the
   index, and nothing that reads a nonempty result back as a
   decomposition of the list, so the name table used to answer the
   citation Unrepresented and the three extract results that name it
   were measured without it.  The goal below is not a corpus entry and
   is not the rule: it asks only for the rule's second conjunct, which
   no ambient dropWhile equation reaches -- the list the dropWhile ran
   down is a variable. *)
val dropWhile_cons_goal =
  ``!predicate xs head tail.
      dropWhile predicate xs = head::tail ==> ~predicate head``

val _ =
  check
    ("a nonempty dropWhile stops at a value its predicate rejects",
     fn () =>
       not (recipe_solves (benchLib.Invoke (benchLib.Auto, []))
              dropWhile_cons_goal) andalso
       recipe_solves
         (benchLib.Invoke
            (benchLib.Auto,
             [benchLib.RewriteAdd
                {name = "parityTranslation$source_dropWhile_eq_cons_conv",
                 theorem =
                   parityTranslationTheory.source_dropWhile_eq_cons_conv}]))
         dropWhile_cons_goal)

val _ =
  check
    ("rotation modulo normalization applies to an unrelated periodic function",
     fn () =>
       let
         val target =
           ``FUNPOW (v_iteration0 : 'a -> 'a) 3 v_value0 = v_value0 ==>
             FUNPOW v_iteration0 4 v_value0 =
             FUNPOW v_iteration0 (4 MOD 3) v_value0``
         val (premise, _) = boolSyntax.dest_imp target
         val instantiated =
           Q.SPECL [`v_iteration0 : 'a -> 'a`, `3`, `v_value0`, `4`]
             parityTranslationTheory.source_funpow_mod_periodic
         val theorem =
           DISCH premise (MP instantiated (ASSUME premise))
       in
         Term.aconv (Thm.concl theorem) target
       end)

val bool_negation_period =
  Tactical.prove
    (``FUNPOW (\value : bool. ~value) 2 T = T``,
     bossLib.simp[arithmeticTheory.FUNPOW_2])

val funpow_mod_zero_normalize =
  parityTranslationTheory.source_funpow_mod_zero_imp_normalize

val funpow_mod_zero_recipe =
  benchLib.Invoke
    (benchLib.Simp,
     [benchLib.RewriteAdd
        {name = "unit$source_funpow_mod_zero_imp_normalize",
         theorem = funpow_mod_zero_normalize},
      benchLib.RewriteAdd
        {name = "unit$bool_negation_period",
         theorem = bool_negation_period}])

val _ =
  check
    ("period-zero implication normalization is operation-generic",
     fn () =>
       recipe_solves funpow_mod_zero_recipe
         ``!count.
             count MOD 2 = 0 ==>
             FUNPOW (\value : bool. ~value) count T = T``)

(* The same goal with its parameter already fixed, which is how the
   generated corpus files state a source result and how the harness
   hands every goal to its method.  The rewrite is stated on the whole
   implication, so it is a redex of the conclusion as it stands and of
   nothing the premise-discharging simplifier leaves: the equation
   [FUNPOW ... T = T] simplifies to its left-hand side, and what the
   fixpoint rebuilds is no longer the term the rewrite spells. *)
val _ =
  check
    ("period-zero implication normalization reaches a fixed parameter",
     fn () =>
       recipe_solves funpow_mod_zero_recipe
         ``(bench_period_count : num) MOD 2 = 0 ==>
           FUNPOW (\value : bool. ~value) bench_period_count T = T``)

(* The generalization tests that used to sit here ran a corpus
   entry's recipe against a statement the corpus does not contain, so
   a tactic that recognised the corpus statement would fail them.
   Each took its recipe from a corpus entry that is now a registered
   shortfall -- the recipes they supplied were built from lemmas the
   Isabelle method never names, and a test whose base goal does not
   solve says nothing about recognition, so the test goes with the
   entry.  The entries were [list_L5409_nths_drop],
   [list_L6384_sorted_insort_insert_key], [list_L6453_sorted_transpose],
   [list_L6847_sorted_list_of_set_nonempty],
   [list_L6873_nth_sorted_list_of_set_greaterThanAtMost],
   [list_L3381_anon_L3381], [list_L5527_Nil_in_shufflesI],
   [list_L8673_these_set_code] and [list_L7954_listrel_iff_nth].
   Closing any of those shortfalls means restoring its generalization
   test in the same commit, as [list_L7508_lexord_trans]'s,
   [list_L7771_wf_measures]'s and [list_L7922_wf_listrel1_iff]'s are
   restored below.  The last two below
   are not restorations: [list_L7570_asym_lenlex] and
   [list_L7318_lenlex_length] never carried one, and gained one with
   the composite definition of [lenlex] that closed them. *)

fun retarget_goal id goal (base : benchLib.corpus_goal) =
  {id = id, goal = goal, source_method = #source_method base,
   recipe = #recipe base, excl = #excl base,
   provenance = #provenance base, representative = true}

val promoted_recovered_schema_goals =
  [retarget_goal "schema-abort-empty-card"
     ``parityTranslation$source_abort_empty_set
         (\domain : num set. CARD domain) = 0``
     (goal_named "list_L3349_anon_L3349" benchListMap.goals),
   retarget_goal "schema-lists-membership-mono"
     ``[1; 1] IN parityTranslation$source_lists ({1} : num set) ==>
       [1; 1] IN parityTranslation$source_lists ({1; 2} : num set)``
     (goal_named "list_L6972_mono_lists" benchListMap.goals),
   retarget_goal "schema-wf-finite-single-edge"
     ``relation$WF
         (set_relation$reln_to_rel
           (LIST_TO_SET [((1 : num), 2)])) <=>
       set_relation$acyclic (LIST_TO_SET [((1 : num), 2)])``
     (goal_named "list_L8709_wf_set" benchListMap.goals),
   retarget_goal "schema-lexord-transitive-lift"
     ``!relation : 'a -> 'a -> bool.
         relation$transitive relation ==>
         !left middle right.
           parityTranslation$source_lexord relation [left] [middle] ==>
           parityTranslation$source_lexord relation [middle] [right] ==>
           parityTranslation$source_lexord relation [left] [right]``
     (goal_named "list_L7508_lexord_trans" benchListMap.goals),
   retarget_goal "schema-wf-measures-inv-image"
     ``relation$WF
         (relation$inv_image
           (parityTranslation$source_measures [LENGTH; SUM])
           (REVERSE : num list -> num list))``
     (goal_named "list_L7771_wf_measures" benchListMap.goals),
   retarget_goal "schema-wf-listrel1-forward"
     ``!relation : num -> num -> bool.
         relation$WF relation ==>
         relation$WF (parityTranslation$source_listrel1 relation)``
     (goal_named "list_L7922_wf_listrel1_iff" benchListMap.goals),
   retarget_goal "schema-asym-lenlex-iterated"
     ``!relation : num -> num -> bool.
         parityTranslation$source_asym relation ==>
         parityTranslation$source_asym
           (parityTranslation$source_lenlex
             (parityTranslation$source_lenlex relation))``
     (goal_named "list_L7570_asym_lenlex" benchListMap.goals),
   retarget_goal "schema-subseqs-three-elements"
     ``({1; 3} : num set) IN
       IMAGE LIST_TO_SET
         (LIST_TO_SET
           (parityTranslation$source_subseqs [1; 2; 3]))``
     (goal_named "list_L5470_subset_subseqs" benchListMap.goals),
   retarget_goal "schema-lenlex-length-iterated"
     ``!relation : num -> num -> bool.
       !xs ys : num list list.
         parityTranslation$source_lenlex
           (parityTranslation$source_lenlex relation) xs ys ==>
         LENGTH xs <= LENGTH ys``
     (goal_named "list_L7318_lenlex_length" benchListMap.goals)]

val _ =
  check
    ("recovered dependency schemas generalize beyond corpus statements",
     fn () =>
       List.all
         (fn goal =>
           case benchLib.run_goal (Time.fromSeconds 5)
                  (#recipe goal) goal of
               benchLib.SOLVED _ => true
             | benchLib.TIMEOUT =>
                 (print ("\n" ^ #id goal ^ ": timeout\n"); false)
             | benchLib.FAILED message =>
                 (print ("\n" ^ #id goal ^ ": " ^ message ^ "\n");
                  false))
         promoted_recovered_schema_goals)

val literal_constructor_recipe =
  benchLib.Invoke
    (benchLib.Simp,
     [benchLib.DefinitionAdd
        {name = "parityTranslation$source_Literal_def",
         theorem = parityTranslationTheory.source_Literal_def},
      benchLib.RewriteAdd
        {name = "parityTranslation$source_literal_abs_11",
         theorem = parityTranslationTheory.source_literal_abs_11},
      benchLib.RewriteAdd
        {name = "parityTranslation$source_Literal_valid",
         theorem = parityTranslationTheory.source_Literal_valid},
      benchLib.RewriteAdd
        {name = "parityTranslation$source_Char_ascii_eq_iff",
         theorem = parityTranslationTheory.source_Char_ascii_eq_iff},
      benchLib.RewriteAdd
        {name = "parityTranslation$source_literal_explode_11",
         theorem = parityTranslationTheory.source_literal_explode_11},
      benchLib.RewriteAdd
        {name = "bool$CONJ_ASSOC",
         theorem = boolTheory.CONJ_ASSOC}])

val literal_empty_recipe =
  benchLib.Invoke
    (benchLib.Simp,
     [benchLib.DefinitionAdd
        {name = "parityTranslation$source_literal_empty_def",
         theorem = parityTranslationTheory.source_literal_empty_def},
      benchLib.DefinitionAdd
        {name = "parityTranslation$source_Literal_def",
         theorem = parityTranslationTheory.source_Literal_def},
      benchLib.DefinitionAdd
        {name = "parityTranslation$source_literal_valid_def",
         theorem = parityTranslationTheory.source_literal_valid_def},
      benchLib.RewriteAdd
        {name = "parityTranslation$source_literal_eq_iff_explode",
         theorem =
           parityTranslationTheory.source_literal_eq_iff_explode},
      benchLib.RewriteAdd
        {name = "parityTranslation$source_literal_explode_abs",
         theorem = parityTranslationTheory.source_literal_explode_abs},
      benchLib.RewriteAdd
        {name = "parityTranslation$source_Literal_valid",
         theorem = parityTranslationTheory.source_Literal_valid}])

val _ =
  check
    ("literal constructors are faithful to the subtype representation",
     fn () =>
       recipe_solves literal_constructor_recipe
         (Thm.concl parityTranslationTheory.source_Literal_eq_iff) andalso
       recipe_solves literal_empty_recipe
         (Thm.concl
            parityTranslationTheory.source_literal_empty_neq_Literal) andalso
       recipe_solves literal_empty_recipe
         (Thm.concl parityTranslationTheory.source_Literal_neq_empty))

val literal_implode_explode_recipe =
  benchLib.Invoke
    (benchLib.Simp,
     [benchLib.DefinitionAdd
        {name = "parityTranslation$source_literal_implode_def",
         theorem = parityTranslationTheory.source_literal_implode_def},
      benchLib.RewriteAdd
        {name = "parityTranslation$source_ascii_map_id",
         theorem = parityTranslationTheory.source_ascii_map_id},
      benchLib.RewriteAdd
        {name = "parityTranslation$source_literal_explode_valid",
         theorem = parityTranslationTheory.source_literal_explode_valid},
      benchLib.RewriteAdd
        {name = "parityTranslation$source_literal_abs_explode",
         theorem = parityTranslationTheory.source_literal_abs_explode}])

val literal_explode_implode_recipe =
  benchLib.Invoke
    (benchLib.Simp,
     [benchLib.DefinitionAdd
        {name = "parityTranslation$source_literal_implode_def",
         theorem = parityTranslationTheory.source_literal_implode_def},
      benchLib.RewriteAdd
        {name = "parityTranslation$source_literal_explode_abs",
         theorem = parityTranslationTheory.source_literal_explode_abs},
      benchLib.RewriteAdd
        {name = "parityTranslation$source_literal_implode_valid",
         theorem = parityTranslationTheory.source_literal_implode_valid}])

val _ =
  check
    ("literal implode and explode round-trip in both directions",
     fn () =>
       recipe_solves literal_implode_explode_recipe
         (Thm.concl
            parityTranslationTheory.source_literal_implode_explode) andalso
       recipe_solves literal_explode_implode_recipe
         (Thm.concl
            parityTranslationTheory.source_literal_explode_implode))

val ball_congruence_goal =
  ``parityTranslation$source_ball (carrier_domain : 'a set)
      (\x. x IN carrier_domain /\ predicate x) <=>
    parityTranslation$source_ball carrier_domain predicate``
val bex_congruence_goal =
  ``parityTranslation$source_bex (carrier_domain : 'a set)
      (\x. x IN carrier_domain /\ predicate x) <=>
    parityTranslation$source_bex carrier_domain predicate``
val image_congruence_goal =
  ``parityTranslation$source_image
      (\x. if x IN (carrier_domain : 'a set)
           then mapper x else other_mapper x)
      carrier_domain =
    parityTranslation$source_image (mapper : 'a -> 'b) carrier_domain``

fun congruence_recipe name theorem =
  benchLib.Invoke
    (benchLib.Simp,
     [benchLib.CongruenceAdd {name = name, theorem = theorem}])

val _ =
  check
    ("local ball congruence simplifies under bounded membership",
     fn () =>
       recipe_solves
         (congruence_recipe "parityTranslation$source_ball_cong_simp"
            parityTranslationTheory.source_ball_cong_simp)
         ball_congruence_goal andalso
       not
         (recipe_solves (benchLib.Invoke (benchLib.Simp, []))
            ball_congruence_goal))

val _ =
  check
    ("local bex congruence simplifies under bounded membership",
     fn () =>
       recipe_solves
         (congruence_recipe "parityTranslation$source_bex_cong_simp"
            parityTranslationTheory.source_bex_cong_simp)
         bex_congruence_goal andalso
       not
         (recipe_solves (benchLib.Invoke (benchLib.Simp, []))
            bex_congruence_goal))

val _ =
  check
    ("local image congruence simplifies under domain membership",
     fn () =>
       recipe_solves
         (congruence_recipe "parityTranslation$source_image_cong_simp"
            parityTranslationTheory.source_image_cong_simp)
         image_congruence_goal andalso
       not
         (recipe_solves (benchLib.Invoke (benchLib.Simp, []))
            image_congruence_goal))

fun family_ok expected run =
  let
    val result : benchLib.family_result =
      run (benchLib.selftest_level ())
  in
    length (#gated result) =
      (case OS.Process.getEnv "HOLBENCHGOAL" of
           NONE => expected
         | SOME ids => length (String.tokens (equal #",") ids))
  end

fun family_selected name =
  case OS.Process.getEnv "HOLBENCHFAMILY" of
      NONE => true
    | SOME selected => selected = name

fun count_cause cause shortfalls =
  length
    (List.filter
      (fn ({cause = item, ...} : benchLib.shortfall) => item = cause)
      shortfalls)

val _ =
  check
    ("exhaustive pinned-source accounting is exact",
     fn () =>
       let
         val source_outcomes =
           length benchClassical.goals + length benchSets.goals +
           length benchListMap.goals + length benchLinarith.goals +
           count_cause benchLib.TranslationGap benchSets.shortfalls +
           count_cause benchLib.TranslationGap benchListMap.shortfalls
       in
         source_outcomes = 1029
       end)

val all_shortfalls =
  benchClassical.shortfalls @ benchSets.shortfalls @
  benchListMap.shortfalls @ benchLinarith.shortfalls

(* The registers are not empty and are not meant to be: they carry the
   measured non-solutions.  What has to hold is that every record says
   something.  [UnderIteration] is a working marker, not a diagnosis,
   so no committed record may carry it; and a record with no date or no
   note is not a diagnosis either.

   A [TranslationGap] is the one classification that takes a source
   result out of the measurement, so the set is pinned by identifier
   rather than counted: declaring a new one is a failing test until it
   is signed here.  That such a record carries no executable goal is
   [benchLib.validate_corpus]'s check, not this one. *)
val translation_gaps =
  ["list_L8259_anon_L8259", "list_L8273_anon_L8273"]

fun translation_gap_ids shortfalls =
  map (#id : benchLib.shortfall -> string)
    (List.filter
      (fn ({cause, ...} : benchLib.shortfall) =>
        cause = benchLib.TranslationGap)
      shortfalls)

fun same_identifiers left right =
  length left = length right andalso
  List.all (fn id => List.exists (fn other => other = id) right) left

fun dated_and_explained (shortfall : benchLib.shortfall) =
  size (#date shortfall) = size "2026-08-20" andalso
  String.isPrefix "20" (#date shortfall) andalso
  size (#note shortfall) >= 20

val _ =
  check
    ("every shortfall record names a cause, a date and a reason",
     fn () =>
       count_cause benchLib.UnderIteration all_shortfalls = 0 andalso
       same_identifiers (translation_gap_ids all_shortfalls)
         translation_gaps andalso
       List.all dated_and_explained all_shortfalls)

val _ =
  check
    ("classical mined-corpus representative slice is exact",
     fn () =>
       not (family_selected "classical") orelse family_ok
         (if benchLib.selftest_level () >= 2 then 25 else 4)
         benchClassical.run)

val _ =
  check
    ("set mined-corpus representative slice is exact",
     fn () =>
       not (family_selected "sets") orelse
       family_ok
         (if benchLib.selftest_level () >= 2 then 353 else 4)
         benchSets.run)

val _ =
  check
    ("list/map mined-corpus representative slice is exact",
     fn () =>
       not (family_selected "listmap") orelse
       family_ok
         (if benchLib.selftest_level () >= 2 then 602 else 5)
         benchListMap.run)

val _ =
  check
    ("linear-arithmetic representative slice is exact",
     fn () =>
       not (family_selected "linarith") orelse family_ok
         (if benchLib.selftest_level () >= 2 then 47 else 4)
         benchLinarith.run)

(* A6.  Goal statements are owner-signed: a changed hash means a goal
   statement moved, which needs an explicit decision rather than an
   updated pin.  The List/map signature was last moved on the owner's
   decision to state [list_L8044_listrel1_subset_listrel]'s two
   inclusions folded, as relation$RSUBSET, rather than pointwise:
   Isabelle states both with its one subset, a relation being a set of
   pairs there, and unfolded the conclusion's LIST_REL stands at
   variable lists where auto's first simplification pass reads it --
   a step ahead of where the source's own method meets it, which
   Isabelle's [auto] fails at too when the lemma is restated that way.

   The decision before that stated [list_L7401_lexord_append_leftD]'s
   premise as its source does, [!item. ~relation item item] rather
   than [relation$irreflexive relation]: Isabelle's
   [lexord_append_leftD] states that premise unfolded, and rendering it
   through the HOL4 constant asked the assigned method to unfold a
   constant its method string does not name.

   The decision before that rendered Isabelle's [fun_upd] as a
   translation constant rather than inlining its body: seventeen goals
   carry an update, and against the inlined conditional none of the
   results Isabelle states of the unapplied constant can be stated at
   all.

   The Linarith signature moved on the owner's decision to drop the
   Presburger family, whose one [arith] goal joined this one.  The
   Classical signature moved with the Algebra family: the harness
   loaded ringLib for it, whose overload read [classical_L124]'s
   predicate variable [R] as [r.carrier]. *)
val goal_term_pins =
  [("Classical", "DF9E4108"), ("Sets", "7641FC9E"),
   ("List/map", "507D17D7"), ("Linarith", "3F5B7CE4")]

val _ =
  check
    ("A6 goal-term hashes match their pins",
     fn () =>
       length goal_term_pins = length parityLib.families andalso
       List.all
         (fn ({name, goals, ...} : parityLib.family) =>
           case List.find (fn (family, _) => family = name)
                  goal_term_pins of
               NONE => false
             | SOME (_, pin) => benchGuards.family_hash goals = pin)
         parityLib.families)

fun read_all path =
  let
    val stream = TextIO.openIn path
    val text = TextIO.inputAll stream
    val _ = TextIO.closeIn stream
  in
    text
  end

(* The measurement a report records beside its results: the times, and
   the date the run was made.  Two reports of the same corpus differ in
   both and agree on everything else, so the comparison below has to
   read past them -- and the date is the half that used to be a literal
   in the prose, which is how it came to date the numbers beside it
   eleven days early. *)
fun report date costs tail =
  "# Report\n\nThe report was generated on " ^ date ^
  " with a budget.\n\n## Cost of the solutions\n\n| a | " ^ costs ^
  " |\n\n## Next\n\n" ^ tail ^ "\n"

val _ =
  check
    ("the report comparison reads past the date and the costs",
     fn () =>
       parityLib.without_measurement (report "2026-01-02" "1" "kept") =
       parityLib.without_measurement (report "2026-09-08" "2" "kept")
         andalso
       parityLib.without_measurement (report "2026-01-02" "1" "kept") <>
       parityLib.without_measurement (report "2026-01-02" "1" "changed"))

(* The comparison measures the whole corpus, so it can only run where
   the whole corpus is what this run measures: a family run and a run
   without the battery each measure a part of it, and level 1 measures
   none.  Skipped rather than answered true in those runs -- answering
   true prints the same green row as a comparison that happened, and
   the family run is how the corpus is measured here, so the row has
   never meant what it says. *)
val whole_corpus_measured =
  benchLib.selftest_level () >= 2 andalso
  not (Option.isSome (OS.Process.getEnv "HOLBENCHFAMILY")) andalso
  OS.Process.getEnv "HOLBENCHNOBATTERY" <> SOME "1"

val _ =
  if whole_corpus_measured then
    check
      ("level-2 generated parity report matches the committed file \
       \outside its measurement",
       fn () =>
         parityLib.without_measurement (read_all "../PARITY.md") =
         parityLib.without_measurement (parityLib.render ()))
  else
    TextIO.print
      ("skipping the generated parity report comparison: this run \
       \measures part of the corpus\n")
