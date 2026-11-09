open HolKernel testutils

structure SelfTestTactical = Tactical
structure Tactical =
struct
  open SelfTestTactical
  fun VALID tactic goal =
    SelfTestTactical.VALID tactic goal (Context.snapshot())
end

(* check and residual come from linarithCorpus, which states the
   assertion helpers once for the suites that reach linear arithmetic;
   with_arith_fact below is from there too. *)
open linarithCorpus

fun rewrite_rhs ss tm =
  snd
    (boolSyntax.dest_eq
      (concl (Conv.QCONV (simpLib.SIMP_CONV ss []) tm)))

val _ =
  check
    ("aesop_simp settype and attribute are registered without collision",
     fn () =>
       List.exists (equal "aesop_simp") (ThmSetData.all_set_types ()) andalso
       ThmAttribute.is_attribute "aesop_simp")

val _ =
  check
    ("aesop trace is registered at levels one through three",
     fn () =>
       List.exists
         (fn Feedback.TraceElt {name, max, ...} =>
           name = "aesop" andalso max = 3)
         (Feedback.traces ()))

val _ =
  check
    ("aesop simpset fixes conditional-rewrite depth at forty",
     fn () =>
       #cond_depth
         (simpLib.traverseconfig_for_ss (aesopData.aesop_ss ())) =
       SOME 40)

val _ =
  check
    ("aesop simpset uses the clasimp safe solver stack",
     fn () =>
       null
         (residual
           (simpLib.GEN_GLOBAL_SIMP_TAC {safe = true}
             {base =
                {strip = false, elimvars = false, droptrues = false,
                 oldestfirst = false},
              concl_in_fixpoint = false, imp_rebuild = false,
              imp_premises = false}
             (simpLib.clear_rules (aesopData.aesop_ss ())) [])
           ([boolSyntax.F], ``aesop_safe_solver_goal:bool``)))

val derived_lhs = ``aesop_derived_lhs:'a``
val derived_rhs = ``aesop_derived_rhs:'a``
val derived_rule =
  ASSUME (boolSyntax.mk_eq (derived_lhs, derived_rhs))
val derived_before =
  rewrite_rhs (aesopData.aesop_ss ()) derived_lhs
val derived_after =
  BasicProvers.with_simpset_updates
    (fn ss =>
      simpLib.++
        (ss,
         simpLib.named_rewrites "aesop-selftest-derived" [derived_rule]))
    (fn () => rewrite_rhs (aesopData.aesop_ss ()) derived_lhs)
    ()
val derived_restored =
  rewrite_rhs (aesopData.aesop_ss ()) derived_lhs

val _ =
  check
    ("aesop simpset cache derives from srw_ss updates",
     fn () =>
       aconv derived_before derived_lhs andalso
       aconv derived_after derived_rhs andalso
       aconv derived_restored derived_lhs)

(* An attribute declaration is keyed on the theory it is made in.  This
   binary starts with no theory segment at all, so the tests from here
   on open one -- which is the state anything declaring is called in
   anyway. *)
val _ = Theory.new_theory "aesopSelftest"

val _ = Datatype.Datatype
  `aesop_clash_narrow =
   AesopClashN0 | AesopClashN1 | AesopClashN2 | AesopClashN3 |
   AesopClashN4 | AesopClashN5 | AesopClashN6 | AesopClashN7 |
   AesopClashN8 | AesopClashN9 | AesopClashN10 | AesopClashN11 |
   AesopClashN12 | AesopClashN13 | AesopClashN14`

val _ = Datatype.Datatype
  `aesop_clash_wide =
   AesopClashW0 | AesopClashW1 | AesopClashW2 | AesopClashW3 |
   AesopClashW4 | AesopClashW5 | AesopClashW6 | AesopClashW7 |
   AesopClashW8 | AesopClashW9 | AesopClashW10 | AesopClashW11 |
   AesopClashW12 | AesopClashW13 | AesopClashW14 | AesopClashW15 num`

val _ = Datatype.Datatype
  `aesop_clash_enum =
   AesopClashE0 | AesopClashE1 | AesopClashE2 | AesopClashE3 |
   AesopClashE4 | AesopClashE5 | AesopClashE6 | AesopClashE7 |
   AesopClashE8 | AesopClashE9 | AesopClashE10 | AesopClashE11 |
   AesopClashE12 | AesopClashE13 | AesopClashE14 | AesopClashE15`

val _ =
  check
    ("AESOP stops cold schematic clash retrieval at its candidate budget",
     fn () =>
       let
         fun stopped limit =
           let
             val claset = Option.valOf
               (clasetLib.claset_of_theory {thyname = "min"})
             val budget = searchBudget.create
               {candidates = SOME limit, applications = NONE,
                normalization = NONE}
             val x = ``x:aesop_clash_wide``
             val y = ``y:aesop_clash_wide``
           in
             (ignore (aesopRule.claset_rules_with (SOME budget)
                {claset = claset, mode = clasetUnify.Unify,
                 conclusion = ``p:bool``,
                 assumptions = [boolSyntax.mk_eq (x, y)],
                 qvars = HOLset.fromList Term.compare [x, y],
                 simpset = simpLib.empty_ss, simp_controls = []}); false)
             handle searchBudget.LimitReached
               (searchBudget.Candidate, usage) => #candidates usage = limit
           end
       in List.all stopped [0, 50] end)

val _ =
  check
    ("AESOP finds constructor witnesses through schematic clashes",
     fn () => List.all (fn target =>
       let
         val (residues, validation) =
           Tactical.VALID (aesopLib.AESOP_TAC []) ([], target)
       in
         null residues andalso Term.aconv (concl (validation [])) target
       end)
       [``?x:aesop_clash_wide. AesopClashW0 = x ==> p``,
        ``?x y:aesop_clash_wide. x = y ==> p``])

val _ =
  check
    ("AESOP refutes narrow and wide constructor clashes without hints",
     fn () => List.all (fn equality =>
       let
         val (residues, validation) = Tactical.VALID
           (aesopLib.AESOP_TAC []) ([equality], ``p:bool``)
       in
         null residues andalso Term.aconv (concl (validation [])) ``p:bool``
       end)
       [``AesopClashN0 = AesopClashN14``,
        ``AesopClashW0 = AesopClashW15 n``,
        ``AesopClashW15 n = AesopClashW0``,
        ``AesopClashE0 = AesopClashE15``])


val attribute_lhs = ``aesop_attribute_lhs:'a``
val attribute_rhs = ``aesop_attribute_rhs:'a``
val attribute_rule =
  ASSUME (boolSyntax.mk_eq (attribute_lhs, attribute_rhs))
val attribute_before =
  rewrite_rhs (aesopData.aesop_ss ()) attribute_lhs
val _ =
  ThmAttribute.local_attribute
    {attrname = "aesop_simp", name = "aesop_selftest_attribute",
     args = [], thm = attribute_rule}
val attribute_after =
  rewrite_rhs (aesopData.aesop_ss ()) attribute_lhs

val _ =
  check
    ("aesop_simp additions mark the derived simpset cache stale",
     fn () =>
       aconv attribute_before attribute_lhs andalso
       aconv attribute_after attribute_rhs)

val _ =
  check
    ("aesop simpset leaves conditional splitting to safe rules",
     fn () =>
       let
         val original =
           ``P (if aesop_split_b then aesop_split_x:'a
               else aesop_split_y) : bool``
         val goal = ([], original)
         val unsplit =
           residual
             (simpLib.SIMP_TAC (aesopData.aesop_ss ()) []) goal
         val split =
           residual
             (simpLib.SIMP_TAC
               (simpLib.++ (aesopData.aesop_ss (), simpLib.split_ss)) [])
             goal
       in
         case (unsplit, split) of
             ([([], unsplit_goal)], [([], split_goal)]) =>
               can (find_term boolSyntax.is_cond) unsplit_goal andalso
               not (can (find_term boolSyntax.is_cond) split_goal)
           | _ => false
       end)

fun rule_names rules =
  map (fn ({name, ...} : aesopRule.rule) => name) rules

fun is_phase expected ({phase, ...} : aesopRule.rule) =
  phase = expected

fun engine_step_succeeds rule goal =
  case #apply (rule : aesopRule.rule) of
      aesopRule.EngineStep step =>
        not (seq.null (step (clasetGoal.from_goal goal, 1)))
    | _ => false

val _ =
  check
    ("aesop closers are safe and ordered assumption before contradiction",
     fn () =>
       let
         val p = Term.mk_var ("aesop_closer_p", Type.bool)
         val q = Term.mk_var ("aesop_closer_q", Type.bool)
         val closers = aesopRule.closers ()
       in
         rule_names closers = ["assumption", "contradiction"] andalso
         List.all (is_phase aesopRule.RSafe) closers andalso
         engine_step_succeeds (hd closers) ([p], p) andalso
         engine_step_succeeds (hd (tl closers))
           ([boolSyntax.mk_neg p, p], q)
       end)

fun add_premise premise theorem =
  DISCH premise (Drule.ADD_ASSUM premise theorem)

(* A rule's free variables are its parameters, so a rule stated over
   variables matches any assumption whatever and two such rules differing
   only in a variable's name are the same rule.  Fixtures that need
   particular propositions -- distinct rules, or a premise with exactly
   one match -- state them closed. *)
val opaque_prop = Term.inst [Type.alpha |-> Type.bool] boolSyntax.arb
val opaque_wrapper =
  Term.inst [Type.alpha |-> (Type.bool --> Type.bool)] boolSyntax.arb
fun distinct_prop count =
  if count <= 0 then opaque_prop
  else Term.mk_comb (opaque_wrapper, distinct_prop (count - 1))

val assembly_p = distinct_prop 1
val assembly_q = distinct_prop 2
val assembly_r = distinct_prop 3
val assembly_s = distinct_prop 4

val assembly_cs =
  clasetLib.empty_cs
  |> clasetLib.add_rule
       {kind = clasetRules.Intro, safe = true, prio = NONE}
       ("safe0", boolTheory.TRUTH)
  |> clasetLib.add_rule
       {kind = clasetRules.Intro, safe = true, prio = NONE}
       ("safep", add_premise assembly_p boolTheory.TRUTH)
  |> clasetLib.add_rule
       {kind = clasetRules.Intro, safe = false, prio = NONE}
       ("unsafe_default", add_premise assembly_q boolTheory.TRUTH)
  |> clasetLib.add_rule
       {kind = clasetRules.Intro, safe = false, prio = SOME 80}
       ("unsafe_eighty",
        add_premise assembly_r
          (add_premise assembly_s boolTheory.TRUTH))

val assembled =
  aesopRule.claset_rules
    {claset = assembly_cs, mode = clasetUnify.Unify,
     conclusion = boolSyntax.T, assumptions = [],
     qvars = HOLset.empty Term.compare, simp_args = []}

val _ =
  check
    ("aesop claset assembly defaults unsafe rules to fifty percent",
     fn () =>
       case #unsafe assembled of
           [{name = "unsafe_eighty", phase = aesopRule.RUnsafe 80, ...},
            {name = "unsafe_default", phase = aesopRule.RUnsafe 50, ...}] =>
             true
         | _ => false)

(* A registered tactic rule competes with the claset candidates on its
   declared percentage: 95 outranks the eighty-percent declaration, and the
   tie at fifty leaves the claset candidate ahead. *)
val merged_unsafe_order =
  aesopRule.with_tactic_rules
    (fn () =>
      (aesopRule.register_tactic_rule
         {name = "tactic_ninety_five",
          phase = aesopRule.RUnsafe 95,
          tactic = NTactical.LIFT (Tactic.ACCEPT_TAC boolTheory.TRUTH),
          index = SOME (aesopRule.TargetPattern boolSyntax.T)};
       aesopRule.register_tactic_rule
         {name = "tactic_fifty",
          phase = aesopRule.RUnsafe 50,
          tactic = NTactical.LIFT (Tactic.ACCEPT_TAC boolTheory.TRUTH),
          index = SOME (aesopRule.TargetPattern boolSyntax.T)};
       #unsafe
         (aesopRule.claset_rules
           {claset = assembly_cs, mode = clasetUnify.Unify,
            conclusion = boolSyntax.T, assumptions = [],
            qvars = HOLset.empty Term.compare, simp_args = []})))
    ()

val _ =
  check
    ("aesop unsafe order merges tactic rules by declared percentage",
     fn () =>
       rule_names merged_unsafe_order =
         ["tactic_ninety_five", "unsafe_eighty", "unsafe_default",
          "tactic_fifty"])

val _ =
  check
    ("aesop safe-order scaffold locks closers safe0 and safep slots",
     fn () =>
       let
         val safe = #safe assembled
       in
         rule_names (aesopRule.safe_rules safe) =
           ["assumption", "contradiction", "safe0", "safep"] andalso
         null (#safe_forward safe) andalso
         null (#conclusion_splits safe) andalso
         null (#assumption_splits safe)
       end)

fun first_engine_record rule goal =
  case #apply (rule : aesopRule.rule) of
      aesopRule.EngineStep step =>
        (case seq.cases (step (clasetGoal.from_goal goal, 1)) of
             SOME ((record, _), _) => SOME record
           | NONE => NONE)
    | _ => NONE

val elim_p = Term.mk_var ("aesop_elim_p", Type.bool)
val elim_q = Term.mk_var ("aesop_elim_q", Type.bool)
val elim_theorem =
  DISCH elim_p (DISCH elim_q (ASSUME elim_q))
val dest_theorem =
  DISCH elim_p (ASSUME elim_p)
val elim_dest_cs =
  clasetLib.empty_cs
  |> clasetLib.add_rule
       {kind = clasetRules.Elim, safe = true, prio = NONE}
       ("safe_elim", elim_theorem)
  |> clasetLib.add_rule
       {kind = clasetRules.Dest, safe = false, prio = SOME 70}
       ("unsafe_dest", dest_theorem)
val elim_dest_rules =
  aesopRule.claset_rules
    {claset = elim_dest_cs, mode = clasetUnify.Unify,
     conclusion = elim_q, assumptions = [elim_p],
     qvars = HOLset.empty Term.compare, simp_args = []}

val _ =
  check
    ("aesop assembly uses plain elim and make-elim dest without variants",
     fn () =>
       let
         val safe =
           List.filter
             (fn ({name, ...} : aesopRule.rule) => name = "safe_elim")
             (aesopRule.safe_rules (#safe elim_dest_rules))
         val unsafe = #unsafe elim_dest_rules
       in
         case (safe, unsafe) of
             ([elim_rule],
              [dest_rule as
                 {name = "unsafe_dest",
                  phase = aesopRule.RUnsafe 70, ...}]) =>
               (case
                  (first_engine_record elim_rule ([elim_p], elim_q),
                   first_engine_record dest_rule ([elim_p], elim_q))
                of
                    (SOME elim_record, SOME dest_record) =>
                      clasetStep.consumed_of elim_record = SOME 1 andalso
                      clasetStep.consumed_of dest_record = SOME 1 andalso
                      (case clasetStep.kind_of elim_record of
                           clasetStep.RuleApplication
                             {variant = clasetStep.Plain, ...} => true
                         | _ => false) andalso
                      (case clasetStep.kind_of dest_record of
                           clasetStep.RuleApplication
                             {variant = clasetStep.Plain, ...} => true
                         | _ => false)
                  | _ => false)
           | _ => false
       end)

val _ =
  check
    ("aesop apply builder makes one engine step with its supplied phase",
     fn () =>
       let
         val rule =
           aesopRule.apply_rule
             {name = "apply_truth", phase = aesopRule.RUnsafe 65,
              theorem = boolTheory.TRUTH, mode = clasetUnify.Unify}
       in
         #name rule = "apply_truth" andalso
         is_phase (aesopRule.RUnsafe 65) rule andalso
         not (#once rule) andalso
         engine_step_succeeds rule ([], boolSyntax.T)
       end)

val _ =
  check
    ("aesop constructors builder is multi-step and unsafe by default",
     fn () =>
       let
         val unsafe =
           aesopRule.constructors_rule
             {name = "constructors", theorems = [boolTheory.TRUTH],
              percent = NONE, mode = clasetUnify.Unify}
         val safe =
           aesopRule.safe_constructors_rule
             {name = "safe_constructors",
              theorems = [boolTheory.TRUTH],
              mode = clasetUnify.Match}
         fun singleton_multi rule =
           case #apply (rule : aesopRule.rule) of
               aesopRule.MultiStep [_] => true
             | _ => false
       in
         is_phase (aesopRule.RUnsafe 50) unsafe andalso
         is_phase aesopRule.RSafe safe andalso
         singleton_multi unsafe andalso singleton_multi safe
       end)

val _ =
  check
    ("aesop simp builder is the built-in penalty-zero rendered rule",
     fn () =>
       let
         val rule =
           aesopRule.simp_rule [clasetLib.Simp boolTheory.TRUTH]
       in
         #name rule = "simp" andalso
         is_phase (aesopRule.RNorm 0) rule andalso
         (case #apply rule of
              aesopRule.RenderedTactic tactic =>
                not (seq.null
                  (tactic ([], boolSyntax.T) (Context.snapshot())))
            | _ => false)
       end)

fun first_engine_result rule goal =
  case #apply (rule : aesopRule.rule) of
      aesopRule.EngineStep step =>
        (case seq.cases (step (clasetGoal.from_goal goal, 1)) of
             SOME (result, _) => SOME result
           | NONE => NONE)
    | _ => NONE

fun rendered_succeeds rule goal =
  case #apply (rule : aesopRule.rule) of
      aesopRule.RenderedTactic tactic =>
        not (seq.null (tactic goal (Context.snapshot())))
    | _ => false

val forward_p = distinct_prop 5
val forward_q = distinct_prop 6
val forward_target = distinct_prop 7
val forward_conclusion =
  boolSyntax.mk_conj (forward_p, forward_q)
val forward_theorem =
  DISCH forward_p
    (DISCH forward_q
      (CONJ (ASSUME forward_p) (ASSUME forward_q)))
val conjunctive_forward_theorem =
  DISCH forward_conclusion
    (CONJUNCT1 (ASSUME forward_conclusion))
val reverse_forward_theorem =
  DISCH forward_p
    (DISCH forward_q
      (CONJ (ASSUME forward_q) (ASSUME forward_p)))

val _ =
  check
    ("aesop forward is all-immediate and retains matched assumptions",
     fn () =>
       let
         val rule =
           aesopRule.default_forward_rule
             {name = "forward", phase = aesopRule.RSafe,
              theorem = forward_theorem, mode = clasetUnify.Match}
       in
         case first_engine_result rule
           ([forward_p, forward_q], forward_target)
         of
             SOME (record, node) =>
               #once rule andalso
               clasetStep.consumed_of record = NONE andalso
               (case clasetGoal.render node 1 of
                    ([added, retained_p, retained_q], target) =>
                      aconv added forward_conclusion andalso
                      aconv retained_p forward_p andalso
                      aconv retained_q forward_q andalso
                      aconv target forward_target
                  | _ => false)
           | NONE => false
       end)

val _ =
  check
    ("aesop forward preserves a conjunctive first premise",
     fn () =>
       let
         val rule =
           aesopRule.default_forward_rule
             {name = "conjunctive-forward", phase = aesopRule.RSafe,
              theorem = conjunctive_forward_theorem,
              mode = clasetUnify.Match}
       in
         case first_engine_result rule
           ([forward_conclusion], forward_target)
         of
             SOME (_, node) =>
               (case clasetGoal.render node 1 of
                    ([added, retained], target) =>
                      aconv added forward_p andalso
                      aconv retained forward_conclusion andalso
                      aconv target forward_target
                  | _ => false)
           | NONE => false
       end)

val _ =
  check
    ("aesop forward keeps a non-immediate suffix in the new hypothesis",
     fn () =>
       let
         val rule =
           aesopRule.forward_rule
             {name = "partial_forward", phase = aesopRule.RUnsafe 60,
              theorem = forward_theorem, immediate = 1,
              mode = clasetUnify.Unify}
         val expected =
           boolSyntax.mk_imp (forward_q, forward_conclusion)
       in
         case first_engine_result rule
           ([forward_p, forward_q], forward_target)
         of
             SOME (record, node) =>
               clasetStep.consumed_of record = NONE andalso
               (case clasetGoal.render node 1 of
                    (added :: retained, target) =>
                      aconv added expected andalso
                      ListPair.allEq (fn (left, right) =>
                        aconv left right)
                        (retained, [forward_p, forward_q]) andalso
                      aconv target forward_target
                  | _ => false)
           | NONE => false
       end)

val _ =
  check
    ("aesop forward records a replayable non-consuming transition",
     fn () =>
       let
         val original = ([forward_p, forward_q], forward_target)
         val rule =
           aesopRule.default_forward_rule
             {name = "forward_replay", phase = aesopRule.RSafe,
              theorem = forward_theorem, mode = clasetUnify.Match}
       in
         case first_engine_result rule original of
             SOME (_, node) =>
               let
                 val grounded =
                   clasetReplay.ground (clasetGoal.store node)
                     (clasetGoal.replay node)
               in
                 case clasetReplay.replay_in (Context.snapshot ())
                        grounded original of
                     clasetReplay.Replayed
                       ([(added :: retained, target)], _) =>
                         aconv added forward_conclusion andalso
                         ListPair.allEq (fn (left, right) =>
                           aconv left right)
                           (retained, [forward_p, forward_q]) andalso
                         aconv target forward_target
                   | _ => false
               end
           | NONE => false
       end)

val _ =
  check
    ("aesop forward duplicate check instantiates before alpha comparison",
     fn () =>
       let
         val (meta, store0) =
           clasetMeta.new_meta
             {allow = [], ty = Type.bool} clasetMeta.empty
       in
         case clasetMeta.bind (meta, forward_p) store0 of
             SOME store =>
               aesopRule.forward_duplicate store [meta] forward_p
           | NONE => false
       end)

val forward_cs =
  clasetLib.empty_cs
  |> clasetLib.add_rule
       {kind = clasetRules.Forward, safe = true, prio = NONE}
       ("safe_forward", forward_theorem)
  |> clasetLib.add_rule
       {kind = clasetRules.Forward, safe = false, prio = SOME 77}
       ("unsafe_forward", reverse_forward_theorem)

val forward_assembled =
  aesopRule.claset_rules
    {claset = forward_cs, mode = clasetUnify.Match,
     conclusion = forward_target, assumptions = [forward_q],
     qvars = HOLset.empty Term.compare, simp_args = []}

val _ =
  check
    ("aesop claset assembly puts forward declarations in their phases",
     fn () =>
       let val safe = #safe forward_assembled
       in
         rule_names (#safe_forward safe) = ["safe_forward"] andalso
         (case #unsafe forward_assembled of
              [{name = "unsafe_forward",
                phase = aesopRule.RUnsafe 77, once = true, ...}] => true
            | _ => false)
       end)

val cases_theorem =
  DISCH boolSyntax.T
    (DISCH forward_q (ASSUME forward_q))

val _ =
  check
    ("aesop cases consumes its major assumption and honours patterns",
     fn () =>
       let
         val allowed =
           aesopRule.cases_rule
             {name = "cases", phase = aesopRule.RUnsafe 50,
              theorem = cases_theorem, patterns = [boolSyntax.T],
              mode = clasetUnify.Match}
         val blocked =
           aesopRule.cases_rule
             {name = "blocked_cases", phase = aesopRule.RUnsafe 50,
              theorem = cases_theorem, patterns = [boolSyntax.F],
              mode = clasetUnify.Match}
       in
         (case first_engine_record allowed ([boolSyntax.T], forward_q) of
              SOME record =>
                clasetStep.consumed_of record = SOME 1
            | NONE => false) andalso
         not (engine_step_succeeds blocked
           ([boolSyntax.T], forward_q))
       end)

val _ =
  check
    ("aesop TypeBase cases builder constructs a changing rendered rule",
     fn () =>
       let
         val variable =
           Term.mk_var ("aesop_cases_bool", Type.bool)
         val target = boolSyntax.mk_eq (variable, boolSyntax.T)
       in
         rendered_succeeds
           (aesopRule.cases_rule_for Type.bool) ([], target)
       end)

val _ =
  check
    ("aesop tactic builder rejects no-op results and applies indexes",
     fn () =>
       let
         val no_op =
           aesopRule.tactic_rule
             {name = "no_op", phase = aesopRule.RSafe,
              tactic = NTactical.NALL_TAC, index = NONE}
         val target_rule =
           aesopRule.tactic_rule
             {name = "target", phase = aesopRule.RSafe,
              tactic = NTactical.LIFT (Tactic.ACCEPT_TAC boolTheory.TRUTH),
              index =
                SOME (aesopRule.TargetPattern boolSyntax.T)}
         val hyp_rule =
           aesopRule.tactic_rule
             {name = "hyp", phase = aesopRule.RSafe,
              tactic = NTactical.LIFT Tactic.DISCH_TAC,
              index = SOME (aesopRule.HypPattern boolSyntax.T)}
       in
         not (rendered_succeeds no_op ([], boolSyntax.T)) andalso
         rendered_succeeds target_rule ([], boolSyntax.T) andalso
         not (rendered_succeeds target_rule ([], boolSyntax.F)) andalso
         rendered_succeeds hyp_rule
           ([boolSyntax.T],
            boolSyntax.mk_imp (forward_p, forward_p)) andalso
         not (rendered_succeeds hyp_rule
           ([], boolSyntax.mk_imp (forward_p, forward_p)))
       end)

val registered_before =
  length (aesopRule.registered_tactic_rules ())

(* Registration is session-global, so a test registers inside the scoping
   combinator and leaves the registry as it found it. *)
fun with_registered_target f =
  aesopRule.with_tactic_rules
    (fn () =>
      (aesopRule.register_tactic_rule
         {name = "registered_target", phase = aesopRule.RUnsafe 42,
          tactic = NTactical.LIFT (Tactic.ACCEPT_TAC boolTheory.TRUTH),
          index = SOME (aesopRule.TargetPattern boolSyntax.T)};
       f ()))
    ()

fun registered_rules_for conclusion =
  aesopRule.claset_rules
    {claset = clasetLib.empty_cs, mode = clasetUnify.Match,
     conclusion = conclusion, assumptions = [],
     qvars = HOLset.empty Term.compare, simp_args = []}

val (registered_during, registered_matching, registered_blocked) =
  with_registered_target
    (fn () =>
      (length (aesopRule.registered_tactic_rules ()),
       registered_rules_for boolSyntax.T,
       registered_rules_for boolSyntax.F))
val registered_after =
  length (aesopRule.registered_tactic_rules ())

val _ =
  check
    ("aesop tactic registry retains rules and applies its index",
     fn () =>
       registered_during = registered_before + 1 andalso
       List.exists
         (fn ({name, ...} : aesopRule.rule) =>
           name = "registered_target")
         (#unsafe registered_matching) andalso
       not
         (List.exists
           (fn ({name, ...} : aesopRule.rule) =>
             name = "registered_target")
           (#unsafe registered_blocked)))

val _ =
  check
    ("aesop scoped registration unwinds on return and on exception",
     fn () =>
       let
         exception ScopedRegistration
       in
         registered_after = registered_before andalso
         (with_registered_target (fn () => raise ScopedRegistration)
            handle ScopedRegistration =>
              length (aesopRule.registered_tactic_rules ()) =
                registered_before)
       end)

val split_theorem = TypeBase.case_pred_disj_of Type.bool
val split_pair =
  aesopRule.split_rule_pair
    {name = "bool_case_split", theorem = split_theorem}
val assumption_split_pair =
  aesopRule.split_rule_pair
    {name = "bool_assumption_split",
     theorem = splitLib.mk_asm_split split_theorem}
val split_goal : Term.term list * Term.term =
  ([],
   ``aesop_split_pred
       (if aesop_split_test then aesop_split_left:'a
        else aesop_split_right) : bool``)
val split_assumption_goal =
  (#2 split_goal :: [], forward_target)

val _ =
  check
    ("aesop split builders change conclusions and assumptions",
     fn () =>
       rendered_succeeds (#conclusion split_pair) split_goal andalso
       rendered_succeeds (#assumption split_pair)
         split_assumption_goal andalso
       rendered_succeeds (#conclusion assumption_split_pair)
         split_goal andalso
       rendered_succeeds (#assumption assumption_split_pair)
         split_assumption_goal)

val _ =
  check
    ("aesop split builders occupy conclusion before assumption slots",
     fn () =>
       let
         val safe =
           {closers = [], safe0_claset = [], safe_forward = [],
            safep_claset = [],
            conclusion_splits = [#conclusion split_pair],
            assumption_splits = [#assumption split_pair]}
       in
         rule_names (aesopRule.safe_rules safe) =
           ["bool_case_split (conclusion split)",
            "bool_case_split (assumption split)"] andalso
         List.all (is_phase aesopRule.RSafe)
           (aesopRule.safe_rules safe)
       end)

fun tree_cgoal params assumptions target : clasetGoal.cgoal =
  {params = params, asl = assumptions, w = target}

fun tree_node store level goals =
  clasetGoal.create {goals = goals, store = store, level = level}

fun new_tree store cgoal unsafe =
  aesopTree.create
    {node = tree_node store 0 [cgoal], unsafe_cursor = unsafe}

fun pop_expected tree =
  case aesopTree.pop_goal tree of
      (SOME id, rest) => (id, rest)
    | _ => raise Fail "expected a queued aesop tree goal"

fun install_tree_rapp tree parent phase name store children records =
  aesopTree.install_rapp parent
    {rule = name, phase = phase, records = records,
     forwarded = NONE,
     node =
       tree_node store
         (#level (aesopTree.goal tree parent) + 1) children}
    tree

fun close_tree_goal tree id =
  #tree
    (install_tree_rapp tree id aesopRule.RSafe "close"
      (aesopTree.active_store (aesopTree.goal tree id)) [] [])

fun norm_complete outcome =
  case outcome of
      aesopNorm.Complete result => SOME result
    | aesopNorm.IterationLimit _ => NONE

fun norm_target tree id =
  #w (aesopTree.active_cgoal (aesopTree.goal tree id))

fun norm_records tree id =
  case #norm (aesopTree.goal tree id) of
      aesopTree.Normalised {records, ...} => records
    | aesopTree.NormProved {records, ...} => records
    | aesopTree.Unnormalised => []

fun record_is_disch record =
  case clasetStep.kind_of record of clasetStep.Disch => true | _ => false

fun record_is_gen record =
  case clasetStep.kind_of record of clasetStep.Gen => true | _ => false

fun record_is_hyp_subst record =
  case clasetStep.kind_of record of
      clasetStep.HypSubst => true
    | _ => false

fun record_is_wrapper record =
  case clasetStep.kind_of record of
      clasetStep.Wrapper => true
    | _ => false

fun norm_transition name penalty equality =
  let
    val (_, target) = boolSyntax.dest_eq (concl equality)
    val theorem =
      DISCH target (EQ_MP (SYM equality) (ASSUME target))
  in
    aesopRule.apply_rule
      {name = name, phase = aesopRule.RNorm penalty,
       theorem = theorem, mode = clasetUnify.Match}
  end

val norm_state1 =
  Term.mk_var ("aesop_norm_state1", Type.bool)
val norm_state2 =
  Term.mk_var ("aesop_norm_state2", Type.bool)
val norm_state3 =
  Term.mk_var ("aesop_norm_state3", Type.bool)
val norm_state4 =
  Term.mk_var ("aesop_norm_state4", Type.bool)
val norm_state_alt =
  Term.mk_var ("aesop_norm_state_alt", Type.bool)

val norm_4_to_3 =
  ASSUME (boolSyntax.mk_eq (norm_state4, norm_state3))
val norm_3_to_2 =
  ASSUME (boolSyntax.mk_eq (norm_state3, norm_state2))
val norm_3_to_alt =
  ASSUME (boolSyntax.mk_eq (norm_state3, norm_state_alt))
val norm_2_to_3 =
  SYM norm_3_to_2

val norm_restart_rules =
  [norm_transition "competing" 10 norm_3_to_alt,
   norm_transition "unlock" 5 norm_4_to_3,
   norm_transition "low" ~10 norm_3_to_2]
val norm_restart_tree0 =
  new_tree clasetMeta.empty
    (tree_cgoal []
      (map concl [norm_4_to_3, norm_3_to_2, norm_3_to_alt])
      norm_state4) []
val norm_restart_root =
  aesopTree.root norm_restart_tree0
val norm_restart_outcome =
  aesopNorm.normalise_in (Context.snapshot ()) NONE
    {max_depth = 10, rules = norm_restart_rules}
    norm_restart_root norm_restart_tree0

val _ =
  check
    ("aesop norm orders penalties and restarts after every success",
     fn () =>
       case norm_complete norm_restart_outcome of
           SOME {tree, iterations} =>
             iterations = 2 andalso
             aconv (norm_target tree norm_restart_root) norm_state2
         | NONE => false)

val custom_norm_simp =
  aesopRule.simp_rule_with
    {name = "simp",
     simpset =
       simpLib.++ (simpLib.empty_ss, simpLib.rewrites [norm_3_to_2]),
     controls = []}
val negative_norm =
  norm_transition "negative" ~1 norm_4_to_3
val norm_simp_tree0 =
  new_tree clasetMeta.empty
    (tree_cgoal []
      (map concl [norm_4_to_3, norm_3_to_2])
      norm_state4) []
val norm_simp_root =
  aesopTree.root norm_simp_tree0
val norm_simp_outcome =
  aesopNorm.normalise_in (Context.snapshot ()) NONE
    {max_depth = 10,
     rules = [custom_norm_simp, negative_norm]}
    norm_simp_root norm_simp_tree0

val _ =
  check
    ("aesop norm runs a negative user rule before penalty-zero simp",
     fn () =>
       case norm_complete norm_simp_outcome of
           SOME {tree, iterations} =>
             iterations = 2 andalso
             aconv (norm_target tree norm_simp_root) norm_state2 andalso
             (case norm_records tree norm_simp_root of
                  [first, second] =>
                    (case clasetStep.kind_of first of
                         clasetStep.RuleApplication _ => true
                       | _ => false) andalso
                    record_is_wrapper second
                | _ => false)
         | NONE => false)

val _ =
  check
    ("aesop norm built-ins have their documented penalty-zero order",
     fn () =>
       rule_names (aesopRule.norm_builtins []) =
         ["disch", "gen", "hyp-subst", "simp"] andalso
       List.all (is_phase (aesopRule.RNorm 0))
         (aesopRule.norm_builtins []))

val norm_declaration_cs =
  clasetLib.empty_cs
  |> clasetLib.add_rule
       {kind = clasetRules.Norm, safe = false, prio = SOME ~7}
       ("declared_norm",
        DISCH norm_state3
          (EQ_MP (SYM norm_4_to_3) (ASSUME norm_state3)))
val norm_declaration_rules =
  aesopRule.claset_rules
    {claset = norm_declaration_cs, mode = clasetUnify.Unify,
     conclusion = norm_state4, assumptions = [concl norm_4_to_3],
     qvars = HOLset.empty Term.compare, simp_args = []}

val _ =
  check
    ("aesop norm declarations are Match-mode apply rules with penalties",
     fn () =>
       case
         List.filter
           (fn ({name, ...} : aesopRule.rule) =>
             name = "declared_norm")
           (#norm norm_declaration_rules)
       of
           [rule as {phase = aesopRule.RNorm ~7, ...}] =>
             (case first_engine_result rule
                ([concl norm_4_to_3], norm_state4)
              of
                  SOME (_, node) =>
                    (case clasetGoal.goals node of
                         [{w, ...}] => aconv w norm_state3
                       | _ => false)
                | NONE => false)
         | _ => false)

val norm_builtin_p =
  Term.mk_var ("aesop_norm_builtin_p", Type.bool)
val norm_builtin_x =
  Term.mk_var ("aesop_norm_builtin_x", Type.bool)
val norm_builtin_goal =
  boolSyntax.mk_imp
    (norm_builtin_p,
     boolSyntax.mk_forall (norm_builtin_x, norm_builtin_p))
val norm_builtin_tree0 =
  new_tree clasetMeta.empty
    (tree_cgoal [] [] norm_builtin_goal) []
val norm_builtin_root =
  aesopTree.root norm_builtin_tree0
val norm_builtin_outcome =
  aesopNorm.normalise_in (Context.snapshot ()) NONE
    {max_depth = 10, rules = aesopRule.norm_builtins []}
    norm_builtin_root norm_builtin_tree0

val _ =
  check
    ("aesop norm introduces assumptions and universals before simp",
     fn () =>
       case norm_complete norm_builtin_outcome of
           SOME {tree, iterations} =>
             iterations = 3 andalso
             #state (aesopTree.goal tree norm_builtin_root) =
               aesopTree.Proved andalso
             (case norm_records tree norm_builtin_root of
                  [disch, gen, simp] =>
                    record_is_disch disch andalso
                    record_is_gen gen andalso
                    record_is_wrapper simp
                | _ => false)
         | NONE => false)

val norm_subst_variable =
  Term.mk_var ("aesop_norm_subst_variable", Type.bool)
val norm_subst_equality =
  boolSyntax.mk_eq (norm_subst_variable, boolSyntax.T)
val norm_subst_tree0 =
  new_tree clasetMeta.empty
    (tree_cgoal [] [norm_subst_equality] norm_subst_variable) []
val norm_subst_root =
  aesopTree.root norm_subst_tree0
val norm_subst_outcome =
  aesopNorm.normalise_in (Context.snapshot ()) NONE
    {max_depth = 10, rules = aesopRule.norm_builtins []}
    norm_subst_root norm_subst_tree0

val _ =
  check
    ("aesop norm hypothesis substitution eliminates variables",
     fn () =>
       case norm_complete norm_subst_outcome of
           SOME {tree, ...} =>
             #state (aesopTree.goal tree norm_subst_root) =
               aesopTree.Proved andalso
             (case norm_records tree norm_subst_root of
                  first :: _ =>
                    record_is_hyp_subst first
                | [] => false)
         | NONE => false)

val norm_function =
  Term.mk_var
    ("aesop_norm_function", Type.bool --> Type.bool)
val norm_argument =
  Term.mk_var ("aesop_norm_argument", Type.bool)
val norm_application =
  Term.mk_comb (norm_function, norm_argument)
val norm_rewrite_assumption =
  boolSyntax.mk_eq (norm_application, boolSyntax.T)

fun run_simp_controls controls =
  let
    val tree0 =
      new_tree clasetMeta.empty
        (tree_cgoal [] [norm_rewrite_assumption]
          norm_application) []
    val root = aesopTree.root tree0
  in
    (root,
     aesopNorm.normalise_in (Context.snapshot ()) NONE
       {max_depth = 10,
        rules = [aesopRule.simp_rule controls]} root tree0)
  end

val (norm_asms_root, norm_asms_outcome) =
  run_simp_controls []
val (norm_no_asms_root, norm_no_asms_outcome) =
  run_simp_controls [markerLib.NoAsms]

val _ =
  check
    ("aesop norm simp uses assumptions unless NoAsms disables them",
     fn () =>
       case
         (norm_complete norm_asms_outcome,
          norm_complete norm_no_asms_outcome)
       of
           (SOME {tree = with_asms, ...},
            SOME {tree = without_asms, iterations = 0}) =>
             #state (aesopTree.goal with_asms norm_asms_root) =
               aesopTree.Proved andalso
             aconv
               (norm_target without_asms norm_no_asms_root)
               norm_application
         | _ => false)

val branching_norm_theorem =
  add_premise norm_state2
    (add_premise norm_state1 (ASSUME norm_state4))
val branching_norm_rule =
  aesopRule.apply_rule
    {name = "branching", phase = aesopRule.RNorm 0,
     theorem = branching_norm_theorem, mode = clasetUnify.Match}
val branching_norm_tree0 =
  new_tree clasetMeta.empty
    (tree_cgoal [] [norm_state4] norm_state4) []
val branching_norm_root =
  aesopTree.root branching_norm_tree0
val branching_norm_outcome =
  aesopNorm.normalise_in (Context.snapshot ()) NONE
    {max_depth = 10, rules = [branching_norm_rule]}
    branching_norm_root branching_norm_tree0

val _ =
  check
    ("aesop norm dynamically rejects applications with two subgoals",
     fn () =>
       case norm_complete branching_norm_outcome of
           SOME {tree, iterations = 0} =>
             aconv (norm_target tree branching_norm_root) norm_state4 andalso
             null (norm_records tree branching_norm_root)
         | _ => false)

fun duplicated_disch input =
  case seq.cases (clasetStep.blast_disch_step_in (Context.snapshot ())
                    input) of
      NONE => seq.empty
    | SOME (result, _) => seq.fromList [result, result]

val alternative_norm_rule : aesopRule.rule =
  {name = "alternatives", phase = aesopRule.RNorm 0,
   apply = aesopRule.EngineStep duplicated_disch, once = false}
val alternative_norm_tree0 =
  new_tree clasetMeta.empty
    (tree_cgoal [] []
      (boolSyntax.mk_imp (norm_builtin_p, norm_builtin_p))) []
val alternative_norm_root =
  aesopTree.root alternative_norm_tree0
val alternative_norm_outcome =
  aesopNorm.normalise_in (Context.snapshot ()) NONE
    {max_depth = 10, rules = [alternative_norm_rule]}
    alternative_norm_root alternative_norm_tree0

val _ =
  check
    ("aesop norm dynamically rejects multiple application alternatives",
     fn () =>
       case norm_complete alternative_norm_outcome of
           SOME {tree, iterations = 0} =>
             aconv
               (norm_target tree alternative_norm_root)
               (boolSyntax.mk_imp
                 (norm_builtin_p, norm_builtin_p))
         | _ => false)

val (norm_meta, norm_meta_store) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} clasetMeta.empty
val binding_norm_rule =
  aesopRule.apply_rule
    {name = "bind-meta", phase = aesopRule.RNorm 0,
     theorem = boolTheory.TRUTH, mode = clasetUnify.Unify}
val binding_norm_tree0 =
  new_tree norm_meta_store
    (tree_cgoal [] [] norm_meta) []
val binding_norm_root =
  aesopTree.root binding_norm_tree0
val binding_norm_outcome =
  aesopNorm.normalise_in (Context.snapshot ()) NONE
    {max_depth = 10, rules = [binding_norm_rule]}
    binding_norm_root binding_norm_tree0

val _ =
  check
    ("aesop norm dynamically rejects metavariable-binding applications",
     fn () =>
       case norm_complete binding_norm_outcome of
           SOME {tree, iterations = 0} =>
             aconv (norm_target tree binding_norm_root) norm_meta andalso
             null
               (#terms
                 (clasetMeta.bindings
                   (aesopTree.active_store
                     (aesopTree.goal tree binding_norm_root))))
         | _ => false)

val looping_norm_rules =
  [norm_transition "forth" 0 norm_2_to_3,
   norm_transition "back" 0 norm_3_to_2]
val looping_norm_tree0 =
  new_tree clasetMeta.empty
    (tree_cgoal []
      (map concl [norm_2_to_3, norm_3_to_2])
      norm_state2) []
val looping_norm_root =
  aesopTree.root looping_norm_tree0
val looping_norm_outcome =
  aesopNorm.normalise_in (Context.snapshot ()) NONE
    {max_depth = 3, rules = looping_norm_rules}
    looping_norm_root looping_norm_tree0

val _ =
  check
    ("aesop norm iteration bound is clean and installs no partial chain",
     fn () =>
       case looping_norm_outcome of
           aesopNorm.IterationLimit
             {tree, iterations = 3, rule = "back"} =>
               not
                 (aesopTree.is_normalised
                   (aesopTree.goal tree looping_norm_root)) andalso
               aconv
                 (#w (#cgoal
                   (aesopTree.goal tree looping_norm_root)))
                 norm_state2
         | _ => false)

fun near expected actual =
  Real.abs (expected - actual) < 0.000000001

val _ =
  check
    ("aesop tree priorities multiply in the log domain",
     fn () =>
       let
         val first =
           aesopTree.extend_priority 0.0 (aesopRule.RUnsafe 50)
         val second =
           aesopTree.extend_priority first (aesopRule.RUnsafe 20)
       in
         near (Math.ln 0.1) second andalso
         near second
           (aesopTree.extend_priority second aesopRule.RSafe)
       end)

val fifo_goal =
  tree_cgoal [] [] boolSyntax.T
val fifo_tree0 =
  new_tree clasetMeta.empty fifo_goal []
val (fifo_root, fifo_tree1) =
  pop_expected fifo_tree0
val fifo_install =
  install_tree_rapp fifo_tree1 fifo_root
    (aesopRule.RUnsafe 50) "fifo" clasetMeta.empty
    [fifo_goal, fifo_goal] []
val (fifo_first, fifo_tree2) =
  pop_expected (#tree fifo_install)
val (fifo_second, _) =
  pop_expected fifo_tree2

val _ =
  check
    ("aesop tree queue uses FIFO order for equal priorities",
     fn () =>
       #goals fifo_install = [fifo_first, fifo_second] andalso
       near
         (#prio (aesopTree.goal (#tree fifo_install) fifo_first))
         (Math.ln 0.5))

val priority_tree0 =
  new_tree clasetMeta.empty fifo_goal []
val (priority_root, priority_tree1) =
  pop_expected priority_tree0
val priority_low =
  install_tree_rapp priority_tree1 priority_root
    (aesopRule.RUnsafe 20) "low_priority" clasetMeta.empty
    [fifo_goal] []
val priority_high =
  install_tree_rapp (#tree priority_low) priority_root
    (aesopRule.RUnsafe 80) "high_priority" clasetMeta.empty
    [fifo_goal] []
val (priority_first, _) =
  pop_expected (#tree priority_high)

val _ =
  check
    ("aesop tree queue pops higher log priorities first",
     fn () => #goals priority_high = [priority_first])

val proved_tree0 =
  new_tree clasetMeta.empty fifo_goal []
val (proved_root, proved_tree1) =
  pop_expected proved_tree0
val proved_install =
  install_tree_rapp proved_tree1 proved_root aesopRule.RSafe
    "two_children" clasetMeta.empty [fifo_goal, fifo_goal] []
val [proved_left, proved_right] = #goals proved_install
val proved_tree2 =
  close_tree_goal (#tree proved_install) proved_left
val proved_rapp =
  #rapp proved_install

val _ =
  check
    ("aesop tree proved states wait for every independent cluster",
     fn () =>
       #state (aesopTree.goal proved_tree2 proved_left) =
         aesopTree.Proved andalso
       #state (aesopTree.rapp proved_tree2 proved_rapp) =
         aesopTree.Unknown andalso
       #state (aesopTree.goal proved_tree2 proved_root) =
         aesopTree.Unknown)

val proved_tree3 =
  close_tree_goal proved_tree2 proved_right

val _ =
  check
    ("aesop tree proved states cascade from clusters to the root",
     fn () =>
       #state (aesopTree.rapp proved_tree3 proved_rapp) =
         aesopTree.Proved andalso
       #state (aesopTree.goal proved_tree3 proved_root) =
         aesopTree.Proved)

val stuck_tree0 =
  new_tree clasetMeta.empty fifo_goal []
val (stuck_root, stuck_tree1) =
  pop_expected stuck_tree0
val stuck_install =
  install_tree_rapp stuck_tree1 stuck_root aesopRule.RSafe
    "stuck_children" clasetMeta.empty [fifo_goal, fifo_goal] []
val [stuck_left, stuck_right] = #goals stuck_install
val stuck_tree2 =
  aesopTree.exhaust_goal stuck_left (#tree stuck_install)
val stuck_rapp =
  #rapp stuck_install

val _ =
  check
    ("aesop tree rapps stick when any child cluster sticks",
     fn () =>
       #state (aesopTree.goal stuck_tree2 stuck_left) =
         aesopTree.Stuck andalso
       #state (aesopTree.rapp stuck_tree2 stuck_rapp) =
         aesopTree.Stuck andalso
       #state (aesopTree.goal stuck_tree2 stuck_root) =
         aesopTree.Unknown)

val stuck_tree3 =
  aesopTree.exhaust_goal stuck_root stuck_tree2

val _ =
  check
    ("aesop tree stuck states cascade and make descendants irrelevant",
     fn () =>
       #state (aesopTree.goal stuck_tree3 stuck_root) =
         aesopTree.Stuck andalso
       #state (aesopTree.goal stuck_tree3 stuck_right) =
         aesopTree.Unknown andalso
       aesopTree.goal_irrelevant stuck_tree3 stuck_right)

val unfinished_rule =
  hd (aesopRule.closers ())
val completion_tree0 =
  new_tree clasetMeta.empty fifo_goal [unfinished_rule]
val completion_root =
  aesopTree.root completion_tree0
val completion_tree1 =
  completion_tree0
  |> aesopTree.set_normalised completion_root
       {records = [], cgoal = fifo_goal, store = clasetMeta.empty}
  |> aesopTree.set_safe_done completion_root true

val _ =
  check
    ("aesop goals stick only after every search phase is exhausted",
     fn () =>
       #state (aesopTree.goal completion_tree1 completion_root) =
         aesopTree.Unknown andalso
       #state
         (aesopTree.goal
           (aesopTree.set_unsafe_cursor completion_root []
             completion_tree1)
           completion_root) =
         aesopTree.Stuck)

val (cluster_m1, cluster_store1) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} clasetMeta.empty
val (cluster_m2, cluster_store2) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} cluster_store1
val (cluster_m3, cluster_store3) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} cluster_store2
val cluster_g1 =
  tree_cgoal [] [] cluster_m1
val cluster_g2 =
  tree_cgoal [] []
    (boolSyntax.mk_conj (cluster_m1, cluster_m2))
val cluster_g3 =
  tree_cgoal [] [] cluster_m2
val cluster_g4 =
  tree_cgoal [] [] cluster_m3
val cluster_tree0 =
  new_tree cluster_store3 fifo_goal []
val (cluster_root, cluster_tree1) =
  pop_expected cluster_tree0
val cluster_install =
  install_tree_rapp cluster_tree1 cluster_root aesopRule.RSafe
    "clusters" cluster_store3
    [cluster_g1, cluster_g2, cluster_g3, cluster_g4] []
val [cluster_id1, cluster_id2] =
  #clusters (aesopTree.rapp (#tree cluster_install)
    (#rapp cluster_install))

val _ =
  check
    ("aesop tree clusters close transitive metavariable overlap",
     fn () =>
       #goals (aesopTree.cluster (#tree cluster_install) cluster_id1) =
         List.take (#goals cluster_install, 3) andalso
       #goals (aesopTree.cluster (#tree cluster_install) cluster_id2) =
         [List.nth (#goals cluster_install, 3)])

val coupled_goal =
  tree_cgoal [] [] cluster_m1

(* Irrelevance has to be readable off every kind of node, so the tree
   below takes it from a settled ancestor: the root offers two
   alternative rule applications, one of them is closed, and everything
   under the other stays open while no longer being worth expanding.  A
   coupled cluster cannot stand in here -- its goals are conjunctive, so
   closing one member settles nothing above it. *)
val irrelevant_tree0 =
  new_tree clasetMeta.empty fifo_goal []
val (irrelevant_root, irrelevant_tree1) =
  pop_expected irrelevant_tree0
val irrelevant_open_install =
  install_tree_rapp irrelevant_tree1 irrelevant_root aesopRule.RSafe
    "open_alternative" clasetMeta.empty [fifo_goal] []
val [irrelevant_open] = #goals irrelevant_open_install
val irrelevant_deep_install =
  install_tree_rapp (#tree irrelevant_open_install) irrelevant_open
    aesopRule.RSafe "open_continuation" clasetMeta.empty [fifo_goal] []
val [irrelevant_deep] = #goals irrelevant_deep_install
val irrelevant_deep_rapp = #rapp irrelevant_deep_install
val irrelevant_deep_cluster =
  #cluster
    (aesopTree.goal (#tree irrelevant_deep_install) irrelevant_deep)
val irrelevant_closed_install =
  install_tree_rapp (#tree irrelevant_deep_install) irrelevant_root
    aesopRule.RSafe "closing_alternative" clasetMeta.empty [fifo_goal] []
val [irrelevant_closed] = #goals irrelevant_closed_install
val irrelevant_tree2 =
  close_tree_goal (#tree irrelevant_closed_install) irrelevant_closed
val irrelevant_pop =
  aesopTree.pop_goal irrelevant_tree2

val _ =
  check
    ("aesop proof lazily removes every kind of irrelevant queued node",
     fn () =>
       #state (aesopTree.goal irrelevant_tree2 irrelevant_root) =
         aesopTree.Proved andalso
       #state (aesopTree.goal irrelevant_tree2 irrelevant_deep) =
         aesopTree.Unknown andalso
       aesopTree.goal_irrelevant irrelevant_tree2 irrelevant_deep andalso
       aesopTree.rapp_irrelevant irrelevant_tree2
         irrelevant_deep_rapp andalso
       aesopTree.cluster_irrelevant irrelevant_tree2
         irrelevant_deep_cluster andalso
       #1 irrelevant_pop = NONE)

(* The goals of one cluster are conjunctive, and a member proved without
   assigning the metavariable they share discharges only itself: it
   installs no application that could copy its siblings, and a norm-proved
   member has no application at all.  Reading such a cluster as proved is
   what used to send [extract] into "winning forest has no proof of goal
   N" on Pelletier 30. *)
val norm_coupled_tree0 =
  new_tree cluster_store1 fifo_goal []
val (norm_coupled_root, norm_coupled_tree1) =
  pop_expected norm_coupled_tree0
val norm_coupled_install =
  install_tree_rapp norm_coupled_tree1 norm_coupled_root
    aesopRule.RSafe "norm_coupled" cluster_store1
    [coupled_goal, coupled_goal] []
val [norm_coupled_left, norm_coupled_right] =
  #goals norm_coupled_install
val norm_coupled_rapp = #rapp norm_coupled_install
val norm_coupled_cluster =
  #cluster
    (aesopTree.goal (#tree norm_coupled_install) norm_coupled_left)
val norm_coupled_tree2 =
  aesopTree.set_norm_proved norm_coupled_left
    {records = [], store = cluster_store1}
    (#tree norm_coupled_install)

val _ =
  check
    ("aesop coupled clusters ignore a member that assigns nothing",
     fn () =>
       #state (aesopTree.goal norm_coupled_tree2 norm_coupled_left) =
         aesopTree.Proved andalso
       #state (aesopTree.goal norm_coupled_tree2 norm_coupled_right) =
         aesopTree.Unknown andalso
       #state
         (aesopTree.cluster norm_coupled_tree2 norm_coupled_cluster) =
         aesopTree.Unknown andalso
       #state (aesopTree.rapp norm_coupled_tree2 norm_coupled_rapp) =
         aesopTree.Unknown andalso
       #state (aesopTree.goal norm_coupled_tree2 norm_coupled_root) =
         aesopTree.Unknown)

(* The same cluster driven the way the coupling intends: the application
   that closes the left member binds the shared metavariable, so
   [install_rapp] copies the right member into that branch, and proving
   the copy is what proves the original. *)
val bound_coupled_store =
  valOf (clasetMeta.bind (cluster_m1, boolSyntax.T) cluster_store1)
val bound_coupled_tree0 =
  new_tree cluster_store1 fifo_goal []
val (bound_coupled_root, bound_coupled_tree1) =
  pop_expected bound_coupled_tree0
val bound_coupled_install =
  install_tree_rapp bound_coupled_tree1 bound_coupled_root
    aesopRule.RSafe "bound_coupled" cluster_store1
    [coupled_goal, coupled_goal] []
val [bound_coupled_left, bound_coupled_right] =
  #goals bound_coupled_install
val bound_coupled_cluster =
  #cluster
    (aesopTree.goal (#tree bound_coupled_install) bound_coupled_left)
val bound_coupled_closer =
  install_tree_rapp (#tree bound_coupled_install) bound_coupled_left
    aesopRule.RSafe "bind_and_close" bound_coupled_store [] []
val [bound_coupled_copy] = #goals bound_coupled_closer
val bound_coupled_tree2 = #tree bound_coupled_closer
val bound_coupled_tree3 =
  close_tree_goal bound_coupled_tree2 bound_coupled_copy

val _ =
  check
    ("aesop coupled clusters close through the copy of every sibling",
     fn () =>
       #copy_of
         (aesopTree.goal bound_coupled_tree2 bound_coupled_copy) =
         SOME bound_coupled_right andalso
       #state (aesopTree.goal bound_coupled_tree2 bound_coupled_right) =
         aesopTree.Unknown andalso
       #state (aesopTree.goal bound_coupled_tree3 bound_coupled_right) =
         aesopTree.Proved andalso
       #state
         (aesopTree.cluster bound_coupled_tree3 bound_coupled_cluster) =
         aesopTree.Proved andalso
       #state (aesopTree.goal bound_coupled_tree3 bound_coupled_root) =
         aesopTree.Proved)

(* A proved copy below a partially open application is not yet connected to
   the application that emitted its original.  An unrelated proof of the
   path goal must not make that orphaned copy prove the root. *)
val orphaned_copy_tree0 =
  new_tree cluster_store1 fifo_goal []
val (orphaned_copy_root, orphaned_copy_tree1) =
  pop_expected orphaned_copy_tree0
val orphaned_copy_created =
  install_tree_rapp orphaned_copy_tree1 orphaned_copy_root
    aesopRule.RSafe "orphaned_copy_root" cluster_store1
    [coupled_goal, coupled_goal] []
val [orphaned_copy_path, orphaned_copy_original] =
  #goals orphaned_copy_created
val orphaned_copy_branch =
  install_tree_rapp (#tree orphaned_copy_created) orphaned_copy_path
    aesopRule.RSafe "orphaned_copy_branch" bound_coupled_store
    [fifo_goal] []
val [orphaned_copy_open, orphaned_copy] = #goals orphaned_copy_branch
val orphaned_copy_tree2 =
  close_tree_goal (#tree orphaned_copy_branch) orphaned_copy
val orphaned_copy_tree3 =
  close_tree_goal orphaned_copy_tree2 orphaned_copy_path

val _ =
  check
    ("aesop copy-derived goals require their proved support path",
     fn () =>
       #copy_of (aesopTree.goal orphaned_copy_tree3 orphaned_copy) =
         SOME orphaned_copy_original andalso
       #state (aesopTree.goal orphaned_copy_tree3 orphaned_copy_open) =
         aesopTree.Unknown andalso
       #state (aesopTree.goal orphaned_copy_tree3 orphaned_copy_original) =
         aesopTree.Unknown andalso
       #state (aesopTree.goal orphaned_copy_tree3 orphaned_copy_root) =
         aesopTree.Unknown)

(* The first support for one obligation can conflict only when a later
   obligation is considered.  Selection must then retry the earlier goal's
   next support, rather than treating the locally valid first path as a
   commitment. *)
val support_store_m1 =
  valOf (clasetMeta.bind (cluster_m1, boolSyntax.T) cluster_store2)
val support_store_both =
  valOf (clasetMeta.bind (cluster_m2, boolSyntax.T) support_store_m1)
val support_tree0 = new_tree cluster_store2 fifo_goal []
val (support_root, support_tree1) = pop_expected support_tree0
val support_root_install =
  install_tree_rapp support_tree1 support_root aesopRule.RSafe
    "support_root" cluster_store2
    [cluster_g2, cluster_g1, cluster_g3] []
val [support_path, support_original1, support_original2] =
  #goals support_root_install
fun support_copy_of tree original ids =
  valOf
    (List.find
      (fn id => #copy_of (aesopTree.goal tree id) = SOME original) ids)
val support_first =
  install_tree_rapp (#tree support_root_install) support_path
    aesopRule.RSafe "support_first" support_store_m1 [] []
val support_first_copy =
  support_copy_of (#tree support_first) support_original1
    (#goals support_first)
val support_second =
  install_tree_rapp (#tree support_first) support_path
    aesopRule.RSafe "support_second" support_store_both [] []
val support_second_copy1 =
  support_copy_of (#tree support_second) support_original1
    (#goals support_second)
val support_second_copy2 =
  support_copy_of (#tree support_second) support_original2
    (#goals support_second)
val support_tree2 =
  close_tree_goal (#tree support_second) support_first_copy
val support_tree3 = close_tree_goal support_tree2 support_second_copy1
val support_tree4 = close_tree_goal support_tree3 support_second_copy2
val support_selection =
  aesopTree.select_copy_supports support_tree4
    [support_original1,support_original2] []

val _ =
  check
    ("aesop copy-support selection backtracks across obligations",
     fn () =>
       case support_selection of
           NONE => false
         | SOME required =>
             List.exists
               (fn (goal,rid) =>
                 goal = support_path andalso rid = #rapp support_second)
               required andalso
             not
               (List.exists
                 (fn (goal,rid) =>
                   goal = support_path andalso rid = #rapp support_first)
                 required))

val coupled_stuck_tree0 =
  new_tree cluster_store1 fifo_goal []
val (coupled_stuck_root, coupled_stuck_tree1) =
  pop_expected coupled_stuck_tree0
val coupled_stuck_install =
  install_tree_rapp coupled_stuck_tree1 coupled_stuck_root
    aesopRule.RSafe "coupled_stuck" cluster_store1
    [coupled_goal, coupled_goal] []
val [coupled_stuck_left, coupled_stuck_right] =
  #goals coupled_stuck_install
val coupled_stuck_rapp =
  #rapp coupled_stuck_install
val coupled_stuck_tree2 =
  aesopTree.exhaust_goal coupled_stuck_left
    (#tree coupled_stuck_install)
val coupled_stuck_tree3 =
  aesopTree.exhaust_goal coupled_stuck_right coupled_stuck_tree2

val _ =
  check
    ("aesop clusters stick only after every coupled goal sticks",
     fn () =>
       #state
         (aesopTree.rapp coupled_stuck_tree2 coupled_stuck_rapp) =
         aesopTree.Unknown andalso
       #state
         (aesopTree.rapp coupled_stuck_tree3 coupled_stuck_rapp) =
         aesopTree.Stuck)

val (dependency_m1, dependency_store1) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} clasetMeta.empty
val (dependency_m2, dependency_store2) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} dependency_store1
val dependency_store3 =
  valOf (clasetMeta.bind
    (dependency_m1, dependency_m2) dependency_store2)
val (dependency_ty1, dependency_store4) =
  clasetMeta.new_tymeta dependency_store3
val (dependency_ty2, dependency_store5) =
  clasetMeta.new_tymeta dependency_store4
val dependency_store6 =
  valOf (clasetMeta.bind_ty
    (dependency_ty1, dependency_ty2) dependency_store5)
val dependency_param =
  Term.mk_var ("aesop_dependency_param", dependency_ty1)
val dependency_goal =
  tree_cgoal [dependency_param] [] dependency_m1
val dependency_deps =
  aesopTree.dependencies_of dependency_store6 dependency_goal

val _ =
  check
    ("aesop goal dependencies follow term and type binding residues",
     fn () =>
       HOLset.equal
         (#terms dependency_deps,
          HOLset.singleton Term.compare dependency_m2) andalso
       HOLset.equal
         (#types dependency_deps,
          HOLset.singleton Type.compare dependency_ty2))

val (assigned_meta, bookkeeping_store1) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} clasetMeta.empty
val (assigned_type, bookkeeping_store2) =
  clasetMeta.new_tymeta bookkeeping_store1
val (created_meta, bookkeeping_store3) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} bookkeeping_store2
val (created_type, bookkeeping_store4) =
  clasetMeta.new_tymeta bookkeeping_store3
val bookkeeping_store5 =
  valOf
    (clasetMeta.bind (assigned_meta, boolSyntax.T)
      bookkeeping_store4)
val bookkeeping_store6 =
  valOf
    (clasetMeta.bind_ty (assigned_type, Type.bool)
      bookkeeping_store5)
val bookkeeping_goal : Abbrev.goal = ([], boolSyntax.T)
val bookkeeping_result =
  Tactical.ALL_TAC bookkeeping_goal (Context.snapshot())
val bookkeeping_record =
  clasetReplay.make_record
    {kind = clasetReplay.Wrapper, target = 1, consumed = NONE,
     created = {terms = [created_meta], types = [created_type]},
     eigenvariables = [], validation = #2 bookkeeping_result,
     action =
       clasetReplay.fixed_action_on bookkeeping_goal bookkeeping_result,
     children = []}
val bookkeeping_root_goal =
  tree_cgoal
    [Term.mk_var ("aesop_assigned_type", assigned_type)]
    [] assigned_meta
val bookkeeping_tree0 =
  new_tree bookkeeping_store2 bookkeeping_root_goal []
val (bookkeeping_root, bookkeeping_tree1) =
  pop_expected bookkeeping_tree0
val bookkeeping_install =
  install_tree_rapp bookkeeping_tree1 bookkeeping_root aesopRule.RSafe
    "bookkeeping" bookkeeping_store6 [] [bookkeeping_record]
val bookkeeping_rapp =
  aesopTree.rapp (#tree bookkeeping_install)
    (#rapp bookkeeping_install)

val _ =
  check
    ("aesop rapps cache created records and parent-to-child assignments",
     fn () =>
       HOLset.equal
         (#terms (#created bookkeeping_rapp),
          HOLset.singleton Term.compare created_meta) andalso
       HOLset.equal
         (#types (#created bookkeeping_rapp),
          HOLset.singleton Type.compare created_type) andalso
       HOLset.equal
         (#terms (#assigned bookkeeping_rapp),
          HOLset.singleton Term.compare assigned_meta) andalso
       HOLset.equal
         (#types (#assigned bookkeeping_rapp),
          HOLset.singleton Type.compare assigned_type))

fun tree_creation_record terms types =
  let
    val goal = ([], boolSyntax.T)
    val result = Tactical.ALL_TAC goal (Context.snapshot())
  in
    clasetReplay.make_record
      {kind = clasetReplay.Wrapper, target = 1, consumed = NONE,
       created = {terms = terms, types = types},
       eigenvariables = [], validation = #2 result,
       action = clasetReplay.fixed_action_on goal result, children = []}
  end

fun bind_tree_meta meta value store =
  case clasetMeta.bind (meta, value) store of
      SOME result => result
    | NONE => raise Fail "expected aesop tree metavariable binding"

fun original_goal tree id =
  case #copy_of (aesopTree.goal tree id) of
      NONE => id
    | SOME original => original

val (copy_meta, copy_store1) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} clasetMeta.empty
val copy_creator_record =
  tree_creation_record [copy_meta] []
val copy_tree0 =
  new_tree clasetMeta.empty fifo_goal []
val (copy_root, copy_tree1) =
  pop_expected copy_tree0
val copy_created =
  install_tree_rapp copy_tree1 copy_root aesopRule.RSafe
    "copy_creator" copy_store1
    [tree_cgoal [] [] copy_meta, tree_cgoal [] [] copy_meta]
    [copy_creator_record]
val [copy_path, copy_sibling] =
  #goals copy_created
val copy_explored =
  install_tree_rapp (#tree copy_created) copy_sibling aesopRule.RSafe
    "copy_existing_subtree" copy_store1
    [tree_cgoal [] [] copy_meta] []
val copy_store2 =
  bind_tree_meta copy_meta boolSyntax.T copy_store1
val copy_assigned =
  install_tree_rapp (#tree copy_explored) copy_path aesopRule.RSafe
    "copy_assign" copy_store2 [] []
val [copied_sibling] =
  #goals copy_assigned
val copied_sibling_node =
  aesopTree.goal (#tree copy_assigned) copied_sibling

val _ =
  check
    ("aesop copying instantiates coupled siblings without their subtrees",
     fn () =>
       #copy_of copied_sibling_node = SOME copy_sibling andalso
       aconv (#w (#cgoal copied_sibling_node)) boolSyntax.T andalso
       not
         (null
           (aesopTree.child_rapps
             (#tree copy_assigned) copy_sibling)) andalso
       null
         (aesopTree.child_rapps
           (#tree copy_assigned) copied_sibling))

(* One metavariable reaches the dependency sets under two spellings:
   [clasetMeta.bindings] reports the redex as [new_meta] created it, at a
   type that was still a type metavariable, while the goal dependencies go
   through [clasetMeta.metas_of], which normalises first and so carries the
   refined type.  Read as two terms they never intersect, and the coupled
   sibling below is left behind unproved instead of being copied. *)
val (respelt_type, respelt_store1) =
  clasetMeta.new_tymeta clasetMeta.empty
val (respelt_meta, respelt_store2) =
  clasetMeta.new_meta
    {allow = [], ty = respelt_type} respelt_store1
val respelt_store3 =
  case clasetMeta.bind_ty (respelt_type, Type.bool) respelt_store2 of
      SOME result => result
    | NONE => raise Fail "expected an aesop tree type binding"
val respelt_predicate =
  Term.mk_var
    ("aesop_respelt_predicate", respelt_type --> Type.bool)
val respelt_cgoal =
  tree_cgoal [] [] (Term.mk_comb (respelt_predicate, respelt_meta))
val respelt_tree0 =
  new_tree clasetMeta.empty fifo_goal []
val (respelt_root, respelt_tree1) =
  pop_expected respelt_tree0
val respelt_created =
  install_tree_rapp respelt_tree1 respelt_root aesopRule.RSafe
    "respelt_creator" respelt_store3 [respelt_cgoal, respelt_cgoal]
    [tree_creation_record [respelt_meta] [respelt_type]]
val [respelt_path, respelt_sibling] =
  #goals respelt_created
val respelt_explored =
  install_tree_rapp (#tree respelt_created) respelt_sibling
    aesopRule.RSafe "respelt_existing_subtree" respelt_store3
    [respelt_cgoal] []
val respelt_store4 =
  bind_tree_meta respelt_meta boolSyntax.T respelt_store3
val respelt_assigned =
  install_tree_rapp (#tree respelt_explored) respelt_path
    aesopRule.RSafe "respelt_assign" respelt_store4 [] []

val _ =
  check
    ("aesop copying identifies a metavariable respelt by a type binding",
     fn () =>
       case #goals respelt_assigned of
           [copied] =>
             #copy_of (aesopTree.goal (#tree respelt_assigned) copied) =
               SOME respelt_sibling
         | _ => false)

val (transitive_x, transitive_store1) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} clasetMeta.empty
val (transitive_y, transitive_store2) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} transitive_store1
val (transitive_z, transitive_store3) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} transitive_store2
val transitive_g1 =
  tree_cgoal [] [] transitive_x
val transitive_g2 =
  tree_cgoal [] []
    (boolSyntax.mk_conj (transitive_x, transitive_y))
val transitive_g3 =
  tree_cgoal [] [] transitive_y
val transitive_g4 =
  tree_cgoal [] [] transitive_z
val transitive_tree0 =
  new_tree clasetMeta.empty fifo_goal []
val (transitive_root, transitive_tree1) =
  pop_expected transitive_tree0
val transitive_created =
  install_tree_rapp transitive_tree1 transitive_root aesopRule.RSafe
    "transitive_creator" transitive_store3
    [transitive_g1, transitive_g2, transitive_g3, transitive_g4]
    [tree_creation_record
       [transitive_x, transitive_y, transitive_z] []]
val [transitive_id1, transitive_id2, transitive_id3,
     transitive_id4] =
  #goals transitive_created
val transitive_store4 =
  bind_tree_meta transitive_y boolSyntax.T transitive_store3
val transitive_first =
  install_tree_rapp (#tree transitive_created) transitive_id3
    aesopRule.RSafe "transitive_assign_y" transitive_store4 [] []
val [transitive_copy2] =
  #goals transitive_first
val transitive_store5 =
  bind_tree_meta transitive_x boolSyntax.F transitive_store4
val transitive_second =
  install_tree_rapp (#tree transitive_first) transitive_copy2
    aesopRule.RSafe "transitive_assign_x" transitive_store5 [] []
val [transitive_copy1] =
  #goals transitive_second

val _ =
  check
    ("aesop copying follows transitive G1-G2-G3 coupling",
     fn () =>
       #copy_of
         (aesopTree.goal
           (#tree transitive_first) transitive_copy2) =
         SOME transitive_id2 andalso
       #copy_of
         (aesopTree.goal
           (#tree transitive_second) transitive_copy1) =
         SOME transitive_id1 andalso
       aconv
         (#w
           (#cgoal
             (aesopTree.goal
               (#tree transitive_second) transitive_copy1)))
         boolSyntax.F andalso
       original_goal (#tree transitive_second) transitive_copy2 =
         transitive_id2 andalso
       transitive_id4 <> transitive_copy1)

val (duplicate_x, duplicate_store1) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} clasetMeta.empty
val (duplicate_y, duplicate_store2) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} duplicate_store1
val duplicate_path_goal =
  tree_cgoal [] []
    (boolSyntax.mk_conj (duplicate_x, duplicate_y))
val duplicate_sibling_goal =
  tree_cgoal [] []
    (boolSyntax.mk_disj (duplicate_x, duplicate_y))
val duplicate_tree0 =
  new_tree clasetMeta.empty fifo_goal []
val (duplicate_root, duplicate_tree1) =
  pop_expected duplicate_tree0
val duplicate_created =
  install_tree_rapp duplicate_tree1 duplicate_root aesopRule.RSafe
    "duplicate_creator" duplicate_store2
    [duplicate_path_goal, duplicate_sibling_goal]
    [tree_creation_record [duplicate_x, duplicate_y] []]
val [duplicate_path, duplicate_original] =
  #goals duplicate_created
val duplicate_store3 =
  bind_tree_meta duplicate_x boolSyntax.T duplicate_store2
val duplicate_first =
  install_tree_rapp (#tree duplicate_created) duplicate_path
    aesopRule.RSafe "duplicate_assign_x" duplicate_store3
    [tree_cgoal [] [] duplicate_y] []
val [duplicate_next, duplicate_first_copy] =
  #goals duplicate_first
val duplicate_store4 =
  bind_tree_meta duplicate_y boolSyntax.F duplicate_store3
val duplicate_second =
  install_tree_rapp (#tree duplicate_first) duplicate_next
    aesopRule.RSafe "duplicate_assign_y" duplicate_store4 [] []
val [duplicate_only_copy] =
  #goals duplicate_second

val _ =
  check
    ("aesop copying suppresses duplicate copies of one original",
     fn () =>
       #copy_of
         (aesopTree.goal
           (#tree duplicate_first) duplicate_first_copy) =
         SOME duplicate_original andalso
       #copy_of
         (aesopTree.goal
           (#tree duplicate_second) duplicate_only_copy) =
         SOME duplicate_original andalso
       aconv
         (#w
           (#cgoal
             (aesopTree.goal
               (#tree duplicate_second) duplicate_only_copy)))
         (clasetMeta.norm duplicate_store4
           (#w duplicate_sibling_goal)))

val dropped_homo =
  Term.mk_var
    ("aesop_dropped_homo",
     Type.bool --> Type.bool)
val dropped_bound =
  Term.mk_var ("aesop_dropped_bound", Type.bool)
val dropped_all =
  boolSyntax.mk_forall
    (dropped_bound, Term.mk_comb (dropped_homo, dropped_bound))
val dropped_root_goal =
  tree_cgoal [] []
    (boolSyntax.mk_exists
      (dropped_bound, Term.mk_comb (dropped_homo, dropped_bound)))
val (dropped_meta, dropped_store1) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} clasetMeta.empty
val dropped_homo_goal =
  tree_cgoal [] [dropped_all]
    (Term.mk_comb (dropped_homo, dropped_meta))
val dropped_related_goal =
  tree_cgoal [] [] dropped_meta
val dropped_tree0 =
  new_tree clasetMeta.empty dropped_root_goal []
val (dropped_root, dropped_tree1) =
  pop_expected dropped_tree0
val dropped_created =
  install_tree_rapp dropped_tree1 dropped_root aesopRule.RSafe
    "dropped_exists_intro" dropped_store1
    [dropped_homo_goal, dropped_related_goal]
    [tree_creation_record [dropped_meta] []]
val [dropped_path, dropped_related] =
  #goals dropped_created
val dropped_closed =
  install_tree_rapp (#tree dropped_created) dropped_path
    aesopRule.RSafe "dropped_witness_independent" dropped_store1 [] []
val [dropped_copy] =
  #goals dropped_closed
val dropped_grounded =
  clasetMeta.ground dropped_store1
val dropped_kernel_proof =
  SPEC (boolSyntax.mk_arb Type.bool) (ASSUME dropped_all)

val _ =
  check
    ("aesop dropped metas copy related goals without synthesis subgoals",
     fn () =>
       #copy_of
         (aesopTree.goal (#tree dropped_closed) dropped_copy) =
         SOME dropped_related andalso
       aconv
         (concl dropped_kernel_proof)
         (clasetMeta.norm dropped_grounded
           (Term.mk_comb (dropped_homo, dropped_meta))))

fun search_source norm safe unsafe
      ({mode, ...} :
       {mode : clasetUnify.mode, cgoal : clasetGoal.cgoal,
        store : clasetMeta.store}) : aesopRule.ruleset =
  {norm = norm,
   safe =
     {closers = safe mode, safe0_claset = [], safe_forward = [],
      safep_claset = [], conclusion_splits = [],
      assumption_splits = []},
   unsafe = unsafe}

fun search_tree outcome =
  case outcome of
      aesopSearch.SafeSaturated tree => tree
    | aesopSearch.SafeDepthLimit _ =>
        raise Fail "unexpected aesop search depth limit"
    | aesopSearch.SafeNormalisationLimit _ =>
        raise Fail "unexpected aesop search normalisation limit"

val search_first_rule =
  aesopRule.apply_rule
    {name = "first-safe", phase = aesopRule.RSafe,
     theorem = boolTheory.TRUTH, mode = clasetUnify.Match}
val search_second_rule =
  aesopRule.apply_rule
    {name = "second-safe", phase = aesopRule.RSafe,
     theorem = boolTheory.TRUTH, mode = clasetUnify.Match}
val search_commit_tree0 =
  new_tree clasetMeta.empty (tree_cgoal [] [] boolSyntax.T) []
val search_commit_tree =
  search_tree
    (aesopSearch.safe_saturate_in (Context.snapshot ())
      {max_depth = 10,
       rules =
         search_source []
           (fn clasetUnify.Match =>
                 [search_first_rule, search_second_rule]
             | clasetUnify.Unify => [search_second_rule])
           []}
      search_commit_tree0)
val search_commit_root =
  aesopTree.root search_commit_tree

val _ =
  check
    ("aesop safe search uses Match mode and commits the first rule",
     fn () =>
       case aesopTree.child_rapps search_commit_tree search_commit_root of
           [rid] =>
             #rule (aesopTree.rapp search_commit_tree rid) =
               "first-safe" andalso
             #state
               (aesopTree.goal search_commit_tree search_commit_root) =
               aesopTree.Proved
         | _ => false)

fun duplicate_search_step input =
  case
    seq.cases
      ((clasetStep.rule_step
         {theorem = boolTheory.TRUTH, elim = false,
          mode = clasetUnify.Match}) input)
  of
      NONE => seq.empty
    | SOME (result, _) => seq.fromList [result, result]

val search_multi_rule : aesopRule.rule =
  {name = "multi-step", phase = aesopRule.RSafe,
   apply =
     aesopRule.MultiStep
       [clasetStep.rule_step
          {theorem = boolTheory.TRUTH, elim = false,
           mode = clasetUnify.Match},
        clasetStep.rule_step
          {theorem = boolTheory.TRUTH, elim = false,
           mode = clasetUnify.Match}],
   once = false}
val search_alternative_rule : aesopRule.rule =
  {name = "alternatives", phase = aesopRule.RSafe,
   apply = aesopRule.EngineStep duplicate_search_step, once = false}
val search_fallback_rule =
  aesopRule.apply_rule
    {name = "fallback", phase = aesopRule.RSafe,
     theorem = boolTheory.TRUTH, mode = clasetUnify.Match}
val search_multi_tree =
  search_tree
    (aesopSearch.safe_saturate_in (Context.snapshot ())
      {max_depth = 10,
       rules =
         search_source []
           (fn _ =>
             [search_multi_rule, search_alternative_rule,
              search_fallback_rule])
           []}
      (new_tree clasetMeta.empty
        (tree_cgoal [] [] boolSyntax.T) []))
val search_multi_root =
  aesopTree.root search_multi_tree

val _ =
  check
    ("aesop safe search dynamically rejects multi-rule alternatives",
     fn () =>
       case aesopTree.child_rapps search_multi_tree search_multi_root of
           [rid] =>
             #rule (aesopTree.rapp search_multi_tree rid) = "fallback"
         | _ => false)

val (search_postpone_meta, search_postpone_store) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} clasetMeta.empty
val search_postpone_tree0 =
  new_tree search_postpone_store
    (tree_cgoal [] [boolSyntax.T] search_postpone_meta) []
val search_postpone_tree =
  search_tree
    (aesopSearch.safe_saturate_in (Context.snapshot ())
      {max_depth = 10,
       rules =
         search_source []
           (fn clasetUnify.Match => []
             | clasetUnify.Unify => [hd (aesopRule.closers ())])
           []}
      search_postpone_tree0)
val search_postpone_root =
  aesopTree.root search_postpone_tree

val _ =
  check
    ("aesop safe search postpones assumption close that assigns a meta",
     fn () =>
       let val root = aesopTree.goal search_postpone_tree
                        search_postpone_root
       in
         #safe_done root andalso
         null (aesopTree.child_rapps search_postpone_tree
           search_postpone_root) andalso
         (case #postponed root of
              [{rule = "assumption", node, ...}] =>
                null (clasetGoal.goals node) andalso
                not
                  (null
                    (#terms
                      (clasetMeta.bindings
                        (clasetGoal.store node))))
            | _ => false)
       end)

val (search_drop_meta, search_drop_store) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} clasetMeta.empty
val search_drop_target =
  boolSyntax.mk_conj (search_drop_meta, boolSyntax.T)
val search_drop_assumption =
  boolSyntax.mk_conj (boolSyntax.T, boolSyntax.T)
val search_split_rule =
  aesopRule.tactic_rule
    {name = "split", phase = aesopRule.RSafe,
     tactic = NTactical.LIFT Tactic.CONJ_TAC, index = NONE}
val search_drop_tree0 =
  new_tree search_drop_store
    (tree_cgoal [] [search_drop_assumption] search_drop_target) []
val search_drop_tree =
  search_tree
    (aesopSearch.safe_saturate_in (Context.snapshot ())
      {max_depth = 10,
       rules =
         search_source []
           (fn clasetUnify.Match => [search_split_rule]
             | clasetUnify.Unify =>
                 [hd (aesopRule.closers ()), search_split_rule])
           []}
      search_drop_tree0)
val search_drop_root =
  aesopTree.root search_drop_tree

val _ =
  check
    ("aesop installed safe result drops earlier postponed results",
     fn () =>
       case aesopTree.child_rapps search_drop_tree search_drop_root of
           [rid] =>
             null
               (#postponed
                 (aesopTree.goal search_drop_tree search_drop_root))
             andalso
             #rule (aesopTree.rapp search_drop_tree rid) = "split"
         | _ => false)

val search_forward_tree0 =
  new_tree clasetMeta.empty
    (tree_cgoal [] [forward_p, forward_q] forward_target) []
fun search_forward_rules mode =
  [aesopRule.default_forward_rule
    {name = "safe-forward", phase = aesopRule.RSafe,
     theorem = forward_theorem, mode = mode}]
val search_forward_tree =
  search_tree
    (aesopSearch.safe_saturate_in (Context.snapshot ())
      {max_depth = 10,
       rules =
         search_source [] search_forward_rules []}
      search_forward_tree0)
val search_forward_root =
  aesopTree.root search_forward_tree
val [search_forward_rapp] =
  aesopTree.child_rapps search_forward_tree search_forward_root
val [search_forward_child] =
  List.concat
    (map
      (fn cluster =>
        #goals (aesopTree.cluster search_forward_tree cluster))
      (#clusters
        (aesopTree.rapp search_forward_tree search_forward_rapp)))

val _ =
  check
    ("aesop safe search prevents repeated forward hypotheses",
     fn () =>
       length (aesopTree.rapps search_forward_tree) = 1 andalso
       (case
          #forwarded
            (aesopTree.goal search_forward_tree search_forward_child)
        of
            [added] => aconv added forward_conclusion
          | _ => false) andalso
       (case aesopSearch.safe_frontier search_forward_tree of
            [(id, {asl = added :: _, w, ...})] =>
              id = search_forward_child andalso
              aconv added forward_conclusion andalso
              aconv w forward_target
          | _ => false))

val search_wide_a =
  Term.mk_var ("aesop_search_wide_a", Type.bool)
val search_wide_b =
  Term.mk_var ("aesop_search_wide_b", Type.bool)
val search_wide_c =
  Term.mk_var ("aesop_search_wide_c", Type.bool)
val search_wide_d =
  Term.mk_var ("aesop_search_wide_d", Type.bool)
val search_wide_target =
  Term.mk_var ("aesop_search_wide_target", Type.bool)
val search_wide_left =
  boolSyntax.mk_conj (search_wide_a, search_wide_b)
val search_wide_right =
  boolSyntax.mk_conj (search_wide_c, search_wide_d)
fun search_wide_rules mode =
  [aesopRule.default_forward_rule
    {name = "wide-forward", phase = aesopRule.RSafe,
     theorem = boolTheory.AND1_THM, mode = mode}]
val search_wide_tree =
  search_tree
    (aesopSearch.safe_saturate_in (Context.snapshot ())
      {max_depth = 10,
       rules = search_source [] search_wide_rules []}
      (new_tree clasetMeta.empty
        (tree_cgoal [] [search_wide_left, search_wide_right]
          search_wide_target) []))

(* A safe forward rule with several conclusions is not a choice: taking one
   leaves the others for the child goal.  A determinism requirement would
   silence such a rule instead. *)
val _ =
  check
    ("aesop safe search installs every forward conclusion in one branch",
     fn () =>
       length (aesopTree.rapps search_wide_tree) = 2 andalso
       List.all
         (fn ({rule, ...} : aesopTree.rapp) => rule = "wide-forward")
         (aesopTree.rapps search_wide_tree) andalso
       (case aesopSearch.safe_frontier search_wide_tree of
            [(id, {asl, w, ...})] =>
              aconv w search_wide_target andalso
              length asl = 4 andalso
              List.exists (aconv search_wide_a) asl andalso
              List.exists (aconv search_wide_c) asl andalso
              length
                (#forwarded (aesopTree.goal search_wide_tree id)) = 2
          | _ => false))

val search_frontier_p =
  Term.mk_var ("aesop_search_frontier_p", Type.bool)
val search_frontier_q =
  Term.mk_var ("aesop_search_frontier_q", Type.bool)
val search_frontier_goal =
  boolSyntax.mk_imp
    (search_frontier_p,
     boolSyntax.mk_conj (search_frontier_p, search_frontier_q))
val search_disch_rule : aesopRule.rule =
  {name = "disch", phase = aesopRule.RNorm 0,
   apply = aesopRule.EngineStep
     (fn input =>
       clasetStep.blast_disch_step_in (Context.snapshot ()) input),
   once = false}
val search_frontier_tree =
  search_tree
    (aesopSearch.safe_saturate_in (Context.snapshot ())
      {max_depth = 10,
       rules =
         search_source [search_disch_rule]
           (fn _ => aesopRule.closers () @ [search_split_rule])
           []}
      (new_tree clasetMeta.empty
        (tree_cgoal [] [] search_frontier_goal) []))

val _ =
  check
    ("aesop safe saturation returns the exact normalised frontier",
     fn () =>
       case aesopSearch.safe_frontier search_frontier_tree of
           [(_, {asl = [assumption], w, ...})] =>
             aconv assumption search_frontier_p andalso
             aconv w search_frontier_q
         | _ => false)

val _ =
  check
    ("aesop search defaults bound rapps and depth",
     fn () =>
       aesopSearch.default_config =
         {max_rapps = 200, max_depth = 30})

val search_unsafe_alternatives : aesopRule.rule =
  {name = "unsafe-alternatives", phase = aesopRule.RUnsafe 70,
   apply = aesopRule.EngineStep duplicate_search_step, once = false}
val search_unsafe_alternative_outcome =
  aesopSearch.search_in (Context.snapshot ()) aesopSearch.default_config
    (search_source [] (fn _ => []) [search_unsafe_alternatives])
    (new_tree clasetMeta.empty
      (tree_cgoal [] [] boolSyntax.T) [])

val _ =
  check
    ("aesop unsafe multi-rules install every alternative as sibling rapps",
     fn () =>
       case search_unsafe_alternative_outcome of
           aesopSearch.SearchProved tree =>
             let val root = aesopTree.root tree
             in
               case aesopTree.child_rapps tree root of
                   [first, second] =>
                     #rule (aesopTree.rapp tree first) =
                       "unsafe-alternatives" andalso
                     #rule (aesopTree.rapp tree second) =
                       "unsafe-alternatives" andalso
                     #prob (aesopTree.rapp tree first) = 70 andalso
                     #prob (aesopTree.rapp tree second) = 70
                 | _ => false
             end
         | _ => false)

val search_reoffer_unsafe =
  aesopRule.apply_rule
    {name = "unsafe-eighty", phase = aesopRule.RUnsafe 80,
     theorem = boolTheory.TRUTH, mode = clasetUnify.Unify}
val search_reoffer_outcome =
  aesopSearch.search_in (Context.snapshot ()) aesopSearch.default_config
    (search_source []
      (fn clasetUnify.Match => []
        | clasetUnify.Unify => [hd (aesopRule.closers ())])
      [search_reoffer_unsafe])
    (new_tree search_postpone_store
      (tree_cgoal [] [boolSyntax.T] search_postpone_meta) [])

val _ =
  check
    ("aesop re-offers postponed safe results as ninety-percent rapps",
     fn () =>
       case search_reoffer_outcome of
           aesopSearch.SearchProved tree =>
             let val root = aesopTree.root tree
             in
               case aesopTree.child_rapps tree root of
                   [rid] =>
                     #rule (aesopTree.rapp tree rid) = "assumption" andalso
                     #prob (aesopTree.rapp tree rid) = 90 andalso
                     (case #unsafe_cursor (aesopTree.goal tree root) of
                          [{name = "unsafe-eighty", ...}] => true
                        | _ => false)
                 | _ => false
             end
         | _ => false)

val transitivity_x =
  Term.mk_var ("aesop_transitivity_x", numSyntax.num)
val transitivity_a =
  Term.mk_var ("aesop_transitivity_a", numSyntax.num)
val transitivity_z =
  Term.mk_var ("aesop_transitivity_z", numSyntax.num)
val transitivity_xa =
  numSyntax.mk_leq (transitivity_x, transitivity_a)
val transitivity_az =
  numSyntax.mk_leq (transitivity_a, transitivity_z)
val transitivity_xz =
  numSyntax.mk_leq (transitivity_x, transitivity_z)

fun transitivity_source
      ({mode, cgoal = {w, ...}, ...} :
       {mode : clasetUnify.mode, cgoal : clasetGoal.cgoal,
        store : clasetMeta.store}) =
  let
    val reflexivity =
      aesopRule.apply_rule
        {name = "le-reflexivity", phase = aesopRule.RSafe,
         theorem = arithmeticTheory.LESS_EQ_REFL, mode = mode}
    val transitivity =
      aesopRule.apply_rule
        {name = "le-transitivity", phase = aesopRule.RUnsafe 60,
         theorem = arithmeticTheory.LESS_EQ_TRANS, mode = mode}
  in
    {norm = [],
     safe =
       {closers = [hd (aesopRule.closers ()), reflexivity],
        safe0_claset = [], safe_forward = [], safep_claset = [],
        conclusion_splits = [], assumption_splits = []},
     unsafe = if aconv w transitivity_xz then [transitivity] else []}
  end

val transitivity_outcome =
  aesopSearch.search_in (Context.snapshot ())
    aesopSearch.default_config transitivity_source
    (new_tree clasetMeta.empty
      (tree_cgoal []
        [transitivity_xa, transitivity_az] transitivity_xz) [])

fun rapp_named name ({rule, ...} : aesopTree.rapp) =
  rule = name

val _ =
  check
    ("aesop proves a transitivity chain through both witness choices",
     fn () =>
       case transitivity_outcome of
           aesopSearch.SearchProved tree =>
             let
               val root = aesopTree.root tree
               val trans_rapps =
                 List.filter (rapp_named "le-transitivity")
                   (aesopTree.rapps tree)
               val trans_children =
                 case trans_rapps of
                     [rapp] =>
                       List.concat
                         (map
                           (fn cid =>
                             #goals (aesopTree.cluster tree cid))
                           (#clusters rapp))
                   | _ => []
               val first =
                 case trans_children of child :: _ => SOME child | _ => NONE
               val choices =
                 case first of
                     NONE => []
                   | SOME child =>
                       map (aesopTree.rapp tree)
                         (aesopTree.child_rapps tree child)
             in
               #state (aesopTree.goal tree root) =
                 aesopTree.Proved andalso
               List.exists (rapp_named "assumption") choices andalso
               List.exists (rapp_named "le-reflexivity") choices andalso
               List.all
                 (fn rapp =>
                   not (aesopTree.dependencies_empty (#assigned rapp)))
                 choices
             end
         | _ => false)

fun kernel_replays tree (goal as (_, target)) =
  case Tactical.VALID (aesopSearch.REPLAY_TAC tree) goal of
      ([], validation) => aconv (concl (validation [])) target
    | _ => false

val _ =
  check
    ("aesop extracts copied transitivity branches positionally",
     fn () =>
       case transitivity_outcome of
           aesopSearch.SearchProved tree =>
             kernel_replays tree
               ([transitivity_xa, transitivity_az],
                transitivity_xz)
         | _ => false)

val replay_norm_p =
  Term.mk_var ("aesop_replay_norm_p", Type.bool)
val replay_norm_target =
  boolSyntax.mk_imp (replay_norm_p, replay_norm_p)
val replay_norm_outcome =
  aesopSearch.search_in (Context.snapshot ()) aesopSearch.default_config
    (search_source [search_disch_rule]
      (fn _ => aesopRule.closers ()) [])
    (new_tree clasetMeta.empty
      (tree_cgoal [] [] replay_norm_target) [])

val _ =
  check
    ("aesop replays each norm chain before its winning rapp",
     fn () =>
       case replay_norm_outcome of
           aesopSearch.SearchProved tree =>
             kernel_replays tree ([], replay_norm_target)
         | _ => false)

val replay_wrapper_target =
  boolSyntax.mk_conj (boolSyntax.T, boolSyntax.T)
fun replay_wrapper_rules mode =
  aesopRule.closers () @
  [aesopRule.apply_rule
     {name = "replay-truth", phase = aesopRule.RSafe,
      theorem = boolTheory.TRUTH, mode = mode},
   search_split_rule]
val replay_wrapper_outcome =
  aesopSearch.search_in (Context.snapshot ()) aesopSearch.default_config
    (search_source []
      replay_wrapper_rules [])
    (new_tree clasetMeta.empty
      (tree_cgoal [] [] replay_wrapper_target) [])

val _ =
  check
    ("aesop replays recorded rendered-tactic actions exactly",
     fn () =>
       case replay_wrapper_outcome of
           aesopSearch.SearchProved tree =>
             kernel_replays tree ([], replay_wrapper_target)
         | _ => false)

val replay_dropped_pred =
  Term.mk_var
    ("aesop_replay_dropped_pred", Type.bool --> Type.bool)
val replay_dropped_bound =
  Term.mk_var ("aesop_replay_dropped_bound", Type.bool)
val replay_dropped_body =
  Term.mk_comb (replay_dropped_pred, replay_dropped_bound)
val replay_dropped_all =
  boolSyntax.mk_forall
    (replay_dropped_bound, replay_dropped_body)
val replay_dropped_exists =
  boolSyntax.mk_exists
    (replay_dropped_bound, replay_dropped_body)
val replay_exists_intro =
  GEN replay_dropped_pred
    (GEN replay_dropped_bound
      (DISCH replay_dropped_body
        (EXISTS
          (replay_dropped_exists, replay_dropped_bound)
          (ASSUME replay_dropped_body))))
val replay_all_elim =
  GEN replay_dropped_pred
    (GEN replay_dropped_bound
      (DISCH replay_dropped_all
        (SPEC replay_dropped_bound
          (ASSUME replay_dropped_all))))

fun replay_dropped_source
      ({mode, ...} :
       {mode : clasetUnify.mode, cgoal : clasetGoal.cgoal,
        store : clasetMeta.store}) =
  let
    val all_elim =
      aesopRule.apply_rule
        {name = "dropped-all-elim", phase = aesopRule.RSafe,
         theorem = replay_all_elim, mode = mode}
    val exists_intro =
      aesopRule.apply_rule
        {name = "dropped-exists-intro",
         phase = aesopRule.RUnsafe 50,
         theorem = replay_exists_intro, mode = mode}
  in
    {norm = [],
     safe =
       {closers = aesopRule.closers (),
        safe0_claset = [all_elim], safe_forward = [],
        safep_claset = [], conclusion_splits = [],
        assumption_splits = []},
     unsafe = [exists_intro]}
  end

val replay_dropped_goal =
  ([replay_dropped_all], replay_dropped_exists)
val replay_dropped_outcome =
  aesopSearch.search_in (Context.snapshot ()) aesopSearch.default_config
    replay_dropped_source
    (new_tree clasetMeta.empty
      (tree_cgoal [] [replay_dropped_all]
        replay_dropped_exists) [])

val _ =
  check
    ("aesop grounds a dropped witness to ARB and verifies it kernel-side",
     fn () =>
       case replay_dropped_outcome of
           aesopSearch.SearchProved tree =>
             let
               val root = aesopTree.root tree
               val rid =
                 valOf
                   (List.find
                     (fn id =>
                       #rule (aesopTree.rapp tree id) =
                         "dropped-exists-intro")
                     (aesopTree.child_rapps tree root))
               val witness =
                 valOf
                   (List.find
                     (fn meta =>
                       Type.compare (type_of meta, Type.bool) = EQUAL)
                     (HOLset.listItems
                       (#terms (#created
                         (aesopTree.rapp tree rid)))))
               val grounded =
                 clasetReplay.grounded_store
                   (aesopSearch.extract tree)
             in
               aconv
                 (clasetMeta.norm grounded witness)
                 (boolSyntax.mk_arb Type.bool) andalso
               kernel_replays tree replay_dropped_goal
             end
         | _ => false)

fun replay_wrapper_record goal (goals, validation) =
  clasetReplay.make_record
    {kind = clasetReplay.Wrapper, target = 1, consumed = NONE,
     created = {terms = [], types = []},
     eigenvariables = map (fn _ => []) goals,
     validation = validation,
     action = clasetReplay.fixed_action_on goal (goals, validation),
     children = map (fn _ => NONE) goals}

val (corrupt_meta, corrupt_store0) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} clasetMeta.empty
val corrupt_store_true =
  bind_tree_meta corrupt_meta boolSyntax.T corrupt_store0
val corrupt_store_false =
  bind_tree_meta corrupt_meta boolSyntax.F corrupt_store0
val corrupt_goal : Abbrev.goal =
  ([], boolSyntax.mk_conj (boolSyntax.T, boolSyntax.T))
val corrupt_split_result =
  Tactic.CONJ_TAC corrupt_goal (Context.snapshot())
val corrupt_tree0 =
  new_tree corrupt_store0
    (tree_cgoal [] (#1 corrupt_goal) (#2 corrupt_goal)) []
val (corrupt_root, corrupt_tree1) =
  pop_expected corrupt_tree0
val corrupt_split =
  install_tree_rapp corrupt_tree1 corrupt_root aesopRule.RSafe
    "corrupt-split" corrupt_store0
    (map
      (fn (asl, w) => tree_cgoal [] asl w)
      (#1 corrupt_split_result))
    [replay_wrapper_record corrupt_goal corrupt_split_result]
val [corrupt_left, corrupt_right] =
  #goals corrupt_split
val corrupt_close_result =
  Tactic.ACCEPT_TAC boolTheory.TRUTH ([], boolSyntax.T) (Context.snapshot())
val corrupt_left_closed =
  install_tree_rapp (#tree corrupt_split) corrupt_left
    aesopRule.RSafe "corrupt-left" corrupt_store_true []
    [replay_wrapper_record ([], boolSyntax.T) corrupt_close_result]
val corrupt_tree =
  #tree
    (install_tree_rapp (#tree corrupt_left_closed) corrupt_right
      aesopRule.RSafe "corrupt-right" corrupt_store_false []
      [replay_wrapper_record ([], boolSyntax.T) corrupt_close_result])

val _ =
  check
    ("aesop treats conflicting winning stores as a hard replay error",
     fn () =>
       ((ignore (aesopSearch.REPLAY_TAC corrupt_tree corrupt_goal
                   (Context.snapshot()));
         false)
        handle HOL_ERR error =>
          String.isSubstring "engine bug" (Feedback.message_of error)))

val interrupt_goal : Abbrev.goal = ([], boolSyntax.T)
val interrupt_result : Abbrev.goal list * Abbrev.validation =
  ([], fn _ => raise Portable.Interrupt)
val interrupt_tree0 =
  new_tree clasetMeta.empty
    (tree_cgoal [] (#1 interrupt_goal) (#2 interrupt_goal)) []
val (interrupt_root, interrupt_tree1) =
  pop_expected interrupt_tree0
val interrupt_tree =
  #tree
    (install_tree_rapp interrupt_tree1 interrupt_root aesopRule.RSafe
      "interrupt-close" clasetMeta.empty []
      [replay_wrapper_record interrupt_goal interrupt_result])

(* The engine-bug diagnostic is a catch-all, so it has to make one
   exception for the interrupt that stopped the user's proof. *)
val _ =
  check
    ("aesop replay diagnostics never reinterpret an interrupt",
     fn () =>
       ((ignore (aesopSearch.REPLAY_TAC interrupt_tree interrupt_goal
                   (Context.snapshot()));
         false)
        handle Portable.Interrupt => true
             | HOL_ERR _ => false))

val search_limit_goal = boolSyntax.T
val search_limit_close =
  aesopRule.apply_rule
    {name = "limit-close", phase = aesopRule.RUnsafe 50,
     theorem = boolTheory.TRUTH, mode = clasetUnify.Unify}
val search_rapp_limit_outcome =
  aesopSearch.search_in (Context.snapshot ()) {max_rapps = 0, max_depth = 10}
    (search_source [] (fn _ => []) [search_limit_close])
    (new_tree clasetMeta.empty
      (tree_cgoal [] [] search_limit_goal) [])

val _ =
  check
    ("aesop max_rapps stops cleanly on the failure path",
     fn () =>
       case search_rapp_limit_outcome of
           aesopSearch.SearchFailed
             {tree, reason = aesopSearch.RappLimitReached,
              safe_goals} =>
                null (aesopTree.rapps tree) andalso
                (case safe_goals () of
                     [(_, {w, ...})] => aconv w search_limit_goal
                   | _ => false)
         | _ => false)

fun triple_search_step input =
  case
    seq.cases
      ((clasetStep.rule_step
         {theorem = boolTheory.TRUTH, elim = false,
          mode = clasetUnify.Match}) input)
  of
      NONE => seq.empty
    | SOME (result, _) => seq.fromList [result, result, result]

val search_wide_unsafe : aesopRule.rule =
  {name = "unsafe-wide", phase = aesopRule.RUnsafe 70,
   apply = aesopRule.EngineStep triple_search_step, once = false}
val search_skip_outcome =
  aesopSearch.search_in (Context.snapshot ()) {max_rapps = 2, max_depth = 10}
    (search_source [] (fn _ => [])
      [search_wide_unsafe, search_limit_close])
    (new_tree clasetMeta.empty
      (tree_cgoal [] [] search_limit_goal) [])

(* An unsafe rule whose alternatives do not fit the global budget is
   inapplicable at that goal, not the end of the search: installing a
   prefix of them would be order-dependent incompleteness, and failing
   outright loses every other rule. *)
val _ =
  check
    ("aesop skips over-budget unsafe rules and keeps searching",
     fn () =>
       case search_skip_outcome of
           aesopSearch.SearchProved tree =>
             (case aesopTree.rapps tree of
                  [{rule, ...}] => rule = "limit-close"
                | _ => false)
         | _ => false)

val search_safe_limit_close =
  aesopRule.apply_rule
    {name = "safe-limit-close", phase = aesopRule.RSafe,
     theorem = boolTheory.TRUTH, mode = clasetUnify.Match}
val search_safe_rapp_limit_outcome =
  aesopSearch.search_in (Context.snapshot ()) {max_rapps = 0, max_depth = 10}
    (search_source []
      (fn _ => [search_safe_limit_close]) [])
    (new_tree clasetMeta.empty
      (tree_cgoal [] [] search_limit_goal) [])

val _ =
  check
    ("aesop max_rapps prevents committed safe applications",
     fn () =>
       case search_safe_rapp_limit_outcome of
           aesopSearch.SearchFailed
             {tree, reason = aesopSearch.RappLimitReached, ...} =>
               null (aesopTree.rapps tree) andalso
               #state
                 (aesopTree.goal tree (aesopTree.root tree)) =
                 aesopTree.Unknown
         | _ => false)

val search_depth_split =
  aesopRule.tactic_rule
    {name = "depth-split", phase = aesopRule.RUnsafe 50,
     tactic = NTactical.LIFT Tactic.CONJ_TAC, index = NONE}
val search_depth_target =
  boolSyntax.mk_conj (search_limit_goal, search_limit_goal)
val search_depth_limit_outcome =
  aesopSearch.search_in (Context.snapshot ()) {max_rapps = 10, max_depth = 1}
    (search_source [] (fn _ => []) [search_depth_split])
    (new_tree clasetMeta.empty
      (tree_cgoal [] [] search_depth_target) [])

val _ =
  check
    ("aesop max_depth exhausts only the offending branch and fails cleanly",
     fn () =>
       case search_depth_limit_outcome of
           aesopSearch.SearchFailed
             {tree, reason = aesopSearch.DepthLimitReached,
              safe_goals} =>
                length (aesopTree.rapps tree) = 1 andalso
                (case safe_goals () of
                     [(_, {w, ...})] => aconv w search_depth_target
                   | _ => false)
         | _ => false)

val search_safe_goal_p =
  Term.mk_var ("aesop_safe_goal_p", Type.bool)
val search_safe_goal_q =
  Term.mk_var ("aesop_safe_goal_q", Type.bool)
val search_safe_goal_target =
  boolSyntax.mk_conj
    (boolSyntax.F,
     boolSyntax.mk_conj (search_safe_goal_p, search_safe_goal_q))
val search_safe_goal_outcome =
  aesopSearch.search_in (Context.snapshot ()) aesopSearch.default_config
    (search_source [] (fn _ => [search_split_rule]) [])
    (new_tree clasetMeta.empty
      (tree_cgoal [] [] search_safe_goal_target) [])

fun contains_target target =
  List.exists
    (fn (_, ({w, ...} : clasetGoal.cgoal)) => aconv w target)

val _ =
  check
    ("aesop failure completes and reports the exhaustive safe goals",
     fn () =>
       case search_safe_goal_outcome of
           aesopSearch.SearchFailed
             {reason = aesopSearch.SearchExhausted, safe_goals, ...} =>
               let
                 val goals = safe_goals ()
               in
                 length goals = 3 andalso
                 contains_target boolSyntax.F goals andalso
                 contains_target search_safe_goal_p goals andalso
                 contains_target search_safe_goal_q goals
               end
         | _ => false)

val _ =
  check
    ("aesop failure defers its safe-goal report until applied",
     fn () =>
       case search_safe_goal_outcome of
           aesopSearch.SearchFailed {safe_goals, ...} =>
             let
               val first = safe_goals ()
               val second = safe_goals ()
             in
               length first = 3 andalso
               ListPair.allEq
                 (fn ((_, {w = w1, ...} : clasetGoal.cgoal),
                      (_, {w = w2, ...} : clasetGoal.cgoal)) =>
                   aconv w1 w2)
                 (first, second)
             end
         | _ => false)

val _ =
  check
    ("aesop trace levels report outcomes expansions and full nodes",
     fn () =>
       let
         val old_trace = Feedback.current_trace "aesop"
         val notices = ref ([] : string list)
         fun remember message = notices := message :: !notices
         val _ = Feedback.set_trace "aesop" 3
         val _ =
           Lib.with_flag
             (Feedback.MESG_outstream, remember)
             (fn () =>
               (ignore
                  (aesopSearch.search_in (Context.snapshot ())
                     aesopSearch.default_config
                    transitivity_source
                    (new_tree clasetMeta.empty
                      (tree_cgoal []
                        [transitivity_xa, transitivity_az]
                        transitivity_xz) []));
                ignore
                  (aesopSearch.search_in (Context.snapshot ())
                     aesopSearch.default_config
                    (search_source [] (fn _ => []) [])
                    (new_tree clasetMeta.empty
                      (tree_cgoal [] [] search_limit_goal) [])))) ()
         val _ = Feedback.set_trace "aesop" old_trace
       in
         List.exists (String.isSubstring "search exhausted") (!notices)
         andalso
         List.exists (String.isSubstring "safe goal") (!notices)
         andalso
         List.exists (String.isSubstring "expanding goal") (!notices)
         andalso
         List.exists (String.isSubstring "copied") (!notices)
         andalso
         List.exists (String.isSubstring "candidate goal") (!notices)
       end)

val _ =
  check
    ("aesopLib exposes the search defaults and TypeBase cases builder",
     fn () =>
       aesopLib.default_config =
         {max_rapps = 200, max_depth = 30} andalso
       String.isPrefix "cases "
         (#name
           (aesopLib.cases_rule_for Type.bool : aesopLib.rule)))

val surface_p = Term.mk_var ("aesop_surface_p", Type.bool)
val surface_q = Term.mk_var ("aesop_surface_q", Type.bool)
val surface_r = Term.mk_var ("aesop_surface_r", Type.bool)

val _ =
  check
    ("AESOP_TAC has close-or-fail semantics",
     fn () =>
       ((ignore (aesopLib.AESOP_TAC [] ([], surface_p)
                   (Context.snapshot())); false)
        handle HOL_ERR _ => true))

(* A caller may pose a quantified assumption contracted, and the engine's
   entry spells it out: the proof aesop replays then assumes [!x. P x]
   where the goal lists [$! P].  Closing the goal means the replay
   restates the proof in the spelling the caller used. *)
val _ =
  check
    ("AESOP_TAC closes a goal whose assumption the caller posed contracted",
     fn () =>
       let
         val predicate =
           Term.mk_var ("aesop_contracted_predicate", Type.ind --> Type.bool)
         val witness = Term.mk_var ("aesop_contracted_witness", Type.ind)
         val assumption =
           Term.mk_comb
             (Term.inst [Type.alpha |-> Type.ind] boolSyntax.universal,
              predicate)
         val goal = ([assumption], Term.mk_comb (predicate, witness))
       in
         null (#1 (Tactical.VALID (aesopLib.AESOP_TAC []) goal))
       end)

val surface_global_rules =
  map (fn (_, (name, _)) => name)
    (clasetLib.rules_of (clasetLib.the_claset ()))

val surface_fact =
  DISJ1 (ASSUME surface_q) surface_r
val surface_inserted =
  residual
    (aesopLib.AESOP_SAFE_TAC [surface_fact, markerLib.NoAsms])
    ([surface_q], surface_p)

val _ =
  check
    ("AESOP_SAFE_TAC counts fact insertion as progress and retains facts",
     fn () =>
       case surface_inserted of
           [([left, left_original], left_target),
            ([right, right_original], right_target)] =>
             aconv left surface_q andalso
             aconv left_original surface_q andalso
             aconv right surface_r andalso
             aconv right_original surface_q andalso
             aconv left_target surface_p andalso
             aconv right_target surface_p
         | _ => false)

val aesop_safe_fact_q_def =
  new_definition
    ("aesop_safe_fact_q_def",
     ``aesop_safe_fact_q (x:'a) <=> T``)
val aesop_safe_implication_fact =
  Tactical.prove
    (``!x:'a. aesop_safe_fact_p x ==> aesop_safe_fact_q x``,
     Rewrite.REWRITE_TAC [aesop_safe_fact_q_def])

val _ =
  check
    ("AESOP_SAFE_TAC retains a supplied conditional fact",
     fn () =>
       let
         val goal =
           ([``aesop_safe_fact_p (a:'a):bool``],
            ``aesop_safe_fact_q (a:'a)``)
         fun outcome tactic =
           SOME (residual tactic goal) handle HOL_ERR _ => NONE
         val explicit =
           outcome
             (Tactical.THEN
               (Tactic.ASSUME_TAC aesop_safe_implication_fact,
                Tactical.TRY (aesopLib.AESOP_SAFE_TAC [])))
         val supplied =
           outcome
             (aesopLib.AESOP_SAFE_TAC
               [aesop_safe_implication_fact])
         val without = outcome (aesopLib.AESOP_SAFE_TAC [])
       in
         (case without of SOME [] => false | _ => true) andalso
         (case (explicit, supplied) of
             (SOME left, SOME right) =>
               ListPair.allEq
                 (fn (first, second) =>
                   boolSyntax.goal_eq first second)
                 (left, right)
           | _ => false)
       end)

val _ =
  check
    ("AESOP_SAFE_TAC does not invent a conditional premise",
     fn () =>
       let
         val target = ``aesop_safe_fact_q (a:'a)``
         val result =
           SOME
             (residual
               (aesopLib.AESOP_SAFE_TAC
                 [aesop_safe_implication_fact])
               ([], target))
           handle HOL_ERR _ => NONE
       in
         case result of
             SOME goals =>
               not (null goals) andalso
               List.exists
                 (fn (_, remaining) => aconv remaining target)
                 goals
           | NONE => false
       end)

val aesop_fact_id_def =
  new_definition ("aesop_fact_id_def", ``aesop_fact_id (x:'a) = x``)
val aesop_fact_bridge_def =
  new_definition
    ("aesop_fact_bridge_def",
     ``aesop_fact_bridge (n:num) = aesop_fact_id T``)
val aesop_fact_id =
  Tactical.prove
    (``!x:'a. aesop_fact_id x = x``,
     Rewrite.REWRITE_TAC [aesop_fact_id_def])
val aesop_fact_bridge =
  Tactical.prove
    (``!n:num. aesop_fact_bridge n = aesop_fact_id T``,
     Rewrite.REWRITE_TAC [aesop_fact_bridge_def])

val _ =
  check
    ("AESOP_SAFE_TAC normalizes with a fact at a later exposed type",
     fn () =>
       let
         val goal = ([], ``aesop_fact_bridge 0 = T``)
         fun closes facts =
           null (residual (aesopLib.AESOP_SAFE_TAC facts) goal)
             handle HOL_ERR _ => false
       in
         not (closes [aesop_fact_bridge]) andalso
         not (closes [aesop_fact_id]) andalso
         closes [aesop_fact_bridge, aesop_fact_id]
       end)

val _ =
  check
    ("AESOP_SAFE_TAC reads equations from a conjunctive citation",
     fn () =>
       null
         (residual
           (aesopLib.AESOP_SAFE_TAC
             [Thm.CONJ aesop_fact_bridge aesop_fact_id])
           ([], ``aesop_fact_bridge 0 = T``)))

val _ =
  check
    ("AESOP_SAFE_TAC fails when insertion and safe search change nothing",
     fn () =>
       ((ignore (aesopLib.AESOP_SAFE_TAC [] ([], surface_p)
                   (Context.snapshot())); false)
        handle HOL_ERR _ => true))

val surface_conj_intro =
  DISCH surface_p
    (DISCH surface_q
      (CONJ (ASSUME surface_p) (ASSUME surface_q)))
val surface_safe_residue =
  residual
    (aesopLib.AESOP_SAFE_TAC
      [clasetLib.SIntro surface_conj_intro])
    ([], boolSyntax.mk_conj (surface_p, surface_q))

val _ =
  check
    ("AESOP_SAFE_TAC consumes claset markers and returns exact residues",
     fn () =>
       case surface_safe_residue of
           [([], left), ([], right)] =>
             aconv left surface_p andalso aconv right surface_q
         | _ => false)

val surface_norm_rule =
  DISCH surface_p
    (DISJ1 (ASSUME surface_p) surface_q)
val surface_norm_residue =
  residual
    (aesopLib.AESOP_SAFE_TAC
      [clasetLib.Norm surface_norm_rule, markerLib.NoAsms])
    ([], boolSyntax.mk_disj (surface_p, surface_q))

val _ =
  check
    ("AESOP_SAFE_TAC consumes Norm markers through the norm builder",
     fn () =>
       case surface_norm_residue of
           [([], target)] => aconv target surface_p
         | _ => false)

val surface_implication =
  boolSyntax.mk_imp (surface_p, surface_q)
val surface_forward_rule = ASSUME surface_implication

val _ =
  check
    ("AESOP_TAC consumes unsafe Forward markers",
     fn () =>
       null
         (residual
           (aesopLib.AESOP_TAC
             [clasetLib.Forward surface_forward_rule,
              markerLib.NoAsms])
           ([surface_p, surface_implication], surface_q)))

val _ =
  check
    ("AESOP_SAFE_TAC consumes SForward markers",
     fn () =>
       null
         (residual
           (aesopLib.AESOP_SAFE_TAC
             [clasetLib.SForward surface_forward_rule,
              markerLib.NoAsms])
           ([surface_p, surface_implication], surface_q)))

val surface_function =
  Term.mk_var
    ("aesop_surface_function", Type.bool --> Type.bool)
val surface_application =
  Term.mk_comb (surface_function, surface_p)
val surface_rewrite =
  ASSUME (boolSyntax.mk_eq (surface_application, surface_p))

val _ =
  check
    ("AESOP_TAC installs Simp arguments in the invocation simpset",
     fn () =>
       null
         (residual
           (aesopLib.AESOP_TAC
             [clasetLib.Simp surface_rewrite, markerLib.NoAsms])
           ([surface_p, concl surface_rewrite],
            surface_application)))

val surface_iff_function =
  Term.mk_var
    ("aesop_surface_iff_function", Type.bool --> Type.bool)
val surface_iff_application =
  Term.mk_comb (surface_iff_function, surface_p)
val surface_iff =
  ASSUME (boolSyntax.mk_eq (surface_iff_application, surface_p))

val _ =
  check
    ("AESOP_TAC installs Iff arguments as rules and rewrites",
     fn () =>
       null
         (residual
           (aesopLib.AESOP_TAC
             [clasetLib.Iff surface_iff, markerLib.NoAsms])
           ([surface_p, concl surface_iff],
            surface_iff_application)))

val surface_control_function =
  Term.mk_var
    ("aesop_surface_control_function", Type.bool --> Type.bool)
val surface_control_application =
  Term.mk_comb (surface_control_function, surface_p)
val surface_control_equality =
  boolSyntax.mk_eq (surface_control_application, boolSyntax.T)

val surface_with_asms =
  residual
    (aesopLib.AESOP_SAFE_TAC [])
    ([surface_control_equality], surface_control_application)
val surface_without_asms =
  SOME
    (residual
      (aesopLib.AESOP_SAFE_TAC [markerLib.NoAsms])
      ([surface_control_equality], surface_control_application))
  handle HOL_ERR _ => NONE

val _ =
  check
    ("AESOP_SAFE_TAC forwards generic simplifier controls",
     fn () =>
       null surface_with_asms andalso
       (case surface_without_asms of
            SOME [(_, target)] =>
              aconv target surface_control_application
          | _ => false))

val surface_explicit_simpset =
  simpLib.++
    (simpLib.empty_ss, simpLib.rewrites [surface_rewrite])

val _ =
  check
    ("CS_AESOP_TAC uses its explicit claset and simpset",
     fn () =>
       null
         (residual
           (aesopLib.CS_AESOP_TAC
             aesopLib.default_config clasetLib.empty_cs
             surface_explicit_simpset)
           ([surface_p, concl surface_rewrite],
            surface_application)))

val surface_explicit_claset =
  clasetLib.add_rule
    {kind = clasetRules.Intro, safe = true, prio = NONE}
    ("aesop-selftest-explicit-safe", surface_conj_intro)
    clasetLib.empty_cs
val surface_explicit_residue =
  residual
    (aesopLib.CS_AESOP_SAFE_TAC
      aesopLib.default_config surface_explicit_claset
      simpLib.empty_ss)
    ([], boolSyntax.mk_conj (surface_p, surface_q))

val _ =
  check
    ("CS_AESOP_SAFE_TAC saturates its explicit safe context",
     fn () =>
       case surface_explicit_residue of
           [([], left), ([], right)] =>
             aconv left surface_p andalso aconv right surface_q
         | _ => false)

(* A polymorphic [Dest] rule applied to a lambda binds the rule's type
   metavariable, and that respells the metavariable its two child goals
   share -- the created spelling the store's bindings report and the
   refined spelling a normalised goal carries.  Read as two metavariables
   the goals are uncoupled: they fall into separate clusters and the
   branch that assigns the shared metavariable copies neither of them, so
   nothing discharges the sibling and kernel replay of the winning tree
   fails.  Constants are needed rather than free variables: only a
   constant's type variable can be instantiated by the match. *)
val aesop_lambda_subp_def =
  new_definition
    ("aesop_lambda_subp_def",
     ``aesop_lambda_subp (s : 'a -> bool) t <=> !x. s x ==> t x``)

val aesop_lambda_inhab_def =
  new_definition
    ("aesop_lambda_inhab_def",
     ``aesop_lambda_inhab (s : 'a -> bool) <=> ?x. s x``)

local
  infix THEN
  val op THEN = Tactical.THEN
in
val aesop_lambda_intro =
  Tactical.prove
    (``!s t. (!x. (s : 'a -> bool) x ==> t x) ==>
             aesop_lambda_subp s t``,
     Rewrite.PURE_REWRITE_TAC [aesop_lambda_subp_def] THEN
     Tactical.REPEAT Tactic.GEN_TAC THEN
     Tactic.DISCH_TAC THEN
     Tactical.FIRST_ASSUM Tactic.ACCEPT_TAC)

val aesop_lambda_dest =
  Tactical.prove
    (``!s t x. aesop_lambda_subp (s : 'a -> bool) t ==> s x ==> t x``,
     Rewrite.PURE_REWRITE_TAC [aesop_lambda_subp_def] THEN
     Tactical.REPEAT Tactic.GEN_TAC THEN
     Tactic.DISCH_TAC THEN
     Tactical.FIRST_ASSUM Tactic.MATCH_ACCEPT_TAC)

val aesop_lambda_forward =
  Tactical.prove
    (``!s t. aesop_lambda_subp (s : 'a -> bool) t ==>
             aesop_lambda_inhab s ==> aesop_lambda_inhab t``,
     Rewrite.PURE_REWRITE_TAC
       [aesop_lambda_subp_def, aesop_lambda_inhab_def] THEN
     Tactical.REPEAT Tactic.GEN_TAC THEN
     Tactic.MATCH_ACCEPT_TAC boolTheory.MONO_EXISTS)
end

val aesop_lambda_goal : Abbrev.goal =
  ([``aesop_lambda_inhab (\x. x = (a:'a))``],
   ``aesop_lambda_subp (\x. x = (a:'a)) s ==> aesop_lambda_inhab s``)

val _ =
  check
    ("AESOP_TAC proves a goal whose coupling metavariable is respelt",
     fn () =>
       valid_closes
         (aesopLib.AESOP_TAC
           [clasetLib.SIntro aesop_lambda_intro,
            clasetLib.Dest aesop_lambda_dest,
            clasetLib.Forward aesop_lambda_forward])
         aesop_lambda_goal)

val _ =
  check
    ("aesop invocation arguments do not leak into the global claset",
     fn () =>
       map (fn (_, (name, _)) => name)
         (clasetLib.rules_of (clasetLib.the_claset ())) =
       surface_global_rules)

fun aesop_closes proposition =
  null (residual (aesopLib.AESOP_TAC []) ([], proposition))

val list_strength_ss =
  simpLib.named_rewrites "aesop-selftest-list-strength"
    [listTheory.APPEND, listTheory.LENGTH, listTheory.REVERSE_DEF,
     listTheory.MEM]

fun aesop_list_closes proposition =
  BasicProvers.with_simpset_updates
    (fn ss =>
      simpLib.++ (ss, list_strength_ss))
    aesop_closes proposition

val list_strength_smoke =
  [("append",
   ``((x:'a) :: xs) ++ ys = x :: (xs ++ ys)``),
   ("length",
    ``LENGTH [(x:'a); y] = SUC (SUC 0)``),
   ("reverse",
    ``REVERSE [(x:'a); y] = [y; x]``),
   ("membership",
    ``MEM (x:'a) ([y] ++ xs) <=> (x = y) \/ MEM x xs``)]

val _ =
  List.app
    (fn (name, proposition) =>
      check
        ("AESOP_TAC listTheory strength smoke: " ^ name,
         fn () => aesop_list_closes proposition))
    list_strength_smoke

val pelletier_propositional_smoke =
  [(1, ``(P ==> Q) <=> (~Q ==> ~P)``),
   (2, ``~~P <=> P``),
   (4, ``(~P ==> Q) <=> (~Q ==> P)``),
   (5, ``((P \/ Q) ==> (P \/ R)) ==> (P \/ (Q ==> R))``),
   (8, ``((P ==> Q) ==> P) ==> P``)]

val _ =
  List.app
    (fn (number, proposition) =>
      check
        ("AESOP_TAC Pelletier " ^ Int.toString number ^
         " propositional smoke",
         fn () => aesop_closes proposition))
    pelletier_propositional_smoke

(* Both goals below reach a rule application whose two coupled subgoals
   are discharged unevenly: one member closes without assigning the
   metavariable they share -- on Pelletier 30 normalisation alone proves
   it -- so no copy of the sibling is made anywhere and the sibling stays
   open.  Reading the cluster disjunctively declared the application, and
   with it the root, proved, and [extract] then walked into a sibling it
   had no proof of and reported "winning forest has no proof of goal N".
   That is the engine contradicting itself, which is what the assertions
   below are about.  Pelletier 30 also exercises a wrapper record made
   before one shared marker is assigned while another remains open; final
   replay must apply the available assignment rather than returning the
   stale wrapper result unchanged. *)
val aesop_coupled_goals =
  [(30,
    ([],
     ``(!x:'a. P x \/ Q x ==> ~R x) /\
       (!x. (Q x ==> ~ss x) ==> P x /\ R x) ==> !x. ss x``)
    : Abbrev.goal),
   (31,
    ([],
     ``~(?x:'a. P x /\ (Q x \/ R x)) /\ (?x. L x /\ P x) /\
       (!x. ~R x ==> M x) ==> ?x. L x /\ M x``))]

fun aesop_diagnostic goal =
  (ignore (residual (aesopLib.AESOP_TAC []) goal); "")
  handle error as HOL_ERR _ => General.exnMessage error

val aesop_coupled_diagnostics =
  map (fn (number, goal) => (number, aesop_diagnostic goal))
    aesop_coupled_goals

val _ =
  List.app
    (fn (number, diagnostic) =>
      check
        ("AESOP_TAC Pelletier " ^ Int.toString number ^
         " proves no cluster it cannot extract",
         fn () =>
           not
             (String.isSubstring
               "winning forest has no proof of goal" diagnostic)))
    aesop_coupled_diagnostics

val _ =
  check
    ("AESOP_TAC Pelletier 30 grounds assigned wrapper markers in replay",
     fn () =>
       case aesop_coupled_diagnostics of
           (30, diagnostic) :: _ =>
             if diagnostic = "" then true
             else
               (print ("Pelletier 30 diagnostic: " ^ diagnostic ^ "\n");
                false)
         | _ => false)

val _ =
  check
    ("AESOP_TAC Pelletier 31 reports no proof instead of an engine bug",
     fn () =>
       case aesop_coupled_diagnostics of
           _ :: (31, diagnostic) :: _ =>
             not (String.isSubstring "aesop engine bug" diagnostic)
         | _ => false)

val strength_safe_imp_residue =
  residual
    (aesopLib.AESOP_SAFE_TAC [])
    ([],
     boolSyntax.mk_imp
       (surface_p, boolSyntax.mk_conj (surface_q, surface_r)))

val _ =
  check
    ("AESOP_SAFE_TAC returns the exact implication-conjunction frontier",
     fn () =>
       case strength_safe_imp_residue of
           [([left_assumption], left), ([right_assumption], right)] =>
             aconv left_assumption surface_p andalso
             aconv right_assumption surface_p andalso
             aconv left surface_q andalso
             aconv right surface_r
         | _ => false)

val strength_safe_disj_residue =
  residual
    (aesopLib.AESOP_SAFE_TAC [])
    ([], boolSyntax.mk_disj (surface_p, surface_q))

val _ =
  check
    ("AESOP_SAFE_TAC returns the exact safe disjunction frontier",
     fn () =>
       case strength_safe_disj_residue of
           [([assumption], target)] =>
             aconv assumption (boolSyntax.mk_neg surface_q) andalso
             aconv target surface_p
         | _ => false)

val surface_augmented =
  Term.mk_var ("aesop_surface_augmented", Type.bool)
val surface_augmented_called = ref false
val surface_registry_before =
  length (aesopRule.registered_tactic_rules ())
val surface_augmented_residue =
  aesopRule.with_tactic_rules
    (fn () =>
      (aesopLib.augment_aesop
         {name = "aesop-selftest-session-tactic",
          phase = aesopRule.RNorm ~1,
          tactic =
            NTactical.LIFT
              (fn goal =>
                (surface_augmented_called := true;
                 Tactic.ACCEPT_TAC (ASSUME surface_augmented) goal))};
       residual
         (aesopLib.AESOP_TAC [])
         ([surface_augmented], surface_augmented)))
    ()
val surface_registry_after =
  length (aesopRule.registered_tactic_rules ())

val _ =
  check
    ("augment_aesop wires session-only tactics into public search",
     fn () =>
       null surface_augmented_residue andalso
       !surface_augmented_called)

(* Deliberately not valid_closes: the goals below are also asserted not
   to close, and AESOP_TAC reports that either by leaving the goal or by
   failing, so a refusal counts as not closing rather than as an error. *)
fun closes_goal tactic goal =
  null (residual tactic goal) handle HOL_ERR _ => false

(* The same eta-matching pin as clasimp/selftest.sml, on aesop's own
   simpset: the two derive separately, so one carrying ETA_ss says
   nothing about the other. *)
val eta_matching_rule =
  Thm.ASSUME
    ``!start count. EVERY eta_matching_p (GENLIST ($+ start) count)``

val eta_matching_goal =
  ``EVERY eta_matching_p (GENLIST (\offset. eta_matching_base + offset) len)``

val _ =
  check
    ("the aesop simpset matches a rule across an eta step",
     fn () =>
       let
         val rewritten =
           simpLib.SIMP_CONV (aesopData.aesop_ss ()) [eta_matching_rule]
             eta_matching_goal
       in
         Term.aconv (boolSyntax.rhs (Thm.concl rewritten)) boolSyntax.T
       end
       handle Conv.UNCHANGED => false)

val aesop_linarith_rewrite =
  hd (Drule.CONJUNCTS arithmeticTheory.MIN_EQ_LE)

val aesop_linarith_tactic =
  aesopLib.AESOP_TAC
    [clasetLib.Simp aesop_linarith_rewrite]

val aesop_linarith_goal : Abbrev.goal =
  ([``(x:num) <= y``, ``y <= z``], ``MIN x z = x``)

val _ =
  check
    ("AESOP_TAC discharges a linear-arithmetic rewrite condition",
     fn () =>
       closes_goal aesop_linarith_tactic aesop_linarith_goal)

val aesop_arith_fact_goal : Abbrev.goal =
  ([``(x:num) ** 2 <= y``], ``MIN x y = x``)

val _ =
  check
    ("AESOP_TAC reads [arith] facts dynamically and leaves the set clean",
     fn () =>
       not
         (closes_goal aesop_linarith_tactic
            aesop_arith_fact_goal) andalso
       with_arith_fact
         (fn () =>
           closes_goal aesop_linarith_tactic
             aesop_arith_fact_goal) andalso
       not
         (closes_goal aesop_linarith_tactic
            aesop_arith_fact_goal))

(* The aesop simpset is derived from srw_ss, so an unsafe solver
   installed into the shared base -- an augment_srw_ss of a solver_ss
   fragment -- would be carried along by the derivation, and reach the
   normalisation phase ahead of linarith: traverseconfig_for_ss hands the
   unsafe solvers to every traversal as its side-condition solvers, and
   Traverse tries them in order.  The sentinel below records that it was
   asked and then declines, so that the goal is still discharged by the
   solver that ought to have had it in the first place and the assertion
   is about who was asked rather than about who succeeded.
   with_simpset_updates makes the base change temporary, so nothing of
   this reaches the tests after it. *)
val aesop_sentinel_name = "aesop-selftest-srw-sentinel"
val aesop_sentinel_asked = ref false
val aesop_sentinel_solver : Traverse.ssolver =
  {name = aesop_sentinel_name,
   solve =
     fn _ => fn _ =>
       (aesop_sentinel_asked := true;
        raise mk_HOL_ERR "selftest" aesop_sentinel_name
          "sentinel solvers decline every side condition")}

fun unsafe_solver_names simpset =
  map (fn ({name, ...} : Traverse.ssolver) => name)
    (#solvers (simpLib.traverseconfig_for_ss simpset))

val aesop_sentinel_names_before =
  unsafe_solver_names (aesopData.aesop_ss ())
val (aesop_sentinel_names, aesop_sentinel_closes) =
  BasicProvers.with_simpset_updates
    (fn base =>
      simpLib.++ (base, simpLib.solver_ss aesop_sentinel_solver))
    (fn () =>
      (unsafe_solver_names (aesopData.aesop_ss ()),
       closes_goal aesop_linarith_tactic aesop_linarith_goal))
    ()
val aesop_sentinel_names_after =
  unsafe_solver_names (aesopData.aesop_ss ())

val _ =
  check
    ("aesop simpset does not inherit unsafe solvers from srw_ss",
     fn () =>
       not (List.exists (equal aesop_sentinel_name)
         aesop_sentinel_names) andalso
       List.exists (equal "lin_arith") aesop_sentinel_names andalso
       not (!aesop_sentinel_asked) andalso
       aesop_sentinel_closes andalso
       aesop_sentinel_names_after = aesop_sentinel_names_before)

(* A tactic value is routinely bound before the declarations its goals
   need -- [val TAC = AESOP_TAC []] at the head of a script, then the
   theorems and simp rules the script proves.  Both entry points are
   therefore bound here, ahead of the rewrite and the claset rule the two
   goals below cannot be closed without. *)
val stale_tactic = aesopLib.AESOP_TAC [markerLib.NoAsms]
val stale_safe_tactic = aesopLib.AESOP_SAFE_TAC [markerLib.NoAsms]

(* The rewritten terms are of an uninterpreted type, so no rule of the
   claset or the simpset can relate them on its own. *)
val stale_element = Term.mk_var ("aesop_stale_element", Type.ind)
val stale_f =
  Term.mk_var ("aesop_stale_f", Type.ind --> Type.ind)
val stale_g =
  Term.mk_var ("aesop_stale_g", Type.ind --> Type.ind)
val stale_predicate =
  Term.mk_var ("aesop_stale_predicate", Type.ind --> Type.bool)
val stale_rewrite =
  ASSUME
    (boolSyntax.mk_eq
      (Term.mk_comb (stale_f, stale_element),
       Term.mk_comb (stale_g, stale_element)))

(* [NoAsms] keeps the rewrite's own hypothesis out of the simplifier, so
   only a simpset carrying the rewrite closes this goal. *)
val stale_simp_goal =
  ([concl stale_rewrite,
    Term.mk_comb
      (stale_predicate, Term.mk_comb (stale_g, stale_element))],
   Term.mk_comb
     (stale_predicate, Term.mk_comb (stale_f, stale_element)))

val stale_simp_closed =
  BasicProvers.with_simpset_updates
    (fn ss =>
      simpLib.++
        (ss,
         simpLib.named_rewrites "aesop-selftest-stale-rewrite"
           [stale_rewrite]))
    (fn () => closes_goal stale_tactic stale_simp_goal)
    ()

val _ =
  check
    ("AESOP_TAC reads the aesop simpset where it is applied",
     fn () => stale_simp_closed)

val stale_p = Term.mk_var ("aesop_stale_p", Type.bool)
val stale_q = Term.mk_var ("aesop_stale_q", Type.bool)
val stale_norm_rule =
  DISCH stale_p (DISJ1 (ASSUME stale_p) stale_q)
val stale_norm_name = "aesop-selftest-stale-norm"
val stale_claset_residue =
  let
    val _ =
      clasetLib.temp_add_rule
        {kind = clasetRules.Norm, safe = false, prio = NONE}
        (stale_norm_name, stale_norm_rule)
    val residue =
      SOME
        (residual stale_safe_tactic
          ([], boolSyntax.mk_disj (stale_p, stale_q)))
      handle HOL_ERR _ => NONE
  in
    clasetLib.temp_delrule stale_norm_name; residue
  end
val stale_claset_restored =
  not
    (List.exists (fn (_, (name, _)) => name = stale_norm_name)
      (clasetLib.rules_of (clasetLib.the_claset ())))

val _ =
  check
    ("AESOP_SAFE_TAC reads the claset where it is applied",
     fn () =>
       stale_claset_restored andalso
       (case stale_claset_residue of
            SOME [([], target)] => aconv target stale_p
          | _ => false))

val cases_predicate =
  Term.mk_var ("aesop_cases_predicate", Type.bool --> Type.bool)
val cases_variable =
  Term.mk_var ("aesop_cases_variable", Type.bool)

(* Only a case split on the boolean variable connects the goal to the two
   assumptions. *)
val cases_goal =
  ([Term.mk_comb (cases_predicate, boolSyntax.T),
    Term.mk_comb (cases_predicate, boolSyntax.F)],
   Term.mk_comb (cases_predicate, cases_variable))
val cases_without_rule =
  closes_goal (aesopLib.AESOP_TAC []) cases_goal
val cases_with_rule =
  aesopRule.with_tactic_rules
    (fn () =>
      (aesopLib.augment_aesop_rule
         (aesopLib.cases_rule_for Type.bool);
       closes_goal (aesopLib.AESOP_TAC []) cases_goal))
    ()
val cases_registry_after =
  length (aesopRule.registered_tactic_rules ())

val _ =
  check
    ("augment_aesop_rule installs a built cases rule into public search",
     fn () =>
       not cases_without_rule andalso
       cases_with_rule andalso
       cases_registry_after = surface_registry_before)

val _ =
  check
    ("augment_aesop_rule refuses rules the tactic registry cannot hold",
     fn () =>
       let
         val engine_rule =
           aesopRule.apply_rule
             {name = "aesop-selftest-engine-rule",
              phase = aesopRule.RUnsafe 50,
              theorem = boolTheory.TRUTH,
              mode = clasetUnify.Match}
         val refused =
           (aesopRule.with_tactic_rules
              (fn () =>
                (aesopLib.augment_aesop_rule engine_rule; false)) ()
            handle HOL_ERR _ => true)
       in
         refused andalso
         length (aesopRule.registered_tactic_rules ()) =
           surface_registry_before
       end)

(* Rule applications are aesop's unit of work; the shared meter carries
   them so a benchmark caller can tell search from rewriting. *)
val _ =
  check
    ("aesop search charges the shared work meter",
     fn () =>
       let
         val goal : Abbrev.goal =
           ([], ``((work_meter_p ==> work_meter_q) ==> work_meter_p) ==>
                 work_meter_p``)
         val (solved, work) =
           searchWork.measure
             (fn () =>
               case Lib.total (Tactical.VALID (aesopLib.AESOP_TAC [])) goal of
                   SOME ([], validation) => (ignore (validation []); true)
                 | _ => false)
       in
         solved andalso #rule_applications work > 0
       end)

(* Known forward conclusions may precede the one useful application.
   The application budget counts installed results, not the number of
   duplicate candidates examined while finding one. *)
val forward_clutter_q_def =
  new_definition
    ("forward_clutter_q_def",
     ``forward_clutter_q (x:'a) <=> T``)
val forward_clutter_fact =
  Tactical.prove
    (``!x:'a. forward_clutter_p x ==> forward_clutter_q x``,
     Rewrite.REWRITE_TAC [forward_clutter_q_def])
val forward_clutter_cs =
  clasetLib.add_rule
    {kind = clasetRules.Forward, safe = true, prio = NONE}
    ("forward-clutter", forward_clutter_fact) clasetLib.empty_cs
val forward_clutter_tac =
  aesopLib.CS_AESOP_TAC
    {max_rapps = 1000, max_depth = 50}
    forward_clutter_cs simpLib.empty_ss

fun forward_clutter_atom head i =
  Term.mk_comb
    (head, Term.mk_var ("clutter_item" ^ Int.toString i, Type.alpha))

fun forward_clutter_goal count position =
  let
    val p = ``forward_clutter_p:'a->bool``
    val q = ``forward_clutter_q:'a->bool``
    val useful = forward_clutter_atom p count
    val known_p = List.tabulate (count, forward_clutter_atom p)
    val known_q = List.tabulate (count, forward_clutter_atom q)
    val premises =
      List.take (known_p, position) @ [useful] @
      List.drop (known_p, position)
  in
    (premises @ known_q, forward_clutter_atom q count)
  end

val _ =
  check
    ("forward clutter fixture closes before the old boundary",
     fn () =>
       closes_goal forward_clutter_tac
         (forward_clutter_goal 0 0) andalso
       closes_goal forward_clutter_tac
         (forward_clutter_goal 199 199))

val _ =
  check
    ("forward search reaches useful candidates through known results",
     fn () =>
       List.all
         (fn count =>
           List.all
             (fn position =>
               closes_goal forward_clutter_tac
                 (forward_clutter_goal count position))
             [0, count div 2, count])
         [201, 0, 1, 199, 200, 257])

(* The first resumption of a fresh budgeted session. *)
fun run_session budget config claset simpset goal =
  aesopSearch.resume_budget_session
    (aesopLib.CS_AESOP_SESSION budget config claset simpset goal)

fun session_cutoff (aesopSearch.ResumedYielded {kind, usage, ...}) =
      SOME (kind, usage)
  | session_cutoff (aesopSearch.ResumedLimitReached {kind, usage}) =
      SOME (kind, usage)
  | session_cutoff (aesopSearch.ResumedFinished _) = NONE

val _ =
  check
    ("budgeted Aesop distinguishes cutoff from a funded forward proof",
     fn () =>
       let
         val goal = forward_clutter_goal 201 201
         val empty_budget =
           searchBudget.create
             {candidates = SOME 0, applications = NONE,
              normalization = NONE}
         val cutoff =
           run_session empty_budget
             {max_rapps = 1000, max_depth = 50}
             forward_clutter_cs simpLib.empty_ss goal
         val no_applications =
           searchBudget.create
             {candidates = NONE, applications = SOME 0,
              normalization = NONE}
         val application_cutoff =
           run_session no_applications
             {max_rapps = 1000, max_depth = 50}
             forward_clutter_cs simpLib.empty_ss goal
         val no_normalization =
           searchBudget.create
             {candidates = NONE, applications = NONE,
              normalization = SOME 0}
         val normalization_cutoff =
           run_session no_normalization
             {max_rapps = 1000, max_depth = 50}
             forward_clutter_cs simpLib.empty_ss goal
         val funded = searchBudget.unbounded ()
         val completed =
           run_session funded
             {max_rapps = 1000, max_depth = 50}
             forward_clutter_cs simpLib.empty_ss goal
         val terminal_budget =
           searchBudget.create
             {candidates = NONE, applications = SOME 0,
              normalization = NONE}
         val terminal_session =
           aesopLib.CS_AESOP_SESSION terminal_budget
             {max_rapps = 1000, max_depth = 50}
             forward_clutter_cs simpLib.empty_ss goal
         val terminal_limit =
           case aesopSearch.resume_budget_session terminal_session of
               aesopSearch.ResumedLimitReached
                 {kind = searchBudget.Application, ...} =>
                   (searchBudget.extend terminal_budget
                      searchBudget.Application 1;
                    (ignore
                       (aesopSearch.resume_budget_session
                         terminal_session);
                     false) handle HOL_ERR _ => true)
             | _ => false
       in
         (case session_cutoff cutoff of
              SOME (searchBudget.Candidate, usage) =>
                #candidates usage = 0
            | _ => false) andalso
         (case session_cutoff application_cutoff of
              SOME (searchBudget.Application, usage) =>
                #applications usage = 0 andalso
                #candidates usage > 0
            | _ => false) andalso
         (case session_cutoff normalization_cutoff of
              SOME (searchBudget.Normalization, usage) =>
                #normalization usage = 0
            | _ => false) andalso
         (case completed of
              aesopSearch.ResumedFinished
                (aesopSearch.SearchProved tree) =>
                  closes_goal (aesopSearch.REPLAY_TAC tree) goal
            | _ => false) andalso
         terminal_limit andalso
         #candidates (searchBudget.usage funded) > 200
       end)

val forward_clutter_unsafe_cs =
  clasetLib.add_rule
    {kind = clasetRules.Forward, safe = false, prio = SOME 50}
    ("forward-clutter-unsafe", forward_clutter_fact)
    clasetLib.empty_cs

val _ =
  check
    ("budgeted Aesop resumes a safe forward candidate scan",
     fn () =>
       let
         val (assumptions, target) =
           forward_clutter_goal 30 30
         val early =
           forward_clutter_atom
             ``forward_clutter_q:'a->bool`` 0
         val goal =
           (List.filter
              (fn fact => not (aconv fact early)) assumptions,
            target)
         val config = {max_rapps = 1000, max_depth = 50}
         val small =
           searchBudget.create
             {candidates = SOME 10, applications = NONE,
              normalization = NONE}
         val large = searchBudget.unbounded ()
         val session =
           aesopLib.CS_AESOP_SESSION small config
             forward_clutter_cs simpLib.empty_ss goal
         val reference =
           run_session large config
             forward_clutter_cs simpLib.empty_ss goal
         fun resume 0 _ _ = NONE
           | resume turns current yielded =
               (case aesopSearch.resume_budget_session current of
                    aesopSearch.ResumedYielded
                      {kind = searchBudget.Candidate,
                       session = next, ...} =>
                        (searchBudget.extend small
                           searchBudget.Candidate 10;
                         resume (turns - 1) next true)
                  | aesopSearch.ResumedFinished
                      (aesopSearch.SearchProved tree) =>
                        SOME (yielded, tree)
                  | _ => NONE)
       in
         case (resume 100 session false, reference) of
             (SOME (true, tree),
              aesopSearch.ResumedFinished
                (aesopSearch.SearchProved _)) =>
               closes_goal (aesopSearch.REPLAY_TAC tree) goal andalso
               #candidates (searchBudget.usage small) =
               #candidates (searchBudget.usage large)
           | _ => false
       end)

val _ =
  check
    ("budgeted Aesop resumes an unsafe forward candidate scan",
     fn () =>
       let
         val goal = forward_clutter_goal 201 201
         val config = {max_rapps = 1000, max_depth = 50}
         val small =
           searchBudget.create
             {candidates = SOME 25, applications = NONE,
              normalization = NONE}
         val large = searchBudget.unbounded ()
         val session =
           aesopLib.CS_AESOP_SESSION small config
             forward_clutter_unsafe_cs simpLib.empty_ss goal
         val reference =
           run_session large config
             forward_clutter_unsafe_cs simpLib.empty_ss goal
         fun resume 0 _ _ = NONE
           | resume turns current yielded =
               (case aesopSearch.resume_budget_session current of
                    aesopSearch.ResumedYielded
                      {kind = searchBudget.Candidate,
                       session = next, ...} =>
                        (searchBudget.extend small
                           searchBudget.Candidate 25;
                         resume (turns - 1) next true)
                  | aesopSearch.ResumedFinished
                      (aesopSearch.SearchProved tree) =>
                        SOME (yielded, tree)
                  | _ => NONE)
       in
         case (resume 100 session false, reference) of
             (SOME (true, tree),
              aesopSearch.ResumedFinished
                (aesopSearch.SearchProved _)) =>
               let
                 val used = searchBudget.usage small
                 val repeated =
                   aesopSearch.resume_budget_session session
               in
                 closes_goal (aesopSearch.REPLAY_TAC tree) goal andalso
                 #candidates used =
                 #candidates (searchBudget.usage large) andalso
                 (case repeated of
                      aesopSearch.ResumedFinished
                        (aesopSearch.SearchProved _) =>
                          #candidates (searchBudget.usage small) =
                          #candidates used
                    | _ => false)
               end
           | _ => false
       end)

(* The first pull offers a proof; the second certifies that it is unique.
   Yielding between them must retain the first result in both phases. *)
fun counted_alternative_rule budget phase : aesopRule.rule =
  let
    fun step input =
      let
        val result =
          Option.map #1
            (seq.cases
              ((clasetStep.rule_step
                 {theorem = boolTheory.TRUTH, elim = false,
                  mode = clasetUnify.Match}) input))
        val first = ref true
        fun next () =
          (searchBudget.charge budget searchBudget.Candidate;
           if !first then (first := false; result) else NONE)
      in
        seq.fresult next
      end
  in
    {name = "counted-alternative", phase = phase,
     apply = aesopRule.EngineStep step, once = false}
  end

fun counted_safe_source budget =
  search_source []
    (fn _ => [counted_alternative_rule budget aesopRule.RSafe]) []

fun counted_unsafe_source budget =
  search_source [] (fn _ => [])
    [counted_alternative_rule budget (aesopRule.RUnsafe 50)]

fun counted_resume make_source =
  let
    val goal = ([], boolSyntax.T)
    val tree =
      new_tree clasetMeta.empty
        (tree_cgoal [] [] boolSyntax.T) []
    val config = {max_rapps = 10, max_depth = 10}
    val small =
      searchBudget.create
        {candidates = SOME 1, applications = NONE,
         normalization = NONE}
    val large = searchBudget.unbounded ()
    val session =
      aesopSearch.new_budget_session small config make_source tree
    val reference =
      aesopSearch.resume_budget_session
        (aesopSearch.new_budget_session large config make_source tree)
    val first = aesopSearch.resume_budget_session session
  in
    case (first, reference) of
        (aesopSearch.ResumedYielded
           {kind = searchBudget.Candidate, ...},
         aesopSearch.ResumedFinished
           (aesopSearch.SearchProved _)) =>
          (searchBudget.extend small searchBudget.Candidate 1;
           case aesopSearch.resume_budget_session session of
               aesopSearch.ResumedFinished
                 (aesopSearch.SearchProved proved) =>
                   closes_goal (aesopSearch.REPLAY_TAC proved) goal andalso
                   #candidates (searchBudget.usage small) = 2 andalso
                   #candidates (searchBudget.usage large) = 2
             | _ => false)
      | _ => false
  end

val _ =
  check
    ("safe uniqueness resumes after its first alternative",
     fn () => counted_resume counted_safe_source)

fun registry_replacement_resumes phase =
  let
    val name =
      if phase = aesopRule.RSafe then
        "generation-sensitive-safe"
      else "generation-sensitive-unsafe"
    val p = Term.mk_var ("generation_sensitive_p", Type.bool)
    val target = boolSyntax.mk_imp (p, p)
    val theorem = DISCH p (ASSUME p)
    val goal = ([], target)
    val tree =
      new_tree clasetMeta.empty
        (tree_cgoal [] [] target) []
    val budget =
      searchBudget.create
        {candidates = SOME 1, applications = NONE,
         normalization = NONE}
    val config = {max_rapps = 10, max_depth = 10}
    fun source input =
      let
        val selected =
          List.filter
            (fn (rule : aesopRule.rule) => #name rule = name)
            (aesopRule.registered_tactic_rules ())
      in
        if phase = aesopRule.RSafe then
          search_source [] (fn _ => selected) [] input
        else
          search_source [] (fn _ => []) selected input
      end
    val session =
      aesopSearch.new_budget_session budget config
        (fn _ => source) tree
    fun register tactic =
      aesopRule.register_tactic_rule
        {name = name, phase = phase,
         tactic = tactic, index = NONE}
    val first =
      aesopRule.with_tactic_rules
        (fn () =>
          (register (NTactical.LIFT Tactic.DISCH_TAC);
           aesopSearch.resume_budget_session session)) ()
    val first_usage = searchBudget.usage budget
    val second =
      aesopRule.with_tactic_rules
        (fn () =>
          (register
             (NTactical.LIFT
               (Tactic.ACCEPT_TAC theorem));
           searchBudget.extend budget searchBudget.Candidate 10;
           aesopSearch.resume_budget_session session)) ()
  in
    (case first of
         aesopSearch.ResumedYielded
           {kind = searchBudget.Candidate, ...} =>
             #candidates first_usage = 1
       | _ => false) andalso
    (case second of
         aesopSearch.ResumedFinished
           (aesopSearch.SearchProved proved) =>
             closes_goal (aesopSearch.REPLAY_TAC proved) goal andalso
             #candidates (searchBudget.usage budget) = 3
       | _ => false)
  end

val _ =
  check
    ("a resumed safe scan refreshes a replaced tactic rule",
     fn () => registry_replacement_resumes aesopRule.RSafe)

val _ =
  check
    ("a resumed unsafe scan refreshes a replaced tactic rule",
     fn () => registry_replacement_resumes (aesopRule.RUnsafe 50))

val _ =
  check
    ("unsafe ordinary alternatives resume without a repeated pull",
     fn () => counted_resume counted_unsafe_source)

val _ =
  check
    ("rendered alternatives charge before forcing and resume in place",
     fn () =>
       let
         val calls = ref 0
         val rule : aesopRule.rule =
           {name = "budgeted-rendered", phase = aesopRule.RUnsafe 50,
            apply =
              aesopRule.RenderedTactic
                (NTactical.LIFT
                  (fn goal => fn ctxt =>
                    (calls := !calls + 1;
                     Tactic.ACCEPT_TAC boolTheory.TRUTH goal ctxt))),
            once = false}
         val meter =
           searchBudget.create
             {candidates = SOME 1, applications = NONE,
              normalization = NONE}
         val tree =
           new_tree clasetMeta.empty
             (tree_cgoal [] [] boolSyntax.T) []
         val session =
           aesopSearch.new_budget_session meter
             {max_rapps = 10, max_depth = 10}
             (fn _ => search_source [] (fn _ => []) [rule]) tree
       in
         case aesopSearch.resume_budget_session session of
             aesopSearch.ResumedYielded
               {kind = searchBudget.Candidate, usage, ...} =>
               !calls = 1 andalso #candidates usage = 1 andalso
               (searchBudget.extend meter searchBudget.Candidate 1;
                case aesopSearch.resume_budget_session session of
                    aesopSearch.ResumedFinished
                      (aesopSearch.SearchProved proved) =>
                        !calls = 1 andalso
                        #candidates (searchBudget.usage meter) = 2 andalso
                        closes_goal (aesopSearch.REPLAY_TAC proved)
                          ([], boolSyntax.T)
                  | _ => false)
           | _ => false
       end)

val explicit_context_slot =
  Context.Data.new
    {name = "aesop-selftest-explicit-context", empty = 0,
     pp = Int.toString}

val _ =
  check
    ("CS_AESOP_TAC gives rendered rules its explicit tactic context",
     fn () =>
       let
         val supplied =
           Context.Data.put explicit_context_slot 1
             (Context.snapshot ())
         val seen = ref ([] : int list)
         val goal = ([], boolSyntax.T)
         fun observer target ctxt =
           (seen := Context.Data.get explicit_context_slot ctxt :: !seen;
            Tactical.ALL_TAC target ctxt)
         fun run () =
           (aesopLib.augment_aesop
              {name = "observe-explicit-context",
               phase = aesopRule.RNorm ~100,
               tactic = NTactical.LIFT observer};
            case
              SelfTestTactical.VALID
                (aesopLib.CS_AESOP_TAC aesopLib.default_config
                   clasetLib.empty_cs simpLib.empty_ss)
                goal supplied
            of
                ([], validation) =>
                  (ignore (validation []);
                   not (null (!seen)) andalso
                   List.all (fn value => value = 1) (!seen))
              | _ => false)
       in
         aesopRule.with_tactic_rules run ()
       end)

val _ =
  check
    ("Aesop engine steps retain the supplied context when forced",
     fn () =>
       let
         val ambient = Context.snapshot ()
         val first_context =
           Context.Data.put explicit_context_slot 1 ambient
         val second_context =
           Context.Data.put explicit_context_slot 2 ambient
         val seen = ref ([] : int list)
         val goal = ([boolSyntax.T], boolSyntax.T)
         val node = clasetGoal.from_goal goal
         fun step ctxt input =
           (seen := Context.Data.get explicit_context_slot ctxt :: !seen;
            clasetStep.blast_assumption_step input)
         val rule : aesopRule.rule =
           {name = "contextual-engine", phase = aesopRule.RSafe,
            apply = aesopRule.ContextualStep step, once = false}
         val first = aesopTree.rule_results_in first_context rule node
         val second = aesopTree.rule_results_in second_context rule node
         fun closes sequence =
           case seq.cases sequence of
               SOME (([_], next), _) =>
                 null (clasetGoal.goals next)
             | _ => false
       in
         closes second andalso closes first andalso (!seen = [1, 2])
       end)

val _ =
  check
    ("interleaved budget sessions retain their own tactic contexts",
     fn () =>
       let
         val ambient = Context.snapshot ()
         val first_context =
           Context.Data.put explicit_context_slot 1 ambient
         val second_context =
           Context.Data.put explicit_context_slot 2 ambient
         val seen = ref ([] : int list)
         fun close target ctxt =
           (seen := Context.Data.get explicit_context_slot ctxt :: !seen;
            Tactic.ACCEPT_TAC boolTheory.TRUTH target ctxt)
         val rule : aesopRule.rule =
           {name = "contextual-rendered",
            phase = aesopRule.RUnsafe 50,
            apply = aesopRule.RenderedTactic (NTactical.LIFT close),
            once = false}
         fun source _ =
           search_source [] (fn _ => []) [rule]
         fun one_charge () =
           searchBudget.create
             {candidates = SOME 1, applications = NONE,
              normalization = NONE}
         val first_budget = one_charge ()
         val second_budget = one_charge ()
         val config = {max_rapps = 10, max_depth = 10}
         val tree =
           new_tree clasetMeta.empty
             (tree_cgoal [] [] boolSyntax.T) []
         val first =
           aesopSearch.new_budget_session_in first_context
             first_budget config source tree
         val second =
           aesopSearch.new_budget_session_in second_context
             second_budget config source tree
         fun yielded session =
           case aesopSearch.resume_budget_session session of
               aesopSearch.ResumedYielded
                 {kind = searchBudget.Candidate, ...} => true
             | _ => false
         fun proved session =
           case aesopSearch.resume_budget_session session of
               aesopSearch.ResumedFinished
                 (aesopSearch.SearchProved result) =>
                   closes_goal (aesopSearch.REPLAY_TAC result)
                     ([], boolSyntax.T)
             | _ => false
       in
         yielded first andalso yielded second andalso
         !seen = [2, 1] andalso
         (searchBudget.extend first_budget searchBudget.Candidate 1;
          searchBudget.extend second_budget searchBudget.Candidate 1;
          proved second andalso proved first andalso
          !seen = [2, 1])
       end)

val _ =
  check
    ("budgeted claset assembly charges an ordinary elimination major",
     fn () =>
       let
         val budget =
           searchBudget.create
             {candidates = SOME 0, applications = NONE,
              normalization = NONE}
         val rules =
           aesopRule.claset_rules_with (SOME budget)
             {claset = elim_dest_cs, mode = clasetUnify.Match,
              conclusion = elim_q, assumptions = [elim_p],
              qvars = HOLset.empty Term.compare,
              simpset = simpLib.empty_ss, simp_controls = []}
         val selected =
           List.filter
             (fn ({name, ...} : aesopRule.rule) =>
               name = "safe_elim")
             (aesopRule.safe_rules (#safe rules))
       in
         case selected of
             [{apply = aesopRule.EngineStep step, ...}] =>
               let
                 val cursor =
                   step (clasetGoal.from_goal ([elim_p], elim_q), 1)
                 val stopped =
                   ((ignore (seq.cases cursor); false)
                    handle searchBudget.LimitReached
                      (searchBudget.Candidate, usage) =>
                        #candidates usage = 0)
                 val _ =
                   searchBudget.extend budget searchBudget.Candidate 1
               in
                 stopped andalso
                 Option.isSome (seq.cases cursor) andalso
                 #candidates (searchBudget.usage budget) = 1
               end
           | _ => false
       end)

val _ =
  check
    ("resumable forward scans survive scheduling another goal",
     fn () =>
       let
         val left = Term.mk_var ("forward_split_left", Type.bool)
         val right = Term.mk_var ("forward_split_right", Type.bool)
         val conjunction_intro =
           DISCH left
             (DISCH right
               (CONJ (ASSUME left) (ASSUME right)))
         val split_cs =
           clasetLib.add_rule
             {kind = clasetRules.Intro, safe = true, prio = NONE}
             ("forward-split", conjunction_intro)
             forward_clutter_unsafe_cs
         val (assumptions, first) =
           forward_clutter_goal 201 201
         val predicate = ``forward_clutter_p:'a->bool``
         val next =
           forward_clutter_atom predicate 202
         val second =
           forward_clutter_atom
             ``forward_clutter_q:'a->bool`` 202
         val goal =
           (assumptions @ [next],
            boolSyntax.mk_conj (first, second))
         val config = {max_rapps = 2000, max_depth = 50}
         val small =
           searchBudget.create
             {candidates = SOME 25, applications = NONE,
              normalization = NONE}
         val large = searchBudget.unbounded ()
         val session =
           aesopLib.CS_AESOP_SESSION small config
             split_cs simpLib.empty_ss goal
         val reference =
           run_session large config
             split_cs simpLib.empty_ss goal
         fun resume 0 _ _ = NONE
           | resume turns current yielded =
               (case aesopSearch.resume_budget_session current of
                    aesopSearch.ResumedYielded
                      {kind = searchBudget.Candidate,
                       session = next, ...} =>
                        (searchBudget.extend small
                           searchBudget.Candidate 25;
                         resume (turns - 1) next true)
                  | aesopSearch.ResumedFinished
                      (aesopSearch.SearchProved tree) =>
                        SOME (yielded, tree)
                  | _ => NONE)
       in
         case (resume 200 session false, reference) of
             (SOME (true, tree),
              aesopSearch.ResumedFinished
                (aesopSearch.SearchProved _)) =>
               closes_goal (aesopSearch.REPLAY_TAC tree) goal andalso
               #candidates (searchBudget.usage small) > 200
           | _ => false
       end)

val _ =
  check
    ("budgeted failure charges and caches its safe frontier",
     fn () =>
       let
         val budget = searchBudget.unbounded ()
         val target =
           Term.mk_var ("budget_failure_target", Type.bool)
         val result =
           run_session budget
             aesopLib.default_config clasetLib.empty_cs
             simpLib.empty_ss ([], target)
       in
         case result of
             aesopSearch.ResumedFinished
               (aesopSearch.SearchFailed {safe_goals, ...}) =>
                 let
                   val usage_before = searchBudget.usage budget
                   val frontier = safe_goals ()
                   val usage_after = searchBudget.usage budget
                 in
                   #normalization usage_before > 0 andalso
                   #normalization usage_before =
                     #normalization usage_after andalso
                   (case frontier of
                        [(_, {w, ...})] => aconv w target
                      | _ => false)
                 end
           | _ => false
       end)

(* Every registration in this file is scoped, so nothing a test declared is
   still visible to the goals of any later test. *)
val _ =
  check
    ("aesop selftest registrations leave the session registry empty",
     fn () =>
       surface_registry_before = 0 andalso
       surface_registry_after = surface_registry_before)
