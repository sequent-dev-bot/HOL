structure aesopRule :> aesopRule =
struct

open Abbrev HolKernel

datatype rphase =
    RNorm of int
  | RSafe
  | RUnsafe of int

  datatype rapply =
    EngineStep of clasetStep.step
  | ContextualStep of Context.t -> clasetStep.step
  | RenderedTactic of NTactical.ntactic
  | MultiStep of clasetStep.step list

datatype tactic_index =
    TargetPattern of term
  | HypPattern of term

type rule =
  {name : string, phase : rphase, apply : rapply, once : bool}

type safe_scaffold =
  {closers : rule list,
   safe0_claset : rule list,
   safe_forward : rule list,
   safep_claset : rule list,
   conclusion_splits : rule list,
   assumption_splits : rule list}

type ruleset =
  {norm : rule list, safe : safe_scaffold, unsafe : rule list}

val ERR = mk_HOL_ERR "aesopRule"
val default_percent = 50

fun checked_percent function_name percent =
  if 1 <= percent andalso percent <= 100 then percent
  else
    raise ERR function_name
      "an unsafe rule percentage must be in the range 1--100"

fun phase_of_spec ({kind, safe, prio} : clasetRules.rulespec) =
  if kind = clasetRules.Norm then
    RNorm (Option.getOpt (prio, 0))
  else if safe then
    RSafe
  else
    RUnsafe
      (checked_percent "phase_of_spec"
        (Option.getOpt (prio, default_percent)))

fun apply_rule {name, phase, theorem, mode} : rule =
  {name = name, phase = phase,
   apply =
     EngineStep
       (clasetStep.rule_step
         {theorem = theorem, elim = false, mode = mode}),
   once = false}

fun constructors_rule_with phase function_name
      {name, theorems, mode} : rule =
  if null theorems then
    raise ERR function_name "a constructors rule needs at least one theorem"
  else
    {name = name, phase = phase,
     apply =
       MultiStep
         (map
           (fn theorem =>
             clasetStep.rule_step
               {theorem = theorem, elim = false, mode = mode})
           theorems),
     once = false}

(* Lean's datatype constructors builder has no direct HOL analogue because
   HOL goals are propositions.  Here constructors means the introduction
   rules of an inductive relation. *)
fun constructors_rule {name, theorems, percent, mode} =
  constructors_rule_with
    (RUnsafe
      (checked_percent "constructors_rule"
        (Option.getOpt (percent, default_percent))))
    "constructors_rule"
    {name = name, theorems = theorems, mode = mode}

fun safe_constructors_rule {name, theorems, mode} =
  constructors_rule_with RSafe "safe_constructors_rule"
    {name = name, theorems = theorems, mode = mode}

(* The engine step, charging [budget] when one is given. *)
fun metered_step unmetered _ NONE = unmetered
  | metered_step _ metered (SOME meter) = metered meter

fun forward_rule_with budget immediate
    {name, phase, theorem, mode} : rule =
  {name = name, phase = phase,
   apply =
     EngineStep
       (metered_step clasetStep.forward_rule_step
          clasetStep.forward_rule_step_budgeted budget
          {theorem = theorem, immediate = immediate, mode = mode}),
   once = true}

fun forward_rule {name, phase, theorem, immediate, mode} =
  forward_rule_with NONE (SOME immediate)
    {name = name, phase = phase, theorem = theorem, mode = mode}

(* The step canonicalizes the theorem once for all of its applications and
   takes every premise of that canonical rule when asked for NONE, so the
   all-immediate default costs no canonicalization here. *)
val default_forward_rule = forward_rule_with NONE NONE

fun forward_duplicate store previous candidate =
  let
    val candidate' = clasetMeta.instantiate store candidate
  in
    List.exists
      (fn earlier =>
        aconv (clasetMeta.instantiate store earlier) candidate')
      previous
  end

fun pattern_matches patterns store assumptions =
  null patterns orelse
  List.exists
    (fn pattern =>
      List.exists
        (fn assumption =>
          can (Term.match_term pattern)
            (clasetMeta.instantiate store assumption))
        assumptions)
    patterns

fun gated_engine_step patterns step (node, pos) =
  let
    val {asl, ...} = clasetGoal.goal_at node pos
  in
    if pattern_matches patterns (clasetGoal.store node) asl then
      step (node, pos)
    else
      seq.empty
  end

fun cases_rule {name, phase, theorem, patterns, mode} : rule =
  {name = name, phase = phase,
   apply =
     EngineStep
       (gated_engine_step patterns
         (clasetStep.rule_step
           {theorem = theorem, elim = true, mode = mode})),
   once = false}

fun goal_matches_index NONE _ = true
  | goal_matches_index (SOME (TargetPattern pattern)) (_, target) =
      can (Term.match_term pattern) target
  | goal_matches_index (SOME (HypPattern pattern)) (assumptions, _) =
      List.exists (can (Term.match_term pattern)) assumptions

fun indexed_changed index tactic goal ctxt =
  if goal_matches_index index goal then
    NTactical.NCHANGED tactic goal ctxt
  else
    seq.empty

(* Rendering exposes engine metavariables as rigid marked frees.  Keeping
   tactic rules in this representation makes their inability to create or
   assign engine metavariables structural rather than a run-time convention. *)
fun tactic_rule {name, phase, tactic, index} : rule =
  {name = name, phase = phase,
   apply = RenderedTactic (indexed_changed index tactic),
   once = false}

type tactic_registry_state =
  {rules : (rule * tactic_index option) list,
   generation : int}

val tactic_registry =
  Sref.new
    ({rules = [], generation = 0} : tactic_registry_state)

fun registry_generation () =
  #generation (Sref.value tactic_registry)

fun register_tactic_rule
      (registration as {index, ...}) =
  Sref.update tactic_registry
    (fn {rules, generation} =>
      {rules = rules @ [(tactic_rule registration, index)],
       generation = generation + 1})

(* Registration is session-global and additive, which is what a library
   augmenting the engine wants.  A caller whose registrations belong to a
   bounded scope -- a tactic installing a rule for one invocation, a test
   exercising one -- runs them inside this combinator instead, which
   restores the registry afterwards whether [f] returns or raises. *)
fun with_tactic_rules f x =
  let
    val saved = #rules (Sref.value tactic_registry)
    fun restore () =
      Sref.update tactic_registry
        (fn {generation, ...} =>
          {rules = saved, generation = generation + 1})
    val result = f x handle e => (restore (); raise e)
  in
    restore (); result
  end

fun registered_tactic_rules () =
  map #1 (#rules (Sref.value tactic_registry))

fun applicable_tactic_rules conclusion assumptions =
  map #1
    (List.filter
      (fn (_, index) =>
        goal_matches_index index (assumptions, conclusion))
      (#rules (Sref.value tactic_registry)))

fun norm_phase_rule ({phase, ...} : rule) =
  case phase of RNorm _ => true | _ => false

fun safe_phase_rule ({phase, ...} : rule) =
  phase = RSafe

fun unsafe_phase_rule ({phase, ...} : rule) =
  case phase of RUnsafe _ => true | _ => false

fun type_candidate ty variable =
  can (Type.match_type ty) (type_of variable)

fun cases_rule_for ty =
  let
    val nchotomy = TypeBase.nchotomy_of ty

    fun cases_tac (assumptions, target) =
      let
        val candidates =
          List.filter (type_candidate ty)
            (free_varsl (target :: assumptions))
        val variable =
          case candidates of
              candidate :: _ => candidate
            | [] =>
                raise ERR "cases_rule_for"
                  "the goal has no free variable of the requested type"
      in
        Tactic.STRUCT_CASES_TAC (Drule.ISPEC variable nchotomy)
          (assumptions, target)
      end
  in
    tactic_rule
      {name = "cases " ^ Parse.type_to_string ty,
       phase = RUnsafe default_percent,
       tactic = NTactical.LIFT cases_tac, index = NONE}
  end

fun split_rule_pair {name, theorem} =
  let
    val (conclusion_theorem, assumption_theorem) =
      if splitLib.is_asm_split theorem then
        (splitLib.mk_asm_split theorem, theorem)
      else
        (theorem, splitLib.mk_asm_split theorem)
    val conclusion =
      tactic_rule
        {name = name ^ " (conclusion split)", phase = RSafe,
         tactic =
           NTactical.LIFT
             (Tactic.CONV_TAC
               (splitLib.SPLIT_CONV [conclusion_theorem])),
         index = NONE}
    val assumption =
      tactic_rule
        {name = name ^ " (assumption split)", phase = RSafe,
         tactic =
           NTactical.LIFT
             (splitLib.SPLIT_ASM_TAC [assumption_theorem]),
         index = NONE}
  in
    {conclusion = conclusion, assumption = assumption}
  end

type split_ruleset =
  {conclusion : rule list, assumption : rule list}

val split_cache =
  Sref.new
    (NONE :
      {source : (string * thm) list, rules : split_ruleset} option)

fun same_split_source left right =
  ListPair.allEq
    (fn ((name1, theorem1), (name2, theorem2)) =>
      name1 = name2 andalso aconv (concl theorem1) (concl theorem2))
    (left, right)

(* Each pair derives its assumption-split theorem, so rebuilding these on
   every rule-set assembly would repeat that derivation for every declared
   split theorem at every goal.  The registered theorems change rarely, so
   cache the built rules against them. *)
fun split_rules () : split_ruleset =
  let
    val source = splitLib.named_split_thms ()
    fun build () =
      let
        val pairs =
          map
            (fn (name, theorem) =>
              split_rule_pair {name = name, theorem = theorem})
            source
        val rules =
          {conclusion = map #conclusion pairs,
           assumption = map #assumption pairs}
      in
        Sref.update split_cache
          (fn _ => SOME {source = source, rules = rules});
        rules
      end
  in
    case Sref.value split_cache of
        SOME {source = cached, rules} =>
          if same_split_source cached source then rules else build ()
      | NONE => build ()
  end

fun is_no_asms theorem =
  case markerLib.dest_directive (markerLib.strip_wrappers theorem) of
      SOME markerLib.DNoAsms => true
    | _ => false

fun simp_rule_with {name, simpset, controls} : rule =
  let
    (* GEN_GLOBAL_SIMP_TAC deliberately traverses assumptions.  NoAsms
       therefore selects its safe conclusion-only counterpart. *)
    val tactic =
      if List.exists is_no_asms controls then
        simpLib.GEN_SIMP_TAC {safe = true} simpset controls
      else
        clasimpLib.safe_asm_full_simp simpset controls
  in
    {name = name, phase = RNorm 0,
     apply = RenderedTactic (NTactical.LIFT tactic),
     once = false}
  end

fun simp_rule arguments =
  let
    val {simp_rules, simp_controls, ...} =
      clasetLib.classify_simp_args arguments
    val invocation_ss =
      simpLib.++
        (aesopData.aesop_ss (), simpLib.rewrites simp_rules)
  in
    simp_rule_with
      {name = "simp", simpset = invocation_ss,
       controls = simp_controls}
  end

fun norm_builtins_with simp : rule list =
  [{name = "disch", phase = RNorm 0,
    apply = ContextualStep clasetStep.blast_disch_step_in,
    once = false},
   {name = "gen", phase = RNorm 0,
    apply = ContextualStep clasetStep.blast_gen_step_in,
    once = false},
   {name = "hyp-subst", phase = RNorm 0,
    apply = ContextualStep clasetStep.blast_hyp_subst_step_in,
    once = false},
   simp]

fun norm_builtins simp_args = norm_builtins_with (simp_rule simp_args)

fun closers () : rule list =
  [{name = "assumption", phase = RSafe,
    apply = EngineStep clasetStep.blast_assumption_step,
    once = false},
   {name = "contradiction", phase = RSafe,
    apply = EngineStep clasetStep.blast_contradiction_step,
    once = false}]

fun safe_rules
      ({closers, safe0_claset, safe_forward, safep_claset,
        conclusion_splits, assumption_splits} : safe_scaffold) =
  closers @ safe0_claset @ safe_forward @ safep_claset @
  conclusion_splits @ assumption_splits

type candidate = clasetLib.aesop_rule

(* Retrieval may offer one declaration through several index entries.  Keep
   the first occurrence of each name, in retrieval order. *)
fun unique_declarations declarations =
  listUtil.distinct_by String.compare (#name : candidate -> string)
    declarations

(* Assembling a rule set inspects a retrieved declaration more than once:
   once per safe-class filter, and once more when its rule is built.  Each
   inspection wants the declaration's classical rule forms, which cost real
   kernel derivations -- CLASSICAL_RULE, MAKE_ELIM_RULE, DUP_ELIM_RULE,
   SWAP_INTRO_RULE.  The claset derived them once when the rule was
   declared and hands them back with the candidate, so no goal expansion
   derives them again. *)
fun candidate_declarations budget claset conclusion assumptions qvars =
  let
    val checkpoint =
      case budget of
          NONE => listUtil.no_checkpoint
        | SOME meter =>
            fn () => searchBudget.charge meter searchBudget.Candidate
    val target =
      clasetLib.aesop_target_rules claset
        {q = conclusion, qvars = qvars}
    fun hypothesis assumption =
      clasetLib.aesop_hyp_rules_measured checkpoint claset
        {q = assumption, qvars = qvars}
  in
    unique_declarations
      (target @ List.concat (map hypothesis assumptions))
  end

fun ordinary_kind clasetRules.Intro = true
  | ordinary_kind clasetRules.Elim = true
  | ordinary_kind clasetRules.Dest = true
  | ordinary_kind _ = false

fun canonical_source ({info, ...} : candidate) = #1 (#rl info)

fun declaration_rule budget mode
      (candidate as {spec, name, thm, ...} : candidate) : rule =
  let
    val kind = #kind spec
    val elim =
      kind = clasetRules.Elim orelse kind = clasetRules.Dest
  in
    if kind = clasetRules.Forward then
      forward_rule_with budget NONE
        {name = name, phase = phase_of_spec spec,
         theorem = thm, mode = mode}
    else
      let val source = canonical_source candidate
      in
        {name = name, phase = phase_of_spec spec,
         apply =
           EngineStep
             (metered_step clasetStep.rule_step
                clasetStep.rule_step_budgeted budget
                {theorem = source, elim = elim, mode = mode}),
         once = false}
      end
  end

fun safe_class wanted ({spec, info, ...} : candidate) =
  #safe spec andalso
  ordinary_kind (#kind spec) andalso
  clasetRules.safe_class_of spec info = SOME wanted

fun unsafe_declaration ({spec, ...} : candidate) =
  (ordinary_kind (#kind spec) orelse
   #kind spec = clasetRules.Forward) andalso
  not (#safe spec)

fun safe_forward_declaration ({spec, ...} : candidate) =
  #kind spec = clasetRules.Forward andalso #safe spec

fun unsafe_percent ({phase, ...} : rule) =
  case phase of
      RUnsafe percent => percent
    | _ => raise ERR "unsafe_percent" "a safe rule reached unsafe ordering"

(* Claset candidates and registered tactic rules share one ordering, so a
   rule's declared success percentage alone decides when it is tried.  The
   sort is stable and the tactic rules follow the claset candidates in its
   input, so equal percentages keep claset candidates -- which arrive in
   the claset's own candidate order -- ahead of tactic rules. *)
fun order_unsafe rules =
  let
    val positioned = Lib.enumerate 0 rules
    fun compare ((left_index, left), (right_index, right)) =
      case Int.compare
             (unsafe_percent right, unsafe_percent left) of
          EQUAL => Int.compare (left_index, right_index)
        | order => order
  in
    map #2 (Listsort.sort compare positioned)
  end

fun claset_rules_core
      {claset, mode, conclusion, assumptions, qvars, simp, budget} =
  let
    val candidates =
      candidate_declarations budget claset conclusion assumptions qvars
    val safe0 =
      map (declaration_rule budget mode)
        (List.filter (safe_class clasetRules.Safe0) candidates)
    val safep =
      map (declaration_rule budget mode)
        (List.filter (safe_class clasetRules.SafeP) candidates)
    val forwards =
      map (declaration_rule budget mode)
        (List.filter safe_forward_declaration candidates)
    val unsafe_claset =
      map (declaration_rule budget mode)
        (List.filter unsafe_declaration candidates)
    val norm_declarations =
      map (declaration_rule budget clasetUnify.Match)
        (clasetLib.norm_rules claset)
    val splits = split_rules ()
    val tactics =
      applicable_tactic_rules conclusion assumptions
    val norm_tactics =
      List.filter norm_phase_rule (registered_tactic_rules ())
    val safe_tactics =
      List.filter safe_phase_rule tactics
    val unsafe_tactics =
      List.filter unsafe_phase_rule tactics
    val safe =
      {closers = closers (),
       safe0_claset = safe0,
       safe_forward = forwards,
       safep_claset = safep,
       conclusion_splits = #conclusion splits,
       assumption_splits = #assumption splits @ safe_tactics}
  in
    {norm = norm_builtins_with simp @ norm_declarations @ norm_tactics,
     safe = safe,
     unsafe = order_unsafe (unsafe_claset @ unsafe_tactics)}
  end

fun claset_rules
      {claset, mode, conclusion, assumptions, qvars, simp_args} =
  claset_rules_core
    {claset = claset, mode = mode, conclusion = conclusion,
     assumptions = assumptions, qvars = qvars,
     simp = simp_rule simp_args, budget = NONE}

fun claset_rules_with budget
      {claset, mode, conclusion, assumptions, qvars,
       simpset, simp_controls} =
  claset_rules_core
    {claset = claset, mode = mode, conclusion = conclusion,
     assumptions = assumptions, qvars = qvars,
     simp =
       simp_rule_with
         {name = "simp", simpset = simpset,
          controls = simp_controls},
     budget = budget}

end
