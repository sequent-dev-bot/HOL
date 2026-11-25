structure aesopLib :> aesopLib =
struct

open Abbrev HolKernel

type aesop_config = aesopSearch.aesop_config
type rphase = aesopRule.rphase
type rule = aesopRule.rule

val default_config = aesopSearch.default_config
val ERR = mk_HOL_ERR "aesopLib"

fun check_config function_name
      ({max_rapps, max_depth} : aesop_config) =
  if max_rapps < 0 then
    raise ERR function_name "max_rapps must not be negative"
  else if max_depth < 0 then
    raise ERR function_name "max_depth must not be negative"
  else
    ()

fun qvars_of store ({asl, w, ...} : clasetGoal.cgoal) =
  let
    fun add (term, seen) =
      HOLset.addList (seen, clasetMeta.metas_of store term)
  in
    if clasetMeta.has_term_metas store then
      List.foldl add (add (w, Term.empty_tmset)) asl
    else Term.empty_tmset
  end

fun rule_source ctxt budget claset simpset simp_controls
      ({mode, cgoal = cgoal as {asl, w, ...}, store} :
       {mode : clasetUnify.mode, cgoal : clasetGoal.cgoal,
        store : clasetMeta.store}) =
  aesopRule.claset_rules_with budget
    {ctxt = ctxt, claset = claset, mode = mode, conclusion = w,
     assumptions = asl, qvars = qvars_of store cgoal,
     simpset = simpset, simp_controls = simp_controls}

fun initial_tree goal =
  aesopTree.create
    {node = clasetGoal.from_goal goal, unsafe_cursor = []}

fun CS_AESOP_SESSION budget config claset simpset goal =
  let
    val _ = check_config "CS_AESOP_SESSION" config
    val ctxt = Context.snapshot ()
  in
    aesopSearch.new_budget_session_in ctxt budget config
      (fn owned => rule_source ctxt (SOME owned) claset simpset [])
      (initial_tree goal)
  end

fun close_raw function_name config claset simpset simp_controls goal ctxt =
  let
    val _ = check_config function_name config
    val source = rule_source ctxt NONE claset simpset simp_controls
  in
    case aesopSearch.search_in ctxt config source
           (initial_tree goal) of
        aesopSearch.SearchProved tree =>
          aesopSearch.REPLAY_TAC tree goal ctxt
      | aesopSearch.SearchFailed _ => Tactical.NO_TAC goal ctxt
  end

fun singleton_replay store record =
  clasetReplay.REPLAY_TAC
    (clasetReplay.ground store
      (clasetReplay.append (clasetReplay.empty 1) record))

fun replay_records store records =
  Tactical.EVERY (map (singleton_replay store) records)

(* Safe search starts from a kernel goal without engine metavariables.
   Match-mode rules therefore produce a deterministic proof tree whose open
   leaves are genuine HOL goals.  Replay each local single-goal script and
   compose its child validations positionally. *)
fun safe_replay tree =
  let
    fun replay_goal id =
      let
        val goal = aesopTree.goal tree id
        val (norm_records, norm_store, norm_proved) =
          case #norm goal of
              aesopTree.Unnormalised =>
                ([], aesopTree.active_store goal, false)
            | aesopTree.Normalised {records, store, ...} =>
                (records, store, false)
            | aesopTree.NormProved {records, store} =>
                (records, store, true)
        val norm_tactic = replay_records norm_store norm_records
      in
        if norm_proved then
          norm_tactic
        else
          case aesopTree.child_rapps tree id of
              [] => norm_tactic
            | [rid] =>
                let
                  val rapp = aesopTree.rapp tree rid
                  val children = aesopTree.direct_children tree rid
                  val application =
                    replay_records (#store rapp) (#records rapp)
                  val descendants =
                    Tactical.THENL
                      (application, map replay_goal children)
                in
                  Tactical.THEN (norm_tactic, descendants)
                end
            | _ =>
                raise ERR "safe_replay"
                  "safe search committed more than one rule application"
      end
  in
    replay_goal (aesopTree.root tree)
  end

fun safe_raw function_name config claset simpset simp_controls goal ctxt =
  let
    val _ = check_config function_name config
    val source = rule_source ctxt NONE claset simpset simp_controls
    val tree = initial_tree goal
  in
    case
      aesopSearch.safe_saturate_in ctxt
        {max_depth = #max_depth config, rules = source} tree
    of
        aesopSearch.SafeSaturated saturated =>
          safe_replay saturated goal ctxt
      | aesopSearch.SafeDepthLimit _ => Tactical.NO_TAC goal ctxt
      | aesopSearch.SafeNormalisationLimit _ => Tactical.NO_TAC goal ctxt
  end

fun changed tactic =
  NTactical.DETERM
    (NTactical.NCHANGED (NTactical.LIFT tactic))

fun aesop_marker theorem =
  case clasetLib.marker_of theorem of
      SOME {name="Norm",spec=SOME spec,
            payload=clasetLib.Theorem rule} => SOME (spec,rule)
    | SOME {name="Forward",spec=SOME spec,
            payload=clasetLib.Theorem rule} => SOME (spec,rule)
    | SOME {name="SForward",spec=SOME spec,
            payload=clasetLib.Theorem rule} => SOME (spec,rule)
    | _ => NONE

fun process_aesop_markers theorems claset =
  let
    fun process _ current rest [] = (current, List.rev rest)
      | process index current rest (theorem :: remaining) =
          case aesop_marker theorem of
              NONE =>
                process index current (theorem :: rest) remaining
            | SOME (spec, rule) =>
                let
                  val name =
                    clasetLib.fresh_rule_name
                      {prefix = "__aesop_marker_", from = index} current
                  val current' =
                    clasetLib.add_rule spec (name, rule) current
                in
                  process (index + 1) current' rest remaining
                end
  in
    process 0 claset [] theorems
  end

fun process_args_with consumer
      body base_claset base_simpset =
  clasetLib.with_invocation_fact_env
    {iff_prefix="__aesop_iff_arg_",
     extra_markers=process_aesop_markers,
     consumer=consumer}
    (fn cs => fn simpset => fn controls => fn environment =>
      case simpset of
          SOME ss =>
            let
              (* Aesop's normalizer rewrites assumptions as well as the
                 target.  Propositional facts must remain there for safe
                 and forward rules; only equational views belong in this
                 phase. *)
              val views =
                map #theorem
                  (clasetFacts.equational_views environment)
            in
              body cs ss (controls @ views)
            end
        | NONE =>
            raise ERR "process_args" "simpset was not installed")
    base_claset
    (SOME {base=base_simpset, extend=clasimpLib.extend_invocation})

fun process_args body =
  process_args_with clasetLib.SearchFacts body
fun process_safe_args body =
  process_args_with clasetLib.SafeFacts body

fun CS_AESOP_TAC config claset simpset =
  close_raw "CS_AESOP_TAC" config claset simpset []

fun CS_AESOP_SAFE_TAC config claset simpset =
  changed (safe_raw "CS_AESOP_SAFE_TAC" config claset simpset [])

(* The invocation context is read inside the goal abstraction, as
   clasimpLib's entry points read theirs.  A tactic value bound before a
   declaration -- [val TAC = AESOP_TAC []] at the head of a script -- must
   still use the claset and the aesop simpset current where it is applied,
   not the ones current where it was bound. *)
fun AESOP_TAC theorems goal ctxt =
  process_args
      (close_raw "AESOP_TAC" default_config)
      (clasetLib.the_claset_of ctxt)
      (aesopData.aesop_ss_of ctxt)
      theorems
    goal ctxt

fun AESOP_SAFE_TAC theorems goal ctxt =
  changed
      (process_safe_args
        (safe_raw "AESOP_SAFE_TAC" default_config)
        (clasetLib.the_claset_of ctxt)
        (aesopData.aesop_ss_of ctxt)
        theorems) goal ctxt

fun augment_aesop {name, phase, tactic} =
  aesopRule.register_tactic_rule
    {name = name, phase = phase, tactic = tactic, index = NONE}

(* The registry holds tactic rules, so a prebuilt rule can enter it exactly
   when its action is a rendered tactic; the theorem-derived engine steps
   would need a rule-taking entry point of aesopRule's own.  A prebuilt
   rule already carries its retrieval index inside that tactic, so the
   registry entry adds none: an index here would only repeat the test the
   rule performs on itself. *)
fun augment_aesop_rule ({name, phase, apply, once} : rule) =
  case apply of
      aesopRule.RenderedTactic tactic =>
        if once then
          raise ERR "augment_aesop_rule"
            "a once-only rule cannot be registered as a tactic rule"
        else
          aesopRule.register_tactic_rule
            {name = name, phase = phase, tactic = tactic,
             index = NONE}
    | _ =>
        raise ERR "augment_aesop_rule"
          "only a rule whose action is a tactic can be registered"

val cases_rule_for = aesopRule.cases_rule_for

end
