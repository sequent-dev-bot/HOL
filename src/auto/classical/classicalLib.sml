structure classicalLib :> classicalLib =
struct

open Abbrev HolKernel

type run_state =
  {node : clasetGoal.node,
   validation : validation}

fun rendered_goals node =
  let
    fun render _ [] = []
      | render pos (_ :: rest) =
          clasetGoal.render node pos :: render (pos + 1) rest
  in
    render 1 (clasetGoal.goals node)
  end

fun initial_validation [theorem] = theorem
  | initial_validation _ =
      raise mk_HOL_ERR "classicalLib" "initial_validation"
        "validation expected one theorem"

(* [clasetGoal.from_goal] reduces the caller's goal on the way in, and the
   engine's own validations therefore prove the reduced goal.  The caller
   posed the goal as written and has to be given a proof of that, so the
   crossing is run backwards here.  A driver that replays its record
   against the caller's goal reconstructs the spelling for itself and does
   not come through this. *)
fun caller_result goal (goals, validation) =
  (goals, fn theorems => clasetNorm.align_goal goal (validation theorems))

fun replace_validation old_count pos child_count step_validation
    old_validation theorem_list =
  if length theorem_list <> old_count - 1 + child_count then
    raise mk_HOL_ERR "classicalLib" "replace_validation"
      "validation received the wrong number of theorems"
  else
    let
      val prefix = List.take (theorem_list, pos - 1)
      val after_prefix = List.drop (theorem_list, pos - 1)
      val children = List.take (after_prefix, child_count)
      val suffix = List.drop (after_prefix, child_count)
      val parent = step_validation children
    in
      old_validation (prefix @ (parent :: suffix))
    end

fun accept_safe_transition
      ((pos, record, next), {node, validation} : run_state) =
  let
    val old_count = clasetGoal.goal_count node
    val child_count = clasetGoal.child_count node next
    val validation' =
      replace_validation old_count pos child_count
        (clasetStep.validation_of record) validation
  in
    {node=next, validation=validation'}
  end

fun safe_saturate cs goal ctxt =
  let
    val initial =
      {node = clasetGoal.from_goal goal,
       validation = initial_validation}
    val final =
      clasetStep.fold_safe_saturation (fn _ => ()) ctxt cs (#node initial)
        accept_safe_transition initial
    val goals = rendered_goals (#node final)
  in
    if boolSyntax.goals_eq goals [goal] then seq.empty
    else seq.result (caller_result goal (goals, #validation final))
  end

fun step_ntactic step cs goal ctxt =
  let
    val node = clasetGoal.from_goal goal
  in
    seq.map
      (fn (record, next) =>
        caller_result goal
          (rendered_goals next, clasetStep.validation_of record))
      (step ctxt cs (node, 1))
  end

fun CS_SAFE_STEP_TAC cs = step_ntactic clasetStep.safe_step_in cs
fun CS_CLARIFY_STEP_TAC cs = step_ntactic clasetStep.clarify_step_in cs
fun CS_SAFE_TAC cs = safe_saturate cs

fun CS_CLARIFY_TAC cs =
  NTactical.NCHANGED
    (NTactical.NREPEAT (CS_CLARIFY_STEP_TAC cs))

(* The searches report at the classical.trace level of the tactic's
   context, read once when the tactic is run. *)
fun classical_level ctxt = traceUtil.level_of clasetReplay.tracer ctxt

fun replay_node original node ctxt =
  let
    val grounded =
      clasetReplay.ground (clasetGoal.store node)
        (clasetGoal.replay node)
  in
    seq.result (clasetReplay.REPLAY_TAC grounded original ctxt)
  end
  handle HOL_ERR error =>
    let
      val _ = traceUtil.trace (classical_level ctxt) 1
        (fn () =>
          "kernel replay failed for an engine solution; backtracking: " ^
          Feedback.message_of error)
    in
      seq.empty
    end

fun replay_step step cs goal ctxt =
  let val initial = clasetGoal.from_goal goal
  in
    seq.bind (step ctxt cs (initial, 1))
      (fn (_, node) => replay_node goal node ctxt)
  end

fun CS_STEP_TAC cs = replay_step clasetStep.step_in cs
fun CS_SLOW_STEP_TAC cs = replay_step clasetStep.slow_step_in cs
fun CS_INST_STEP_TAC cs = replay_step clasetStep.inst_step_in cs

fun project_steps steps =
  seq.map (fn (_, node) => node) steps

fun expand_at step cs pos node =
  project_steps (step cs (node, pos))

(* The first goal that does not stand on an unknown, and the first goal
   when they all do.  A goal whose conclusion still carries an unknown
   is closed only by a step that guesses it, because nothing in the
   conclusion constrains the guess, while a sibling's proof may settle
   it outright; taking such a goal first is what makes a rule whose
   conclusion carries an unknown its premises do not fix unusable at any
   bound.  Exactly one goal is expanded either way, so a state whose
   goals all stand settled is expanded as it was before. *)
fun expand_settled_first step cs node =
  let
    val count = clasetGoal.goal_count node
    fun choose pos =
      if pos > count then 1
      else if clasetGoal.stands_on_unknown node pos then choose (pos + 1)
      else pos
  in
    if count = 0 then seq.empty else expand_at step cs (choose 1) node
  end

fun expand_first step cs node =
  let
    fun first _ [] = seq.empty
      | first pos (_ :: goals) =
          seq.delay
            (fn () =>
              case seq.cases (expand_at step cs pos node) of
                  NONE => first (pos + 1) goals
                | SOME (result, rest) => seq.cons result rest)
  in
    first 1 (clasetGoal.goals node)
  end

(* Isabelle's safe_depth_tac saturates the complete selected state before
   depth search.  Keeping the resulting goals visible to DEPTH_SOLVE also
   lets its D25 commitment test run between safely generated siblings. *)
fun safe_saturate_node_in_with charge ctxt cs initial =
  clasetStep.fold_safe_saturation charge ctxt cs initial
    (fn ((_, _, next), _) => next) initial

fun safe_saturate_node_in ctxt cs initial =
  safe_saturate_node_in_with (fn _ => ()) ctxt cs initial

fun solved node = List.null (clasetGoal.goals node)

fun solve search goal ctxt =
  let val initial = clasetGoal.from_goal goal
  in
    seq.bind (search initial)
      (fn node =>
        if solved node then replay_node goal node ctxt else seq.empty)
  end

fun depth_driver step ctxt cs =
  clasetSearch.DEPTH_SOLVE (classical_level ctxt)
    (expand_settled_first (step ctxt) cs)

fun best_driver step ctxt cs =
  clasetSearch.BEST_FIRST (classical_level ctxt) solved
    (expand_at (step ctxt) cs 1)

fun astar_driver step ctxt cs =
  clasetSearch.ASTAR (classical_level ctxt) solved
    (expand_at (step ctxt) cs 1)

fun CS_FAST_TAC cs goal ctxt =
  solve (depth_driver clasetStep.step_in ctxt cs) goal ctxt
fun CS_SLOW_TAC cs goal ctxt =
  solve (depth_driver clasetStep.slow_step_in ctxt cs) goal ctxt
fun CS_BEST_TAC cs goal ctxt =
  solve (best_driver clasetStep.step_in ctxt cs) goal ctxt
fun CS_SLOW_BEST_TAC cs goal ctxt =
  solve (best_driver clasetStep.slow_step_in ctxt cs) goal ctxt

fun first_best search cs goal ctxt =
  solve
    (search (classical_level ctxt) solved
       (expand_first (clasetStep.step_in ctxt) cs))
    goal ctxt

fun CS_FIRST_BEST_TAC cs = first_best clasetSearch.BEST_FIRST cs

(* A bounded turn for the frontier search, keeping its first solution.  A
   search that reaches the bound reports no solution, which is failure, so
   a caller can offer the goal to another engine. *)
fun CS_BOUNDED_FIRST_BEST_TAC cs expansions goal ctxt =
  if expansions >= 1 then
    NTactical.DETERM
      (first_best (clasetSearch.BOUNDED_BEST_FIRST expansions) cs)
      goal ctxt
  else
    (* The search reads a limit of zero as no limit, so a turn of none
       would be the unbounded search rather than the empty one. *)
    raise mk_HOL_ERR "classicalLib" "CS_BOUNDED_FIRST_BEST_TAC"
      "a turn is at least one expansion"

type budget_session =
  {frontier : clasetSearch.frontier_session,
   budget : searchBudget.budget,
   goal : goal,
   ctxt : Context.t,
   pending : clasetGoal.node option ref,
   terminal : (searchBudget.kind * searchBudget.usage) option ref,
   aborted : bool ref}

datatype budget_outcome =
    BudgetProved of
      {result : goal list * validation, session : budget_session}
  | BudgetExhausted
  | BudgetYielded of
      {kind : searchBudget.kind, usage : searchBudget.usage,
       session : budget_session}
  | BudgetLimitReached of
      {kind : searchBudget.kind, usage : searchBudget.usage}

fun CS_FIRST_BEST_SESSION budget cs goal ctxt : budget_session =
  {frontier =
     clasetSearch.new_best_session (classical_level ctxt) budget solved
       (expand_first
          (clasetStep.step_in_with
             (fn () => searchBudget.charge budget searchBudget.Candidate)
             ctxt) cs)
       (clasetGoal.from_goal goal),
   budget = budget, goal = goal, ctxt = ctxt, pending = ref NONE,
   terminal = ref NONE, aborted = ref false}

fun RESUME_FIRST_BEST_SESSION
      (session as
        {frontier, budget, goal, ctxt, pending, terminal, aborted} :
        budget_session) =
  let
    fun replay node =
      let
        val admitted =
          (searchBudget.charge budget searchBudget.Normalization; NONE)
          handle searchBudget.LimitReached (kind, usage) =>
            SOME (kind, usage)
      in
        case admitted of
            SOME (kind, usage) =>
              BudgetYielded
                {kind = kind, usage = usage, session = session}
          | NONE =>
              let
                val _ = pending := NONE
                val grounded =
                  clasetReplay.ground
                    (clasetGoal.store node)
                    (clasetGoal.replay node)
                val result =
                  Tactical.VALID
                    (clasetReplay.REPLAY_TAC grounded) goal ctxt
              in
                if null (#1 result) then
                  BudgetProved
                    {result = result, session = session}
                else advance ()
              end
              handle HOL_ERR _ => advance ()
                   | searchBudget.LimitReached (kind, usage) =>
                       (terminal := SOME (kind, usage);
                        BudgetLimitReached
                          {kind = kind, usage = usage})
      end
    and advance () =
      case !pending of
          SOME node => replay node
        | NONE =>
            (case clasetSearch.resume_frontier frontier of
                 clasetSearch.FrontierResult {node, ...} =>
                   (pending := SOME node; replay node)
               | clasetSearch.FrontierExhausted => BudgetExhausted
               | clasetSearch.FrontierYielded {kind, usage, ...} =>
                   BudgetYielded
                     {kind = kind, usage = usage, session = session}
               | clasetSearch.FrontierLimitReached {kind, usage} =>
                   (terminal := SOME (kind, usage);
                    BudgetLimitReached
                      {kind = kind, usage = usage}))
  in
    if !aborted then
      raise mk_HOL_ERR "classicalLib" "RESUME_FIRST_BEST_SESSION"
        "an interrupted or failed session cannot be resumed"
    else
      case !terminal of
          SOME (kind, usage) =>
            BudgetLimitReached {kind = kind, usage = usage}
        | NONE =>
            (advance ()
             handle exn => (aborted := true; raise exn))
  end

fun CS_ASTAR_TAC cs goal ctxt =
  solve (astar_driver clasetStep.step_in ctxt cs) goal ctxt
fun CS_SLOW_ASTAR_TAC cs goal ctxt =
  solve (astar_driver clasetStep.slow_step_in ctxt cs) goal ctxt

fun bounded_depth_in_with charge ctxt {dup} cs bound initial =
  let
    val part =
      if dup then clasetLib.dup_part cs else clasetLib.unsafe_part cs
    val saturated =
      safe_saturate_node_in_with charge ctxt cs initial
    val search =
      clasetSearch.DEPTH_SOLVE (classical_level ctxt)
        (fn node =>
          (charge searchBudget.Application;
           seq.map
             (fn child =>
               (charge searchBudget.Candidate; child))
             (project_steps
                (clasetStep.depth_step_in_with
                   (fn () => charge searchBudget.Candidate)
                   ctxt cs part bound (node, 1)))))
  in
    search saturated
  end

fun bounded_depth_in ctxt config cs bound initial =
  bounded_depth_in_with (fn _ => ()) ctxt config cs bound initial

fun CS_DEPTH_SOLVE_TAC config bound cs goal ctxt =
  solve (bounded_depth_in ctxt config cs bound) goal ctxt

fun CS_DEPTH_SOLVE_TAC_BUDGETED budget config bound cs =
  NTactical.DETERM
    (fn goal => fn ctxt =>
      solve
        (bounded_depth_in_with (searchBudget.charge budget)
           ctxt config cs bound)
        goal ctxt)

type depth_session =
  {cursor : clasetGoal.node seq.seq ref,
   pending : (clasetGoal.node * clasetGoal.node seq.seq) option ref,
   budget : searchBudget.budget,
   goal : goal,
   ctxt : Context.t,
   aborted : bool ref}

datatype depth_outcome =
    DepthProved of
      {result : goal list * validation, session : depth_session}
  | DepthExhausted
  | DepthYielded of
      {kind : searchBudget.kind, usage : searchBudget.usage,
       session : depth_session}

fun CS_DEPTH_SESSION budget config bound cs goal ctxt : depth_session =
  let val initial = clasetGoal.from_goal goal
  in
    {cursor =
       ref
         (seq.delay
           (fn () =>
             bounded_depth_in_with (searchBudget.charge budget)
               ctxt config cs bound initial)),
     pending = ref NONE, budget = budget, goal = goal,
     ctxt = ctxt, aborted = ref false}
  end

fun RESUME_DEPTH_SESSION
      (session as {cursor, pending, budget, goal, ctxt, aborted} :
       depth_session) =
  let
    fun discard rest =
      (pending := NONE; cursor := rest; advance ())
    and replay (node, rest) =
      let
        val _ =
          searchBudget.charge budget searchBudget.Normalization
        val result =
          case seq.cases (replay_node goal node ctxt) of
              NONE => NONE
            | SOME (proof, _) =>
                SOME
                  (Tactical.VALID
                    (fn _ => fn _ => proof) goal ctxt)
        val _ = pending := NONE
        val _ = cursor := rest
      in
        case result of
            SOME proved =>
              if null (#1 proved) then
                DepthProved {result = proved, session = session}
              else advance ()
          | NONE => advance ()
      end
      handle HOL_ERR _ => discard rest
    and advance () =
      case !pending of
          SOME candidate => replay candidate
        | NONE =>
            (case seq.cases (!cursor) of
                 NONE => DepthExhausted
               | SOME candidate =>
                   (pending := SOME candidate; replay candidate))
  in
    if !aborted then
      raise mk_HOL_ERR "classicalLib" "RESUME_DEPTH_SESSION"
        "an interrupted or failed depth session cannot be resumed"
    else
      (advance ()
       handle searchBudget.LimitReached (kind, usage) =>
                DepthYielded
                  {kind = kind, usage = usage, session = session}
            | exn => (aborted := true; raise exn))
  end

fun CS_DEEPEN_TAC cs {start} goal ctxt =
  solve
    (clasetSearch.DEEPEN (classical_level ctxt) (2, 10)
      (bounded_depth_in ctxt {dup = true} cs) start) goal ctxt

fun invocation body = clasetLib.with_context_claset clasetLib.SearchFacts body
fun safe_invocation body =
  clasetLib.with_context_claset clasetLib.SafeFacts body

fun public tactic = invocation (NTactical.DETERM o tactic)
fun public_safe tactic = safe_invocation (NTactical.DETERM o tactic)

(* The saturating tactics report a no-op as failure, and inserting a fact is
   not a no-op, so their progress test spans the whole invocation: an engine
   that finds no step leaves the supplied facts in the residue instead of
   discarding them.  With nothing to insert this is exactly the engine's own
   test.  The step tactics keep theirs, since one that could "succeed" by
   inserting alone would make NREPEAT insert for ever. *)
fun progress_with invoke tactic theorems =
  Tactical.CHANGED_TAC
    (invoke (NTactical.DETERM o NTactical.NTRY o tactic) theorems)

fun progress tactic = progress_with safe_invocation tactic

fun SAFE_TAC theorems = progress CS_SAFE_TAC theorems
fun CLARIFY_TAC theorems = progress CS_CLARIFY_TAC theorems
fun SAFE_STEP_TAC theorems = public_safe CS_SAFE_STEP_TAC theorems
fun CLARIFY_STEP_TAC theorems = public_safe CS_CLARIFY_STEP_TAC theorems
fun STEP_TAC theorems = public CS_STEP_TAC theorems
fun SLOW_STEP_TAC theorems = public CS_SLOW_STEP_TAC theorems
fun INST_STEP_TAC theorems = public CS_INST_STEP_TAC theorems

fun FAST_TAC theorems = public CS_FAST_TAC theorems
fun SLOW_TAC theorems = public CS_SLOW_TAC theorems
fun BEST_TAC theorems = public CS_BEST_TAC theorems
fun SLOW_BEST_TAC theorems = public CS_SLOW_BEST_TAC theorems
fun FIRST_BEST_TAC theorems = public CS_FIRST_BEST_TAC theorems
fun ASTAR_TAC theorems = public CS_ASTAR_TAC theorems
fun SLOW_ASTAR_TAC theorems = public CS_SLOW_ASTAR_TAC theorems
fun DEEPEN_TAC theorems =
  public (fn cs => CS_DEEPEN_TAC cs {start = 4}) theorems

end
