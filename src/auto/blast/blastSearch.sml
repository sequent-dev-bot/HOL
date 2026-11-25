structure blastSearch :> blastSearch =
struct

(* Faithful search port from Isabelle src/Provers/blast.ML.
   Branches and initialization map lines 93--99 and 1179--1184.
   Equality maps lines 692--790; closers map lines 797--815.
   Child md flags map lines 817--826.  Backtracking and pruning map
   lines 829--874; addTrackedLit maps lines 876--894; the penalty and
   recursive check map lines 897--915.

   The five prv clauses map lines 938--940, 941--1064, 1065--1072,
   1073--1174, and 1175--1176.  Within clause 2, safe expansion maps
   lines 953--1006, closing maps lines 1008--1031, and the committed
   equality/close/safe/defer cascade maps lines 1032--1063.  Clause 3's
   level merge maps lines 1065--1072.  Clause 4's children, gamma
   requeue, recursive-level sharing, penalty, mayUndo, and kill-all map
   lines 1082--1160; its literal fallback maps lines 1167--1173.
   Replay-failure re-entry maps lines 1254--1277.  deepenGoal maps the
   DEEPEN call at lines 1284--1292.
*)

open blastTerm listUtil

infix 9 $

type pterm = blastTerm.term
type var = blastTerm.var
type goal = Abbrev.goal
type claset = clasetLib.claset
type tableau_rule = blastRule.tableau_rule

type level =
  (pterm * bool) list * (pterm * bool) list

type branch =
  {pairs : level list,
   lits : pterm list,
   vars : var list,
   lim : int}

datatype script_step =
    HypSubst of
      {equality : int, changed : bool list,
       side : clasetStep.hyp_subst_side}
  | CloseAssume of {assumption : int}
  | CloseContradiction of {negative : int, positive : int}
  | SafeRule of
      {rule : tableau_rule, updated : bool, major : int option}
  | DeferGoal
  | UnsafeRule of
      {rule : tableau_rule, updated : bool, duplicate : bool,
       major : int option}

type script = script_step list

type proof =
  {script : script,
   trace : branch list list,
   depth : int,
   branches_created : int,
   branches_closed : int,
   choices_pruned : int}

type phase_statistics =
  {emergency_cleanup_assignments : int,
   cooperative_checkpoints : int,
   candidate_rules_enumerated : int,
   candidate_conversions_attempted : int,
   safe_rule_attempts : int,
   unsafe_rule_attempts : int,
   rule_unification_attempts : int,
   rule_unification_successes : int,
   equality_substitution_attempts : int,
   equality_substitution_successes : int,
   literal_close_attempts : int,
   literal_close_successes : int}

type statistics =
  {configured_depth : int,
   maximum_resource_cost : int,
   inferences_performed : int,
   branches_created : int,
   branches_closed : int,
   choices_pruned : int,
   rule_cache_hits : int,
   rule_conversions : int,
   remaining_trail_assignments : int,
   phase : phase_statistics}

datatype completion = Completed | Interrupted

type 'a measured_result =
  {completion : completion,
   fullTrace : branch list list,
   result : 'a option,
   statistics : statistics}

type debug_result =
  {fullTrace : branch list list,
   result : proof option}

val depth_limit = ref 20

exception PROOF_FAILED
exception PROVE
exception DEST_EQ
exception NEWBRANCHES
exception CLOSEF

(* Assumption tokens are local to one [runTerms] invocation.  Search queues
   may rotate, partition, normalize and deduplicate formulae, so neither a
   queue position nor term equality identifies a typed assumption occurrence.
   Every queued formula therefore carries its occurrence token, while each
   internal branch separately carries the exact ordered model of the typed
   goal's assumptions.  Goal formulae have no token until DeferGoal performs
   ccontr.  Tokens are never exported: recorded script positions are resolved
   against the model at the committing transition. *)
type assumption_token = int
type assumption_model = (assumption_token * pterm) list

datatype tracked_formula =
  Tracked of {term : pterm, token : assumption_token option}

type tracked_level =
  (tracked_formula * bool) list * (tracked_formula * bool) list

type search_branch =
  {pairs : tracked_level list,
   lits : tracked_formula list,
   vars : var list,
   lim : int,
   assumptions : assumption_model}

fun trackedTerm (Tracked {term, ...}) = term
fun trackedToken (Tracked {token, ...}) = token

fun withTrackedTerm term (Tracked {token, ...}) =
  Tracked {term = term, token = token}

fun provenanceError function message =
  raise Fail ("blastSearch." ^ function ^ ": " ^ message)

fun tokenPosition function token assumptions =
  let
    fun find _ [] =
          provenanceError function
            "an assumption token is absent from the branch model"
      | find position ((current, _) :: rest) =
          if current = token then position else find (position + 1) rest
  in
    find 1 assumptions
  end

fun trackedPosition function formula assumptions =
  case trackedToken formula of
      NONE =>
        provenanceError function
          "an assumption formula has no provenance token"
    | SOME token => tokenPosition function token assumptions

fun deleteToken function token assumptions =
  let
    fun remove [] =
          provenanceError function
            "an eliminated assumption token is absent from the branch model"
      | remove ((entry as (current, _)) :: rest) =
          if current = token then rest else entry :: remove rest
  in
    remove assumptions
  end

fun moveTokenLast function token assumptions =
  let
    fun move [] =
          provenanceError function
            "an assumption token is absent from the branch model"
      | move ((entry as (current, _)) :: rest) =
          if current = token then rest @ [entry] else entry :: move rest
  in
    move assumptions
  end

fun projectPair (formula, md) = (trackedTerm formula, md)

fun projectBranch
      ({pairs, lits, vars, lim, ...} : search_branch) : branch =
  {pairs = map (fn (safe, unsafe) =>
                  (map projectPair safe, map projectPair unsafe)) pairs,
   lits = map trackedTerm lits, vars = vars, lim = lim}

fun projectBranches branches = map projectBranch branches

datatype choice = Choice of int * int * exn

val not_name = {Thy = "bool", Name = "~"}
val equality_name = {Thy = "min", Name = "="}

fun negate formula = Const (not_name, []) $ formula

fun isNot (Const (name, _) $ _) = name = not_name
  | isNot _ = false

fun negOfGoal formula =
  if isGoal formula then negate (rand formula) else formula

fun negOfTracked formula =
  withTrackedTerm (negOfGoal (trackedTerm formula)) formula

fun negOfTrackedPair (formula, md) = (negOfTracked formula, md)

(* A goal formula is the branch's conclusion, not one of its assumptions,
   so its negation has no occurrence to cite.  A rule whose premises carry
   a goal negates the goals the branch already holds, and contraposing
   those goals first is what gives the negations an occurrence.  Only the
   branch's own conclusion can be moved this way, so the formula the rule
   is about to consume is left alone. *)
fun tokenlessGoal (Tracked {term = term, token = NONE}) = isGoal term
  | tokenlessGoal _ = false

fun tokenlessGoalPair (formula, _) = tokenlessGoal formula

fun branchHasTokenlessGoal checkpoint (lits, pairs) =
  let
    fun inLevel (safe, unsafe) =
      existsMeasured checkpoint tokenlessGoalPair safe orelse
      existsMeasured checkpoint tokenlessGoalPair unsafe
  in
    existsMeasured checkpoint tokenlessGoal lits orelse
    existsMeasured checkpoint inLevel pairs
  end

fun contraposeGoals checkpoint fresh (lits, pairs, assumptions) =
  let
    val added = ref ([] : (assumption_token * pterm) list)
    fun contrapose formula =
      if tokenlessGoal formula then
        let
          val token = fresh ()
          val term = negOfGoal (trackedTerm formula)
        in
          added := (token, term) :: !added;
          Tracked {term = term, token = SOME token}
        end
      else formula
    fun contraposePair (formula, md) = (contrapose formula, md)
    fun contraposeLevel (safe, unsafe) =
      (mapMeasured checkpoint contraposePair safe,
       mapMeasured checkpoint contraposePair unsafe)
    val lits' = mapMeasured checkpoint contrapose lits
    val pairs' = mapMeasured checkpoint contraposeLevel pairs
  in
    (lits', pairs',
     foldl (fn (entry, model) => entry :: model) assumptions (!added))
  end

(* Every search worker below has one checkpoint-parameterized body.  The
   plain entry point instantiates it with a no-op callback, while the
   measured entry point passes the run's checkpoint. *)

fun negOfTrackedGoalsMeasured checkpoint pairs =
  let
    val negate_pairs = mapMeasured checkpoint negOfTrackedPair
    fun negate_level (safe, unsafe) = (negate_pairs safe, unsafe)
  in
    mapMeasured checkpoint negate_level pairs
  end

fun negOfTrackedGoals pairs =
  negOfTrackedGoalsMeasured (fn () => ()) pairs

fun joinTrackedMdMeasured checkpoint md formulas =
  let
    fun has term =
      (checkpoint ();
       case term of
           Skolem _ => true
         | Abs (_, body) => has body
         | left $ right => has left orelse has right
         | _ => false)
    fun join formula = (formula, has (trackedTerm formula) orelse md)
  in
    mapMeasured checkpoint join formulas
  end

fun joinTrackedMd md formulas =
  if md then map (fn formula => (formula, true)) formulas
  else joinTrackedMdMeasured (fn () => ()) false formulas

fun initSearchBranchWith checkpoint addVars fresh (formulas, lim) :
      search_branch =
  let
    fun make [] = ([], [])
      | make (term :: rest) =
          let
            val _ = checkpoint ()
            val (tracked, assumptions) = make rest
          in
            if isGoal term then
              (Tracked {term = term, token = NONE} :: tracked,
               assumptions)
            else
              let val token = fresh ()
              in
                (Tracked {term = term, token = SOME token} :: tracked,
                 (token, term) :: assumptions)
              end
          end
    val (tracked, assumptions) = make formulas
    val vars = addVars (formulas, [])
  in
    {pairs = [(map (fn formula => (formula, true)) tracked, [])],
     lits = [], vars = vars, lim = lim, assumptions = assumptions}
  end

fun initSearchBranch fresh arguments =
  initSearchBranchWith (fn () => ()) add_terms_vars fresh arguments

fun initSearchBranchMeasured checkpoint fresh arguments =
  initSearchBranchWith checkpoint (add_terms_vars_measured checkpoint)
    fresh arguments

(* The projection drops the tokens, so they need not be fresh. *)
fun initBranch arguments =
  projectBranch (initSearchBranch (fn () => 0) arguments)

fun lengthMeasured checkpoint values =
  let
    fun count [] n = n
      | count (_ :: rest) n =
          (checkpoint (); count rest (n + 1))
  in
    count values 0
  end

fun trackPremise fresh premise =
  let
    fun track [] = ([], [])
      | track (term :: rest) =
          if isGoal term then
            let val (tracked, entries) = track rest
            in
              (Tracked {term = term, token = NONE} :: tracked, entries)
            end
          else
            let
              val token = fresh ()
              val (tracked, entries) = track rest
            in
              (Tracked {term = term, token = SOME token} :: tracked,
               (token, term) :: entries)
            end
  in
    track premise
  end

fun addHiddenAssumption fresh hidden entries =
  case hidden of
      NONE => entries
    | SOME index =>
        let
          val token = fresh ()
          val term = negate False
          val entry = (token, term)
          fun insert 0 rest = entry :: rest
            | insert _ [] =
                provenanceError "addHiddenAssumption"
                  "hidden elimination antecedent index is out of range"
            | insert n (item :: rest) =
                item :: insert (n - 1) rest
        in
          if index < 0 then
            provenanceError "addHiddenAssumption"
              "hidden elimination antecedent index is negative"
          else insert index entries
        end

fun ruleIsElim ({origin, ...} : tableau_rule) =
  case origin of
      blastRule.Stored {is_elim, ...} => is_elim
    | _ => false

(* Formulae constructed by switching tableau goals are deliberately
   tokenless: they do not name an assumption occurrence in the replay goal.
   A stored elimination rule must therefore never select one as its major.
   Conversely, introduction rules apply only to the tokenless goal side. *)
fun ruleHasCompatibleMajor rule formula =
  ruleIsElim rule = Option.isSome (trackedToken formula)

fun ruleMajor function rule formula assumptions =
  if ruleIsElim rule then
    SOME (trackedPosition function formula assumptions)
  else
    (case trackedToken formula of
         NONE => NONE
       | SOME _ =>
           provenanceError function
             "an introduction rule selected an assumption formula")

fun childAssumptions function rule duplicate formula assumptions =
  let
    val inherited =
      if not (ruleIsElim rule) then assumptions
      else
        case trackedToken formula of
            NONE =>
              provenanceError function
                "an elimination rule selected a goal formula"
          | SOME token =>
              if duplicate then moveTokenLast function token assumptions
              else deleteToken function token assumptions
  in
    fn introduced => List.revAppend (introduced, inherited)
  end

fun sameVarsWith checkpoint ([], []) = true
  | sameVarsWith checkpoint (left :: lefts, right :: rights) =
      (checkpoint ();
       left = right andalso sameVarsWith checkpoint (lefts, rights))
  | sameVarsWith checkpoint _ = false

fun log4 n = if n < 4 then 0 else 1 + log4 (n div 4)

fun instantiationPenalty n = 1 + log4 n

(* An instantiating step that leaves one of the branch's unknowns bound
   to a term with a rigid head has not answered the formula: it has
   chosen a shape for it, out of as many shapes as the claset has rules
   to offer there.  Isabelle's charge reads that supply off a
   library-wide claset, where the same choice costs a level more than it
   does under a per-theory one; the choice itself is what is dear, so
   charge the level here instead of inheriting it from a rule count.
   Assignments to the rule's own variables are how a rule is matched,
   not how a formula is guessed, and are not charged. *)
fun guessedShapeWith checkpoint {assigned, rule_vars} =
  let
    fun rigid term =
      (checkpoint ();
       case head_of term of
           Var assignment =>
             (case !assignment of
                  NONE => false
                | SOME body => rigid body)
         | _ => true)

    fun chosen variable =
      (checkpoint ();
       not (mem_var (variable, rule_vars)) andalso
       (case !variable of
            NONE => false
          | SOME body => rigid body))
  in
    existsMeasured checkpoint chosen assigned
  end

fun guessedShape query = guessedShapeWith (fn () => ()) query

fun assignedSinceWith checkpoint state mark =
  let
    fun take (_, 0) = []
      | take ([], _) = []
      | take (variable :: rest, remaining) =
          (checkpoint (); variable :: take (rest, remaining - 1))
  in
    take (trailVars state, trailSize state - mark)
  end

fun guessedAt checkpoint state mark rule_vars =
  guessedShapeWith checkpoint
    {assigned = assignedSinceWith checkpoint state mark,
     rule_vars = rule_vars}

fun recursivePremiseMeasured checkpoint pattern premise =
  let
    fun matches (Var _) _ = (checkpoint (); true)
      | matches Goal (Const (name, _)) =
          (checkpoint (); name = not_name)
      | matches (Const (name, _)) Goal =
          (checkpoint (); name = not_name)
      | matches (Const (a, ats)) (Const (b, bts)) =
          (checkpoint ();
           a = b andalso match_lists (ats, bts))
      | matches (Fvar a) (Fvar b) = (checkpoint (); a = b)
      | matches Goal Goal = (checkpoint (); true)
      | matches False False = (checkpoint (); true)
      | matches (Bound i) (Bound j) = (checkpoint (); i = j)
      | matches (Abs (_, left)) (Abs (_, right)) =
          (checkpoint (); matches left right)
      | matches (f $ x) (g $ y) =
          (checkpoint (); matches f g andalso matches x y)
      | matches _ _ = (checkpoint (); false)
    and match_lists ([], []) = true
      | match_lists (left :: lefts, right :: rights) =
          (checkpoint ();
           matches left right andalso match_lists (lefts, rights))
      | match_lists _ = false
  in
    existsMeasured checkpoint (matches pattern) premise
  end

fun recursivePremise pattern premise =
  recursivePremiseMeasured (fn () => ()) pattern premise

fun requeueTrackedGammaMeasured checkpoint
      (formula, md) remaining duplicate =
  if not duplicate then remaining
  else appendMeasured checkpoint remaining [(negOfTracked formula, md)]

fun requeueTrackedGamma pair remaining duplicate =
  requeueTrackedGammaMeasured (fn () => ()) pair remaining duplicate

fun requeueGamma (formula, md) remaining duplicate =
  let
    fun untracked (term, flag) = (Tracked {term = term, token = NONE}, flag)
  in
    map projectPair
      (requeueTrackedGamma (untracked (formula, md))
         (map untracked remaining) duplicate)
  end

fun killsAllAlternatives limit prems =
  limit < 0 andalso not (null prems)

fun mayUndoMeasured checkpoint {other_rules, updated, old_vars, new_vars} =
  other_rules orelse updated orelse
  sameVarsWith checkpoint (old_vars, new_vars)

fun mayUndo arguments = mayUndoMeasured (fn () => ()) arguments

(* The trail is newest first.  As in blast.ML:831--838, assignments in
   instantiations of next_vars count as clashes too. *)
fun clashVar [] _ = false
  | clashVar vars (n, trail) =
      let
        fun clash (0, _) = false
          | clash (_, []) = false
          | clash (left, variable :: variables) =
              List.exists
                (fn next => varOccur variable (Var next)) vars orelse
              clash (left - 1, variables)
      in
        clash (n, trail)
      end

(* The measured clash test polls once per trail entry and once per next
   variable.  It therefore cannot take clashVar's shortcut on an empty
   next_vars without losing those checkpoints, so the clash test stays a
   parameter of the shared pruning body below. *)
fun clashVarMeasured checkpoint vars (n, trail) =
  let
    fun occurs_in variable =
      existsMeasured checkpoint
        (fn next => varOccurMeasured checkpoint variable (Var next))
    fun clash (0, _) = false
      | clash (_, []) = false
      | clash (left, variable :: variables) =
          (checkpoint ();
           occurs_in variable vars orelse clash (left - 1, variables))
  in
    clash (n, trail)
  end

fun dropWith checkpoint (0, values) = values
  | dropWith checkpoint (_, []) = []
  | dropWith checkpoint (n, _ :: values) =
      (checkpoint (); dropWith checkpoint (n - 1, values))

fun pruneChoicesWith checkpoint clashes project
      {branches, next_vars, trail_mark, trail, choices} =
  if branches = 1 then (choices, 0)
  else
    let
      (* Newer choices from other branches are only discarded when a
         choice for this branch can be discarded too. *)
      fun scan (last, _, _, _, []) = last
        | scan (last, visited, mark, current, choice :: older) =
            let
              val _ = checkpoint ()
              val (oldmark, oldbrs) = project choice
            in
              if oldbrs < branches then last
              else if oldbrs > branches then
                scan (last, visited + 1, mark, current, older)
              else if clashes next_vars (mark - oldmark, current) then
                last
              else
                scan ((older, visited + 1), visited + 1, oldmark,
                      dropWith checkpoint (mark - oldmark, current), older)
            end
    in
      scan ((choices, 0), 0, trail_mark, trail, choices)
    end

fun prunePlanWith checkpoint clashes arguments =
  #1 (pruneChoicesWith checkpoint clashes Lib.I arguments)

(* Pure projection of prune, exported so its clash/no-clash boundary can be
   regression-tested without manufacturing exception values. *)
fun prunePlan arguments =
  prunePlanWith (fn () => ()) clashVar arguments

fun choiceMark (Choice (mark, branches, _)) = (mark, branches)

fun pruneWith checkpoint clashes state pruned
      (branches, next_vars, choices) =
  if branches = 1 then choices
  else
    let
      val all_marks = mapMeasured checkpoint choiceMark choices
      val remaining =
        prunePlanWith checkpoint clashes
          {branches = branches,
           next_vars = next_vars,
           trail_mark = trailSize state,
           trail = trailVars state,
           choices = all_marks}
      val removed =
        lengthMeasured checkpoint choices -
        lengthMeasured checkpoint remaining
      val _ = pruned := !pruned + removed
    in
      dropWith checkpoint (removed, choices)
    end

fun prune state pruned (branches, next_vars, choices) =
  if branches = 1 then choices
  else
    let
      val (remaining, removed) =
        pruneChoicesWith (fn () => ()) clashVar choiceMark
          {branches = branches,
           next_vars = next_vars,
           trail_mark = trailSize state,
           trail = trailVars state,
           choices = choices}
    in
      pruned := !pruned + removed;
      remaining
    end

fun pruneMeasured checkpoint state pruned arguments =
  pruneWith checkpoint (clashVarMeasured checkpoint) state pruned
    arguments

fun nextVars ({vars, ...} : search_branch) = vars

fun remainingVars [] = []
  | remainingVars (branch :: _) = nextVars branch

fun backtrack [] = raise PROVE
  | backtrack (Choice (_, _, jump) :: _) = raise jump

fun addTrackedLitWith checkpoint equal (original, lits) =
  let
    val original_term = trackedTerm original
    fun ins formula =
      if existsMeasured checkpoint
           (fn other => equal (trackedTerm formula, trackedTerm other)) lits
      then lits
      else formula :: lits
  in
    case original_term of
        Goal $ formula =>
          let
            fun bad lit =
              case trackedTerm lit of
                  Goal $ _ => true
                | Const (head, _) $ other =>
                    head = not_name andalso equal (formula, other)
                | _ => false
            fun change lit =
              case trackedTerm lit of
                  Goal $ other =>
                    if equal (formula, other) then NONE
                    else SOME (withTrackedTerm (negate other) lit)
                | Const (head, _) $ other =>
                    if head = not_name andalso equal (formula, other) then
                      NONE
                    else SOME lit
                | _ => SOME lit
            val rest =
              if existsMeasured checkpoint bad lits then
                mapPartialMeasured checkpoint change lits
              else lits
          in
            Tracked
              {term = Goal $ formula, token = trackedToken original} :: rest
          end
      | _ => ins original
  end

fun addTrackedLit arguments =
  addTrackedLitWith (fn () => ()) aconv arguments

fun addTrackedLitMeasured checkpoint arguments =
  addTrackedLitWith checkpoint (aconvMeasured checkpoint) arguments

fun substAtomicWith checkpoint (old, replacement) term =
  let
    fun subst value =
      (checkpoint ();
       case value of
           Var variable =>
             (case !variable of
                  SOME assigned => subst assigned
                | NONE =>
                    if aconv (value, old) then replacement else value)
         | Abs (name, body) =>
             let val body' = subst body
             in
               if Portable.pointer_eq (body', body) then value
               else Abs (name, body')
             end
         | left $ right =>
             let
               val left' = subst left
               val right' = subst right
             in
               if Portable.pointer_eq (left', left) andalso
                  Portable.pointer_eq (right', right) then value
               else left' $ right'
             end
         | _ => if aconv (value, old) then replacement else value)
  in
    subst term
  end

fun substAtomic pair term = substAtomicWith (fn () => ()) pair term

(* Eta-contraction, the occurs check and the Skolem/Fvar orientation of
   blast.ML:692--790, as one body. *)
fun destEqWith checkpoint equal term =
  let
    val member_zero = existsMeasured checkpoint (fn i => i = 0)
    val loose = loose_bnos_measured checkpoint
    val decrement = incr_boundvars_measured checkpoint ~1
    fun contract original =
      (checkpoint ();
       case original of
           Abs (name, body) =>
             (case contract2 body of
                  f $ Bound 0 =>
                    if member_zero (loose f) then original
                    else contract (decrement f)
                | _ => original)
         | _ => original)
    and contract2 (left $ right) =
          (checkpoint (); left $ contract right)
      | contract2 term = (checkpoint (); contract term)

    fun occurs target =
      let
        val allowed =
          case target of Skolem (_, variables) => variables | _ => []
        fun member variable =
          existsMeasured checkpoint (fn item => variable = item)
        fun occursEqual value =
          equal (target, value) orelse visit value
        and visit value =
          (checkpoint ();
           case value of
               Var variable =>
                 (case !variable of
                      SOME assigned => occursEqual assigned
                    | NONE => not (member variable allowed))
             | Abs (_, body) => occursEqual body
             | left $ right => occursEqual right orelse occursEqual left
             | _ => false)
      in
        occursEqual
      end

    fun checked (old, replacement) =
      if occurs old replacement then raise DEST_EQ
      else (old, replacement)

    (* The eliminated side is reported, not left to be recomputed: by the
       time the script is replayed a metavariable in the equality may have
       been instantiated, making the other side substitutable too. *)
    fun eliminate_left (left, right) =
      let val (old, replacement) = checked (left, right)
      in (clasetStep.EliminateLeft, old, replacement) end
    fun eliminate_right (left, right) =
      let val (old, replacement) = checked (right, left)
      in (clasetStep.EliminateRight, old, replacement) end

    fun orient (left, right) =
      case (left, right) of
          (Skolem _, _) => eliminate_left (left, right)
        | (_, Skolem _) => eliminate_right (left, right)
        | (Fvar _, _) => eliminate_left (left, right)
        | (_, Fvar _) => eliminate_right (left, right)
        | _ => raise DEST_EQ
  in
    checkpoint ();
    case term of
        Const (name, _) $ left0 $ right0 =>
          if name = equality_name then
            let
              val left = contract left0
              val right = contract right0
            in
              orient (left, right)
            end
          else raise DEST_EQ
      | _ => raise DEST_EQ
  end

fun equalTrackedSubstWith checkpoint equal function
      (formula,
       {pairs, lits, vars, lim, assumptions} : search_branch) =
  let
    val (side, old, replacement) =
      destEqWith checkpoint equal (trackedTerm formula)
    val token =
      case trackedToken formula of
          SOME token => token
        | NONE =>
            provenanceError function
              "an assumption formula has no provenance token"
    val subst = substAtomicWith checkpoint (old, replacement)
    (* The model mirrors work already polled while traversing the search
       queues.  Keep this bounded positional bookkeeping pure so provenance
       does not perturb the established measured checkpoint counters. *)
    val model_subst = substAtomic (old, replacement)
    fun substitute tracked =
      withTrackedTerm (subst (trackedTerm tracked)) tracked
    fun subForm ((item, md), (changed, unchanged)) =
      let
        val _ = checkpoint ()
        val result = substitute item
      in
        if equal (trackedTerm result, trackedTerm item) then
          (changed, (item, md) :: unchanged)
        else ((result, md) :: changed, unchanged)
      end
    fun subFrame ((safe, unsafe), (changed, frames)) =
      let
        val _ = checkpoint ()
        val (changed', safe') = List.foldr subForm (changed, []) safe
        val (changed'', unsafe') =
          List.foldr subForm (changed', []) unsafe
      in
        (changed'', (safe', unsafe') :: frames)
      end
    fun subLit (lit, (changed, unchanged)) =
      let
        val _ = checkpoint ()
        val result = substitute lit
      in
        if equal (trackedTerm result, trackedTerm lit) then
          (changed, result :: unchanged)
        else ((result, true) :: changed, unchanged)
      end
    fun subEntry
          ((entry as (_, term)), (mask, changed, unchanged)) =
      let val result = model_subst term
      in
        if aconv (result, term) then
          (false :: mask, changed, entry :: unchanged)
        else
          (true :: mask, (#1 entry, result) :: changed, unchanged)
      end
    val equality = ref 0
    fun subEntries _ [] =
          provenanceError function
            "an assumption token is absent from the branch model"
      | subEntries position ((entry as (current, _)) :: rest) =
          if current = token then
            (equality := position; List.foldr subEntry ([], [], []) rest)
          else subEntry (entry, subEntries (position + 1) rest)
    val (changed_mask, changed_assumptions, unchanged_assumptions) =
      subEntries 1 assumptions
    val (changed, lits') = List.foldr subLit ([], []) lits
    val (changed', pairs') = List.foldr subFrame (changed, []) pairs
    val _ = checkpoint ()
  in
    (!equality, changed_mask, side,
     {pairs = (changed', []) :: pairs', lits = lits', vars = vars,
      lim = lim,
      assumptions = changed_assumptions @ unchanged_assumptions})
  end

fun equalTrackedSubst arguments =
  equalTrackedSubstWith (fn () => ()) aconv "equalTrackedSubst" arguments

fun equalTrackedSubstMeasured checkpoint arguments =
  equalTrackedSubstWith checkpoint (aconvMeasured checkpoint)
    "equalTrackedSubstMeasured" arguments

fun closeStep function assumptions (formula, literal) =
  let
    val formula_term = trackedTerm formula
    val literal_term = trackedTerm literal
    fun assumption tracked =
      trackedPosition function tracked assumptions
    fun contradiction negative positive =
      CloseContradiction
        {negative = assumption negative, positive = assumption positive}
  in
    if isGoal formula_term then
      CloseAssume {assumption = assumption literal}
    else if isGoal literal_term then
      CloseAssume {assumption = assumption formula}
    else if isNot formula_term then contradiction formula literal
    else if isNot literal_term then contradiction literal formula
    else
      provenanceError function
        "a successful literal close has no supported polarity"
  end

fun tryTrackedCloseWith unifier function assumptions (formula, literal) =
  let
    val formula_term = trackedTerm formula
    val literal_term = trackedTerm literal
    fun positioned tracked = Option.isSome (trackedToken tracked)
    val reconstructible =
      if isGoal formula_term then positioned literal
      else if isGoal literal_term then positioned formula
      else if isNot formula_term orelse isNot literal_term then
        positioned formula andalso positioned literal
      else false
    fun close (left, right) =
      if reconstructible andalso unifier ([], left, right) then
        SOME (closeStep function assumptions (formula, literal))
      else NONE
  in
    if isGoal formula_term then
      close (rand formula_term, literal_term)
    else if isGoal literal_term then
      close (formula_term, rand literal_term)
    else if isNot formula_term then
      close (rand formula_term, literal_term)
    else if isNot literal_term then
      close (formula_term, rand literal_term)
    else NONE
  end

fun tryTrackedClose state assumptions arguments =
  tryTrackedCloseWith (unify state) "tryTrackedClose" assumptions
    arguments

fun tryTrackedCloseMeasured cleanup checkpoint state assumptions
      arguments =
  tryTrackedCloseWith (unifyMeasuredWith cleanup checkpoint state)
    "tryTrackedCloseMeasured" assumptions arguments

fun foldPremVarsWith checkpoint addVars prems vars =
  let
    fun fold [] accumulated = accumulated
      | fold (premise :: rest) accumulated =
          (checkpoint (); fold rest (addVars (premise, accumulated)))
  in
    fold (rev prems) vars
  end

fun foldPremVars prems vars =
  foldPremVarsWith (fn () => ()) add_terms_vars prems vars

fun foldPremVarsMeasured checkpoint prems vars =
  foldPremVarsWith checkpoint (add_terms_vars_measured checkpoint)
    prems vars

fun termString term =
  case term of
      Const (name, []) => KernelSig.name_toString name
    | Const (name, args) =>
        KernelSig.name_toString name ^ "{" ^
        String.concatWith "," (map termString args) ^ "}"
    | Skolem (name, variables) =>
        name ^ "[" ^ Int.toString (length variables) ^ "]"
    | Fvar name => name
    | Goal => "*Goal*"
    | False => "*False*"
    | Var variable =>
        (case !variable of
             SOME value => termString value
           | NONE => "?")
    | Bound index => "B" ^ Int.toString index
    | Abs (name, body) => "(\\" ^ name ^ ". " ^ termString body ^ ")"
    | left $ right =>
        "(" ^ termString left ^ " " ^ termString right ^ ")"

fun pairString (formula, md) =
  termString formula ^ (if md then "+" else "-")

fun levelString (safe, unsafe) =
  "S[" ^ String.concatWith ", " (map pairString safe) ^ "] U[" ^
  String.concatWith ", " (map pairString unsafe) ^ "]"

fun branchString ({pairs, lits, vars, lim} : branch) =
  "{lim=" ^ Int.toString lim ^ ", vars=" ^
  Int.toString (length vars) ^ ", lits=[" ^
  String.concatWith ", " (map termString lits) ^ "], levels=[" ^
  String.concatWith "; " (map levelString pairs) ^ "]}"

(* [branches] is forced only when the trace is printed. *)
fun traceState level depth branches =
  traceUtil.trace level 3
    (fn () =>
       "Blast trace at depth " ^ Int.toString depth ^ ":\n" ^
       String.concatWith "\n" (map branchString (branches ())))

datatype instrumentation =
    Stats
  | On of
      {debug : bool, stop : unit -> bool,
       budget : searchBudget.budget option}

datatype 'a budget_outcome =
    BudgetFinished of {result : 'a option, statistics : statistics}
  | BudgetYielded of
      {kind : searchBudget.kind, usage : searchBudget.usage,
       trail_assignments : int,
       resume : unit -> 'a budget_outcome}
  | BudgetLimitReached of
      {kind : searchBudget.kind, usage : searchBudget.usage}

datatype 'a run_outcome =
    RunDone of 'a measured_result
  | RunYielded of
      {kind : searchBudget.kind, usage : searchBudget.usage,
       trail_assignments : int,
       resume : unit -> 'a run_outcome}

val zero_phase_statistics : phase_statistics =
  {emergency_cleanup_assignments = 0,
   cooperative_checkpoints = 0,
   candidate_rules_enumerated = 0,
   candidate_conversions_attempted = 0,
   safe_rule_attempts = 0,
   unsafe_rule_attempts = 0,
   rule_unification_attempts = 0,
   rule_unification_successes = 0,
   equality_substitution_attempts = 0,
   equality_substitution_successes = 0,
   literal_close_attempts = 0,
   literal_close_successes = 0}

datatype interruption_cleanup = Restore | AbandonOwned

fun runGoal trace_level {keep_history, resumable} cleanup_policy instrumentation
    claset depth goal cont =
  let
    exception INTERRUPTED
    exception STOP_EXCEPTION of exn
    exception YIELDED
    val suspended = ref NONE
    val suspended_limit = ref NONE
    val state = newState ()
    val rule_cache = blastRule.newCache trace_level
    val closed = ref 0
    val created = ref 1
    val pruned = ref 0
    val next_token = ref 0
    fun freshToken () =
      (next_token := !next_token + 1; !next_token)
    val safeRuleOrigin = "safe rule"
    val safeChildOrigin = "safe child"
    val unsafeRuleOrigin = "unsafe rule"
    val unsafeChildOrigin = "unsafe child"
    (* The search workers come as two aligned records, one plain and one
       measured, selected once per run: [Stats] takes the plain one, [On]
       the measured one.  [prv] has a single body that closes
       over the selected components as ordinary free variables, so the
       production and the measured search cannot drift apart.  The phase
       counters and the cooperative checkpoint exist only in the [On] arm;
       every plain counterpart is inert.

       Workers whose measured variant polls the checkpoint -- and so may
       have to roll the trail back before propagating an interruption --
       take the current search step's trail mark as their leading
       argument.  Binding the components once here, rather than passing a
       worker record through [prv]'s mutual recursion, is deliberate: the
       recursion must stay free of record construction and field
       selection. *)
    val plainWorkers =
      let
        val noop = fn () => ()
        val unifyPlain = unify state
        val tryClose = tryTrackedClose state
        val prunePlain = prune state pruned
        val negLits = map negOfTracked
        val existsGoal = List.exists isGoal
        val appendPlain = fn left => fn right => left @ right
        val pairUnflagged = map (fn item => (item, false))
      in
        {checkpointAt=fn _ => (),
         rollbackAt=fn mark => clearTo state mark,
         noteSafeRuleAttempt=noop,
         noteUnificationSuccess=noop,
         noteEqualityAttempt=noop,
         noteEqualitySuccess=noop,
         noteLiteralAttempt=noop,
         noteLiteralSuccess=noop,
         addVarsAt=fn _ => add_term_vars,
         varsInVarsAt=fn _ => vars_in_vars,
         foldPremVarsAt=fn _ => foldPremVars,
         unifyAt=fn _ => unifyPlain,
         tryCloseAt=fn _ => tryClose,
         pruneAt=fn _ => prunePlain,
         equalSubstAt=fn _ => equalTrackedSubst,
         joinMdAt=fn _ => joinTrackedMd,
         negGoalsAt=fn _ => negOfTrackedGoals,
         mapNegLitsAt=fn _ => negLits,
         existsGoalAt=fn _ => existsGoal,
         addTrackedLitAt=fn _ => addTrackedLit,
         appendUnsafeAt=fn _ => appendPlain,
         safeRulesFor=blastRule.safeRules rule_cache claset,
         unsafeRulesFor=blastRule.unsafeRules rule_cache claset,
         noteUnsafeRuleAttempt=noop,
         mapPairAt=fn _ => pairUnflagged,
         requeueGammaAt=fn _ => requeueTrackedGamma,
         recursivePremiseAt=fn _ => recursivePremise,
         mayUndoAt=fn _ => mayUndo,
         normAt=fn _ => norm,
         mergeUnsafe=appendPlain,
         initialFormulasOf=blastRule.initialBranch,
         initialBranchOf=initSearchBranch freshToken,
         cleanupRun=fn _ => ()}
      end

    val (instrumentEntry, noteInference, noteRuleInference,
         instrumentationResult, searchWorkers) =
      case instrumentation of
          Stats =>
            let
              val inferences = ref 0
              val maximum_resource_cost = ref 0
              fun inference () = inferences := !inferences + 1
              fun ruleInference lim =
                (inferences := !inferences + 1;
                 maximum_resource_cost :=
                   Int.max (!maximum_resource_cost, depth - lim))
              fun result () =
                (!inferences, !maximum_resource_cost, [],
                 zero_phase_statistics)
            in
              (fn brs =>
                 traceState trace_level depth (fn () => projectBranches brs),
               inference, ruleInference, result, plainWorkers)
            end
        | On {debug, stop, budget} =>
            let
              val inferences = ref 0
              val maximum_resource_cost = ref 0
              val fullTrace = ref ([] : branch list list)
              val checkpoints = ref 0
              val candidates = ref 0
              val conversions = ref 0
              val safe_attempts = ref 0
              val unsafe_attempts = ref 0
              val unify_attempts = ref 0
              val unify_successes = ref 0
              val equality_attempts = ref 0
              val equality_successes = ref 0
              val literal_attempts = ref 0
              val literal_successes = ref 0
              val emergency_cleanups = ref 0

              fun charge kind =
                case budget of
                    NONE => ()
                  | SOME owned => searchBudget.charge owned kind

              fun checkpoint_kind kind () =
                let
                  val _ = charge kind
                  val _ = checkpoints := !checkpoints + 1
                  val requested =
                    stop () handle exn => raise STOP_EXCEPTION exn
                in
                  if requested then raise INTERRUPTED else ()
                end

              val checkpoint = checkpoint_kind searchBudget.Candidate

              fun entry brs =
                (checkpoint ();
                 if debug then
                    let val projected = projectBranches brs
                    in
                      fullTrace := projected :: !fullTrace;
                      traceState trace_level depth (fn () => projected)
                    end
                 else
                   traceState trace_level depth
                     (fn () => projectBranches brs))
              fun inference () =
                (charge searchBudget.Application;
                 inferences := !inferences + 1)
              fun ruleInference lim =
                (charge searchBudget.Application;
                 inferences := !inferences + 1;
                 maximum_resource_cost :=
                   Int.max (!maximum_resource_cost, depth - lim))

              fun candidate () =
                candidates := !candidates + 1
              fun conversion () =
                conversions := !conversions + 1
              val rule_monitor : blastRule.monitor =
                {candidate = candidate, conversion = conversion,
                 checkpoint = checkpoint}

              fun ruleAttempt attempts () =
                (attempts := !attempts + 1;
                 unify_attempts := !unify_attempts + 1)
              fun unificationSuccess () =
                unify_successes := !unify_successes + 1
              fun equalityAttempt () =
                equality_attempts := !equality_attempts + 1
              fun equalitySuccess () =
                equality_successes := !equality_successes + 1
              fun literalAttempt () =
                literal_attempts := !literal_attempts + 1
              fun literalSuccess () =
                literal_successes := !literal_successes + 1

              fun emergencyCleanup () =
                emergency_cleanups := !emergency_cleanups + 1

              (* Only INTERRUPTED may abandon state, and only because the
                 goal entry point created every prototerm reachable from the
                 search.  Predicate and continuation exceptions restore. *)
              fun cleanupException exn cleanup_state mark =
                case exn of
                    INTERRUPTED =>
                      (case cleanup_policy of
                           Restore =>
                             clearToWith emergencyCleanup cleanup_state mark
                         | AbandonOwned => ())
                  | _ =>
                      clearToWith emergencyCleanup cleanup_state mark

              fun checkpointRollbackWith kind mark =
                checkpoint_kind kind ()
                handle exn =>
                  (cleanupException exn state mark; raise exn)

              fun checkpointRollback mark =
                checkpointRollbackWith searchBudget.Candidate mark

              fun phaseResult () : phase_statistics =
                {emergency_cleanup_assignments = !emergency_cleanups,
                 cooperative_checkpoints = !checkpoints,
                 candidate_rules_enumerated = !candidates,
                 candidate_conversions_attempted = !conversions,
                 safe_rule_attempts = !safe_attempts,
                 unsafe_rule_attempts = !unsafe_attempts,
                 rule_unification_attempts = !unify_attempts,
                 rule_unification_successes = !unify_successes,
                 equality_substitution_attempts = !equality_attempts,
                 equality_substitution_successes = !equality_successes,
                 literal_close_attempts = !literal_attempts,
                 literal_close_successes = !literal_successes}
              fun result () =
                (!inferences, !maximum_resource_cost,
                 if debug then rev (!fullTrace) else [], phaseResult ())

              (* [at mark] is the checkpoint a worker polls when it may have
                 to roll the trail back to that step's mark first. *)
              fun at mark () = checkpointRollback mark

              val measuredWorkers =
                {checkpointAt=checkpointRollback,
                 rollbackAt=fn mark =>
                   clearToMeasuredWith cleanupException checkpoint state
                     mark,
                 noteSafeRuleAttempt=ruleAttempt safe_attempts,
                 noteUnificationSuccess=unificationSuccess,
                 noteEqualityAttempt=equalityAttempt,
                 noteEqualitySuccess=equalitySuccess,
                 noteLiteralAttempt=literalAttempt,
                 noteLiteralSuccess=literalSuccess,
                 addVarsAt=fn mark =>
                   add_term_vars_measured (at mark),
                 varsInVarsAt=fn mark =>
                   vars_in_vars_measured (at mark),
                 foldPremVarsAt=fn mark =>
                   foldPremVarsMeasured (at mark),
                 unifyAt=fn mark =>
                   unifyMeasuredWith cleanupException (at mark) state,
                 tryCloseAt=fn mark =>
                   tryTrackedCloseMeasured cleanupException (at mark) state,
                 pruneAt=fn mark =>
                   pruneMeasured (at mark) state pruned,
                 equalSubstAt=fn mark =>
                   equalTrackedSubstMeasured
                     (fn () =>
                       checkpointRollbackWith
                         searchBudget.Normalization mark),
                 joinMdAt=fn mark =>
                   joinTrackedMdMeasured (at mark),
                 negGoalsAt=fn mark =>
                   negOfTrackedGoalsMeasured (at mark),
                 mapNegLitsAt=fn mark =>
                   mapMeasured (at mark) negOfTracked,
                 existsGoalAt=fn mark =>
                   existsMeasured (at mark) isGoal,
                 addTrackedLitAt=fn mark =>
                   addTrackedLitMeasured (at mark),
                 appendUnsafeAt=fn mark =>
                   appendMeasured (at mark),
                 safeRulesFor=blastRule.safeRulesMeasured
                   rule_monitor rule_cache claset,
                 unsafeRulesFor=blastRule.unsafeRulesMeasured
                   rule_monitor rule_cache claset,
                 noteUnsafeRuleAttempt=ruleAttempt unsafe_attempts,
                 mapPairAt=fn mark =>
                   mapMeasured (at mark) (fn item => (item, false)),
                 requeueGammaAt=fn mark =>
                   requeueTrackedGammaMeasured (at mark),
                 recursivePremiseAt=fn mark =>
                   recursivePremiseMeasured (at mark),
                 mayUndoAt=fn mark =>
                   mayUndoMeasured (at mark),
                 normAt=fn mark =>
                   normMeasured
                     (fn () =>
                       checkpointRollbackWith
                         searchBudget.Normalization mark),
                 mergeUnsafe=appendMeasured checkpoint,
                 (* The search polls once per formula it takes in. *)
                 initialFormulasOf=fn goal =>
                   mapMeasured checkpoint Lib.I
                     (blastRule.initialBranchMeasured checkpoint goal),
                 initialBranchOf=initSearchBranchMeasured
                   checkpoint freshToken,
                 cleanupRun=fn exn => cleanupException exn state 0}
            in
              (entry, inference, ruleInference, result, measuredWorkers)
            end

    val {checkpointAt,rollbackAt,noteSafeRuleAttempt,
         noteUnificationSuccess,noteEqualityAttempt,noteEqualitySuccess,
         noteLiteralAttempt,noteLiteralSuccess,addVarsAt,varsInVarsAt,
         foldPremVarsAt,unifyAt,tryCloseAt,pruneAt,equalSubstAt,joinMdAt,
         negGoalsAt,mapNegLitsAt,existsGoalAt,addTrackedLitAt,
         appendUnsafeAt,safeRulesFor,unsafeRulesFor,noteUnsafeRuleAttempt,
         mapPairAt,requeueGammaAt,recursivePremiseAt,mayUndoAt,normAt,
         mergeUnsafe,initialFormulasOf,initialBranchOf,
         cleanupRun} = searchWorkers

    (* A function, not a worker: a record field cannot be polymorphic.  The
       plain build's inert checkpoint makes it [List.length]. *)
    fun lengthAt mark values =
      lengthMeasured (fn () => checkpointAt mark) values

    (* Measured search still polls while visiting each pending branch. *)
    val branchCountAt =
      case instrumentation of
          Stats => (fn _ => fn count => fn _ => count)
        | On _ => (fn mark => fn _ => fn branches => lengthAt mark branches)

    (* Siblings inherit the same branch lists. Keep the measured traversals
       in premise order so they still poll at their original checkpoints. *)
    fun shareForPremises prems compute =
      case (instrumentation, prems) of
          (Stats, _ :: _ :: _) =>
            let val shared = Portable.HOLSusp.delay compute
            in fn () => Portable.HOLSusp.force shared end
        | _ => compute

    val prepared =
      SOME (initialFormulasOf goal)
      handle INTERRUPTED => NONE
           | STOP_EXCEPTION exn => (cleanupRun exn; raise exn)
           | exn => (cleanupRun exn; raise exn)

    fun remember branches history =
      if keep_history then branches :: history else history

    fun proofOf (tacs, trace) =
      {script = rev tacs,
       trace = map projectBranches (rev trace),
       depth = depth,
       branches_created = !created,
       branches_closed = !closed,
       choices_pruned = !pruned}

    (* A yielded child keeps its backtracking handler when resumed.  The
       closure saved by the deepest prv call restarts only that call; each
       enclosing handler wraps it on the way out. *)
    fun preserve handler action =
      let
        fun suspend limit resume =
          (suspended_limit := SOME limit;
           suspended := SOME resume;
           raise YIELDED)
        fun continue_with resume =
          let val next = valOf (!suspended)
          in
            suspended := SOME (fn () => resume next);
            raise YIELDED
          end
        fun run_work work =
          ((work ()
            handle YIELDED => continue_with run_work
                 | searchBudget.LimitReached limit =>
                     if resumable then
                       suspend limit (fn () => run_work work)
                     else raise searchBudget.LimitReached limit)
           handle exn =>
             (case handler exn of
                  SOME recover => run_recover recover
                | NONE => raise exn))
        and run_recover recover =
          (recover ()
           handle YIELDED => continue_with run_recover
                | searchBudget.LimitReached limit =>
                    if resumable then
                      suspend limit (fn () => run_recover recover)
                    else raise searchBudget.LimitReached limit)
      in
        if resumable then run_work action
        else
          (action ()
           handle exn =>
             case handler exn of
                 SOME recover => recover ()
               | NONE => raise exn)
      end

    (* The rule loop both expansion arms share.  [fire] receives each rule
       that unified with [formula]; [limAfter unchanged] is the child's
       depth bound, [unchanged] when the unifier bound nothing, and [next]
       rolls back and tries the remaining rules. *)
    fun tryRules {mark, formula, lim, rule_count, noteAttempt, fire} =
      let
        fun deeper [] = raise NEWBRANCHES
          | deeper ((rule : tableau_rule) :: other) =
              let
                val _ = checkpointAt mark
                val pattern = #pattern rule
                val rule_vars = addVarsAt mark (pattern, [])
                val _ = checkpointAt mark
                val _ = noteAttempt ()
              in
                if not (ruleHasCompatibleMajor rule formula) then
                  deeper other
                else if not
                     (unifyAt mark
                       (rule_vars, pattern, trackedTerm formula)) then
                  deeper other
                else
                  let
                    val _ = noteUnificationSuccess ()
                    val _ = checkpointAt mark
                    val updated = mark < trailSize state
                    fun limAfter unchanged =
                      if updated then
                        lim - instantiationPenalty rule_count -
                        (if guessedAt (fn () => checkpointAt mark)
                              state mark rule_vars
                         then 1 else 0)
                      else unchanged
                  in
                    fire {rule = rule, other = other, updated = updated,
                          limAfter = limAfter,
                          next = fn () => (rollbackAt mark; deeper other)}
                  end
              end
      in
        deeper
      end

    (* A premise's tracked formulae and the assumptions it introduces. *)
    fun premiseChild mark (premise, hidden) =
      let
        val _ = checkpointAt mark
        val (tracked, visible_introduced) = trackPremise freshToken premise
      in
        (tracked, addHiddenAssumption freshToken hidden visible_introduced)
      end

    fun premiseBranches (rule : tableau_rule) child brs prems =
      let
        fun make (premise :: rest) (hidden :: more) =
              child (premise, hidden) :: make rest more
          | make _ _ = brs
      in
        make prems (#hidden_assumptions rule)
      end

    fun contraposing mark formula prems (lits, levels) =
      let val checkpoint = fn () => checkpointAt mark
      in
        not (isGoal (trackedTerm formula)) andalso
        existsMeasured checkpoint (existsGoalAt mark) prems andalso
        branchHasTokenlessGoal checkpoint (lits, levels)
      end

    (* Contrapose before the rule fires rather than after: ccontr moves the
       conclusion, and the conclusion is this branch's goal only until the
       rule replaces it.  [restore] puts the expanded formula back, so
       restarting on the result re-selects this same rule. *)
    fun contraposedBranch mark
          {lits, levels, restore, vars, lim, assumptions} : search_branch =
      let
        val (lits', levels', assumptions') =
          contraposeGoals (fn () => checkpointAt mark) freshToken
            (lits, levels, assumptions)
        val pairs' = restore levels'
        val _ = rollbackAt mark
      in
        {pairs = pairs', lits = lits', vars = vars, lim = lim,
         assumptions = assumptions'}
      end

    fun prv (tacs, trace, choices, open_count, brs) =
      let
        val entry_mark = if resumable then trailSize state else 0
      in
      (instrumentEntry brs;
       case brs of
          [] =>
            preserve
              (fn PROOF_FAILED =>
                    SOME (fn () =>
                      (traceUtil.trace trace_level 1
                         (fn () =>
                            "PROOF FAILED for depth " ^ Int.toString depth);
                       backtrack choices))
                | _ => NONE)
              (fn () => cont (proofOf (tacs, trace)))
        | brs0 as
            ({pairs = (((formula, md) :: safe, unsafe) :: pairs),
              lits, vars, lim, assumptions} : search_branch) :: brs =>
            let
              exception PRV
              val mark = trailSize state
              val branches = branchCountAt mark open_count brs0
              val next_vars = remainingVars brs
              val formula =
                withTrackedTerm (normAt mark (trackedTerm formula)) formula
              val rules = safeRulesFor vars (trackedTerm formula)
              val rule_count = lengthAt mark rules

              fun child assumptionsFor negated (vars', lim')
                    (premise, hidden) =
                let
                  val (tracked, introduced) =
                    premiseChild mark (premise, hidden)
                  val joined = joinMdAt mark md tracked
                  val child_assumptions = assumptionsFor introduced
                in
                  if existsGoalAt mark premise then
                    let val (negated_pairs, negated_lits) = negated ()
                    in
                      {pairs = (joined, []) :: negated_pairs,
                       lits = negated_lits, vars = vars', lim = lim',
                       assumptions = child_assumptions}
                    end
                  else
                    {pairs =
                       (joined, []) :: (safe, unsafe) :: pairs,
                     lits = lits, vars = vars', lim = lim',
                     assumptions = child_assumptions}
                end

              (* The lead positions worth retrying a split from.  Only a
                 variable still unbound after the rule fired can carry one
                 branch's decision into its siblings, so a split whose
                 premises share none of them has no order to reconsider. *)
              fun sharedLeads prems =
                let
                  fun premiseVars premise = foldPremVarsAt mark [premise] []
                  fun meets seen =
                    existsMeasured (fn () => checkpointAt mark)
                      (fn variable => mem_var (variable, seen))
                  fun shared _ [] = false
                    | shared seen (premise :: rest) =
                        let val vars = premiseVars premise
                        in
                          meets seen vars orelse shared (vars @ seen) rest
                        end
                  val count = lengthAt mark prems
                in
                  if count < 2 orelse not (shared [] prems) then []
                  else List.tabulate (count - 1, fn lead => lead + 1)
                end

              fun fire {rule : tableau_rule, other = _, updated, limAfter,
                        next} =
                let
                  val prems = #premises rule
                  val unified = trailSize state
                  val lim' = limAfter lim
                  val vars0 = varsInVarsAt mark vars
                  val choices' = Choice (mark, branches, PRV) :: choices
                  val major =
                    ruleMajor safeRuleOrigin rule formula assumptions
                  val contraposing =
                    contraposing mark formula prems
                      (lits, (safe, unsafe) :: pairs)

                  fun restore ((safe', unsafe') :: rest) =
                        ((formula, md) :: safe', unsafe') :: rest
                    | restore [] = []

                  fun descend limit variant =
                    let
                      val prems' = #premises variant
                      val vars' = foldPremVarsAt mark prems' vars0
                      val tacs' =
                        SafeRule
                          {rule = variant, updated = updated,
                           major = major} :: tacs
                    in
                      if null prems' then
                        let
                          val before_prune = !pruned
                          val choices'' =
                            pruneAt mark (branches, next_vars, choices')
                            handle searchBudget.LimitReached limit =>
                              (pruned := before_prune;
                               raise searchBudget.LimitReached limit)
                        in
                          (noteRuleInference limit
                           handle searchBudget.LimitReached work =>
                             (pruned := before_prune;
                              raise searchBudget.LimitReached work));
                          closed := !closed + 1;
                          prv (tacs', remember brs0 trace, choices'',
                               branches - 1, brs)
                        end
                      else if limit < 0 then
                        (rollbackAt mark; raise NEWBRANCHES)
                      else
                        let
                          val assumptionsFor =
                            childAssumptions safeChildOrigin variant false
                              formula assumptions
                          val negated = shareForPremises prems' (fn () =>
                            (negGoalsAt mark ((safe, unsafe) :: pairs),
                             mapNegLitsAt mark lits))
                          val children =
                            premiseBranches variant
                              (child assumptionsFor negated (vars', limit))
                              brs prems'
                          val count = lengthAt mark prems'
                        in
                          noteRuleInference limit;
                          created := !created + count - 1;
                          prv (tacs', remember brs0 trace, choices',
                               branches + count - 1, children)
                        end
                    end

                  fun exhausted () =
                    if updated then next () else backtrack choices

                  (* Reordering is not free: it is the one part of a safe
                     rule that commits, so it is priced like an
                     instantiating safe rule and a branch can afford only
                     as many reorderings as its remaining depth pays
                     for. *)
                  val retry_lim = lim' - instantiationPenalty rule_count

                  (* Sibling branches that share an unbound variable are
                     not independent: whichever is attempted first decides
                     the variable and the other inherits that decision.
                     Both orders are equally safe, so which sibling leads
                     is a genuine choice, and on failure the split is
                     retried with each of the others leading. *)
                  fun retry [] = exhausted ()
                    | retry (index :: rest) =
                        (case blastRule.rotatePremises index rule of
                             NONE => retry rest
                           | SOME variant =>
                               (rollbackAt unified;
                                preserve
                                  (fn PRV => SOME (fn () => retry rest)
                                    | _ => NONE)
                                  (fn () => descend retry_lim variant)))
                in
                  if contraposing then
                    prv
                      (DeferGoal :: tacs, remember brs0 trace, choices,
                       open_count,
                       contraposedBranch mark
                         {lits = lits, levels = (safe, unsafe) :: pairs,
                          restore = restore, vars = vars, lim = lim,
                          assumptions = assumptions} :: brs)
                  else
                    preserve
                      (fn PRV =>
                            SOME (fn () =>
                              if retry_lim < 0 then exhausted ()
                              else retry (sharedLeads prems))
                        | _ => NONE)
                      (fn () => descend lim' rule)
                end

              val deeper =
                tryRules
                  {mark = mark, formula = formula, lim = lim,
                   rule_count = rule_count,
                   noteAttempt = noteSafeRuleAttempt, fire = fire}

              fun closeF _ [] = raise CLOSEF
                | closeF literal_of (item :: items) =
                    let
                      val _ = checkpointAt mark
                      val _ = noteLiteralAttempt ()
                    in
                      case tryCloseAt mark assumptions
                             (formula, literal_of item) of
                          NONE => closeF literal_of items
                        | SOME step =>
                            let
                              val _ = noteLiteralSuccess ()
                              val _ = checkpointAt mark
                              val choices' =
                                pruneAt mark
                                  (branches, next_vars,
                                   Choice (mark, branches, PRV) :: choices)
                            in
                              noteInference ();
                              closed := !closed + 1;
                              preserve
                                (fn PRV =>
                                      SOME (fn () =>
                                        (rollbackAt mark;
                                         closeF literal_of items))
                                  | _ => NONE)
                                (fn () =>
                                  prv
                                    (step :: tacs, remember brs0 trace,
                                     choices', branches - 1, brs))
                            end
                    end

              fun onClose recover action =
                preserve
                  (fn CLOSEF => SOME recover | _ => NONE) action

              fun closeLevels [] = raise CLOSEF
                | closeLevels ((level_safe, level_unsafe) :: rest) =
                    (checkpointAt mark;
                     onClose
                       (fn () =>
                         onClose
                           (fn () => closeLevels rest)
                           (fn () => closeF Lib.fst level_unsafe))
                       (fn () => closeF Lib.fst level_safe))

              fun cascade () =
                if lim < 0 then backtrack choices
                else
                  preserve
                    (fn DEST_EQ =>
                          SOME (fn () =>
                            onClose
                              (fn () =>
                                onClose
                                  (fn () => deeper rules)
                                  (fn () =>
                                    closeLevels
                                      ((safe, unsafe) :: pairs)))
                              (fn () => closeF Lib.I lits))
                      | _ => NONE)
                    (fn () =>
                      let
                        val _ = checkpointAt mark
                        val _ = noteEqualityAttempt ()
                        val (equality, changed, side, substituted) =
                          equalSubstAt mark
                            (formula,
                             {pairs = (safe, unsafe) :: pairs,
                              lits = lits, vars = vars, lim = lim,
                              assumptions = assumptions})
                        val _ = noteEqualitySuccess ()
                        val _ = noteInference ()
                      in
                        prv
                          (HypSubst
                             {equality = equality, changed = changed,
                              side = side} :: tacs,
                           remember brs0 trace, choices, open_count,
                           substituted :: brs)
                      end)

              fun fallback () =
                case unsafeRulesFor vars (trackedTerm formula) of
                    [] =>
                      prv
                        (tacs, remember brs0 trace, choices, open_count,
                         {pairs = (safe, unsafe) :: pairs,
                          lits = addTrackedLitAt mark (formula, lits),
                          vars = vars, lim = lim,
                          assumptions = assumptions} :: brs)
                  | _ =>
                      let
                        val goal_formula = isGoal (trackedTerm formula)
                        val (deferred, assumptions') =
                          if goal_formula then
                            let
                              val token = freshToken ()
                              val term = negOfGoal (trackedTerm formula)
                            in
                              (Tracked {term = term, token = SOME token},
                               (token, term) :: assumptions)
                            end
                          else (negOfTracked formula, assumptions)
                      in
                        prv
                          ((if goal_formula then DeferGoal :: tacs
                            else tacs),
                           remember brs0 trace, choices, open_count,
                           {pairs =
                              (safe,
                               appendUnsafeAt mark unsafe
                                 [(deferred, md)]) :: pairs,
                            lits = lits, vars = vars, lim = lim,
                            assumptions = assumptions'} :: brs)
                      end

            in
              preserve
                (fn NEWBRANCHES => SOME fallback | _ => NONE)
                cascade
            end
        | ({pairs = ([], unsafe) :: (safe, unsafe') :: pairs,
            lits, vars, lim, assumptions} : search_branch) :: brs =>
            let
              val merged = mergeUnsafe unsafe unsafe'
            in
              prv
                (tacs, trace, choices, open_count,
                 {pairs = (safe, merged) :: pairs,
                  lits = lits, vars = vars, lim = lim,
                  assumptions = assumptions} :: brs)
            end
        | brs0 as
            ({pairs = [([], (formula, md) :: unsafe)],
              lits, vars, lim, assumptions} : search_branch) :: brs =>
            let
              exception PRV
              val mark = trailSize state
              val formula =
                withTrackedTerm (normAt mark (trackedTerm formula)) formula
              val rules = unsafeRulesFor vars (trackedTerm formula)
              val rule_count = lengthAt mark rules
              val branches = branchCountAt mark open_count brs0

              fun child (assumptionsFor, vars', pattern, requeued, negated,
                         lim')
                    (premise, hidden) =
                let
                  val _ = checkpointAt mark
                  val (tracked, introduced) =
                    premiseChild mark (premise, hidden)
                  val safe' = mapPairAt mark tracked
                  val unsafe' = requeued ()
                  val lits' =
                    if existsGoalAt mark premise then
                      negated ()
                    else lits
                  val pairs' =
                    if recursivePremiseAt mark pattern premise then
                      [(safe', unsafe')]
                    else [(safe', []), ([], unsafe')]
                  val child_assumptions = assumptionsFor introduced
                in
                  {pairs = pairs', lits = lits',
                   vars = vars', lim = lim',
                   assumptions = child_assumptions}
                end

              fun fire {rule : tableau_rule, other, updated, limAfter, next} =
                let
                  val pattern = #pattern rule
                  val prems = #premises rule
                  val old_vars = varsInVarsAt mark vars
                  val new_vars = foldPremVarsAt mark prems old_vars
                  val duplicate = md
                  val lim' = limAfter (lim - 1)
                  val undo =
                    mayUndoAt mark
                      {other_rules = not (null other),
                       updated = updated,
                       old_vars = old_vars,
                       new_vars = new_vars}
                  val major =
                    ruleMajor unsafeRuleOrigin rule formula assumptions
                  val step =
                    UnsafeRule
                      {rule = rule, updated = updated,
                       duplicate = duplicate, major = major}
                  val contraposing =
                    contraposing mark formula prems (lits, [])

                  fun descend () =
                    if killsAllAlternatives lim' prems then
                      (rollbackAt mark; raise NEWBRANCHES)
                    else
                      let
                        val children =
                          if null prems then brs
                          else
                            let
                              val assumptionsFor =
                                childAssumptions unsafeChildOrigin rule
                                  duplicate formula assumptions
                              val requeued = shareForPremises prems (fn () =>
                                requeueGammaAt mark (formula, md) unsafe
                                  duplicate)
                              val negated = shareForPremises prems (fn () =>
                                mapNegLitsAt mark lits)
                            in
                              premiseBranches rule
                                (child
                                   (assumptionsFor, new_vars, pattern,
                                    requeued, negated, lim'))
                                brs prems
                            end
                        val count = lengthAt mark prems
                      in
                        noteRuleInference lim';
                        if null prems then closed := !closed + 1
                        else created := !created + count - 1;
                        prv
                          (step :: tacs, remember brs0 trace,
                           Choice (mark, branches, PRV) :: choices,
                           branches + count - 1,
                           children)
                      end
                in
                  if contraposing then
                    prv
                      (DeferGoal :: tacs, remember brs0 trace, choices,
                       open_count,
                       contraposedBranch mark
                         {lits = lits, levels = [],
                          restore = fn _ => [([], (formula, md) :: unsafe)],
                          vars = vars, lim = lim,
                          assumptions = assumptions} :: brs)
                  else
                    preserve
                      (fn PRV =>
                            SOME (fn () =>
                              if undo then next () else backtrack choices)
                        | _ => NONE)
                      descend
                end

              val deeper =
                tryRules
                  {mark = mark, formula = formula, lim = lim,
                   rule_count = rule_count,
                   noteAttempt = noteUnsafeRuleAttempt, fire = fire}

            in
              if lim < 1 then backtrack choices
              else
                preserve
                  (fn NEWBRANCHES =>
                        SOME (fn () =>
                          prv
                            (tacs, remember brs0 trace, choices, open_count,
                             {pairs = [([], unsafe)],
                              lits = formula :: lits,
                              vars = vars, lim = lim,
                              assumptions = assumptions} :: brs))
                    | _ => NONE)
                  (fn () => deeper rules)
            end
        | _ :: _ => backtrack choices)
      handle searchBudget.LimitReached (kind, usage) =>
        if resumable then
          (clearTo state entry_mark;
           suspended_limit := SOME (kind, usage);
           suspended :=
             SOME (fn () => prv (tacs, trace, choices, open_count, brs));
           raise YIELDED)
        else raise searchBudget.LimitReached (kind, usage)
      end

    fun report completion result =
      let
        val (inferences, maximum_resource_cost, fullTrace, phase) =
          instrumentationResult ()
        val statistics =
          {configured_depth = depth,
           maximum_resource_cost = maximum_resource_cost,
           inferences_performed = inferences,
           branches_created = !created,
           branches_closed = !closed,
           choices_pruned = !pruned,
           rule_cache_hits = blastRule.hitCount rule_cache,
           rule_conversions = blastRule.conversionCount rule_cache,
           remaining_trail_assignments = trailSize state,
           phase = phase}
        val _ =
          searchWork.note_tableau
            {depth = depth, branches = !created,
             inferences = inferences}
      in
        RunDone
          {completion = completion, fullTrace = fullTrace,
           result = result, statistics = statistics}
      end

    fun execute work =
      (report Completed (SOME (work ()))
       handle PROVE => report Completed NONE
            | INTERRUPTED =>
                (cleanupRun INTERRUPTED;
                 report Interrupted NONE)
            | YIELDED =>
                let
                  val (kind, usage) = valOf (!suspended_limit)
                  val next = valOf (!suspended)
                in
                  RunYielded
                    {kind = kind, usage = usage,
                     trail_assignments = trailSize state,
                     resume = fn () => execute next}
                end
            | STOP_EXCEPTION exn => (cleanupRun exn; raise exn)
            | exn => (cleanupRun exn; raise exn))
  in
    case prepared of
        NONE => report Interrupted NONE
      | SOME formulas =>
          execute
            (fn () =>
              let val initial = initialBranchOf (formulas, depth)
              in
                prv
                  ([], [], [Choice (trailSize state, 1, PROVE)], 1,
                   [initial])
              end)
  end

(* Every entry point runs at the blast.trace level of the context
   given. *)
fun searchGoalMeasured ctxt {debug, stop} claset depth goal cont =
  case runGoal (traceUtil.level_of blastRule.tracer ctxt)
         {keep_history = true, resumable = false} AbandonOwned
         (On {debug = debug, stop = stop, budget = NONE})
         claset depth goal cont of
      RunDone report => report
    | RunYielded _ => raise Fail "unbudgeted tableau yielded"

fun search_goal_budgeted keep_history ctxt budget claset depth goal cont =
  let
    val report =
      runGoal (traceUtil.level_of blastRule.tracer ctxt)
        {keep_history = keep_history, resumable = false} Restore
        (On {debug = false, stop = fn () => false,
             budget = SOME budget}) claset depth goal cont
  in
    case report of
        RunDone finished =>
          BudgetFinished
            {result = #result finished,
             statistics = #statistics finished}
      | RunYielded _ =>
          raise Fail "one-shot tableau yielded"
  end
  handle searchBudget.LimitReached (kind, usage) =>
    BudgetLimitReached {kind = kind, usage = usage}

fun searchGoalBudgeted ctxt = search_goal_budgeted true ctxt

fun searchGoalBudgetedForReplay ctxt = search_goal_budgeted false ctxt

fun search_goal_resumable keep_history ctxt budget claset depth goal cont =
  let
    val trace_level = traceUtil.level_of blastRule.tracer ctxt
    fun once resume =
      let val used = ref false
      in
        fn () =>
          if !used then
            raise Fail
              "blastSearch.searchGoalResumable: continuation already used"
          else (used := true; resume ())
      end
    fun convert (RunDone report) =
          BudgetFinished
            {result = #result report,
             statistics = #statistics report}
      | convert (RunYielded
                   {kind, usage, trail_assignments, resume}) =
          BudgetYielded
            {kind = kind, usage = usage,
             trail_assignments = trail_assignments,
             resume = once (fn () => convert (resume ()))}
    fun start () =
      convert
        (runGoal trace_level
           {keep_history = keep_history, resumable = true} Restore
           (On {debug = false, stop = fn () => false,
                budget = SOME budget}) claset depth goal cont)
      handle searchBudget.LimitReached (kind, usage) =>
        BudgetYielded
          {kind = kind, usage = usage, trail_assignments = 0,
           resume = once start}
  in
    start ()
  end

fun searchGoalResumable ctxt = search_goal_resumable true ctxt

fun searchGoalResumableForReplay ctxt = search_goal_resumable false ctxt

fun search_with_stats keep_history ctxt claset depth goal cont =
  let
    val report =
      runGoal (traceUtil.level_of blastRule.tracer ctxt)
        {keep_history = keep_history, resumable = false} Restore Stats
        claset depth goal cont
  in
    case report of
        RunDone finished =>
          {result = #result finished,
           statistics = #statistics finished}
      | RunYielded _ => raise Fail "statistics tableau yielded"
  end

fun searchGoalWithStats ctxt = search_with_stats true ctxt

fun searchGoalForReplay ctxt = search_with_stats false ctxt

(* Keep the inference and resource-cost counters for the shared work meter. *)
fun searchGoal ctxt claset depth goal cont =
  #result (searchGoalWithStats ctxt claset depth goal cont)

fun tryGoal ctxt claset depth goal =
  searchGoal ctxt claset depth goal (fn proof => proof)

fun debugGoal ctxt claset depth goal =
  let
    val report =
      searchGoalMeasured ctxt {debug = true, stop = fn () => false}
        claset depth goal (fn proof => proof)
  in
    {fullTrace = #fullTrace report, result = #result report}
  end

(* This legacy iterative-deepening API has no cooperative timeout: each
   fixed-depth run is bounded only by its resource limit, while the
   sequence of runs is capped by depth_limit.  Callers that need
   cooperative interruption use the measured fixed-depth APIs. *)
fun deepenGoal ctxt claset goal cont =
  let
    val limit = !depth_limit
    fun deepen depth =
      if depth > limit then NONE
      else
        case searchGoal ctxt claset depth goal cont of
            NONE => deepen (depth + 1)
          | result => result
  in
    deepen 0
  end

end
