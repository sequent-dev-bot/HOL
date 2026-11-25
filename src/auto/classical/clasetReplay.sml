structure clasetReplay :> clasetReplay =
struct

open Abbrev HolKernel boolSyntax

val tracer =
  traceUtil.create
    {group = "classical", max = 7,
     emit = fn m => Feedback.HOL_MESG ("Classical reasoner: " ^ m)}

datatype rule_variant = Plain | Swapped | Duplicate | MakeElim

datatype hyp_subst_side = EliminateLeft | EliminateRight

datatype hyp_subst_elimination =
    DeleteReflexive of int
  | SubstituteAt of {position : int, side : hyp_subst_side}

datatype step_kind =
    Assumption of int
  | Contradiction of int * int
  | ModusPonens of {implication : int, antecedent : int}
  | RuleApplication of
      {original : thm, theorem : thm, variant : rule_variant,
       elim : bool}
  | Disch
  | Gen
  | SplitPaired
  | HypSubst
  | CContr
  | SwappedBuiltin of int
  | MoveAssumptionToBack of int
  | Wrapper

type created =
  {terms : clasetMeta.meta list, types : clasetMeta.tymeta list}
type exact_prefix_descriptor = {foralls : int, implications : int}
type exact_prefix_rebuild =
  {fresh : term list, assumptions : term list, premise : term}
type replay_action = clasetMeta.store -> tactic

datatype step_record =
  StepRecord of
    {kind : step_kind,
     target : int,
     consumed : int option,
     created : created,
     eigenvariables : string list list,
     validation : validation,
     action : replay_action,
     children : step_record option list}

datatype script =
  Script of
    {records : step_record list,
     length : int,
     open_goals : int}
datatype grounded_script =
  Grounded of {store : clasetMeta.store, script : script}

datatype replay_failure =
  ReplayFailure of
    {goal : goal, step : step_kind option, message : string,
     script : string}
datatype replay_outcome =
    Replayed of goal list * validation
  | ReplayFailed of replay_failure

fun make_record fields = StepRecord fields

fun new_free_names _ [] = []
  | new_free_names (asl, w) goals =
      let
        val old_frees = FVLset (w :: asl)
        fun names (child_asl, child_w) =
          map (fst o dest_var)
            (List.filter
              (fn variable => not (HOLset.member (old_frees, variable)))
              (free_varsl (child_w :: child_asl)))
      in
        map names goals
      end
fun kind_of (StepRecord {kind, ...}) = kind
fun target_of (StepRecord {target, ...}) = target
fun consumed_of (StepRecord {consumed, ...}) = consumed
fun created_of (StepRecord {created, ...}) = created
fun validation_of (StepRecord {validation, ...}) = validation
fun children_of (StepRecord {children, ...}) = children
fun action_of (StepRecord {action, ...}) = action

fun eigenvariables_of (StepRecord {eigenvariables, ...}) =
  List.concat eigenvariables

fun nth1 function_name =
  clasetNorm.nth1 ("clasetReplay", function_name)

fun delete_nth function_name =
  clasetNorm.delete_nth ("clasetReplay", function_name)

(* Replay reproduces what the search did, so it shapes terms exactly as the
   search shaped them: beta and eta, and no membership crossing.  Where the
   search crossed [x IN P] against [P x] it did so to compare two forms, and
   replay meets that with [clasetNorm.align_conclusion] at the same places. *)
val normalize_conv = clasetNorm.reduce_conv
val normalize_thm = clasetNorm.normalize_thm

fun restore_target function_name target normalized_target theorem =
  let
    val conclusion = concl theorem
    val aligned =
      if aconv conclusion normalized_target then
        EQ_MP (ALPHA conclusion normalized_target) theorem
      else
        raise mk_HOL_ERR "clasetReplay" function_name
          "the produced theorem misses the normalized target"
  in
    clasetNorm.align_conclusion target aligned
      handle HOL_ERR _ =>
        raise mk_HOL_ERR "clasetReplay" function_name
          "the normalized target cannot be restored exactly"
  end

val normalize_rule_thm = clasetNorm.normalize_rule_thm

fun split_imp_prefix function_name arity tm =
  clasetNorm.split_imp_prefix ("clasetReplay", function_name) arity tm

fun assumption_thm store asm target =
  let
    val asm' = clasetMeta.norm store asm
    val target' = clasetMeta.norm store target
    val assumption =
      if aconv asm' asm then ASSUME asm
      else
        let val asm_equality = normalize_conv asm
        in
          if aconv asm' (rhs (concl asm_equality)) then
            EQ_MP asm_equality (ASSUME asm)
          else
            raise mk_HOL_ERR "clasetReplay" "ASSUMPTION_TAC"
              "the normalized assumption cannot be restored exactly"
        end
    val normalized = normalize_thm assumption
    val closing =
      clasetNorm.align_conclusion target' normalized
        handle HOL_ERR _ =>
          raise mk_HOL_ERR "clasetReplay" "ASSUMPTION_TAC"
            "the selected assumption does not close the goal"
  in
    restore_target "ASSUMPTION_TAC" target target' closing
  end

fun assumption_validation prove [] = prove ()
  | assumption_validation _ _ =
      raise mk_HOL_ERR "clasetReplay" "ASSUMPTION_TAC"
        "validation received child theorems"

fun ASSUMPTION_TAC store pos (asl, w) _ =
  let val asm = nth1 "ASSUMPTION_TAC" asl pos
  in ([], assumption_validation (fn () => assumption_thm store asm w)) end

fun CONTRADICTION_TAC store (negative_pos, positive_pos) (asl, w) _ =
  let
    val negative = nth1 "CONTRADICTION_TAC" asl negative_pos
    val positive = nth1 "CONTRADICTION_TAC" asl positive_pos
    val negative' = clasetMeta.norm store negative
    val proposition = dest_neg negative'
    val normalized_target = clasetMeta.norm store w
    fun validation [] =
          let
            val nthm = assumption_thm store negative negative'
            val pthm = assumption_thm store positive proposition
            val contradiction =
              Drule.CONTR normalized_target
                (MP (NOT_ELIM nthm) pthm)
          in
            restore_target "CONTRADICTION_TAC" w normalized_target
              contradiction
          end
      | validation _ =
          raise mk_HOL_ERR "clasetReplay" "CONTRADICTION_TAC"
            "validation received child theorems"
  in
    ([], validation)
  end

fun MP_TAC store {implication, antecedent} (asl, w) _ =
  let
    val implication_tm = nth1 "MP_TAC" asl implication
    val antecedent_tm = nth1 "MP_TAC" asl antecedent
    val implication' = clasetMeta.norm store implication_tm
    val (premise, consequence) = dest_imp_only implication'
    val child = (consequence :: delete_nth "MP_TAC" asl implication, w)

    fun validation [child_thm] =
          let
            val ithm = assumption_thm store implication_tm implication'
            val athm = assumption_thm store antecedent_tm premise
            val consequence_thm = MP ithm athm
          in
            Drule.PROVE_HYP consequence_thm child_thm
          end
      | validation _ =
          raise mk_HOL_ERR "clasetReplay" "MP_TAC"
            "validation received the wrong number of theorems"
  in
    ([child], validation)
  end

fun cons_assumptions assumptions asl =
  List.foldl (fn (asm, current) => asm :: current) asl assumptions

fun exact_prefix_descriptor premise =
  let
    val (bounds, body) = strip_forall premise
    val (assumptions, _) = strip_imp_only body
  in
    {foralls = length bounds, implications = length assumptions}
  end

fun split_foralls function_name count premise =
  let
    fun split 0 rev_bounds body = (List.rev rev_bounds, body)
      | split remaining rev_bounds body =
          (case total dest_forall body of
               SOME (bound, rest) =>
                 split (remaining - 1) (bound :: rev_bounds) rest
             | NONE =>
                 raise mk_HOL_ERR "clasetReplay" function_name
                   "the instantiated premise has too few foralls")
  in
    if count < 0 then
      raise mk_HOL_ERR "clasetReplay" function_name
        "negative forall-prefix arity"
    else split count [] premise
  end

fun exact_prefix_bounds
      ({foralls, implications} : exact_prefix_descriptor) premise =
  let
    val _ =
      if implications < 0 then
        raise mk_HOL_ERR "clasetReplay" "exact_prefix_bounds"
          "negative implication-prefix arity"
      else ()
    val (bounds, _) =
      split_foralls "exact_prefix_bounds" foralls premise
  in
    bounds
  end

fun split_exact_prefix
      {descriptor = {foralls, implications}, premise, fresh} =
  let
    val (bounds, body) =
      split_foralls "split_exact_prefix" foralls premise
    val _ =
      if implications < 0 then
        raise mk_HOL_ERR "clasetReplay" "split_exact_prefix"
          "negative implication-prefix arity"
      else if length bounds <> length fresh then
        raise mk_HOL_ERR "clasetReplay" "split_exact_prefix"
          "fresh-parameter arity differs from the descriptor"
      else if
        ListPair.allEq
          (fn (bound, variable) =>
            is_var variable andalso type_of bound = type_of variable)
          (bounds, fresh)
      then ()
      else
        raise mk_HOL_ERR "clasetReplay" "split_exact_prefix"
          "a fresh parameter has the wrong type"
    val substitution =
      ListPair.map
        (fn (bound, variable) => {redex = bound, residue = variable})
        (bounds, fresh)
    val body' = Term.subst substitution body
    val (assumptions, residual) =
      split_imp_prefix "split_exact_prefix" implications body'
    val rebuild =
      {fresh = fresh, assumptions = assumptions, premise = premise}
  in
    {assumptions = assumptions, residual = residual, rebuild = rebuild}
  end

fun rebuild_exact_prefix
      ({fresh, assumptions, premise} : exact_prefix_rebuild) child_thm =
  let
    val discharged =
      List.foldr (fn (assumption, th) => DISCH assumption th)
        child_thm assumptions
    val generalized = GENL fresh discharged
  in
    EQ_MP (ALPHA (concl generalized) premise) generalized
  end

fun rule_child function_name parent_asl premise names descriptor =
  let
    val bounds = exact_prefix_bounds descriptor premise
    val _ =
      if length bounds = length names then ()
      else
        raise mk_HOL_ERR "clasetReplay" function_name
          "recorded eigenvariable arity is corrupt"
    val fresh =
      ListPair.map
        (fn (bound, name) => mk_var (name, type_of bound))
        (bounds, names)
    val {assumptions, residual, rebuild} =
      split_exact_prefix
        {descriptor = descriptor, premise = premise, fresh = fresh}
  in
    ((cons_assumptions assumptions parent_asl, residual), rebuild)
  end

val normalize_assumption = clasetNorm.normalize_assumption

fun theorem_hypothesis normalized_asl hypothesis =
  case List.find (fn (normalized, _) => aconv normalized hypothesis)
    normalized_asl
  of
      SOME (_, theorem) => theorem
    | NONE =>
        raise mk_HOL_ERR "clasetReplay" "RULE_TAC"
          "a theorem hypothesis is absent from the goal"

fun rule_tac_with function_name make_children
    {theorem, elim, consumed, parameters, eigenvariables} (asl, w) =
  let
    val rule0 = normalize_rule_thm theorem
    val reduced_target = rhs (concl (normalize_conv w))
    val recorded_arity =
      length eigenvariables + (if elim then 1 else 0)
    val (_, initial_conclusion) =
      split_imp_prefix function_name recorded_arity (concl rule0)
    (* The search may have matched this rule across the membership crossing,
       in which case only the form the rule was stated in matches here.  The
       goal as it stands is tried first, so an ordinary replay is untouched;
       [restore_target] carries the result back to [w] either way. *)
    val (normalized_target, term_substitution, type_substitution) =
      case total (Term.match_term initial_conclusion) reduced_target of
          SOME (terms, types) => (reduced_target, terms, types)
        | NONE =>
            let
              val crossed =
                rhs (concl (clasetNorm.membership_conv reduced_target))
              val (terms, types) =
                Term.match_term initial_conclusion crossed
            in
              (crossed, terms, types)
            end
    fun allowed_parameter {redex, residue} =
      is_var redex andalso is_var residue andalso
      tmem redex parameters
    val _ =
      if List.all allowed_parameter term_substitution then ()
      else
        raise mk_HOL_ERR "clasetReplay" function_name
          "conclusion alignment would instantiate a rigid variable"
    val aligned_rule =
      Drule.INST_TY_TERM
        (term_substitution, type_substitution) rule0
    val normalized_asl = map normalize_assumption asl
    val rule =
      List.foldl
        (fn (hypothesis, current) =>
          Drule.PROVE_HYP
            (theorem_hypothesis normalized_asl hypothesis) current)
        aligned_rule (hyp aligned_rule)
    val (premises0, conclusion) =
      split_imp_prefix function_name recorded_arity (concl rule)
    val _ =
      if aconv conclusion normalized_target then ()
      else
        raise mk_HOL_ERR "clasetReplay" function_name
          ("the instantiated rule conclusion misses the goal: " ^
           Parse.term_to_string conclusion ^ " versus " ^
           Parse.term_to_string normalized_target)
    val (supplied, premises, parent_asl) =
      if elim then
        let
          val major_pos =
            case consumed of
                SOME pos => pos
              | NONE =>
                  raise mk_HOL_ERR "clasetReplay" function_name
                    "an elimination record has no consumed assumption"
          val major = nth1 function_name asl major_pos
          val rule_major = hd premises0
          val (_, major_thm) =
            normalize_assumption major
          val major_thm =
            clasetNorm.align_conclusion rule_major major_thm
              handle HOL_ERR _ =>
                raise mk_HOL_ERR "clasetReplay" function_name
                  "the selected assumption misses the major premise"
        in
          ([major_thm], tl premises0,
           delete_nth function_name asl major_pos)
        end
      else ([], premises0, asl)
    val _ =
      if length premises = length eigenvariables then ()
      else
        raise mk_HOL_ERR "clasetReplay" function_name
          "recorded child arity is corrupt"
    val child_data = make_children parent_asl premises eigenvariables
    val child_goals = map #1 child_data
    val rebuild_data = map #2 child_data

    fun validation child_thms =
      if length child_thms <> length premises then
        raise mk_HOL_ERR "clasetReplay" function_name
          "validation received the wrong number of theorems"
      else
        let
          val premise_thms =
            ListPair.map
              (fn (data, theorem) =>
                rebuild_exact_prefix data theorem)
              (rebuild_data, child_thms)
          val result0 = Drule.LIST_MP (supplied @ premise_thms) rule
        in
          restore_target function_name w normalized_target result0
        end
  in
    (child_goals, validation)
  end
  handle Empty =>
    raise mk_HOL_ERR "clasetReplay" function_name
      "an elimination rule has no major premise"

(* The whole forall-then-implication prefix of each premise. *)
fun ordinary_rule_children parent_asl premises eigenvariables =
  ListPair.map
    (fn (premise, names) =>
      rule_child "RULE_TAC" parent_asl premise names
        (exact_prefix_descriptor premise))
    (premises, eigenvariables)

fun RULE_TAC fields goal _ =
  rule_tac_with "RULE_TAC" ordinary_rule_children fields goal

fun FORWARD_RULE_TAC {theorem, immediate, assumptions} (asl, w) _ =
  let
    val function_name = "FORWARD_RULE_TAC"
    val rule0 = normalize_rule_thm theorem
    val (premises, _) = strip_imp_only (concl rule0)
    val _ =
      if immediate > 0 andalso immediate <= length premises then ()
      else
        raise mk_HOL_ERR "clasetReplay" function_name
          "the immediate-premise count is out of range"
    val _ =
      if length assumptions = immediate then ()
      else
        raise mk_HOL_ERR "clasetReplay" function_name
          "the recorded assumption arity is corrupt"
    val normalized_asl = map normalize_assumption asl
    val rule =
      List.foldl
        (fn (hypothesis, current) =>
          Drule.PROVE_HYP
            (theorem_hypothesis normalized_asl hypothesis) current)
        rule0 (hyp rule0)

    fun premise_thm (premise, position) =
      let
        val assumption = nth1 function_name asl position
        val (normalized, theorem) = normalize_assumption assumption
      in
        if aconv normalized premise then theorem
        else
          raise mk_HOL_ERR "clasetReplay" function_name
            "a selected assumption misses its immediate premise"
      end

    val supplied =
      ListPair.map premise_thm
        (List.take (premises, immediate), assumptions)
    val forward = Drule.LIST_MP supplied rule
    val added = concl forward
    val child = (added :: asl, w)

    fun validation [child_thm] = Drule.PROVE_HYP forward child_thm
      | validation _ =
          raise mk_HOL_ERR "clasetReplay" function_name
            "validation received the wrong number of theorems"
  in
    ([child], validation)
  end

fun BLAST_RULE_TAC
    {theorem, elim, consumed, parameters, eigenvariables, prefixes} =
  let
    fun make_children parent_asl premises names =
      if length premises = length prefixes then
        ListPair.map
          (fn ((premise, child_names), descriptor) =>
            rule_child "BLAST_RULE_TAC" parent_asl premise child_names
              descriptor)
          (ListPair.zip (premises, names), prefixes)
      else
        raise mk_HOL_ERR "clasetReplay" "BLAST_RULE_TAC"
          "recorded prefix-descriptor arity is corrupt"
  in
    fn goal => fn _ =>
      rule_tac_with "BLAST_RULE_TAC" make_children
        {theorem = theorem, elim = elim, consumed = consumed,
         parameters = parameters, eigenvariables = eigenvariables} goal
  end

(* The classical hyp-subst step saturates, and stops where the equality it
   reached is one the search may not use.  Replay runs against a grounded
   goal, and a binding the search chose after the step can have made that
   equality usable after all: saturating afresh there eliminates what the
   recorded step left standing, and the step recorded against the residue
   then finds nothing to do.  So which equalities a step eliminated is part
   of the record, the way the substituted side already is for blast, and a
   replay repeats exactly those. *)
fun reflexive_equality tm =
  case total dest_eq tm of
      SOME (left, right) => if aconv left right then SOME left else NONE
    | NONE => NONE

fun carries_meta tm =
  List.exists clasetMeta.is_meta (free_vars tm) orelse
  List.exists clasetMeta.is_tymeta (type_vars_in_term tm)

(* src/Provers/hypsubst.ML:83 @ Isabelle2025-2 refuses an equality with a
   schematic variable on either side.  Engine metavariables are the
   analogue, and the eliminated side is not the only one that matters:
   replacing a goal variable by a metavariable restates the branch over
   an unknown the search has not chosen yet, and drops the assumptions
   the sibling branches are stated over. *)
fun subst_orientation equality =
  if carries_meta equality then NONE
  else
    case total dest_eq equality of
        NONE => NONE
      | SOME (left, right) =>
          if is_var left andalso not (free_in left right)
          then SOME (EliminateLeft, left, right, ASSUME equality)
          else if is_var right andalso not (free_in right left)
          then SOME (EliminateRight, right, left, SYM (ASSUME equality))
          else NONE

fun hyp_subst_elimination position equality =
  case reflexive_equality equality of
      SOME _ => SOME (DeleteReflexive position)
    | NONE =>
        (case subst_orientation equality of
             SOME (side, _, _, _) =>
               SOME (SubstituteAt {position = position, side = side})
           | NONE => NONE)

fun first_hyp_subst_elimination asl =
  let
    fun search _ [] = NONE
      | search position (equality :: rest) =
          (case hyp_subst_elimination position equality of
               SOME elimination => SOME elimination
             | NONE => search (position + 1) rest)
  in
    search 1 asl
  end

fun single_child function_name [child] = child
  | single_child function_name _ =
      raise mk_HOL_ERR "clasetReplay" function_name
        "elimination did not produce one child"

fun single_theorem function_name [theorem] = theorem
  | single_theorem function_name _ =
      raise mk_HOL_ERR "clasetReplay" function_name
        "validation received the wrong number of theorems"

fun claset_hyp_subst_once (DeleteReflexive position) (asl, w) _ =
      let
        val equality = nth1 "CLASET_HYP_SUBST_TAC_AT" asl position
        val reflexive =
          case reflexive_equality equality of
              SOME term => term
            | NONE =>
                raise mk_HOL_ERR "clasetReplay" "CLASET_HYP_SUBST_TAC_AT"
                  "recorded assumption is not a reflexive equality"
        val child =
          (delete_nth "CLASET_HYP_SUBST_TAC_AT" asl position, w)
        fun validation theorems =
          Drule.PROVE_HYP (REFL reflexive)
            (single_theorem "CLASET_HYP_SUBST_TAC_AT" theorems)
      in
        ([child], validation)
      end
  | claset_hyp_subst_once (SubstituteAt {position, side}) (asl, w) ctxt =
      let
        val equality = nth1 "CLASET_HYP_SUBST_TAC_AT" asl position
        val equality_thm =
          case subst_orientation equality of
              SOME (oriented, _, _, theorem) =>
                if oriented = side then theorem
                else
                  raise mk_HOL_ERR "clasetReplay" "CLASET_HYP_SUBST_TAC_AT"
                    "recorded assumption substitutes the other side"
            | NONE =>
                raise mk_HOL_ERR "clasetReplay" "CLASET_HYP_SUBST_TAC_AT"
                  "recorded assumption is not a substitutable equality"
      in
        Tactic.SUBST_ALL_TAC equality_thm
          (delete_nth "CLASET_HYP_SUBST_TAC_AT" asl position, w) ctxt
      end

fun claset_hyp_subst_along function_name [] goal _ =
      ([goal], single_theorem function_name)
  | claset_hyp_subst_along function_name (elimination :: rest) goal ctxt =
      let
        val (children, validation) =
          claset_hyp_subst_once elimination goal ctxt
        val child = single_child function_name children
        val (goals, residual) =
          claset_hyp_subst_along function_name rest child ctxt
      in
        (goals, fn theorems => validation [residual theorems])
      end

fun CLASET_HYP_SUBST_TAC_AT eliminations goal ctxt =
  if List.null eliminations then
    raise mk_HOL_ERR "clasetReplay" "CLASET_HYP_SUBST_TAC_AT"
      "the recorded step eliminates nothing"
  else
    claset_hyp_subst_along "CLASET_HYP_SUBST_TAC_AT" eliminations goal ctxt

fun COMPUTE_CLASET_HYP_SUBST_TAC_IN ctxt goal =
  let
    fun saturate (goal as (asl, _)) =
      case first_hyp_subst_elimination asl of
          NONE =>
            ([],
             ([goal], single_theorem "COMPUTE_CLASET_HYP_SUBST_TAC"))
        | SOME elimination =>
            let
              val (children, validation) =
                claset_hyp_subst_once elimination goal ctxt
              val child =
                single_child "COMPUTE_CLASET_HYP_SUBST_TAC" children
              val (rest, (goals, residual)) = saturate child
            in
              (elimination :: rest,
               (goals, fn theorems => validation [residual theorems]))
            end
  in
    case saturate goal of
        ([], _) =>
          raise mk_HOL_ERR "clasetReplay" "COMPUTE_CLASET_HYP_SUBST_TAC"
            "no substitutable equality"
      | computed => computed
  end

(* Blast records one equality substitution at a time.  Unlike the classical
   hyp-subst slot, affected assumptions are stably moved to the front. *)
fun eta_atom_conv tm =
  case total Drule.ETA_CONV tm of
      NONE => REFL tm
    | SOME theorem =>
        TRANS theorem (eta_atom_conv (rhs (concl theorem)))

(* The side a substitution eliminates is part of the recorded step, and is
   preferred here over the default left-first choice: an equality whose
   metavariable was instantiated after the step was recorded has two
   substitutable sides where it had one, and choosing afresh then reverses
   the substitution the rest of the script was recorded against.  It is a
   preference and not a constraint because the search sees a beta-reduced
   equality where the goal has a redex, so the recorded side can be
   unsubstitutable here -- and then the other side is the only choice. *)
fun blast_hyp_orientation_for recorded equality =
  let
    val equality_conversion =
      Conv.THENC
        (Conv.LAND_CONV eta_atom_conv,
         Conv.RAND_CONV eta_atom_conv) equality
    val contracted = rhs (concl equality_conversion)
    val contracted_thm = EQ_MP equality_conversion (ASSUME equality)
  in
    case total dest_eq contracted of
        NONE => NONE
      | SOME (left, right) =>
          let
            fun suitable variable other =
              is_var variable andalso
              not (clasetMeta.is_meta variable) andalso
              not (free_in variable other)
            val eliminate_left =
              SOME (EliminateLeft, left, right, contracted_thm)
            val eliminate_right =
              SOME (EliminateRight, right, left, SYM contracted_thm)
            fun first_suitable [] = NONE
              | first_suitable (EliminateLeft :: rest) =
                  if suitable left right then eliminate_left
                  else first_suitable rest
              | first_suitable (EliminateRight :: rest) =
                  if suitable right left then eliminate_right
                  else first_suitable rest
            fun preference NONE = [EliminateLeft, EliminateRight]
              | preference (SOME EliminateLeft) =
                  [EliminateLeft, EliminateRight]
              | preference (SOME EliminateRight) =
                  [EliminateRight, EliminateLeft]
          in
            first_suitable (preference recorded)
          end
  end

fun blast_hyp_orientation equality =
  case blast_hyp_orientation_for NONE equality of
      NONE => NONE
    | SOME (_, old, replacement, equality_thm) =>
        SOME (old, replacement, equality_thm)

fun blast_hyp_subst_tac_at position recorded (asl, w) ctxt =
  let
    val equality = nth1 "BLAST_HYP_SUBST_TAC_AT" asl position
    val recorded_changed = Option.map #changed recorded
    val (side, old, replacement, equality_thm) =
      case blast_hyp_orientation_for (Option.map #side recorded) equality of
          SOME oriented => oriented
        | NONE =>
            raise mk_HOL_ERR "clasetReplay" "BLAST_HYP_SUBST_TAC_AT"
              "selected assumption is not a suitable equality"
    val remaining =
      delete_nth "BLAST_HYP_SUBST_TAC_AT" asl position
    val substitution = [{redex = old, residue = replacement}]
    fun substituted tm = Term.subst substitution tm
    fun affected tm = not (aconv (substituted tm) tm)
    val changed_mask =
      case recorded_changed of
          NONE => map affected remaining
        | SOME mask =>
            if length mask = length remaining then mask
            else
              raise mk_HOL_ERR "clasetReplay"
                "BLAST_HYP_SUBST_TAC_AT"
                "recorded changed mask has the wrong length"
    fun partition [] [] changed unchanged =
          (List.rev changed, List.rev unchanged)
      | partition (true :: flags) (tm :: terms) changed unchanged =
          partition flags terms (tm :: changed) unchanged
      | partition (false :: flags) (tm :: terms) changed unchanged =
          partition flags terms changed (tm :: unchanged)
      | partition _ _ _ _ =
          raise mk_HOL_ERR "clasetReplay" "BLAST_HYP_SUBST_TAC_AT"
            "recorded changed mask has the wrong length"
    val (changed, unchanged) =
      partition changed_mask remaining [] []
    val reordered = map substituted (changed @ unchanged)
    val target = substituted w
    val target_equality = normalize_conv w
    val normalized_target = rhs (concl target_equality)
    val (children, validation0) =
      Tactic.SUBST_ALL_TAC equality_thm (remaining, w) ctxt
    val _ =
      case children of
          [_] => ()
        | _ =>
            raise mk_HOL_ERR "clasetReplay" "BLAST_HYP_SUBST_TAC_AT"
              "substitution did not produce one child"

    fun validation [child_thm] =
          let
            val result0 = validation0 [child_thm]
            val result_equality = normalize_conv (concl result0)
            val normalized_result = rhs (concl result_equality)
            val result = EQ_MP result_equality result0
          in
            if aconv normalized_result normalized_target then
              restore_target "BLAST_HYP_SUBST_TAC_AT" w
                normalized_target result
            else
              raise mk_HOL_ERR "clasetReplay"
                "BLAST_HYP_SUBST_TAC_AT"
                "substitution validation misses the original target"
          end
      | validation _ =
          raise mk_HOL_ERR "clasetReplay" "BLAST_HYP_SUBST_TAC_AT"
            "validation received the wrong number of theorems"
  in
    ({changed = changed_mask, side = side},
     ([(reordered, target)], validation))
  end

fun BLAST_HYP_SUBST_TAC_AT {position, changed, side} goal ctxt =
  #2 (blast_hyp_subst_tac_at position
        (SOME {changed = changed, side = side}) goal ctxt)

fun COMPUTE_BLAST_HYP_SUBST_TAC_AT_IN ctxt position goal =
  blast_hyp_subst_tac_at position NONE goal ctxt

fun BLAST_HYP_SUBST_TAC (goal as (asl, _)) ctxt =
  let
    fun first _ [] =
          raise mk_HOL_ERR "clasetReplay" "BLAST_HYP_SUBST_TAC"
            "no suitable equality assumption"
      | first position (_ :: rest) =
          (#2 (blast_hyp_subst_tac_at position NONE goal ctxt)
           handle HOL_ERR _ => first (position + 1) rest)
  in
    first 1 asl
  end

fun eta_forall_predicate tm =
  case strip_comb tm of
      (head, [predicate]) =>
        (case total Type.dom_rng (type_of predicate) of
             SOME (domain, range) =>
               let
                 val bound = genvar domain
                 val forall_head = #1 (strip_comb (mk_forall (bound, T)))
               in
                 if range = bool andalso same_const head forall_head then
                   SOME (bound, predicate)
                 else NONE
               end
           | NONE => NONE)
    | _ => NONE

fun GEN_NAMED_TAC name (asl, w) ctxt =
  case total dest_forall w of
      SOME (bound, _) =>
        Tactic.X_GEN_TAC (mk_var (name, type_of bound)) (asl, w) ctxt
    | NONE =>
        (case eta_forall_predicate w of
             NONE =>
               raise mk_HOL_ERR "clasetReplay" "GEN_NAMED_TAC"
                 "goal is not universally quantified"
           | SOME (bound, predicate) =>
               let
                 val variable = mk_var (name, type_of bound)
                 val child = (asl, mk_comb (predicate, variable))

                 fun validation [child_thm] =
                       Conv.CONV_RULE
                         (Conv.RAND_CONV Drule.ETA_CONV)
                         (GEN variable child_thm)
                   | validation _ =
                       raise mk_HOL_ERR "clasetReplay" "GEN_NAMED_TAC"
                         "validation received the wrong number of theorems"
               in
                 ([child], validation)
               end)

(* src/HOL/Product_Type.thy:518 @ Isabelle2025-2 installs [split_all_tac]
   as a safe claset wrapper, so a parameter of product type is replaced by
   one parameter per component before any safe rule is tried.  HOL4 has no
   meta-quantifier: the parameter is a leading universal, and the same step
   is [FORALL_PROD] applied to the quantifier rather than to every subterm
   of the goal. *)
local
  fun split_conv term =
    if is_forall term then
      Conv.THENC
        (Conv.REPEATC (Conv.HO_REWR_CONV pairTheory.FORALL_PROD),
         Conv.TRY_CONV (Conv.BINDER_CONV split_conv))
        term
    else Conv.ALL_CONV term
in
  val SPLIT_PAIRED_TAC = Tactic.CONV_TAC (Conv.CHANGED_CONV split_conv)
end

(* The parameter case of the same step.  A product parameter reaches a
   subgoal already stripped -- a rule's own bound variable becomes an
   eigenvariable, never a universal the goal still carries -- so the
   split is a case analysis on the parameter, and it has to reach the
   assumptions it was stripped alongside. *)
fun SPLIT_PAIRED_VAR_TAC {variable, left, right} (goal as (asl, w)) ctxt =
  let
    val target =
      case List.find (fn free => fst (dest_var free) = variable)
        (free_varsl (w :: asl))
      of
          SOME free => free
        | NONE =>
            raise mk_HOL_ERR "clasetReplay" "SPLIT_PAIRED_VAR_TAC"
              "the parameter is not free in the goal"
    val (first_type, second_type) = pairSyntax.dest_prod (type_of target)
  in
    Thm_cont.X_CHOOSE_THEN (mk_var (left, first_type))
      (Thm_cont.X_CHOOSE_THEN (mk_var (right, second_type))
        Tactic.SUBST_ALL_TAC)
      (Drule.ISPEC target pairTheory.ABS_PAIR_THM) goal
      ctxt
  end

val GOAL_NEGATION_TAC = Tactic.CCONTR_TAC

fun SWAPPED_BUILTIN_TAC _ pos (asl, w) _ =
  let
    val negative = nth1 "SWAPPED_BUILTIN_TAC" asl pos
    val positive = dest_neg negative
    val child_asl =
      mk_neg w :: delete_nth "SWAPPED_BUILTIN_TAC" asl pos
    val child = (child_asl, positive)

    fun validation [positive_thm] =
          let
            val negative_thm = ASSUME negative
            val false_thm = MP (NOT_ELIM negative_thm) positive_thm
          in
            CCONTR w false_thm
          end
      | validation _ =
          raise mk_HOL_ERR "clasetReplay" "SWAPPED_BUILTIN_TAC"
            "validation received the wrong number of theorems"
  in
    ([child], validation)
  end

fun NORMALIZED_SWAPPED_BUILTIN_TAC _ pos (asl, w) _ =
  let
    fun normalize tm = rhs (concl (normalize_conv tm))

    fun prove_normalized asm target =
      let
        val equality = normalize_conv asm
        val theorem = EQ_MP equality (ASSUME asm)
      in
        if aconv (concl theorem) target then
          EQ_MP (ALPHA (concl theorem) target) theorem
        else
          raise mk_HOL_ERR "clasetReplay"
            "NORMALIZED_SWAPPED_BUILTIN_TAC"
            "replay normalization differs from search normalization"
      end

    val negative0 = nth1 "SWAPPED_BUILTIN_TAC" asl pos
    val negative = normalize negative0
    val positive = dest_neg negative
    val target = normalize w
    val remaining0 = delete_nth "SWAPPED_BUILTIN_TAC" asl pos
    val remaining = map normalize remaining0
    val child = (mk_neg target :: remaining, positive)

    fun validation [positive_thm] =
          let
            val restored =
              ListPair.foldlEq
                (fn (original, normalized, theorem) =>
                  Drule.PROVE_HYP
                    (prove_normalized original normalized) theorem)
                positive_thm (remaining0, remaining)
            val negative_thm = prove_normalized negative0 negative
            val false_thm = MP (NOT_ELIM negative_thm) restored
            val result = CCONTR target false_thm
            val target_equality = normalize_conv w
          in
            EQ_MP (SYM target_equality) result
          end
      | validation _ =
          raise mk_HOL_ERR "clasetReplay" "SWAPPED_BUILTIN_TAC"
            "validation received the wrong number of theorems"
  in
    ([child], validation)
  end

fun MOVE_ASSUMPTION_TO_BACK_TAC pos (asl, w) _ =
  let
    val selected = nth1 "MOVE_ASSUMPTION_TO_BACK_TAC" asl pos
    val rest = delete_nth "MOVE_ASSUMPTION_TO_BACK_TAC" asl pos
    fun validation [theorem] = theorem
      | validation _ =
          raise mk_HOL_ERR "clasetReplay"
            "MOVE_ASSUMPTION_TO_BACK_TAC"
            "validation received the wrong number of theorems"
  in
    ([(rest @ [selected], w)], validation)
  end

(* Rule replay can introduce alpha-renamed eigenvariables in a different
   positional order from search.  Keep the recorded position when possible,
   but recover by the semantic closing condition if that position drifted. *)
fun assumption_action pos store (asl, w) =
  let
    val selected = nth1 "ASSUMPTION_TAC" asl pos
    val close = total (fn asm => assumption_thm store asm w)
    val theorem =
      case close selected of
          SOME theorem => theorem
        | NONE =>
            (case Lib.get_first close asl of
                 SOME theorem => theorem
               | NONE =>
                   raise mk_HOL_ERR "clasetReplay" "ASSUMPTION_TAC"
                     "no assumption closes the replay goal")
  in
    fn _ => ([], assumption_validation (fn () => theorem))
  end

(* Exact reconstruction must reject a stale occurrence selector. *)
fun strict_assumption_action pos store goal =
  ASSUMPTION_TAC store pos goal
fun contradiction_action positions store =
  CONTRADICTION_TAC store positions
fun mp_action positions store = MP_TAC store positions
fun rule_action make store = RULE_TAC (make store)
fun forward_rule_action make store =
  FORWARD_RULE_TAC (make store)
fun blast_rule_action make store = BLAST_RULE_TAC (make store)
fun claset_hyp_subst_action_at eliminations _ =
  CLASET_HYP_SUBST_TAC_AT eliminations
fun blast_hyp_subst_action_at fields _ =
  BLAST_HYP_SUBST_TAC_AT fields
val disch_action = fn _ => Tactic.DISCH_TAC
fun gen_action name _ = GEN_NAMED_TAC name
val split_paired_action = fn _ => SPLIT_PAIRED_TAC
fun split_paired_var_action names _ = SPLIT_PAIRED_VAR_TAC names
val goal_negation_action = fn _ => GOAL_NEGATION_TAC
fun swapped_builtin_action pos store =
  NORMALIZED_SWAPPED_BUILTIN_TAC store pos
fun move_assumption_to_back_action pos _ =
  MOVE_ASSUMPTION_TO_BACK_TAC pos

(* Opaque wrapper results mention the marked frees visible when the wrapper
   ran.  Replay may have grounded only some of them, so apply every binding
   the covering store already has to both the children and a theorem schema
   for the validation.  The schema makes instantiation happen before the
   opaque closure consumes the replayed child theorems. *)
fun grounded_fixed_action (goals, validation) store =
  let
    fun ground_goal (child_asl, child_w) =
      (map (clasetMeta.norm store) child_asl,
       clasetMeta.norm store child_w)
    val (type_subst, term_subst) = clasetMeta.collapse store

    fun package_term (child_asl, child_w) =
      List.foldr boolSyntax.mk_imp child_w child_asl

    fun assume_package (child as (child_asl, _)) =
      let
        fun apply_assumptions [] theorem = theorem
          | apply_assumptions (asm :: rest) theorem =
              apply_assumptions rest (MP theorem (ASSUME asm))
      in
        apply_assumptions child_asl (ASSUME (package_term child))
      end

    val validation_schema = validation (map assume_package goals)
    val grounded_schema =
      Drule.INST_TY_TERM (term_subst, type_subst) validation_schema
    val grounded_goals = map ground_goal goals

    fun ground_validation theorems =
      let
        fun package_theorem ((child_asl, _), theorem) =
          List.foldr (fn (asm, result) => DISCH asm result)
            theorem child_asl
        val packaged =
          ListPair.map package_theorem (grounded_goals, theorems)
      in
        List.foldl
          (fn (theorem, result) => Drule.PROVE_HYP theorem result)
          grounded_schema packaged
      end
  in
    (grounded_goals, ground_validation)
  end

fun fixed_action_on recorded result store current _ =
  if boolSyntax.goal_eq recorded current then result
  else grounded_fixed_action result store

fun empty count =
  if count < 0 then
    raise mk_HOL_ERR "clasetReplay" "empty" "negative root count"
  else
    Script {records = [], length = 0, open_goals = count}

fun count_open [] count = count
  | count_open (NONE :: rest) count = count_open rest (count + 1)
  | count_open (SOME child :: rest) count =
      count_open rest (count_open (children_of child) count)

fun append (Script {records, length, open_goals}) record =
  let
    val target = target_of record
  in
    if target < 1 orelse target > open_goals then
      raise mk_HOL_ERR "clasetReplay" "append"
        "the target does not identify an open goal"
    else
      Script
        {records = record :: records, length = length + 1,
         open_goals = count_open (children_of record) (open_goals - 1)}
  end

(* Undo the frontier changes in reverse record order. At each recorded
   target, the following slots are the finished subtrees (or open goals)
   for the record's holes in depth-first order. Prefilled children keep
   their shape and consume slots only for their own holes. *)
fun materialize (Script {records, open_goals, ...}) =
  let
    fun graft (record as StepRecord {children = [], ...}) frontier =
          (record, frontier)
      | graft (StepRecord
                 {kind, target, consumed, created, eigenvariables,
                  validation, action, children}) frontier =
          let
            val (children', rest) = fill children frontier []
          in
            (StepRecord
               {kind = kind, target = target, consumed = consumed,
                created = created, eigenvariables = eigenvariables,
                validation = validation, action = action, children = children'},
             rest)
          end
    and fill [] frontier acc = (List.rev acc, frontier)
      | fill (NONE :: children) (next :: frontier) acc =
          fill children frontier (next :: acc)
      | fill (NONE :: _) [] _ = raise Fail "missing replay frontier slot"
      | fill (SOME child :: children) frontier acc =
          let
            val (child', rest) = graft child frontier
          in
            fill children rest (SOME child' :: acc)
          end
    fun install (record, frontier) =
      let
        fun at 1 slots =
              let val (tree, rest) = graft record slots in SOME tree :: rest end
          | at n (slot :: slots) = slot :: at (n - 1) slots
          | at _ [] = raise Fail "invalid replay frontier target"
      in
        at (target_of record) frontier
      end
  in
    List.foldl install (List.tabulate (open_goals, fn _ => NONE)) records
  end

fun script_length (Script {length, ...}) = length

fun variant_name Plain = "plain"
  | variant_name Swapped = "swapped"
  | variant_name Duplicate = "duplicate"
  | variant_name MakeElim = "make-elim"

fun kind_name (Assumption pos) = "assumption " ^ Int.toString pos
  | kind_name (Contradiction (left, right)) =
      "contradiction " ^ Int.toString left ^ "," ^ Int.toString right
  | kind_name (ModusPonens _) = "mp"
  | kind_name (RuleApplication {variant, elim, ...}) =
      "rule(" ^ variant_name variant ^
      (if elim then ",elim)" else ",intro)")
  | kind_name Disch = "DISCH"
  | kind_name Gen = "GEN"
  | kind_name SplitPaired = "split-paired"
  | kind_name HypSubst = "hyp-subst"
  | kind_name CContr = "CCONTR"
  | kind_name (SwappedBuiltin pos) =
      "swapped-builtin " ^ Int.toString pos
  | kind_name (MoveAssumptionToBack pos) =
      "move-back " ^ Int.toString pos
  | kind_name Wrapper = "wrapper"

fun lines_of_record indent (StepRecord {kind, target, children, ...}) =
  let
    val line = indent ^ Int.toString target ^ ": " ^ kind_name kind
    val child_lines =
      List.concat
        (map
          (fn NONE => [indent ^ "  open"]
            | SOME child => lines_of_record (indent ^ "  ") child)
          children)
  in
    line :: child_lines
  end

fun to_string script =
  String.concatWith "\n"
    (List.concat
      (map
        (fn NONE => ["open"]
          | SOME record => lines_of_record "" record)
        (materialize script)))

fun ground store script =
  Grounded {store = clasetMeta.ground store, script = script}

fun grounded_store (Grounded {store, ...}) = store
fun grounded_to_string (Grounded {script, ...}) = to_string script

exception ReplayError of step_record * goal * string

fun split_lengths [] theorems =
      if List.null theorems then []
      else raise Fail "extra replay theorems"
  | split_lengths (count :: counts) theorems =
      let
        val prefix = List.take (theorems, count)
        val suffix = List.drop (theorems, count)
      in
        prefix :: split_lengths counts suffix
      end

fun replay_option _ _ NONE goal = ([goal], fn [th] => th | _ =>
      raise mk_HOL_ERR "clasetReplay" "replay"
        "open-goal validation arity")
  | replay_option ctxt store (SOME record) goal =
      let
        (* A step proves the goal in the spelling the engine recorded it
           in, and replay runs it against the goal as the caller posed
           one: the two spell a binder or a redex differently wherever
           the entry reduced the caller's terms.  The step's proof is
           restated in the replay goal's own spelling before its validity
           is judged, as [clasetStep.aligned_result] restates a child's. *)
        fun aligned_action replay_goal current =
          let
            val (children, validation) =
              action_of record store replay_goal current
          in
            (children,
             fn theorems =>
               clasetNorm.align_goal replay_goal (validation theorems))
          end
        val (children, parent_validation) =
          Tactical.VALID aligned_action goal ctxt
          handle Portable.Interrupt => raise Portable.Interrupt
               | searchBudget.LimitReached info =>
                   raise searchBudget.LimitReached info
               | error =>
                   raise ReplayError
                     (record, goal, Feedback.exn_to_string error)
        val subtrees = children_of record
        val _ =
          if length children = length subtrees then ()
          else
            raise ReplayError
              (record, goal, "recorded and emitted child arities differ")
        val replayed =
          ListPair.map
            (fn (subtree, child) =>
              replay_option ctxt store subtree child)
            (subtrees, children)
        val residuals = List.concat (map #1 replayed)
        val counts = map (length o #1) replayed
        val validations = map #2 replayed

        fun validation theorems =
          let
            val groups = split_lengths counts theorems
            val child_theorems =
              ListPair.map (fn (validate, group) => validate group)
                (validations, groups)
          in
            parent_validation child_theorems
          end
      in
        (residuals, validation)
      end

fun replay_roots _ _ [] [] = ([], fn [] => [] | _ =>
      raise mk_HOL_ERR "clasetReplay" "replay_roots"
        "root validation arity")
  | replay_roots ctxt store (root :: roots) (goal :: goals) =
      let
        val (first_goals, first_validation) =
          replay_option ctxt store root goal
        val (rest_goals, rest_validation) =
          replay_roots ctxt store roots goals
        val first_count = length first_goals
        fun validation theorems =
          let
            val first = List.take (theorems, first_count)
            val rest = List.drop (theorems, first_count)
          in
            first_validation first :: rest_validation rest
          end
      in
        (first_goals @ rest_goals, validation)
      end
  | replay_roots _ _ _ _ =
      raise mk_HOL_ERR "clasetReplay" "replay_roots"
        "script root count does not match the input"

fun replay_in ctxt
      (Grounded {store, script}) goal =
  let
    val (goals, validate_roots) =
      replay_roots ctxt store (materialize script) [goal]
    fun validation theorems =
      case validate_roots theorems of
          [theorem] => theorem
        | _ =>
            raise mk_HOL_ERR "clasetReplay" "replay"
              "single-goal replay produced several root theorems"
  in
    Replayed (goals, validation)
  end
  handle ReplayError (record, bad_goal, message) =>
    ReplayFailed
      (ReplayFailure
        {goal = bad_goal, step = SOME (kind_of record),
         message = message, script = to_string script})
       | Portable.Interrupt => raise Portable.Interrupt
       | searchBudget.LimitReached info =>
           raise searchBudget.LimitReached info
       | error =>
           ReplayFailed
             (ReplayFailure
               {goal = goal, step = NONE,
                message = Feedback.exn_to_string error,
                script = to_string script})

fun goal_string (asl, w) =
  let
    val assumptions =
      String.concatWith ", " (map Parse.term_to_string asl)
  in
    "[" ^ assumptions ^ "] ?- " ^ Parse.term_to_string w
  end

fun REPLAY_TAC grounded goal ctxt =
  case replay_in ctxt grounded goal of
      Replayed result => result
    | ReplayFailed
        (ReplayFailure {goal = bad_goal, step, message, script}) =>
        let
          val step_text =
            case step of NONE => "<script>" | SOME kind => kind_name kind
          val diagnostic =
            "Replay failed at " ^ step_text ^ " on " ^
            goal_string bad_goal ^ ": " ^ message
          val _ = traceUtil.trace (traceUtil.level_of tracer ctxt) 1
            (fn () => diagnostic ^ "\nReplay script:\n" ^ script)
        in
          raise mk_HOL_ERR "clasetReplay" "REPLAY_TAC" diagnostic
        end

val length = script_length

end
