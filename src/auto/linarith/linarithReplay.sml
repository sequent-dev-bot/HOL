structure linarithReplay :> linarithReplay =
struct

open Abbrev HolKernel Conv Drule
open linarithSolve

val ERR = mk_HOL_ERR "linarithReplay"

val same_type = linarithData.same_type

type config = linarithData.linarith_config

val dest_binary = linarithDecomp.binary_parts

fun relation_body tm =
  case Lib.total boolSyntax.dest_neg tm of
      SOME body => body
    | NONE => tm

fun relation_carrier tm =
  let
    val (_, left, _) = dest_binary (relation_body tm)
  in
    Term.type_of left
  end

fun instance_of_term tm =
  let val carrier = relation_carrier tm in
    case linarithData.instance_for carrier of
        SOME instance => instance
      | NONE =>
          raise ERR "mkthm"
            ("no linarith instance for " ^
             Parse.type_to_string carrier)
  end

fun instance_of_thm theorem = instance_of_term (Thm.concl theorem)

(* The first application of f that does not raise. *)
fun first_result f items = Lib.total (Lib.tryfind f) items

(* The first of a rule set's implications that matches.  Every set
   replay uses arrives derived from the registry, in the order the
   rules were given, so taking the first match over the flattened set
   is taking the first rule that matches. *)
fun match_implications implications theorem =
  first_result (fn implication => MATCH_MP implication theorem)
    implications

fun required_match operation implications theorem =
  case match_implications implications theorem of
      SOME result => result
    | NONE =>
        raise ERR "mkthm"
          ("Linear arithmetic: failed to " ^ operation ^ " theorem\n" ^
           Parse.thm_to_string theorem)

(* The conversions come from the registry already built; an injection
   with no usable homomorphism reports that by raising UNCHANGED, which
   is the same answer as a term the rewrites do not touch. *)
fun rewrite_injections conversion theorem =
  CONV_RULE conversion theorem handle UNCHANGED => theorem

(* Decomposition strips an injection from an argument built out of the
   operators it distributes over, counting the source carrier's
   successor as the sum that carrier's own normalizer turns it into.
   Normalizing an injected argument with its carrier's norm_conv is what
   puts replay in step with that: it is the step that makes &(SUC n) the
   &(n + 1) the add homomorphism can then split.  It fails, rather than
   raising UNCHANGED, on a term that is not an injection, because
   ONCE_DEPTH_CONV descends past a failure and not past UNCHANGED. *)
fun injected_argument_conv tm =
  let
    val (operator, _) = Term.dest_comb tm
    val injection =
      case linarithData.injection_by_const operator of
          SOME injection => injection
        | NONE => raise ERR "injected_argument_conv" "not an injection"
  in
    case linarithData.instance_for (#from_ty injection) of
        SOME source => RAND_CONV (#norm_conv source) tm
      | NONE => raise ERR "injected_argument_conv" "no source instance"
  end

fun with_injected_arguments conversion =
  ONCE_DEPTH_CONV injected_argument_conv THENC conversion

fun normalize_lift conversion theorem =
  rewrite_injections (with_injected_arguments conversion) theorem

fun normalize_injections theorem =
  rewrite_injections
    (with_injected_arguments
       (linarithData.all_injection_rewrite_conv ()))
    theorem

(* Where an instance's norm_conv meets a conclusion: at the two sides of
   its relation, or at the conclusion entire -- which is how norm_conv
   gets to report that the relation reduces to T or F. *)
datatype depth = Sides | Whole

fun depth_conv depth instance =
  case depth of
      Sides => BINOP_CONV (#norm_conv instance)
    | Whole => #norm_conv instance

(* Apply an instance's norm_conv at the depth the conclusion needs.  A
   negated conclusion carries its relation one level deeper, so a caller
   that is handed one reaches it through normalize_under_negation; the
   callers that only ever see a plain relation stay with normalize_at,
   which leaves a negation alone rather than descending into it. *)
fun normalize_at depth instance theorem =
  CONV_RULE (depth_conv depth instance) theorem

fun normalize_under_negation depth instance theorem =
  CONV_RULE (RAND_CONV (depth_conv depth instance)) theorem

(* Normalizing is opportunistic at some call sites: a conclusion whose
   carrier has no instance, or one norm_conv declines, is answered with
   the theorem we already had.  CONV_RULE absorbs UNCHANGED itself, so
   the second handler is for a conv that raises it before CONV_RULE is
   reached. *)
fun absorb normalize theorem =
  normalize theorem
  handle HOL_ERR _ => theorem
       | UNCHANGED => theorem

fun normalize_relation_sides theorem =
  absorb (fn thm => normalize_at Sides (instance_of_thm thm) thm) theorem

(* One lift per registered injection whose order homomorphisms the
   relation matches, pushed inwards again by the rewrite conversion the
   registry built for that injection. *)
fun lift_by (entry : linarithData.derived_injection) theorem =
  Option.map (normalize_lift (#rewrite_conv entry))
    (match_implications (#relation_imps entry) theorem)

fun lifts visited theorem =
  let
    val normalized = normalize_relation_sides theorem
    fun unseen_lift entry =
      case lift_by entry normalized of
          NONE => NONE
        | SOME lifted =>
            let val carrier = relation_carrier (Thm.concl lifted) in
              if List.exists (same_type carrier) visited then NONE
              else SOME (lifted, carrier :: visited)
            end
  in
    List.mapPartial unseen_lift
      (linarithData.derived_injections ())
  end

(* List lifts breadth-first, because replay takes the first pair that
   adds: first the direct lifts, then their lifts. Each queued theorem
   also carries the carriers visited on its path. An injection cycle
   may return to an earlier
   carrier with a newly nested conclusion, so conclusion equality alone
   cannot close it.  The carrier-simple paths retain conversions between
   sibling carriers through their common source and are bounded by the
   finite registry.

   The queue is kept as a front list and a reversed back list, and the
   result is accumulated reversed, so neither the enqueueing nor the
   appending walks what it has already built. *)
fun conversion_lifts theorem =
  let
    fun explore ([], []) _ found = List.rev found
      | explore ([], back) seen found =
          explore (List.rev back, []) seen found
      | explore ((current, visited) :: front, back) seen found =
          let val conclusion = Thm.concl current
          in
            if Termtab.defined seen conclusion then
              explore (front, back) seen found
            else
              explore (front, List.revAppend (lifts visited current, back))
                (Termtab.insert_set conclusion seen) (current :: found)
          end
    val conclusion = Thm.concl theorem
  in
    case lifts [relation_carrier conclusion] theorem of
        [] => []
      | direct =>
          explore (direct, []) (Termtab.insert_set conclusion Termtab.empty) []
  end

(* The relation's operator constant, read off the first subterm of the
   rule that the instance's destructor accepts. *)
fun relation_operator destructor theorem =
  Option.map (#1 o dest_binary)
    (Lib.total (find_term (Lib.can destructor)) (Thm.concl theorem))

fun operator_in_rules destructor rules =
  Lib.get_first (relation_operator destructor) rules

fun required_operator function what destructor rules =
  case operator_in_rules destructor rules of
      SOME operator => operator
    | NONE =>
        raise ERR function
          ("no " ^ what ^ " operator occurs in the instance kit")

fun equality_as_le instance theorem =
  if not (boolSyntax.is_eq (relation_body (Thm.concl theorem))) then
    theorem
  else
    let
      val dest = #dest instance
      val operator =
        required_operator "equality_as_le" "leq" (#dest_leq dest)
          (#add_mono (#kit instance))
      val (left, _) = boolSyntax.dest_eq (Thm.concl theorem)
      val variable = genvar (#ty instance)
      fun leq l r = Term.list_mk_comb (operator, [l, r])
      val relation = leq left left
      val reflexive = EQT_ELIM (#norm_conv instance relation)
      val function = Term.mk_abs (variable, leq left variable)
      val congruence =
        CONV_RULE (BINOP_CONV BETA_CONV) (AP_TERM function theorem)
    in
      EQ_MP congruence reflexive
    end

fun add_equalities instance theorem1 theorem2 =
  let
    val operator =
      required_operator "add_equalities" "plus"
        (#dest_plus (#dest instance)) (#add_mono (#kit instance))
  in
    MK_COMB (MK_COMB (REFL operator, theorem1), theorem2)
  end

fun add_direct_raw instance theorem1 theorem2 =
  match_implications
    (#add_mono (linarithData.instance_implications instance))
    (CONJ theorem1 theorem2)

fun add_direct theorem1 theorem2 =
  let
    val instance = instance_of_thm theorem1
    fun is_equality theorem =
      boolSyntax.is_eq (relation_body (Thm.concl theorem))
  in
    case add_direct_raw instance theorem1 theorem2 of
        SOME theorem => SOME theorem
      | NONE =>
          (case (is_equality theorem1, is_equality theorem2) of
               (true, true) => SOME (add_equalities instance theorem1 theorem2)
             | (false, false) => NONE
             | _ =>
                 add_direct_raw instance
                   (equality_as_le instance theorem1)
                   (equality_as_le instance theorem2))
  end
  handle HOL_ERR _ => NONE

fun try_add theorem others = Lib.get_first (add_direct theorem) others

fun try_add_pairs theorems others =
  Lib.get_first (fn theorem => try_add theorem others) theorems

fun add_failure level theorem1 theorem2 =
  let
    val _ = linarithData.trace_thm level 1 "failed add, left:" theorem1
    val _ =
      linarithData.trace_thm level 1 "failed add, right:" theorem2
  in
    raise ERR "mkthm" "Linear arithmetic: failed to add thms"
  end

fun add_thms level theorem1 theorem2 =
  case add_direct theorem1 theorem2 of
      SOME theorem => theorem
    | NONE =>
        let
          val left = conversion_lifts theorem1
          val right = conversion_lifts theorem2
        in
          (* The original pair has already failed. *)
          case try_add theorem1 right of
              SOME theorem => theorem
            | NONE =>
                (case try_add_pairs left (theorem2 :: right) of
                     SOME theorem => theorem
                   | NONE => add_failure level theorem1 theorem2)
        end

(* The multiplier is a Fourier--Motzkin coefficient -- a product of lcms
   -- so it is unbounded, and n - 1 additions is too many.  Double
   instead, adding one copy back on a set bit: O(log n) additions.  The
   intermediate sums come out balanced rather than right-nested, but
   normalize_sides is what the caller reads, and that is unchanged. *)
fun mult_by_add level n theorem =
  if Arbint.< (n, Arbint.one) then
    raise ERR "mult_by_add" "non-positive inequality multiplier"
  else
    let
      (* i copies of theorem summed, for i >= 1. *)
      fun multiple i =
        if i = Arbint.one then theorem
        else
          let
            val (half, bit) = Arbint.divmod (i, Arbint.two)
            val halved = multiple half
            val doubled = add_thms level halved halved
          in
            if bit = Arbint.zero then doubled
            else add_thms level theorem doubled
          end
    in
      multiple n
    end

(* Linear, and deliberately not doubled the way the multiplication above
   it is.  What is built here is a term, not a chain of inferences, and
   apply_to_product abstracts the variable out of it and beta-reduces on
   the spot.  The variable occurs at every node a doubled construction
   would share, so substitution copies each shared path back out: the
   term that reaches cancellation has n summands and n nodes whichever
   shape it was assembled in, and the instance's norm_conv walks it in
   O(n) either way.  Doubling would bound the recursion depth here and
   buy nothing else.

   This is the path an instance takes whose mult_mono mentions no
   multiplication, which is a registration the layer supports rather
   than a malformed one. *)
fun additive_scale instance n variable =
  let
    val dest = #dest instance
    val zero = #mk_lit dest Arbrat.zero
    val operator =
      required_operator "additive_scale" "addition" (#dest_plus dest)
        (#add_mono (#kit instance))
    fun add left right =
      Term.list_mk_comb (operator, [left, right])
    fun sum i =
      if i = Arbint.zero then zero
      else if i = Arbint.one then variable
      else add variable (sum (Arbint.- (i, Arbint.one)))
  in
    sum n
  end

(* Beta-reduced before it leaves, as the congruence equality_as_le
   builds is: an instance's expression conversion normalizes
   polynomials, not redexes, so a scaled side left as (\v. v * 3) x
   reaches cancellation as an atom distinct from the 3 * x it has to
   meet, and the certificate replays to a true relation instead of to
   falsity. *)
fun apply_to_product instance n literal theorem =
  let
    val dest = #dest instance
    val variable = genvar (#ty instance)
    val body =
      case operator_in_rules (#dest_mult dest)
             (#mult_mono (#kit instance)) of
          SOME operator =>
            Term.list_mk_comb (operator, [variable, literal])
        | NONE => additive_scale instance n variable
    val function = Term.mk_abs (variable, body)
  in
    CONV_RULE (BINOP_CONV BETA_CONV) (AP_TERM function theorem)
  end

fun specialize_literal literal theorem =
  let
    fun loop result =
      case Lib.total boolSyntax.dest_forall (Thm.concl result) of
          NONE => result
        | SOME _ => loop (SPEC literal result)
  in
    loop theorem
  end

fun prove_positive instance tm =
  EQT_ELIM (#norm_conv instance tm)

(* One rule's implications, both passes over them made before the next
   rule is tried: a rule that matches only with a positive premise
   still wins over a later rule that matches directly. *)
fun apply_mult_rule instance literal theorem implications =
  let
    fun direct implication =
      specialize_literal literal (MATCH_MP implication theorem)

    fun with_positive implication =
      let
        val opened = SPEC_ALL implication
        val variables =
          List.filter
            (fn variable =>
              same_type (Term.type_of variable) (#ty instance))
            (Term.free_vars (Thm.concl opened))
        fun try_variable variable =
          let
            val specialized = INST [variable |-> literal] opened
            val (antecedent, _) =
              boolSyntax.dest_imp (Thm.concl specialized)
            val (left, right) = boolSyntax.dest_conj antecedent
            fun positive_first () =
              MATCH_MP specialized
                (CONJ (prove_positive instance left) theorem)
            fun positive_second () =
              MATCH_MP specialized
                (CONJ theorem (prove_positive instance right))
          in
            case Lib.total positive_first () of
                SOME result => result
              | NONE => positive_second ()
          end
      in
        case first_result try_variable variables of
            SOME result => result
          | NONE => raise ERR "apply_mult_rule" "positive premise failed"
      end
  in
    case first_result direct implications of
        SOME result => result
      | NONE =>
          (case first_result with_positive implications of
               SOME result => result
             | NONE => raise ERR "apply_mult_rule" "rule does not match")
  end

fun mult_positive level instance n theorem =
  let
    val literal = #mk_lit (#dest instance) (Arbrat.fromAInt n)
  in
    case first_result
           (apply_mult_rule instance literal theorem)
           (#mult_mono (linarithData.instance_implications instance)) of
        SOME result => result
      | NONE => mult_by_add level n theorem
  end

(* Renormalize the two sides of a relation, which sit one level deeper
   when the conclusion is a negated one.  Scaling produces both kinds,
   so this is the one caller that descends. *)
fun normalize_sides instance theorem =
  (if boolSyntax.is_neg (Thm.concl theorem) then normalize_under_negation
   else normalize_at) Sides instance theorem

(* Scaling has to renormalize whatever it built, and for both kinds of
   relation.  Scaling an inequality did not, so a row scaled again on
   the way to a refutation kept the shape t * 2 * 3, which cancellation
   cannot match against the t * 6 on the other side, and replay ended at
   a true relation instead of at falsity. *)
fun mult_thm level n theorem =
  let
    val instance = instance_of_thm theorem
    val equality = boolSyntax.is_eq (relation_body (Thm.concl theorem))
    val negative = Arbint.< (n, Arbint.zero)
    val magnitude = if negative then Arbint.~ n else n
    val scaled =
      if n = Arbint.~ Arbint.one then SYM theorem
      else if equality then
        let
          val literal =
            #mk_lit (#dest instance) (Arbrat.fromAInt magnitude)
          val product =
            apply_to_product instance magnitude literal theorem
        in
          if negative then SYM product else product
        end
      else if negative then
        raise ERR "mult_thm" "negative multiplier on an inequality"
      else mult_positive level instance n theorem
  in
    normalize_sides instance scaled
  end

exception FalseReached of thm

(* Whole, not Sides: norm_conv normalizes both sides of a relation
   itself, so a BINOP_CONV pass before it would only run the carrier's
   polynomial conversion -- the most expensive step of the replay loop --
   a second time for no change. *)
fun normalize_added theorem =
  let
    val expanded = normalize_injections theorem
    val theorem' = normalize_at Whole (instance_of_thm expanded) expanded
  in
    if Term.aconv (Thm.concl theorem') boolSyntax.F then
      raise FalseReached theorem'
    else if Term.aconv (Thm.concl theorem') boolSyntax.T then expanded
    else theorem'
  end

fun normalize_final theorem =
  if Term.aconv (Thm.concl theorem) boolSyntax.F then theorem
  else
    let
      val expanded = normalize_injections theorem
    in
      normalize_at Whole (instance_of_thm expanded) expanded
    end

fun implications_of theorem =
  linarithData.instance_implications (instance_of_thm theorem)

fun mkthm_with checkpoint level assumption trace_assumptions justification =
  let
    val charge = Option.getOpt (checkpoint, fn () => ())
    (* Elimination reuses rows, so a certificate can refer to the same
       subproof more than once. Keep only a bounded set of physical nodes
       for this replay. Metered and traced replay visit the original tree. *)
    val memo =
      if Option.isSome checkpoint orelse traceUtil.enabled level 1 then NONE
      else SOME (memoUtil.bounded_memo 64
        (fn left => fn right => Portable.pointer_eq (left, right))
        (fn _ => ref (NONE : thm option)))
    fun one why = (charge (); replay why)
    and replay (why as Asm _) = decode why
      | replay (why as Nonneg _) = decode why
      | replay why =
          case memo of
              NONE => decode why
            | SOME lookup =>
                let val result = lookup why
                in
                  case !result of
                      SOME theorem => theorem
                    | NONE =>
                        let val theorem = decode why
                        in result := SOME theorem; theorem end
                end
    and decode (Asm index) =
          (assumption index
           handle Subscript =>
             raise ERR "mkthm"
               ("assumption index " ^ Int.toString index ^
                " is out of range"))
      | decode (Nonneg atom) =
          (case linarithData.instance_for (Term.type_of atom) of
               NONE =>
                 raise ERR "mkthm"
                   ("no linarith instance for nonnegative atom " ^
                    Parse.term_to_string atom)
             | SOME instance =>
                 (case #nonneg (#kit instance) atom of
                      SOME theorem => theorem
                    | NONE =>
                        raise ERR "mkthm"
                          ("instance declined nonnegative atom " ^
                           Parse.term_to_string atom)))
      | decode (LessD why) = from_instance "LessD" #lessD why
      | decode (NotLessD why) = from_instance "NotLessD" #not_less why
      | decode (NotLeD why) = from_instance "NotLeD" #not_le why
      | decode (NotLeDD why) =
          let
            val theorem = one why
            val imps = implications_of theorem
            val less =
              required_match "apply NotLeDD to" (#not_le imps) theorem
          in
            required_match "finish NotLeDD on" (#lessD imps) less
          end
      | decode (Multiplied (n, why)) = mult_thm level n (one why)
      | decode (Added (left, right)) =
          normalize_added (add_thms level (one left) (one right))
    (* Apply the rules the justification's own carrier supplies.  Only
       a discrete carrier supplies the lessD LessD and NotLeDD ask for,
       and those justifications never arise for a dense one, whose
       lessD implications are empty. *)
    and from_instance name
          (select : linarithData.instance_implications -> thm list) why =
          let
            val theorem = one why
          in
            required_match ("apply " ^ name ^ " to")
              (select (implications_of theorem)) theorem
          end

    val theorem =
      (charge ();
       normalize_final (one justification)
       handle FalseReached theorem => theorem)
    val _ =
      linarithData.trace_thm level 2 "replayed certificate:" theorem
  in
    if Term.aconv (Thm.concl theorem) boolSyntax.F then theorem
    else
      let
        val _ = trace_assumptions ()
        val _ = linarithData.trace_thm level 1 "Proved:" theorem
        val message =
          "Linear arithmetic should have refuted the assumptions but " ^
          "failed to."
        val _ = HOL_WARNING "linarithReplay" "mkthm" message
      in
        raise ERR "mkthm" message
      end
  end

fun mkthm level assumptions justification =
  let
    val indexed = Vector.fromList assumptions
    fun assumption index = Vector.sub (indexed, index)
    fun trace_assumptions () =
      linarithData.trace_items level 1 "Assumptions:"
        Parse.thm_to_string assumptions
  in
    mkthm_with NONE level assumption trace_assumptions justification
  end

(* Both replay paths use this operation to select neqE from the instance
   belonging to the disequality's carrier.  REL_NEQ is the only encoding
   to test for: decomp canonicalises a negated equality into it (see
   linarithSolve.sig). *)
fun is_disequality tm =
  case linarithDecomp.decomp tm of
      SOME (Decomp {rel = REL_NEQ, ...}) => true
    | _ => false

datatype split = Split of thm * term * term

fun extract_split theorem =
  let
    val (left_imp, rest) = boolSyntax.dest_imp (Thm.concl theorem)
    val (left, left_result) = boolSyntax.dest_imp left_imp
    val (right_imp, result) = boolSyntax.dest_imp rest
    val (right, right_result) = boolSyntax.dest_imp right_imp
  in
    if Term.aconv left_result boolSyntax.F andalso
       Term.aconv right_result boolSyntax.F andalso
       Term.aconv result boolSyntax.F
    then Split (theorem, left, right)
    else raise ERR "extract_split" "neqE has an unexpected conclusion"
  end

(* Which assumptions are splittable is decided by exactly the test the
   search used -- the disequality-elimination step inside linarithSolve
   asks whether a row is a disequality and whether it is discrete, which
   are is_disequality and the instance's discreteness here -- because
   the search emits one justification per case it generated and replay
   has to produce the matching goal for each.  Answering NONE for an
   assumption the search split leaves refute_tac's THENL with more
   tactics than goals, and the arity mismatch is what the user then
   sees.  So neqE not applying to an assumption that passed the test is
   an ill-formed instance, and is reported as one here. *)
fun split_assumption discrete_only assumption =
  case Lib.total instance_of_term assumption of
      NONE => NONE
    | SOME instance =>
        if not (is_disequality assumption) then NONE
        else if discrete_only andalso
                not (Option.isSome (#discrete instance))
        then NONE
        else
          let
            val theorem = Thm.ASSUME assumption
          in
            case match_implications
                   (#neqE (linarithData.instance_implications instance))
                   theorem of
                SOME implication => SOME (extract_split implication)
              | NONE =>
                  raise ERR "split_assumption"
                    ("the neqE of the linarith instance for " ^
                     Parse.type_to_string (#ty instance) ^
                     " does not apply to\n" ^
                     Parse.thm_to_string theorem)
          end

fun finish_forward conclusion negated false_theorem =
  if boolSyntax.is_neg conclusion then
    Thm.NOT_INTRO (Thm.DISCH negated false_theorem)
  else Thm.CCONTR conclusion false_theorem

fun find_split split assumptions =
  let
    fun find _ [] = NONE
      | find prefix (assumption :: rest) =
          case split assumption of
              SOME split => SOME (List.revAppend (prefix, rest), split)
            | NONE => find (assumption :: prefix) rest
  in
    find [] assumptions
  end

fun neq_elim_step (common, Split (split, left, right)) =
  let
    val goals =
      [(common @ [left], boolSyntax.F),
       (common @ [right], boolSyntax.F)]
    fun justify [left_false, right_false] =
          Thm.MP
            (Thm.MP split (Thm.DISCH left left_false))
            (Thm.DISCH right right_false)
      | justify _ =
          raise ERR "neq_elim_tac" "invalid justification"
  in
    (goals, justify)
  end

(* Tactical.REPEAT ends its loop on any HOL_ERR, so it cannot tell the
   "nothing left to split" that legitimately ends this one from the
   diagnostic split_assumption raises where replay and search disagree,
   and would leave the user with the arity mismatch that diagnostic
   exists to replace.  Hence the loop written out: it ends exactly where
   find_split reports no splittable disequality. *)
fun neq_elim_tac discrete_only =
  let
    val splits = ref Termtab.empty
    fun split assumption =
      (* Decomposition produces REL_NEQ only for a negated equality. *)
      if not (boolSyntax.is_neg assumption andalso
              boolSyntax.is_eq (boolSyntax.dest_neg assumption)) then NONE
      else
        case Termtab.lookup (!splits) assumption of
            SOME result => result
          | NONE =>
              let val result = split_assumption discrete_only assumption
              in
                splits := Termtab.update (assumption, result) (!splits);
                result
              end
    fun eliminate (goal as (assumptions, conclusion)) ctxt =
      if not (Term.aconv conclusion boolSyntax.F) then
        Tactical.ALL_TAC goal ctxt
      else
        case find_split split assumptions of
            NONE => Tactical.ALL_TAC goal ctxt
          | SOME found =>
              let
                fun step (_ : goal) _ = neq_elim_step found
              in
                Tactical.THEN (step, eliminate) goal ctxt
              end
  in
    eliminate
  end

fun append_negated_tac (assumptions, conclusion) _ =
  let
    val negated = negate conclusion
    val goal = (assumptions @ [negated], boolSyntax.F)
    fun justify [false_theorem] =
          finish_forward conclusion negated false_theorem
      | justify _ =
          raise ERR "append_negated_tac" "invalid justification"
  in
    ([goal], justify)
  end

fun justification_tac_with checkpoint justification
      (assumptions, goal) ctxt =
  if not (Term.aconv goal boolSyntax.F) then
    raise ERR "justification_tac" "goal is not false"
  else
    let
      val level = traceUtil.level_of linarithData.tracer ctxt
      (* Validate the whole context before charging replay. Use ASSUME
         for the kernel's diagnostic if a premise is malformed. *)
      val _ =
        List.app (fn tm =>
          if Term.type_of tm = Type.bool then () else ignore (Thm.ASSUME tm))
          assumptions
      val terms = Vector.fromList assumptions
      val proved = Array.array (Vector.length terms, NONE)
      fun assumption index =
        case Array.sub (proved, index) of
            SOME theorem => theorem
          | NONE =>
              let
                val theorem = Thm.ASSUME (Vector.sub (terms, index))
              in
                Array.update (proved, index, SOME theorem);
                theorem
              end
      fun trace_assumptions () =
        linarithData.trace_items level 1 "Assumptions:"
          (Parse.thm_to_string o Thm.ASSUME) assumptions
    in
      Tactic.ACCEPT_TAC
        (mkthm_with checkpoint level assumption trace_assumptions
           justification)
        (assumptions, goal) ctxt
    end

fun refute_tac_with checkpoint split_neq justifications =
  let
    fun split_tac goal ctxt =
      if split_neq then
        (* Branches share the same disequalities. Reuse their kernel
           split theorems across branches within this replay. Each pass
           has its own cache because the first omits dense carriers. *)
        Tactical.THEN (neq_elim_tac true, neq_elim_tac false) goal ctxt
      else Tactical.ALL_TAC goal ctxt
    val leaves =
      List.map (justification_tac_with checkpoint) justifications
  in
    Tactical.THEN
      (append_negated_tac, Tactical.THENL (split_tac, leaves))
  end

fun refute_tac split_neq justifications =
  refute_tac_with NONE split_neq justifications

fun refute level config assumptions conclusion =
  let
    val (split_neq, result) =
      linarithSolve.prove level config linarithDecomp.decomp
        linarithDecomp.is_nonnegative assumptions conclusion
  in
    Option.map (refute_tac split_neq) result
  end

datatype refutation_outcome =
    RefutationReady of tactic
  | RefutationExhausted
  | RefutationLimitReached of
      {kind : searchBudget.kind, usage : searchBudget.usage}

fun refute_budgeted level budget config assumptions conclusion =
  let
    fun charge () =
      searchBudget.charge budget searchBudget.Normalization
  in
    case linarithSolve.prove_budgeted level budget config
           linarithDecomp.decomp linarithDecomp.is_nonnegative
           assumptions conclusion of
        linarithSolve.CertificateFound
          {split_neq, justifications} =>
            RefutationReady
              (refute_tac_with (SOME charge) split_neq justifications)
      | linarithSolve.CertificateExhausted => RefutationExhausted
      | linarithSolve.CertificateLimitReached {kind, usage} =>
          RefutationLimitReached {kind = kind, usage = usage}
  end

(* The forward proof is the tactic replay run on a goal made of the
   premises' own conclusions.  Reproducing the disequality case split a
   second time as a tree of theorems would have to stay case-for-case in
   step with refute_tac, since both consume the one justification list
   in the order the search's disequality elimination generated it. *)
fun fwd_prove_in ctxt config theorems conclusion =
  let
    val level = traceUtil.level_of linarithData.tracer ctxt
    val hypotheses = List.map Thm.concl theorems
    val tactic =
      case refute level config hypotheses conclusion of
          SOME tactic => tactic
        | NONE =>
            raise ERR "fwd_prove_in" "linear arithmetic found no proof"
    val (goals, validation) = tactic (hypotheses, conclusion) ctxt
    val _ =
      if null goals then ()
      else raise ERR "fwd_prove_in" "replay left a subgoal open"
    val theorem = Lib.rev_itlist PROVE_HYP theorems (validation [])
    val _ = linarithData.trace_thm level 2 "forward proof:" theorem
  in
    theorem
  end

datatype budget_outcome =
    ReplayProved of thm
  | ReplayExhausted
  | ReplayLimitReached of
      {kind : searchBudget.kind, usage : searchBudget.usage}

fun fwd_prove_budgeted_in ctxt budget config theorems conclusion =
  let
    val hypotheses = List.map Thm.concl theorems
    fun charge () =
      searchBudget.charge budget searchBudget.Normalization
  in
    case refute_budgeted (traceUtil.level_of linarithData.tracer ctxt) budget
           config hypotheses conclusion of
        RefutationExhausted => ReplayExhausted
      | RefutationLimitReached {kind, usage} =>
          ReplayLimitReached {kind = kind, usage = usage}
      | RefutationReady tactic =>
          let
            val _ = charge ()
            val (goals, validation) =
              Tactical.VALID tactic (hypotheses, conclusion) ctxt
            val _ =
              if null goals then ()
              else raise ERR "fwd_prove_budgeted_in"
                "replay left a subgoal open"
            val _ = charge ()
            val proof = validation []
            fun discharge premise theorem =
              (charge (); PROVE_HYP premise theorem)
            val theorem =
              Lib.rev_itlist discharge theorems proof
          in
            ReplayProved theorem
          end
  end
  handle searchBudget.LimitReached (kind, usage) =>
    ReplayLimitReached {kind = kind, usage = usage}

end
