structure linarithCorpus :> linarithCorpus =
struct

open Abbrev testutils

datatype strength_outcome =
    StrengthSuccess
  | StrengthExpectedFailure of {error : string, remedy : string}

type strength_goal = int * strength_outcome * term

(* Isabelle's Arith_Examples.thy at f7e02b7e1f31 has 54 lemma goals,
   numbered here in source order.  The 34 num/bool ones are a strict
   subset: the other 20 need int, real or rat syntax and so can only
   run in instances/.  Both lists are spelled out, so that the count and
   the duplicate-freeness numbering_relation_holds asserts of each are
   things a mis-edited numbering can actually break. *)
val full_numbering =
  [1, 2, 3, 4, 5, 6, 7, 8, 9,
   10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
   20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
   30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
   40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
   50, 51, 52, 53, 54]

val core_numbering =
  [1, 3, 5, 7, 9,
   14, 15, 16, 17, 18,
   22, 23, 24,
   30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
   40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
   51]

(* The core goals themselves, in source order.  They are stated here
   rather than in either suite because both run them: the suite in this
   directory runs exactly these, and the instances suite merges them
   with the 20 that need int, real or rat syntax.  Those 20 are the
   whole of what the pre-boss grammar cannot state, so they are the
   whole of what the split has to duplicate; a goal stated in both files
   instead is one whose two statements can drift apart while both suites
   still pass, because what check_numbering checks is the numbers.

   Both upstream "oops" goals are retained: [47] is proved, because
   splitting on demand never builds the disjunctive normal form whose
   size defeated upstream, and [48] is the corpus's one method boundary
   -- linear arithmetic's documented integer-divisibility incompleteness
   -- asserted to be reported, promptly and by that name, rather than
   run into. *)
val core_arith_examples : strength_goal list =
  [(1, StrengthSuccess, “(i:num) <= MAX i j”),
   (3, StrengthSuccess, “MIN i j <= (i:num)”),
   (5, StrengthSuccess, “MIN (i:num) j <= MAX i j”),
   (7, StrengthSuccess,
    “MIN (i:num) j + MAX i j = i + j”),
   (9, StrengthSuccess,
    “(i:num) < j ==> MIN i j < MAX i j”),
   (14, StrengthSuccess, “(x:num) <= y ==> x - y = 0”),
   (15, StrengthSuccess, “(x:num) - y = 0 ==> x <= y”),
   (16, StrengthSuccess,
    “((x:num) <= y) = (x - y = 0)”),
   (17, StrengthSuccess,
    “(x:num) < y /\ d < 1 ==> x - y = d”),
   (18, StrengthSuccess,
    “(x:num) < y /\ d < 1 ==> x - y - x = d - x”),
   (22, StrengthSuccess, “(i:num) MOD 0 = i”),
   (23, StrengthSuccess, “(i:num) MOD 1 = 0”),
   (24, StrengthSuccess, “(i:num) MOD 42 <= 41”),
   (30, StrengthSuccess, “(x:num) < SUC y <=> x <= y”),
   (31, StrengthSuccess,
    “((x:num) = z ==> x <> y) ==> x <> y \/ z <> y”),
   (32, StrengthSuccess,
    “((x:num) < SUC y) = (x <= y)”),
   (33, StrengthSuccess,
    “(x:num) < y /\ y < z ==> x < z”),
   (34, StrengthSuccess,
    “(x:num) < y /\ y < z ==> x < z”),
   (35, StrengthSuccess, “(P:bool) = Q ==> Q = P”),
   (36, StrengthSuccess,
    “P = ((x:num) = 0) /\ ~P = (y = 0) ==> MIN x y = 0”),
   (37, StrengthSuccess,
    “P = ((x:num) = 0) /\ ~P = (y = 0) ==>
     MAX x y = x + y”),
   (38, StrengthSuccess,
    “(x:num) <> y /\ a + 2 = b /\ a < y /\ y < b /\
     a < x /\ x < b ==> F”),
   (39, StrengthSuccess,
    “y < (x:num) /\ z < y /\ x < z ==> F”),
   (40, StrengthSuccess, “y < (x:num) - 5 ==> y < x”),
   (41, StrengthSuccess, “(x:num) <> 0 ==> 0 < x”),
   (42, StrengthSuccess,
    “(x:num) <> y /\ x <= y ==> x < y”),
   (43, StrengthSuccess,
    “(x:num) < y /\ P (x - y) ==> P 0”),
   (44, StrengthSuccess,
    “(x - y) - (x:num) = (x - x) - y”),
   (45, StrengthSuccess,
    “(a:num) < b /\ c < d ==> a - b = c - d”),
   (46, StrengthSuccess,
    “(a:num) - (b - (c - (d - e))) =
     a - (b - (c - (d - e)))”),
   (47, StrengthSuccess,
    “((n:num) < m /\ m < n') \/
     (n < m /\ m = n') \/
     (n < n' /\ n' < m) \/
     (n = n' /\ n' < m) \/
     (n = m /\ m < n') \/
     (n' < m /\ m < n) \/
     (n' < m /\ m = n) \/
     (n' < n /\ n < m) \/
     (n' = n /\ n < m) \/
     (n' = m /\ m < n) \/
     (m < n /\ n < n') \/
     (m < n /\ n' = n) \/
     (m < n' /\ n' < n) \/
     (m = n /\ n < n') \/
     (m = n' /\ n' < n) \/
     (n' = m /\ m = n)”),
   (48,
    StrengthExpectedFailure
      {error = "CFG_LINARITH_TAC: linear arithmetic found no proof",
       remedy =
         "requires intLib.ARITH_TAC/COOPER_TAC (integer divisibility)"},
    “2 * (x:num) <> 1”),
   (49, StrengthSuccess, “(0:num) < 1”),
   (51, StrengthSuccess, “(47:num) + 11 < 8 * 15”)]

(* Source order is goal-number order, so a corpus assembled from two
   partitions of the numbering is their merge by number.  That the
   partitions are disjoint and between them exhaust the numbering is not
   asserted here: check_numbering says it, of the assembled list, and
   says it for a corpus written out in one piece too. *)
fun merge_by_number ([], goals) = goals
  | merge_by_number (goals, []) = goals
  | merge_by_number (left as (first as (left_number, _, _)) :: left_rest,
                     right as (second as (right_number, _, _)) ::
                       right_rest) =
      if left_number <= right_number then
        first :: merge_by_number (left_rest, right)
      else second :: merge_by_number (left, right_rest)

fun check (name, predicate) =
  (tprint name;
   if predicate () then OK () else die "failed")

fun residual tactic goal =
  #1 (Tactical.VALID tactic goal (Context.snapshot()))

fun valid_closes tactic goal = null (residual tactic goal)

fun tactic_fails tactic goal =
  ((ignore (Tactical.VALID tactic goal (Context.snapshot())); false)
   handle Feedback.HOL_ERR _ => true)

fun normalized_rhs (instance : linarithData.linarith_instance) tm =
  #2 (boolSyntax.dest_eq (Thm.concl (#norm_conv instance tm)))

fun canonical_form (instance : linarithData.linarith_instance) tm =
  #2 (boolSyntax.dest_eq
        (Thm.concl (Conv.QCONV (#norm_conv instance) tm)))

(* X_LE_X_SQUARED is not linear, so it can only reach a goal as a fact
   the table supplies.  That is what makes it a usable probe: a caller
   brackets one goal with it and asserts the goal is closed inside the
   bracket and refused outside, which no solver that snapshots the
   table can satisfy. *)
fun with_arith_fact operation =
  case ThmSetData.data_exportfns {settype = "arith"} of
      NONE => false
    | SOME export =>
        let
          val name =
            {Thy = "arithmetic", Name = "X_LE_X_SQUARED"}
          fun remove () =
            #remove export
              {thy = "arithmetic",
               remove = "arithmetic$X_LE_X_SQUARED"}
          val _ =
            #add export
              {thy = "arithmetic",
               named_thm =
                 (name, arithmeticTheory.X_LE_X_SQUARED)}
          val result =
            operation () handle e => (remove (); raise e)
          val _ = remove ()
        in
          result
        end

(* The [arith] set a tactic reads is that of the context it is applied in,
   not the ambient one.  [contexts_with_and_without_fact] answers a
   snapshot that has the probe fact and one that lacks it; the tactic is
   run with its context given explicitly, while the ambient set has the
   fact (second group) or lacks it (first group).  Both are taken from the
   ambient state when the assertion runs, not when this structure loads:
   a snapshot is a simpset-derivation key for the suites that read it,
   and one from load time would carry a theory state older than the
   suite's own. *)
fun contexts_with_and_without_fact () =
  let
    val without_fact = Context.snapshot ()
    val captured = ref without_fact
    val _ = with_arith_fact
              (fn () => (captured := Context.snapshot (); true))
  in
    (!captured, without_fact)
  end

fun closes_in ctxt tactic goal =
  null (#1 (Tactical.VALID tactic goal ctxt))
  handle Feedback.HOL_ERR _ => false

fun follows_arith_context tactic_in goal =
  let
    val (with_fact, without_fact) = contexts_with_and_without_fact ()
    fun closes ctxt = closes_in ctxt (tactic_in ctxt) goal
    fun discriminates () = closes with_fact andalso not (closes without_fact)
    val ambient_without = discriminates ()
    val ambient_with = with_arith_fact discriminates
  in ambient_without andalso ambient_with end

fun selftest_level () =
  case Option.mapPartial Int.fromString
         (OS.Process.getEnv "HOLSELFTESTLEVEL") of
      SOME level => level
    | NONE => 1

fun duplicates [] = []
  | duplicates (number :: rest) =
      if Lib.mem number rest then
        number :: duplicates (List.filter (fn n => n <> number) rest)
      else duplicates rest

fun outside numbering = List.filter (fn n => not (Lib.mem n numbering))

fun show numbers =
  String.concat (Lib.commafy (map Int.toString numbers))

(* The relation the two suites are partitioned by; asserted from both
   so that either one alone still catches a corpus drifting. *)
fun numbering_relation_holds () =
  null (duplicates full_numbering) andalso
  null (duplicates core_numbering) andalso
  List.length full_numbering = 54 andalso
  List.length core_numbering = 34 andalso
  null (outside full_numbering core_numbering) andalso
  List.length (outside core_numbering full_numbering) = 20

fun check_numbering {suite, numbering} goals =
  let
    val actual = map #1 goals
    val repeated = duplicates actual
    val missing = outside actual numbering
    val extra = outside numbering actual
    val _ = tprint (suite ^ " corpus numbering")
  in
    if not (null repeated) then
      die ("goal numbers occur more than once: " ^ show repeated)
    else if not (null missing) then
      die ("goal numbers missing from the corpus: " ^ show missing)
    else if not (null extra) then
      die ("goal numbers outside the canonical numbering: " ^ show extra)
    else if not (numbering_relation_holds ()) then
      die "core_numbering is no longer 34 of the 54 full_numbering goals"
    else OK ()
  end

(* Each budget carries the text the failure message names it by, so the
   number a reader is told to look for cannot drift from the number
   actually enforced. *)
val goal_budget = (Time.fromSeconds 30, "30 seconds")
val boundary_budget = (Time.fromSeconds 5, "5 seconds")

(* What running one goal to completion can amount to.  Refused carries
   origin and message together: a goal is refused for the documented
   reason or it is not refused as documented. *)
datatype attempt =
    Closed
  | Refused of string
  | Residual
  | Exceeded

fun attempt tactic (budget, _) proposition =
  (if Timeout.apply budget
        (fn () => valid_closes (tactic ()) ([], proposition)) ()
   then Closed
   else Residual)
  handle Timeout.TIMEOUT _ => Exceeded
       | Feedback.HOL_ERR error =>
           Refused
             (Feedback.top_function_of error ^ ": " ^
              Feedback.message_of error)

fun run_goal (suite, tactic, succeeded, boundaries)
             (number, outcome, proposition) =
  let
    val prefix = suite ^ " goal " ^ Int.toString number
    val (label, budget) =
      case outcome of
          StrengthSuccess => (prefix, goal_budget)
        | StrengthExpectedFailure {remedy, ...} =>
            (prefix ^ " (expected failure: " ^ remedy ^ ")",
             boundary_budget)
    val _ = tprint label
    val allowance = " budget of " ^ #2 budget
  in
    case (outcome, attempt tactic budget proposition) of
        (StrengthSuccess, Closed) =>
          (succeeded := !succeeded + 1; OK ())
      | (StrengthSuccess, Exceeded) =>
          die (prefix ^ " exceeded its" ^ allowance)
      | (StrengthSuccess, Residual) =>
          die (prefix ^ " was not closed by LINARITH_TAC")
      | (StrengthSuccess, Refused message) =>
          die (prefix ^ " was not proved by LINARITH_TAC: " ^ message)
      | (StrengthExpectedFailure {error, ...}, Refused message) =>
          if message = error then
            (boundaries := !boundaries + 1; OK ())
          else
            die (prefix ^ " failed with \"" ^ message ^
                 "\" rather than the expected \"" ^ error ^ "\"")
      | (StrengthExpectedFailure {remedy, ...}, Closed) =>
          die (prefix ^ " closed a goal recorded as beyond the method; " ^
               remedy)
      | (StrengthExpectedFailure _, Exceeded) =>
          die (prefix ^ " ran into its boundary instead of reporting " ^
               "it, exceeding the" ^ allowance)
      | (StrengthExpectedFailure _, Residual) =>
          die (prefix ^ " left goals behind instead of reporting that " ^
               "the method does not decide it")
  end

fun run_suite {suite, tactic, suite_budget,
               expected_successes, expected_boundaries} goals =
  let
    val succeeded = ref 0
    val boundaries = ref 0
    val started = Time.now ()
    val _ =
      List.app (run_goal (suite, tactic, succeeded, boundaries)) goals
    val elapsed = Time.- (Time.now (), started)
    val _ = tprint (suite ^ " suite count and time budget")
  in
    if !succeeded = expected_successes andalso
       !boundaries = expected_boundaries andalso
       Time.< (elapsed, suite_budget)
    then OK ()
    else die "failed"
  end

end
