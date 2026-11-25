Theory batchAddChild
Ancestors
  batchAddBase
Libs
  clasetRules clasetLib

fun fail message = raise Fail ("ADD-only claset batch test: " ^ message)

val cs = the_claset ()
val declarations = rules_of cs

fun find_rule name =
  List.find (fn (_, (name', _)) => name = name') declarations

fun same_thm th1 th2 =
  Term.aconv (concl (canonical_rule th1)) (concl (canonical_rule th2))

fun candidate_thms candidates = map (fn (_, (_, th)) => th) candidates

fun select expected candidates =
  List.filter
    (fn th => List.exists (fn expected_th => same_thm expected_th th) expected)
    (candidate_thms candidates)

fun same_thms expected actual =
  ListPair.allEq (fn (th1, th2) => same_thm th1 th2) (expected, actual)

val unsafe_expected = [batch_unsafe_two, batch_unsafe_one]
val duplicate_expected = map DUP_INTRO_RULE unsafe_expected
val disjunction = ``batch_add_p \/ batch_add_q``

val match_unsafe =
  select unsafe_expected
    (match_intro_candidates (unsafe_part cs) disjunction)
val unify_unsafe =
  select unsafe_expected
    (unify_intro_candidates (unsafe_part cs) disjunction)
val match_duplicate =
  select duplicate_expected
    (match_intro_candidates (dup_part cs) disjunction)
val unify_duplicate =
  select duplicate_expected
    (unify_intro_candidates (dup_part cs) disjunction)

val safe_zero =
  match_intro_candidates (safe0_part cs) ``T /\ T``
val safe_positive =
  match_intro_candidates
    (safep_part cs) ``(batch_add_p /\ batch_add_q) /\ T``

val _ =
  if not (Option.isSome (find_rule "batchAddBase$batch_safe_zero")) then
    fail "the safe zero-subgoal declaration is absent"
  else if not
    (Option.isSome (find_rule "batchAddBase$batch_safe_positive")) then
    fail "the safe positive-subgoal declaration is absent"
  else if not (Option.isSome (find_rule "batchAddBase$batch_unsafe_one")) then
    fail "the first unsafe declaration is absent"
  else if not (Option.isSome (find_rule "batchAddBase$batch_unsafe_two")) then
    fail "the second unsafe declaration is absent"
  else if Option.isSome
    (find_rule "batchAddBase$batch_unsafe_duplicate") then
    fail "the duplicate ADD changed the declaration set"
  else if not
    (List.exists (fn (_, (_, th)) => same_thm batch_safe_zero th) safe_zero)
  then fail "the safe-zero declaration is in the wrong netpart"
  else if not
    (List.exists
       (fn (_, (_, th)) => same_thm batch_safe_positive th) safe_positive)
  then fail "the safe-positive declaration is in the wrong netpart"
  else if not (same_thms unsafe_expected match_unsafe) then
    fail "match candidates do not retain equal-weight declaration order"
  else if not (same_thms unsafe_expected unify_unsafe) then
    fail "unify candidates do not retain equal-weight declaration order"
  else if not (same_thms duplicate_expected match_duplicate) then
    fail "match candidates are wrong in the duplicate netpart"
  else if not (same_thms duplicate_expected unify_duplicate) then
    fail "unify candidates are wrong in the duplicate netpart"
  else ()
