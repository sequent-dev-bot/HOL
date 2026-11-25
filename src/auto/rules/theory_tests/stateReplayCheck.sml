open HolKernel boolSyntax clasetRules clasetLib

fun fail message = raise Fail ("claset state replay test: " ^ message)

val spec = {kind = clasetRules.Intro, safe = true, prio = NONE}

val p = ``state_replay_p : bool``
val q = ``state_replay_q : bool``

val conflict_rule = DISCH p (ASSUME p)
val chronology_rule =
  let
    val pq = mk_disj (p, q)
  in
    DISCH pq
      (DISJ_CASES (ASSUME pq)
        (DISJ2 q (ASSUME p)) (DISJ1 (ASSUME q) p))
  end
val restore_rule = DISCH (mk_conj (p, q)) (CONJUNCT1 (ASSUME (mk_conj (p, q))))
val consecutive_rule1 = DISCH p (DISJ1 (ASSUME p) q)
val consecutive_rule2 = DISCH q (DISJ2 p (ASSUME q))

fun contribution name th _ = [(spec, (name, th))]

val conflict_name = "claset-state-replay-typebase-winner"
val temporary_name = "claset-state-replay-temporary-winner"
val chronology_temporary_name = "claset-state-replay-chronology-temporary"
val chronology_future_name = "claset-state-replay-chronology-future"
val restore_name = "claset-state-replay-restored"
val consecutive_name1 = "claset-state-replay-consecutive-one"
val consecutive_name2 = "claset-state-replay-consecutive-two"

val _ = register_tyinfo_contribution
  ("claset-state-replay-conflict", contribution conflict_name conflict_rule)
val _ = temp_add_rule spec (temporary_name, conflict_rule)

(* This declaration precedes its conflicting provider.  Lazy replay must not
   let an earlier catch-up marker see that future provider. *)
val _ = temp_add_rule spec (chronology_temporary_name, chronology_rule)
val _ = register_tyinfo_contribution
  ("claset-state-replay-chronology-future",
   contribution chronology_future_name chronology_rule)

val _ = register_tyinfo_contribution
  ("claset-state-replay-consecutive-one",
   contribution consecutive_name1 consecutive_rule1)
val _ = register_tyinfo_contribution
  ("claset-state-replay-consecutive-two",
   contribution consecutive_name2 consecutive_rule2)

val _ = register_tyinfo_contribution
  ("claset-state-replay-restore", contribution restore_name restore_rule)
val _ = temp_delrule restore_name

val rules = rules_of (the_claset ())

fun same_statement th1 th2 =
  Term.aconv (concl (canonical_rule th1)) (concl (canonical_rule th2))

fun declarations_for th =
  List.filter (fn (_, (_, th')) => same_statement th th') rules

fun exactly_named name th =
  case declarations_for th of
      [(_, (name', _))] => name = name'
    | _ => false

val _ =
  if not (exactly_named conflict_name conflict_rule) then
    fail "a later temporary declaration won a same-theorem conflict"
  else if not (exactly_named chronology_temporary_name chronology_rule) then
    fail "a future provider preempted an earlier temporary declaration"
  else if not (exactly_named restore_name restore_rule) then
    fail "the final catch-up did not restore a deleted derived rule"
  else if not (exactly_named consecutive_name1 consecutive_rule1) then
    fail "the first consecutive contribution is absent or duplicated"
  else if not (exactly_named consecutive_name2 consecutive_rule2) then
    fail "the second consecutive contribution is absent or duplicated"
  else ()
