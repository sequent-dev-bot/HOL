Theory batchAddBase
Ancestors
  clasetSeed
Libs
  clasetLib

val sintro_spec =
  {kind = clasetRules.Intro, safe = true, prio = NONE};
val intro_spec =
  {kind = clasetRules.Intro, safe = false, prio = NONE};

Theorem batch_safe_zero:
  T /\ T
Proof
  BasicProvers.PROVE_TAC []
QED

val _ = export_rule sintro_spec "batchAddBase.batch_safe_zero";

Theorem batch_safe_positive:
  !p q. p ==> q ==> (p /\ q) /\ T
Proof
  BasicProvers.PROVE_TAC []
QED

val _ = export_rule sintro_spec "batchAddBase.batch_safe_positive";

Theorem batch_unsafe_one:
  !p q. p ==> q ==> p \/ q
Proof
  BasicProvers.PROVE_TAC []
QED

val _ = export_rule intro_spec "batchAddBase.batch_unsafe_one";

Theorem batch_unsafe_two:
  !p q. p ==> q ==> q \/ p
Proof
  BasicProvers.PROVE_TAC []
QED

val _ = export_rule intro_spec "batchAddBase.batch_unsafe_two";

Theorem batch_unsafe_duplicate:
  !p q. p ==> q ==> p \/ q
Proof
  BasicProvers.PROVE_TAC []
QED

(* This intentionally records a duplicate ADD in the theory batch. *)
val _ = export_rule intro_spec "batchAddBase.batch_unsafe_duplicate";
