Theory declA
Ancestors
  clasetSeed
Libs
  clasetLib

val intro_spec =
  {kind = clasetRules.Intro, safe = false, prio = NONE};
val sdest_spec =
  {kind = clasetRules.Dest, safe = true, prio = NONE};

Theorem declA_attr[sintro]:
  !p. p ==> p
Proof
  BasicProvers.PROVE_TAC []
QED

Theorem declA_intro_priority[intro=75]:
  !p q. p ==> p \/ q
Proof
  BasicProvers.PROVE_TAC []
QED

Theorem declA_elim_priority[elim=50]:
  !p q. p /\ q ==> q /\ p
Proof
  BasicProvers.PROVE_TAC []
QED

Theorem declA_dest_priority[dest=25]:
  !p q. p /\ q ==> p
Proof
  BasicProvers.PROVE_TAC []
QED

Theorem declA_export:
  !p q. p ==> q ==> p
Proof
  BasicProvers.PROVE_TAC []
QED

val _ = export_rule intro_spec "declA.declA_export";

Theorem declA_removed:
  !p q r. p /\ q ==> (p ==> r) ==> r
Proof
  BasicProvers.PROVE_TAC []
QED

val _ = export_rule sdest_spec "declA.declA_removed";
val _ = delrule "declA.declA_removed";
