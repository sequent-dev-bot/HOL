Theory diamondAdd
Ancestors
  diamondRoot
Libs
  clasetLib

val selim_spec =
  {kind = clasetRules.Elim, safe = true, prio = NONE};

Theorem diamond_add_rule:
  !p q r. p \/ q ==> (p ==> r) ==> (q ==> r) ==> r
Proof
  BasicProvers.PROVE_TAC []
QED

val _ = export_rule selim_spec "diamondAdd.diamond_add_rule";
