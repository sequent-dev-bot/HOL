Theory diamondRoot
Ancestors
  clasetSeed
Libs
  clasetLib

val intro_spec =
  {kind = clasetRules.Intro, safe = false, prio = NONE};

Theorem diamond_root_rule:
  !p. p ==> p
Proof
  BasicProvers.PROVE_TAC []
QED

val _ = export_rule intro_spec "diamondRoot.diamond_root_rule";
