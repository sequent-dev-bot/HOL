Theory specReloadBase
Ancestors
  clasetSeed
Libs
  clasetLib

Theorem spec_intro[intro=64]:
  !p q. p ==> p \/ q
Proof
  BasicProvers.PROVE_TAC []
QED

Theorem spec_elim[elim=37]:
  !p q. p /\ q ==> q /\ p
Proof
  BasicProvers.PROVE_TAC []
QED

Theorem spec_dest[dest=82]:
  !p q. p /\ q ==> p
Proof
  BasicProvers.PROVE_TAC []
QED

Theorem spec_forward[forward=73]:
  !p q. p /\ q ==> q
Proof
  BasicProvers.PROVE_TAC []
QED

Theorem spec_sforward[sforward]:
  !p q r. p /\ q /\ r ==> q
Proof
  BasicProvers.PROVE_TAC []
QED

Theorem spec_norm_default[norm]:
  !p. p /\ T <=> p
Proof
  BasicProvers.PROVE_TAC []
QED

Theorem spec_norm_negative[norm= ~7]:
  !p. T /\ p <=> p
Proof
  BasicProvers.PROVE_TAC []
QED
