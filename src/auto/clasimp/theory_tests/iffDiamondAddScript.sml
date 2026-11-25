Theory iffDiamondAdd
Ancestors
  iffDiamondRoot
Libs
  clasimpLib

Definition iff_diamond_add_def:
  iff_diamond_add (p : bool) = p
End

Theorem iff_diamond_add_rule[iff]:
  !p. iff_diamond_add p <=> p
Proof
  simp[iff_diamond_add_def]
QED
