Theory iffDiamondRoot
Ancestors
  clasetSeed
Libs
  clasimpLib

Definition iff_diamond_root_def:
  iff_diamond_root (p : bool) = p
End

Theorem iff_diamond_root_rule[iff]:
  !p. iff_diamond_root p <=> p
Proof
  simp[iff_diamond_root_def]
QED
