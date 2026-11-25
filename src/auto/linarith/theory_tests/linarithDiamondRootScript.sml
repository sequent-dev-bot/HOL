Theory linarithDiamondRoot
Ancestors
  bool
Libs
  linarithData

Definition arith_diamond_root_def:
  arith_diamond_root (p : bool) = p
End

Theorem arith_diamond_root_fact[arith]:
  !p. arith_diamond_root p <=> p
Proof
  simp[arith_diamond_root_def]
QED

Definition arith_split_diamond_root_def:
  arith_split_diamond_root (p : bool) = p
End

Theorem arith_split_diamond_root_rule[arith_split]:
  !P p. P (arith_split_diamond_root p) <=> P p
Proof
  simp[arith_split_diamond_root_def]
QED
