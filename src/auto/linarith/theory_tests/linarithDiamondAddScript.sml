Theory linarithDiamondAdd
Ancestors
  linarithDiamondRoot
Libs
  linarithData

Definition arith_diamond_add_def:
  arith_diamond_add (p : bool) = p
End

Theorem arith_diamond_add_fact[arith]:
  !p. arith_diamond_add p <=> p
Proof
  simp[arith_diamond_add_def]
QED

Definition arith_split_diamond_add_def:
  arith_split_diamond_add (p : bool) = p
End

Theorem arith_split_diamond_add_rule[arith_split]:
  !P p. P (arith_split_diamond_add p) <=> P p
Proof
  simp[arith_split_diamond_add_def]
QED

(* The two contested declarations: the sibling branch retracts these by
   name without having them in its own ancestry, so only the merge in
   the common descendant can bring the retraction and the declaration
   together. *)

Definition arith_diamond_contested_def:
  arith_diamond_contested (p : bool) = p
End

Theorem arith_diamond_contested_fact[arith]:
  !p. arith_diamond_contested p <=> p
Proof
  simp[arith_diamond_contested_def]
QED

Definition arith_split_diamond_contested_def:
  arith_split_diamond_contested (p : bool) = p
End

Theorem arith_split_diamond_contested_rule[arith_split]:
  !P p. P (arith_split_diamond_contested p) <=> P p
Proof
  simp[arith_split_diamond_contested_def]
QED
