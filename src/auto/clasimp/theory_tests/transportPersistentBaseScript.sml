Theory transportPersistentBase
Ancestors
  arithmetic
Libs
  clasimpLib

Definition transport_persistent_p_def:
  transport_persistent_p (n:num) <=> n = 0
End

Definition transport_persistent_q_def:
  transport_persistent_q (n:num) <=> n = 0
End

Definition transport_persistent_r_def:
  transport_persistent_r (n:num) <=> n = 0
End

Theorem transport_persistent_bridge:
  !n. transport_persistent_p n <=> transport_persistent_q n
Proof
  simp[transport_persistent_p_def, transport_persistent_q_def]
QED

Theorem transport_persistent_dest[sdest]:
  !n. transport_persistent_p n ==> transport_persistent_r n
Proof
  simp[transport_persistent_p_def, transport_persistent_r_def]
QED
