Theory linarithSeed
Ancestors
  arithmetic

Theorem NUM_LT_ADD2:
  !m n p q. m < p /\ n < q ==> m + n < p + q
Proof
  metis_tac [LESS_MONO_ADD, ADD_COMM, LESS_TRANS]
QED

Theorem NUM_LET_ADD2:
  !m n p q. m <= p /\ n < q ==> m + n < p + q
Proof
  metis_tac [LESS_EQ_MONO_ADD_EQ, LESS_MONO_ADD, ADD_COMM,
             LESS_EQ_LESS_TRANS]
QED

Theorem NUM_LTE_ADD2:
  !m n p q. m < p /\ n <= q ==> m + n < p + q
Proof
  metis_tac [LESS_MONO_ADD, LESS_EQ_MONO_ADD_EQ, ADD_COMM,
             LESS_LESS_EQ_TRANS]
QED

Theorem NUM_NEQ_E:
  !x y. x <> y ==> (x < y ==> F) ==> (y < x ==> F) ==> F
Proof
  metis_tac [LESS_CASES, LESS_OR_EQ]
QED

Theorem NUM_MIN_SPLIT:
  !P m n.
    P (MIN m n) <=>
    (m < n ==> P m) /\ (n <= m ==> P n)
Proof
  rw [MIN_DEF, NOT_LESS]
QED

Theorem NUM_MAX_SPLIT:
  !P m n.
    P (MAX m n) <=>
    (m < n ==> P n) /\ (n <= m ==> P m)
Proof
  rw [MAX_DEF, NOT_LESS]
QED

Theorem NUM_SUB_SPLIT:
  !P m n.
    P (m - n) <=>
    (m < n /\ P 0) \/ ?d. m = n + d /\ P d
Proof
  metis_tac [SUB_ELIM_THM_EXISTS']
QED
