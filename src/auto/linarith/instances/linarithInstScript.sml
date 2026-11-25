Theory linarithInst
Ancestors
  integer real rat

Theorem INT_LE_LMUL_POS:
  !a b c : int. 0 < c /\ a <= b ==> c * a <= c * b
Proof
  metis_tac [INT_LE_MONO]
QED

Theorem INT_LT_LMUL_POS:
  !a b c : int. 0 < c /\ a < b ==> c * a < c * b
Proof
  metis_tac [INT_LT_MONO]
QED

Theorem INT_NEQ_E:
  !x y : int.
    x <> y ==> (x < y ==> F) ==> (y < x ==> F) ==> F
Proof
  metis_tac [INT_LT_TOTAL]
QED

Theorem INT_MIN_SPLIT:
  !P (x : int) y.
    P (int_min x y) <=>
    (x < y ==> P x) /\ (y <= x ==> P y)
Proof
  rw [INT_MIN, INT_NOT_LT] >>
  metis_tac [INT_NOT_LT]
QED

Theorem INT_MAX_SPLIT:
  !P (x : int) y.
    P (int_max x y) <=>
    (x < y ==> P y) /\ (y <= x ==> P x)
Proof
  rw [INT_MAX, INT_NOT_LT] >>
  metis_tac [INT_NOT_LT]
QED

Theorem INT_ABS_SPLIT:
  !P (x : int).
    P (ABS x) <=>
    (x < 0 ==> P (~x)) /\ (0 <= x ==> P x)
Proof
  rw [INT_ABS, INT_NOT_LT] >>
  metis_tac [INT_NOT_LT]
QED

Theorem REAL_NEQ_E:
  !x y : real.
    x <> y ==> (x < y ==> F) ==> (y < x ==> F) ==> F
Proof
  metis_tac [REAL_LT_TOTAL]
QED

Theorem REAL_MIN_SPLIT:
  !P (x : real) y.
    P (min x y) <=>
    (x <= y ==> P x) /\ (y < x ==> P y)
Proof
  rw [min_def] >>
  metis_tac [REAL_NOT_LE]
QED

Theorem REAL_MAX_SPLIT:
  !P (x : real) y.
    P (max x y) <=>
    (x <= y ==> P y) /\ (y < x ==> P x)
Proof
  rw [max_def] >>
  metis_tac [REAL_NOT_LE]
QED

Theorem REAL_ABS_SPLIT:
  !P (x : real).
    P (abs x) <=>
    (0 <= x ==> P x) /\ (x < 0 ==> P (-x))
Proof
  rw [abs] >>
  metis_tac [REAL_NOT_LE]
QED

Theorem RAT_LT_ADD2:
  !a b c d : rat. a < b /\ c < d ==> a + c < b + d
Proof
  metis_tac [RAT_LES_RADD, RAT_LES_LADD, RAT_LES_TRANS]
QED

Theorem RAT_LET_ADD2:
  !a b c d : rat. a <= b /\ c < d ==> a + c < b + d
Proof
  metis_tac [RAT_LEQ_RADD, RAT_LES_LADD, RAT_LEQ_LES_TRANS]
QED

Theorem RAT_LTE_ADD2:
  !a b c d : rat. a < b /\ c <= d ==> a + c < b + d
Proof
  metis_tac [RAT_LES_RADD, RAT_LEQ_LADD, RAT_LES_LEQ_TRANS]
QED

Theorem RAT_LEQ_LMUL_POS:
  !a b c : rat. 0 < c /\ a <= b ==> c * a <= c * b
Proof
  metis_tac [RAT_LEQ_LES, RAT_LES_LMUL_POS]
QED

Theorem RAT_NEQ_E:
  !x y : rat.
    x <> y ==> (x < y ==> F) ==> (y < x ==> F) ==> F
Proof
  metis_tac [RAT_LES_TOTAL]
QED

Theorem RAT_LT_LMUL_POS:
  !a b c : rat. 0 < c /\ a < b ==> c * a < c * b
Proof
  metis_tac [RAT_LES_LMUL_POS]
QED

Theorem RAT_POLY_CLAUSES_BASE[local]:
  (!x y z : rat. x + (y + z) = (x + y) + z) /\
  (!x y : rat. x + y = y + x) /\
  (!x : rat. 0 + x = x) /\
  (!x y z : rat. x * (y * z) = (x * y) * z) /\
  (!x y : rat. x * y = y * x) /\
  (!x : rat. 1 * x = x) /\
  (!x : rat. 0 * x = 0) /\
  (!x y z : rat. x * (y + z) = x * y + x * z) /\
  (!x : rat. rat_expn x 0 = 1) /\
  (!x : rat. !n. rat_expn x (SUC n) = x * rat_expn x n)
Proof
  REWRITE_TAC [RAT_ADD_ASSOC, RAT_ADD_LID, RAT_MUL_ASSOC,
               RAT_MUL_LID, RAT_MUL_LZERO, RAT_LDISTRIB,
               rat_expn_def] >>
  REWRITE_TAC [Once RAT_ADD_COMM, Once RAT_MUL_COMM]
QED

Theorem RAT_POLY_CLAUSES =
  MATCH_MP normalizerTheory.SEMIRING_PTHS RAT_POLY_CLAUSES_BASE

Theorem RAT_POLY_NEG_CLAUSES:
  (!x : rat. -x = -1 * x) /\
  (!x y : rat. x - y = x + -1 * y)
Proof
  simp [RAT_SUB_ADDAINV, GSYM RAT_AINV_LMUL]
QED

Theorem RAT_OF_NUM_NONNEG:
  !n : num. 0q <= &n
Proof
  simp [RAT_OF_NUM_LEQ]
QED
