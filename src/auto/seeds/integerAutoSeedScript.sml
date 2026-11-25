Theory integerAutoSeed
Ancestors
  integer
Libs
  clasetLib clasimpLib seedCollections

(* src/HOL/Int.thy:726-732 @ f7e02b7e. *)
Theorem INT_AUTO_NEG_SUC_LT_NUM[iff]:
  -&(SUC n) < &m
Proof
  intLib.ARITH_TAC
QED

Theorem INT_AUTO_NEG_LE_NUM[iff]:
  -&n <= &m
Proof
  intLib.ARITH_TAC
QED

(* Conservative arithmetic facts, never claset transitivity rules. *)
Theorem INT_LT_TOTAL_ARITH[arith] = integerTheory.INT_LT_TOTAL
Theorem INT_LE_TOTAL_ARITH[arith] = integerTheory.INT_LE_TOTAL
Theorem INT_LT_TRANS_ARITH[arith] = integerTheory.INT_LT_TRANS
Theorem INT_LE_TRANS_ARITH[arith] = integerTheory.INT_LE_TRANS
Theorem INT_LT_IMP_LE_ARITH[arith] = integerTheory.INT_LT_IMP_LE
Theorem INT_EQ_IMP_LE_ARITH[arith] = integerTheory.INT_EQ_IMP_LE

(* src/HOL/Groups.thy:221-341,563-612 @ f7e02b7e. *)
Theorem INT_ADD_ASSOC_ALGEBRA[algebra_simps, field_simps] =
  integerTheory.INT_ADD_ASSOC

Theorem INT_ADD_COMM_ALGEBRA[algebra_simps, field_simps] =
  integerTheory.INT_ADD_COMM

Theorem INT_MUL_ASSOC_ALGEBRA[algebra_simps, field_simps] =
  integerTheory.INT_MUL_ASSOC

Theorem INT_MUL_COMM_ALGEBRA[algebra_simps, field_simps] =
  integerTheory.INT_MUL_COMM

Theorem INT_EQ_SUB_RADD_ALGEBRA[algebra_simps, field_simps] =
  integerTheory.INT_EQ_SUB_RADD

Theorem INT_EQ_SUB_LADD_ALGEBRA[algebra_simps, field_simps] =
  integerTheory.INT_EQ_SUB_LADD

Theorem INT_LT_SUB_RADD_ALGEBRA[algebra_simps, field_simps] =
  integerTheory.INT_LT_SUB_RADD

Theorem INT_LT_SUB_LADD_ALGEBRA[algebra_simps, field_simps] =
  integerTheory.INT_LT_SUB_LADD

Theorem INT_LE_SUB_RADD_ALGEBRA[algebra_simps, field_simps] =
  integerTheory.INT_LE_SUB_RADD

Theorem INT_LE_SUB_LADD_ALGEBRA[algebra_simps, field_simps] =
  integerTheory.INT_LE_SUB_LADD

Theorem ALG_INT_ADD_LEFT_COMM[algebra_simps, field_simps]:
  !x y z : int. x + (y + z) = y + (x + z)
Proof
  intLib.INT_RING_TAC
QED

Theorem ALG_INT_MUL_LEFT_COMM[algebra_simps, field_simps]:
  !x y z : int. x * (y * z) = y * (x * z)
Proof
  intLib.INT_RING_TAC
QED

Theorem ALG_INT_DIFF_DIFF_ADD[algebra_simps, field_simps]:
  !a b c : int. a - b - c = a - (b + c)
Proof
  intLib.INT_RING_TAC
QED

Theorem ALG_INT_ADD_DIFF_EQ[algebra_simps, field_simps]:
  !a b c : int. a + (b - c) = (a + b) - c
Proof
  intLib.INT_RING_TAC
QED

Theorem ALG_INT_DIFF_DIFF_EQ2[algebra_simps, field_simps]:
  !a b c : int. a - (b - c) = (a + c) - b
Proof
  intLib.INT_RING_TAC
QED

Theorem ALG_INT_DIFF_ADD_EQ[algebra_simps, field_simps]:
  !a b c : int. (a - b) + c = (a + c) - b
Proof
  intLib.INT_RING_TAC
QED
