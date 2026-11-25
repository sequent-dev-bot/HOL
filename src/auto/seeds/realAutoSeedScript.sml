Theory realAutoSeed
Ancestors
  real rat
Libs
  clasetLib clasimpLib seedCollections RealField

(* src/HOL/Real.thy:1231-1265 and Fields.thy:32-62 @ f7e02b7e. *)
Theorem REAL_AUTO_ADD_NEG_EQ_ZERO[iff]:
  (x : real) + -a = 0 <=> x = a
Proof
  REAL_ARITH_TAC
QED

Theorem REAL_SUMSQ_AUTO[iff] = realTheory.REAL_SUMSQ

Theorem REAL_SUMSQ_ARITH[arith] = realTheory.REAL_SUMSQ
Theorem REAL_LE_SQUARE_ARITH[arith] = realTheory.REAL_LE_SQUARE
Theorem REAL_POSSQ_ARITH[arith] = realTheory.REAL_POSSQ
Theorem REAL_MUL_POS_LT_ARITH[arith] = realTheory.REAL_MUL_POS_LT
Theorem REAL_LT_TOTAL_ARITH[arith] = realTheory.REAL_LT_TOTAL
Theorem REAL_LE_TOTAL_ARITH[arith] = realTheory.REAL_LE_TOTAL
Theorem REAL_LT_TRANS_ARITH[arith] = realTheory.REAL_LT_TRANS
Theorem REAL_LE_TRANS_ARITH[arith] = realTheory.REAL_LE_TRANS
Theorem REAL_LT_IMP_LE_ARITH[arith] = realTheory.REAL_LT_IMP_LE
Theorem REAL_EQ_IMP_LE_ARITH[arith] = realTheory.REAL_EQ_IMP_LE

(* src/HOL/Groups.thy:221-341,563-612 @ f7e02b7e.  Rat lives here
   because Phase 8 deliberately has no separate rational seed. *)
Theorem REAL_ADD_ASSOC_ALGEBRA[algebra_simps, field_simps] =
  realTheory.REAL_ADD_ASSOC

Theorem REAL_ADD_COMM_ALGEBRA[algebra_simps, field_simps] =
  realTheory.REAL_ADD_COMM

Theorem REAL_MUL_ASSOC_ALGEBRA[algebra_simps, field_simps] =
  realTheory.REAL_MUL_ASSOC

Theorem REAL_MUL_COMM_ALGEBRA[algebra_simps, field_simps] =
  realTheory.REAL_MUL_COMM

Theorem REAL_EQ_SUB_RADD_ALGEBRA[algebra_simps, field_simps] =
  realTheory.REAL_EQ_SUB_RADD

Theorem REAL_EQ_SUB_LADD_ALGEBRA[algebra_simps, field_simps] =
  realTheory.REAL_EQ_SUB_LADD

Theorem REAL_LT_SUB_RADD_ALGEBRA[algebra_simps, field_simps] =
  realTheory.REAL_LT_SUB_RADD

Theorem REAL_LT_SUB_LADD_ALGEBRA[algebra_simps, field_simps] =
  realTheory.REAL_LT_SUB_LADD

Theorem REAL_LE_SUB_RADD_ALGEBRA[algebra_simps, field_simps] =
  realTheory.REAL_LE_SUB_RADD

Theorem REAL_LE_SUB_LADD_ALGEBRA[algebra_simps, field_simps] =
  realTheory.REAL_LE_SUB_LADD

Theorem RAT_ADD_ASSOC_ALGEBRA[algebra_simps, field_simps] =
  ratTheory.RAT_ADD_ASSOC

Theorem RAT_ADD_COMM_ALGEBRA[algebra_simps, field_simps] =
  ratTheory.RAT_ADD_COMM

Theorem RAT_MUL_ASSOC_ALGEBRA[algebra_simps, field_simps] =
  ratTheory.RAT_MUL_ASSOC

Theorem RAT_MUL_COMM_ALGEBRA[algebra_simps, field_simps] =
  ratTheory.RAT_MUL_COMM

Theorem RAT_LSUB_EQ_ALGEBRA[algebra_simps, field_simps] = ratTheory.RAT_LSUB_EQ
Theorem RAT_RSUB_EQ_ALGEBRA[algebra_simps, field_simps] = ratTheory.RAT_RSUB_EQ

Theorem RAT_LSUB_LES_ALGEBRA[algebra_simps, field_simps] =
  ratTheory.RAT_LSUB_LES

Theorem RAT_RSUB_LES_ALGEBRA[algebra_simps, field_simps] =
  ratTheory.RAT_RSUB_LES

Theorem RAT_LSUB_LEQ_ALGEBRA[algebra_simps, field_simps] =
  ratTheory.RAT_LSUB_LEQ

Theorem RAT_RSUB_LEQ_ALGEBRA[algebra_simps, field_simps] =
  ratTheory.RAT_RSUB_LEQ

Theorem ALG_REAL_ADD_LEFT_COMM[algebra_simps, field_simps]:
  !x y z : real. x + (y + z) = y + (x + z)
Proof
  REAL_ARITH_TAC
QED

Theorem ALG_REAL_MUL_LEFT_COMM[algebra_simps, field_simps]:
  !x y z : real. x * (y * z) = y * (x * z)
Proof
  simp [AC realTheory.REAL_MUL_ASSOC realTheory.REAL_MUL_COMM]
QED

Theorem ALG_REAL_DIFF_DIFF_ADD[algebra_simps, field_simps]:
  !a b c : real. a - b - c = a - (b + c)
Proof
  REAL_ARITH_TAC
QED

Theorem ALG_REAL_ADD_DIFF_EQ[algebra_simps, field_simps]:
  !a b c : real. a + (b - c) = (a + b) - c
Proof
  REAL_ARITH_TAC
QED

Theorem ALG_REAL_DIFF_DIFF_EQ2[algebra_simps, field_simps]:
  !a b c : real. a - (b - c) = (a + c) - b
Proof
  REAL_ARITH_TAC
QED

Theorem ALG_REAL_DIFF_ADD_EQ[algebra_simps, field_simps]:
  !a b c : real. (a - b) + c = (a + c) - b
Proof
  REAL_ARITH_TAC
QED

Theorem ALG_RAT_ADD_LEFT_COMM[algebra_simps, field_simps]:
  !x y z : rat. x + (y + z) = y + (x + z)
Proof
  simp [AC ratTheory.RAT_ADD_ASSOC ratTheory.RAT_ADD_COMM]
QED

Theorem ALG_RAT_MUL_LEFT_COMM[algebra_simps, field_simps]:
  !x y z : rat. x * (y * z) = y * (x * z)
Proof
  simp [AC ratTheory.RAT_MUL_ASSOC ratTheory.RAT_MUL_COMM]
QED

Theorem ALG_RAT_DIFF_DIFF_ADD[algebra_simps, field_simps]:
  !a b c : rat. a - b - c = a - (b + c)
Proof
  simp [ratTheory.RAT_SUB_ADDAINV, ratTheory.RAT_AINV_ADD,
        AC ratTheory.RAT_ADD_ASSOC ratTheory.RAT_ADD_COMM]
QED

Theorem ALG_RAT_ADD_DIFF_EQ[algebra_simps, field_simps]:
  !a b c : rat. a + (b - c) = (a + b) - c
Proof
  simp [ratTheory.RAT_SUB_ADDAINV,
        AC ratTheory.RAT_ADD_ASSOC ratTheory.RAT_ADD_COMM]
QED

Theorem ALG_RAT_DIFF_DIFF_EQ2[algebra_simps, field_simps]:
  !a b c : rat. a - (b - c) = (a + c) - b
Proof
  simp [ratTheory.RAT_SUB_ADDAINV, ratTheory.RAT_AINV_ADD,
        AC ratTheory.RAT_ADD_ASSOC ratTheory.RAT_ADD_COMM]
QED

Theorem ALG_RAT_DIFF_ADD_EQ[algebra_simps, field_simps]:
  !a b c : rat. (a - b) + c = (a + c) - b
Proof
  simp [ratTheory.RAT_SUB_ADDAINV,
        AC ratTheory.RAT_ADD_ASSOC ratTheory.RAT_ADD_COMM]
QED

(* src/HOL/Fields.thy:180,204-252,775-887 @ f7e02b7e. *)
Theorem REAL_INV_1OVER_FIELD[field_simps] = realTheory.REAL_INV_1OVER
Theorem REAL_EQ_RDIV_EQ_FIELD[field_simps] = realTheory.REAL_EQ_RDIV_EQ'
Theorem REAL_LT_RDIV_EQ_FIELD[field_simps] = realTheory.REAL_LT_RDIV_EQ
Theorem REAL_LT_LDIV_EQ_FIELD[field_simps] = realTheory.REAL_LT_LDIV_EQ
Theorem REAL_LE_RDIV_EQ_FIELD[field_simps] = realTheory.REAL_LE_RDIV_EQ
Theorem REAL_LE_LDIV_EQ_FIELD[field_simps] = realTheory.REAL_LE_LDIV_EQ
Theorem RAT_RDIV_EQ_FIELD[field_simps] = ratTheory.RAT_RDIV_EQ
Theorem RAT_LDIV_EQ_FIELD[field_simps] = ratTheory.RAT_LDIV_EQ
Theorem RAT_RDIV_LES_POS_FIELD[field_simps] = ratTheory.RAT_RDIV_LES_POS
Theorem RAT_LDIV_LES_POS_FIELD[field_simps] = ratTheory.RAT_LDIV_LES_POS
Theorem RAT_RDIV_LEQ_POS_FIELD[field_simps] = ratTheory.RAT_RDIV_LEQ_POS
Theorem RAT_LDIV_LEQ_POS_FIELD[field_simps] = ratTheory.RAT_LDIV_LEQ_POS
Theorem RAT_RDIV_LES_NEG_FIELD[field_simps] = ratTheory.RAT_RDIV_LES_NEG
Theorem RAT_LDIV_LES_NEG_FIELD[field_simps] = ratTheory.RAT_LDIV_LES_NEG
Theorem RAT_RDIV_LEQ_NEG_FIELD[field_simps] = ratTheory.RAT_RDIV_LEQ_NEG
Theorem RAT_LDIV_LEQ_NEG_FIELD[field_simps] = ratTheory.RAT_LDIV_LEQ_NEG

Theorem FIELD_REAL_RDIV_EQ[field_simps]:
  !a b c : real. c <> 0 ==> (b / c = a <=> b = a * c)
Proof
  REAL_FIELD_TAC
QED

Theorem FIELD_REAL_NEG_RDIV_EQ[field_simps]:
  !a b c : real. b <> 0 ==>
    (-(a / b) = c <=> -a = c * b)
Proof
  REAL_FIELD_TAC
QED

Theorem FIELD_REAL_EQ_NEG_RDIV[field_simps]:
  !a b c : real. b <> 0 ==>
    (c = -(a / b) <=> c * b = -a)
Proof
  REAL_FIELD_TAC
QED

Theorem FIELD_REAL_ADD_RDIV[field_simps]:
  !x y z : real. z <> 0 ==>
    x + y / z = (x * z + y) / z
Proof
  REAL_FIELD_TAC
QED

Theorem FIELD_REAL_RDIV_ADD[field_simps]:
  !x y z : real. z <> 0 ==>
    x / z + y = (x + y * z) / z
Proof
  REAL_FIELD_TAC
QED

Theorem FIELD_REAL_DIFF_RDIV[field_simps]:
  !x y z : real. z <> 0 ==>
    x - y / z = (x * z - y) / z
Proof
  REAL_FIELD_TAC
QED

Theorem FIELD_REAL_NEG_RDIV_ADD[field_simps]:
  !x y z : real. z <> 0 ==>
    -(x / z) + y = (-x + y * z) / z
Proof
  REAL_FIELD_TAC
QED

Theorem FIELD_REAL_RDIV_DIFF[field_simps]:
  !x y z : real. z <> 0 ==>
    x / z - y = (x - y * z) / z
Proof
  REAL_FIELD_TAC
QED

Theorem FIELD_REAL_NEG_RDIV_DIFF[field_simps]:
  !x y z : real. z <> 0 ==>
    -(x / z) - y = (-x - y * z) / z
Proof
  REAL_FIELD_TAC
QED

Theorem FIELD_REAL_POS_LE_NEG_RDIV[field_simps]:
  !a b c : real. 0 < c ==>
    (a <= -(b / c) <=> a * c <= -b)
Proof
  metis_tac [realTheory.REAL_DIV_LNEG,
             realTheory.REAL_LE_RDIV_EQ]
QED

Theorem FIELD_REAL_LE_RDIV_EQ_NEG[field_simps]:
  !a b c : real. c < 0 ==>
    (a <= b / c <=> b <= a * c)
Proof
  rpt strip_tac >>
  `c <> 0` by
    metis_tac [realTheory.REAL_LT_IMP_NE] >>
  `c * (b / c) <= c * a <=> a <= b / c` by
    (irule realTheory.REAL_LE_LMUL_NEG >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `c * (b / c) = b` by
    (irule realTheory.REAL_DIV_LMUL >>
     FIRST_ASSUM ACCEPT_TAC) >>
  metis_tac [realTheory.REAL_MUL_COMM]
QED

Theorem FIELD_REAL_LT_RDIV_EQ_NEG[field_simps]:
  !a b c : real. c < 0 ==>
    (a < b / c <=> b < a * c)
Proof
  rpt strip_tac >>
  `c <> 0` by
    metis_tac [realTheory.REAL_LT_IMP_NE] >>
  `c * (b / c) < c * a <=> a < b / c` by
    (irule realTheory.REAL_LT_LMUL_NEG >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `c * (b / c) = b` by
    (irule realTheory.REAL_DIV_LMUL >>
     FIRST_ASSUM ACCEPT_TAC) >>
  metis_tac [realTheory.REAL_MUL_COMM]
QED

Theorem FIELD_REAL_LT_LDIV_EQ_NEG[field_simps]:
  !a b c : real. c < 0 ==>
    (b / c < a <=> a * c < b)
Proof
  rpt strip_tac >>
  `c <> 0` by
    metis_tac [realTheory.REAL_LT_IMP_NE] >>
  `c * a < c * (b / c) <=> b / c < a` by
    (irule realTheory.REAL_LT_LMUL_NEG >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `c * (b / c) = b` by
    (irule realTheory.REAL_DIV_LMUL >>
     FIRST_ASSUM ACCEPT_TAC) >>
  metis_tac [realTheory.REAL_MUL_COMM]
QED

Theorem FIELD_REAL_LE_LDIV_EQ_NEG[field_simps]:
  !a b c : real. c < 0 ==>
    (b / c <= a <=> a * c <= b)
Proof
  rpt strip_tac >>
  `c <> 0` by
    metis_tac [realTheory.REAL_LT_IMP_NE] >>
  `c * a <= c * (b / c) <=> b / c <= a` by
    (irule realTheory.REAL_LE_LMUL_NEG >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `c * (b / c) = b` by
    (irule realTheory.REAL_DIV_LMUL >>
     FIRST_ASSUM ACCEPT_TAC) >>
  metis_tac [realTheory.REAL_MUL_COMM]
QED

Theorem FIELD_REAL_NEG_LE_NEG_RDIV[field_simps]:
  !a b c : real. c < 0 ==>
    (a <= -(b / c) <=> -b <= a * c)
Proof
  metis_tac [realTheory.REAL_DIV_LNEG,
             FIELD_REAL_LE_RDIV_EQ_NEG]
QED

Theorem FIELD_REAL_POS_LT_NEG_RDIV[field_simps]:
  !a b c : real. 0 < c ==>
    (a < -(b / c) <=> a * c < -b)
Proof
  metis_tac [realTheory.REAL_DIV_LNEG,
             realTheory.REAL_LT_RDIV_EQ]
QED

Theorem FIELD_REAL_NEG_LT_NEG_RDIV[field_simps]:
  !a b c : real. c < 0 ==>
    (a < -(b / c) <=> -b < a * c)
Proof
  metis_tac [realTheory.REAL_DIV_LNEG,
             FIELD_REAL_LT_RDIV_EQ_NEG]
QED

Theorem FIELD_REAL_POS_NEG_RDIV_LT[field_simps]:
  !a b c : real. 0 < c ==>
    (-(b / c) < a <=> -b < a * c)
Proof
  metis_tac [realTheory.REAL_DIV_LNEG,
             realTheory.REAL_LT_LDIV_EQ]
QED

Theorem FIELD_REAL_NEG_NEG_RDIV_LT[field_simps]:
  !a b c : real. c < 0 ==>
    (-(b / c) < a <=> a * c < -b)
Proof
  metis_tac [realTheory.REAL_DIV_LNEG,
             FIELD_REAL_LT_LDIV_EQ_NEG]
QED

Theorem FIELD_REAL_POS_NEG_RDIV_LE[field_simps]:
  !a b c : real. 0 < c ==>
    (-(b / c) <= a <=> -b <= a * c)
Proof
  metis_tac [realTheory.REAL_DIV_LNEG,
             realTheory.REAL_LE_LDIV_EQ]
QED

Theorem FIELD_REAL_NEG_NEG_RDIV_LE[field_simps]:
  !a b c : real. c < 0 ==>
    (-(b / c) <= a <=> a * c <= -b)
Proof
  metis_tac [realTheory.REAL_DIV_LNEG,
             FIELD_REAL_LE_LDIV_EQ_NEG]
QED

Theorem FIELD_RAT_INV_EQ_DIV[field_simps]:
  !a : rat. rat_minv a = 1 / a
Proof
  simp [ratTheory.RAT_DIV_MULMINV]
QED

Theorem FIELD_RAT_RDIV_EQ[field_simps]:
  !a b c : rat. c <> 0 ==> (b / c = a <=> b = a * c)
Proof
  simp [ratTheory.RAT_LDIV_EQ, ratTheory.RAT_MUL_COMM]
QED

Theorem FIELD_RAT_NEG_DIV[field_simps]:
  !a b : rat. -(a / b) = -a / b
Proof
  simp [ratTheory.RAT_DIV_MULMINV,
        ratTheory.RAT_AINV_LMUL]
QED

Theorem FIELD_RAT_NEG_RDIV_EQ[field_simps]:
  !a b c : rat. b <> 0 ==>
    (-(a / b) = c <=> -a = c * b)
Proof
  metis_tac [FIELD_RAT_NEG_DIV,
             ratTheory.RAT_LDIV_EQ,
             ratTheory.RAT_MUL_COMM]
QED

Theorem FIELD_RAT_EQ_NEG_RDIV[field_simps]:
  !a b c : rat. b <> 0 ==>
    (c = -(a / b) <=> c * b = -a)
Proof
  metis_tac [FIELD_RAT_NEG_DIV,
             ratTheory.RAT_RDIV_EQ]
QED

Theorem FIELD_RAT_ADD_RDIV[field_simps]:
  !x y z : rat. z <> 0 ==>
    x + y / z = (x * z + y) / z
Proof
  simp [ratTheory.RAT_DIV_MULMINV,
        ratTheory.RAT_RDISTRIB,
        GSYM ratTheory.RAT_MUL_ASSOC,
        ratTheory.RAT_MUL_RINV]
QED

Theorem FIELD_RAT_RDIV_ADD[field_simps]:
  !x y z : rat. z <> 0 ==>
    x / z + y = (x + y * z) / z
Proof
  simp [ratTheory.RAT_DIV_MULMINV,
        ratTheory.RAT_RDISTRIB,
        GSYM ratTheory.RAT_MUL_ASSOC,
        ratTheory.RAT_MUL_RINV,
        AC ratTheory.RAT_ADD_ASSOC ratTheory.RAT_ADD_COMM,
        AC ratTheory.RAT_MUL_ASSOC ratTheory.RAT_MUL_COMM]
QED

Theorem FIELD_RAT_DIFF_RDIV[field_simps]:
  !x y z : rat. z <> 0 ==>
    x - y / z = (x * z - y) / z
Proof
  simp [ratTheory.RAT_SUB_ADDAINV,
        ratTheory.RAT_DIV_MULMINV,
        ratTheory.RAT_AINV_LMUL,
        ratTheory.RAT_RDISTRIB,
        GSYM ratTheory.RAT_MUL_ASSOC,
        ratTheory.RAT_MUL_RINV]
QED

Theorem FIELD_RAT_NEG_RDIV_ADD[field_simps]:
  !x y z : rat. z <> 0 ==>
    -(x / z) + y = (-x + y * z) / z
Proof
  simp [ratTheory.RAT_DIV_MULMINV,
        ratTheory.RAT_AINV_LMUL,
        ratTheory.RAT_RDISTRIB,
        GSYM ratTheory.RAT_MUL_ASSOC,
        ratTheory.RAT_MUL_RINV,
        AC ratTheory.RAT_ADD_ASSOC ratTheory.RAT_ADD_COMM,
        AC ratTheory.RAT_MUL_ASSOC ratTheory.RAT_MUL_COMM]
QED

Theorem FIELD_RAT_RDIV_DIFF[field_simps]:
  !x y z : rat. z <> 0 ==>
    x / z - y = (x - y * z) / z
Proof
  simp [ratTheory.RAT_SUB_ADDAINV,
        FIELD_RAT_RDIV_ADD,
        ratTheory.RAT_AINV_LMUL]
QED

Theorem FIELD_RAT_NEG_RDIV_DIFF[field_simps]:
  !x y z : rat. z <> 0 ==>
    -(x / z) - y = (-x - y * z) / z
Proof
  simp [ratTheory.RAT_SUB_ADDAINV,
        FIELD_RAT_NEG_RDIV_ADD,
        ratTheory.RAT_AINV_LMUL]
QED

Theorem FIELD_RAT_POS_LE_NEG_RDIV[field_simps]:
  !a b c : rat. 0 < c ==>
    (a <= -(b / c) <=> a * c <= -b)
Proof
  metis_tac [FIELD_RAT_NEG_DIV,
             ratTheory.RAT_RDIV_LEQ_POS]
QED

Theorem FIELD_RAT_NEG_LE_NEG_RDIV[field_simps]:
  !a b c : rat. c < 0 ==>
    (a <= -(b / c) <=> -b <= a * c)
Proof
  metis_tac [FIELD_RAT_NEG_DIV,
             ratTheory.RAT_RDIV_LEQ_NEG]
QED

Theorem FIELD_RAT_POS_LT_NEG_RDIV[field_simps]:
  !a b c : rat. 0 < c ==>
    (a < -(b / c) <=> a * c < -b)
Proof
  metis_tac [FIELD_RAT_NEG_DIV,
             ratTheory.RAT_RDIV_LES_POS]
QED

Theorem FIELD_RAT_NEG_LT_NEG_RDIV[field_simps]:
  !a b c : rat. c < 0 ==>
    (a < -(b / c) <=> -b < a * c)
Proof
  metis_tac [FIELD_RAT_NEG_DIV,
             ratTheory.RAT_RDIV_LES_NEG]
QED

Theorem FIELD_RAT_POS_NEG_RDIV_LT[field_simps]:
  !a b c : rat. 0 < c ==>
    (-(b / c) < a <=> -b < a * c)
Proof
  metis_tac [FIELD_RAT_NEG_DIV,
             ratTheory.RAT_LDIV_LES_POS,
             ratTheory.RAT_MUL_COMM]
QED

Theorem FIELD_RAT_NEG_NEG_RDIV_LT[field_simps]:
  !a b c : rat. c < 0 ==>
    (-(b / c) < a <=> a * c < -b)
Proof
  metis_tac [FIELD_RAT_NEG_DIV,
             ratTheory.RAT_LDIV_LES_NEG,
             ratTheory.RAT_MUL_COMM]
QED

Theorem FIELD_RAT_POS_NEG_RDIV_LE[field_simps]:
  !a b c : rat. 0 < c ==>
    (-(b / c) <= a <=> -b <= a * c)
Proof
  metis_tac [FIELD_RAT_NEG_DIV,
             ratTheory.RAT_LDIV_LEQ_POS,
             ratTheory.RAT_MUL_COMM]
QED

Theorem FIELD_RAT_NEG_NEG_RDIV_LE[field_simps]:
  !a b c : rat. c < 0 ==>
    (-(b / c) <= a <=> a * c <= -b)
Proof
  metis_tac [FIELD_RAT_NEG_DIV,
             ratTheory.RAT_LDIV_LEQ_NEG,
             ratTheory.RAT_MUL_COMM]
QED
