structure realLinarith :> realLinarith =
struct

open HolKernel Conv

val ac_ops : linarithCancel.ac_ops =
  {dest_less = realSyntax.dest_less,
   dest_leq = realSyntax.dest_leq,
   strip_plus = realSyntax.strip_plus,
   mk_plus = realSyntax.mk_plus,
   assoc = realTheory.REAL_ADD_ASSOC,
   comm = realTheory.REAL_ADD_COMM,
   rid = realTheory.REAL_ADD_RID,
   ac_fallback = NONE}

val expression_conv =
  linarithCancel.mk_expression_conv realSyntax.real_ty
    [linarithCancel.safe_conv
       (TOP_DEPTH_CONV
         (FIRST_CONV
           [REWR_CONV intrealTheory.real_of_int_neg,
            REWR_CONV intrealTheory.real_of_int_num])),
     TRY_CONV RealField.REAL_POLY_CONV,
     TRY_CONV realSimps.REALADDCANON,
     TRY_CONV RealField.REAL_RAT_REDUCE_CONV]

val norm_conv =
  linarithCancel.mk_norm_conv
    {ac = ac_ops,
     ty = realSyntax.real_ty,
     leq_cancel = realTheory.REAL_LE_LADD,
     less_cancel = realTheory.REAL_LT_LADD,
     eq_cancel = realTheory.REAL_EQ_LADD,
     expression_conv = expression_conv,
     reduce_conv = RealField.REAL_RAT_REDUCE_CONV,
     refl_thms = [realTheory.REAL_LT_REFL, realTheory.REAL_LE_REFL]}

val nonneg =
  linarithData.injected_nonneg realSyntax.dest_injected realTheory.REAL_POS

val instance : linarithData.linarith_instance =
  {ty = realSyntax.real_ty,
   discrete = NONE,
   dest =
     {dest_plus = realSyntax.dest_plus,
      dest_minus = SOME realSyntax.dest_minus,
      dest_neg = SOME realSyntax.dest_negated,
      dest_mult = realSyntax.dest_mult,
      dest_div = SOME realSyntax.dest_div,
      dest_suc = NONE,
      dest_lit = RealArith.rat_of_term,
      mk_lit = RealArith.term_of_rat,
      dest_less = realSyntax.dest_less,
      dest_leq = realSyntax.dest_leq},
   kit =
     {add_mono =
        [realTheory.REAL_LE_ADD2,
         realTheory.REAL_LT_ADD2,
         realTheory.REAL_LET_ADD2,
         realTheory.REAL_LTE_ADD2],
      mult_mono =
        [realTheory.REAL_LE_LMUL_IMP,
         realTheory.REAL_LT_LMUL_IMP],
      not_less = realTheory.REAL_NOT_LT,
      not_le = realTheory.REAL_NOT_LE,
      neqE = linarithInstTheory.REAL_NEQ_E,
      nonneg = nonneg},
   norm_conv = norm_conv,
   nnf_rules = [],
   pre_split =
     [linarithInstTheory.REAL_MIN_SPLIT,
      linarithInstTheory.REAL_MAX_SPLIT,
      linarithInstTheory.REAL_ABS_SPLIT],
   atom_facts = (fn _ => [])}

val _ = linarithData.register_instance instance

val _ =
  linarithData.register_injection
    {from_ty = numSyntax.num,
     to_ty = realSyntax.real_ty,
     inj = realSyntax.real_injection,
     hom =
       {le = realTheory.REAL_OF_NUM_LE,
        lt = realTheory.REAL_OF_NUM_LT,
        eq = realTheory.REAL_OF_NUM_EQ,
        add = realTheory.REAL_OF_NUM_ADD,
        mul = realTheory.REAL_OF_NUM_MUL}}

val _ =
  linarithData.register_injection
    {from_ty = intSyntax.int_ty,
     to_ty = realSyntax.real_ty,
     inj = intrealSyntax.real_of_int_tm,
     hom =
       {le = intrealTheory.real_of_int_le,
        lt = intrealTheory.real_of_int_lt,
        eq = intrealTheory.real_of_int_11,
        add = intrealTheory.real_of_int_add,
        mul = intrealTheory.real_of_int_mul}}

end
