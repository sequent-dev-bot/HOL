structure intLinarith :> intLinarith =
struct

open HolKernel Conv Drule

fun dest_lit tm =
  Arbrat.fromAInt (intSyntax.int_of_term tm)

fun mk_lit value = intSyntax.term_of_int (Arbrat.toAInt value)

val ac_ops : linarithCancel.ac_ops =
  {dest_less = intSyntax.dest_less,
   dest_leq = intSyntax.dest_leq,
   strip_plus = intSyntax.strip_plus,
   mk_plus = intSyntax.mk_plus,
   assoc = integerTheory.INT_ADD_ASSOC,
   comm = integerTheory.INT_ADD_COMM,
   rid = integerTheory.INT_ADD_RID,
   ac_fallback = NONE}

val expression_conv =
  linarithCancel.mk_expression_conv intSyntax.int_ty
    [TRY_CONV intLib.INT_POLY_CONV,
     TRY_CONV intSimps.ADDR_CANON_CONV,
     TRY_CONV intReduce.RED_CONV]

val norm_conv =
  linarithCancel.mk_norm_conv
    {ac = ac_ops,
     ty = intSyntax.int_ty,
     leq_cancel = integerTheory.INT_LE_LADD,
     less_cancel = integerTheory.INT_LT_LADD,
     eq_cancel = integerTheory.INT_EQ_LADD,
     expression_conv = expression_conv,
     reduce_conv = intReduce.RED_CONV,
     refl_thms =
       [integerTheory.INT_LT_REFL, integerTheory.INT_LE_REFL]}

fun nonzero_literal divisor =
  if not (intSyntax.is_int_literal divisor) then NONE
  else
    SOME
      (EQT_ELIM
        (intReduce.REDUCE_CONV
          (boolSyntax.mk_neg
            (boolSyntax.mk_eq (divisor, intSyntax.zero_tm)))))
    handle HOL_ERR _ => NONE

val dest_divmod =
  linarithData.dest_divmod
    {dest_div=intSyntax.dest_div,dest_mod=intSyntax.dest_mod}

(* INT_DIVISION exposes directly the quotient/remainder facts represented
   existentially by INT_DIV_P and INT_MOD_P, without adding split cases. *)
fun division_facts dividend divisor nonzero =
  let
    val division =
      Thm.SPEC dividend
        (Thm.MP
          (Thm.SPEC divisor integerTheory.INT_DIVISION)
          nonzero)
    val sign =
      intReduce.REDUCE_CONV
        (intSyntax.mk_less (divisor, intSyntax.zero_tm))
  in
    CONJUNCTS
      (simpLib.SIMP_RULE boolSimps.bool_ss [sign] division)
  end

val nonneg =
  linarithData.injected_nonneg intSyntax.dest_injected integerTheory.INT_POS

(* atom_facts sees every atom of every carrier.  The Num arm deliberately
   fires on natural-number atoms; the divmod arm declines everything
   outside the integers. *)
fun atom_facts tm =
  case Lib.total intSyntax.dest_Num tm of
      SOME i => [Thm.SPEC i integerTheory.INT_OF_NUM]
    | NONE =>
        case dest_divmod tm of
            NONE => []
          | SOME (dividend, divisor) =>
              case nonzero_literal divisor of
                  NONE => []
                | SOME nonzero =>
                    division_facts dividend divisor nonzero

val instance : linarithData.linarith_instance =
  {ty = intSyntax.int_ty,
   discrete = SOME {lessD = [integerTheory.INT_LT_LE1]},
   dest =
     {dest_plus = intSyntax.dest_plus,
      dest_minus = SOME intSyntax.dest_minus,
      dest_neg = SOME intSyntax.dest_negated,
      dest_mult = intSyntax.dest_mult,
      dest_div = NONE,
      dest_suc = NONE,
      dest_lit = dest_lit,
      mk_lit = mk_lit,
      dest_less = intSyntax.dest_less,
      dest_leq = intSyntax.dest_leq},
   kit =
     {add_mono =
        [integerTheory.INT_LE_ADD2,
         integerTheory.INT_LT_ADD2,
         integerTheory.INT_LET_ADD2,
         integerTheory.INT_LTE_ADD2],
      mult_mono =
        [linarithInstTheory.INT_LE_LMUL_POS,
         linarithInstTheory.INT_LT_LMUL_POS],
      not_less = integerTheory.INT_NOT_LT,
      not_le = integerTheory.INT_NOT_LE,
      neqE = linarithInstTheory.INT_NEQ_E,
      nonneg = nonneg},
   norm_conv = norm_conv,
   nnf_rules = [],
   pre_split =
     [linarithInstTheory.INT_MIN_SPLIT,
      linarithInstTheory.INT_MAX_SPLIT,
      linarithInstTheory.INT_ABS_SPLIT],
   atom_facts = atom_facts}

val _ = linarithData.register_instance instance

val _ =
  linarithData.register_injection
    {from_ty = numSyntax.num,
     to_ty = intSyntax.int_ty,
     inj = intSyntax.int_injection,
     hom =
       {le = integerTheory.INT_LE,
        lt = integerTheory.INT_LT,
        eq = integerTheory.INT_INJ,
        add = integerTheory.INT_ADD,
        mul = integerTheory.INT_MUL}}

end
