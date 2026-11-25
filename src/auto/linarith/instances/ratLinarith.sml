structure ratLinarith :> ratLinarith =
struct

open HolKernel Conv

val ERR = mk_HOL_ERR "ratLinarith"

val rat_of_int_tm =
  prim_mk_const {Name = "rat_of_int", Thy = "rat"}

val dest_rat_of_int =
  sdest_monop ("rat_of_int", "rat")
    (ERR "dest_rat_of_int" "not a rat_of_int application")

(* A quotient by zero has no rational value to report: ratTheory fixes
   only 0 / x = 0, and leaves x / 0 = x * rat_minv 0 unspecified.
   Failing here keeps such a quotient an opaque atom, which is how
   linarithDecomp's demult already treats a divisor cancelling to
   zero; every caller reaches dest_lit through Lib.total. *)
fun dest_lit tm =
  case Lib.total dest_rat_of_int tm of
      SOME integer => Arbrat.fromAInt (intSyntax.int_of_term integer)
    | NONE =>
        (case Lib.total ratSyntax.dest_rat_div tm of
             SOME (numerator, denominator) =>
               let
                 val d = dest_lit denominator
               in
                 if d = Arbrat.zero then
                   raise ERR "dest_lit" "zero denominator"
                 else Arbrat./ (dest_lit numerator, d)
               end
           | NONE => Arbrat.fromAInt (ratSyntax.int_of_term tm))

fun mk_lit value =
  let
    val numerator =
      ratSyntax.term_of_int (Arbrat.numerator value)
    val denominator = Arbrat.denominator value
  in
    if denominator = Arbnum.one then numerator
    else
      ratSyntax.mk_rat_div
        (numerator,
         ratSyntax.term_of_int (Arbint.fromNat denominator))
  end

fun is_poly_lit tm =
  null (Term.free_vars tm) andalso
  Option.isSome (Lib.total dest_lit tm)

val (_, _, _, _, _, rat_poly_conv) =
  Normalizer.SEMIRING_NORMALIZERS_CONV
    linarithInstTheory.RAT_POLY_CLAUSES
    linarithInstTheory.RAT_POLY_NEG_CLAUSES
    (is_poly_lit, ratReduce.RAT_ADD_CONV, ratReduce.RAT_MUL_CONV,
     NO_CONV)
    (fn left => fn right => Term.compare (left, right) = LESS)

val ac_ops : linarithCancel.ac_ops =
  {dest_less = ratSyntax.dest_rat_les,
   dest_leq = ratSyntax.dest_rat_leq,
   strip_plus = ratSyntax.strip_rat_add,
   mk_plus = ratSyntax.mk_rat_add,
   assoc = ratTheory.RAT_ADD_ASSOC,
   comm = ratTheory.RAT_ADD_COMM,
   rid = ratTheory.RAT_ADD_RID,
   ac_fallback = NONE}

fun division_conv tm =
  let
    val (_, denominator) = ratSyntax.dest_rat_div tm
    val denominator_thm =
      linarithCancel.safe_conv rat_poly_conv denominator
    val denominator' =
      #2 (boolSyntax.dest_eq (Thm.concl denominator_thm))
    val normalized =
      RAND_CONV (fn _ => denominator_thm) tm
    val normalized_tm =
      #2 (boolSyntax.dest_eq (Thm.concl normalized))
    val coefficient =
      ratSyntax.mk_rat_div (ratSyntax.rat_1_tm, denominator')
    val coefficient_thm =
      (REWR_CONV ratTheory.RAT_DIV_MULMINV THENC
       REWR_CONV ratTheory.RAT_MUL_LID) coefficient
    val expanded =
      (REWR_CONV ratTheory.RAT_DIV_MULMINV THENC
       RAND_CONV (REWR_CONV (Thm.SYM coefficient_thm)) THENC
       REWR_CONV ratTheory.RAT_MUL_COMM) normalized_tm
  in
    Thm.TRANS normalized expanded
  end

val expression_conv =
  linarithCancel.mk_expression_conv ratSyntax.rat_ty
    [linarithCancel.safe_conv
       (TOP_DEPTH_CONV
         (FIRST_CONV
           [REWR_CONV ratTheory.rat_of_int_ainv,
            REWR_CONV ratTheory.rat_of_int_of_num])),
     linarithCancel.safe_conv (DEPTH_CONV division_conv),
     linarithCancel.safe_conv rat_poly_conv]

val norm_conv =
  linarithCancel.mk_norm_conv
    {ac = ac_ops,
     ty = ratSyntax.rat_ty,
     leq_cancel = ratTheory.RAT_LEQ_LADD,
     less_cancel = ratTheory.RAT_LES_LADD,
     eq_cancel = ratTheory.RAT_EQ_LADD,
     expression_conv = expression_conv,
     reduce_conv = ratLib.RAT_BASIC_ARITH_CONV,
     refl_thms = [ratTheory.RAT_LES_REF, ratTheory.RAT_LEQ_REF]}

val nonneg =
  linarithData.injected_nonneg ratSyntax.dest_rat_of_num
    linarithInstTheory.RAT_OF_NUM_NONNEG

val instance : linarithData.linarith_instance =
  {ty = ratSyntax.rat_ty,
   discrete = NONE,
   dest =
     {dest_plus = ratSyntax.dest_rat_add,
      dest_minus = SOME ratSyntax.dest_rat_sub,
      dest_neg = SOME ratSyntax.dest_rat_ainv,
      dest_mult = ratSyntax.dest_rat_mul,
      dest_div = SOME ratSyntax.dest_rat_div,
      dest_suc = NONE,
      dest_lit = dest_lit,
      mk_lit = mk_lit,
      dest_less = ratSyntax.dest_rat_les,
      dest_leq = ratSyntax.dest_rat_leq},
   kit =
     {add_mono =
        [ratTheory.RAT_ADD_MONO,
         linarithInstTheory.RAT_LT_ADD2,
         linarithInstTheory.RAT_LET_ADD2,
         linarithInstTheory.RAT_LTE_ADD2],
      mult_mono =
        [linarithInstTheory.RAT_LEQ_LMUL_POS,
         linarithInstTheory.RAT_LT_LMUL_POS],
      not_less = ratTheory.RAT_LEQ_LES,
      not_le = ratTheory.RAT_LES_LEQ,
      neqE = linarithInstTheory.RAT_NEQ_E,
      nonneg = nonneg},
   norm_conv = norm_conv,
   nnf_rules = [],
   pre_split = [],
   atom_facts = (fn _ => [])}

val _ = linarithData.register_instance instance

val _ =
  linarithData.register_injection
    {from_ty = numSyntax.num,
     to_ty = ratSyntax.rat_ty,
     inj = ratSyntax.rat_of_num_tm,
     hom =
       {le = ratTheory.RAT_OF_NUM_LEQ,
        lt = ratTheory.RAT_OF_NUM_LES,
        eq = CONJUNCT1 ratTheory.RAT_EQ_NUM_CALCULATE,
        add = CONJUNCT1 ratTheory.RAT_ADD_NUM_CALCULATE,
        mul = CONJUNCT1 ratTheory.RAT_MUL_NUM_CALCULATE}}

val _ =
  linarithData.register_injection
    {from_ty = intSyntax.int_ty,
     to_ty = ratSyntax.rat_ty,
     inj = rat_of_int_tm,
     hom =
       {le = ratTheory.rat_of_int_LE,
        lt = ratTheory.rat_of_int_LT,
        eq = ratTheory.rat_of_int_11,
        add = ratTheory.rat_of_int_ADD,
        mul = ratTheory.rat_of_int_MUL}}

end
