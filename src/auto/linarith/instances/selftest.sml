open HolKernel testutils linarithInstTheory linarithCorpus

fun clean_norm (instance : linarithData.linarith_instance) tm =
  null (Thm.hyp (#norm_conv instance tm))

val int_instance = intLinarith.instance
val real_instance = realLinarith.instance
val rat_instance = ratLinarith.instance

val ix = Term.mk_var ("linarith_int_x", intSyntax.int_ty)
val iy = Term.mk_var ("linarith_int_y", intSyntax.int_ty)
val iz = Term.mk_var ("linarith_int_z", intSyntax.int_ty)
val i0 = intSyntax.zero_tm
val i2 = intSyntax.term_of_int (Arbint.fromInt 2)
val i3 = intSyntax.term_of_int (Arbint.fromInt 3)
val i7 = intSyntax.term_of_int (Arbint.fromInt 7)
val i8 = intSyntax.term_of_int (Arbint.fromInt 8)
val im1 = intSyntax.term_of_int (Arbint.fromInt ~1)
val im3 = intSyntax.term_of_int (Arbint.fromInt ~3)

fun iplus left right = intSyntax.mk_plus (left, right)
fun ileq left right = intSyntax.mk_leq (left, right)
fun iless left right = intSyntax.mk_less (left, right)

val _ =
  check
    ("int norm_conv satisfies cancellation and decision contract",
     fn () =>
       Term.aconv
         (normalized_rhs int_instance
           (ileq (iplus ix i3) (iplus ix i2)))
         boolSyntax.F andalso
       Term.aconv
         (normalized_rhs int_instance
           (ileq (iplus ix iy) (iplus iy iz)))
         (ileq ix iz) andalso
       Term.aconv
         (normalized_rhs int_instance (iless i7 i8))
         boolSyntax.T andalso
       clean_norm int_instance
         (ileq (iplus ix i3) (iplus ix i2)))

(* Replay normalizes the two sides of a derived relation, so norm_conv is
   offered bare expressions as well as relations.  It used to answer
   those by raising UNCHANGED out of the whole conversion, because
   relation_conv signalled "not a relation" that way and ORELSEC catches
   HOL_ERR only. *)
val _ =
  check
    ("int norm_conv canonicalizes a bare expression",
     fn () =>
       Term.aconv
         (canonical_form int_instance (iplus i3 ix))
         (canonical_form int_instance (iplus ix i3)))

val _ =
  check
    ("int divmod facts cover INT_DIV_P and INT_MOD_P behavior",
     fn () =>
       let
         val facts = #atom_facts int_instance
         val positive = facts (intSyntax.mk_mod (ix, i3))
         val negative = facts (intSyntax.mk_div (ix, im3))
       in
         List.length positive = 3 andalso
         List.length negative = 3 andalso
         null (facts (intSyntax.mk_mod (ix, i0))) andalso
         List.all (null o Thm.hyp) (positive @ negative)
       end)

val rx = Term.mk_var ("linarith_real_x", realSyntax.real_ty)
val ry = Term.mk_var ("linarith_real_y", realSyntax.real_ty)
val rz = Term.mk_var ("linarith_real_z", realSyntax.real_ty)
val r0 = realSyntax.zero_tm
val r2 = RealArith.term_of_rat (Arbrat.fromInt 2)
val r3 = RealArith.term_of_rat (Arbrat.fromInt 3)
val r7 = RealArith.term_of_rat (Arbrat.fromInt 7)
val r8 = RealArith.term_of_rat (Arbrat.fromInt 8)
val rim2 =
  intrealSyntax.mk_real_of_int
    (intSyntax.term_of_int (Arbint.fromInt ~2))
val rhalf =
  RealArith.term_of_rat
    (Arbrat./ (Arbrat.one, Arbrat.two))

fun rplus left right = realSyntax.mk_plus (left, right)
fun rleq left right = realSyntax.mk_leq (left, right)
fun rless left right = realSyntax.mk_less (left, right)

val _ =
  check
    ("real norm_conv satisfies cancellation and decision contract",
     fn () =>
       Term.aconv
         (normalized_rhs real_instance
           (rleq (rplus rx r3) (rplus rx r2)))
         boolSyntax.F andalso
       Term.aconv
         (normalized_rhs real_instance
           (rleq (rplus rx ry) (rplus ry rz)))
         (rleq rx rz) andalso
       Term.aconv
         (normalized_rhs real_instance (rless r7 r8))
         boolSyntax.T andalso
       Term.aconv
         (normalized_rhs real_instance
           (boolSyntax.mk_eq (rplus rhalf rhalf,
              realSyntax.one_tm)))
         boolSyntax.T andalso
       Term.aconv
         (normalized_rhs real_instance
           (boolSyntax.mk_eq
             (rim2, RealArith.term_of_rat (Arbrat.fromInt ~2))))
         boolSyntax.T andalso
       clean_norm real_instance
         (rleq (rplus rx r3) (rplus rx r2)))

val _ =
  check
    ("real norm_conv canonicalizes a bare expression",
     fn () =>
       Term.aconv
         (canonical_form real_instance (rplus r3 rx))
         (canonical_form real_instance (rplus rx r3)))

(* REAL_POLY_CONV turns x / 3 into 1 / 3 * x, and RealField's rational
   compset did not terminate on that literal, so a real relation
   containing a division hung the whole tactic. *)
val rdiv3 = realSyntax.mk_div (rx, r3)

val _ =
  check
    ("real norm_conv terminates on a relation containing division",
     fn () => clean_norm real_instance (rleq rdiv3 ry))

val _ =
  check
    ("real battery reasons about division by a literal",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], boolSyntax.mk_imp
                (rleq rdiv3 ry,
                 rleq rx (realSyntax.mk_mult (r3, ry)))))

val qx = Term.mk_var ("linarith_rat_x", ratSyntax.rat_ty)
val qy = Term.mk_var ("linarith_rat_y", ratSyntax.rat_ty)
val qz = Term.mk_var ("linarith_rat_z", ratSyntax.rat_ty)
val q0 = ratSyntax.rat_0_tm
val q2 = #mk_lit (#dest rat_instance) (Arbrat.fromInt 2)
val q3 = #mk_lit (#dest rat_instance) (Arbrat.fromInt 3)
val q7 = #mk_lit (#dest rat_instance) (Arbrat.fromInt 7)
val q8 = #mk_lit (#dest rat_instance) (Arbrat.fromInt 8)
val rat_of_int_tm =
  prim_mk_const {Name = "rat_of_int", Thy = "rat"}
val qim2 =
  Term.mk_comb
    (rat_of_int_tm, intSyntax.term_of_int (Arbint.fromInt ~2))
val qhalf =
  #mk_lit (#dest rat_instance)
    (Arbrat./ (Arbrat.one, Arbrat.two))

fun qplus left right = ratSyntax.mk_rat_add (left, right)
fun qleq left right = ratSyntax.mk_rat_leq (left, right)
fun qless left right = ratSyntax.mk_rat_les (left, right)

val _ =
  check
    ("rat norm_conv satisfies cancellation and decision contract",
     fn () =>
       Term.aconv
         (normalized_rhs rat_instance
           (qleq (qplus qx q3) (qplus qx q2)))
         boolSyntax.F andalso
       Term.aconv
         (normalized_rhs rat_instance
           (qleq (qplus qx qy) (qplus qy qz)))
         (qleq qx qz) andalso
       Term.aconv
         (normalized_rhs rat_instance (qless q7 q8))
         boolSyntax.T andalso
       #dest_lit (#dest rat_instance) qhalf =
         Arbrat./ (Arbrat.one, Arbrat.two) andalso
       Term.aconv
         (normalized_rhs rat_instance
           (boolSyntax.mk_eq (qplus qhalf qhalf,
              ratSyntax.rat_1_tm)))
         boolSyntax.T andalso
       Term.aconv
         (normalized_rhs rat_instance
           (boolSyntax.mk_eq
             (qim2, #mk_lit (#dest rat_instance) (Arbrat.fromInt ~2))))
         boolSyntax.T andalso
       clean_norm rat_instance
         (qleq (qplus qx q3) (qplus qx q2)))

val _ =
  check
    ("int battery uses abs splitting through Tactical.VALID",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], ileq i0 (intSyntax.mk_absval ix)))

val abs_ix_eq_ix =
  boolSyntax.mk_eq (intSyntax.mk_absval ix, ix)
val abs_iy_eq_iy =
  boolSyntax.mk_eq (intSyntax.mk_absval iy, iy)
val pruned_abs_goal =
  boolSyntax.mk_disj (abs_ix_eq_ix, abs_iy_eq_iy)

fun same_search_stats
      ({nodes = nodes1, refutations = refutations1,
        disjunction_splits = disjunction_splits1,
        operator_splits = operator_splits1,
        augmentations = augmentations1} : linarithLib.search_stats)
      ({nodes = nodes2, refutations = refutations2,
        disjunction_splits = disjunction_splits2,
        operator_splits = operator_splits2,
        augmentations = augmentations2} : linarithLib.search_stats) =
  nodes1 = nodes2 andalso refutations1 = refutations2 andalso
  disjunction_splits1 = disjunction_splits2 andalso
  operator_splits1 = operator_splits2 andalso
  augmentations1 = augmentations2

fun run_pruned_abs () =
  let
    val closed =
      valid_closes (linarithLib.LINARITH_TAC [])
        ([ileq i0 ix], pruned_abs_goal)
  in
    (closed, linarithLib.last_search_stats ())
  end

fun expected_pruned_stats
      ({nodes, refutations, disjunction_splits,
        operator_splits, augmentations} : linarithLib.search_stats) =
  nodes = 4 andalso refutations = 1 andalso
  disjunction_splits = 1 andalso operator_splits = 1 andalso
  augmentations = 0

val _ =
  check
    ("an inconsistent ABS branch is pruned before a later split",
     fn () =>
       let
         val (closed1, stats1) = run_pruned_abs ()
         val (closed2, stats2) = run_pruned_abs ()
       in
         closed1 andalso closed2 andalso
         same_search_stats stats1 stats2 andalso
         expected_pruned_stats stats1
       end)

val _ =
  check
    ("a satisfiable ABS sign system still returns failure",
     fn () =>
       tactic_fails (linarithLib.LINARITH_TAC [])
         ([abs_ix_eq_ix], boolSyntax.mk_eq (ix, i0)))

val nine_abs_recurrence =
  ``x3 = ABS x2 - x1 ==> x4 = ABS x3 - x2 ==>
    x5 = ABS x4 - x3 ==> x6 = ABS x5 - x4 ==>
    x7 = ABS x6 - x5 ==> x8 = ABS x7 - x6 ==>
    x9 = ABS x8 - x7 ==> x10 = ABS x9 - x8 ==>
    x11 = ABS x10 - x9 ==> x1 = x10 /\ x2 = (x11 : int)``

fun expected_recurrence_stats
      ({nodes, refutations, disjunction_splits,
        operator_splits, augmentations} : linarithLib.search_stats) =
  nodes = 363 andalso refutations = 243 andalso
  disjunction_splits = 121 andalso operator_splits = 120 andalso
  augmentations = 0

val _ =
  check
    ("nine-step ABS recurrence has a stable pruned search size",
     fn () =>
       let
         val closed =
           valid_closes (linarithLib.LINARITH_TAC [])
             ([], nine_abs_recurrence)
       in
         closed andalso
         expected_recurrence_stats (linarithLib.last_search_stats ())
       end)

val imod3 = intSyntax.mk_mod (ix, i3)
val idiv3 = intSyntax.mk_div (ix, i3)

val _ =
  check
    ("int battery uses discreteness and min/max splitting",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([iless ix iy], ileq (iplus ix intSyntax.one_tm) iy) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], ileq (intSyntax.mk_min (ix, iy)) ix) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], ileq ix (intSyntax.mk_max (ix, iy))))

val _ =
  check
    ("int battery uses P-form divmod behavior through Tactical.VALID",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], boolSyntax.mk_eq
           (ix, iplus (intSyntax.mk_mult (idiv3, i3)) imod3)) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], ileq i0 imod3) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], iless imod3 i3) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], iless im3 (intSyntax.mk_mod (ix, im3))) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], ileq (intSyntax.mk_mod (ix, im3)) i0))

val midpoint = realSyntax.mk_div (rplus rx ry, r2)

val _ =
  check
    ("real battery proves the lower dense midpoint bound",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([rless rx ry], rless rx midpoint))

val _ =
  check
    ("real battery proves the upper dense midpoint bound",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([rless rx ry], rless midpoint ry))

val _ =
  check
    ("real battery uses abs splitting through Tactical.VALID",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], rleq r0 (realSyntax.mk_absval rx)))

(* The bound on a conditional between literals is the registry's and
   not one instance's: the carrier is the conditional's own type, so a
   registered instance has it without declaring anything.  The negative
   branch is the case the naturals cannot state. *)
val int_conditional =
  boolSyntax.mk_cond (Term.mk_var ("linarith_int_condition", Type.bool),
                      i3, im3)

val _ =
  check
    ("a conditional between int literals is bounded by both branches",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], ileq int_conditional i3) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], ileq im3 int_conditional) andalso
       tactic_fails (linarithLib.LINARITH_TAC [])
         ([], iless int_conditional i3))

val rat_transitivity =
  boolSyntax.mk_imp
    (boolSyntax.mk_conj (qleq qx qy, qless qy qz),
     qless qx qz)
val qmidpoint = ratSyntax.mk_rat_div (qplus qx qy, q2)

val _ =
  check
    ("real battery uses min/max splitting through Tactical.VALID",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], rleq (realSyntax.mk_min (rx, ry)) rx) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], rleq rx (realSyntax.mk_max (rx, ry))))

val _ =
  check
    ("rat field normalization proves dense midpoint bounds",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([qless qx qy], qless qx qmidpoint) andalso
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([qless qx qy], qless qmidpoint qy))

val _ =
  check
    ("rat battery exceeds RAT_BASIC_ARITH_CONV",
     fn () =>
       tactic_fails (Tactic.CONV_TAC ratLib.RAT_BASIC_ARITH_CONV)
         ([], rat_transitivity) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], rat_transitivity) andalso
       Term.aconv
         (Thm.concl (linarithLib.LINARITH_PROVE rat_transitivity))
         rat_transitivity)

val n = Term.mk_var ("linarith_injection_n", numSyntax.num)
val m = Term.mk_var ("linarith_injection_m", numSyntax.num)
val p = Term.mk_var ("linarith_injection_p", numSyntax.num)
val ii = Term.mk_var ("linarith_injection_i", intSyntax.int_ty)
val ij = Term.mk_var ("linarith_injection_j", intSyntax.int_ty)
val ik = Term.mk_var ("linarith_injection_k", intSyntax.int_ty)
val rr = Term.mk_var ("linarith_injection_r", realSyntax.real_ty)
val qq = Term.mk_var ("linarith_injection_q", ratSyntax.rat_ty)
val n_int = intSyntax.mk_injected n
val m_int = intSyntax.mk_injected m
val p_int = intSyntax.mk_injected p
val ii_real = intrealSyntax.mk_real_of_int ii
val ij_real = intrealSyntax.mk_real_of_int ij
val ik_real = intrealSyntax.mk_real_of_int ik
val n_rat = ratSyntax.mk_rat_of_num n
val m_rat = ratSyntax.mk_rat_of_num m
val p_rat = ratSyntax.mk_rat_of_num p

fun inject from_ty to_ty tm =
  let
    val injection =
      valOf (linarithData.injection_for from_ty to_ty)
  in
    Term.mk_comb (#inj injection, tm)
  end

val n_real = inject numSyntax.num realSyntax.real_ty n
val m_real = inject numSyntax.num realSyntax.real_ty m
val ii_rat = inject intSyntax.int_ty ratSyntax.rat_ty ii
val ij_rat = inject intSyntax.int_ty ratSyntax.rat_ty ij
val ik_rat = inject intSyntax.int_ty ratSyntax.rat_ty ik
val im2_rat =
  inject intSyntax.int_ty ratSyntax.rat_ty
    (intSyntax.term_of_int (Arbint.fromInt ~2))

val _ =
  check
    ("all specified injections are registered at module load",
     fn () =>
       List.all Option.isSome
         [linarithData.injection_for numSyntax.num intSyntax.int_ty,
          linarithData.injection_for numSyntax.num realSyntax.real_ty,
          linarithData.injection_for intSyntax.int_ty realSyntax.real_ty,
          linarithData.injection_for numSyntax.num ratSyntax.rat_ty,
          linarithData.injection_for intSyntax.int_ty ratSyntax.rat_ty] andalso
       #dest_lit (#dest rat_instance) im2_rat = Arbrat.fromInt ~2)

val _ =
  check
    ("mixed num-to-int replay uses the registered injection",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([numSyntax.mk_leq (n, m), ileq m_int ii], ileq n_int ii))

val _ =
  check
    ("mixed int-to-real replay uses the registered injection",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([ileq ii ij, rleq ij_real rr], rleq ii_real rr))

val _ =
  check
    ("mixed num-to-real replay uses the registered injection",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([numSyntax.mk_leq (n, m), rleq m_real rr], rleq n_real rr))

val _ =
  check
    ("num-to-int strict-order injection homomorphism replays",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([numSyntax.mk_less (n, m)], iless n_int m_int))

val _ =
  check
    ("int-to-real strict-order injection homomorphism replays",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([iless ii ij], rless ii_real ij_real))

val _ =
  check
    ("num-to-rat strict-order injection homomorphism replays",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([numSyntax.mk_less (n, m)], qless n_rat m_rat))

val _ =
  check
    ("int-to-rat strict-order injection homomorphism replays",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([iless ii ij], qless ii_rat ij_rat))

val _ =
  check
    ("negative injected literals normalize during mixed replay",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([ileq ii (intSyntax.term_of_int (Arbint.fromInt ~2))],
          rleq ii_real rim2) andalso
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([ileq ii (intSyntax.term_of_int (Arbint.fromInt ~2))],
          qleq ii_rat qim2))

val _ =
  check
    ("mixed int-to-rat replay uses the registered injection",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([ileq ii ij, qleq ij_rat qq], qleq ii_rat qq))

val _ =
  check
    ("mixed num-to-rat replay uses the registered injection",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([numSyntax.mk_leq (n, m), qleq m_rat qq], qleq n_rat qq))

val _ =
  check
    ("mixed sibling carriers replay through their common source",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([rleq n_real r0, qless q0 n_rat], boolSyntax.F))

val _ =
  check
    ("num-to-int add homomorphism normalizes compound source terms",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([numSyntax.mk_leq (numSyntax.mk_plus (n, m), p)],
          ileq (iplus n_int m_int) p_int))

val _ =
  check
    ("int-to-real add homomorphism normalizes compound source terms",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([ileq (iplus ii ij) ik],
          rleq (rplus ii_real ij_real) ik_real))

val _ =
  check
    ("int-to-rat add homomorphism normalizes compound source terms",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([ileq (iplus ii ij) ik],
          qleq (qplus ii_rat ij_rat) ik_rat))

val _ =
  check
    ("num-to-rat add homomorphism normalizes compound source terms",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([numSyntax.mk_leq (numSyntax.mk_plus (n, m), p)],
          qleq (qplus n_rat m_rat) p_rat))

val _ =
  check
    ("injection mul homomorphisms normalize compound source terms",
     fn () =>
       let
         val n2 = numSyntax.mk_numeral (Arbnum.fromInt 2)
         val n2_int = intSyntax.mk_injected n2
       in
         valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
           ([numSyntax.mk_leq (numSyntax.mk_mult (n2, n), p)],
            ileq (intSyntax.mk_mult (n2_int, n_int)) p_int)
       end)

(* A tactic that raises has not closed the goal, and reporting that as a
   failed assertion rather than an escaping exception keeps the goal
   that noticed legible and lets the rest of the suite run. *)
fun simple_closes goal =
  valid_closes (linarithLib.SIMPLE_LINARITH_TAC []) goal
  handle Feedback.HOL_ERR _ => false

(* An injection is stripped from an argument built out of the operators
   it distributes over, and a successor is one of them: SUC k is the sum
   k + 1, which is how the source carrier decomposes it as well.  Kept
   whole, &(SUC n) was an atom unrelated to n, and a goal the naturals
   close stayed open one carrier up. *)
val n_suc = numSyntax.mk_suc n

val _ =
  check
    ("injected successors decompose in every target carrier",
     fn () =>
       simple_closes ([], iless n_int (intSyntax.mk_injected n_suc)) andalso
       simple_closes
         ([], rless n_real
                (inject numSyntax.num realSyntax.real_ty n_suc)) andalso
       simple_closes ([], qless n_rat (ratSyntax.mk_rat_of_num n_suc)))

val _ =
  check
    ("Nonneg of injected atoms strengthens all target carriers",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([], ileq i0 n_int) andalso
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([], rleq r0 (realSyntax.mk_injected n)) andalso
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([], qleq q0 n_rat))

val _ =
  check
    ("golden Added replay lifts Nonneg through num-to-int injection",
     fn () =>
       let
         val bad = ileq n_int im1
         val theorem =
           linarithReplay.mkthm traceUtil.silent
             [Thm.ASSUME bad]
             (linarithSolve.Added
               (linarithSolve.Nonneg n_int, linarithSolve.Asm 0))
       in
         Term.aconv (Thm.concl theorem) boolSyntax.F
       end)

(* Both sides of the golden above are int -- Nonneg answers in the
   carrier of the atom it names -- so it does not reach the add
   fallback.  This one does: mkthm returns each assumption in the
   carrier it was stated in, so summing a num premise with an int one
   has no direct addition available, and only the conversion closure's
   lift of m < n to &m < &n closes it.  The mixed-carrier tactic checks
   above drive the same path from the surface. *)
val _ =
  check
    ("golden Added replay sums two carriers through the injection",
     fn () =>
       let
         val theorem =
           linarithReplay.mkthm traceUtil.silent
             [Thm.ASSUME (numSyntax.mk_less (m, n)),
              Thm.ASSUME (ileq n_int m_int)]
             (linarithSolve.Added
               (linarithSolve.Asm 0, linarithSolve.Asm 1))
       in
         Term.aconv (Thm.concl theorem) boolSyntax.F
       end)

(* Scaling an equality applies (\v. v * n) to both of its sides.  The
   int and rat instances normalize expressions with polynomial
   conversions, which rewrite polynomials and not redexes, so a side
   left unreduced reaches cancellation as an atom distinct from the
   multiple it has to meet on the other side, and the certificate
   replays to a true relation rather than to falsity. *)
val _ =
  check
    ("golden Multiplied replay scales an int equality to falsity",
     fn () =>
       let
         val doubled = intSyntax.mk_mult (i2, ix)
         val contradiction =
           boolSyntax.mk_eq (doubled, iplus doubled intSyntax.one_tm)
       in
         Term.aconv
           (Thm.concl
             (linarithReplay.mkthm traceUtil.silent [Thm.ASSUME contradiction]
               (linarithSolve.Multiplied
                 (Arbint.fromInt 3, linarithSolve.Asm 0))))
           boolSyntax.F
         handle Feedback.HOL_ERR _ => false
       end)

(* A rational assumption with a denominator reaches the search already
   scaled by it, so Multiplied is the top of its certificate and there
   is no later pass over the whole relation to repair what scaling
   left. *)
val qhalf_x = ratSyntax.mk_rat_mul (qhalf, qx)
val q1 = #mk_lit (#dest rat_instance) Arbrat.one

val _ =
  check
    ("rat replay scales a fractional equality to falsity",
     fn () =>
       simple_closes
         ([boolSyntax.mk_eq (qhalf_x, qplus qhalf_x q1)],
          boolSyntax.F))

(* rat_minv 0 is unspecified -- ratTheory fixes 0 / x = 0 and nothing
   about x / 0 -- so a quotient by zero has no literal value to report.
   dest_lit used to answer 0 for one, which made &5 / 0q a constant in
   the decomposed row: the solver believed it had refuted the negation
   of &5 / 0q < 1q, replay could not build the theorem from that, and
   the run ended in an internal-inconsistency warning.  The quotient is
   an atom instead, as demult already treats a divisor that cancels to
   zero. *)
val q5 = #mk_lit (#dest rat_instance) (Arbrat.fromInt 5)
val qdiv0 = ratSyntax.mk_rat_div (q5, q0)

fun warnings_while operation =
  let
    val warnings = ref ([] : string list)
    val saved = !Feedback.WARNING_outstream
    fun restore () = Feedback.WARNING_outstream := saved
    val _ =
      Feedback.WARNING_outstream :=
        (fn message => warnings := message :: !warnings)
    val _ =
      (ignore (Lib.total operation ()); restore ())
      handle e => (restore (); raise e)
  in
    !warnings
  end

val _ =
  check
    ("a zero denominator leaves a rational quotient an opaque atom",
     fn () =>
       not (Option.isSome
              (Lib.total (#dest_lit (#dest rat_instance)) qdiv0)) andalso
       null (warnings_while
               (fn () =>
                  linarithLib.LINARITH_TAC [] ([], qless qdiv0 q1))) andalso
       simple_closes ([qless qdiv0 qx], qless qdiv0 (qplus qx q1)))

val _ =
  check
    ("load-time registration warns and does not duplicate entries",
     fn () =>
       let
         val instance_count =
           List.length (linarithData.all_instances ())
         val injection_count =
           List.length (linarithData.injections ())
         val old_injections = linarithData.injections ()
         val warnings = ref ([] : string list)
         val saved = !Feedback.WARNING_outstream
         val _ =
           Feedback.WARNING_outstream :=
             (fn message => warnings := message :: !warnings)
         fun restore () = Feedback.WARNING_outstream := saved
         val _ =
           (List.app linarithData.register_instance
              [int_instance, real_instance, rat_instance];
            List.app linarithData.register_injection
              (List.rev old_injections);
            restore ())
           handle e => (restore (); raise e)
       in
         List.length (!warnings) = 3 andalso
         List.all
           (String.isSubstring "replacing the linarith instance")
           (!warnings) andalso
         instance_count = List.length (linarithData.all_instances ()) andalso
         injection_count = List.length (linarithData.injections ())
       end)

fun neq tm = boolSyntax.mk_neg tm

val nx = Term.mk_var ("linarith_neq_num", numSyntax.num)
val jx = Term.mk_var ("linarith_neq_int", intSyntax.int_ty)
val sx = Term.mk_var ("linarith_neq_real", realSyntax.real_ty)
val tx = Term.mk_var ("linarith_neq_rat", ratSyntax.rat_ty)
val num_eq0 = boolSyntax.mk_eq (nx, numSyntax.zero_tm)
val int_eq0 = boolSyntax.mk_eq (jx, i0)
val real_eq0 = boolSyntax.mk_eq (sx, r0)
val rat_eq0 = boolSyntax.mk_eq (tx, q0)
val equalities = [num_eq0, int_eq0, real_eq0, rat_eq0]
val disequalities = map neq equalities
val zero_bounds =
  [numSyntax.mk_leq (numSyntax.zero_tm, nx),
   numSyntax.mk_leq (nx, numSyntax.zero_tm),
   ileq i0 jx, ileq jx i0,
   rleq r0 sx, rleq sx r0,
   qleq q0 tx, qleq tx q0]
val neq_config : linarithData.linarith_config =
  {neq_limit = 4, split_limit = 9}

fun cross_neq_forward order =
  let
    val assumptions = map Thm.ASSUME (order @ zero_bounds)
  in
    Term.aconv
      (Thm.concl
        (linarithReplay.fwd_prove_in (Context.snapshot ())
           neq_config assumptions boolSyntax.F))
      boolSyntax.F
  end

val _ =
  check
    ("cross-type neq replay is independent of premise permutation",
     fn () =>
       cross_neq_forward disequalities andalso
       cross_neq_forward (List.rev disequalities) andalso
       valid_closes
         (linarithLib.CFG_LINARITH_TAC neq_config [])
         (disequalities @ zero_bounds, boolSyntax.F) andalso
       valid_closes
         (linarithLib.CFG_LINARITH_TAC neq_config [])
         (List.rev disequalities @ zero_bounds, boolSyntax.F))

val side_ss =
  simpLib.++ (boolSimps.bool_ss, linarithLib.LINARITH_ss)

fun conditional_goal condition =
  boolSyntax.mk_eq
    (boolSyntax.mk_cond (condition, boolSyntax.T, boolSyntax.F),
     boolSyntax.T)

val _ =
  check
    ("LINARITH_ss discharges int real and rat side conditions",
     fn () =>
       valid_closes (simpLib.FULL_SIMP_TAC side_ss [])
         ([ileq ix iy, ileq iy iz], conditional_goal (ileq ix iz)) andalso
       valid_closes (simpLib.FULL_SIMP_TAC side_ss [])
         ([rleq rx ry, rleq ry rz], conditional_goal (rleq rx rz)) andalso
       valid_closes (simpLib.FULL_SIMP_TAC side_ss [])
         ([qleq qx qy, qleq qy qz], conditional_goal (qleq qx qz)))

val _ =
  check
    ("LINARITH_ext_ss discharges int real and rat side conditions",
     fn () =>
       let
         val ss =
           simpLib.++ (boolSimps.bool_ss, linarithLib.LINARITH_ext_ss)
         val tactic = simpLib.FULL_SIMP_TAC ss []
       in
         valid_closes tactic
           ([ileq ix iy, ileq iy iz], conditional_goal (ileq ix iz)) andalso
         valid_closes tactic
           ([rleq rx ry, rleq ry rz], conditional_goal (rleq rx rz)) andalso
         valid_closes tactic
           ([qleq qx qy, qleq qy qz], conditional_goal (qleq qx qz))
       end)

(* Translation of the 20 lemma goals in Isabelle's Arith_Examples.thy at
   f7e02b7e1f31 that need int, real or rat syntax, in source order.  The
   other 34 are num/bool and are stated in linarithCorpus, which both
   this suite and the pre-boss one run; assembling the full corpus is
   merging the two partitions of the numbering, and the numbering check
   below is what says the assembled list is all 54, once each.

   Isabelle's nat coercion truncates negative integers, so [20], [21],
   [53], and [54] use Num (int_max i 0), rather than HOL4's
   absolute-value Num coercion.  The two upstream "oops" goals, [47] and
   [48], are among the shared ones and are described there.

   On 2026-08-02 the full instances selftest took 10.0s at level 2 versus
   7.7s at level 1 on an AMD Ryzen 9 9950X, down from 50.2s at level 2
   before the tactics began splitting on demand.  The 120s suite budget,
   30s goal budget, and 5s boundary budget deliberately leave ample
   headroom.

   linarithCorpus owns the driver, the budgets and the canonical goal
   numbering; the numbering check below pins the merged list to all of
   it. *)

val carrier_arith_examples : strength_goal list =
  [(2, StrengthSuccess, “(i:int) <= int_max i j”),
   (4, StrengthSuccess, “int_min i j <= (i:int)”),
   (6, StrengthSuccess,
    “int_min (i:int) j <= int_max i j”),
   (8, StrengthSuccess,
    “int_min (i:int) j + int_max i j = i + j”),
   (10, StrengthSuccess,
    “(i:int) < j ==> int_min i j < int_max i j”),
   (11, StrengthSuccess, “(0:int) <= ABS i”),
   (12, StrengthSuccess, “(i:int) <= ABS i”),
   (13, StrengthSuccess, “ABS (ABS (i:int)) = ABS i”),
   (19, StrengthSuccess, “(x:int) < y ==> x - y < 0”),
   (20, StrengthSuccess,
    “Num (int_max ((i:int) + j) 0) <=
     Num (int_max i 0) + Num (int_max j 0)”),
   (21, StrengthSuccess,
    “(i:int) < j ==> Num (int_max (i - j) 0) = 0”),
   (* HOL4 int_mod is unspecified at zero.  Isabelle's total zmod
      source goal therefore translates to its specified result. *)
   (25, StrengthSuccess, “(i:int) = i”),
   (26, StrengthSuccess, “(i:int) % 1 = 0”),
   (27, StrengthSuccess, “(i:int) % 42 <= 41”),
   (28, StrengthSuccess, “-(i:int) * 1 = 0 ==> i = 0”),
   (29, StrengthSuccess,
    “(0:int) < ABS i /\ ABS i * 1 < ABS i * j ==>
     1 < ABS i * j”),
   (50, StrengthSuccess, “(0:int) < 1”),
   (52, StrengthSuccess, “(47:int) + 11 < 8 * 15”),
   (53, StrengthSuccess,
    “(a:num) <> b /\ (i:int) <> j /\ a < 2 /\ b < 2 ==>
     a + b <= Num (int_max (ABS i) (ABS j))”),
   (54, StrengthSuccess,
    “(i:int) <> j /\ (a:num) <> b /\ a < 2 /\ b < 2 ==>
     a + b <= Num (int_max (ABS i) (ABS j))”)]

val arith_examples_corpus : strength_goal list =
  merge_by_number (core_arith_examples, carrier_arith_examples)

val _ =
  check_numbering
    {suite = "Arith_Examples", numbering = full_numbering}
    arith_examples_corpus

val _ =
  if selftest_level () >= 2 then
    run_suite
      {suite = "Arith_Examples",
       tactic = fn () => linarithLib.LINARITH_TAC [],
       suite_budget = Time.fromSeconds 120,
       expected_successes = 53,
       expected_boundaries = 1}
      arith_examples_corpus
  else ()

(* A second spelling of the integer operators exercises the registered
   theorem kit through the public solver.  These laws are derived from
   the integer kit, so replay must use the supplied operator views rather
   than identify the built-in constant names in generic code. *)
val _ = Theory.new_theory "linarithRenamedSelftest"

val renamed_plus_def =
  new_definition
    ("renamed_plus_def",
     ``renamed_plus (a:int) b = a + b``)
val renamed_le_def =
  new_definition
    ("renamed_le_def",
     ``renamed_le (a:int) b <=> a <= b``)
val renamed_lt_def =
  new_definition
    ("renamed_lt_def",
     ``renamed_lt (a:int) b <=> a < b``)

val renamed_defs =
  [renamed_plus_def, renamed_le_def, renamed_lt_def]

val renamed_plus =
  prim_mk_const {Thy = "linarithRenamedSelftest", Name = "renamed_plus"}
val renamed_le =
  prim_mk_const {Thy = "linarithRenamedSelftest", Name = "renamed_le"}
val renamed_lt =
  prim_mk_const {Thy = "linarithRenamedSelftest", Name = "renamed_lt"}

fun renamed_binary operator tm =
  case strip_comb tm of
      (head, [left, right]) =>
        if Term.aconv head operator then (left, right)
        else raise mk_HOL_ERR "linarithRenamedSelftest"
                     "renamed_binary" "different operator"
    | _ => raise mk_HOL_ERR "linarithRenamedSelftest"
                 "renamed_binary" "not a binary application"

fun renamed_app operator left right =
  Term.list_mk_comb (operator, [left, right])

val old_dest = #dest int_instance
val old_kit = #kit int_instance
val fold_renamed =
  Rewrite.REWRITE_RULE (map Conv.GSYM renamed_defs)
val unfold_renamed =
  Conv.TOP_DEPTH_CONV
    (Conv.FIRST_CONV (map Conv.REWR_CONV renamed_defs))
val fold_renamed_conv =
  Conv.TOP_DEPTH_CONV
    (Conv.FIRST_CONV
       (map (Conv.REWR_CONV o Conv.GSYM) renamed_defs))

val renamed_instance : linarithData.linarith_instance =
  {ty = intSyntax.int_ty,
   discrete =
     Option.map
       (fn {lessD} => {lessD = map fold_renamed lessD})
       (#discrete int_instance),
   dest =
     {dest_plus = renamed_binary renamed_plus,
      dest_minus = #dest_minus old_dest,
      dest_neg = #dest_neg old_dest,
      dest_mult = #dest_mult old_dest,
      dest_div = #dest_div old_dest,
      dest_suc = #dest_suc old_dest,
      dest_lit = #dest_lit old_dest,
      mk_lit = #mk_lit old_dest,
      dest_less = renamed_binary renamed_lt,
      dest_leq = renamed_binary renamed_le},
   kit =
     {add_mono = map fold_renamed (#add_mono old_kit),
      mult_mono = map fold_renamed (#mult_mono old_kit),
      not_less = fold_renamed (#not_less old_kit),
      not_le = fold_renamed (#not_le old_kit),
      neqE = fold_renamed (#neqE old_kit),
      nonneg = #nonneg old_kit},
   norm_conv =
     Conv.THENC
       (Conv.THENC
          (unfold_renamed, Conv.QCONV (#norm_conv int_instance)),
        Conv.QCONV fold_renamed_conv),
   nnf_rules = map fold_renamed (#nnf_rules int_instance),
   pre_split = map fold_renamed (#pre_split int_instance),
   atom_facts = #atom_facts int_instance}

val renamed_goal =
  ([renamed_app renamed_le ix iy,
    renamed_app renamed_le iz i7],
   renamed_app renamed_le
     (renamed_app renamed_plus ix iz)
     (renamed_app renamed_plus iy i7))

val _ =
  check
    ("renamed arithmetic declarations replay through a theorem kit",
     fn () =>
       let
         val ordinary_declines =
           not (valid_closes (linarithLib.LINARITH_TAC [])
                  renamed_goal
                handle Feedback.HOL_ERR _ => false)
         val _ = linarithData.register_instance renamed_instance
         val result =
           valid_closes (linarithLib.LINARITH_TAC []) renamed_goal
           handle error =>
             (linarithData.register_instance int_instance; raise error)
         val _ = linarithData.register_instance int_instance
       in
         ordinary_declines andalso result
       end)

(* This carrier is a fresh datatype, not another spelling of int.  Its
   arithmetic laws are proved by reducing the wrapper to integer laws;
   the generic solver only sees the registered, wrapped theorems. *)
val _ = Datatype.Datatype `client_integer = ClientInteger int`

val client_plus_def = bossLib.Define
  `client_plus (ClientInteger a) (ClientInteger b) =
     ClientInteger (a + b)`
val client_le_def = bossLib.Define
  `client_le (ClientInteger a) (ClientInteger b) <=> a <= b`
val client_lt_def = bossLib.Define
  `client_lt (ClientInteger a) (ClientInteger b) <=> a < b`

val client_defs = [client_plus_def, client_le_def, client_lt_def]

fun client_law statement variables int_laws =
  Tactical.prove
    (statement,
     Tactical.THEN
       (Tactical.rpt Tactic.GEN_TAC,
        Tactical.THEN
          (List.foldr
             (fn (name, tac) =>
               Tactical.THEN (bossLib.Cases_on name, tac))
             Tactical.ALL_TAC variables,
           Tactical.THEN
             (simpLib.SIMP_TAC boolSimps.bool_ss
                (DB.fetch "linarithRenamedSelftest" "client_integer_11" ::
                 client_defs),
              metisLib.METIS_TAC int_laws))))

val client_add_mono =
  client_law
    ``!a b c d : client_integer.
        client_le a b /\ client_le c d ==>
        client_le (client_plus a c) (client_plus b d)``
    [`a`, `b`, `c`, `d`] [integerTheory.INT_LE_ADD2]
val client_lt_add_mono =
  client_law
    ``!a b c d : client_integer.
        client_lt a b /\ client_lt c d ==>
        client_lt (client_plus a c) (client_plus b d)``
    [`a`, `b`, `c`, `d`] [integerTheory.INT_LT_ADD2]
val client_let_add_mono =
  client_law
    ``!a b c d : client_integer.
        client_le a b /\ client_lt c d ==>
        client_lt (client_plus a c) (client_plus b d)``
    [`a`, `b`, `c`, `d`] [integerTheory.INT_LET_ADD2]
val client_lte_add_mono =
  client_law
    ``!a b c d : client_integer.
        client_lt a b /\ client_le c d ==>
        client_lt (client_plus a c) (client_plus b d)``
    [`a`, `b`, `c`, `d`] [integerTheory.INT_LTE_ADD2]

val client_not_less =
  client_law
    ``!a b : client_integer.
        ~client_lt a b <=> client_le b a``
    [`a`, `b`] [integerTheory.INT_NOT_LT]
val client_not_le =
  client_law
    ``!a b : client_integer.
        ~client_le a b <=> client_lt b a``
    [`a`, `b`] [integerTheory.INT_NOT_LE]
val client_neq =
  client_law
    ``!a b : client_integer.
        a <> b ==>
        (client_lt a b ==> F) ==>
        (client_lt b a ==> F) ==> F``
    [`a`, `b`] [linarithInstTheory.INT_NEQ_E]

val client_assoc =
  client_law
    ``!a b c : client_integer.
        client_plus (client_plus a b) c =
        client_plus a (client_plus b c)``
    [`a`, `b`, `c`] [integerTheory.INT_ADD_ASSOC]
val client_comm =
  client_law
    ``!a b : client_integer.
        client_plus a b = client_plus b a``
    [`a`, `b`] [integerTheory.INT_ADD_COMM]
val client_rid =
  client_law
    ``!a : client_integer.
        client_plus a (ClientInteger 0) = a``
    [`a`] [integerTheory.INT_ADD_RID]
val client_le_cancel =
  client_law
    ``!a b c : client_integer.
        client_le (client_plus a b) (client_plus a c) <=>
        client_le b c``
    [`a`, `b`, `c`] [integerTheory.INT_LE_LADD]
val client_lt_cancel =
  client_law
    ``!a b c : client_integer.
        client_lt (client_plus a b) (client_plus a c) <=>
        client_lt b c``
    [`a`, `b`, `c`] [integerTheory.INT_LT_LADD]
val client_eq_cancel =
  client_law
    ``!a b c : client_integer.
        (client_plus a b = client_plus a c) <=> (b = c)``
    [`a`, `b`, `c`] [integerTheory.INT_EQ_LADD]
val client_lt_refl =
  client_law ``!a : client_integer. ~client_lt a a`` [`a`]
    [integerTheory.INT_LT_REFL]
val client_le_refl =
  client_law ``!a : client_integer. client_le a a`` [`a`]
    [integerTheory.INT_LE_REFL]

val client_plus =
  prim_mk_const {Thy = "linarithRenamedSelftest", Name = "client_plus"}
val client_le =
  prim_mk_const {Thy = "linarithRenamedSelftest", Name = "client_le"}
val client_lt =
  prim_mk_const {Thy = "linarithRenamedSelftest", Name = "client_lt"}
val client_ctor =
  prim_mk_const {Thy = "linarithRenamedSelftest", Name = "ClientInteger"}
val client_ty = Term.type_of (Term.mk_comb (client_ctor, i0))

fun client_strip tm =
  case Lib.total (renamed_binary client_plus) tm of
      SOME (left, right) => client_strip left @ client_strip right
    | NONE => [tm]

fun client_dest_lit tm =
  let
    val (ctor, value) = Term.dest_comb tm
  in
    if Term.aconv ctor client_ctor then
      Arbrat.fromAInt (intSyntax.int_of_term value)
    else raise mk_HOL_ERR "linarithRenamedSelftest"
                 "client_dest_lit" "not a client literal"
  end

fun client_mk_lit value =
  Term.mk_comb (client_ctor,
    intSyntax.term_of_int (Arbrat.toAInt value))

fun client_ac_canon tm =
  let
    val summands = Listsort.sort Term.compare (client_strip tm)
    val normal =
      list_mk_lbinop (renamed_app client_plus) summands
  in
    if Term.aconv tm normal then Thm.REFL tm
    else
      Tactical.prove
        (boolSyntax.mk_eq (tm, normal),
         metisLib.METIS_TAC [client_assoc, client_comm])
  end

val client_instance : linarithData.linarith_instance =
  {ty = client_ty,
   discrete = NONE,
   dest =
     {dest_plus = renamed_binary client_plus,
      dest_minus = NONE,
      dest_neg = NONE,
      dest_mult = fn _ =>
        raise mk_HOL_ERR "linarithRenamedSelftest"
          "dest_mult" "no multiplication on client_integer",
      dest_div = NONE,
      dest_suc = NONE,
      dest_lit = client_dest_lit,
      mk_lit = client_mk_lit,
      dest_less = renamed_binary client_lt,
      dest_leq = renamed_binary client_le},
   kit =
     {add_mono =
        [client_add_mono, client_lt_add_mono,
         client_let_add_mono, client_lte_add_mono],
      mult_mono = [],
      not_less = client_not_less,
      not_le = client_not_le,
      neqE = client_neq,
      nonneg = fn _ => NONE},
   norm_conv =
     linarithCancel.mk_norm_conv
       {ac =
          {dest_less = renamed_binary client_lt,
           dest_leq = renamed_binary client_le,
           strip_plus = client_strip,
           mk_plus = fn (left, right) =>
             renamed_app client_plus left right,
           assoc = client_assoc,
           comm = client_comm,
           rid = client_rid,
           ac_fallback = SOME client_ac_canon},
        ty = client_ty,
        leq_cancel = client_le_cancel,
        less_cancel = client_lt_cancel,
        eq_cancel = client_eq_cancel,
        expression_conv = fn _ => raise Conv.UNCHANGED,
        reduce_conv = Conv.NO_CONV,
        refl_thms = [client_lt_refl, client_le_refl]},
   nnf_rules = [],
   pre_split = [],
   atom_facts = fn _ => []}

val client_x = Term.mk_var ("client_x", client_ty)
val client_y = Term.mk_var ("client_y", client_ty)
val client_z = Term.mk_var ("client_z", client_ty)
val client_w = Term.mk_var ("client_w", client_ty)

val client_goal =
  ([renamed_app client_le client_x client_y,
    renamed_app client_le client_z client_w],
   renamed_app client_le
     (renamed_app client_plus client_x client_z)
     (renamed_app client_plus client_y client_w))

val _ =
  check
    ("a new arithmetic carrier uses its registered theorem kit",
     fn () =>
       let
         val ordinary_declines =
           not (valid_closes (linarithLib.LINARITH_TAC []) client_goal
                handle Feedback.HOL_ERR _ => false)
         val _ = linarithData.register_instance client_instance
       in
         ordinary_declines andalso
         valid_closes (linarithLib.LINARITH_TAC []) client_goal
       end)
