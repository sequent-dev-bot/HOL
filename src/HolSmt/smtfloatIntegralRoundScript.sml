open HolKernel Parse boolLib bossLib;
open smtfloatTheory;

(* Kernel certificates used by the ground evaluator for the four IEEE-754
   integral rounding modes.  Keeping these after smtfloatTheory avoids
   coupling the SMT-facing definitions to certificate implementation. *)
val _ = new_theory "smtfloatIntegralRound";

Theorem RTZ_positive_closest[local]:
  0 < float_to_real (y : ('t,'w) float) /\
  float_to_real y <= x /\ x < float_to_real y + 1 /\
  float_is_integral y ==>
  is_closest
    {a | float_is_integral a /\ abs (float_to_real a) <= abs x} x y
Proof
  strip_tac >> fs [] >>
  simp [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  conj_tac >- realLib.REAL_ASM_ARITH_TAC >>
  rpt strip_tac >>
  `0 < x` by realLib.REAL_ASM_ARITH_TAC >>
  `binary_ieee$is_integral (float_to_real y) /\
   binary_ieee$is_integral (float_to_real b)` by
    metis_tac [float_is_integral_to_real] >>
  `float_to_real b <= float_to_real y` by
    (CCONTR_TAC >> fs [] >>
     `1 <= abs (float_to_real b - float_to_real y)` by
       (irule is_integral_separated >> simp [] >>
        realLib.REAL_ASM_ARITH_TAC) >>
     realLib.REAL_ASM_ARITH_TAC) >>
  realLib.REAL_ASM_ARITH_TAC
QED

Theorem RTZ_positive_unique[local]:
  0 < float_to_real (y : ('t,'w) float) /\
  float_to_real y <= x /\ x < float_to_real y + 1 /\
  float_is_integral y /\
  is_closest
    {a | float_is_integral a /\ abs (float_to_real a) <= abs x} x z ==>
  z = y
Proof
  strip_tac >>
  fs [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  `0 < x` by realLib.REAL_ASM_ARITH_TAC >>
  `binary_ieee$is_integral (float_to_real z) /\
   binary_ieee$is_integral (float_to_real y)` by
    metis_tac [float_is_integral_to_real] >>
  `float_to_real z <= float_to_real y` by
    (CCONTR_TAC >> fs [] >>
     `1 <= abs (float_to_real z - float_to_real y)` by
       (irule is_integral_separated >> simp [] >>
     realLib.REAL_ASM_ARITH_TAC) >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `abs (float_to_real z - x) <= abs (float_to_real y - x)` by
    (qpat_x_assum
       `!b. float_is_integral b /\ abs (float_to_real b) <= abs x ==>
          abs (float_to_real z - x) <= abs (float_to_real b - x)`
       (qspec_then `y` mp_tac) >>
     simp [] >> realLib.REAL_ASM_ARITH_TAC) >>
  `float_to_real z = float_to_real y` by
    (CCONTR_TAC >>
     `1 <= abs (float_to_real z - float_to_real y)` by
       (irule is_integral_separated >> simp []) >>
     realLib.REAL_ASM_ARITH_TAC) >>
  mp_tac (Q.SPECL [`z`, `y`] binary_ieeeTheory.float_to_real_eq) >>
  simp [binary_ieeeTheory.float_is_zero_to_real] >>
  realLib.REAL_ASM_ARITH_TAC
QED

Theorem integral_round_RTZ_positive:
  0 < float_to_real (y : ('t,'w) float) /\
  float_to_real y <= x /\ x < float_to_real y + 1 /\
  x <= largest (:'t # 'w) /\ float_is_integral y ==>
  integral_round roundTowardZero x = y
Proof
  strip_tac >> fs [] >>
  `0 < x` by realLib.REAL_ASM_ARITH_TAC >>
  `~(x < -largest (:'t # 'w)) /\
   ~(x > largest (:'t # 'w))` by
    (conj_tac >- (simp [] >> realLib.REAL_ASM_ARITH_TAC) >>
     realLib.REAL_ASM_ARITH_TAC) >>
  simp [binary_ieeeTheory.integral_round_def,
        binary_ieeeTheory.closest_def,
        binary_ieeeTheory.closest_such_def] >>
  SELECT_ELIM_TAC >>
  conj_tac
  >- (qexists_tac `y` >>
      irule RTZ_positive_closest >> simp [])
  >- metis_tac [RTZ_positive_unique]
QED

Theorem RTZ_negative_closest[local]:
  float_to_real (y : ('t,'w) float) < 0 /\
  float_to_real y - 1 < x /\ x <= float_to_real y /\
  float_is_integral y ==>
  is_closest
    {a | float_is_integral a /\ abs (float_to_real a) <= abs x} x y
Proof
  strip_tac >> fs [] >>
  simp [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  conj_tac >- realLib.REAL_ASM_ARITH_TAC >>
  rpt strip_tac >>
  `x < 0` by realLib.REAL_ASM_ARITH_TAC >>
  `binary_ieee$is_integral (float_to_real y) /\
   binary_ieee$is_integral (float_to_real b)` by
    metis_tac [float_is_integral_to_real] >>
  `float_to_real y <= float_to_real b` by
    (CCONTR_TAC >> fs [] >>
     `1 <= abs (float_to_real y - float_to_real b)` by
       (irule is_integral_separated >> simp [] >>
        realLib.REAL_ASM_ARITH_TAC) >>
     realLib.REAL_ASM_ARITH_TAC) >>
  realLib.REAL_ASM_ARITH_TAC
QED

Theorem RTZ_negative_unique[local]:
  float_to_real (y : ('t,'w) float) < 0 /\
  float_to_real y - 1 < x /\ x <= float_to_real y /\
  float_is_integral y /\
  is_closest
    {a | float_is_integral a /\ abs (float_to_real a) <= abs x} x z ==>
  z = y
Proof
  strip_tac >>
  fs [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  `x < 0` by realLib.REAL_ASM_ARITH_TAC >>
  `binary_ieee$is_integral (float_to_real z) /\
   binary_ieee$is_integral (float_to_real y)` by
    metis_tac [float_is_integral_to_real] >>
  `float_to_real y <= float_to_real z` by
    (CCONTR_TAC >> fs [] >>
     `1 <= abs (float_to_real y - float_to_real z)` by
       (irule is_integral_separated >> simp [] >>
        realLib.REAL_ASM_ARITH_TAC) >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `abs (float_to_real z - x) <= abs (float_to_real y - x)` by
    (qpat_x_assum
       `!b. float_is_integral b /\ abs (float_to_real b) <= abs x ==>
          abs (float_to_real z - x) <= abs (float_to_real b - x)`
       (qspec_then `y` mp_tac) >>
     simp [] >> realLib.REAL_ASM_ARITH_TAC) >>
  `float_to_real z = float_to_real y` by
    (CCONTR_TAC >>
     `1 <= abs (float_to_real z - float_to_real y)` by
       (irule is_integral_separated >> simp []) >>
     realLib.REAL_ASM_ARITH_TAC) >>
  mp_tac (Q.SPECL [`z`, `y`] binary_ieeeTheory.float_to_real_eq) >>
  simp [binary_ieeeTheory.float_is_zero_to_real] >>
  realLib.REAL_ASM_ARITH_TAC
QED

Theorem integral_round_RTZ_negative:
  float_to_real (y : ('t,'w) float) < 0 /\
  float_to_real y - 1 < x /\ x <= float_to_real y /\
  -largest (:'t # 'w) <= x /\ float_is_integral y ==>
  integral_round roundTowardZero x = y
Proof
  strip_tac >> fs [] >>
  `x < 0` by realLib.REAL_ASM_ARITH_TAC >>
  `~(x < -largest (:'t # 'w)) /\
   ~(x > largest (:'t # 'w))` by
    (conj_tac >- realLib.REAL_ASM_ARITH_TAC >>
     simp [] >> realLib.REAL_ASM_ARITH_TAC) >>
  simp [binary_ieeeTheory.integral_round_def,
        binary_ieeeTheory.closest_def,
        binary_ieeeTheory.closest_such_def] >>
  SELECT_ELIM_TAC >> conj_tac
  >- (qexists_tac `y` >>
      irule RTZ_negative_closest >> simp [])
  >- metis_tac [RTZ_negative_unique]
QED

Theorem integral_round_RNE_underflow:
  x <= -threshold (:'t # 'w) ==>
  integral_round roundTiesToEven x =
    float_minus_infinity (:'t # 'w)
Proof
  fs [binary_ieeeTheory.integral_round_def, realTheory.real_ge, realTheory.real_gt]
QED

Theorem integral_round_RNE_overflow:
  threshold (:'t # 'w) <= x ==>
  integral_round roundTiesToEven x =
    float_plus_infinity (:'t # 'w)
Proof
  strip_tac >>
  `0 < threshold (:'t # 'w)` by simp [] >>
  `~(x <= -threshold (:'t # 'w))` by
    realLib.REAL_ASM_ARITH_TAC >>
  fs [binary_ieeeTheory.integral_round_def, realTheory.real_ge, realTheory.real_gt]
QED

Theorem integral_round_RTZ_underflow:
  x < -largest (:'t # 'w) ==>
  integral_round roundTowardZero x = float_bottom (:'t # 'w)
Proof
  fs [binary_ieeeTheory.integral_round_def, realTheory.real_ge, realTheory.real_gt]
QED

Theorem integral_round_RTZ_overflow:
  largest (:'t # 'w) < x ==>
  integral_round roundTowardZero x = float_top (:'t # 'w)
Proof
  strip_tac >>
  `0 <= largest (:'t # 'w)` by simp [] >>
  `~(x < -largest (:'t # 'w))` by
    realLib.REAL_ASM_ARITH_TAC >>
  fs [binary_ieeeTheory.integral_round_def, realTheory.real_ge, realTheory.real_gt]
QED

Theorem integral_round_RTP_underflow:
  x < -largest (:'t # 'w) ==>
  integral_round roundTowardPositive x = float_bottom (:'t # 'w)
Proof
  simp [binary_ieeeTheory.integral_round_def, realTheory.real_ge, realTheory.real_gt]
QED

Theorem integral_round_RTP_overflow:
  largest (:'t # 'w) < x ==>
  integral_round roundTowardPositive x =
    float_plus_infinity (:'t # 'w)
Proof
  strip_tac >>
  `0 <= largest (:'t # 'w)` by simp [] >>
  `~(x < -largest (:'t # 'w))` by
    realLib.REAL_ASM_ARITH_TAC >>
  fs [binary_ieeeTheory.integral_round_def, realTheory.real_ge, realTheory.real_gt]
QED

Theorem integral_round_RTN_underflow:
  x < -largest (:'t # 'w) ==>
  integral_round roundTowardNegative x =
    float_minus_infinity (:'t # 'w)
Proof
  simp [binary_ieeeTheory.integral_round_def, realTheory.real_ge, realTheory.real_gt]
QED

Theorem integral_round_RTN_overflow:
  largest (:'t # 'w) < x ==>
  integral_round roundTowardNegative x = float_top (:'t # 'w)
Proof
  strip_tac >>
  `0 <= largest (:'t # 'w)` by simp [] >>
  `~(x < -largest (:'t # 'w))` by
    realLib.REAL_ASM_ARITH_TAC >>
  fs [binary_ieeeTheory.integral_round_def, realTheory.real_ge, realTheory.real_gt]
QED

(* A real integral value strictly between -1 and 1 is zero.  The
   float-facing operation needs precisely this zero-class fact: choosing a
   particular raw +0/-0 record here would lose the input sign that SMT-LIB
   requires the outer operation to restore. *)
Theorem integral_float_abs_lt_one_is_zero[local]:
  float_is_integral (y : ('t,'w) float) /\
  abs (float_to_real y) < 1 ==>
  float_is_zero y
Proof
  strip_tac >>
  rewrite_tac [binary_ieeeTheory.float_is_zero_to_real] >>
  `binary_ieee$is_integral (float_to_real y)` by
    metis_tac [float_is_integral_to_real] >>
  fs [is_integral_real_of_int] >>
  Cases_on `i` >> fs [realTheory.abs]
QED

Theorem integral_zero_is_closest_at_half[local]:
  abs x <= 1 / 2 ==>
  is_closest float_is_integral x
    (float_plus_zero (:'t # 'w))
Proof
  rw [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  `binary_ieee$is_integral (float_to_real b)` by
    metis_tac [float_is_integral_to_real] >>
  fs [binary_ieeeTheory.is_integral_def] >>
  Cases_on `n`
  >- fs []
  >- (`1 <= abs (float_to_real b)` by fs [] >>
      `abs (float_to_real b) <=
       abs (float_to_real b - x) + abs x` by
        (mp_tac (Q.SPECL [`float_to_real b - x`, `x`]
           realTheory.ABS_TRIANGLE) >>
         realLib.REAL_ASM_ARITH_TAC) >>
      realLib.REAL_ASM_ARITH_TAC)
QED

Theorem even_float_abs_le_one_is_zero[local]:
  (?n. EVEN n /\ abs (float_to_real y) = &n) /\
  abs (float_to_real y) <= 1 ==>
  float_is_zero (y : ('t,'w) float)
Proof
  rw [arithmeticTheory.EVEN_EXISTS] >>
  Cases_on `m`
  >- fs [binary_ieeeTheory.float_is_zero_to_real]
  >- (`2 <= (&(2 * SUC n) : real)` by simp [] >>
      realLib.REAL_ASM_ARITH_TAC)
QED

Theorem closest_such_prefers_even_integral[local]:
  (float_is_integral : ('t,'w) float -> bool) <> {} /\
  is_closest (float_is_integral : ('t,'w) float -> bool) x
    (float_plus_zero (:'t # 'w)) ==>
  ?n. EVEN n /\
      abs (float_to_real
        (closest_such
          (\a : ('t,'w) float.
            ?n. EVEN n /\ abs (float_to_real a) = &n)
          (float_is_integral : ('t,'w) float -> bool) x)) = &n
Proof
  strip_tac >>
  simp [binary_ieeeTheory.closest_such_def] >>
  SELECT_ELIM_TAC >> conj_tac
  >- (qexists_tac `float_plus_zero (:'t # 'w)` >> simp [])
  >- (rpt strip_tac >>
      first_x_assum
        (qspec_then `float_plus_zero (:'t # 'w)` mp_tac) >>
      simp [])
QED

Theorem integral_round_RNE_zero_class:
  -threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w) /\
  abs x <= 1 / 2 ==>
  float_is_zero
    (integral_round roundTiesToEven x : ('t,'w) float)
Proof
  strip_tac >>
  `~(x <= -threshold (:'t # 'w)) /\
   ~(x >= threshold (:'t # 'w))` by realLib.REAL_ASM_ARITH_TAC >>
  simp [binary_ieeeTheory.integral_round_def] >>
  qabbrev_tac `y : ('t,'w) float =
    closest_such (\a. ?n. EVEN n /\ abs (float_to_real a) = &n)
      float_is_integral x` >>
  `(float_is_integral : ('t,'w) float -> bool) <> {}` by
    (simp [pred_setTheory.EXTENSION, IN_DEF] >>
     qexists_tac `float_plus_zero (:'t # 'w)` >> simp []) >>
  `is_closest float_is_integral x y` by
    (simp [Abbr `y`] >>
     irule (cj 1 closest_such_properties) >> simp []) >>
  `is_closest float_is_integral x
     (float_plus_zero (:'t # 'w))` by
    metis_tac [integral_zero_is_closest_at_half] >>
  irule even_float_abs_le_one_is_zero >>
  conj_tac
  >- (rw [Abbr `y`] >>
      irule closest_such_prefers_even_integral >> simp [])
  >- (`abs (float_to_real y - x) <= abs x` by
        (qpat_x_assum `is_closest float_is_integral x y`
           (mp_tac o Q.SPEC `float_plus_zero (:'t # 'w)` o cj 2 o
            REWRITE_RULE [binary_ieeeTheory.is_closest_def, IN_DEF]) >>
         simp []) >>
      `abs (float_to_real y) <=
       abs (float_to_real y - x) + abs x` by
        (mp_tac (Q.SPECL [`float_to_real y - x`, `x`]
         realTheory.ABS_TRIANGLE) >> realLib.REAL_ASM_ARITH_TAC) >>
      realLib.REAL_ASM_ARITH_TAC)
QED

Theorem integral_round_RTZ_zero_class:
  -largest (:'t # 'w) <= x /\ x <= largest (:'t # 'w) /\
  abs x < 1 ==>
  float_is_zero
    (integral_round roundTowardZero x : ('t,'w) float)
Proof
  strip_tac >>
  `~(x < -largest (:'t # 'w)) /\
   ~(x > largest (:'t # 'w))` by realLib.REAL_ASM_ARITH_TAC >>
  simp [binary_ieeeTheory.integral_round_def,
        binary_ieeeTheory.closest_def] >>
  qabbrev_tac `s = {a : ('t,'w) float |
    float_is_integral a /\ abs (float_to_real a) <= abs x}` >>
  qabbrev_tac `y : ('t,'w) float = closest_such (K T) s x` >>
  `float_plus_zero (:'t # 'w) IN s` by
    (simp [Abbr `s`, IN_DEF] >> realLib.REAL_ASM_ARITH_TAC) >>
  `s <> {}` by metis_tac [pred_setTheory.MEMBER_NOT_EMPTY] >>
  `is_closest s x y` by
    (simp [Abbr `y`] >>
     irule (cj 1 closest_such_properties) >> simp []) >>
  `float_is_integral y /\ abs (float_to_real y) <= abs x` by
    fs [binary_ieeeTheory.is_closest_def, Abbr `s`, IN_DEF] >>
  irule integral_float_abs_lt_one_is_zero >>
  simp [] >> realLib.REAL_ASM_ARITH_TAC
QED

Theorem integral_round_RTP_zero_class:
  -largest (:'t # 'w) <= x /\ x <= largest (:'t # 'w) /\
  -1 < x /\ x <= 0 ==>
  float_is_zero
    (integral_round roundTowardPositive x : ('t,'w) float)
Proof
  strip_tac >>
  `~(x < -largest (:'t # 'w)) /\
   ~(x > largest (:'t # 'w))` by realLib.REAL_ASM_ARITH_TAC >>
  simp [binary_ieeeTheory.integral_round_def,
        binary_ieeeTheory.closest_def] >>
  qabbrev_tac `s = {a : ('t,'w) float |
    float_is_integral a /\ float_to_real a >= x}` >>
  qabbrev_tac `y : ('t,'w) float = closest_such (K T) s x` >>
  `float_plus_zero (:'t # 'w) IN s` by
    (simp [Abbr `s`, IN_DEF] >> realLib.REAL_ASM_ARITH_TAC) >>
  `s <> {}` by metis_tac [pred_setTheory.MEMBER_NOT_EMPTY] >>
  `is_closest s x y` by
    (simp [Abbr `y`] >>
     irule (cj 1 closest_such_properties) >> simp []) >>
  `float_is_integral y /\ float_to_real y >= x` by
    fs [binary_ieeeTheory.is_closest_def, Abbr `s`, IN_DEF] >>
  `abs (float_to_real y - x) <= -x` by
    (qpat_x_assum `is_closest s x y`
       (mp_tac o Q.SPEC `float_plus_zero (:'t # 'w)` o cj 2 o
        REWRITE_RULE [binary_ieeeTheory.is_closest_def, IN_DEF]) >>
     simp [Abbr `s`, IN_DEF] >> realLib.REAL_ASM_ARITH_TAC) >>
  `abs (float_to_real y) < 1` by
    (Cases_on `0 <= float_to_real y` >>
     fs [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
  metis_tac [integral_float_abs_lt_one_is_zero]
QED

Theorem integral_round_RTN_zero_class:
  -largest (:'t # 'w) <= x /\ x <= largest (:'t # 'w) /\
  0 <= x /\ x < 1 ==>
  float_is_zero
    (integral_round roundTowardNegative x : ('t,'w) float)
Proof
  strip_tac >>
  `~(x < -largest (:'t # 'w)) /\
   ~(x > largest (:'t # 'w))` by realLib.REAL_ASM_ARITH_TAC >>
  simp [binary_ieeeTheory.integral_round_def,
        binary_ieeeTheory.closest_def] >>
  qabbrev_tac `s = {a : ('t,'w) float |
    float_is_integral a /\ float_to_real a <= x}` >>
  qabbrev_tac `y : ('t,'w) float = closest_such (K T) s x` >>
  `float_plus_zero (:'t # 'w) IN s` by
    (simp [Abbr `s`, IN_DEF] >> realLib.REAL_ASM_ARITH_TAC) >>
  `s <> {}` by metis_tac [pred_setTheory.MEMBER_NOT_EMPTY] >>
  `is_closest s x y` by
    (simp [Abbr `y`] >>
     irule (cj 1 closest_such_properties) >> simp []) >>
  `float_is_integral y /\ float_to_real y <= x` by
    fs [binary_ieeeTheory.is_closest_def, Abbr `s`, IN_DEF] >>
  `abs (float_to_real y - x) <= x` by
    (qpat_x_assum `is_closest s x y`
       (mp_tac o Q.SPEC `float_plus_zero (:'t # 'w)` o cj 2 o
        REWRITE_RULE [binary_ieeeTheory.is_closest_def, IN_DEF]) >>
     simp [Abbr `s`, IN_DEF] >> realLib.REAL_ASM_ARITH_TAC) >>
  `abs (float_to_real y) < 1` by
    (Cases_on `0 <= float_to_real y` >>
     fs [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
  metis_tac [integral_float_abs_lt_one_is_zero]
QED

(* realLib.REAL_ASM_ARITH_TAC feeds the whole assumption list to the
   arithmetic procedure, which case-splits on every abs and if in it and
   gets exponential in the goals below.  Pass it only the assumptions
   matching the given patterns. *)
fun real_arith_from pats =
  MAP_EVERY (fn p => qpat_x_assum p mp_tac) pats >> realLib.REAL_ARITH_TAC

Theorem integral_round_RNA_zero_class:
  -threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w) /\
  abs x < 1 / 2 /\
  abs x <
    abs (float_to_real (float_plus_infinity (:'t # 'w)) - x) /\
  abs x <
    abs (float_to_real (float_minus_infinity (:'t # 'w)) - x) ==>
  float_is_zero
    (integral_round_tiesToAway x : ('t,'w) float)
Proof
  strip_tac >>
  `is_closest integral_round_candidate x
     (integral_round_tiesToAway x : ('t,'w) float)` by
    metis_tac [integral_round_tiesToAway_is_closest] >>
  qabbrev_tac `y : ('t,'w) float = integral_round_tiesToAway x` >>
  `abs (float_to_real y - x) <= abs x` by
    (qpat_x_assum `is_closest integral_round_candidate x y`
       (mp_tac o Q.SPEC `float_plus_zero (:'t # 'w)` o cj 2 o
        REWRITE_RULE [binary_ieeeTheory.is_closest_def, IN_DEF]) >>
     simp [integral_round_candidate_def]) >>
  `integral_round_candidate y` by
    fs [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  `~float_is_infinite y` by
    (strip_tac >>
     fs [GSYM IN_DEF, binary_ieeeTheory.float_sets] >>
     qpat_x_assum `y = _` SUBST_ALL_TAC >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `float_is_integral y` by fs [integral_round_candidate_def] >>
  `abs (float_to_real y) <=
   abs (float_to_real y - x) + abs x` by
    (mp_tac (Q.SPECL [`float_to_real y - x`, `x`]
       realTheory.ABS_TRIANGLE) >> realLib.REAL_ASM_ARITH_TAC) >>
  irule integral_float_abs_lt_one_is_zero >>
  simp [] >>
  real_arith_from
    [`abs (float_to_real y) <= abs (float_to_real y - x) + abs x`,
     `abs (float_to_real y - x) <= abs x`, `abs x < 1 / 2`]
QED

Theorem integral_floor_closest[local]:
  float_to_real (y : ('t,'w) float) <= x /\
  x < float_to_real y + 1 /\ float_is_integral y ==>
  is_closest {a | float_is_integral a /\ float_to_real a <= x} x y
Proof
  strip_tac >> fs [] >>
  simp [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  rpt strip_tac >>
  `binary_ieee$is_integral (float_to_real y) /\
   binary_ieee$is_integral (float_to_real b)` by
    metis_tac [float_is_integral_to_real] >>
  `float_to_real b <= float_to_real y` by
    (CCONTR_TAC >> fs [] >>
     `1 <= abs (float_to_real b - float_to_real y)` by
       (irule is_integral_separated >> simp [] >>
        realLib.REAL_ASM_ARITH_TAC) >>
     realLib.REAL_ASM_ARITH_TAC) >>
  realLib.REAL_ASM_ARITH_TAC
QED

Theorem integral_floor_unique[local]:
  float_to_real (y : ('t,'w) float) <= x /\
  x < float_to_real y + 1 /\ float_is_integral y /\
  ~float_is_zero y /\
  is_closest {a | float_is_integral a /\ float_to_real a <= x} x z ==>
  z = y
Proof
  strip_tac >> fs [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  `binary_ieee$is_integral (float_to_real z) /\
   binary_ieee$is_integral (float_to_real y)` by
    metis_tac [float_is_integral_to_real] >>
  `float_to_real z <= float_to_real y` by
    (CCONTR_TAC >> fs [] >>
     `1 <= abs (float_to_real z - float_to_real y)` by
       (irule is_integral_separated >> simp [] >>
        realLib.REAL_ASM_ARITH_TAC) >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `abs (float_to_real z - x) <= abs (float_to_real y - x)` by
    (qpat_x_assum
       `!b. float_is_integral b /\ float_to_real b <= x ==>
          abs (float_to_real z - x) <= abs (float_to_real b - x)`
       (qspec_then `y` mp_tac) >> simp []) >>
  `float_to_real z = float_to_real y` by
    (CCONTR_TAC >>
     `1 <= abs (float_to_real z - float_to_real y)` by
       (irule is_integral_separated >> simp []) >>
     realLib.REAL_ASM_ARITH_TAC) >>
  mp_tac (Q.SPECL [`z`, `y`] binary_ieeeTheory.float_to_real_eq) >>
  simp []
QED

Theorem integral_round_RTN_inrange:
  -largest (:'t # 'w) <= x /\ x <= largest (:'t # 'w) /\
  float_to_real (y : ('t,'w) float) <= x /\
  x < float_to_real y + 1 /\ float_is_integral y /\
  ~float_is_zero y ==>
  integral_round roundTowardNegative x = y
Proof
  strip_tac >> fs [] >>
  `~(x < -largest (:'t # 'w)) /\
   ~(x > largest (:'t # 'w))` by realLib.REAL_ASM_ARITH_TAC >>
  simp [binary_ieeeTheory.integral_round_def,
        binary_ieeeTheory.closest_def,
        binary_ieeeTheory.closest_such_def] >>
  SELECT_ELIM_TAC >> conj_tac
  >- (qexists_tac `y` >> irule integral_floor_closest >> simp [])
  >- metis_tac [integral_floor_unique]
QED

Theorem integral_ceiling_closest[local]:
  float_to_real (y : ('t,'w) float) - 1 < x /\
  x <= float_to_real y /\ float_is_integral y ==>
  is_closest {a | float_is_integral a /\ float_to_real a >= x} x y
Proof
  strip_tac >> fs [] >>
  simp [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  conj_tac >- realLib.REAL_ASM_ARITH_TAC >>
  rpt strip_tac >>
  `binary_ieee$is_integral (float_to_real y) /\
   binary_ieee$is_integral (float_to_real b)` by
    metis_tac [float_is_integral_to_real] >>
  `float_to_real y <= float_to_real b` by
    (CCONTR_TAC >> fs [] >>
     `1 <= abs (float_to_real y - float_to_real b)` by
       (irule is_integral_separated >> simp [] >>
        realLib.REAL_ASM_ARITH_TAC) >>
     realLib.REAL_ASM_ARITH_TAC) >>
  realLib.REAL_ASM_ARITH_TAC
QED

Theorem integral_ceiling_unique[local]:
  float_to_real (y : ('t,'w) float) - 1 < x /\
  x <= float_to_real y /\ float_is_integral y /\
  ~float_is_zero y /\
  is_closest {a | float_is_integral a /\ float_to_real a >= x} x z ==>
  z = y
Proof
  strip_tac >> fs [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  `binary_ieee$is_integral (float_to_real z) /\
   binary_ieee$is_integral (float_to_real y)` by
    metis_tac [float_is_integral_to_real] >>
  `float_to_real y <= float_to_real z` by
    (CCONTR_TAC >> fs [] >>
     `1 <= abs (float_to_real y - float_to_real z)` by
       (irule is_integral_separated >> simp [] >>
        realLib.REAL_ASM_ARITH_TAC) >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `abs (float_to_real z - x) <= abs (float_to_real y - x)` by
    (qpat_x_assum
       `!b. float_is_integral b /\ float_to_real b >= x ==>
          abs (float_to_real z - x) <= abs (float_to_real b - x)`
       (qspec_then `y` mp_tac) >> simp [] >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `float_to_real z = float_to_real y` by
    (CCONTR_TAC >>
     `1 <= abs (float_to_real y - float_to_real z)` by
       (irule is_integral_separated >> simp []) >>
     realLib.REAL_ASM_ARITH_TAC) >>
  mp_tac (Q.SPECL [`z`, `y`] binary_ieeeTheory.float_to_real_eq) >>
  simp []
QED

Theorem integral_round_RTP_inrange:
  -largest (:'t # 'w) <= x /\ x <= largest (:'t # 'w) /\
  float_to_real (y : ('t,'w) float) - 1 < x /\
  x <= float_to_real y /\ float_is_integral y /\
  ~float_is_zero y ==>
  integral_round roundTowardPositive x = y
Proof
  strip_tac >> fs [] >>
  `~(x < -largest (:'t # 'w)) /\
   ~(x > largest (:'t # 'w))` by realLib.REAL_ASM_ARITH_TAC >>
  simp [binary_ieeeTheory.integral_round_def,
        binary_ieeeTheory.closest_def,
        binary_ieeeTheory.closest_such_def] >>
  SELECT_ELIM_TAC >> conj_tac
  >- (qexists_tac `y` >> irule integral_ceiling_closest >> simp [])
  >- metis_tac [integral_ceiling_unique]
QED

Theorem directed_floor_result_is_closest:
  -largest (:'t # 'w) <= x /\ x <= largest (:'t # 'w) /\
  integral_round roundTowardNegative x = lo /\
  float_is_integral lo /\ float_to_real lo <= x ==>
  is_closest
    {a : ('t,'w) float |
       float_is_integral a /\ float_to_real a <= x} x lo
Proof
  strip_tac >>
  `~(x < -largest (:'t # 'w)) /\
   ~(x > largest (:'t # 'w))` by realLib.REAL_ASM_ARITH_TAC >>
  fs [binary_ieeeTheory.integral_round_def,
      binary_ieeeTheory.closest_def] >>
  qpat_x_assum `closest_such (K T) _ x = lo`
    (fn result_eq =>
      rewrite_tac [GSYM result_eq] >>
      irule (cj 1 closest_such_properties) >>
      rewrite_tac [GSYM pred_setTheory.MEMBER_NOT_EMPTY] >>
      qexists_tac `lo` >> simp [IN_DEF])
QED

Theorem directed_ceiling_result_is_closest:
  -largest (:'t # 'w) <= x /\ x <= largest (:'t # 'w) /\
  integral_round roundTowardPositive x = hi /\
  float_is_integral hi /\ float_to_real hi >= x ==>
  is_closest
    {a : ('t,'w) float |
       float_is_integral a /\ float_to_real a >= x} x hi
Proof
  strip_tac >>
  `~(x < -largest (:'t # 'w)) /\
   ~(x > largest (:'t # 'w))` by realLib.REAL_ASM_ARITH_TAC >>
  fs [binary_ieeeTheory.integral_round_def,
      binary_ieeeTheory.closest_def] >>
  qpat_x_assum `closest_such (K T) _ x = hi`
    (fn result_eq =>
      rewrite_tac [GSYM result_eq] >>
      irule (cj 1 closest_such_properties) >>
      rewrite_tac [GSYM pred_setTheory.MEMBER_NOT_EMPTY] >>
      qexists_tac `hi` >> simp [IN_DEF])
QED

Theorem integral_round_RNE_certificate[local]:
  -threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w) /\
  is_closest float_is_integral x (y : ('t,'w) float) /\
  (?n. EVEN n /\ abs (float_to_real y) = &n) /\
  (!z. is_closest float_is_integral x z /\
       (?n. EVEN n /\ abs (float_to_real z) = &n) ==> z = y) ==>
  integral_round roundTiesToEven x = y
Proof
  strip_tac >> fs [] >>
  `~(x <= -threshold (:'t # 'w)) /\
   ~(x >= threshold (:'t # 'w))` by realLib.REAL_ASM_ARITH_TAC >>
  simp [binary_ieeeTheory.integral_round_def,
        binary_ieeeTheory.closest_such_def] >>
  SELECT_ELIM_TAC >> conj_tac
  >- (qexists_tac `y` >> simp [])
  >- metis_tac []
QED

Theorem even_num_reals_separated[local]:
  m <> n ==> 2 <= abs (&(2 * m) - &(2 * n))
Proof
  strip_tac >> Cases_on `m < n`
  >- (`SUC m <= n` by fs [arithmeticTheory.LESS_EQ] >>
      `&(SUC m) <= (&n : real)` by simp [] >>
      `(&(2 * m) : real) = 2 * &m /\
       (&(2 * n) : real) = 2 * &n /\
       (&(SUC m) : real) = &m + 1` by simp [] >>
      `abs (&(2 * m) - &(2 * n)) =
       -(&(2 * m) - &(2 * n))` by
        (irule realTheory.ABS_EQ_NEG' >>
         realLib.REAL_ASM_ARITH_TAC) >>
      realLib.REAL_ASM_ARITH_TAC)
  >- (`n < m` by metis_tac [arithmeticTheory.LESS_CASES_IMP] >>
      `SUC n <= m` by fs [arithmeticTheory.LESS_EQ] >>
      `&(SUC n) <= (&m : real)` by simp [] >>
      `(&(2 * m) : real) = 2 * &m /\
       (&(2 * n) : real) = 2 * &n /\
       (&(SUC n) : real) = &n + 1` by simp [] >>
      `abs (&(2 * m) - &(2 * n)) =
       &(2 * m) - &(2 * n)` by
        (irule realTheory.ABS_REDUCE >>
         realLib.REAL_ASM_ARITH_TAC) >>
      realLib.REAL_ASM_ARITH_TAC)
QED

Theorem even_num_reals_opposite_separated[local]:
  m <> 0 \/ n <> 0 ==> 2 <= abs (&(2 * m) + &(2 * n))
Proof
  strip_tac >>
  `1 <= m \/ 1 <= n` by Omega.OMEGA_TAC >>
  fs [] >>
  `(&1 : real) <= &m \/ (&1 : real) <= &n` by simp [] >>
  simp [realTheory.abs, realTheory.REAL_OF_NUM_MUL] >>
  realLib.REAL_ASM_ARITH_TAC
QED

Theorem even_absolute_reals_separated[local]:
  (?m. EVEN m /\ abs a = &m) /\
  (?n. EVEN n /\ abs b = &n) /\ a <> b ==>
  2 <= abs (a - b)
Proof
  rw [arithmeticTheory.EVEN_EXISTS] >>
  Cases_on `0 <= a` >> Cases_on `0 <= b`
  >- (fs [realTheory.ABS_REDUCE] >>
      irule even_num_reals_separated >>
      CCONTR_TAC >> fs [] >> metis_tac [])
  >- (`b < 0` by realLib.REAL_ASM_ARITH_TAC >>
      `abs b = -b` by metis_tac [realTheory.ABS_EQ_NEG] >>
      fs [realTheory.ABS_REDUCE] >>
      qpat_x_assum `-b = _` (fn th =>
        assume_tac (SIMP_RULE (srw_ss ()) []
          (AP_TERM ``\r : real. -r`` th))) >>
      fs [realTheory.REAL_SUB_RNEG])
  >- (`a < 0` by realLib.REAL_ASM_ARITH_TAC >>
      `abs a = -a` by metis_tac [realTheory.ABS_EQ_NEG] >>
      fs [realTheory.ABS_REDUCE] >>
      qpat_x_assum `-a = _` (fn th =>
        assume_tac (SIMP_RULE (srw_ss ()) []
          (AP_TERM ``\r : real. -r`` th))) >>
      once_rewrite_tac [realTheory.ABS_SUB] >>
      fs [realTheory.REAL_SUB_RNEG])
  >- (`a < 0 /\ b < 0` by realLib.REAL_ASM_ARITH_TAC >>
      `abs a = -a /\ abs b = -b` by
        metis_tac [realTheory.ABS_EQ_NEG] >>
      fs [] >>
      qpat_x_assum `-a = _` (fn th =>
        assume_tac (SIMP_RULE (srw_ss ()) []
          (AP_TERM ``\r : real. -r`` th))) >>
      qpat_x_assum `-b = _` (fn th =>
        assume_tac (SIMP_RULE (srw_ss ()) []
          (AP_TERM ``\r : real. -r`` th))) >>
      fs [realTheory.REAL_SUB_NEG2] >>
      irule even_num_reals_separated >>
      CCONTR_TAC >> fs [] >> metis_tac [])
QED

Theorem integral_candidate_closest_is_integral[local]:
  is_closest integral_round_candidate x
    (y : ('t,'w) float) /\ float_is_integral y ==>
  is_closest float_is_integral x y
Proof
  rw [binary_ieeeTheory.is_closest_def, IN_DEF,
      integral_round_candidate_def] >>
  metis_tac []
QED

Theorem even_integral_closest_unique[local]:
  is_closest float_is_integral x (y : ('t,'w) float) /\
  (?n. EVEN n /\ abs (float_to_real y) = &n) /\
  ~float_is_zero y /\
  2 * abs (float_to_real y - x) <= 1 ==>
  !z. is_closest float_is_integral x z /\
      (?n. EVEN n /\ abs (float_to_real z) = &n) ==> z = y
Proof
  strip_tac >> gen_tac >> strip_tac >>
  fs [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  `abs (float_to_real y - x) <=
   abs (float_to_real z - x) /\
   abs (float_to_real z - x) <=
   abs (float_to_real y - x)` by metis_tac [] >>
  `abs (float_to_real y - float_to_real z) <=
   abs (float_to_real y - x) +
   abs (float_to_real z - x)` by
    (qspec_then `float_to_real y - x`
       (qspec_then `x - float_to_real z` mp_tac)
       realTheory.ABS_TRIANGLE >>
     simp [] >> realLib.REAL_ARITH_TAC) >>
  `float_to_real y = float_to_real z` by
    (CCONTR_TAC >>
     `2 <= abs (float_to_real y - float_to_real z)` by
       (irule even_absolute_reals_separated >> simp []) >>
     real_arith_from
       [`2 <= abs (float_to_real y - float_to_real z)`,
        `abs (float_to_real y - float_to_real z) <=
         abs (float_to_real y - x) + abs (float_to_real z - x)`,
        `abs (float_to_real y - x) <= abs (float_to_real z - x)`,
        `abs (float_to_real z - x) <= abs (float_to_real y - x)`,
        `2 * abs (float_to_real y - x) <= 1`]) >>
  mp_tac (Q.SPECL [`y`, `z`]
    binary_ieeeTheory.float_to_real_eq) >>
  simp []
QED

Theorem integral_round_RNE_nearest:
  -threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w) /\
  float_is_integral (y : ('t,'w) float) /\ ~float_is_zero y /\
  2 * abs (float_to_real y - x) <= 1 /\
  (?n. EVEN n /\ abs (float_to_real y) = &n) /\
  abs (float_to_real y - x) <
    abs (float_to_real (float_plus_infinity (:'t # 'w)) - x) /\
  abs (float_to_real y - x) <
    abs (float_to_real (float_minus_infinity (:'t # 'w)) - x) ==>
  integral_round roundTiesToEven x = y
Proof
  strip_tac >>
  `is_closest integral_round_candidate x y` by
    (irule integral_candidate_nearest >> simp []) >>
  `is_closest float_is_integral x y` by
    (irule integral_candidate_closest_is_integral >> simp []) >>
  irule integral_round_RNE_certificate >> simp [] >>
  metis_tac [even_integral_closest_unique]
QED

(* When the two directed integral rounds expose distinct neighboring
   candidates, a strict distance comparison makes the closest integral
   record unique.  This is the coarse-spacing path: it never rounds a
   mathematical integer and then rounds that result a second time. *)
Theorem integral_round_RNE_from_directed_lower:
  -threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w) /\
  is_closest
    {a : ('t,'w) float |
       float_is_integral a /\ float_to_real a <= x} x lo /\
  is_closest
    {a : ('t,'w) float |
       float_is_integral a /\ float_to_real a >= x} x hi /\
  float_is_integral lo /\ float_to_real lo <= x /\
  float_is_integral hi /\ float_to_real hi >= x /\
  ~float_is_zero lo /\
  abs (float_to_real lo - x) < abs (float_to_real hi - x) /\
  (?n. EVEN n /\ abs (float_to_real lo) = &n) ==>
  integral_round roundTiesToEven x = lo
Proof
  strip_tac >>
  irule integral_round_RNE_certificate >> simp [] >>
  conj_tac
  >- (fs [binary_ieeeTheory.is_closest_def, IN_DEF] >>
      rpt strip_tac >>
      Cases_on `float_to_real z <= x`
      >- (qpat_x_assum
            `!b. float_is_integral b /\ float_to_real b <= x ==> _`
            (qspec_then `z` mp_tac) >>
          qpat_x_assum `!b. float_is_integral b ==> _`
            (qspec_then `lo` mp_tac) >>
          mp_tac (Q.SPECL [`lo`, `z`]
            binary_ieeeTheory.float_to_real_eq) >>
          simp [] >> rpt strip_tac >> sym_tac >>
          qpat_x_assum
            `float_to_real lo = float_to_real z <=> lo = z`
            (irule o iffLR) >>
          real_arith_from
            [`abs (float_to_real lo - x) <= abs (float_to_real z - x)`,
             `abs (float_to_real z - x) <= abs (float_to_real lo - x)`,
             `float_to_real z <= x`, `float_to_real lo <= x`])
      >- (qpat_x_assum
            `!b. float_is_integral b /\ float_to_real b >= x ==> _`
            (qspec_then `z` mp_tac) >>
          qpat_x_assum `!b. float_is_integral b ==> _`
            (qspec_then `lo` mp_tac) >>
          simp [] >>
          real_arith_from
            [`~(float_to_real z <= x)`, `float_is_integral z`,
             `float_is_integral lo`,
             `abs (float_to_real lo - x) < abs (float_to_real hi - x)`])) >>
  (fs [binary_ieeeTheory.is_closest_def, IN_DEF] >>
   rpt strip_tac >>
   Cases_on `float_to_real b <= x`
   >- (qpat_x_assum
         `!c. float_is_integral c /\ float_to_real c <= x ==> _`
         (qspec_then `b` mp_tac) >>
       simp [])
   >- (qpat_x_assum
         `!c. float_is_integral c /\ float_to_real c >= x ==> _`
         (qspec_then `b` mp_tac) >>
       simp [] >>
       real_arith_from
         [`~(float_to_real b <= x)`, `float_is_integral b`,
          `abs (float_to_real lo - x) < abs (float_to_real hi - x)`]))
QED

Theorem integral_round_RNE_from_directed_upper:
  -threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w) /\
  is_closest
    {a : ('t,'w) float |
       float_is_integral a /\ float_to_real a <= x} x lo /\
  is_closest
    {a : ('t,'w) float |
       float_is_integral a /\ float_to_real a >= x} x hi /\
  float_is_integral lo /\ float_to_real lo <= x /\
  float_is_integral hi /\ float_to_real hi >= x /\
  ~float_is_zero hi /\
  abs (float_to_real hi - x) < abs (float_to_real lo - x) /\
  (?n. EVEN n /\ abs (float_to_real hi) = &n) ==>
  integral_round roundTiesToEven x = hi
Proof
  strip_tac >>
  irule integral_round_RNE_certificate >> simp [] >>
  conj_tac
  >- (fs [binary_ieeeTheory.is_closest_def, IN_DEF] >>
      rpt strip_tac >>
      Cases_on `x <= float_to_real z`
      >- (qpat_x_assum
            `!b. float_is_integral b /\ float_to_real b >= x ==> _`
            (qspec_then `z` mp_tac) >>
          qpat_x_assum `!b. float_is_integral b ==> _`
            (qspec_then `hi` mp_tac) >>
          mp_tac (Q.SPECL [`hi`, `z`]
            binary_ieeeTheory.float_to_real_eq) >>
          simp [realTheory.real_ge] >> rpt strip_tac >> sym_tac >>
          qpat_x_assum
            `float_to_real hi = float_to_real z <=> hi = z`
            (irule o iffLR) >>
          real_arith_from
            [`abs (float_to_real hi - x) <= abs (float_to_real z - x)`,
             `abs (float_to_real z - x) <= abs (float_to_real hi - x)`,
             `x <= float_to_real z`, `float_to_real hi >= x`])
      >- (qpat_x_assum
            `!b. float_is_integral b /\ float_to_real b <= x ==> _`
            (qspec_then `z` mp_tac) >>
          qpat_x_assum `!b. float_is_integral b ==> _`
            (qspec_then `hi` mp_tac) >>
          simp [] >>
          real_arith_from
            [`~(x <= float_to_real z)`, `float_is_integral z`,
             `float_is_integral hi`,
             `abs (float_to_real hi - x) < abs (float_to_real lo - x)`])) >>
  (fs [binary_ieeeTheory.is_closest_def, IN_DEF] >>
   rpt strip_tac >>
   Cases_on `x <= float_to_real b`
   >- (qpat_x_assum
         `!c. float_is_integral c /\ float_to_real c >= x ==> _`
         (qspec_then `b` mp_tac) >>
       simp [] >>
       real_arith_from [`x <= float_to_real b`, `float_is_integral b`])
   >- (qpat_x_assum
         `!c. float_is_integral c /\ float_to_real c <= x ==> _`
         (qspec_then `b` mp_tac) >>
       simp [] >>
       real_arith_from
         [`~(x <= float_to_real b)`, `float_is_integral b`,
          `abs (float_to_real hi - x) < abs (float_to_real lo - x)`]))
QED

Theorem integral_float_is_finite[local]:
  float_is_integral (y : ('t,'w) float) ==> float_is_finite y
Proof
  fs [binary_ieeeTheory.float_is_integral_def,
      binary_ieeeTheory.float_is_finite_def] >>
  Cases_on `float_value y` >> fs []
QED

Theorem integral_float_within_largest[local]:
  float_is_integral (y : ('t,'w) float) ==>
  -largest (:'t # 'w) <= float_to_real y /\
  float_to_real y <= largest (:'t # 'w)
Proof
  strip_tac >> drule integral_float_is_finite >> strip_tac >>
  drule lift_ieeeTheory.float_to_real_finite >>
  Cases_on `0 <= float_to_real y` >>
  fs [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC
QED

Theorem directed_round_floor_integral_closest[local]:
  -largest (:'t # 'w) <= x /\ x <= largest (:'t # 'w) /\
  round roundTowardNegative x = (y : ('t,'w) float) /\
  float_is_integral y /\ float_to_real y <= x ==>
  is_closest
    {a : ('t,'w) float |
       float_is_integral a /\ float_to_real a <= x} x y
Proof
  strip_tac >>
  `float_is_finite y` by metis_tac [integral_float_is_finite] >>
  `~(x < -largest (:'t # 'w)) /\
   ~(x > largest (:'t # 'w))` by realLib.REAL_ASM_ARITH_TAC >>
  `is_closest
     {a : ('t,'w) float |
        float_is_finite a /\ float_to_real a <= x} x y` by
    (fs [binary_ieeeTheory.round_def,
         binary_ieeeTheory.closest_def] >>
     qpat_x_assum `closest_such (K T) _ x = y`
       (fn result_eq =>
         rewrite_tac [GSYM result_eq] >>
         irule (cj 1 closest_such_properties) >>
         rewrite_tac [GSYM pred_setTheory.MEMBER_NOT_EMPTY] >>
         qexists_tac `y` >> simp [IN_DEF])) >>
  fs [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  rpt strip_tac >> first_x_assum irule >>
  simp [] >> metis_tac [integral_float_is_finite]
QED

Theorem directed_round_ceiling_integral_closest[local]:
  -largest (:'t # 'w) <= x /\ x <= largest (:'t # 'w) /\
  round roundTowardPositive x = (y : ('t,'w) float) /\
  float_is_integral y /\ float_to_real y >= x ==>
  is_closest
    {a : ('t,'w) float |
       float_is_integral a /\ float_to_real a >= x} x y
Proof
  strip_tac >>
  `float_is_finite y` by metis_tac [integral_float_is_finite] >>
  `~(x < -largest (:'t # 'w)) /\
   ~(x > largest (:'t # 'w))` by realLib.REAL_ASM_ARITH_TAC >>
  `is_closest
     {a : ('t,'w) float |
        float_is_finite a /\ float_to_real a >= x} x y` by
    (fs [binary_ieeeTheory.round_def,
         binary_ieeeTheory.closest_def] >>
     qpat_x_assum `closest_such (K T) _ x = y`
       (fn result_eq =>
         rewrite_tac [GSYM result_eq] >>
         irule (cj 1 closest_such_properties) >>
         rewrite_tac [GSYM pred_setTheory.MEMBER_NOT_EMPTY] >>
         qexists_tac `y` >> simp [IN_DEF])) >>
  fs [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  rpt strip_tac >> first_x_assum irule >>
  simp [] >> metis_tac [integral_float_is_finite]
QED

Theorem directed_floor_integral_closest_unique[local]:
  is_closest
    {a : ('t,'w) float |
       float_is_integral a /\ float_to_real a <= x} x y /\
  ~float_is_zero y /\
  is_closest
    {a : ('t,'w) float |
       float_is_integral a /\ float_to_real a <= x} x z ==>
  z = y
Proof
  strip_tac >> fs [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  `abs (float_to_real y - x) <= abs (float_to_real z - x) /\
   abs (float_to_real z - x) <= abs (float_to_real y - x)` by
    metis_tac [] >>
  `float_to_real z = float_to_real y` by
    (Cases_on `0 <= float_to_real z - x` >>
     Cases_on `0 <= float_to_real y - x` >>
     fs [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
  mp_tac (Q.SPECL [`z`, `y`] binary_ieeeTheory.float_to_real_eq) >>
  simp []
QED

Theorem directed_ceiling_integral_closest_unique[local]:
  is_closest
    {a : ('t,'w) float |
       float_is_integral a /\ float_to_real a >= x} x y /\
  ~float_is_zero y /\
  is_closest
    {a : ('t,'w) float |
       float_is_integral a /\ float_to_real a >= x} x z ==>
  z = y
Proof
  strip_tac >> fs [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  `abs (float_to_real y - x) <= abs (float_to_real z - x) /\
   abs (float_to_real z - x) <= abs (float_to_real y - x)` by
    metis_tac [] >>
  `float_to_real z = float_to_real y` by
    (Cases_on `0 <= float_to_real z - x` >>
     Cases_on `0 <= float_to_real y - x` >>
     fs [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
  mp_tac (Q.SPECL [`z`, `y`] binary_ieeeTheory.float_to_real_eq) >>
  simp []
QED

Theorem integral_round_RTN_from_float_round:
  -largest (:'t # 'w) <= x /\ x <= largest (:'t # 'w) /\
  round roundTowardNegative x = (y : ('t,'w) float) /\
  float_is_integral y /\ float_to_real y <= x /\
  ~float_is_zero y ==>
  integral_round roundTowardNegative x = y
Proof
  strip_tac >>
  `is_closest
     {a : ('t,'w) float |
        float_is_integral a /\ float_to_real a <= x} x y` by
    (irule directed_round_floor_integral_closest >> simp []) >>
  `~(x < -largest (:'t # 'w)) /\
   ~(x > largest (:'t # 'w))` by realLib.REAL_ASM_ARITH_TAC >>
  simp [binary_ieeeTheory.integral_round_def,
        binary_ieeeTheory.closest_def,
        binary_ieeeTheory.closest_such_def] >>
  SELECT_ELIM_TAC >> conj_tac
  >- (qexists_tac `y` >> simp [])
  >- metis_tac [directed_floor_integral_closest_unique]
QED

Theorem integral_round_RTP_from_float_round:
  -largest (:'t # 'w) <= x /\ x <= largest (:'t # 'w) /\
  round roundTowardPositive x = (y : ('t,'w) float) /\
  float_is_integral y /\ float_to_real y >= x /\
  ~float_is_zero y ==>
  integral_round roundTowardPositive x = y
Proof
  strip_tac >>
  `is_closest
     {a : ('t,'w) float |
        float_is_integral a /\ float_to_real a >= x} x y` by
    (irule directed_round_ceiling_integral_closest >> simp []) >>
  `~(x < -largest (:'t # 'w)) /\
   ~(x > largest (:'t # 'w))` by realLib.REAL_ASM_ARITH_TAC >>
  simp [binary_ieeeTheory.integral_round_def,
        binary_ieeeTheory.closest_def,
        binary_ieeeTheory.closest_such_def] >>
  SELECT_ELIM_TAC >> conj_tac
  >- (qexists_tac `y` >> simp [])
  >- metis_tac [directed_ceiling_integral_closest_unique]
QED

Theorem above_largest_integral_closest[local]:
  largest (:'t # 'w) < x /\
  float_is_integral (y : ('t,'w) float) /\
  float_to_real y = largest (:'t # 'w) ==>
  is_closest float_is_integral x y
Proof
  strip_tac >>
  simp [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  rpt strip_tac >>
  drule integral_float_within_largest >>
  Cases_on `0 <= float_to_real b - x` >>
  Cases_on `0 <= float_to_real y - x` >>
  fs [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC
QED

Theorem above_largest_integral_closest_unique[local]:
  largest (:'t # 'w) < x /\
  float_is_integral (y : ('t,'w) float) /\
  float_to_real y = largest (:'t # 'w) /\
  ~float_is_zero y /\
  is_closest float_is_integral x z ==>
  z = y
Proof
  strip_tac >>
  fs [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  drule integral_float_within_largest >> strip_tac >>
  qpat_x_assum `!b. float_is_integral b ==> _`
    (qspec_then `y` mp_tac) >> simp [] >> strip_tac >>
  `float_to_real z = float_to_real y` by
    (Cases_on `0 <= float_to_real z - x` >>
     Cases_on `0 <= float_to_real y - x` >>
     fs [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
  mp_tac (Q.SPECL [`z`, `y`] binary_ieeeTheory.float_to_real_eq) >>
  simp []
QED

Theorem below_minus_largest_integral_closest[local]:
  x < -largest (:'t # 'w) /\
  float_is_integral (y : ('t,'w) float) /\
  float_to_real y = -largest (:'t # 'w) ==>
  is_closest float_is_integral x y
Proof
  strip_tac >>
  simp [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  rpt strip_tac >>
  drule integral_float_within_largest >>
  Cases_on `0 <= float_to_real b - x` >>
  Cases_on `0 <= float_to_real y - x` >>
  fs [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC
QED

Theorem below_minus_largest_integral_closest_unique[local]:
  x < -largest (:'t # 'w) /\
  float_is_integral (y : ('t,'w) float) /\
  float_to_real y = -largest (:'t # 'w) /\
  ~float_is_zero y /\
  is_closest float_is_integral x z ==>
  z = y
Proof
  strip_tac >>
  fs [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  drule integral_float_within_largest >> strip_tac >>
  qpat_x_assum `!b. float_is_integral b ==> _`
    (qspec_then `y` mp_tac) >> simp [] >> strip_tac >>
  `float_to_real z = float_to_real y` by
    (Cases_on `0 <= float_to_real z - x` >>
     Cases_on `0 <= float_to_real y - x` >>
     fs [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
  mp_tac (Q.SPECL [`z`, `y`] binary_ieeeTheory.float_to_real_eq) >>
  simp []
QED

Theorem integral_round_RNE_just_below_overflow:
  largest (:'t # 'w) < x /\ x < threshold (:'t # 'w) /\
  float_is_integral (y : ('t,'w) float) /\
  float_to_real y = largest (:'t # 'w) /\ ~float_is_zero y /\
  (?n. EVEN n /\ abs (float_to_real y) = &n) ==>
  integral_round roundTiesToEven x = y
Proof
  strip_tac >> irule integral_round_RNE_certificate >> simp [] >>
  conj_tac
  >- (rpt strip_tac >>
      metis_tac [above_largest_integral_closest_unique])
  >- (conj_tac
      >- (`0 <= largest (:'t # 'w)` by simp [] >>
          `0 < threshold (:'t # 'w)` by simp [] >>
          realLib.REAL_ASM_ARITH_TAC)
      >- (irule above_largest_integral_closest >> simp []))
QED

Theorem integral_round_RNE_just_above_underflow:
  -threshold (:'t # 'w) < x /\ x < -largest (:'t # 'w) /\
  float_is_integral (y : ('t,'w) float) /\
  float_to_real y = -largest (:'t # 'w) /\ ~float_is_zero y /\
  (?n. EVEN n /\ abs (float_to_real y) = &n) ==>
  integral_round roundTiesToEven x = y
Proof
  strip_tac >> irule integral_round_RNE_certificate >> simp [] >>
  conj_tac
  >- (rpt strip_tac >>
      metis_tac [below_minus_largest_integral_closest_unique])
  >- (conj_tac
      >- (`0 <= largest (:'t # 'w)` by simp [] >>
          `0 < threshold (:'t # 'w)` by simp [] >>
          realLib.REAL_ASM_ARITH_TAC)
      >- (irule below_minus_largest_integral_closest >> simp []))
QED

val _ = export_theory ();
