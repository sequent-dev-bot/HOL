open HolKernel Parse boolLib bossLib wordsLib;
open arithmeticTheory logrootTheory smtfloatTheory;

val _ = new_theory "smtfloatReplay";

Definition smtfp_jam_def:
  smtfp_jam (n : num) (d : num) =
    let q = n DIV (2 ** d) in
    let r = n MOD (2 ** d) in
      q + if r <> 0 /\ EVEN q then 1 else 0
End

Theorem smtfp_jam_zero_shift[simp]:
  smtfp_jam n 0 = n
Proof
  simp [smtfp_jam_def]
QED

Theorem smtfp_jam_eq_zero[simp]:
  smtfp_jam n d = 0 <=> n = 0
Proof
  eq_tac
  >- (strip_tac >>
      `n DIV 2 ** d = 0` by
        (Cases_on `n MOD 2 ** d <> 0 /\ EVEN (n DIV 2 ** d)` >>
         fs [smtfp_jam_def]) >>
      `n MOD 2 ** d = 0` by fs [smtfp_jam_def] >>
      `0 < 2 ** d` by simp [] >>
      `n = n DIV 2 ** d * 2 ** d + n MOD 2 ** d /\
       n MOD 2 ** d < 2 ** d` by
        (MATCH_MP_TAC (Q.SPEC `2 ** d` DIVISION) >> simp []) >>
      rfs [])
  >- simp [smtfp_jam_def]
QED

Theorem smtfp_jam_step_even_lt[local]:
  EVEN (a : num) ==>
  (q + (if (r : num) <> 0 /\ EVEN q then 1 else 0) < a <=> q < a)
Proof
  strip_tac >> Cases_on `r = 0` >> simp [] >>
  Cases_on `EVEN q` >> fs [EVEN_EXISTS] >> Omega.OMEGA_TAC
QED

Theorem smtfp_jam_step_even_eq[local]:
  EVEN (a : num) ==>
  (q + (if (r : num) <> 0 /\ EVEN q then 1 else 0) = a <=>
   q = a /\ r = 0)
Proof
  strip_tac >> Cases_on `r = 0` >> simp [] >>
  Cases_on `EVEN q` >> fs [EVEN_EXISTS] >> Omega.OMEGA_TAC
QED

Theorem smtfp_jam_even_lt:
  EVEN (a : num) ==> (smtfp_jam n d < a <=> n < a * 2 ** d)
Proof
  strip_tac >> simp_tac pure_ss [smtfp_jam_def, LET_THM] >>
  irule EQ_TRANS >> qexists_tac `n DIV 2 ** d < a` >> conj_tac
  >- (MATCH_MP_TAC smtfp_jam_step_even_lt >> ASM_REWRITE_TAC [])
  >- simp [DIV_LT_X]
QED

Theorem smtfp_jam_even_eq:
  EVEN (a : num) ==> (smtfp_jam n d = a <=> n = a * 2 ** d)
Proof
  strip_tac >> simp [smtfp_jam_def, smtfp_jam_step_even_eq] >>
  `0 < 2 ** d` by simp [] >>
  `n = n DIV 2 ** d * 2 ** d + n MOD 2 ** d /\
   n MOD 2 ** d < 2 ** d` by
    (MATCH_MP_TAC (Q.SPEC `2 ** d` DIVISION) >> simp []) >>
  eq_tac >> strip_tac >> fs []
QED

Theorem smtfp_jam_even_add:
  EVEN (a : num) ==>
  smtfp_jam (a * 2 ** d + b) d = a + smtfp_jam b d
Proof
  strip_tac >>
  `0 < 2 ** d` by simp [] >>
  `(a * 2 ** d + b) DIV 2 ** d = a + b DIV 2 ** d` by
    simp [ADD_DIV_ADD_DIV] >>
  `(a * 2 ** d + b) MOD 2 ** d = b MOD 2 ** d` by
    simp [MOD_TIMES] >>
  simp_tac pure_ss [smtfp_jam_def, LET_THM] >>
  asm_rewrite_tac [] >>
  asm_simp_tac pure_ss [EVEN_ADD, ADD_ASSOC, EQ_CLAUSES] >> REFL_TAC
QED

Theorem num_lt_ext[local]:
  (!a : num. x < a <=> y < a) ==> x = y
Proof
  strip_tac >> CCONTR_TAC >>
  Cases_on `x < y`
  >- (first_x_assum (mp_tac o Q.SPEC `y`) >> simp [])
  >- (`y < x` by Omega.OMEGA_TAC >>
      first_x_assum (mp_tac o Q.SPEC `x`) >> simp [])
QED

Theorem smtfp_jam_div:
  EVEN (divisor : num) /\ 0 < divisor ==>
  smtfp_jam n d DIV divisor = n DIV (divisor * 2 ** d)
Proof
  strip_tac >> irule num_lt_ext >> gen_tac >>
  simp [DIV_LT_X, smtfp_jam_even_lt, EVEN_MULT, MULT_ASSOC]
QED

Theorem smtfp_jam_div_pow:
  1 <= k ==>
  smtfp_jam n d DIV 2 ** k = n DIV 2 ** (d + k)
Proof
  strip_tac >>
  `EVEN (2 ** k) /\ 0 < 2 ** k` by simp [EVEN_EXP_IFF] >>
  drule smtfp_jam_div >>
  simp [EXP_ADD, MULT_COMM]
QED

Theorem num_mod_lt_cut[local]:
  0 < divisor ==>
  (x MOD divisor < a <=>
   x < x DIV divisor * divisor + a)
Proof
  strip_tac >>
  `x = x DIV divisor * divisor + x MOD divisor /\
   x MOD divisor < divisor` by
    (MATCH_MP_TAC (Q.SPEC `divisor` DIVISION) >> simp []) >>
  Omega.OMEGA_TAC
QED

Theorem num_mod_eq_cut[local]:
  0 < divisor ==>
  (x MOD divisor = a <=>
   x = x DIV divisor * divisor + a)
Proof
  strip_tac >>
  `x = x DIV divisor * divisor + x MOD divisor /\
   x MOD divisor < divisor` by
    (MATCH_MP_TAC (Q.SPEC `divisor` DIVISION) >> simp []) >>
  Omega.OMEGA_TAC
QED

Theorem smtfp_jam_mod_lt:
  EVEN (divisor : num) /\ 0 < divisor /\ EVEN a ==>
  (smtfp_jam n d MOD divisor < a <=>
   n MOD (divisor * 2 ** d) < a * 2 ** d)
Proof
  strip_tac >>
  `smtfp_jam n d DIV divisor = n DIV (divisor * 2 ** d)` by
    simp [smtfp_jam_div] >>
  qabbrev_tac `q = n DIV (divisor * 2 ** d)` >>
  `EVEN (q * divisor + a)` by simp [EVEN_ADD, EVEN_MULT] >>
  `smtfp_jam n d < q * divisor + a <=>
   n < (q * divisor + a) * 2 ** d` by
    simp [smtfp_jam_even_lt] >>
  `0 < divisor * 2 ** d` by simp [] >>
  `smtfp_jam n d MOD divisor < a <=>
   smtfp_jam n d < q * divisor + a` by
    simp [num_mod_lt_cut, Abbr `q`] >>
  `n MOD (divisor * 2 ** d) < a * 2 ** d <=>
   n < q * (divisor * 2 ** d) + a * 2 ** d` by
    simp [num_mod_lt_cut, Abbr `q`] >>
  fs [LEFT_ADD_DISTRIB, MULT_ASSOC]
QED

Theorem smtfp_jam_mod_eq:
  EVEN (divisor : num) /\ 0 < divisor /\ EVEN a ==>
  (smtfp_jam n d MOD divisor = a <=>
   n MOD (divisor * 2 ** d) = a * 2 ** d)
Proof
  strip_tac >>
  `smtfp_jam n d DIV divisor = n DIV (divisor * 2 ** d)` by
    simp [smtfp_jam_div] >>
  qabbrev_tac `q = n DIV (divisor * 2 ** d)` >>
  `EVEN (q * divisor + a)` by simp [EVEN_ADD, EVEN_MULT] >>
  `smtfp_jam n d = q * divisor + a <=>
   n = (q * divisor + a) * 2 ** d` by
    simp [smtfp_jam_even_eq] >>
  `0 < divisor * 2 ** d` by simp [] >>
  `smtfp_jam n d MOD divisor = a <=>
   smtfp_jam n d = q * divisor + a` by
    simp [num_mod_eq_cut, Abbr `q`] >>
  `n MOD (divisor * 2 ** d) = a * 2 ** d <=>
   n = q * (divisor * 2 ** d) + a * 2 ** d` by
    simp [num_mod_eq_cut, Abbr `q`] >>
  fs [LEFT_ADD_DISTRIB, MULT_ASSOC]
QED

Theorem smtfp_jam_log2:
  2 ** d <= n ==> LOG2 (smtfp_jam n d) + d = LOG2 n
Proof
  strip_tac >> qabbrev_tac `j = smtfp_jam n d` >>
  `0 < 2 ** d` by simp [] >>
  `0 < n` by
    (MATCH_MP_TAC LESS_LESS_EQ_TRANS >> qexists_tac `2 ** d` >> simp []) >>
  `j <> 0` by fs [Abbr `j`, smtfp_jam_eq_zero] >>
  `0 < j` by Omega.OMEGA_TAC >>
  `2 ** LOG2 j <= j /\ j < 2 ** SUC (LOG2 j)` by
    simp [bitTheory.LOG2_def, logrootTheory.LOG2_PROPERTY] >>
  `EVEN (2 ** SUC (LOG2 j))` by simp [EVEN_EXP_IFF] >>
  `n < 2 ** SUC (LOG2 j) * 2 ** d` by
    fs [Abbr `j`, smtfp_jam_even_lt] >>
  `2 ** (LOG2 j + d) <= n` by
    (Cases_on `LOG2 j`
     >- simp []
     >- (`EVEN (2 ** SUC n')` by simp [EVEN_EXP_IFF] >>
         `~(j < 2 ** SUC n')` by simp [] >>
         `j < 2 ** SUC n' <=> n < 2 ** SUC n' * 2 ** d` by
           (simp_tac pure_ss [Abbr `j`] >>
            MATCH_MP_TAC smtfp_jam_even_lt >> simp [EVEN_EXP_IFF]) >>
         `~(n < 2 ** SUC n' * 2 ** d)` by fs [] >>
         `2 ** SUC n' * 2 ** d <= n` by simp [GSYM NOT_LESS] >>
         fs [EXP_ADD])) >>
  `n < 2 ** SUC (LOG2 j + d)` by
    (`SUC (LOG2 j + d) = SUC (LOG2 j) + d` by Omega.OMEGA_TAC >>
     asm_rewrite_tac [EXP_ADD]) >>
  sym_tac >> MATCH_MP_TAC bitTheory.LOG2_UNIQUE >> simp []
QED

Theorem smtfp_jam_doubled_comparisons[local]:
  !(half : num) (scaled_half : num) (jr : num) (nr : num).
  (jr < half <=> nr < scaled_half) /\
  (jr = half <=> nr = scaled_half) ==>
  (2 * half < 2 * jr <=> 2 * scaled_half < 2 * nr) /\
  (2 * half = 2 * jr <=> 2 * scaled_half = 2 * nr) /\
  (2 * half <= 2 * jr <=> 2 * scaled_half <= 2 * nr)
Proof
  rpt strip_tac >> Omega.OMEGA_TAC
QED

Theorem smtfp_circuit_round_cong[local]:
  q1 = q2 /\ (r1 = 0 <=> r2 = 0) /\
  (d1 < 2 * r1 <=> d2 < 2 * r2) /\
  (d1 = 2 * r1 <=> d2 = 2 * r2) /\
  (d1 <= 2 * r1 <=> d2 <= 2 * r2) ==>
  smtfp_circuit_round mode sign q1 r1 d1 =
  smtfp_circuit_round mode sign q2 r2 d2
Proof
  strip_tac >> Cases_on `mode` >>
  simp_tac pure_ss [smtfp_circuit_round_def,
    smtfp_circuit_round_up_def] >>
  asm_rewrite_tac []
QED

Theorem smtfp_jam_round_components[local]:
  EVEN small /\ 0 < small /\ EVEN half /\
  small = 2 * half /\ big = small * 2 ** d ==>
  (smtfp_jam n d DIV small = n DIV big) /\
  (smtfp_jam n d MOD small = 0 <=> n MOD big = 0) /\
  (small < 2 * (smtfp_jam n d MOD small) <=>
   big < 2 * (n MOD big)) /\
  (small = 2 * (smtfp_jam n d MOD small) <=>
   big = 2 * (n MOD big)) /\
  (small <= 2 * (smtfp_jam n d MOD small) <=>
   big <= 2 * (n MOD big))
Proof
  strip_tac >>
  qabbrev_tac `jr : num = smtfp_jam n d MOD small` >>
  qabbrev_tac `nr : num = n MOD big` >>
  `smtfp_jam n d DIV small = n DIV big` by
    (qpat_x_assum `big = small * 2 ** d`
       (fn theorem => once_rewrite_tac [theorem]) >>
     MATCH_MP_TAC smtfp_jam_div >> simp []) >>
  `jr = 0 <=> nr = 0` by
    (simp_tac pure_ss [Abbr `jr`, Abbr `nr`] >>
     qpat_x_assum `big = small * 2 ** d`
       (fn theorem => once_rewrite_tac [theorem]) >>
     simp [smtfp_jam_mod_eq]) >>
  `jr < half <=> nr < half * 2 ** d` by
    (simp_tac pure_ss [Abbr `jr`, Abbr `nr`] >>
     qpat_x_assum `big = small * 2 ** d`
       (fn theorem => once_rewrite_tac [theorem]) >>
     MATCH_MP_TAC smtfp_jam_mod_lt >> simp []) >>
  `jr = half <=> nr = half * 2 ** d` by
    (simp_tac pure_ss [Abbr `jr`, Abbr `nr`] >>
     qpat_x_assum `big = small * 2 ** d`
       (fn theorem => once_rewrite_tac [theorem]) >>
     MATCH_MP_TAC smtfp_jam_mod_eq >> simp []) >>
  `big = 2 * (half * 2 ** d)` by
    (qpat_x_assum `big = small * 2 ** d`
       (fn theorem => once_rewrite_tac [theorem]) >>
     qpat_x_assum `small = 2 * half`
       (fn theorem => once_rewrite_tac [theorem]) >>
     REWRITE_TAC [MULT_ASSOC]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `big = 2 * (half * 2 ** d)`
    (fn theorem => REWRITE_TAC [theorem]) >>
  qpat_x_assum `small = 2 * half`
    (fn theorem => REWRITE_TAC [theorem]) >>
  MATCH_MP_TAC smtfp_jam_doubled_comparisons >>
  asm_rewrite_tac []
QED

Theorem smtfp_jam_round:
  2 <= k ==>
  smtfp_circuit_round mode sign
    (n DIV 2 ** (d + k)) (n MOD 2 ** (d + k)) (2 ** (d + k)) =
  smtfp_circuit_round mode sign
    (smtfp_jam n d DIV 2 ** k) (smtfp_jam n d MOD 2 ** k)
    (2 ** k)
Proof
  strip_tac >>
  qabbrev_tac `j : num = smtfp_jam n d` >>
  qabbrev_tac `big : num = 2 ** (d + k)` >>
  qabbrev_tac `small : num = 2 ** k` >>
  qabbrev_tac `half : num = 2 ** (k - 1)` >>
  `EVEN small /\ 0 < small /\ EVEN half` by
    simp [Abbr `small`, Abbr `half`, EVEN_EXP_IFF] >>
  `small = 2 * half` by
    (simp_tac pure_ss [Abbr `small`, Abbr `half`] >>
     Cases_on `k` >> fs [] >>
     Cases_on `n'` >> fs [EXP, MULT_COMM]) >>
  `big = small * 2 ** d` by
    (simp_tac pure_ss [Abbr `big`, Abbr `small`] >>
     once_rewrite_tac [EXP_ADD] >> MATCH_ACCEPT_TAC MULT_COMM) >>
  `(smtfp_jam n d DIV small = n DIV big) /\
   (smtfp_jam n d MOD small = 0 <=> n MOD big = 0) /\
   (small < 2 * (smtfp_jam n d MOD small) <=>
    big < 2 * (n MOD big)) /\
   (small = 2 * (smtfp_jam n d MOD small) <=>
    big = 2 * (n MOD big)) /\
   (small <= 2 * (smtfp_jam n d MOD small) <=>
    big <= 2 * (n MOD big))` by
    (MATCH_MP_TAC smtfp_jam_round_components >> asm_rewrite_tac []) >>
  simp_tac pure_ss [Abbr `j`] >>
  MATCH_MP_TAC smtfp_circuit_round_cong >>
  rpt conj_tac
  >- (sym_tac >> first_assum ACCEPT_TAC)
  >- (sym_tac >> first_assum ACCEPT_TAC)
  >- (sym_tac >> first_assum ACCEPT_TAC)
  >- (sym_tac >> first_assum ACCEPT_TAC)
  >- (sym_tac >> first_assum ACCEPT_TAC)
QED

Theorem num_divmod_multiple[local]:
  0 < p ==> q * p DIV p = q /\ q * p MOD p = 0
Proof
  strip_tac >> conj_tac
  >- (MATCH_MP_TAC DIV_UNIQUE >> qexists_tac `0` >> simp [])
  >- (MATCH_MP_TAC MOD_UNIQUE >> qexists_tac `q` >> simp [])
QED

Theorem smtfp_jam_even_sub_step[local]:
  EVEN a /\ q < a ==>
  a - q - 1 + (if EVEN (a - q - 1) then 1 else 0) =
  a - (q + if EVEN q then 1 else 0)
Proof
  strip_tac >>
  `q <= a /\ 1 <= a - q` by Omega.OMEGA_TAC >>
  Cases_on `EVEN q` >> fs [EVEN_SUB] >> Omega.OMEGA_TAC
QED

Theorem num_divmod_complement[local]:
  0 < p /\ r < p /\ r <> 0 /\ q * p + r <= a * p ==>
  q < a /\ p - r <> 0 /\
  a * p - (q * p + r) = (a - q - 1) * p + (p - r) /\
  ((a - q - 1) * p + (p - r)) DIV p = a - q - 1 /\
  ((a - q - 1) * p + (p - r)) MOD p = p - r
Proof
  strip_tac >>
  `q < a` by
    (CCONTR_TAC >>
     `a <= q` by Omega.OMEGA_TAC >>
     `a * p <= q * p` by simp [LE_MULT_RCANCEL] >>
     Omega.OMEGA_TAC) >>
  `0 < r /\ p - r < p /\ p - r <> 0` by Omega.OMEGA_TAC >>
  `a * p - (q * p + r) = (a - q - 1) * p + (p - r)` by
    (`?gap. a = q + (gap + 1)` by
       (MATCH_MP_TAC LESS_ADD_1 >> first_assum ACCEPT_TAC) >>
     pop_assum strip_assume_tac >>
     qpat_x_assum `a = q + (_ + 1)` SUBST_ALL_TAC >>
     simp [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB]) >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (MATCH_MP_TAC DIV_UNIQUE >> qexists_tac `p - r` >> simp [])
  >- (MATCH_MP_TAC MOD_UNIQUE >> qexists_tac `a - q - 1` >> simp [])
QED

Theorem smtfp_jam_even_sub:
  EVEN a /\ b <= a * 2 ** d ==>
  smtfp_jam (a * 2 ** d - b) d = a - smtfp_jam b d
Proof
  strip_tac >>
  qabbrev_tac `p : num = 2 ** d` >>
  `0 < p` by simp [Abbr `p`] >>
  `2 ** d = p` by simp [Abbr `p`] >>
  qpat_assum `2 ** d = p` (fn theorem => REWRITE_TAC [theorem]) >>
  drule DA >>
  disch_then (qspec_then `b` strip_assume_tac) >>
  qpat_x_assum `b = _` SUBST_ALL_TAC >>
  Cases_on `r = 0` >-
    (qpat_x_assum `r = 0` SUBST_ALL_TAC >>
     simp_tac pure_ss [smtfp_jam_def] >>
     qpat_assum `2 ** d = p`
       (fn theorem => REWRITE_TAC [theorem]) >>
     `q * p <= a * p` by Omega.OMEGA_TAC >>
     `q <= a` by fs [LE_MULT_RCANCEL] >>
     `a * p - q * p = (a - q) * p` by
       simp [RIGHT_SUB_DISTRIB] >>
     drule num_divmod_multiple >>
     disch_then (qspec_then `q` strip_assume_tac) >>
     drule num_divmod_multiple >>
     disch_then (qspec_then `a - q` strip_assume_tac) >>
     simp_tac pure_ss [LET_THM, ADD_CLAUSES] >>
     qpat_x_assum `a * p - q * p = (a - q) * p`
       (fn theorem => REWRITE_TAC [theorem]) >>
     asm_rewrite_tac [] >> simp []) >>
  `(q * p + r) DIV p = q /\ (q * p + r) MOD p = r` by
    (conj_tac
     >- (MATCH_MP_TAC DIV_UNIQUE >> qexists_tac `r` >> simp [])
     >- (MATCH_MP_TAC MOD_UNIQUE >> qexists_tac `q` >> simp [])) >>
  `q < a /\ p - r <> 0 /\
   a * p - (q * p + r) = (a - q - 1) * p + (p - r) /\
   ((a - q - 1) * p + (p - r)) DIV p = a - q - 1 /\
   ((a - q - 1) * p + (p - r)) MOD p = p - r` by
    (MATCH_MP_TAC num_divmod_complement >> simp []) >>
  simp_tac pure_ss [smtfp_jam_def] >>
  qpat_assum `2 ** d = p` (fn theorem => REWRITE_TAC [theorem]) >>
  asm_rewrite_tac [] >>
  simp_tac pure_ss [LET_THM] >> asm_rewrite_tac [] >>
  MATCH_MP_TAC smtfp_jam_even_sub_step >> simp []
QED

Theorem smtfp_circuit_exponents_cong[local]:
  bit$LOG2 m + scale = bit$LOG2 n + new_scale ==>
  smtfp_circuit_encoded_exponent maximum fraction_width scale m =
    smtfp_circuit_encoded_exponent maximum fraction_width new_scale n /\
  smtfp_circuit_effective_exponent maximum fraction_width scale m =
    smtfp_circuit_effective_exponent maximum fraction_width new_scale n
Proof
  strip_tac >>
  simp [smtfp_circuit_encoded_exponent_def,
    smtfp_circuit_effective_exponent_def,
    smtfp_circuit_wanted_exponent_def]
QED

Theorem smtfp_circuit_shift_jam_arithmetic[local]:
  (drop : num) + 2 <= (effective : num) - (scale : num) ==>
  scale <= effective /\ scale + drop <= effective /\
  effective - scale = drop + (effective - (scale + drop)) /\
  2 <= effective - (scale + drop)
Proof
  strip_tac >> Omega.OMEGA_TAC
QED

Theorem smtfp_circuit_rounded_jam[local]:
  scale <=
      smtfp_circuit_effective_exponent maximum fraction_width scale m /\
  scale + drop <=
      smtfp_circuit_effective_exponent maximum fraction_width
        (scale + drop) j /\
  smtfp_circuit_shift maximum fraction_width scale m =
    drop + smtfp_circuit_shift maximum fraction_width (scale + drop) j /\
  2 <= smtfp_circuit_shift maximum fraction_width (scale + drop) j /\
  j = smtfp_jam m drop ==>
  smtfp_circuit_rounded mode sign maximum fraction_width scale m =
  smtfp_circuit_rounded mode sign maximum fraction_width
    (scale + drop) j
Proof
  strip_tac >>
  simp_tac pure_ss [smtfp_circuit_rounded_def,
    smtfp_circuit_quotient_def, smtfp_circuit_remainder_def,
    smtfp_circuit_divisor_def, LET_THM] >>
  asm_rewrite_tac [] >>
  MATCH_MP_TAC smtfp_jam_round >> fs [ADD_COMM]
QED

Theorem smtfp_circuit_encode_jam:
  2 ** drop <= magnitude /\
  drop + 2 <= smtfp_circuit_shift (dimword (:'w) - 2)
    (dimindex (:'t)) scale magnitude ==>
  smtfp_circuit_encode mode (format : ('t,'w) smtfp)
    (sign : word1) scale magnitude =
  smtfp_circuit_encode mode format sign (scale + drop)
    (smtfp_jam magnitude drop)
Proof
  strip_tac >>
  qabbrev_tac `maximum : num = dimword (:'w) - 2` >>
  qabbrev_tac `fraction_width : num = dimindex (:'t)` >>
  qabbrev_tac `j : num = smtfp_jam magnitude drop` >>
  `0 < magnitude` by
    (MATCH_MP_TAC LESS_LESS_EQ_TRANS >> qexists_tac `2 ** drop` >>
     simp []) >>
  `magnitude <> 0 /\ j <> 0` by
    fs [Abbr `j`, smtfp_jam_eq_zero] >>
  `bit$LOG2 magnitude + scale =
   bit$LOG2 j + (scale + drop)` by
    (`bit$LOG2 j + drop = bit$LOG2 magnitude` by
       (simp_tac pure_ss [Abbr `j`] >>
        MATCH_MP_TAC smtfp_jam_log2 >> simp []) >>
     Omega.OMEGA_TAC) >>
  `smtfp_circuit_encoded_exponent maximum fraction_width scale magnitude =
     smtfp_circuit_encoded_exponent maximum fraction_width
       (scale + drop) j /\
   smtfp_circuit_effective_exponent maximum fraction_width scale magnitude =
     smtfp_circuit_effective_exponent maximum fraction_width
       (scale + drop) j` by
    (MATCH_MP_TAC smtfp_circuit_exponents_cong >> simp []) >>
  qabbrev_tac `effective : num =
    smtfp_circuit_effective_exponent maximum fraction_width scale
      magnitude` >>
  `scale <= effective /\ scale + drop <= effective /\
   effective - scale = drop + (effective - (scale + drop)) /\
   2 <= effective - (scale + drop)` by
    (MATCH_MP_TAC smtfp_circuit_shift_jam_arithmetic >>
     fs [Abbr `maximum`, Abbr `fraction_width`, Abbr `effective`,
       smtfp_circuit_shift_def]) >>
  `smtfp_circuit_rounded mode sign maximum fraction_width scale magnitude =
   smtfp_circuit_rounded mode sign maximum fraction_width
     (scale + drop) j` by
    (MATCH_MP_TAC smtfp_circuit_rounded_jam >>
     fs [Abbr `j`, Abbr `effective`, smtfp_circuit_shift_def]) >>
  simp_tac pure_ss [smtfp_circuit_encode_def, LET_THM] >>
  asm_rewrite_tac [] >>
  fs [Abbr `maximum`, Abbr `fraction_width`, Abbr `j`]
QED

Theorem num_sub_strict_lower[local]:
  (t : num) < l /\ 2 * l <= a ==> l < a - t
Proof
  strip_tac >> Omega.OMEGA_TAC
QED

Theorem num_double_product_mono[local]:
  (p : num) <= (s : num) ==> 2 * (p * (h : num)) <= s * (2 * h)
Proof
  strip_tac >>
  `2 * (p * h) = p * (2 * h)` by
    CONV_TAC (AC_CONV (MULT_ASSOC, MULT_COMM)) >>
  qpat_x_assum `2 * (p * h) = p * (2 * h)`
    (fn theorem => once_rewrite_tac [theorem]) >>
  `p * (2 * h) <= s * (2 * h)` by
    (MATCH_MP_TAC LESS_MONO_MULT >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Theorem smtfp_alignment_magnitude_lower:
  2 <= (gap : num) /\ 2 ** (f : num) <= (s : num) /\
  (t : num) < 2 ** (f + 1) ==>
  2 ** (f + gap - 1) < s * 2 ** gap - t /\
  2 ** (f + gap - 1) < s * 2 ** gap + t
Proof
  strip_tac >>
  qabbrev_tac `p : num = 2 ** f` >>
  qabbrev_tac `h : num = 2 ** (gap - 1)` >>
  qabbrev_tac `l : num = p * h` >>
  `2 <= h` by
    (simp_tac pure_ss [Abbr `h`] >>
     `1 <= gap - 1` by Omega.OMEGA_TAC >>
     fs [EXP_BASE_LE_MONO]) >>
  `2 ** (f + gap - 1) = l` by
    (simp_tac pure_ss [Abbr `l`, Abbr `p`, Abbr `h`] >>
     `f + gap - 1 = f + (gap - 1)` by Omega.OMEGA_TAC >>
     asm_rewrite_tac [EXP_ADD]) >>
  `2 ** gap = 2 * h` by
    (simp_tac pure_ss [Abbr `h`] >>
     Cases_on `gap` >> fs [] >>
     simp [EXP, MULT_COMM]) >>
  `t < 2 * p` by
    (`2 ** (f + 1) = 2 * p` by
       simp [Abbr `p`, EXP_ADD, EXP, MULT_COMM] >>
     qpat_x_assum `t < 2 ** (f + 1)` mp_tac >>
     qpat_x_assum `2 ** (f + 1) = 2 * p`
       (fn theorem => REWRITE_TAC [theorem])) >>
  `2 * p <= l` by
    fs [Abbr `l`, LE_MULT_LCANCEL] >>
  `t < l` by Omega.OMEGA_TAC >>
  `2 * l <= s * (2 * h)` by
    (simp_tac pure_ss [Abbr `l`] >>
     MATCH_MP_TAC num_double_product_mono >>
     fs [Abbr `p`]) >>
  conj_tac
  >- (qpat_x_assum `2 ** (f + gap - 1) = l`
        (fn theorem => REWRITE_TAC [theorem]) >>
      qpat_x_assum `2 ** gap = 2 * h`
        (fn theorem => REWRITE_TAC [theorem]) >>
      MATCH_MP_TAC num_sub_strict_lower >> simp [])
  >- (qpat_x_assum `2 ** (f + gap - 1) = l`
        (fn theorem => REWRITE_TAC [theorem]) >>
      qpat_x_assum `2 ** gap = 2 * h`
        (fn theorem => REWRITE_TAC [theorem]) >>
      Omega.OMEGA_TAC)
QED

Theorem smtfp_alignment_shift_lower:
  2 <= (gap : num) /\ 2 ** ((f : num) + gap - 1) < (magnitude : num) /\
  (low : num) + gap - 1 <= (maximum : num) ==>
  gap - 1 <= smtfp_circuit_shift maximum f low magnitude
Proof
  strip_tac >>
  `f + gap - 1 <= bit$LOG2 magnitude` by
    (MATCH_MP_TAC (CONJUNCT1 bitTheory.TWOEXP_LE_IMP_LE_LOG2) >>
     Omega.OMEGA_TAC) >>
  simp_tac pure_ss [smtfp_circuit_shift_def,
    smtfp_circuit_effective_exponent_def,
    smtfp_circuit_encoded_exponent_def,
    smtfp_circuit_wanted_exponent_def] >>
  rw [MIN_DEF, MAX_DEF] >> Omega.OMEGA_TAC
QED

Theorem smtfp_alignment_encode_ready[local]:
  4 <= (gap : num) /\
  2 ** ((f : num) + gap - 1) < (magnitude : num) /\
  (low : num) + gap - 1 <= (maximum : num) ==>
  2 ** (gap - 3) <= magnitude /\
  gap - 3 + 2 <= smtfp_circuit_shift maximum f low magnitude
Proof
  strip_tac >>
  `gap - 3 <= f + gap - 1` by Omega.OMEGA_TAC >>
  `2 ** (gap - 3) <= 2 ** (f + gap - 1)` by
    fs [EXP_BASE_LE_MONO] >>
  conj_tac
  >- (MATCH_MP_TAC LESS_EQ_TRANS >>
      qexists_tac `2 ** (f + gap - 1)` >> simp [])
  >- (`gap - 1 <= smtfp_circuit_shift maximum f low magnitude` by
        (MATCH_MP_TAC smtfp_alignment_shift_lower >> simp []) >>
      Omega.OMEGA_TAC)
QED

Theorem smtfp_alignment_power_split[local]:
  4 <= (gap : num) ==>
  (s : num) * 2 ** gap = (s * 8) * 2 ** (gap - 3)
Proof
  strip_tac >>
  `3 < gap` by Omega.OMEGA_TAC >>
  drule LESS_ADD_1 >> strip_tac >>
  qpat_x_assum `gap = 3 + (_ + 1)` SUBST_ALL_TAC >>
  simp [EXP_ADD]
QED

Theorem smtfp_circuit_encode_alignment_add:
  4 <= gap /\ 2 ** dimindex (:'t) <= s /\
  t < 2 ** (dimindex (:'t) + 1) /\
  low + gap - 1 <= dimword (:'w) - 2 ==>
  smtfp_circuit_encode mode (format : ('t,'w) smtfp)
    (sign : word1) low (s * 2 ** gap + t) =
  smtfp_circuit_encode mode format sign (low + (gap - 3))
    (s * 8 + smtfp_jam t (gap - 3))
Proof
  strip_tac >>
  `2 ** (dimindex (:'t) + gap - 1) < s * 2 ** gap - t /\
   2 ** (dimindex (:'t) + gap - 1) < s * 2 ** gap + t` by
    (MATCH_MP_TAC smtfp_alignment_magnitude_lower >> simp []) >>
  `2 ** (gap - 3) <= s * 2 ** gap + t /\
   gap - 3 + 2 <=
     smtfp_circuit_shift (dimword (:'w) - 2) (dimindex (:'t)) low
       (s * 2 ** gap + t)` by
    (MATCH_MP_TAC smtfp_alignment_encode_ready >> simp []) >>
  `smtfp_jam (s * 2 ** gap + t) (gap - 3) =
   s * 8 + smtfp_jam t (gap - 3)` by
    (`s * 2 ** gap = (s * 8) * 2 ** (gap - 3)` by
       (MATCH_MP_TAC smtfp_alignment_power_split >> simp []) >>
     qpat_x_assum `s * 2 ** gap = _`
       (fn theorem => once_rewrite_tac [theorem]) >>
     MATCH_MP_TAC smtfp_jam_even_add >>
     simp [EVEN_EXISTS] >> qexists_tac `s * 4` >> simp []) >>
  qpat_x_assum `smtfp_jam _ _ = _`
    (fn theorem => once_rewrite_tac [GSYM theorem]) >>
  MATCH_MP_TAC smtfp_circuit_encode_jam >> simp []
QED

Theorem smtfp_circuit_encode_alignment_sub:
  4 <= gap /\ 2 ** dimindex (:'t) <= s /\
  t < 2 ** (dimindex (:'t) + 1) /\
  low + gap - 1 <= dimword (:'w) - 2 ==>
  smtfp_circuit_encode mode (format : ('t,'w) smtfp)
    (sign : word1) low (s * 2 ** gap - t) =
  smtfp_circuit_encode mode format sign (low + (gap - 3))
    (s * 8 - smtfp_jam t (gap - 3))
Proof
  strip_tac >>
  `2 ** (dimindex (:'t) + gap - 1) < s * 2 ** gap - t /\
   2 ** (dimindex (:'t) + gap - 1) < s * 2 ** gap + t` by
    (MATCH_MP_TAC smtfp_alignment_magnitude_lower >> simp []) >>
  `2 ** (gap - 3) <= s * 2 ** gap - t /\
   gap - 3 + 2 <=
     smtfp_circuit_shift (dimword (:'w) - 2) (dimindex (:'t)) low
       (s * 2 ** gap - t)` by
    (MATCH_MP_TAC smtfp_alignment_encode_ready >> simp []) >>
  `t <= s * 2 ** gap` by Omega.OMEGA_TAC >>
  `smtfp_jam (s * 2 ** gap - t) (gap - 3) =
   s * 8 - smtfp_jam t (gap - 3)` by
    (`s * 2 ** gap = (s * 8) * 2 ** (gap - 3)` by
       (MATCH_MP_TAC smtfp_alignment_power_split >> simp []) >>
     `t <= (s * 8) * 2 ** (gap - 3)` by
       (qpat_x_assum `s * 2 ** gap = _`
          (fn theorem => once_rewrite_tac [GSYM theorem]) >>
        simp []) >>
     qpat_x_assum `s * 2 ** gap = _`
       (fn theorem => once_rewrite_tac [theorem]) >>
     MATCH_MP_TAC smtfp_jam_even_sub >>
     conj_tac
     >- (simp [EVEN_EXISTS] >> qexists_tac `s * 4` >> simp [])
     >- simp []) >>
  qpat_x_assum `smtfp_jam _ _ = _`
    (fn theorem => once_rewrite_tac [GSYM theorem]) >>
  MATCH_MP_TAC smtfp_circuit_encode_jam >> simp []
QED

Theorem num_product_strict_bound[local]:
  (a : num) < upper /\ (b : num) <= factor /\ 0 < factor ==>
  a * b < upper * factor
Proof
  strip_tac >>
  MATCH_MP_TAC LESS_EQ_LESS_TRANS >> qexists_tac `a * factor` >>
  conj_tac
  >- (once_rewrite_tac [MULT_COMM] >>
      MATCH_MP_TAC LESS_MONO_MULT >> simp [])
  >- fs [LT_MULT_RCANCEL]
QED

Theorem num_lt_scaled[local]:
  (a : num) < upper /\ 1 <= (factor : num) ==>
  a < upper * factor
Proof
  strip_tac >>
  MATCH_MP_TAC LESS_LESS_EQ_TRANS >> qexists_tac `upper` >>
  simp [LE_MULT_LCANCEL]
QED

Theorem num_sum_strict_double[local]:
  (a : num) < bound /\ (b : num) < bound ==>
  a + b < bound + bound
Proof
  strip_tac >> Omega.OMEGA_TAC
QED

Theorem num_two_power_succ[local]:
  (2 : num) ** (n + 1) = 2 ** n + 2 ** n
Proof
  `n + 1 = SUC n` by Omega.OMEGA_TAC >>
  qpat_x_assum `n + 1 = _`
    (fn theorem => once_rewrite_tac [theorem]) >>
  CONV_TAC (LAND_CONV (REWR_CONV (CONJUNCT2 EXP))) >>
  REWRITE_TAC [TIMES2]
QED

Theorem num_two_power_plus_five[local]:
  (2 : num) ** (f + 5) = 2 ** (f + 4) + 2 ** (f + 4)
Proof
  `f + 5 = (f + 4) + 1` by Omega.OMEGA_TAC >>
  qpat_x_assum `f + 5 = _`
    (fn theorem => once_rewrite_tac [theorem]) >>
  irule num_two_power_succ
QED

Theorem num_two_power_plus_four_times_eight[local]:
  (2 : num) ** (f + 1) * 8 = 2 ** (f + 4)
Proof
  simp_tac std_ss [EXP_ADD, EXP, MULT_ASSOC] >>
  once_rewrite_tac [GSYM MULT_ASSOC] >> simp []
QED

Theorem smtfp_alignment_individual_bounds[local]:
  (s : num) < 2 ** ((f : num) + 1) /\
  (t : num) < 2 ** (f + 1) ==>
  s * 2 ** MIN (gap : num) 3 < 2 ** (f + 4) /\
  smtfp_jam t (gap - 3) < 2 ** (f + 1)
Proof
  strip_tac >>
  `2 ** MIN gap 3 <= 8` by
    (`MIN gap 3 <= 3` by simp [] >>
     `2 ** MIN gap 3 <= 2 ** 3` by fs [EXP_BASE_LE_MONO] >>
     fs []) >>
  `s * 2 ** MIN gap 3 < 2 ** (f + 4)` by
    (`s * 2 ** MIN gap 3 < 2 ** (f + 1) * 8` by
       (MATCH_MP_TAC num_product_strict_bound >> simp []) >>
     `(2 : num) ** (f + 1) * 8 = (2 : num) ** (f + 4)` by
       MATCH_ACCEPT_TAC num_two_power_plus_four_times_eight >>
     qpat_x_assum `(2 : num) ** (f + 1) * 8 = _`
       (fn theorem => once_rewrite_tac [GSYM theorem]) >>
     first_assum ACCEPT_TAC) >>
  `EVEN ((2 : num) ** (f + 1))` by
    (simp [EXP_ADD, EVEN_EXISTS] >>
     qexists_tac `2 ** f` >> simp [MULT_COMM]) >>
  `smtfp_jam t (gap - 3) < 2 ** (f + 1)` by
    (`smtfp_jam t (gap - 3) < 2 ** (f + 1) <=>
      t < 2 ** (f + 1) * 2 ** (gap - 3)` by
       (MATCH_MP_TAC smtfp_jam_even_lt >> simp []) >>
     qpat_x_assum `smtfp_jam _ _ < _ <=> _`
       (fn theorem => once_rewrite_tac [theorem]) >>
     MATCH_MP_TAC num_lt_scaled >> simp []) >>
  simp []
QED

Theorem smtfp_alignment_retained_bounds:
  (s : num) < 2 ** ((f : num) + 1) /\
  (t : num) < 2 ** (f + 1) ==>
  s * 2 ** MIN (gap : num) 3 < 2 ** (f + 4) /\
  smtfp_jam t (gap - 3) < 2 ** (f + 1) /\
  s * 2 ** MIN gap 3 + smtfp_jam t (gap - 3) <
    2 ** (f + 5) /\
  s * 2 ** MIN gap 3 - smtfp_jam t (gap - 3) <
    2 ** (f + 4)
Proof
  strip_tac >>
  `s * 2 ** MIN gap 3 < 2 ** (f + 4) /\
   smtfp_jam t (gap - 3) < 2 ** (f + 1)` by
    (MATCH_MP_TAC smtfp_alignment_individual_bounds >> simp []) >>
  `2 ** (f + 1) <= 2 ** (f + 4)` by
    (`f + 1 <= f + 4` by Omega.OMEGA_TAC >>
     fs [EXP_BASE_LE_MONO]) >>
  `smtfp_jam t (gap - 3) < 2 ** (f + 4)` by
    (MATCH_MP_TAC LESS_LESS_EQ_TRANS >>
     qexists_tac `2 ** (f + 1)` >> simp []) >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (`s * 2 ** MIN gap 3 + smtfp_jam t (gap - 3) <
       2 ** (f + 4) + 2 ** (f + 4)` by
        (MATCH_MP_TAC num_sum_strict_double >> simp []) >>
      `(2 : num) ** (f + 5) =
       (2 : num) ** (f + 4) + (2 : num) ** (f + 4)` by
        irule num_two_power_plus_five >>
      qpat_x_assum `(2 : num) ** (f + 5) = _`
        (fn theorem => once_rewrite_tac [theorem]) >>
      first_assum ACCEPT_TAC)
  >- Omega.OMEGA_TAC
QED

Definition smtfp_bounded_align_def:
  smtfp_bounded_align retained_scale exponent significand =
    if retained_scale <= exponent then
      significand * 2 ** (exponent - retained_scale)
    else smtfp_jam significand (retained_scale - exponent)
End

Definition smtfp_bounded_addsub_trace_def:
  smtfp_bounded_addsub_trace subtract (x : ('t,'w) smtfp)
      (y : ('t,'w) smtfp) =
    let xr = smtfp_rep x in
    let yr = smtfp_rep y in
    let xe = smtfp_circuit_exp xr.Exponent in
    let ye = smtfp_circuit_exp yr.Exponent in
    let low = MIN xe ye in
    let gap = MAX xe ye - low in
    let scale = low + (gap - 3) in
    let xa = smtfp_bounded_align scale xe
      (smtfp_circuit_sig xr.Exponent xr.Significand) in
    let ya = smtfp_bounded_align scale ye
      (smtfp_circuit_sig yr.Exponent yr.Significand) in
    let ys = if subtract then ~yr.Sign else yr.Sign in
    let sign = if xr.Sign = ys \/ ya <= xa then xr.Sign else ys in
    let magnitude =
      if xr.Sign = ys then xa + ya
      else if ya <= xa then xa - ya else ya - xa
    in
      (scale, xa, ya, sign, magnitude)
End

Definition smtfp_bounded_addsub_circuit_def:
  smtfp_bounded_addsub_circuit subtract mode (x : ('t,'w) smtfp) y =
    let xr = smtfp_rep x in
    let yr = smtfp_rep y in
    let ys = if subtract then ~yr.Sign else yr.Sign in
    if xr.Exponent = UINT_MAXw /\ xr.Significand <> 0w \/
       yr.Exponent = UINT_MAXw /\ yr.Significand <> 0w then
      smtfp_nan
    else if xr.Exponent = UINT_MAXw /\ yr.Exponent = UINT_MAXw then
      if xr.Sign = ys then smtfp_circuit_infinity x xr.Sign else smtfp_nan
    else if xr.Exponent = UINT_MAXw then
      smtfp_circuit_infinity x xr.Sign
    else if yr.Exponent = UINT_MAXw then
      smtfp_circuit_infinity x ys
    else
      let (scale, xa, ya, sign, magnitude) =
        smtfp_bounded_addsub_trace subtract x y in
      if yr.Exponent = 0w /\ yr.Significand = 0w /\ magnitude <> 0 then x
      else
        let sign = if magnitude = 0 then
                     smtfp_addsub_zero_sign subtract mode x y
                   else sign
        in smtfp_circuit_encode mode x sign scale magnitude
End

Definition smtfp_pair_trace_def:
  smtfp_pair_trace (scale : num) (xa : num) (ya : num)
      (sx : word1) sy =
    let sign = if sx = sy \/ ya <= xa then sx else sy in
    let magnitude =
      if sx = sy then xa + ya
      else if ya <= xa then xa - ya else ya - xa
    in (scale, xa, ya, sign, magnitude)
End

Theorem smtfp_bounded_align_exact:
  (retained_scale : num) <= exponent ==>
  smtfp_bounded_align retained_scale exponent significand =
  significand * 2 ** (exponent - retained_scale)
Proof
  simp [smtfp_bounded_align_def]
QED

Theorem smtfp_bounded_addsub_trace_small_gap:
  MAX (smtfp_circuit_exp (smtfp_rep x).Exponent)
      (smtfp_circuit_exp (smtfp_rep y).Exponent) -
    MIN (smtfp_circuit_exp (smtfp_rep x).Exponent)
      (smtfp_circuit_exp (smtfp_rep y).Exponent) <= 3 ==>
  smtfp_bounded_addsub_trace subtract (x : ('t,'w) smtfp) y =
  smtfp_addsub_trace subtract x y
Proof
  strip_tac >>
  simp_tac pure_ss [smtfp_bounded_addsub_trace_def,
    smtfp_addsub_trace_def, LET_THM] >>
  `MAX (smtfp_circuit_exp (smtfp_rep x).Exponent)
       (smtfp_circuit_exp (smtfp_rep y).Exponent) -
     MIN (smtfp_circuit_exp (smtfp_rep x).Exponent)
       (smtfp_circuit_exp (smtfp_rep y).Exponent) - 3 = 0` by
    Omega.OMEGA_TAC >>
  asm_rewrite_tac [ADD_CLAUSES] >>
  simp [smtfp_bounded_align_def, MIN_LE]
QED

Theorem smtfp_addsub_trace_pair[local]:
  smtfp_addsub_trace subtract (x : ('t,'w) smtfp) y =
  let xe = smtfp_circuit_exp (smtfp_rep x).Exponent in
  let ye = smtfp_circuit_exp (smtfp_rep y).Exponent in
  let low = MIN xe ye in
  smtfp_pair_trace low
    (smtfp_circuit_sig (smtfp_rep x).Exponent
       (smtfp_rep x).Significand * 2 ** (xe - low))
    (smtfp_circuit_sig (smtfp_rep y).Exponent
       (smtfp_rep y).Significand * 2 ** (ye - low))
    (smtfp_rep x).Sign
    (if subtract then ~(smtfp_rep y).Sign else (smtfp_rep y).Sign)
Proof
  simp [smtfp_addsub_trace_def, smtfp_pair_trace_def]
QED

Theorem smtfp_bounded_addsub_trace_pair[local]:
  smtfp_bounded_addsub_trace subtract (x : ('t,'w) smtfp) y =
  let xe = smtfp_circuit_exp (smtfp_rep x).Exponent in
  let ye = smtfp_circuit_exp (smtfp_rep y).Exponent in
  let low = MIN xe ye in
  let gap = MAX xe ye - low in
  let scale = low + (gap - 3) in
  smtfp_pair_trace scale
    (smtfp_bounded_align scale xe
      (smtfp_circuit_sig (smtfp_rep x).Exponent
        (smtfp_rep x).Significand))
    (smtfp_bounded_align scale ye
      (smtfp_circuit_sig (smtfp_rep y).Exponent
        (smtfp_rep y).Significand))
    (smtfp_rep x).Sign
    (if subtract then ~(smtfp_rep y).Sign else (smtfp_rep y).Sign)
Proof
  simp [smtfp_bounded_addsub_trace_def, smtfp_pair_trace_def]
QED

Theorem smtfp_gap_minmax[local]:
  4 <= (gap : num) ==>
  MIN (low + gap) low = low /\ MAX (low + gap) low = low + gap /\
  MIN low (low + gap) = low /\ MAX low (low + gap) = low + gap
Proof
  rw [MIN_DEF, MAX_DEF] >> Omega.OMEGA_TAC
QED

Theorem smtfp_gap_arithmetic[local]:
  4 <= (gap : num) ==>
  low + gap - low = gap /\ low - low = 0 /\
  low + gap - low - 3 = gap - 3 /\
  low + (low + gap - low - 3) = low + (gap - 3)
Proof
  strip_tac >> Omega.OMEGA_TAC
QED

Theorem smtfp_finite_circuit_exp_bound[local]:
  2 <= dimindex (:'w) /\ (e : 'w word) <> UINT_MAXw ==>
  smtfp_circuit_exp e <= dimword (:'w) - 2
Proof
  strip_tac >> Cases_on `e = 0w`
  >- (`4 <= dimword (:'w)` by
        (simp [wordsTheory.dimword_def] >>
         MATCH_MP_TAC LESS_EQ_TRANS >> qexists_tac `2 ** 2` >>
         simp [EXP_BASE_LE_MONO]) >>
      simp [smtfp_circuit_exp_def])
  >- (`w2n e < dimword (:'w)` by
        MATCH_ACCEPT_TAC wordsTheory.w2n_lt >>
      Cases_on `w2n e < dimword (:'w) - 1`
      >- (simp [smtfp_circuit_exp_def] >> Omega.OMEGA_TAC) >>
      `dimword (:'w) - 1 <= w2n e` by fs [GSYM NOT_LESS] >>
      `w2n e = dimword (:'w) - 1` by Omega.OMEGA_TAC >>
      `w2n (UINT_MAXw : 'w word) = dimword (:'w) - 1` by
        simp [wordsTheory.w2n_minus1, wordsTheory.UINT_MAX_def] >>
      `w2n e = w2n (UINT_MAXw : 'w word)` by asm_rewrite_tac [] >>
      `e = (UINT_MAXw : 'w word)` by
        metis_tac [wordsTheory.w2n_11] >>
      fs [] >>
      simp [smtfp_circuit_exp_def] >> Omega.OMEGA_TAC)
QED

Theorem smtfp_normal_circuit_sig_lower[local]:
  (e : 'w word) <> 0w ==>
  2 ** dimindex (:'t) <= smtfp_circuit_sig e (m : 't word)
Proof
  simp [smtfp_circuit_sig_def]
QED

Theorem smtfp_alignment_ordered_pair[local]:
  4 <= (gap : num) /\ 2 ** (f : num) <= (s : num) /\
  (t : num) < 2 ** (f + 1) ==>
  t < s * 2 ** gap /\
  smtfp_jam t (gap - 3) < s * 8
Proof
  strip_tac >>
  `2 ** (f + gap - 1) < s * 2 ** gap - t /\
   2 ** (f + gap - 1) < s * 2 ** gap + t` by
    (MATCH_MP_TAC smtfp_alignment_magnitude_lower >> simp []) >>
  `smtfp_jam t (gap - 3) < 2 ** (f + 1)` by
    (`EVEN ((2 : num) ** (f + 1))` by simp [EVEN_EXP_IFF] >>
     simp [smtfp_jam_even_lt] >>
     MATCH_MP_TAC num_lt_scaled >> simp []) >>
  `2 ** (f + 3 - 1) < s * 2 ** 3 - smtfp_jam t (gap - 3) /\
   2 ** (f + 3 - 1) < s * 2 ** 3 + smtfp_jam t (gap - 3)` by
    (MATCH_MP_TAC smtfp_alignment_magnitude_lower >> simp []) >>
  `0 < 2 ** (f + gap - 1) /\ 0 < 2 ** (f + 3 - 1)` by simp [] >>
  conj_tac
  >- Omega.OMEGA_TAC
  >- (fs [] >> Omega.OMEGA_TAC)
QED

Theorem smtfp_bounded_align_ordered[local]:
  4 <= (gap : num) ==>
  smtfp_bounded_align (low + (gap - 3)) (low + gap) s = s * 8 /\
  smtfp_bounded_align (low + (gap - 3)) low t =
    smtfp_jam t (gap - 3)
Proof
  strip_tac >> simp_tac pure_ss [smtfp_bounded_align_def] >>
  `low + gap - (low + (gap - 3)) = 3 /\
   ~(low + (gap - 3) <= low) /\
   low + (gap - 3) - low = gap - 3` by Omega.OMEGA_TAC >>
  asm_rewrite_tac [] >> simp []
QED

Theorem smtfp_pair_trace_ordered_refinement[local]:
  (t : num) < a /\ tj < aj /\
  smtfp_circuit_encode mode (format : ('t,'w) smtfp)
      (high_sign : word1) low (a + t) =
    smtfp_circuit_encode mode format high_sign scale (aj + tj) /\
  smtfp_circuit_encode mode format high_sign low (a - t) =
    smtfp_circuit_encode mode format high_sign scale (aj - tj) ==>
  case smtfp_pair_trace low
      (if high_first then a else t) (if high_first then t else a)
      (if high_first then high_sign else low_sign)
      (if high_first then low_sign else high_sign) of
    (s,x,y,sg,m) =>
      case smtfp_pair_trace scale
          (if high_first then aj else tj) (if high_first then tj else aj)
          (if high_first then high_sign else low_sign)
          (if high_first then low_sign else high_sign) of
        (bs,bx,by,bsg,bm) => sg = bsg /\ (m = 0 <=> bm = 0) /\
          smtfp_circuit_encode mode format sg s m =
            smtfp_circuit_encode mode format bsg bs bm
Proof
  strip_tac >> simp_tac pure_ss [smtfp_pair_trace_def, LET_THM,
    pairTheory.pair_case_thm] >>
  Cases_on `high_first` >> Cases_on `high_sign = low_sign` >>
  fs [] >> Omega.OMEGA_TAC
QED

Theorem smtfp_ordered_field_bounds[local]:
  2 <= dimindex (:'w) /\ (high_e : 'w word) <> UINT_MAXw /\
  4 <= smtfp_circuit_exp high_e - smtfp_circuit_exp low_e ==>
  2 ** dimindex (:'t) <= smtfp_circuit_sig high_e (high_m : 't word) /\
  smtfp_circuit_sig low_e (low_m : 't word) <
    2 ** (dimindex (:'t) + 1) /\
  smtfp_circuit_exp low_e +
      (smtfp_circuit_exp high_e - smtfp_circuit_exp low_e) - 1 <=
    dimword (:'w) - 2
Proof
  strip_tac >>
  `high_e <> 0w` by
    (strip_tac >> Cases_on `low_e = 0w` >>
     fs [smtfp_circuit_exp_def, wordsTheory.w2n_eq_0] >>
     Omega.OMEGA_TAC) >>
  `smtfp_circuit_exp high_e <= dimword (:'w) - 2` by
    (MATCH_MP_TAC smtfp_finite_circuit_exp_bound >> simp []) >>
  `smtfp_circuit_sig low_e low_m < 2 * 2 ** dimindex (:'t)` by
    MATCH_ACCEPT_TAC smtfp_circuit_sig_bound >>
  rpt conj_tac
  >- (MATCH_MP_TAC smtfp_normal_circuit_sig_lower >> simp [])
  >- fs [EXP_ADD]
  >- Omega.OMEGA_TAC
QED

Theorem smtfp_bounded_trace_x_high[local]:
  2 <= dimindex (:'w) /\ (smtfp_rep x).Exponent <> UINT_MAXw /\
  (smtfp_rep y).Exponent <> UINT_MAXw /\
  4 <= smtfp_circuit_exp (smtfp_rep x).Exponent -
    smtfp_circuit_exp (smtfp_rep y).Exponent ==>
  case smtfp_addsub_trace subtract (x : ('t,'w) smtfp) y of
    (s,xa,ya,sg,m) => case smtfp_bounded_addsub_trace subtract x y of
      (bs,bxa,bya,bsg,bm) => sg = bsg /\ (m = 0 <=> bm = 0) /\
      smtfp_circuit_encode mode x sg s m =
        smtfp_circuit_encode mode x bsg bs bm
Proof
  rpt strip_tac >>
  qabbrev_tac `gap = smtfp_circuit_exp (smtfp_rep x).Exponent -
    smtfp_circuit_exp (smtfp_rep y).Exponent` >>
  qabbrev_tac `xs = smtfp_circuit_sig (smtfp_rep x).Exponent
    (smtfp_rep x).Significand` >>
  qabbrev_tac `ys = smtfp_circuit_sig (smtfp_rep y).Exponent
    (smtfp_rep y).Significand` >>
  `4 <= gap` by fs [Abbr `gap`] >>
  `2 ** dimindex (:'t) <= xs /\ ys < 2 ** (dimindex (:'t) + 1) /\
  smtfp_circuit_exp (smtfp_rep y).Exponent + gap - 1 <=
     dimword (:'w) - 2` by
    (simp_tac pure_ss [Abbr `gap`, Abbr `xs`, Abbr `ys`] >>
     MATCH_MP_TAC smtfp_ordered_field_bounds >> simp []) >>
  pop_assum strip_assume_tac >>
  `ys < xs * 2 ** gap /\ smtfp_jam ys (gap - 3) < xs * 8` by
    (MATCH_MP_TAC (Q.INST [`f` |-> `dimindex (:'t)`]
       smtfp_alignment_ordered_pair) >> simp []) >>
  `smtfp_circuit_exp (smtfp_rep x).Exponent =
   smtfp_circuit_exp (smtfp_rep y).Exponent + gap` by
    (simp_tac pure_ss [Abbr `gap`] >> Omega.OMEGA_TAC) >>
  simp_tac pure_ss [smtfp_addsub_trace_pair,
    smtfp_bounded_addsub_trace_pair, LET_THM] >>
  asm_simp_tac std_ss [smtfp_gap_minmax,
    smtfp_gap_arithmetic, smtfp_bounded_align_ordered] >>
  MATCH_MP_TAC (SIMP_RULE bool_ss []
    (Q.INST [`high_first` |-> `T`]
      smtfp_pair_trace_ordered_refinement)) >>
  fs [Abbr `xs`, Abbr `ys`, smtfp_circuit_encode_alignment_add,
    smtfp_circuit_encode_alignment_sub]
QED

Theorem smtfp_bounded_trace_y_high[local]:
  2 <= dimindex (:'w) /\ (smtfp_rep x).Exponent <> UINT_MAXw /\
  (smtfp_rep y).Exponent <> UINT_MAXw /\
  4 <= smtfp_circuit_exp (smtfp_rep y).Exponent -
    smtfp_circuit_exp (smtfp_rep x).Exponent ==>
  case smtfp_addsub_trace subtract (x : ('t,'w) smtfp) y of
    (s,xa,ya,sg,m) => case smtfp_bounded_addsub_trace subtract x y of
      (bs,bxa,bya,bsg,bm) => sg = bsg /\ (m = 0 <=> bm = 0) /\
      smtfp_circuit_encode mode x sg s m =
        smtfp_circuit_encode mode x bsg bs bm
Proof
  rpt strip_tac >>
  qabbrev_tac `gap = smtfp_circuit_exp (smtfp_rep y).Exponent -
    smtfp_circuit_exp (smtfp_rep x).Exponent` >>
  qabbrev_tac `ys = smtfp_circuit_sig (smtfp_rep y).Exponent
    (smtfp_rep y).Significand` >>
  qabbrev_tac `xs = smtfp_circuit_sig (smtfp_rep x).Exponent
    (smtfp_rep x).Significand` >>
  qabbrev_tac `ysign = if subtract then ~(smtfp_rep y).Sign
    else (smtfp_rep y).Sign` >>
  `4 <= gap` by fs [Abbr `gap`] >>
  `2 ** dimindex (:'t) <= ys /\ xs < 2 ** (dimindex (:'t) + 1) /\
  smtfp_circuit_exp (smtfp_rep x).Exponent + gap - 1 <=
     dimword (:'w) - 2` by
    (simp_tac pure_ss [Abbr `gap`, Abbr `ys`, Abbr `xs`] >>
     MATCH_MP_TAC smtfp_ordered_field_bounds >> simp []) >>
  pop_assum strip_assume_tac >>
  `xs < ys * 2 ** gap /\ smtfp_jam xs (gap - 3) < ys * 8` by
    (MATCH_MP_TAC (Q.INST [`f` |-> `dimindex (:'t)`]
       smtfp_alignment_ordered_pair) >> simp []) >>
  `smtfp_circuit_exp (smtfp_rep y).Exponent =
   smtfp_circuit_exp (smtfp_rep x).Exponent + gap` by
    (simp_tac pure_ss [Abbr `gap`] >> Omega.OMEGA_TAC) >>
  simp_tac pure_ss [smtfp_addsub_trace_pair,
    smtfp_bounded_addsub_trace_pair, LET_THM] >>
  asm_simp_tac std_ss [smtfp_gap_minmax,
    smtfp_gap_arithmetic, smtfp_bounded_align_ordered] >>
  MATCH_MP_TAC (SIMP_RULE bool_ss []
    (Q.INST [`high_first` |-> `F`]
      smtfp_pair_trace_ordered_refinement)) >>
  fs [Abbr `ys`, Abbr `xs`, Abbr `ysign`,
    smtfp_circuit_encode_alignment_add,
    smtfp_circuit_encode_alignment_sub, ADD_COMM]
QED

Theorem smtfp_bounded_addsub_trace_correspondence:
  2 <= dimindex (:'w) /\ (smtfp_rep x).Exponent <> UINT_MAXw /\
  (smtfp_rep y).Exponent <> UINT_MAXw ==>
  case smtfp_addsub_trace subtract (x : ('t,'w) smtfp) y of
    (s,xa,ya,sg,m) => case smtfp_bounded_addsub_trace subtract x y of
      (bs,bxa,bya,bsg,bm) => sg = bsg /\ (m = 0 <=> bm = 0) /\
      smtfp_circuit_encode mode x sg s m =
        smtfp_circuit_encode mode x bsg bs bm
Proof
  rpt strip_tac >>
  qabbrev_tac `gap = MAX (smtfp_circuit_exp (smtfp_rep x).Exponent)
    (smtfp_circuit_exp (smtfp_rep y).Exponent) -
    MIN (smtfp_circuit_exp (smtfp_rep x).Exponent)
      (smtfp_circuit_exp (smtfp_rep y).Exponent)` >>
  Cases_on `gap <= 3`
  >- (`smtfp_bounded_addsub_trace subtract x y =
       smtfp_addsub_trace subtract x y` by
        (MATCH_MP_TAC smtfp_bounded_addsub_trace_small_gap >>
         fs [Abbr `gap`]) >>
      asm_rewrite_tac [] >>
      qabbrev_tac `tr = smtfp_addsub_trace subtract x y` >>
      PairCases_on `tr` >> gvs []) >>
  Cases_on `smtfp_circuit_exp (smtfp_rep y).Exponent <=
    smtfp_circuit_exp (smtfp_rep x).Exponent`
  >- (MATCH_MP_TAC smtfp_bounded_trace_x_high >>
      fs [Abbr `gap`, MIN_DEF, MAX_DEF] >> Omega.OMEGA_TAC)
  >- (MATCH_MP_TAC smtfp_bounded_trace_y_high >>
      fs [Abbr `gap`, MIN_DEF, MAX_DEF] >> Omega.OMEGA_TAC)
QED

Theorem smtfp_trace_result_refinement[local]:
  (case exact_trace of (s,xa,ya,sg,m) =>
     case bounded_trace of (bs,bxa,bya,bsg,bm) =>
       sg = bsg /\ (m = 0 <=> bm = 0) /\
       smtfp_circuit_encode mode (format : ('t,'w) smtfp) sg s m =
         smtfp_circuit_encode mode format bsg bs bm) ==>
  (\(bs,bxa,bya,bsg,bm).
     if right_zero /\ bm <> 0 then fallback
     else smtfp_circuit_encode mode format
       (if bm = 0 then zero_sign else bsg) bs bm) bounded_trace =
  (\(s,xa,ya,sg,m).
     if right_zero /\ m <> 0 then fallback
     else smtfp_circuit_encode mode format
       (if m = 0 then zero_sign else sg) s m) exact_trace
Proof
  strip_tac >> PairCases_on `exact_trace` >>
  PairCases_on `bounded_trace` >>
  Cases_on `bounded_trace4 = 0` >> Cases_on `right_zero` >> fs [] >>
  qpat_x_assum `exact_trace3 = bounded_trace3` SUBST_ALL_TAC >>
  sym_tac >> first_assum ACCEPT_TAC
QED

Theorem smtfp_bounded_addsub_circuit_eq:
  2 <= dimindex (:'w) ==>
  smtfp_bounded_addsub_circuit subtract mode
      (x : ('t,'w) smtfp) y =
    SND (smtfp_addsub_circuit subtract mode x y)
Proof
  strip_tac >>
  Cases_on `(smtfp_rep x).Exponent = UINT_MAXw` >>
  Cases_on `(smtfp_rep y).Exponent = UINT_MAXw` >>
  simp [smtfp_bounded_addsub_circuit_def, smtfp_addsub_circuit_def] >>
  simp_tac pure_ss [CONJ_ASSOC] >>
  MATCH_MP_TAC smtfp_trace_result_refinement >>
  MATCH_MP_TAC smtfp_bounded_addsub_trace_correspondence >> simp []
QED

Theorem smtfp_bounded_addsub_circuit_correspondence:
  2 <= dimindex (:'w) ==>
  (if subtract then smtfp_sub mode x y else smtfp_add mode x y) =
  smtfp_bounded_addsub_circuit subtract mode (x : ('t,'w) smtfp) y
Proof
  metis_tac [smtfp_addsub_circuit_correspondence,
    smtfp_bounded_addsub_circuit_eq]
QED

Theorem smtfp_retained_scale_bounds[local]:
  0 < (xe : num) /\ 0 < (ye : num) ==>
  let low = MIN xe ye in
  let gap = MAX xe ye - low in
  let scale = low + (gap - 3) in
    0 < scale /\ scale <= MAX xe ye /\
    xe <= scale + 3 /\ ye <= scale + 3
Proof
  rw [MIN_DEF, MAX_DEF] >> Omega.OMEGA_TAC
QED

Theorem smtfp_bounded_align_bound[local]:
  exponent <= retained_scale + 3 /\
  significand < 2 ** ((f : num) + 1) ==>
  smtfp_bounded_align retained_scale exponent significand <
    2 ** (f + 4)
Proof
  strip_tac >> Cases_on `retained_scale <= exponent`
  >- (simp_tac pure_ss [smtfp_bounded_align_def] >>
      asm_rewrite_tac [] >>
      `exponent - retained_scale <= 3` by Omega.OMEGA_TAC >>
      `2 ** (exponent - retained_scale) <= 8` by
        (`2 ** (exponent - retained_scale) <= (2 : num) ** 3` by
           fs [EXP_BASE_LE_MONO] >> fs []) >>
      `significand * 2 ** (exponent - retained_scale) <
       2 ** (f + 1) * 8` by
        (MATCH_MP_TAC num_product_strict_bound >> simp []) >>
      `(2 : num) ** (f + 1) * 8 = 2 ** (f + 4)` by
        MATCH_ACCEPT_TAC num_two_power_plus_four_times_eight >>
      qpat_x_assum `(2 : num) ** (f + 1) * 8 = _`
        (fn theorem => once_rewrite_tac [GSYM theorem]) >>
      first_assum ACCEPT_TAC)
  >- (simp_tac pure_ss [smtfp_bounded_align_def] >>
      asm_rewrite_tac [] >>
      `smtfp_jam significand (retained_scale - exponent) <
       2 ** (f + 1)` by
        (`EVEN ((2 : num) ** (f + 1))` by simp [EVEN_EXP_IFF] >>
         simp [smtfp_jam_even_lt] >>
         MATCH_MP_TAC num_lt_scaled >> simp []) >>
      `2 ** (f + 1) <= (2 : num) ** (f + 4)` by
        fs [EXP_BASE_LE_MONO] >>
      Omega.OMEGA_TAC)
QED

Theorem smtfp_circuit_sig_power_bound[local]:
  smtfp_circuit_sig e (m : 't word) < 2 ** (dimindex (:'t) + 1)
Proof
  `smtfp_circuit_sig e m < 2 * 2 ** dimindex (:'t)` by
    MATCH_ACCEPT_TAC smtfp_circuit_sig_bound >>
  fs [EXP_ADD, MULT_COMM]
QED

Theorem smtfp_pair_trace_bounds[local]:
  xa < 2 ** ((f : num) + 4) /\ ya < 2 ** (f + 4) ==>
  case smtfp_pair_trace scale xa ya sx sy of (s,x,y,sg,m) =>
    x < 2 ** (f + 4) /\ y < 2 ** (f + 4) /\ m < 2 ** (f + 5)
Proof
  strip_tac >>
  `xa + ya < 2 ** (f + 5)` by
    (`xa + ya < 2 ** (f + 4) + 2 ** (f + 4)` by
       (MATCH_MP_TAC num_sum_strict_double >> simp []) >>
     fs [num_two_power_plus_five]) >>
  `2 ** (f + 4) < (2 : num) ** (f + 5)` by
    simp [EXP_BASE_LT_MONO] >>
  simp_tac pure_ss [smtfp_pair_trace_def, LET_THM,
    pairTheory.pair_case_thm] >>
  Cases_on `sx = sy` >> Cases_on `ya <= xa` >> fs [] >>
  TRY (qpat_x_assum `sx <> sy` kall_tac) >>
  TRY (qpat_x_assum `sx = sy` kall_tac) >> Omega.OMEGA_TAC
QED

Theorem smtfp_bounded_addsub_trace_bounds:
  case smtfp_bounded_addsub_trace subtract
      (x : ('t,'w) smtfp) y of (scale,xa,ya,sign,magnitude) =>
    xa < 2 ** (dimindex (:'t) + 4) /\
    ya < 2 ** (dimindex (:'t) + 4) /\
    magnitude < 2 ** (dimindex (:'t) + 5)
Proof
  qabbrev_tac `xe = smtfp_circuit_exp (smtfp_rep x).Exponent` >>
  qabbrev_tac `ye = smtfp_circuit_exp (smtfp_rep y).Exponent` >>
  qabbrev_tac `scale = MIN xe ye + (MAX xe ye - MIN xe ye - 3)` >>
  `xe <= scale + 3 /\ ye <= scale + 3` by
    (mp_tac (Q.INST [`xe` |-> `xe`, `ye` |-> `ye`]
       smtfp_retained_scale_bounds) >>
     simp_tac std_ss [LET_THM] >>
     impl_tac >- simp [Abbr `xe`, Abbr `ye`] >>
     fs [Abbr `scale`]) >>
  `smtfp_circuit_sig (smtfp_rep x).Exponent
       (smtfp_rep x).Significand < 2 ** (dimindex (:'t) + 1)` by
    irule smtfp_circuit_sig_power_bound >>
  `smtfp_circuit_sig (smtfp_rep y).Exponent
       (smtfp_rep y).Significand < 2 ** (dimindex (:'t) + 1)` by
    irule smtfp_circuit_sig_power_bound >>
  simp_tac pure_ss [smtfp_bounded_addsub_trace_pair, LET_THM,
    Abbr `xe`, Abbr `ye`, Abbr `scale`] >>
  MATCH_MP_TAC smtfp_pair_trace_bounds >>
  conj_tac >> MATCH_MP_TAC smtfp_bounded_align_bound >> simp []
QED

Theorem smtfp_bounded_addsub_scale_bounds:
  case smtfp_bounded_addsub_trace subtract
      (x : ('t,'w) smtfp) y of (scale,xa,ya,sign,magnitude) =>
    0 < scale /\
    scale <= MAX (smtfp_circuit_exp (smtfp_rep x).Exponent)
      (smtfp_circuit_exp (smtfp_rep y).Exponent)
Proof
  simp_tac pure_ss [smtfp_bounded_addsub_trace_pair, LET_THM,
    smtfp_pair_trace_def, pairTheory.pair_case_thm] >>
  metis_tac [smtfp_retained_scale_bounds, smtfp_circuit_exp_positive]
QED

Theorem smtfp_bounded_addsub_finite_scale_bound:
  2 <= dimindex (:'w) /\ (smtfp_rep x).Exponent <> UINT_MAXw /\
  (smtfp_rep y).Exponent <> UINT_MAXw ==>
  case smtfp_bounded_addsub_trace subtract
      (x : ('t,'w) smtfp) y of (scale,xa,ya,sign,magnitude) =>
    0 < scale /\ scale <= dimword (:'w) - 2
Proof
  rpt strip_tac >>
  `smtfp_circuit_exp (smtfp_rep x).Exponent <= dimword (:'w) - 2 /\
   smtfp_circuit_exp (smtfp_rep y).Exponent <= dimword (:'w) - 2` by
    (conj_tac >> MATCH_MP_TAC smtfp_finite_circuit_exp_bound >> simp []) >>
  `MAX (smtfp_circuit_exp (smtfp_rep x).Exponent)
       (smtfp_circuit_exp (smtfp_rep y).Exponent) <=
     dimword (:'w) - 2` by simp [MAX_LE] >>
  mp_tac (Q.INST [`subtract` |-> `subtract`, `x` |-> `x`, `y` |-> `y`]
    smtfp_bounded_addsub_scale_bounds) >>
  qabbrev_tac `trace = smtfp_bounded_addsub_trace subtract x y` >>
  PairCases_on `trace` >> fs [] >> Omega.OMEGA_TAC
QED

val _ = export_theory ();
