open HolKernel Parse boolLib bossLib wordsLib;
open arithmeticTheory bitTheory wordsTheory;
open smtfloatTheory smtfloatReplayTheory smtfloatReplayWordTheory;
open smtfloatReplayEncodeWordTheory;

val _ = new_theory "smtfloatReplayAddSubWord";

Definition smtfp_word_addsub_exp_def:
  smtfp_word_addsub_exp (exponent : 'e word) : 'c word =
    if exponent = 0w then 1w else w2w exponent
End

Definition smtfp_word_addsub_sig_def:
  smtfp_word_addsub_sig (exponent : 'e word)
      (fraction : 't word) : 'd word =
    if exponent = 0w then w2w fraction
    else n2w (2 ** dimindex (:'t)) + w2w fraction
End

Definition smtfp_word_retained_scale_def:
  smtfp_word_retained_scale (xe : 'c word) (ye : 'c word) =
    let low = if xe <=+ ye then xe else ye in
    let high = if xe <=+ ye then ye else xe in
    let gap = high - low in
      if gap <=+ (3w : 'c word) then low else high - 3w
End

Definition smtfp_word_bounded_align_def:
  smtfp_word_bounded_align (scale : 'c word) (exponent : 'c word)
      (significand : 'd word) =
    if scale <=+ exponent then
      smtfp_word_lsl_bv significand (exponent - scale)
    else smtfp_word_jam_bv significand (scale - exponent)
End

Definition smtfp_word_pair_trace_def:
  smtfp_word_pair_trace (scale : 'c word) (xa : 'd word) (ya : 'd word)
      (sx : word1) sy =
    let sign = if sx = sy \/ ya <=+ xa then sx else sy in
    let magnitude =
      if sx = sy then xa + ya
      else if ya <=+ xa then xa - ya else ya - xa
    in (scale,xa,ya,sign,magnitude)
End

Definition smtfp_word_addsub_trace_def:
  smtfp_word_addsub_trace subtract (sx : word1)
      (ex : 'e word) (fx : 't word) (sy : word1)
      (ey : 'e word) (fy : 't word) (cty : 'c itself)
      (dty : 'd itself) =
    let xe = (smtfp_word_addsub_exp ex : 'c word) in
    let ye = (smtfp_word_addsub_exp ey : 'c word) in
    let xs = (smtfp_word_addsub_sig ex fx : 'd word) in
    let ys = (smtfp_word_addsub_sig ey fy : 'd word) in
    let scale = smtfp_word_retained_scale xe ye in
    let xa = smtfp_word_bounded_align scale xe xs in
    let ya = smtfp_word_bounded_align scale ye ys in
    let ysign = if subtract then ~sy else sy in
      smtfp_word_pair_trace scale xa ya sx ysign
End

Definition smtfp_raw_addsub_trace_def:
  smtfp_raw_addsub_trace subtract (sx : word1)
      (ex : 'e word) (fx : 't word) (sy : word1)
      (ey : 'e word) (fy : 't word) =
    let xe = smtfp_circuit_exp ex in
    let ye = smtfp_circuit_exp ey in
    let scale = MIN xe ye + (MAX xe ye - MIN xe ye - 3) in
    let xa = smtfp_bounded_align scale xe (smtfp_circuit_sig ex fx) in
    let ya = smtfp_bounded_align scale ye (smtfp_circuit_sig ey fy) in
    let ysign = if subtract then ~sy else sy in
      smtfp_pair_trace scale xa ya sx ysign
End

Definition smtfp_word_addsub_zero_sign_def:
  smtfp_word_addsub_zero_sign subtract mode (sx : word1)
      (ex : 'e word) (fx : 't word) (sy : word1)
      (ey : 'e word) (fy : 't word) =
    let ysign = if subtract then ~sy else sy in
    let both_zero =
      (ex = 0w /\ fx = 0w /\ ey = 0w /\ fy = 0w) in
      if both_zero /\ sx = ysign then sx
      else if mode = RTN then 1w else 0w
End

Definition smtfp_word_addsub_fields_def:
  smtfp_word_addsub_fields subtract mode
      (sx : word1) (ex : 'e word)
      (fx : 't word) (sy : word1) (ey : 'e word) (fy : 't word)
      (cty : 'c itself) (dty : 'd itself) =
    let ysign = if subtract then ~sy else sy in
    if smtfp_nan_pattern ex fx \/ smtfp_nan_pattern ey fy then
      (0w : word1, UINT_MAXw : 'e word, 1w : 't word)
    else if ex = UINT_MAXw /\ ey = UINT_MAXw then
      if sx = ysign then (sx,UINT_MAXw,0w)
      else (0w,UINT_MAXw,1w)
    else if ex = UINT_MAXw then (sx,UINT_MAXw,0w)
    else if ey = UINT_MAXw then (ysign,UINT_MAXw,0w)
    else
      let (scale,xa,ya,sign,magnitude) =
        smtfp_word_addsub_trace subtract sx ex fx sy ey fy cty dty in
      if ey = 0w /\ fy = 0w /\ magnitude <> 0w then (sx,ex,fx)
      else
        let sign =
          if magnitude = 0w then
            smtfp_word_addsub_zero_sign subtract mode sx ex fx sy ey fy
          else sign in
        let (encoded,fraction) =
          smtfp_word_encode_fields mode sign
            (smtfp_bits sx ex fx : ('t,'e) smtfp) scale magnitude in
          (sign,encoded,fraction)
End

Definition smtfp_word_addsub_def:
  smtfp_word_addsub subtract mode
      (sx : word1) (ex : 'e word) (fx : 't word)
      (sy : word1) (ey : 'e word) (fy : 't word)
      (cty : 'c itself) (dty : 'd itself) =
    let (sign,exponent,fraction) =
      smtfp_word_addsub_fields subtract mode
        sx ex fx sy ey fy cty dty in
      smtfp_bits sign exponent fraction
End

Theorem smtfp_word_addsub_exp_exact:
  w2n (exponent : 'e word) < dimword (:'c) ==>
  w2n (smtfp_word_addsub_exp exponent : 'c word) =
  smtfp_circuit_exp exponent
Proof
  strip_tac >>
  Cases_on `exponent = 0w`
  >- (asm_simp_tac std_ss [smtfp_word_addsub_exp_def,
        smtfp_circuit_exp_def, word_1_n2w]) >>
  asm_simp_tac std_ss [smtfp_word_addsub_exp_def,
    smtfp_circuit_exp_def, w2w_def, w2n_n2w, LESS_MOD]
QED

Theorem smtfp_word_addsub_sig_exact:
  dimindex (:'t) + 2 <= dimindex (:'d) ==>
  w2n (smtfp_word_addsub_sig exponent (fraction : 't word) : 'd word) =
  smtfp_circuit_sig exponent fraction
Proof
  strip_tac >>
  `w2n fraction < 2 ** dimindex (:'t)` by
    simp [GSYM dimword_def, w2n_lt] >>
  `2 ** dimindex (:'t) + w2n fraction <
   (2 : num) ** (dimindex (:'t) + 1)` by
    (`2 ** dimindex (:'t) + w2n fraction <
      2 ** dimindex (:'t) + 2 ** dimindex (:'t)` by
       Omega.OMEGA_TAC >>
     `2 ** dimindex (:'t) + 2 ** dimindex (:'t) =
      (2 : num) ** (dimindex (:'t) + 1)` by simp [EXP_ADD] >>
     Omega.OMEGA_TAC) >>
  `2 ** dimindex (:'t) + w2n fraction < dimword (:'d)` by
    (simp_tac pure_ss [dimword_def] >>
     `2 ** (dimindex (:'t) + 1) <= (2 : num) ** dimindex (:'d)` by
       simp [EXP_BASE_LE_MONO] >>
     Omega.OMEGA_TAC) >>
  `w2n (w2w fraction : 'd word) = w2n fraction` by
    simp [w2w_def, w2n_n2w, LESS_MOD] >>
  Cases_on `exponent = 0w`
  >- asm_simp_tac std_ss [smtfp_word_addsub_sig_def,
       smtfp_circuit_sig_def] >>
  `w2n (n2w (2 ** dimindex (:'t)) : 'd word) =
   2 ** dimindex (:'t)` by simp [w2n_n2w, LESS_MOD] >>
  `w2n ((n2w (2 ** dimindex (:'t)) : 'd word) + w2w fraction) =
   2 ** dimindex (:'t) + w2n fraction` by
    (qsuff_tac
       `w2n ((n2w (2 ** dimindex (:'t)) : 'd word) + w2w fraction) =
        w2n (n2w (2 ** dimindex (:'t)) : 'd word) +
          w2n (w2w fraction : 'd word)`
     >- asm_rewrite_tac [] >>
     MATCH_MP_TAC w2n_add_2 >> asm_rewrite_tac []) >>
  asm_simp_tac std_ss [smtfp_word_addsub_sig_def,
    smtfp_circuit_sig_def]
QED

Theorem smtfp_word_ordered_retained_value:
  (low : 'c word) <=+ high ==>
  w2n (if high - low <=+ cutoff then low else high - cutoff) =
  w2n low + (w2n high - w2n low - w2n cutoff)
Proof
  strip_tac >>
  `w2n (high - low) = w2n high - w2n low` by
    (MATCH_MP_TAC word_sub_w2n >> first_assum ACCEPT_TAC) >>
  Cases_on `high - low <=+ cutoff`
  >- (`w2n (high - low) <= w2n cutoff` by
        (qpat_x_assum `high - low <=+ cutoff` mp_tac >>
         simp_tac pure_ss [WORD_LS] >> asm_rewrite_tac []) >>
      asm_simp_tac pure_ss [COND_CLAUSES] >>
      Omega.OMEGA_TAC)
  >- (`w2n cutoff < w2n (high - low)` by
        (qpat_x_assum `~(high - low <=+ cutoff)` mp_tac >>
         simp_tac pure_ss [WORD_LS] >> Omega.OMEGA_TAC) >>
      `cutoff <=+ high` by
        (
         simp_tac pure_ss [WORD_LS] >>
         `w2n high - w2n low <= w2n high` by simp [] >>
         Omega.OMEGA_TAC) >>
      `w2n (high - cutoff) = w2n high - w2n cutoff` by
        (MATCH_MP_TAC word_sub_w2n >> first_assum ACCEPT_TAC) >>
      asm_simp_tac pure_ss [COND_CLAUSES] >>
      Omega.OMEGA_TAC)
QED

Theorem smtfp_word_retained_scale_exact:
  3 < dimword (:'c) ==>
  w2n (smtfp_word_retained_scale (xe : 'c word) ye) =
  MIN (w2n xe) (w2n ye) +
    (MAX (w2n xe) (w2n ye) - MIN (w2n xe) (w2n ye) - 3)
Proof
  strip_tac >>
  `w2n (3w : 'c word) = 3` by
    asm_simp_tac std_ss [w2n_n2w, LESS_MOD] >>
  Cases_on `w2n xe <= w2n ye`
  >- (`xe <=+ ye` by simp [WORD_LS] >>
      asm_simp_tac pure_ss [smtfp_word_retained_scale_def, LET_THM,
        COND_CLAUSES, MIN_EQ_LE, MAX_EQ_GE] >>
      qsuff_tac
        `w2n (if ye - xe <=+ (3w : 'c word) then xe else ye - 3w) =
         w2n xe + (w2n ye - w2n xe - w2n (3w : 'c word))`
      >- asm_rewrite_tac [] >>
      MATCH_MP_TAC smtfp_word_ordered_retained_value >>
      asm_rewrite_tac [])
  >- (`~(xe <=+ ye)` by simp [WORD_LS] >>
      `w2n ye <= w2n xe` by Omega.OMEGA_TAC >>
      `ye <=+ xe` by (simp [WORD_LS] >> Omega.OMEGA_TAC) >>
      asm_simp_tac pure_ss [smtfp_word_retained_scale_def, LET_THM,
        COND_CLAUSES, MIN_EQ_LE, MAX_EQ_GE] >>
      qsuff_tac
        `w2n (if xe - ye <=+ (3w : 'c word) then ye else xe - 3w) =
         w2n ye + (w2n xe - w2n ye - w2n (3w : 'c word))`
      >- asm_rewrite_tac [] >>
      MATCH_MP_TAC smtfp_word_ordered_retained_value >>
      asm_rewrite_tac [])
QED

Theorem smtfp_word_lsl_value[local]:
  w2n (w : 'a word) * 2 ** amount < dimword (:'a) ==>
  w2n (w << amount) = w2n w * 2 ** amount
Proof
  strip_tac >>
  `(n2w (2 ** amount) : 'a word) * n2w (w2n w) =
   n2w (2 ** amount * w2n w)` by
    MATCH_ACCEPT_TAC word_mul_n2w >>
  `(n2w (2 ** amount) : 'a word) * w =
   n2w (2 ** amount * w2n w)` by metis_tac [n2w_w2n] >>
  `w << amount = n2w (2 ** amount * w2n w)` by
    metis_tac [WORD_MUL_LSL] >>
  `2 ** amount * w2n w = w2n w * 2 ** amount` by
    MATCH_ACCEPT_TAC MULT_COMM >>
  asm_rewrite_tac [w2n_n2w] >>
  MATCH_MP_TAC LESS_MOD >> simp []
QED

Theorem smtfp_word_bounded_align_exact:
  w2n (scale : 'c word) = retained_scale /\
  w2n (exponent : 'c word) = exp_value /\
  w2n (significand : 'd word) = sig_value /\
  smtfp_bounded_align retained_scale exp_value sig_value <
    dimword (:'d) ==>
  w2n (smtfp_word_bounded_align scale exponent significand) =
  smtfp_bounded_align retained_scale exp_value sig_value
Proof
  strip_tac >> Cases_on `scale <=+ exponent`
  >- (`w2n scale <= w2n exponent` by fs [WORD_LS] >>
      `retained_scale <= exp_value` by Omega.OMEGA_TAC >>
      `w2n (exponent - scale) = w2n exponent - w2n scale` by
        (MATCH_MP_TAC word_sub_w2n >> simp [WORD_LS]) >>
      `w2n significand * 2 ** w2n (exponent - scale) <
       dimword (:'d)` by
        (qpat_x_assum
           `smtfp_bounded_align retained_scale exp_value sig_value < _`
         mp_tac >>
         asm_simp_tac pure_ss [smtfp_bounded_align_def, COND_CLAUSES] >>
         strip_tac >> first_assum ACCEPT_TAC) >>
      `w2n (significand << w2n (exponent - scale)) =
       w2n significand * 2 ** w2n (exponent - scale)` by
        (MATCH_MP_TAC smtfp_word_lsl_value >> asm_rewrite_tac []) >>
      simp_tac pure_ss [smtfp_word_bounded_align_def,
        smtfp_bounded_align_def] >>
      asm_rewrite_tac [smtfp_word_lsl_bv_exact] >>
      qpat_x_assum `w2n (significand << w2n (exponent - scale)) = _`
        mp_tac >> asm_simp_tac pure_ss [] >>
      strip_tac >> first_assum ACCEPT_TAC)
  >- (`w2n exponent < w2n scale` by
        (qpat_x_assum `~(scale <=+ exponent)` mp_tac >>
         simp_tac pure_ss [WORD_LS] >> Omega.OMEGA_TAC) >>
      `~(retained_scale <= exp_value)` by Omega.OMEGA_TAC >>
      `w2n (scale - exponent) = w2n scale - w2n exponent` by
        (MATCH_MP_TAC word_sub_w2n >> simp [WORD_LS]) >>
      simp_tac pure_ss [smtfp_word_bounded_align_def,
        smtfp_bounded_align_def] >>
      asm_rewrite_tac [smtfp_word_jam_bv_exact])
QED

Theorem smtfp_word_pair_trace_exact:
  w2n (xa : 'd word) + w2n ya < dimword (:'d) ==>
  case smtfp_word_pair_trace (scale : 'c word) xa ya sx sy of
    (word_scale,word_xa,word_ya,word_sign,word_magnitude) =>
      (w2n word_scale,w2n word_xa,w2n word_ya,
       word_sign,w2n word_magnitude) =
      smtfp_pair_trace (w2n scale) (w2n xa) (w2n ya) sx sy
Proof
  strip_tac >> Cases_on `sx = sy`
  >- (`w2n (xa + ya) = w2n xa + w2n ya` by
        (MATCH_MP_TAC w2n_add_2 >> asm_rewrite_tac []) >>
      asm_simp_tac std_ss [smtfp_word_pair_trace_def,
        smtfp_pair_trace_def, LET_THM, COND_CLAUSES,
        pairTheory.pair_case_thm])
  >- (Cases_on `ya <=+ xa`
      >- (`w2n ya <= w2n xa` by
            (qpat_x_assum `ya <=+ xa` mp_tac >> simp [WORD_LS]) >>
          `w2n (xa - ya) = w2n xa - w2n ya` by
            (MATCH_MP_TAC word_sub_w2n >> asm_rewrite_tac []) >>
          asm_simp_tac std_ss [smtfp_word_pair_trace_def,
            smtfp_pair_trace_def, LET_THM, COND_CLAUSES,
            pairTheory.pair_case_thm, WORD_LS])
      >- (`w2n xa < w2n ya` by
            FULL_SIMP_TAC std_ss [WORD_LS, NOT_LESS_EQUAL] >>
          `xa <=+ ya` by simp [WORD_LS] >>
          `w2n (ya - xa) = w2n ya - w2n xa` by
            (MATCH_MP_TAC word_sub_w2n >> asm_rewrite_tac []) >>
          `~(w2n ya <= w2n xa)` by
            asm_simp_tac std_ss [NOT_LESS_EQUAL] >>
          asm_simp_tac std_ss [smtfp_word_pair_trace_def,
            smtfp_pair_trace_def, LET_THM, COND_CLAUSES,
            pairTheory.pair_case_thm, WORD_LS]))
QED

Theorem smtfp_rep_bits_raw:
  ~smtfp_nan_pattern exponent significand ==>
  smtfp_rep (smtfp_bits sign exponent significand : ('t,'e) smtfp) =
    <| Sign := sign; Exponent := exponent; Significand := significand |>
Proof
  simp [smtfp_rep_bits, canon_def]
QED

Theorem smtfp_nan_selector_guard[local]:
  smtfp_is_nan x <=>
  (smtfp_rep x).Exponent = UINT_MAXw /\
  (smtfp_rep x).Significand <> 0w
Proof
  rewrite_tac [smtfp_is_nan_def] >>
  Cases_on `smtfp_rep x` >>
  Cases_on `c0 = UINT_MAXw` >> Cases_on `c1 = 0w` >>
  asm_simp_tac std_ss [binary_ieeeTheory.float_is_nan_def,
    binary_ieeeTheory.float_value_def,
    binary_ieeeTheory.float_accessors] >>
  simp []
QED

Theorem smtfp_raw_nan_guard[local]:
  smtfp_nan_pattern exponent significand <=>
  (smtfp_rep
    (smtfp_bits sign exponent significand : ('t,'e) smtfp)).Exponent =
      UINT_MAXw /\
  (smtfp_rep
    (smtfp_bits sign exponent significand : ('t,'e) smtfp)).Significand <>
      0w
Proof
  once_rewrite_tac [GSYM smtfp_nan_selector_guard] >>
  MATCH_ACCEPT_TAC (GSYM smtfp_is_nan_bits)
QED

Theorem smtfp_word_nan_result[local]:
  smtfp_bits (0w : word1) (UINT_MAXw : 'e word) (1w : 't word) =
    (smtfp_nan : ('t,'e) smtfp)
Proof
  MATCH_MP_TAC smtfp_bits_nan >>
  simp [word_1_n2w]
QED

Theorem smtfp_raw_addsub_trace_reference:
  ~smtfp_nan_pattern ex fx /\ ~smtfp_nan_pattern ey fy ==>
  smtfp_raw_addsub_trace subtract sx (ex : 'e word) (fx : 't word)
    sy ey fy =
  smtfp_bounded_addsub_trace subtract
    (smtfp_bits sx ex fx) (smtfp_bits sy ey fy)
Proof
  strip_tac >>
  simp [smtfp_raw_addsub_trace_def, smtfp_bounded_addsub_trace_def,
    smtfp_rep_bits_raw, LET_THM, smtfp_pair_trace_def]
QED

Theorem smtfp_raw_addsub_trace_bounds:
  ~smtfp_nan_pattern ex fx /\ ~smtfp_nan_pattern ey fy ==>
  case smtfp_raw_addsub_trace subtract sx (ex : 'e word) (fx : 't word)
      sy ey fy of
    (scale,xa,ya,sign,magnitude) =>
      xa < 2 ** (dimindex (:'t) + 4) /\
      ya < 2 ** (dimindex (:'t) + 4) /\
      magnitude < 2 ** (dimindex (:'t) + 5)
Proof
  strip_tac >>
  `smtfp_raw_addsub_trace subtract sx ex fx sy ey fy =
   smtfp_bounded_addsub_trace subtract
     (smtfp_bits sx ex fx) (smtfp_bits sy ey fy)` by
    (MATCH_MP_TAC smtfp_raw_addsub_trace_reference >>
     asm_rewrite_tac []) >>
  asm_rewrite_tac [] >>
  MATCH_ACCEPT_TAC smtfp_bounded_addsub_trace_bounds
QED

Theorem smtfp_raw_addsub_finite_scale_bound:
  2 <= dimindex (:'e) /\ (ex : 'e word) <> UINT_MAXw /\
  (ey : 'e word) <> UINT_MAXw ==>
  case smtfp_raw_addsub_trace subtract sx ex (fx : 't word) sy ey fy of
    (scale,xa,ya,sign,magnitude) =>
      0 < scale /\ scale <= dimword (:'e) - 2
Proof
  strip_tac >>
  `~smtfp_nan_pattern ex fx /\ ~smtfp_nan_pattern ey fy` by
    fs [smtfp_nan_pattern_def] >>
  `smtfp_raw_addsub_trace subtract sx ex fx sy ey fy =
   smtfp_bounded_addsub_trace subtract
     (smtfp_bits sx ex fx) (smtfp_bits sy ey fy)` by
    (MATCH_MP_TAC smtfp_raw_addsub_trace_reference >>
     asm_rewrite_tac []) >>
  asm_rewrite_tac [] >>
  MATCH_MP_TAC smtfp_bounded_addsub_finite_scale_bound >>
  fs [smtfp_rep_bits_raw]
QED

Theorem smtfp_word_addsub_zero_sign_exact:
  ~smtfp_nan_pattern ex fx /\ ~smtfp_nan_pattern ey fy ==>
  smtfp_word_addsub_zero_sign subtract mode sx ex fx sy ey fy =
  smtfp_addsub_zero_sign subtract mode
    (smtfp_bits sx ex fx) (smtfp_bits sy ey fy)
Proof
  strip_tac >>
  simp [smtfp_word_addsub_zero_sign_def, smtfp_addsub_zero_sign_def,
    smtfp_rep_bits_raw, LET_THM]
QED

Theorem smtfp_word_addsub_capacity:
  2 <= dimindex (:'e) /\
  dimindex (:'t) + 5 <= dimindex (:'d) /\
  dimword (:'e) - 2 + dimindex (:'d) <= dimword (:'c) ==>
  dimword (:'e) <= dimword (:'c) /\
  3 < dimword (:'c) /\
  dimindex (:'t) + 2 <= dimindex (:'d) /\
  2 ** (dimindex (:'t) + 5) <= dimword (:'d)
Proof
  strip_tac >>
  `4 <= dimword (:'e)` by
    (simp_tac pure_ss [dimword_def] >>
     `2 ** 2 <= (2 : num) ** dimindex (:'e)` by
       simp [EXP_BASE_LE_MONO] >>
     fs []) >>
  `2 <= dimindex (:'d)` by Omega.OMEGA_TAC >>
  `dimword (:'e) <= dimword (:'c)` by Omega.OMEGA_TAC >>
  rpt conj_tac >> TRY Omega.OMEGA_TAC >>
  simp [dimword_def, EXP_BASE_LE_MONO]
QED

Theorem smtfp_num_sum_strict_double[local]:
  (a : num) < bound /\ (b : num) < bound ==>
  a + b < bound + bound
Proof
  strip_tac >> Omega.OMEGA_TAC
QED

Theorem smtfp_word_power_plus_five[local]:
  (2 : num) ** (f + 5) = 2 ** (f + 4) + 2 ** (f + 4)
Proof
  `f + 5 = SUC (f + 4)` by Omega.OMEGA_TAC >>
  qpat_x_assum `f + 5 = _` (fn th => once_rewrite_tac [th]) >>
  CONV_TAC (LAND_CONV (REWR_CONV (CONJUNCT2 EXP))) >>
  REWRITE_TAC [TIMES2]
QED

Theorem smtfp_word_aligned_sum_bound[local]:
  (xa : num) < (2 : num) ** ((f : num) + 4) /\
  (ya : num) < (2 : num) ** (f + 4) ==>
  xa + ya < 2 ** (f + 5)
Proof
  strip_tac >>
  `xa + ya < 2 ** (f + 4) + 2 ** (f + 4)` by
    (MATCH_MP_TAC smtfp_num_sum_strict_double >>
     asm_simp_tac std_ss []) >>
  fs [smtfp_word_power_plus_five]
QED

Theorem smtfp_word_addsub_front_exact[local]:
  dimword (:'e) <= dimword (:'c) /\ 3 < dimword (:'c) /\
  dimindex (:'t) + 2 <= dimindex (:'d) ==>
  w2n (smtfp_word_addsub_exp (ex : 'e word) : 'c word) =
      smtfp_circuit_exp ex /\
  w2n (smtfp_word_addsub_exp (ey : 'e word) : 'c word) =
      smtfp_circuit_exp ey /\
  w2n (smtfp_word_addsub_sig ex (fx : 't word) : 'd word) =
      smtfp_circuit_sig ex fx /\
  w2n (smtfp_word_addsub_sig ey (fy : 't word) : 'd word) =
      smtfp_circuit_sig ey fy /\
  w2n (smtfp_word_retained_scale
      (smtfp_word_addsub_exp ex : 'c word)
      (smtfp_word_addsub_exp ey : 'c word)) =
    MIN (smtfp_circuit_exp ex) (smtfp_circuit_exp ey) +
    (MAX (smtfp_circuit_exp ex) (smtfp_circuit_exp ey) -
     MIN (smtfp_circuit_exp ex) (smtfp_circuit_exp ey) - 3)
Proof
  strip_tac >>
  `w2n ex < dimword (:'c) /\ w2n ey < dimword (:'c)` by
    (`w2n ex < dimword (:'e) /\ w2n ey < dimword (:'e)` by
       simp [w2n_lt] >> Omega.OMEGA_TAC) >>
  rpt conj_tac
  >- simp [smtfp_word_addsub_exp_exact]
  >- simp [smtfp_word_addsub_exp_exact]
  >- simp [smtfp_word_addsub_sig_exact]
  >- simp [smtfp_word_addsub_sig_exact] >>
  qsuff_tac
    `w2n (smtfp_word_retained_scale
       (smtfp_word_addsub_exp ex : 'c word)
       (smtfp_word_addsub_exp ey : 'c word)) =
     MIN (w2n (smtfp_word_addsub_exp ex : 'c word))
       (w2n (smtfp_word_addsub_exp ey : 'c word)) +
     (MAX (w2n (smtfp_word_addsub_exp ex : 'c word))
        (w2n (smtfp_word_addsub_exp ey : 'c word)) -
      MIN (w2n (smtfp_word_addsub_exp ex : 'c word))
        (w2n (smtfp_word_addsub_exp ey : 'c word)) - 3)`
  >- asm_simp_tac std_ss [smtfp_word_addsub_exp_exact] >>
  MATCH_MP_TAC smtfp_word_retained_scale_exact >>
  asm_rewrite_tac []
QED

Theorem smtfp_word_aligned_pair_exact[local]:
  w2n (wscale : 'c word) = scale /\ w2n wxe = xe /\ w2n wye = ye /\
  w2n (wxs : 'd word) = xs /\ w2n (wys : 'd word) = ys /\
  smtfp_bounded_align scale xe xs < (2 : num) ** (f + 4) /\
  smtfp_bounded_align scale ye ys < 2 ** (f + 4) /\
  2 ** (f + 5) <= dimword (:'d) ==>
  w2n (smtfp_word_bounded_align wscale wxe wxs) =
      smtfp_bounded_align scale xe xs /\
  w2n (smtfp_word_bounded_align wscale wye wys) =
      smtfp_bounded_align scale ye ys /\
  w2n (smtfp_word_bounded_align wscale wxe wxs) +
  w2n (smtfp_word_bounded_align wscale wye wys) < dimword (:'d)
Proof
  strip_tac >>
  `2 ** (f + 4) <= dimword (:'d)` by
    (MATCH_MP_TAC LESS_EQ_TRANS >> qexists_tac `2 ** (f + 5)` >>
     asm_rewrite_tac [] >> simp [EXP_BASE_LE_MONO]) >>
  `smtfp_bounded_align scale xe xs < dimword (:'d) /\
   smtfp_bounded_align scale ye ys < dimword (:'d)` by
    (conj_tac >> MATCH_MP_TAC LESS_LESS_EQ_TRANS >>
     qexists_tac `2 ** (f + 4)` >> asm_rewrite_tac []) >>
  `w2n (smtfp_word_bounded_align wscale wxe wxs) =
   smtfp_bounded_align scale xe xs` by
    (MATCH_MP_TAC smtfp_word_bounded_align_exact >>
     asm_simp_tac std_ss [] >> REWRITE_TAC []) >>
  `w2n (smtfp_word_bounded_align wscale wye wys) =
   smtfp_bounded_align scale ye ys` by
    (MATCH_MP_TAC smtfp_word_bounded_align_exact >>
     asm_simp_tac std_ss [] >> REWRITE_TAC []) >>
  asm_rewrite_tac [] >>
  MATCH_MP_TAC LESS_LESS_EQ_TRANS >> qexists_tac `2 ** (f + 5)` >>
  asm_simp_tac std_ss [smtfp_word_aligned_sum_bound]
QED

Theorem smtfp_word_addsub_aligned_exact[local]:
  2 <= dimindex (:'e) /\
  dimindex (:'t) + 5 <= dimindex (:'d) /\
  dimword (:'e) - 2 + dimindex (:'d) <= dimword (:'c) /\
  ~smtfp_nan_pattern (ex : 'e word) (fx : 't word) /\
  ~smtfp_nan_pattern (ey : 'e word) (fy : 't word) ==>
  let xe = smtfp_circuit_exp ex in
  let ye = smtfp_circuit_exp ey in
  let xs = smtfp_circuit_sig ex fx in
  let ys = smtfp_circuit_sig ey fy in
  let scale = MIN xe ye + (MAX xe ye - MIN xe ye - 3) in
  let wxe = (smtfp_word_addsub_exp ex : 'c word) in
  let wye = (smtfp_word_addsub_exp ey : 'c word) in
  let wxs = (smtfp_word_addsub_sig ex fx : 'd word) in
  let wys = (smtfp_word_addsub_sig ey fy : 'd word) in
  let wscale = smtfp_word_retained_scale wxe wye in
  let wxa = smtfp_word_bounded_align wscale wxe wxs in
  let wya = smtfp_word_bounded_align wscale wye wys in
    w2n wscale = scale /\
    w2n wxa = smtfp_bounded_align scale xe xs /\
    w2n wya = smtfp_bounded_align scale ye ys /\
    w2n wxa + w2n wya < dimword (:'d)
Proof
  strip_tac >> simp_tac pure_ss [LET_THM] >>
  `dimword (:'e) <= dimword (:'c) /\ 3 < dimword (:'c) /\
   dimindex (:'t) + 2 <= dimindex (:'d) /\
   2 ** (dimindex (:'t) + 5) <= dimword (:'d)` by
    (MATCH_MP_TAC smtfp_word_addsub_capacity >> asm_rewrite_tac []) >>
  mp_tac smtfp_word_addsub_front_exact >>
  impl_tac >- asm_rewrite_tac [] >> strip_tac >>
  `smtfp_bounded_align
       (MIN (smtfp_circuit_exp ex) (smtfp_circuit_exp ey) +
        (MAX (smtfp_circuit_exp ex) (smtfp_circuit_exp ey) -
         MIN (smtfp_circuit_exp ex) (smtfp_circuit_exp ey) - 3))
       (smtfp_circuit_exp ex) (smtfp_circuit_sig ex fx) <
       2 ** (dimindex (:'t) + 4) /\
   smtfp_bounded_align
       (MIN (smtfp_circuit_exp ex) (smtfp_circuit_exp ey) +
        (MAX (smtfp_circuit_exp ex) (smtfp_circuit_exp ey) -
         MIN (smtfp_circuit_exp ex) (smtfp_circuit_exp ey) - 3))
       (smtfp_circuit_exp ey) (smtfp_circuit_sig ey fy) <
       2 ** (dimindex (:'t) + 4)` by
    (mp_tac smtfp_raw_addsub_trace_bounds >>
     impl_tac >- asm_rewrite_tac [] >>
     simp_tac pure_ss [smtfp_raw_addsub_trace_def, LET_THM,
       smtfp_pair_trace_def, pairTheory.pair_case_thm] >>
     strip_tac >> asm_rewrite_tac []) >>
  conj_tac >- asm_rewrite_tac [] >>
  MATCH_MP_TAC (Q.INST [`f` |-> `dimindex (:'t)`]
    smtfp_word_aligned_pair_exact) >>
  asm_simp_tac std_ss []
QED

Theorem smtfp_word_pair_trace_transport[local]:
  w2n (word_scale : 'c word) = scale /\
  w2n (word_xa : 'd word) = xa /\ w2n (word_ya : 'd word) = ya /\
  w2n word_xa + w2n word_ya < dimword (:'d) ==>
  case smtfp_word_pair_trace word_scale word_xa word_ya sx sy of
    (ws,wx,wy,ss,wm) => (w2n ws,w2n wx,w2n wy,ss,w2n wm) =
      smtfp_pair_trace scale xa ya sx sy
Proof
  strip_tac >>
  qsuff_tac
    `case smtfp_word_pair_trace word_scale word_xa word_ya sx sy of
       (ws,wx,wy,ss,wm) => (w2n ws,w2n wx,w2n wy,ss,w2n wm) =
         smtfp_pair_trace (w2n word_scale) (w2n word_xa)
           (w2n word_ya) sx sy`
  >- asm_rewrite_tac [] >>
  MATCH_MP_TAC smtfp_word_pair_trace_exact >> asm_rewrite_tac []
QED

Theorem smtfp_word_addsub_trace_exact:
  2 <= dimindex (:'e) /\
  dimindex (:'t) + 5 <= dimindex (:'d) /\
  dimword (:'e) - 2 + dimindex (:'d) <= dimword (:'c) /\
  ~smtfp_nan_pattern ex fx /\ ~smtfp_nan_pattern ey fy ==>
  case smtfp_word_addsub_trace subtract sx (ex : 'e word) (fx : 't word)
      sy ey fy (:'c) (:'d) of
    (word_scale,word_xa,word_ya,word_sign,word_magnitude) =>
      (w2n word_scale,w2n word_xa,w2n word_ya,
       word_sign,w2n word_magnitude) =
      smtfp_raw_addsub_trace subtract sx ex fx sy ey fy
Proof
  strip_tac >>
  mp_tac smtfp_word_addsub_aligned_exact >>
  impl_tac >- asm_rewrite_tac [] >>
  simp_tac pure_ss [LET_THM] >> strip_tac >>
  simp_tac pure_ss [smtfp_word_addsub_trace_def,
    smtfp_raw_addsub_trace_def, LET_THM] >>
  MATCH_MP_TAC smtfp_word_pair_trace_transport >>
  asm_simp_tac std_ss []
QED

Theorem smtfp_word_finite_result:
  2 <= dimindex (:'e) /\ dimindex (:'t) + 2 <= dimindex (:'d) /\
  dimword (:'e) - 2 + dimindex (:'d) <= dimword (:'c) /\
  w2n (word_scale : 'c word) = scale /\
  w2n (word_magnitude : 'd word) = magnitude /\
  0 < scale /\ scale <= dimword (:'e) - 2 /\
  word_zero_sign = zero_sign ==>
  (if right_zero /\ word_magnitude <> 0w then
     (format : ('t,'e) smtfp)
   else smtfp_word_encode mode
     (if word_magnitude = 0w then word_zero_sign else result_sign)
     format word_scale word_magnitude) =
  (if right_zero /\ magnitude <> 0 then format
   else smtfp_circuit_encode mode format
     (if magnitude = 0 then zero_sign else result_sign) scale magnitude)
Proof
  strip_tac >>
  `word_magnitude = 0w <=> magnitude = 0` by
    metis_tac [w2n_eq_0] >>
  `!chosen. smtfp_word_encode mode chosen format word_scale word_magnitude =
    smtfp_circuit_encode mode format chosen
      (w2n word_scale) (w2n word_magnitude)` by
    (strip_tac >> MATCH_MP_TAC smtfp_word_encode_exact >>
     asm_simp_tac std_ss []) >>
  Cases_on `right_zero` >> Cases_on `word_magnitude = 0w` >>
  FULL_SIMP_TAC std_ss []
QED

Theorem smtfp_word_addsub_finite_form[local]:
  (ex : 'e word) <> UINT_MAXw /\ (ey : 'e word) <> UINT_MAXw ==>
  smtfp_word_addsub subtract mode sx ex (fx : 't word) sy ey fy
      (:'c) (:'d) =
  case smtfp_word_addsub_trace subtract sx ex fx sy ey fy (:'c) (:'d) of
    (scale,xa,ya,sign,magnitude) =>
      if ey = 0w /\ fy = 0w /\ magnitude <> 0w then
        smtfp_bits sx ex fx
      else smtfp_word_encode mode
        (if magnitude = 0w then
           smtfp_word_addsub_zero_sign subtract mode sx ex fx sy ey fy
         else sign)
        (smtfp_bits sx ex fx) scale magnitude
Proof
  strip_tac >>
  `~smtfp_nan_pattern ex fx /\ ~smtfp_nan_pattern ey fy` by
    fs [smtfp_nan_pattern_def] >>
  qabbrev_tac `wtrace = smtfp_word_addsub_trace subtract sx ex fx sy ey fy
    (:'c) (:'d)` >> PairCases_on `wtrace` >>
  qpat_x_assum
    `Abbrev ((wtrace0,wtrace1,wtrace2,wtrace3,wtrace4) = _)` mp_tac >>
  simp_tac pure_ss [markerTheory.Abbrev_def] >>
  DISCH_THEN (assume_tac o SYM) >>
  qabbrev_tac `fields = smtfp_word_encode_fields mode
    (if wtrace4 = 0w then
       smtfp_word_addsub_zero_sign subtract mode sx ex fx sy ey fy
     else wtrace3) (smtfp_bits sx ex fx) wtrace0 wtrace4` >>
  PairCases_on `fields` >>
  qpat_x_assum `Abbrev ((fields0,fields1) = _)` mp_tac >>
  simp_tac pure_ss [markerTheory.Abbrev_def] >>
  DISCH_THEN (assume_tac o SYM) >>
  asm_simp_tac pure_ss [smtfp_word_addsub_def,
    smtfp_word_addsub_fields_def, smtfp_word_encode_def, LET_THM,
    pairTheory.pair_case_thm, boolTheory.COND_CLAUSES,
    boolTheory.OR_CLAUSES, boolTheory.AND_CLAUSES] >>
  Cases_on `ey = 0w /\ fy = 0w /\ wtrace4 <> 0w` >>
  asm_simp_tac std_ss [pairTheory.pair_case_thm]
QED

Theorem smtfp_bounded_addsub_bits_finite_form[local]:
  (ex : 'e word) <> UINT_MAXw /\ (ey : 'e word) <> UINT_MAXw ==>
  smtfp_bounded_addsub_circuit subtract mode
      (smtfp_bits sx ex (fx : 't word)) (smtfp_bits sy ey fy) =
  case smtfp_bounded_addsub_trace subtract
      (smtfp_bits sx ex fx) (smtfp_bits sy ey fy) of
    (scale,xa,ya,sign,magnitude) =>
      if ey = 0w /\ fy = 0w /\ magnitude <> 0 then smtfp_bits sx ex fx
      else smtfp_circuit_encode mode (smtfp_bits sx ex fx)
        (if magnitude = 0 then
           smtfp_addsub_zero_sign subtract mode
             (smtfp_bits sx ex fx) (smtfp_bits sy ey fy)
         else sign) scale magnitude
Proof
  strip_tac >>
  `~smtfp_nan_pattern ex fx /\ ~smtfp_nan_pattern ey fy` by
    fs [smtfp_nan_pattern_def] >>
  qabbrev_tac `trace = smtfp_bounded_addsub_trace subtract
    (smtfp_bits sx ex fx) (smtfp_bits sy ey fy)` >>
  PairCases_on `trace` >>
  qpat_x_assum
    `Abbrev ((trace0,trace1,trace2,trace3,trace4) = _)` mp_tac >>
  simp_tac pure_ss [markerTheory.Abbrev_def] >>
  DISCH_THEN (assume_tac o SYM) >>
  asm_simp_tac std_ss [smtfp_bounded_addsub_circuit_def,
    smtfp_rep_bits_raw, binary_ieeeTheory.float_accessors,
    LET_THM, pairTheory.pair_case_thm] >>
  fs []
QED

Theorem smtfp_word_addsub_finite_trace[local]:
  2 <= dimindex (:'e) /\
  dimindex (:'t) + 5 <= dimindex (:'d) /\
  dimword (:'e) - 2 + dimindex (:'d) <= dimword (:'c) /\
  (ex : 'e word) <> UINT_MAXw /\ (ey : 'e word) <> UINT_MAXw ==>
  case smtfp_word_addsub_trace subtract sx ex (fx : 't word)
      sy ey fy (:'c) (:'d) of
    (ws,wx,wy,ss,wm) =>
      smtfp_bounded_addsub_trace subtract
        (smtfp_bits sx ex fx) (smtfp_bits sy ey fy) =
          (w2n ws,w2n wx,w2n wy,ss,w2n wm) /\
      0 < w2n ws /\ w2n ws <= dimword (:'e) - 2
Proof
  strip_tac >>
  `~smtfp_nan_pattern ex fx /\ ~smtfp_nan_pattern ey fy` by
    fs [smtfp_nan_pattern_def] >>
  qabbrev_tac `wtrace = smtfp_word_addsub_trace subtract sx ex fx sy ey fy
    (:'c) (:'d)` >> PairCases_on `wtrace` >>
  qpat_x_assum
    `Abbrev ((wtrace0,wtrace1,wtrace2,wtrace3,wtrace4) = _)` mp_tac >>
  simp_tac pure_ss [markerTheory.Abbrev_def] >>
  DISCH_THEN (assume_tac o SYM) >>
  `(w2n wtrace0,w2n wtrace1,w2n wtrace2,wtrace3,w2n wtrace4) =
   smtfp_raw_addsub_trace subtract sx ex fx sy ey fy` by
    (`case smtfp_word_addsub_trace subtract sx ex fx sy ey fy
          (:'c) (:'d) of
        (ws,wx,wy,ss,wm) => (w2n ws,w2n wx,w2n wy,ss,w2n wm) =
          smtfp_raw_addsub_trace subtract sx ex fx sy ey fy` by
       (MATCH_MP_TAC smtfp_word_addsub_trace_exact >>
        asm_rewrite_tac []) >>
     first_x_assum mp_tac >>
     asm_simp_tac pure_ss [pairTheory.pair_case_thm] >>
     DISCH_THEN ACCEPT_TAC) >>
  `smtfp_raw_addsub_trace subtract sx ex fx sy ey fy =
   smtfp_bounded_addsub_trace subtract
     (smtfp_bits sx ex fx) (smtfp_bits sy ey fy)` by
    (MATCH_MP_TAC smtfp_raw_addsub_trace_reference >> asm_rewrite_tac []) >>
  `0 < w2n wtrace0 /\ w2n wtrace0 <= dimword (:'e) - 2` by
    (mp_tac smtfp_raw_addsub_finite_scale_bound >>
     impl_tac >- asm_rewrite_tac [] >>
     qpat_x_assum `(w2n wtrace0,_,_,_,_) = _`
       (fn th => simp_tac pure_ss [GSYM th, pairTheory.pair_case_thm]) >>
     DISCH_THEN ACCEPT_TAC) >>
  qpat_x_assum `_ = smtfp_bounded_addsub_trace _ _ _`
    (fn th => once_rewrite_tac [GSYM th]) >>
  qpat_x_assum `(w2n wtrace0,_,_,_,_) = _`
    (fn th => once_rewrite_tac [GSYM th]) >>
  asm_simp_tac std_ss [pairTheory.pair_case_thm]
QED

Theorem smtfp_word_addsub_finite_exact:
  2 <= dimindex (:'e) /\
  dimindex (:'t) + 5 <= dimindex (:'d) /\
  dimword (:'e) - 2 + dimindex (:'d) <= dimword (:'c) /\
  (ex : 'e word) <> UINT_MAXw /\ (ey : 'e word) <> UINT_MAXw ==>
  smtfp_word_addsub subtract mode sx ex (fx : 't word) sy ey fy
    (:'c) (:'d) =
  smtfp_bounded_addsub_circuit subtract mode
    (smtfp_bits sx ex fx) (smtfp_bits sy ey fy)
Proof
  strip_tac >>
  `~smtfp_nan_pattern ex fx /\ ~smtfp_nan_pattern ey fy` by
    fs [smtfp_nan_pattern_def] >>
  `dimindex (:'t) + 2 <= dimindex (:'d)` by Omega.OMEGA_TAC >>
  qabbrev_tac `wtrace = smtfp_word_addsub_trace subtract sx ex fx sy ey fy
    (:'c) (:'d)` >> PairCases_on `wtrace` >>
  qpat_x_assum
    `Abbrev ((wtrace0,wtrace1,wtrace2,wtrace3,wtrace4) = _)` mp_tac >>
  simp_tac pure_ss [markerTheory.Abbrev_def] >>
  DISCH_THEN (assume_tac o SYM) >>
  `smtfp_bounded_addsub_trace subtract
      (smtfp_bits sx ex fx) (smtfp_bits sy ey fy) =
       (w2n wtrace0,w2n wtrace1,w2n wtrace2,wtrace3,w2n wtrace4) /\
   0 < w2n wtrace0 /\ w2n wtrace0 <= dimword (:'e) - 2` by
    (`case smtfp_word_addsub_trace subtract sx ex fx sy ey fy
          (:'c) (:'d) of
        (ws,wx,wy,ss,wm) =>
          smtfp_bounded_addsub_trace subtract
            (smtfp_bits sx ex fx) (smtfp_bits sy ey fy) =
              (w2n ws,w2n wx,w2n wy,ss,w2n wm) /\
          0 < w2n ws /\ w2n ws <= dimword (:'e) - 2` by
       (MATCH_MP_TAC smtfp_word_addsub_finite_trace >>
        asm_rewrite_tac []) >>
     first_x_assum mp_tac >>
     asm_simp_tac pure_ss [pairTheory.pair_case_thm] >>
     DISCH_THEN ACCEPT_TAC) >>
  `smtfp_word_addsub_zero_sign subtract mode sx ex fx sy ey fy =
   smtfp_addsub_zero_sign subtract mode
     (smtfp_bits sx ex fx) (smtfp_bits sy ey fy)` by
    (MATCH_MP_TAC smtfp_word_addsub_zero_sign_exact >>
     asm_rewrite_tac []) >>
  mp_tac smtfp_word_addsub_finite_form >>
  impl_tac >- asm_rewrite_tac [] >>
  asm_simp_tac pure_ss [pairTheory.pair_case_thm] >> strip_tac >>
  mp_tac smtfp_bounded_addsub_bits_finite_form >>
  impl_tac >- asm_rewrite_tac [] >>
  asm_simp_tac pure_ss [pairTheory.pair_case_thm] >>
  strip_tac >> asm_rewrite_tac [] >>
  simp_tac pure_ss [CONJ_ASSOC] >>
  MATCH_MP_TAC smtfp_word_finite_result >>
  asm_simp_tac std_ss []
QED

Theorem smtfp_word_addsub_bounded_exact:
  2 <= dimindex (:'e) /\
  dimindex (:'t) + 5 <= dimindex (:'d) /\
  dimword (:'e) - 2 + dimindex (:'d) <= dimword (:'c) ==>
  smtfp_word_addsub subtract mode sx (ex : 'e word) (fx : 't word)
      sy ey fy (:'c) (:'d) =
  smtfp_bounded_addsub_circuit subtract mode
    (smtfp_bits sx ex fx) (smtfp_bits sy ey fy)
Proof
  strip_tac >>
  Cases_on `smtfp_nan_pattern ex fx`
  >- (asm_simp_tac std_ss [smtfp_word_addsub_def,
        smtfp_word_addsub_fields_def, smtfp_bounded_addsub_circuit_def,
        GSYM smtfp_raw_nan_guard, smtfp_word_nan_result, LET_THM,
        pairTheory.pair_case_thm] >>
      fs [smtfp_word_nan_result]) >>
  Cases_on `smtfp_nan_pattern ey fy`
  >- (asm_simp_tac std_ss [smtfp_word_addsub_def,
        smtfp_word_addsub_fields_def, smtfp_bounded_addsub_circuit_def,
        GSYM smtfp_raw_nan_guard, smtfp_word_nan_result, LET_THM,
        pairTheory.pair_case_thm] >> fs [smtfp_word_nan_result]) >>
  `smtfp_rep (smtfp_bits sx ex fx : ('t,'e) smtfp) =
   <| Sign := sx; Exponent := ex; Significand := fx |>` by
    (MATCH_MP_TAC smtfp_rep_bits_raw >> asm_rewrite_tac []) >>
  `smtfp_rep (smtfp_bits sy ey fy : ('t,'e) smtfp) =
   <| Sign := sy; Exponent := ey; Significand := fy |>` by
    (MATCH_MP_TAC smtfp_rep_bits_raw >> asm_rewrite_tac []) >>
  Cases_on `ex = UINT_MAXw` >> Cases_on `ey = UINT_MAXw`
  >- (`fx = 0w /\ fy = 0w` by fs [smtfp_nan_pattern_def] >>
      Cases_on `sx = if subtract then ~sy else sy` >>
      asm_simp_tac pure_ss [smtfp_word_addsub_def,
        smtfp_word_addsub_fields_def,
        smtfp_bounded_addsub_circuit_def, smtfp_rep_bits_raw,
        smtfp_circuit_infinity_def, smtfp_word_nan_result,
        binary_ieeeTheory.float_accfupds, combinTheory.K_THM, LET_THM,
        pairTheory.pair_case_thm, boolTheory.COND_CLAUSES,
        boolTheory.OR_CLAUSES, boolTheory.AND_CLAUSES] >>
      simp_tac std_ss [pairTheory.pair_case_thm] >>
      TRY (MATCH_ACCEPT_TAC smtfp_word_nan_result) >> REWRITE_TAC [])
  >- (`fx = 0w` by fs [smtfp_nan_pattern_def] >>
      asm_simp_tac std_ss [smtfp_word_addsub_def,
        smtfp_word_addsub_fields_def,
        smtfp_bounded_addsub_circuit_def, smtfp_rep_bits_raw,
        smtfp_circuit_infinity_def, binary_ieeeTheory.float_accfupds,
        LET_THM, pairTheory.pair_case_thm] >> fs [])
  >- (`fy = 0w` by fs [smtfp_nan_pattern_def] >>
      asm_simp_tac std_ss [smtfp_word_addsub_def,
        smtfp_word_addsub_fields_def,
        smtfp_bounded_addsub_circuit_def, smtfp_rep_bits_raw,
        smtfp_circuit_infinity_def, binary_ieeeTheory.float_accfupds,
        LET_THM, pairTheory.pair_case_thm] >> fs []) >>
  MATCH_MP_TAC smtfp_word_addsub_finite_exact >>
  asm_rewrite_tac []
QED

Theorem smtfp_word_addsub_exact:
  2 <= dimindex (:'e) /\
  dimindex (:'t) + 5 <= dimindex (:'d) /\
  dimword (:'e) - 2 + dimindex (:'d) <= dimword (:'c) ==>
  smtfp_word_addsub subtract mode sx (ex : 'e word) (fx : 't word)
      sy ey fy (:'c) (:'d) =
  if subtract then
    smtfp_sub mode (smtfp_bits sx ex fx) (smtfp_bits sy ey fy)
  else smtfp_add mode (smtfp_bits sx ex fx) (smtfp_bits sy ey fy)
Proof
  strip_tac >>
  `smtfp_word_addsub subtract mode sx ex fx sy ey fy (:'c) (:'d) =
   smtfp_bounded_addsub_circuit subtract mode
     (smtfp_bits sx ex fx) (smtfp_bits sy ey fy)` by
    (MATCH_MP_TAC smtfp_word_addsub_bounded_exact >>
     asm_rewrite_tac []) >>
  `(if subtract then
      smtfp_sub mode (smtfp_bits sx ex fx) (smtfp_bits sy ey fy)
    else smtfp_add mode (smtfp_bits sx ex fx) (smtfp_bits sy ey fy)) =
   smtfp_bounded_addsub_circuit subtract mode
     (smtfp_bits sx ex fx) (smtfp_bits sy ey fy)` by
    (MATCH_MP_TAC smtfp_bounded_addsub_circuit_correspondence >>
     asm_rewrite_tac []) >>
  asm_rewrite_tac []
QED

Theorem smtfp_n2w_nonzero[local]:
  0 < n /\ n < dimword (:'a) ==> (n2w n : 'a word) <> 0w
Proof
  simp [GSYM wordsTheory.w2n_eq_0, wordsTheory.w2n_n2w,
    arithmeticTheory.LESS_MOD]
QED

Theorem smtfp_circuit_overflow_not_zero[local]:
  2 <= dimindex (:'e) ==>
  ~smtfp_is_zero
    (smtfp_circuit_overflow mode (format : ('t,'e) smtfp) sign)
Proof
  strip_tac >>
  `2 < dimword (:'e)` by
    (simp [wordsTheory.dimword_def] >>
     `2 ** 2 <= (2 : num) ** dimindex (:'e)` by
       (irule bitTheory.TWOEXP_MONO2 >> asm_rewrite_tac []) >>
     numLib.ARITH_TAC) >>
  `(UINT_MAXw : 'e word) <> 0w` by
    (simp [wordsTheory.word_T_def, wordsTheory.UINT_MAX_def] >>
     irule smtfp_n2w_nonzero >> numLib.ARITH_TAC) >>
  Cases_on `mode` >> Cases_on `sign = 0w` >>
  Cases_on `sign = 1w` >>
  simp [smtfp_circuit_overflow_def, smtfp_circuit_infinity_def,
    smtfp_circuit_top_def, smtfp_is_zero_bits, wordsTheory.dimword_def,
    wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]
QED

Theorem smtfp_circuit_encode_is_zero:
  2 <= dimindex (:'e) /\ 0 < scale ==>
  (smtfp_is_zero
     (smtfp_circuit_encode mode (format : ('t,'e) smtfp)
       sign scale magnitude) <=>
   magnitude = 0)
Proof
  strip_tac >> Cases_on `magnitude = 0`
  >- simp [smtfp_is_zero_bits] >>
  `0 < magnitude` by decide_tac >>
  qabbrev_tac `maximum_exponent = dimword (:'e) - 2` >>
  qabbrev_tac `fraction_width = dimindex (:'t)` >>
  qabbrev_tac
    `exponent = smtfp_circuit_encoded_exponent maximum_exponent
      fraction_width scale magnitude` >>
  qabbrev_tac
    `quotient = smtfp_circuit_quotient maximum_exponent fraction_width
      scale magnitude` >>
  qabbrev_tac
    `rounded = smtfp_circuit_rounded mode sign maximum_exponent
      fraction_width scale magnitude` >>
  `1 <= maximum_exponent` by
    (simp [Abbr `maximum_exponent`, wordsTheory.dimword_def] >>
     `2 ** 2 <= (2 : num) ** dimindex (:'e)` by
       (irule bitTheory.TWOEXP_MONO2 >> asm_rewrite_tac []) >>
     qpat_x_assum `2 ** 2 <= _` mp_tac >>
     rewrite_tac [EVAL ``((2 : num) ** 2)``] >>
     numLib.ARITH_TAC) >>
  `smtfp_circuit_effective_exponent maximum_exponent fraction_width
       scale magnitude = exponent /\
   1 <= exponent /\ exponent <= maximum_exponent` by
    (mp_tac (Q.INST
       [`maximum_exponent` |-> `maximum_exponent`,
        `fraction_width` |-> `fraction_width`, `scale` |-> `scale`,
        `magnitude` |-> `magnitude`]
       smtfp_circuit_effective_encoded) >>
     simp [Abbr `exponent`]) >>
  `0 < quotient` by
    (Cases_on `quotient = 0`
     >- (`quotient < 2 ** fraction_width` by simp [] >>
         `exponent = 1` by
           (mp_tac (Q.INST
              [`maximum_exponent` |-> `maximum_exponent`,
               `fraction_width` |-> `fraction_width`,
               `scale` |-> `scale`, `magnitude` |-> `magnitude`]
              smtfp_circuit_quotient_normalized_lower) >>
            simp [Abbr `quotient`, Abbr `exponent`]) >>
         mp_tac (Q.INST
           [`maximum_exponent` |-> `maximum_exponent`,
            `fraction_width` |-> `fraction_width`, `scale` |-> `scale`,
            `magnitude` |-> `magnitude`]
           smtfp_circuit_quotient_units) >>
         impl_tac >- asm_rewrite_tac [] >>
         simp_tac pure_ss [Abbr `quotient`] >>
         asm_rewrite_tac [] >> simp []) >>
     decide_tac) >>
  `0 < rounded` by
    (mp_tac (Q.INST
       [`mode` |-> `mode`, `sign` |-> `sign`, `q` |-> `quotient`,
        `residue` |->
          `smtfp_circuit_remainder maximum_exponent fraction_width
            scale magnitude`,
        `divisor` |->
          `smtfp_circuit_divisor maximum_exponent fraction_width
            scale magnitude`]
       smtfp_circuit_round_bounds) >>
     simp [Abbr `rounded`, smtfp_circuit_rounded_def]) >>
  `dimword (:'t) = 2 ** dimindex (:'t)` by
    simp [wordsTheory.dimword_def] >>
  `(n2w exponent : 'e word) <> 0w` by
    (irule smtfp_n2w_nonzero >> simp [Abbr `maximum_exponent`] >>
     numLib.ARITH_TAC) >>
  `(n2w (exponent + 1) : 'e word) <> 0w` by
    (irule smtfp_n2w_nonzero >> simp [Abbr `maximum_exponent`] >>
     numLib.ARITH_TAC) >>
  simp_tac pure_ss [smtfp_circuit_encode_def] >>
  asm_rewrite_tac [] >>
  simp_tac pure_ss [LET_THM] >>
  simp_tac pure_ss [Abbr `maximum_exponent`, Abbr `fraction_width`,
    Abbr `exponent`, Abbr `rounded`, smtfp_circuit_pack_def, LET_THM] >>
  rpt IF_CASES_TAC >>
  asm_simp_tac std_ss [smtfp_is_zero_bits] >>
  TRY (MATCH_MP_TAC smtfp_circuit_overflow_not_zero >>
       asm_rewrite_tac []) >>
  TRY (MATCH_MP_TAC smtfp_n2w_nonzero >> asm_rewrite_tac []) >>
  fs []
QED

Theorem smtfp_word_encode_is_zero[local]:
  2 <= dimindex (:'e) /\
  dimindex (:'t) + 2 <= dimindex (:'d) /\
  dimword (:'e) - 2 + dimindex (:'d) <= dimword (:'c) /\
  0 < w2n (scale : 'c word) /\
  w2n scale <= dimword (:'e) - 2 ==>
  (smtfp_is_zero
     (smtfp_word_encode mode sign (format : ('t,'e) smtfp)
       scale (data : 'd word)) <=>
   data = 0w)
Proof
  strip_tac >>
  `smtfp_word_encode mode sign format scale data =
   smtfp_circuit_encode mode format sign (w2n scale) (w2n data)` by
    (MATCH_MP_TAC smtfp_word_encode_exact >> asm_rewrite_tac []) >>
  asm_simp_tac std_ss [smtfp_circuit_encode_is_zero,
    wordsTheory.w2n_eq_0]
QED

Theorem smtfp_addsub_is_zero_word_trace:
  2 <= dimindex (:'e) /\
  dimindex (:'t) + 5 <= dimindex (:'d) /\
  dimword (:'e) - 2 + dimindex (:'d) <= dimword (:'c) ==>
  (smtfp_is_zero
    (if subtract then
       smtfp_sub mode
         (smtfp_bits sx (ex : 'e word) (fx : 't word))
         (smtfp_bits sy ey fy)
     else
       smtfp_add mode
         (smtfp_bits sx ex fx)
         (smtfp_bits sy ey fy)) <=>
   ex <> UINT_MAXw /\ ey <> UINT_MAXw /\
   case smtfp_word_addsub_trace subtract sx ex fx sy ey fy
       (:'c) (:'d) of
     (scale,xa,ya,sign,magnitude) => magnitude = 0w)
Proof
  strip_tac >>
  `2 < dimword (:'e)` by
    (simp [wordsTheory.dimword_def] >>
     `2 ** 2 <= (2 : num) ** dimindex (:'e)` by
       (irule bitTheory.TWOEXP_MONO2 >> asm_rewrite_tac []) >>
     numLib.ARITH_TAC) >>
  `(UINT_MAXw : 'e word) <> 0w` by
    (simp [wordsTheory.word_T_def, wordsTheory.UINT_MAX_def] >>
     irule smtfp_n2w_nonzero >> numLib.ARITH_TAC) >>
  `smtfp_word_addsub subtract mode sx ex fx sy ey fy (:'c) (:'d) =
   (if subtract then
      smtfp_sub mode (smtfp_bits sx ex fx) (smtfp_bits sy ey fy)
    else
      smtfp_add mode (smtfp_bits sx ex fx) (smtfp_bits sy ey fy))` by
    (MATCH_MP_TAC smtfp_word_addsub_exact >> asm_rewrite_tac []) >>
  pop_assum (fn th => once_rewrite_tac [GSYM th]) >>
  qabbrev_tac `trace = smtfp_word_addsub_trace subtract sx ex fx sy ey fy
    (:'c) (:'d)` >>
  PairCases_on `trace` >>
  qpat_x_assum
    `Abbrev ((trace0,trace1,trace2,trace3,trace4) = _)` mp_tac >>
  simp_tac pure_ss [markerTheory.Abbrev_def] >>
  DISCH_THEN (assume_tac o SYM) >>
  Cases_on `ex = UINT_MAXw` >> Cases_on `ey = UINT_MAXw`
  >- (asm_simp_tac std_ss [smtfp_word_addsub_def,
        smtfp_word_addsub_fields_def, smtfp_nan_pattern_def, LET_THM,
        pairTheory.pair_case_thm] >>
      rpt IF_CASES_TAC >> simp [smtfp_is_zero_bits])
  >- (asm_simp_tac std_ss [smtfp_word_addsub_def,
        smtfp_word_addsub_fields_def, smtfp_nan_pattern_def, LET_THM,
        pairTheory.pair_case_thm] >>
      rpt IF_CASES_TAC >> simp [smtfp_is_zero_bits])
  >- (asm_simp_tac std_ss [smtfp_word_addsub_def,
        smtfp_word_addsub_fields_def, smtfp_nan_pattern_def, LET_THM,
        pairTheory.pair_case_thm] >>
      rpt IF_CASES_TAC >> simp [smtfp_is_zero_bits])
  >- (`~smtfp_nan_pattern ex fx /\ ~smtfp_nan_pattern ey fy` by
        fs [smtfp_nan_pattern_def] >>
      `(w2n trace0,w2n trace1,w2n trace2,trace3,w2n trace4) =
       smtfp_raw_addsub_trace subtract sx ex fx sy ey fy` by
        (mp_tac smtfp_word_addsub_trace_exact >>
         impl_tac >- asm_rewrite_tac [] >>
         asm_simp_tac pure_ss [pairTheory.pair_case_thm] >>
         DISCH_THEN ACCEPT_TAC) >>
      `0 < w2n trace0 /\ w2n trace0 <= dimword (:'e) - 2` by
        (mp_tac smtfp_raw_addsub_finite_scale_bound >>
         impl_tac >- asm_rewrite_tac [] >>
         qpat_x_assum `(w2n trace0,_,_,_,_) = _`
           (fn th => simp_tac pure_ss [GSYM th,
             pairTheory.pair_case_thm]) >>
         DISCH_THEN ACCEPT_TAC) >>
      `dimindex (:'t) + 2 <= dimindex (:'d)` by
        Omega.OMEGA_TAC >>
      `smtfp_word_addsub subtract mode sx ex fx sy ey fy (:'c) (:'d) =
       if ey = 0w /\ fy = 0w /\ trace4 <> 0w then
         smtfp_bits sx ex fx
       else
         smtfp_word_encode mode
           (if trace4 = 0w then
              smtfp_word_addsub_zero_sign subtract mode sx ex fx sy ey fy
            else trace3)
           (smtfp_bits sx ex fx) trace0 trace4` by
        (qabbrev_tac `fields = smtfp_word_encode_fields mode
           (if trace4 = 0w then
              smtfp_word_addsub_zero_sign subtract mode sx ex fx sy ey fy
            else trace3) (smtfp_bits sx ex fx) trace0 trace4` >>
         PairCases_on `fields` >>
         qpat_x_assum `Abbrev ((fields0,fields1) = _)` mp_tac >>
         simp_tac pure_ss [markerTheory.Abbrev_def] >>
         DISCH_THEN (assume_tac o SYM) >>
         asm_simp_tac pure_ss [smtfp_word_addsub_def,
           smtfp_word_addsub_fields_def, smtfp_word_encode_def,
           LET_THM, pairTheory.pair_case_thm,
           boolTheory.COND_CLAUSES, boolTheory.OR_CLAUSES,
           boolTheory.AND_CLAUSES] >>
         Cases_on `ey = 0w /\ fy = 0w /\ trace4 <> 0w` >>
         asm_simp_tac std_ss [pairTheory.pair_case_thm]) >>
      asm_rewrite_tac [] >>
      simp_tac pure_ss [pairTheory.pair_case_thm] >>
      Cases_on `trace4 = 0w`
      >- asm_simp_tac std_ss [smtfp_word_encode_is_zero] >>
      Cases_on `ey = 0w /\ fy = 0w /\ trace4 <> 0w`
      >- (asm_simp_tac std_ss [smtfp_is_zero_bits] >>
          strip_tac >> CCONTR_TAC >> fs [] >>
          `w2n trace4 <> 0` by metis_tac [wordsTheory.w2n_eq_0] >>
          qpat_x_assum `(w2n trace0,_,_,_,w2n trace4) = _` mp_tac >>
          asm_simp_tac (srw_ss()) [smtfp_raw_addsub_trace_def,
            smtfp_circuit_exp_def, smtfp_circuit_sig_def,
            smtfp_bounded_align_def, smtfp_jam_def,
            smtfp_pair_trace_def, LET_THM,
            pairTheory.pair_case_thm, wordsTheory.w2n_eq_0]) >>
      asm_simp_tac std_ss [smtfp_word_encode_is_zero])
QED

Theorem smtfp_rep_bits_raw_fields[local]:
  ~smtfp_nan_pattern exponent significand ==>
  (smtfp_rep
     (smtfp_bits sign exponent significand : ('t,'e) smtfp)).Sign = sign /\
  (smtfp_rep
     (smtfp_bits sign exponent significand : ('t,'e) smtfp)).Exponent =
    exponent /\
  (smtfp_rep
     (smtfp_bits sign exponent significand : ('t,'e) smtfp)).Significand =
    significand
Proof
  strip_tac >>
  `smtfp_rep (smtfp_bits sign exponent significand : ('t,'e) smtfp) =
   <| Sign := sign; Exponent := exponent; Significand := significand |>` by
    (irule smtfp_rep_bits_raw >> asm_rewrite_tac []) >>
  asm_simp_tac (srw_ss()) []
QED

Theorem smtfp_nan_is_nan[local]:
  smtfp_is_nan (smtfp_nan : ('t,'e) smtfp)
Proof
  simp [smtfp_nan_def, smtfp_is_nan_def, canon_def,
    smtfp_canonical_def]
QED

Theorem smtfp_n2w_not_uint_max[local]:
  n < dimword (:'e) - 1 ==> (n2w n : 'e word) <> UINT_MAXw
Proof
  strip_tac >>
  `0 < dimword (:'e)` by simp [dimword_def] >>
  `n < dimword (:'e)` by Omega.OMEGA_TAC >>
  `dimword (:'e) - 1 < dimword (:'e)` by Omega.OMEGA_TAC >>
  simp [word_T_def, UINT_MAX_def, n2w_11, LESS_MOD] >>
  Omega.OMEGA_TAC
QED

Theorem smtfp_n2w_not_uint_max_le[local]:
  2 < dimword (:'e) /\ n <= dimword (:'e) - 2 ==>
  (n2w n : 'e word) <> UINT_MAXw
Proof
  strip_tac >> irule smtfp_n2w_not_uint_max >> Omega.OMEGA_TAC
QED

Theorem smtfp_circuit_infinity_not_nan[local]:
  ~smtfp_is_nan
    (smtfp_circuit_infinity (format : ('t,'e) smtfp) sign)
Proof
  simp [smtfp_circuit_infinity_def, smtfp_is_nan_bits,
    smtfp_nan_pattern_def]
QED

Theorem smtfp_circuit_top_not_nan[local]:
  2 <= dimindex (:'e) ==>
  ~smtfp_is_nan (smtfp_circuit_top (format : ('t,'e) smtfp) sign)
Proof
  strip_tac >>
  `2 < dimword (:'e)` by
    (simp [dimword_def] >>
     `2 ** 2 <= (2 : num) ** dimindex (:'e)` by
       (irule TWOEXP_MONO2 >> asm_rewrite_tac []) >>
     numLib.ARITH_TAC) >>
  `(n2w (dimword (:'e) - 2) : 'e word) <> UINT_MAXw` by
    (irule smtfp_n2w_not_uint_max >> Omega.OMEGA_TAC) >>
  simp [smtfp_circuit_top_def, smtfp_is_nan_bits,
    smtfp_nan_pattern_def]
QED

Theorem smtfp_circuit_overflow_not_nan[local]:
  2 <= dimindex (:'e) ==>
  ~smtfp_is_nan
    (smtfp_circuit_overflow mode (format : ('t,'e) smtfp) sign)
Proof
  strip_tac >> Cases_on `mode` >>
  simp_tac (srw_ss()) [smtfp_circuit_overflow_def] >>
  rpt IF_CASES_TAC >>
  asm_simp_tac std_ss [smtfp_circuit_infinity_not_nan,
    smtfp_circuit_top_not_nan]
QED

Theorem smtfp_circuit_pack_not_nan[local]:
  2 <= dimindex (:'e) /\ exponent <= dimword (:'e) - 2 ==>
  ~smtfp_is_nan
    (smtfp_circuit_pack mode (format : ('t,'e) smtfp) sign
      (dimword (:'e) - 2) fraction_width exponent rounded)
Proof
  strip_tac >>
  `2 < dimword (:'e)` by
    (simp [dimword_def] >>
     `2 ** 2 <= (2 : num) ** dimindex (:'e)` by
       (irule TWOEXP_MONO2 >> asm_rewrite_tac []) >>
     numLib.ARITH_TAC) >>
  `dimword (:'e) - 2 <> 0` by Omega.OMEGA_TAC >>
  `!n. n <= dimword (:'e) - 2 ==>
      (n2w n : 'e word) <> UINT_MAXw` by
    simp [smtfp_n2w_not_uint_max_le] >>
  asm_simp_tac pure_ss [smtfp_circuit_pack_def, LET_THM] >>
  rpt IF_CASES_TAC >>
  asm_simp_tac std_ss [smtfp_circuit_overflow_not_nan,
    smtfp_is_nan_bits, smtfp_nan_pattern_def] >>
  first_x_assum irule >> Omega.OMEGA_TAC
QED

Theorem smtfp_circuit_encode_not_nan:
  2 <= dimindex (:'e) ==>
  ~smtfp_is_nan
    (smtfp_circuit_encode mode (format : ('t,'e) smtfp)
      sign scale magnitude)
Proof
  strip_tac >>
  simp_tac pure_ss [smtfp_circuit_encode_def] >>
  IF_CASES_TAC
  >- simp [smtfp_is_nan_bits, smtfp_nan_pattern_def] >>
  simp_tac pure_ss [LET_THM] >>
  irule smtfp_circuit_pack_not_nan >>
  asm_simp_tac std_ss [smtfp_circuit_encoded_exponent_def] >>
  `2 <= dimword (:'e)` by
    (simp [dimword_def] >>
     irule LESS_EQ_TRANS >> qexists_tac `(2 : num) ** 2` >>
     simp [EXP_BASE_LE_MONO]) >>
  Omega.OMEGA_TAC
QED

Theorem smtfp_addsub_is_nan_word_fields:
  2 <= dimindex (:'e) /\
  dimindex (:'t) + 5 <= dimindex (:'d) /\
  dimword (:'e) - 2 + dimindex (:'d) <= dimword (:'c) ==>
  (smtfp_is_nan
    (if subtract then
       smtfp_sub mode
         (smtfp_bits sx (ex : 'e word) (fx : 't word))
         (smtfp_bits sy ey fy)
     else
       smtfp_add mode
         (smtfp_bits sx ex fx)
         (smtfp_bits sy ey fy)) <=>
   smtfp_nan_pattern ex fx \/ smtfp_nan_pattern ey fy \/
   ex = UINT_MAXw /\ fx = 0w /\
   ey = UINT_MAXw /\ fy = 0w /\
   sx <> (if subtract then ~sy else sy))
Proof
  strip_tac >>
  `smtfp_word_addsub subtract mode sx ex fx sy ey fy (:'c) (:'d) =
   (if subtract then
      smtfp_sub mode (smtfp_bits sx ex fx) (smtfp_bits sy ey fy)
    else
      smtfp_add mode (smtfp_bits sx ex fx) (smtfp_bits sy ey fy))` by
    (irule smtfp_word_addsub_exact >> asm_rewrite_tac []) >>
  `smtfp_word_addsub subtract mode sx ex fx sy ey fy (:'c) (:'d) =
   smtfp_bounded_addsub_circuit subtract mode
     (smtfp_bits sx ex fx) (smtfp_bits sy ey fy)` by
    (irule smtfp_word_addsub_bounded_exact >> asm_rewrite_tac []) >>
  `((if subtract then
       smtfp_sub mode (smtfp_bits sx ex fx) (smtfp_bits sy ey fy)
     else
       smtfp_add mode (smtfp_bits sx ex fx) (smtfp_bits sy ey fy)) =
    smtfp_bounded_addsub_circuit subtract mode
      (smtfp_bits sx ex fx) (smtfp_bits sy ey fy))` by
    metis_tac [] >>
  pop_assum (fn th => once_rewrite_tac [th]) >>
  Cases_on `smtfp_nan_pattern ex fx`
  >- (asm_simp_tac std_ss [smtfp_bounded_addsub_circuit_def,
        GSYM smtfp_raw_nan_guard, smtfp_nan_is_nan, LET_THM]) >>
  Cases_on `smtfp_nan_pattern ey fy`
  >- (asm_simp_tac std_ss [smtfp_bounded_addsub_circuit_def,
        GSYM smtfp_raw_nan_guard, smtfp_nan_is_nan, LET_THM]) >>
  `smtfp_rep (smtfp_bits sx ex fx : ('t,'e) smtfp) =
   <| Sign := sx; Exponent := ex; Significand := fx |>` by
    (irule smtfp_rep_bits_raw >> asm_rewrite_tac []) >>
  `smtfp_rep (smtfp_bits sy ey fy : ('t,'e) smtfp) =
   <| Sign := sy; Exponent := ey; Significand := fy |>` by
    (irule smtfp_rep_bits_raw >> asm_rewrite_tac []) >>
  Cases_on `ex = UINT_MAXw` >> Cases_on `ey = UINT_MAXw`
  >- (`fx = 0w /\ fy = 0w` by fs [smtfp_nan_pattern_def] >>
      Cases_on `sx = if subtract then ~sy else sy` >>
      asm_simp_tac pure_ss [smtfp_bounded_addsub_circuit_def,
        smtfp_rep_bits_raw_fields, smtfp_circuit_infinity_not_nan,
        smtfp_nan_is_nan, LET_THM, binary_ieeeTheory.float_accfupds,
        combinTheory.K_THM, boolTheory.COND_CLAUSES,
        boolTheory.OR_CLAUSES, boolTheory.AND_CLAUSES] >>
      simp_tac std_ss [smtfp_circuit_infinity_not_nan,
        smtfp_nan_is_nan])
  >- (`fx = 0w` by fs [smtfp_nan_pattern_def] >>
      asm_simp_tac pure_ss [smtfp_bounded_addsub_circuit_def,
        smtfp_rep_bits_raw_fields, smtfp_circuit_infinity_not_nan,
        smtfp_nan_is_nan, LET_THM, binary_ieeeTheory.float_accfupds,
        combinTheory.K_THM, boolTheory.COND_CLAUSES,
        boolTheory.OR_CLAUSES, boolTheory.AND_CLAUSES] >>
      simp_tac std_ss [smtfp_circuit_infinity_not_nan,
        smtfp_nan_is_nan])
  >- (`fy = 0w` by fs [smtfp_nan_pattern_def] >>
      asm_simp_tac pure_ss [smtfp_bounded_addsub_circuit_def,
        smtfp_rep_bits_raw_fields, smtfp_circuit_infinity_not_nan,
        smtfp_nan_is_nan, LET_THM, binary_ieeeTheory.float_accfupds,
        combinTheory.K_THM, boolTheory.COND_CLAUSES,
        boolTheory.OR_CLAUSES, boolTheory.AND_CLAUSES] >>
      simp_tac std_ss [smtfp_circuit_infinity_not_nan,
        smtfp_nan_is_nan]) >>
  `(smtfp_rep (smtfp_bits sx ex fx : ('t,'e) smtfp)).Exponent = ex` by
    metis_tac [smtfp_rep_bits_raw_fields] >>
  `(smtfp_rep (smtfp_bits sy ey fy : ('t,'e) smtfp)).Exponent = ey` by
    metis_tac [smtfp_rep_bits_raw_fields] >>
  `(smtfp_rep (smtfp_bits sx ex fx : ('t,'e) smtfp)).Exponent <>
   UINT_MAXw` by metis_tac [] >>
  `(smtfp_rep (smtfp_bits sy ey fy : ('t,'e) smtfp)).Exponent <>
   UINT_MAXw` by metis_tac [] >>
  `~smtfp_is_nan (smtfp_bits sx ex fx : ('t,'e) smtfp)` by
    asm_simp_tac std_ss [smtfp_is_nan_bits] >>
  asm_simp_tac pure_ss [smtfp_bounded_addsub_circuit_def, LET_THM,
    boolTheory.COND_CLAUSES, boolTheory.OR_CLAUSES,
    boolTheory.AND_CLAUSES] >>
  pairarg_tac >> simp_tac (srw_ss()) [] >>
  Cases_on `ey = 0w /\ fy = 0w /\ magnitude <> 0` >>
  asm_simp_tac std_ss [smtfp_circuit_encode_not_nan,
    pairTheory.pair_case_thm]
QED

val _ = export_theory ();
