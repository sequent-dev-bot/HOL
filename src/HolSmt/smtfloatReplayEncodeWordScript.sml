open HolKernel Parse boolLib bossLib wordsLib;
open arithmeticTheory bitTheory wordsTheory;
open smtfloatTheory smtfloatReplayTheory smtfloatReplayWordTheory;

val _ = new_theory "smtfloatReplayEncodeWord";

Definition smtfp_word_encode_exponent_def:
  smtfp_word_encode_exponent (format : ('t,'e) smtfp)
      (scale : 'c word) (data : 'd word) : 'c word =
    let leading =
      (smtfp_word_priority (dimindex (:'d)) data : 'c word) in
    let total = leading + scale in
    let fraction_width = (n2w (dimindex (:'t)) : 'c word) in
    let wanted =
      if total <=+ fraction_width then 1w
      else total - fraction_width in
    let maximum = (n2w (dimword (:'e) - 2) : 'c word) in
      if maximum <+ wanted then maximum else wanted
End

Definition smtfp_word_encode_qrd_def:
  smtfp_word_encode_qrd (scale : 'c word) (exponent : 'c word)
      (data : 'd word) =
    if scale <=+ exponent then
      let shift = exponent - scale in
      let quotient = smtfp_word_lsr_bv data shift in
      let rebuilt = smtfp_word_lsl_bv quotient shift in
      let residue = data - rebuilt in
      let divisor = smtfp_word_lsl_bv (1w : 'd word) shift in
        (quotient, residue, divisor)
    else
      let shift = scale - exponent in
      let quotient = smtfp_word_lsl_bv data shift in
        (quotient, 0w, 1w)
End

Definition smtfp_word_round_up_def:
  smtfp_word_round_up mode (sign : word1) (quotient : 'd word)
      (residue : 'd word) (divisor : 'd word) <=>
    residue <> 0w /\
    let twice = residue << 1 in
    case mode of
      RNE => divisor <+ twice \/
             divisor = twice /\ word_lsb quotient
    | RNA => divisor <=+ twice
    | RTP => sign = 0w
    | RTN => sign = 1w
    | RTZ => F
End

Definition smtfp_word_round_def:
  smtfp_word_round mode sign quotient residue divisor =
    if smtfp_word_round_up mode sign quotient residue divisor then
      quotient + 1w
    else quotient
End

Definition smtfp_word_overflow_fields_def:
  smtfp_word_overflow_fields mode (sign : word1)
      (format : ('t,'e) smtfp) =
    let infinity = (UINT_MAXw : 'e word, 0w : 't word) in
    let top =
      (n2w (dimword (:'e) - 2) : 'e word,
       n2w (2 ** dimindex (:'t) - 1) : 't word) in
    case mode of
      RNE => infinity
    | RNA => infinity
    | RTP => if sign = 0w then infinity else top
    | RTN => if sign = 1w then infinity else top
    | RTZ => top
End

Definition smtfp_word_pack_fields_def:
  smtfp_word_pack_fields mode sign (format : ('t,'e) smtfp)
      (exponent : 'c word) (rounded : 'd word) =
    let lower = (n2w (2 ** dimindex (:'t)) : 'd word) in
    let upper = (n2w (2 ** (dimindex (:'t) + 1)) : 'd word) in
    let maximum = (n2w (dimword (:'e) - 2) : 'c word) in
      if upper <+ rounded then
        smtfp_word_overflow_fields mode sign format
      else if rounded = upper then
        if exponent <+ maximum then
          (w2w (exponent + 1w) : 'e word, 0w : 't word)
        else smtfp_word_overflow_fields mode sign format
      else if rounded <+ lower then
        (0w : 'e word, w2w rounded : 't word)
      else
        (w2w exponent : 'e word, w2w (rounded - lower) : 't word)
End

Definition smtfp_word_encode_fields_def:
  smtfp_word_encode_fields mode sign (format : ('t,'e) smtfp)
      (scale : 'c word) (data : 'd word) =
    if data = 0w then (0w : 'e word, 0w : 't word)
    else
      let exponent = smtfp_word_encode_exponent format scale data in
      let (quotient,residue,divisor) =
        smtfp_word_encode_qrd scale exponent data in
      let rounded =
        smtfp_word_round mode sign quotient residue divisor in
        smtfp_word_pack_fields mode sign format exponent rounded
End

Definition smtfp_word_encode_def:
  smtfp_word_encode mode sign (format : ('t,'e) smtfp)
      (scale : 'c word) (data : 'd word) =
    let (exponent,fraction) =
      smtfp_word_encode_fields mode sign format scale data in
      smtfp_bits sign exponent fraction
End

Theorem smtfp_word_encode_maximum_positive[local]:
  2 <= dimindex (:'e) ==> 1 <= dimword (:'e) - 2
Proof
  strip_tac >>
  `4 <= (2 : num) ** dimindex (:'e)` by
    (`(2 : num) ** 2 <= 2 ** dimindex (:'e)` by
       simp [EXP_BASE_LE_MONO] >>
     fs []) >>
  simp_tac pure_ss [dimword_def] >> Omega.OMEGA_TAC
QED

Theorem smtfp_word_encode_log_bound[local]:
  0 < magnitude /\ magnitude < 2 ** width ==>
  bit$LOG2 magnitude < width
Proof
  simp [bitTheory.LT_TWOEXP]
QED

Theorem smtfp_word_encode_shift_bound[local]:
  0 < magnitude /\ magnitude < 2 ** width /\ 1 <= scale /\
  fraction_width + 2 <= width ==>
  MIN maximum
      (MAX 1 (bit$LOG2 magnitude + scale - fraction_width)) - scale <=
    width - 1 - fraction_width
Proof
  strip_tac >>
  `bit$LOG2 magnitude < width` by
    metis_tac [smtfp_word_encode_log_bound] >>
  simp [MIN_ALT, MAX_ALT] >> rpt IF_CASES_TAC >> Omega.OMEGA_TAC
QED

Theorem smtfp_word_encode_total_bound[local]:
  0 < magnitude /\ magnitude < 2 ** width /\ scale <= maximum /\
  maximum + width <= modulus ==>
  bit$LOG2 magnitude + scale < modulus
Proof
  strip_tac >>
  `bit$LOG2 magnitude < width` by
    metis_tac [smtfp_word_encode_log_bound] >>
  Omega.OMEGA_TAC
QED

Theorem smtfp_word_lsl_value[local]:
  w2n (w : 'a word) * 2 ** amount < dimword (:'a) ==>
  w2n (w << amount) = w2n w * 2 ** amount
Proof
  strip_tac >>
  `(n2w (2 ** amount) : 'a word) *
     n2w (w2n w) = n2w (2 ** amount * w2n w)` by
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

Theorem smtfp_word_increment_value[local]:
  w2n (w : 'a word) + 1 < dimword (:'a) ==>
  w2n (w + 1w) = w2n w + 1
Proof
  strip_tac >>
  `w2n (1w : 'a word) = 1` by simp [w2n_n2w, LESS_MOD] >>
  `w2n (w + 1w) = w2n w + w2n (1w : 'a word)` by
    (MATCH_MP_TAC w2n_add_2 >> asm_rewrite_tac []) >>
  asm_rewrite_tac []
QED

Theorem smtfp_word_exponent_select[local]:
  1 <= fraction_width /\ 1 <= maximum /\
  w2n (leading : 'c word) + w2n scale < dimword (:'c) /\
  fraction_width < dimword (:'c) /\ maximum < dimword (:'c) ==>
  w2n
    (if (n2w maximum : 'c word) <+
          (if leading + scale <=+ n2w fraction_width then 1w
           else leading + scale - n2w fraction_width) then
       n2w maximum
     else if leading + scale <=+ n2w fraction_width then 1w
     else leading + scale - n2w fraction_width) =
  MIN maximum
    (MAX 1 (w2n leading + w2n scale - fraction_width))
Proof
  strip_tac >>
  `w2n (leading + scale) = w2n leading + w2n scale` by
    (MATCH_MP_TAC w2n_add_2 >> simp []) >>
  `w2n (n2w fraction_width : 'c word) = fraction_width` by
    simp [w2n_n2w, LESS_MOD] >>
  `w2n (n2w maximum : 'c word) = maximum` by
    simp [w2n_n2w, LESS_MOD] >>
  `w2n (1w : 'c word) = 1` by
    (`1 < dimword (:'c)` by Omega.OMEGA_TAC >>
     simp [w2n_n2w, LESS_MOD]) >>
  Cases_on `w2n leading + w2n scale <= fraction_width`
  >- (`leading + scale <=+ (n2w fraction_width : 'c word)` by
        metis_tac [WORD_LS] >>
      fs [MIN_ALT, MAX_ALT, WORD_LO])
  >- (`(n2w fraction_width : 'c word) <=+ leading + scale` by
        (simp [WORD_LS] >> Omega.OMEGA_TAC) >>
      `~(leading + scale <=+ (n2w fraction_width : 'c word))` by
        (simp [WORD_LS] >> Omega.OMEGA_TAC) >>
      `w2n (leading + scale - n2w fraction_width : 'c word) =
       w2n (leading + scale) -
         w2n (n2w fraction_width : 'c word)` by
        (MATCH_MP_TAC word_sub_w2n >> simp []) >>
      fs [MIN_ALT, MAX_ALT, WORD_LO] >>
      rpt IF_CASES_TAC >> fs [] >> Omega.OMEGA_TAC)
QED

Theorem smtfp_word_encode_exponent_exact:
  2 <= dimindex (:'e) /\
  dimindex (:'t) + 2 <= dimindex (:'d) /\
  dimword (:'e) - 2 + dimindex (:'d) <= dimword (:'c) /\
  0 < w2n (scale : 'c word) /\
  w2n scale <= dimword (:'e) - 2 /\ data <> (0w : 'd word) ==>
  w2n (smtfp_word_encode_exponent
    (format : ('t,'e) smtfp) scale data) =
  smtfp_circuit_encoded_exponent (dimword (:'e) - 2)
    (dimindex (:'t)) (w2n scale) (w2n data)
Proof
  strip_tac >>
  `w2n data <> 0` by metis_tac [w2n_eq_0] >>
  `0 < w2n data` by Omega.OMEGA_TAC >>
  `w2n data < 2 ** dimindex (:'d)` by
    (mp_tac (INST_TYPE [alpha |-> ``:'d``] w2n_lt) >>
     simp [dimword_def]) >>
  `1 <= dimword (:'e) - 2` by
    metis_tac [smtfp_word_encode_maximum_positive] >>
  `dimindex (:'d) <= dimword (:'c)` by Omega.OMEGA_TAC >>
  `bit$LOG2 (w2n data) + w2n scale < dimword (:'c)` by
    (MATCH_MP_TAC (Q.INST
       [`maximum` |-> `dimword (:'e) - 2`,
        `width` |-> `dimindex (:'d)`]
       smtfp_word_encode_total_bound) >> simp []) >>
  `dimindex (:'t) < dimword (:'c) /\
   dimword (:'e) - 2 < dimword (:'c)` by
    (assume_tac (INST_TYPE [alpha |-> ``:'t``] DIMINDEX_GT_0) >>
     Omega.OMEGA_TAC) >>
  `w2n (smtfp_word_priority (dimindex (:'d)) data : 'c word) =
   bit$LOG2 (w2n data)` by
    simp [smtfp_word_priority_w2n] >>
  `w2n scale +
     w2n (smtfp_word_priority (dimindex (:'d)) data : 'c word) <
   dimword (:'c)` by metis_tac [ADD_COMM] >>
  simp_tac pure_ss [smtfp_word_encode_exponent_def,
    smtfp_circuit_encoded_exponent_def,
    smtfp_circuit_wanted_exponent_def, LET_THM] >>
  qpat_x_assum
    `w2n (smtfp_word_priority (dimindex (:'d)) data : 'c word) = _`
    (fn th => once_rewrite_tac [GSYM th]) >>
  irule (Q.INST
    [`leading` |->
       `(smtfp_word_priority (dimindex (:'d)) data : 'c word)`,
     `fraction_width` |-> `dimindex (:'t)`,
     `maximum` |-> `dimword (:'e) - 2`]
    smtfp_word_exponent_select) >> simp []
QED

Theorem smtfp_word_encode_qrd_values[local]:
  w2n (data : 'd word) *
    2 ** (w2n scale - w2n exponent) < dimword (:'d) /\
  2 ** (w2n exponent - w2n scale) < dimword (:'d) ==>
  case smtfp_word_encode_qrd scale exponent data of
    (quotient,residue,divisor) =>
      w2n quotient =
        (if w2n scale <= w2n exponent then
           w2n data DIV 2 ** (w2n exponent - w2n scale)
         else w2n data * 2 ** (w2n scale - w2n exponent)) /\
      w2n residue =
        (if w2n scale <= w2n exponent then
           w2n data MOD 2 ** (w2n exponent - w2n scale)
         else 0) /\
      w2n divisor = 2 ** (w2n exponent - w2n scale)
Proof
  strip_tac >> `w2n data < dimword (:'d)` by MATCH_ACCEPT_TAC w2n_lt >>
  Cases_on `w2n scale <= w2n exponent`
  >- (`scale <=+ exponent` by simp [WORD_LS] >>
      `w2n (exponent - scale) = w2n exponent - w2n scale` by
        (MATCH_MP_TAC word_sub_w2n >> simp [WORD_LS]) >>
      simp_tac pure_ss [smtfp_word_encode_qrd_def, LET_THM] >>
      asm_rewrite_tac [smtfp_word_lsr_bv_exact, w2n_lsr,
        smtfp_word_lsl_bv_exact] >>
      `w2n data DIV 2 ** (w2n exponent - w2n scale) *
         2 ** (w2n exponent - w2n scale) <= w2n data` by
        (irule dividesTheory.DIV_MULT_LE >> simp []) >>
      `w2n (data >>> (w2n exponent - w2n scale)) *
         2 ** (w2n exponent - w2n scale) < dimword (:'d)` by
        (simp_tac pure_ss [w2n_lsr] >> irule LESS_EQ_LESS_TRANS >>
         qexists_tac `w2n data` >> conj_tac
         >- qpat_x_assum `w2n data < dimword (:'d)` ACCEPT_TAC >>
         qpat_x_assum `w2n data DIV _ * _ <= w2n data` ACCEPT_TAC) >>
      `w2n
         ((data >>> (w2n exponent - w2n scale)) <<
            (w2n exponent - w2n scale)) =
       w2n (data >>> (w2n exponent - w2n scale)) *
         2 ** (w2n exponent - w2n scale)` by
        (MATCH_MP_TAC smtfp_word_lsl_value >> qpat_x_assum
           `w2n (data >>> _) * _ < dimword (:'d)` ACCEPT_TAC) >>
      `w2n
         ((data >>> (w2n exponent - w2n scale)) <<
            (w2n exponent - w2n scale)) =
       w2n data DIV 2 ** (w2n exponent - w2n scale) *
         2 ** (w2n exponent - w2n scale)` by
        asm_rewrite_tac [w2n_lsr] >>
      `((data >>> (w2n exponent - w2n scale)) <<
          (w2n exponent - w2n scale)) <=+ data` by
        (simp_tac pure_ss [WORD_LS] >> metis_tac []) >>
      simp [word_sub_w2n, smtfp_word_lsl_value] >>
      conj_tac >- simp [w2n_lsr] >>
      `w2n data =
       w2n data DIV 2 ** (w2n exponent - w2n scale) *
         2 ** (w2n exponent - w2n scale) +
       w2n data MOD 2 ** (w2n exponent - w2n scale)` by
        simp [DIVISION] >>
      Omega.OMEGA_TAC)
  >- (`exponent <=+ scale` by (simp [WORD_LS] >> Omega.OMEGA_TAC) >>
      `~(scale <=+ exponent)` by (simp [WORD_LS] >> Omega.OMEGA_TAC) >>
      `w2n (scale - exponent) = w2n scale - w2n exponent` by
        (MATCH_MP_TAC word_sub_w2n >> simp []) >>
      simp_tac pure_ss [smtfp_word_encode_qrd_def, LET_THM] >>
      asm_rewrite_tac [smtfp_word_lsl_bv_exact] >>
      simp [smtfp_word_lsl_value])
QED

Theorem smtfp_word_encode_exponent_bounds:
  2 <= dimindex (:'e) /\
  dimindex (:'t) + 2 <= dimindex (:'d) /\
  dimword (:'e) - 2 + dimindex (:'d) <= dimword (:'c) /\
  0 < w2n (word_scale : 'c word) /\
  w2n word_scale <= dimword (:'e) - 2 /\ data <> (0w : 'd word) ==>
  1 <= w2n (smtfp_word_encode_exponent
    (format : ('t,'e) smtfp) word_scale data) /\
  w2n (smtfp_word_encode_exponent format word_scale data) <=
    dimword (:'e) - 2 /\
  w2n (smtfp_word_encode_exponent format word_scale data) -
    w2n word_scale <=
    dimindex (:'d) - 1 - dimindex (:'t)
Proof
  strip_tac >>
  `w2n data <> 0` by metis_tac [w2n_eq_0] >>
  `0 < w2n data /\ w2n data < 2 ** dimindex (:'d)` by
    (conj_tac >- Omega.OMEGA_TAC >>
     mp_tac (INST_TYPE [alpha |-> ``:'d``] w2n_lt) >>
     simp [dimword_def]) >>
  `1 <= dimword (:'e) - 2` by
    metis_tac [smtfp_word_encode_maximum_positive] >>
  `w2n (smtfp_word_encode_exponent
      (format : ('t,'e) smtfp) word_scale data) =
   smtfp_circuit_encoded_exponent (dimword (:'e) - 2)
     (dimindex (:'t)) (w2n word_scale) (w2n data)` by
    (irule smtfp_word_encode_exponent_exact >> simp []) >>
  mp_tac (Q.INST
    [`(maximum_exponent : num)` |-> `dimword (:'e) - 2`,
     `(fraction_width : num)` |-> `dimindex (:'t)`,
     `scale` |-> `w2n (word_scale : 'c word)`,
     `(magnitude : num)` |-> `w2n (data : 'd word)`]
    smtfp_circuit_effective_encoded) >> impl_tac >- simp [] >> strip_tac >>
  asm_rewrite_tac [] >>
  simp_tac pure_ss [smtfp_circuit_encoded_exponent_def,
    smtfp_circuit_wanted_exponent_def] >>
  MATCH_MP_TAC smtfp_word_encode_shift_bound >> simp []
QED

Theorem smtfp_word_encode_storage_bounds[local]:
  2 <= dimindex (:'e) /\
  dimindex (:'t) + 2 <= dimindex (:'d) /\
  0 < scale /\ scale <= dimword (:'e) - 2 /\ 0 < magnitude /\
  magnitude < dimword (:'d) ==>
  2 **
    (smtfp_circuit_encoded_exponent (dimword (:'e) - 2)
       (dimindex (:'t)) scale magnitude - scale) < dimword (:'d) /\
  magnitude * 2 **
    (scale - smtfp_circuit_encoded_exponent (dimword (:'e) - 2)
       (dimindex (:'t)) scale magnitude) < dimword (:'d)
Proof
  strip_tac >>
  `1 <= dimword (:'e) - 2` by
    metis_tac [smtfp_word_encode_maximum_positive] >>
  mp_tac (Q.INST
    [`maximum_exponent` |-> `dimword (:'e) - 2`,
     `fraction_width` |-> `dimindex (:'t)`, `scale` |-> `scale`,
     `magnitude` |-> `magnitude`]
    smtfp_circuit_effective_encoded) >> impl_tac >- simp [] >> strip_tac >>
  `magnitude < 2 ** dimindex (:'d)` by fs [dimword_def] >>
  `smtfp_circuit_encoded_exponent (dimword (:'e) - 2)
       (dimindex (:'t)) scale magnitude - scale < dimindex (:'d)` by
    (simp_tac pure_ss [smtfp_circuit_encoded_exponent_def,
       smtfp_circuit_wanted_exponent_def] >>
     MATCH_MP_TAC LESS_EQ_LESS_TRANS >>
     qexists_tac `dimindex (:'d) - 1 - dimindex (:'t)` >>
     conj_tac >- (MATCH_MP_TAC smtfp_word_encode_shift_bound >> simp []) >>
     assume_tac (INST_TYPE [alpha |-> ``:'t``] DIMINDEX_GT_0) >>
     Omega.OMEGA_TAC) >>
  conj_tac >- fs [dimword_def, EXP_BASE_LT_MONO] >>
  Cases_on `scale <= smtfp_circuit_encoded_exponent (dimword (:'e) - 2)
      (dimindex (:'t)) scale magnitude`
  >- (`scale - smtfp_circuit_encoded_exponent (dimword (:'e) - 2)
         (dimindex (:'t)) scale magnitude = 0` by Omega.OMEGA_TAC >>
      simp []) >>
  `smtfp_circuit_encoded_exponent (dimword (:'e) - 2)
      (dimindex (:'t)) scale magnitude < dimword (:'e) - 2` by
    Omega.OMEGA_TAC >>
  mp_tac (Q.INST
    [`maximum_exponent` |-> `dimword (:'e) - 2`,
     `fraction_width` |-> `dimindex (:'t)`, `scale` |-> `scale`,
     `magnitude` |-> `magnitude`]
    smtfp_circuit_quotient_normalized_upper) >>
  impl_tac >- simp [] >>
  fs [smtfp_circuit_quotient_def, LET_THM] >> strip_tac >>
  `2 ** (dimindex (:'t) + 1) < 2 ** dimindex (:'d)` by
    simp [EXP_BASE_LT_MONO] >>
  irule LESS_TRANS >> qexists_tac `2 ** (dimindex (:'t) + 1)` >>
  conj_tac
  >- qpat_x_assum
       `magnitude *
          2 **
            (scale - smtfp_circuit_encoded_exponent
              (dimword (:'e) - 2) (dimindex (:'t)) scale magnitude) <
        2 ** (dimindex (:'t) + 1)` ACCEPT_TAC >>
  simp [dimword_def]
QED

Theorem smtfp_word_encode_qrd_exact:
  2 <= dimindex (:'e) /\
  dimindex (:'t) + 2 <= dimindex (:'d) /\
  dimword (:'e) - 2 + dimindex (:'d) <= dimword (:'c) /\
  0 < w2n (scale_word : 'c word) /\
  w2n scale_word <= dimword (:'e) - 2 /\ data <> (0w : 'd word) ==>
  case smtfp_word_encode_qrd scale_word
      (smtfp_word_encode_exponent
        (format : ('t,'e) smtfp) scale_word data) data of
    (quotient,residue,divisor) =>
      w2n quotient =
        smtfp_circuit_quotient (dimword (:'e) - 2)
          (dimindex (:'t)) (w2n scale_word) (w2n data) /\
      w2n residue =
        smtfp_circuit_remainder (dimword (:'e) - 2)
          (dimindex (:'t)) (w2n scale_word) (w2n data) /\
      w2n divisor =
        smtfp_circuit_divisor (dimword (:'e) - 2)
          (dimindex (:'t)) (w2n scale_word) (w2n data)
Proof
  strip_tac >>
  `w2n data <> 0` by metis_tac [w2n_eq_0] >>
  `0 < w2n data /\ w2n data < dimword (:'d)` by
    (conj_tac >- Omega.OMEGA_TAC >> MATCH_ACCEPT_TAC w2n_lt) >>
  `1 <= dimword (:'e) - 2` by
    metis_tac [smtfp_word_encode_maximum_positive] >>
  `w2n (smtfp_word_encode_exponent
      (format : ('t,'e) smtfp) scale_word data) =
  smtfp_circuit_encoded_exponent (dimword (:'e) - 2)
     (dimindex (:'t)) (w2n scale_word) (w2n data)` by
    (irule smtfp_word_encode_exponent_exact >> simp []) >>
  `2 **
      (smtfp_circuit_encoded_exponent (dimword (:'e) - 2)
         (dimindex (:'t)) (w2n scale_word) (w2n data) -
       w2n scale_word) < dimword (:'d) /\
   w2n data * 2 **
      (w2n scale_word -
       smtfp_circuit_encoded_exponent (dimword (:'e) - 2)
         (dimindex (:'t)) (w2n scale_word) (w2n data)) < dimword (:'d)` by
    (MATCH_MP_TAC smtfp_word_encode_storage_bounds >> simp []) >>
  `2 **
      (w2n (smtfp_word_encode_exponent format scale_word data) -
       w2n scale_word) < dimword (:'d) /\
   w2n data * 2 **
      (w2n scale_word -
       w2n (smtfp_word_encode_exponent format scale_word data)) <
     dimword (:'d)` by asm_rewrite_tac [] >>
  `smtfp_circuit_effective_exponent (dimword (:'e) - 2)
       (dimindex (:'t)) (w2n scale_word) (w2n data) =
     smtfp_circuit_encoded_exponent (dimword (:'e) - 2)
       (dimindex (:'t)) (w2n scale_word) (w2n data) /\
   1 <= smtfp_circuit_encoded_exponent (dimword (:'e) - 2)
       (dimindex (:'t)) (w2n scale_word) (w2n data) /\
   smtfp_circuit_encoded_exponent (dimword (:'e) - 2)
       (dimindex (:'t)) (w2n scale_word) (w2n data) <=
     dimword (:'e) - 2` by
    (MATCH_MP_TAC smtfp_circuit_effective_encoded >> simp []) >>
  simp_tac pure_ss [smtfp_circuit_quotient_def,
    smtfp_circuit_remainder_def, smtfp_circuit_divisor_def,
    smtfp_circuit_shift_def, LET_THM] >>
  asm_rewrite_tac [] >>
  qpat_x_assum
    `w2n (smtfp_word_encode_exponent _ scale_word data) = _`
    (fn th => rewrite_tac [GSYM th]) >>
  irule smtfp_word_encode_qrd_values >> asm_rewrite_tac []
QED

Theorem smtfp_word_encode_lsb[local]:
  word_lsb (w : 'a word) = ODD (w2n w)
Proof
  `(n2w (w2n w) : 'a word) = w` by MATCH_ACCEPT_TAC n2w_w2n >>
  `word_lsb (n2w (w2n w) : 'a word) = ODD (w2n w)` by
    MATCH_ACCEPT_TAC word_lsb_n2w >>
  metis_tac []
QED

Theorem smtfp_word_round_up_exact[local]:
  2 * w2n (residue : 'd word) < dimword (:'d) ==>
  smtfp_word_round_up mode sign quotient residue divisor =
  smtfp_circuit_round_up mode sign (w2n quotient)
    (w2n residue) (w2n divisor)
Proof
  strip_tac >>
  `(2 : num) ** 1 = 2` by simp [] >>
  `w2n residue * 2 = 2 * w2n residue` by
    MATCH_ACCEPT_TAC MULT_COMM >>
  `w2n (residue << 1) = w2n residue * 2 ** 1` by
    (MATCH_MP_TAC smtfp_word_lsl_value >> asm_rewrite_tac []) >>
  `w2n (residue << 1) = 2 * w2n residue` by
    metis_tac [] >>
  `word_lsb quotient = ODD (w2n quotient)` by
    MATCH_ACCEPT_TAC smtfp_word_encode_lsb >>
  `(residue <> 0w) = (w2n residue <> 0)` by
    metis_tac [w2n_eq_0] >>
  `(divisor <+ residue << 1) =
   (w2n divisor < 2 * w2n residue)` by simp [WORD_LO] >>
  `(divisor <=+ residue << 1) =
   (w2n divisor <= 2 * w2n residue)` by simp [WORD_LS] >>
  `(divisor = residue << 1) =
   (w2n divisor = 2 * w2n residue)` by metis_tac [w2n_11] >>
  simp_tac pure_ss [smtfp_word_round_up_def,
    smtfp_circuit_round_up_def, LET_THM] >>
  asm_rewrite_tac [] >>
  Cases_on `mode` >> REFL_TAC
QED

Theorem smtfp_word_round_exact:
  2 * w2n (residue : 'd word) < dimword (:'d) /\
  smtfp_circuit_round mode sign (w2n quotient)
      (w2n residue) (w2n divisor) < dimword (:'d) ==>
  w2n (smtfp_word_round mode sign quotient residue divisor) =
  smtfp_circuit_round mode sign (w2n quotient)
    (w2n residue) (w2n divisor)
Proof
  strip_tac >>
  `smtfp_word_round_up mode sign quotient residue divisor =
   smtfp_circuit_round_up mode sign (w2n quotient)
     (w2n residue) (w2n divisor)` by
    (MATCH_MP_TAC smtfp_word_round_up_exact >> simp []) >>
  simp_tac pure_ss [smtfp_word_round_def, smtfp_circuit_round_def] >>
  asm_rewrite_tac [] >>
  Cases_on `smtfp_circuit_round_up mode sign (w2n quotient)
    (w2n residue) (w2n divisor)` >> simp [] >>
  `w2n quotient + 1 < dimword (:'d)` by
    fs [smtfp_circuit_round_def] >>
  `w2n (quotient + 1w) = w2n quotient + 1` by
    (MATCH_MP_TAC smtfp_word_increment_value >> simp []) >>
  asm_rewrite_tac []
QED

Theorem smtfp_circuit_round_div_mod_le[local]:
  0 < divisor ==>
  smtfp_circuit_round mode sign (magnitude DIV divisor)
      (magnitude MOD divisor) divisor <= magnitude
Proof
  strip_tac >>
  `magnitude = magnitude DIV divisor * divisor +
      magnitude MOD divisor /\ magnitude MOD divisor < divisor` by
    simp [DIVISION] >>
  Cases_on `smtfp_circuit_round_up mode sign (magnitude DIV divisor)
    (magnitude MOD divisor) divisor`
  >- (`magnitude MOD divisor <> 0` by
        fs [smtfp_circuit_round_up_def] >>
      `0 < magnitude /\ 1 < divisor` by Omega.OMEGA_TAC >>
      `magnitude DIV divisor < magnitude` by simp [DIV_LESS] >>
      simp [smtfp_circuit_round_def] >> Omega.OMEGA_TAC)
  >- (simp [smtfp_circuit_round_def] >>
      MATCH_MP_TAC DIV_LESS_EQ >> simp [])
QED

Theorem smtfp_word_twice_pow_bound[local]:
  (value : num) < (2 : num) ** shift /\ shift < width ==>
  2 * value < (2 : num) ** width
Proof
  strip_tac >>
  `2 * value < 2 * (2 : num) ** shift` by
    (rewrite_tac [LT_MULT_LCANCEL] >> conj_tac >- simp [] >>
     first_assum ACCEPT_TAC) >>
  `(2 : num) ** (shift + 1) = 2 * 2 ** shift` by
    simp [GSYM ADD1, EXP] >>
  `shift + 1 <= width` by Omega.OMEGA_TAC >>
  `(2 : num) ** (shift + 1) <= 2 ** width` by
    (mp_tac (Q.SPEC `(2 : num)` EXP_BASE_LE_MONO) >>
     impl_tac >- simp [] >>
     disch_then (qspecl_then [`width`, `shift + 1`]
       (fn th => rewrite_tac [th])) >>
     qpat_x_assum `shift + 1 <= width` ACCEPT_TAC) >>
  irule LESS_LESS_EQ_TRANS >>
  qexists_tac `(2 : num) ** (shift + 1)` >>
  asm_rewrite_tac []
QED

Theorem smtfp_word_twice_mod_pow_bound[local]:
  shift < width ==>
  2 * ((value : num) MOD (2 : num) ** shift) < 2 ** width
Proof
  strip_tac >>
  MATCH_MP_TAC smtfp_word_twice_pow_bound >>
  simp [MOD_LESS]
QED

Theorem smtfp_word_encode_round_storage_bounds[local]:
  2 <= dimindex (:'e) /\ dimindex (:'t) + 2 <= dimindex (:'d) /\
  0 < scale /\ scale <= dimword (:'e) - 2 /\
  0 < magnitude /\ magnitude < dimword (:'d) ==>
  2 * smtfp_circuit_remainder (dimword (:'e) - 2)
      (dimindex (:'t)) scale magnitude < dimword (:'d) /\
  smtfp_circuit_rounded mode sign (dimword (:'e) - 2)
      (dimindex (:'t)) scale magnitude < dimword (:'d)
Proof
  strip_tac >> `1 <= dimword (:'e) - 2` by
    metis_tac [smtfp_word_encode_maximum_positive] >>
  `magnitude < 2 ** dimindex (:'d)` by fs [dimword_def] >>
  mp_tac (Q.INST [`maximum_exponent` |-> `dimword (:'e) - 2`,
     `fraction_width` |-> `dimindex (:'t)`, `scale` |-> `scale`,
     `magnitude` |-> `magnitude`]
    smtfp_circuit_effective_encoded) >> impl_tac >- simp [] >> strip_tac >>
  `smtfp_circuit_encoded_exponent (dimword (:'e) - 2)
      (dimindex (:'t)) scale magnitude - scale < dimindex (:'d)` by
    (simp_tac pure_ss [smtfp_circuit_encoded_exponent_def,
       smtfp_circuit_wanted_exponent_def] >>
     MATCH_MP_TAC LESS_EQ_LESS_TRANS >>
     qexists_tac `dimindex (:'d) - 1 - dimindex (:'t)` >> conj_tac
     >- (MATCH_MP_TAC smtfp_word_encode_shift_bound >> simp []) >>
     assume_tac (INST_TYPE [alpha |-> ``:'t``] DIMINDEX_GT_0) >>
     Omega.OMEGA_TAC) >>
  `2 **
      (smtfp_circuit_encoded_exponent (dimword (:'e) - 2)
         (dimindex (:'t)) scale magnitude - scale) < dimword (:'d) /\
   magnitude * 2 **
      (scale - smtfp_circuit_encoded_exponent (dimword (:'e) - 2)
         (dimindex (:'t)) scale magnitude) < dimword (:'d)` by
    (MATCH_MP_TAC smtfp_word_encode_storage_bounds >> simp []) >>
  conj_tac
  >- (simp_tac pure_ss [smtfp_circuit_remainder_def,
        smtfp_circuit_divisor_def, smtfp_circuit_shift_def, LET_THM] >>
      asm_rewrite_tac [] >> IF_CASES_TAC
      >- (`2 *
             (magnitude MOD
               2 **
                 (smtfp_circuit_encoded_exponent (dimword (:'e) - 2)
                   (dimindex (:'t)) scale magnitude - scale)) <
          2 ** dimindex (:'d)` by
            (MATCH_MP_TAC smtfp_word_twice_mod_pow_bound >>
             qpat_x_assum `smtfp_circuit_encoded_exponent _ _ _ _ - scale <
                  dimindex (:'d)` ACCEPT_TAC) >>
          `dimword (:'d) = 2 ** dimindex (:'d)` by simp [dimword_def] >>
          metis_tac []) >>
      simp []) >>
  simp_tac pure_ss [smtfp_circuit_rounded_def,
    smtfp_circuit_quotient_def, smtfp_circuit_remainder_def,
    smtfp_circuit_divisor_def, smtfp_circuit_shift_def, LET_THM] >>
  asm_rewrite_tac [] >> IF_CASES_TAC
  >- (MATCH_MP_TAC LESS_EQ_LESS_TRANS >> qexists_tac `magnitude` >>
      conj_tac >- (simp [] >> MATCH_MP_TAC smtfp_circuit_round_div_mod_le >>
          simp []) >>
      simp []) >>
  asm_rewrite_tac [smtfp_circuit_round_exact]
QED

Theorem smtfp_word_encode_round_exact:
  2 <= dimindex (:'e) /\
  dimindex (:'t) + 2 <= dimindex (:'d) /\
  dimword (:'e) - 2 + dimindex (:'d) <= dimword (:'c) /\
  0 < w2n (scale_word : 'c word) /\
  w2n scale_word <= dimword (:'e) - 2 /\ data <> (0w : 'd word) ==>
  case smtfp_word_encode_qrd scale_word
      (smtfp_word_encode_exponent
        (format : ('t,'e) smtfp) scale_word data) data of
    (quotient,residue,divisor) =>
      w2n (smtfp_word_round mode sign quotient residue divisor) =
      smtfp_circuit_rounded mode sign (dimword (:'e) - 2)
        (dimindex (:'t)) (w2n scale_word) (w2n data)
Proof
  strip_tac >>
  `case smtfp_word_encode_qrd scale_word
      (smtfp_word_encode_exponent format scale_word data) data of
     (quotient,residue,divisor) =>
       w2n quotient =
         smtfp_circuit_quotient (dimword (:'e) - 2) (dimindex (:'t))
           (w2n scale_word) (w2n data) /\
       w2n residue =
         smtfp_circuit_remainder (dimword (:'e) - 2) (dimindex (:'t))
           (w2n scale_word) (w2n data) /\
       w2n divisor =
         smtfp_circuit_divisor (dimword (:'e) - 2) (dimindex (:'t))
           (w2n scale_word) (w2n data)` by
    (irule smtfp_word_encode_qrd_exact >> simp []) >>
  qabbrev_tac `qrd = smtfp_word_encode_qrd scale_word
    (smtfp_word_encode_exponent format scale_word data) data` >>
  PairCases_on `qrd` >> fs [] >>
  `2 * w2n qrd1 < dimword (:'d) /\
   smtfp_circuit_round mode sign (w2n qrd0) (w2n qrd1) (w2n qrd2) <
     dimword (:'d)` by
    (qsuff_tac
       `2 * smtfp_circuit_remainder (dimword (:'e) - 2)
           (dimindex (:'t)) (w2n scale_word) (w2n data) < dimword (:'d) /\
        smtfp_circuit_rounded mode sign (dimword (:'e) - 2)
           (dimindex (:'t)) (w2n scale_word) (w2n data) < dimword (:'d)`
     >- simp [smtfp_circuit_rounded_def] >>
     `w2n data <> 0` by metis_tac [w2n_eq_0] >>
     `0 < w2n data` by Omega.OMEGA_TAC >>
     `w2n data < dimword (:'d)` by MATCH_ACCEPT_TAC w2n_lt >>
     MATCH_MP_TAC smtfp_word_encode_round_storage_bounds >> simp []) >>
  MATCH_MP_TAC EQ_TRANS >>
  qexists_tac
    `smtfp_circuit_round mode sign (w2n qrd0) (w2n qrd1) (w2n qrd2)` >>
  conj_tac >- (MATCH_MP_TAC smtfp_word_round_exact >> simp []) >>
  simp [smtfp_circuit_rounded_def]
QED

Theorem smtfp_word_overflow_fields_exact:
  case smtfp_word_overflow_fields mode sign
      (format : ('t,'e) smtfp) of
    (exponent,fraction) =>
      smtfp_bits sign exponent fraction =
      smtfp_circuit_overflow mode format sign
Proof
  simp_tac pure_ss [smtfp_word_overflow_fields_def,
    smtfp_circuit_overflow_def, smtfp_circuit_infinity_def,
    smtfp_circuit_top_def, LET_THM] >>
  Cases_on `mode` >> simp [] >> rpt IF_CASES_TAC >> fs []
QED

Theorem smtfp_word_pack_fields_exact:
  2 <= dimindex (:'e) /\
  dimindex (:'t) + 2 <= dimindex (:'d) /\
  dimword (:'e) - 2 < dimword (:'c) ==>
  case smtfp_word_pack_fields mode sign (format : ('t,'e) smtfp)
      (exponent : 'c word) (rounded : 'd word) of
    (encoded,fraction) =>
      smtfp_bits sign encoded fraction =
      smtfp_circuit_pack mode format sign (dimword (:'e) - 2)
        (dimindex (:'t)) (w2n exponent) (w2n rounded)
Proof
  strip_tac >> `1 <= dimword (:'e) - 2` by
    metis_tac [smtfp_word_encode_maximum_positive] >>
  `2 ** dimindex (:'t) < dimword (:'d) /\
   2 ** (dimindex (:'t) + 1) < dimword (:'d)` by
    (simp [dimword_def, EXP_BASE_LT_MONO]) >>
  `w2n (n2w (2 ** dimindex (:'t)) : 'd word) =
     2 ** dimindex (:'t) /\ w2n
       (n2w (2 ** (dimindex (:'t) + 1)) : 'd word) =
     2 ** (dimindex (:'t) + 1) /\
   w2n (n2w (dimword (:'e) - 2) : 'c word) = dimword (:'e) - 2` by
    simp [w2n_n2w, LESS_MOD] >>
  `(rounded = (n2w (2 ** (dimindex (:'t) + 1)) : 'd word)) =
     (w2n rounded = 2 ** (dimindex (:'t) + 1))` by metis_tac [w2n_11] >>
  `dimword (:'e) - 2 <> 0` by Omega.OMEGA_TAC >>
  simp_tac pure_ss [smtfp_word_pack_fields_def,
    smtfp_circuit_pack_def, LET_THM] >>
  simp_tac pure_ss [WORD_LO] >> asm_rewrite_tac [] >> IF_CASES_TAC
  >- (asm_rewrite_tac [] >> MATCH_ACCEPT_TAC
        smtfp_word_overflow_fields_exact) >>
  asm_rewrite_tac [] >> IF_CASES_TAC
  >- (asm_rewrite_tac [] >> IF_CASES_TAC
      >- (asm_rewrite_tac [] >>
          `w2n exponent + 1 < dimword (:'c)` by Omega.OMEGA_TAC >>
          `w2n (exponent + 1w) = w2n exponent + 1` by
            (MATCH_MP_TAC smtfp_word_increment_value >>
             asm_rewrite_tac []) >>
          asm_simp_tac pure_ss [pairTheory.pair_case_thm,
            boolTheory.COND_CLAUSES, w2w_def] >> REFL_TAC)
      >- (asm_rewrite_tac [] >> MATCH_ACCEPT_TAC
            smtfp_word_overflow_fields_exact)) >>
  asm_rewrite_tac [] >> IF_CASES_TAC
  >- (asm_simp_tac pure_ss [pairTheory.pair_case_thm,
        boolTheory.COND_CLAUSES, w2w_def] >> REFL_TAC) >>
  asm_rewrite_tac [] >>
  `w2n (n2w (2 ** dimindex (:'t)) : 'd word) <= w2n rounded` by
    Omega.OMEGA_TAC >>
  `w2n (rounded - n2w (2 ** dimindex (:'t)) : 'd word) =
     w2n rounded - 2 ** dimindex (:'t)` by
    (qsuff_tac
       `w2n (rounded - n2w (2 ** dimindex (:'t)) : 'd word) =
        w2n rounded - w2n (n2w (2 ** dimindex (:'t)) : 'd word)`
     >- asm_rewrite_tac [] >>
     MATCH_MP_TAC word_sub_w2n >> asm_simp_tac std_ss [WORD_LS]) >>
  asm_simp_tac pure_ss [pairTheory.pair_case_thm,
    boolTheory.COND_CLAUSES, w2w_def] >> REFL_TAC
QED

Theorem smtfp_word_encode_fields_exact:
  2 <= dimindex (:'e) /\
  dimindex (:'t) + 2 <= dimindex (:'d) /\
  dimword (:'e) - 2 + dimindex (:'d) <= dimword (:'c) /\
  0 < w2n (scale_word : 'c word) /\
  w2n scale_word <= dimword (:'e) - 2 ==>
  case smtfp_word_encode_fields mode sign (format : ('t,'e) smtfp)
      scale_word (data : 'd word) of
    (exponent,fraction) =>
      smtfp_bits sign exponent fraction =
      smtfp_circuit_encode mode format sign (w2n scale_word) (w2n data)
Proof
  strip_tac >> Cases_on `data = 0w`
  >- (asm_simp_tac std_ss [smtfp_word_encode_fields_def,
        smtfp_circuit_encode_def, pairTheory.pair_case_thm,
        w2n_eq_0] >> REFL_TAC) >>
  `w2n data <> 0` by metis_tac [w2n_eq_0] >>
  `w2n (smtfp_word_encode_exponent format scale_word data) =
   smtfp_circuit_encoded_exponent (dimword (:'e) - 2)
     (dimindex (:'t)) (w2n scale_word) (w2n data)` by
    (irule smtfp_word_encode_exponent_exact >> simp []) >>
  `case smtfp_word_encode_qrd scale_word
      (smtfp_word_encode_exponent format scale_word data) data of
     (quotient,residue,divisor) =>
       w2n (smtfp_word_round mode sign quotient residue divisor) =
       smtfp_circuit_rounded mode sign (dimword (:'e) - 2)
         (dimindex (:'t)) (w2n scale_word) (w2n data)` by
    (irule smtfp_word_encode_round_exact >> simp []) >>
  simp_tac pure_ss [smtfp_word_encode_fields_def,
    smtfp_circuit_encode_def, LET_THM] >> asm_rewrite_tac [] >>
  qabbrev_tac `qrd = smtfp_word_encode_qrd scale_word
    (smtfp_word_encode_exponent format scale_word data) data` >>
  PairCases_on `qrd` >> fs [] >>
  `dimword (:'e) - 2 < dimword (:'c)` by
    (assume_tac (INST_TYPE [alpha |-> ``:'d``] DIMINDEX_GT_0) >>
     Omega.OMEGA_TAC) >>
  `case smtfp_word_pack_fields mode sign format
       (smtfp_word_encode_exponent format scale_word data)
       (smtfp_word_round mode sign qrd0 qrd1 qrd2) of
     (encoded,fraction) =>
       smtfp_bits sign encoded fraction =
       smtfp_circuit_pack mode format sign (dimword (:'e) - 2)
         (dimindex (:'t))
         (w2n (smtfp_word_encode_exponent format scale_word data))
         (w2n (smtfp_word_round mode sign qrd0 qrd1 qrd2))` by
    (irule smtfp_word_pack_fields_exact >> simp []) >>
  qpat_x_assum `case smtfp_word_pack_fields _ _ _ _ _ of _ => _` mp_tac >>
  asm_rewrite_tac []
QED

Theorem smtfp_word_encode_exact:
  2 <= dimindex (:'e) /\
  dimindex (:'t) + 2 <= dimindex (:'d) /\
  dimword (:'e) - 2 + dimindex (:'d) <= dimword (:'c) /\
  0 < w2n (scale_word : 'c word) /\
  w2n scale_word <= dimword (:'e) - 2 ==>
  smtfp_word_encode mode sign (format : ('t,'e) smtfp)
      scale_word (data : 'd word) =
  smtfp_circuit_encode mode format sign (w2n scale_word) (w2n data)
Proof
  strip_tac >>
  simp_tac pure_ss [smtfp_word_encode_def, LET_THM] >>
  qabbrev_tac `fields = smtfp_word_encode_fields mode sign format
    scale_word data` >>
  PairCases_on `fields` >> fs [] >>
  `case smtfp_word_encode_fields mode sign format scale_word data of
     (exponent,fraction) =>
       smtfp_bits sign exponent fraction =
       smtfp_circuit_encode mode format sign
         (w2n scale_word) (w2n data)` by
    (irule smtfp_word_encode_fields_exact >> simp []) >>
  qpat_x_assum `case _ of _ => _` mp_tac >>
  qpat_x_assum `_ = (fields0,fields1)`
    (fn th => rewrite_tac [th]) >> simp []
QED

val _ = export_theory ();
