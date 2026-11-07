open HolKernel Parse boolLib bossLib wordsLib;
open arithmeticTheory bitTheory wordsTheory;
open smtfloatReplayTheory;

(* Word-level replay primitives with width-independent count semantics. *)

val _ = new_theory "smtfloatReplayWord";

(* SymFPU's five-bit rounding-mode encoding is one-hot in this order. *)
Definition smtfp_cvc_rounding_bits_def:
  smtfp_cvc_rounding_bits mode =
    (if mode = RNE then 1w
     else if mode = RNA then 2w
     else if mode = RTP then 4w
     else if mode = RTN then 8w
     else 16w : 5 word)
End

Definition smtfp_word_jam_def:
  smtfp_word_jam (w : 'a word) d =
    let q = w >>> d in
      if q << d = w \/ word_lsb q then q else q + 1w
End

Definition smtfp_word_lsr_bv_def:
  smtfp_word_lsr_bv (data : 'a word) (amount : 'b word) =
    if dimindex (:'a) < dimword (:'b) then
      if amount <+ (n2w (dimindex (:'a)) : 'b word) then
        data >>>~ (w2w amount : 'a word)
      else 0w
    else data >>>~ (w2w amount : 'a word)
End

Definition smtfp_word_lsl_bv_def:
  smtfp_word_lsl_bv (data : 'a word) (amount : 'b word) =
    if dimindex (:'a) < dimword (:'b) then
      if amount <+ (n2w (dimindex (:'a)) : 'b word) then
        data <<~ (w2w amount : 'a word)
      else 0w
    else data <<~ (w2w amount : 'a word)
End

Theorem smtfp_word_narrow_count[local]:
  w2n (amount : 'b word) < dimindex (:'a) ==>
  w2n (w2w amount : 'a word) = w2n amount
Proof
  strip_tac >>
  `w2n amount < dimword (:'a)` by
    metis_tac [dimindex_lt_dimword, LESS_TRANS] >>
  simp [w2w_def, w2n_n2w, LESS_MOD]
QED

Theorem smtfp_num_div_reconstruct[local]:
  0 < p ==>
  n DIV p * p <= n /\ (n DIV p * p = n <=> n MOD p = 0)
Proof
  strip_tac >>
  `n = n DIV p * p + n MOD p /\ n MOD p < p` by
    (MATCH_MP_TAC (Q.SPEC `p` DIVISION) >> simp []) >>
  Omega.OMEGA_TAC
QED

Theorem smtfp_word_lsr_value[local]:
  (w : 'a word) >>> d = n2w (w2n w DIV 2 ** d)
Proof
  rewrite_tac [GSYM w2n_11, w2n_lsr, w2n_n2w] >>
  `w2n w DIV 2 ** d <= w2n w` by simp [DIV_LESS_EQ] >>
  `w2n w DIV 2 ** d < dimword (:'a)` by
    metis_tac [w2n_lt, LESS_EQ_LESS_TRANS] >>
  simp [LESS_MOD]
QED

Theorem smtfp_word_shift_reconstruct[local]:
  (((w : 'a word) >>> d) << d = w <=> w2n w MOD 2 ** d = 0)
Proof
  `0 < 2 ** d` by simp [] >>
  `w2n w DIV 2 ** d * 2 ** d <= w2n w /\
   (w2n w DIV 2 ** d * 2 ** d = w2n w <=>
    w2n w MOD 2 ** d = 0)` by
    (MATCH_MP_TAC smtfp_num_div_reconstruct >> simp []) >>
  `w2n w DIV 2 ** d * 2 ** d < dimword (:'a)` by
    metis_tac [w2n_lt, LESS_EQ_LESS_TRANS] >>
  `2 ** d * (w2n w DIV 2 ** d) =
   w2n w DIV 2 ** d * 2 ** d` by
    MATCH_ACCEPT_TAC MULT_COMM >>
  `((w >>> d) << d) =
   n2w (w2n w DIV 2 ** d * 2 ** d)` by
    (once_rewrite_tac [smtfp_word_lsr_value] >>
     once_rewrite_tac [WORD_MUL_LSL] >>
     once_rewrite_tac [word_mul_n2w] >>
     asm_rewrite_tac []) >>
  asm_rewrite_tac [] >> eq_tac >> strip_tac
  >- (`w2n (n2w (w2n w DIV 2 ** d * 2 ** d) : 'a word) =
       w2n w` by asm_rewrite_tac [] >>
      `w2n w DIV 2 ** d * 2 ** d = w2n w` by
        metis_tac [w2n_n2w, LESS_MOD] >>
      fs [])
  >- (`w2n w DIV 2 ** d * 2 ** d = w2n w` by fs [] >>
      asm_rewrite_tac [n2w_w2n])
QED

Theorem smtfp_word_lsb_w2n[local]:
  word_lsb (w : 'a word) = ODD (w2n w)
Proof
  `(n2w (w2n w) : 'a word) = w` by
    MATCH_ACCEPT_TAC n2w_w2n >>
  `word_lsb (n2w (w2n w) : 'a word) = ODD (w2n w)` by
    MATCH_ACCEPT_TAC word_lsb_n2w >>
  metis_tac []
QED

Theorem smtfp_word_jam_range[local]:
  smtfp_jam (w2n (w : 'a word)) d < dimword (:'a)
Proof
  `EVEN (dimword (:'a))` by
    simp [dimword_def, EVEN_EXP_IFF, DIMINDEX_GT_0] >>
  simp [smtfp_jam_even_lt] >>
  MATCH_MP_TAC LESS_LESS_EQ_TRANS >> qexists_tac `dimword (:'a)` >>
  simp [LE_MULT_LCANCEL] >> MATCH_ACCEPT_TAC w2n_lt
QED

Theorem smtfp_word_conditional_increment[local]:
  w2n (q : 'a word) +
    (if ~rebuilt /\ EVEN (w2n q) then 1 else 0) < dimword (:'a) ==>
  w2n (if rebuilt \/ word_lsb q then q else q + 1w) =
  w2n q + (if ~rebuilt /\ EVEN (w2n q) then 1 else 0)
Proof
  strip_tac >> Cases_on `rebuilt` >> Cases_on `word_lsb q` >>
  fs [smtfp_word_lsb_w2n, EVEN_ODD] >>
  mp_tac (Q.INST [`a` |-> `q`, `b` |-> `(1w : 'a word)`]
    w2n_add_2) >> simp []
QED

Theorem smtfp_word_jam_exact:
  w2n (smtfp_word_jam (w : 'a word) d) = smtfp_jam (w2n w) d
Proof
  `smtfp_jam (w2n w) d =
   w2n (w >>> d) +
     (if ~((w >>> d) << d = w) /\ EVEN (w2n (w >>> d))
      then 1 else 0)` by
    (simp_tac pure_ss [smtfp_jam_def, LET_THM, w2n_lsr,
       smtfp_word_shift_reconstruct] >>
     REFL_TAC) >>
  simp_tac pure_ss [smtfp_word_jam_def, LET_THM] >>
  first_x_assum (fn th =>
    once_rewrite_tac [th] >>
    MATCH_MP_TAC smtfp_word_conditional_increment >>
    once_rewrite_tac [GSYM th] >>
    MATCH_ACCEPT_TAC smtfp_word_jam_range)
QED

Theorem smtfp_word_lsr_bv_exact:
  smtfp_word_lsr_bv (data : 'a word) (amount : 'b word) =
  data >>> w2n amount
Proof
  Cases_on `dimindex (:'a) < dimword (:'b)`
  >- (`w2n (n2w (dimindex (:'a)) : 'b word) = dimindex (:'a)` by
        simp [w2n_n2w, LESS_MOD] >>
      Cases_on `amount <+ (n2w (dimindex (:'a)) : 'b word)`
      >- (`w2n amount < dimindex (:'a)` by
            metis_tac [WORD_LO] >>
          simp [smtfp_word_lsr_bv_def, word_lsr_bv_def,
            smtfp_word_narrow_count])
      >- (`dimindex (:'a) <= w2n amount` by
            metis_tac [WORD_LO, NOT_LESS] >>
          simp [smtfp_word_lsr_bv_def, LSR_LIMIT]))
  >- (`w2n amount < dimindex (:'a)` by
        (`w2n amount < dimword (:'b)` by
           MATCH_ACCEPT_TAC w2n_lt >>
         Omega.OMEGA_TAC) >>
      simp [smtfp_word_lsr_bv_def, word_lsr_bv_def,
        smtfp_word_narrow_count])
QED

Theorem smtfp_word_lsl_bv_exact:
  smtfp_word_lsl_bv (data : 'a word) (amount : 'b word) =
  data << w2n amount
Proof
  Cases_on `dimindex (:'a) < dimword (:'b)`
  >- (`w2n (n2w (dimindex (:'a)) : 'b word) = dimindex (:'a)` by
        simp [w2n_n2w, LESS_MOD] >>
      Cases_on `amount <+ (n2w (dimindex (:'a)) : 'b word)`
      >- (`w2n amount < dimindex (:'a)` by
            metis_tac [WORD_LO] >>
          simp [smtfp_word_lsl_bv_def, word_lsl_bv_def,
            smtfp_word_narrow_count])
      >- (`dimindex (:'a) <= w2n amount` by
            metis_tac [WORD_LO, NOT_LESS] >>
          simp [smtfp_word_lsl_bv_def, LSL_LIMIT]))
  >- (`w2n amount < dimindex (:'a)` by
        (`w2n amount < dimword (:'b)` by
           MATCH_ACCEPT_TAC w2n_lt >>
         Omega.OMEGA_TAC) >>
      simp [smtfp_word_lsl_bv_def, word_lsl_bv_def,
        smtfp_word_narrow_count])
QED

Definition smtfp_word_jam_bv_def:
  smtfp_word_jam_bv (data : 'a word) (amount : 'b word) =
    let q = smtfp_word_lsr_bv data amount in
    let rebuilt = smtfp_word_lsl_bv q amount in
      if rebuilt = data \/ word_lsb q then q else q + 1w
End

Theorem smtfp_word_jam_bv_exact:
  w2n (smtfp_word_jam_bv (data : 'a word) (amount : 'b word)) =
  smtfp_jam (w2n data) (w2n amount)
Proof
  `smtfp_word_jam_bv data amount =
   smtfp_word_jam data (w2n amount)` by
    simp [smtfp_word_jam_bv_def, smtfp_word_jam_def,
      smtfp_word_lsr_bv_exact, smtfp_word_lsl_bv_exact] >>
  asm_rewrite_tac [smtfp_word_jam_exact]
QED

Definition smtfp_word_priority_def:
  (smtfp_word_priority 0 (w : 'a word) : 'b word = 0w) /\
  (smtfp_word_priority (SUC n) w =
    if word_bit n w then n2w n else smtfp_word_priority n w)
End

(* cvc5 represents an IEEE value during FP bit-blasting by special-value
   flags plus a signed unbiased exponent and a normalized significand.  Keep
   the witness compact while it is substituted through a replay theorem;
   graph replay unfolds these definitions only when checking that witness. *)
Definition smtfp_cvc_unpacked_exponent_def:
  smtfp_cvc_unpacked_exponent special (exponent : 'e word)
      (fraction : 't word) (shape : 'u word) =
    if special then 0w
    else
      let exponent' : 'u word = w2w exponent;
          bias : 'u word = n2w (2 ** (dimindex (:'e) - 1) - 1);
          shift : 'u word =
            n2w (dimindex (:'t)) -
            smtfp_word_priority (dimindex (:'t)) fraction
      in
        if exponent = 0w then 1w - bias - shift
        else exponent' - bias
End

Definition smtfp_cvc_unpacked_significand_def:
  smtfp_cvc_unpacked_significand special (exponent : 'e word)
      (fraction : 't word) (shape : 's word) =
    let canonical : 's word =
          word_concat (1w : word1) (0w : 't word) in
      if special then canonical
      else if exponent = 0w then
        smtfp_word_lsl_bv
          (word_concat (0w : word1) fraction : 's word)
          ((n2w (dimindex (:'t)) : 's word) -
           smtfp_word_priority (dimindex (:'t)) fraction)
      else (word_concat (1w : word1) fraction : 's word)
End

Theorem smtfp_word_priority_zero[local]:
  (smtfp_word_priority n (0w : 'a word) : 'b word) = 0w
Proof
  Induct_on `n` >> simp [smtfp_word_priority_def]
QED

Theorem smtfp_word_bit_w2n[local]:
  i < dimindex (:'a) ==>
  (word_bit i (w : 'a word) <=> BIT i (w2n w))
Proof
  strip_tac >>
  `i <= dimindex (:'a) - 1` by
    (assume_tac DIMINDEX_GT_0 >> Omega.OMEGA_TAC) >>
  mp_tac (Q.SPECL [`i`, `w2n w`]
    (INST_TYPE [alpha |-> ``:'a``] word_bit_n2w)) >> simp []
QED

Theorem smtfp_word_priority_highest[local]:
  L < n /\ word_bit L (w : 'a word) /\
  (!i. L < i /\ i < n ==> ~word_bit i w) ==>
  (smtfp_word_priority n w : 'b word) = n2w L
Proof
  Induct_on `n` >> simp [] >> rpt strip_tac >>
  Cases_on `n = L`
  >- fs [smtfp_word_priority_def]
  >- (`L < n` by Omega.OMEGA_TAC >>
      `~word_bit n w` by
        (first_x_assum MATCH_MP_TAC >> simp []) >>
      simp [smtfp_word_priority_def] >>
      first_x_assum MATCH_MP_TAC >> simp [] >> metis_tac [LESS_TRANS])
QED

Theorem smtfp_word_priority:
  (smtfp_word_priority (dimindex (:'a)) (w : 'a word) : 'b word) =
  if w = 0w then 0w else n2w (bit$LOG2 (w2n w))
Proof
  Cases_on `w = 0w` >> simp [smtfp_word_priority_zero] >>
  irule smtfp_word_priority_highest >>
  `bit$LOG2 (w2n w) < dimindex (:'a)` by
    (`w2n w < dimword (:'a)` by MATCH_ACCEPT_TAC w2n_lt >>
     `w2n w <> 0` by simp [] >>
     fs [dimword_def, bitTheory.LT_TWOEXP]) >>
  rpt strip_tac >>
  fs [smtfp_word_bit_w2n, bitTheory.BIT_LOG2,
    bitTheory.NOT_BIT_GT_LOG2] >>
  `word_bit i w <=> BIT i (w2n w)` by
    (irule smtfp_word_bit_w2n >> simp []) >>
  `~BIT i (w2n w)` by
    (irule bitTheory.NOT_BIT_GT_LOG2 >> simp []) >>
  fs []
QED

Theorem smtfp_word_priority_w2n:
  dimindex (:'a) <= dimword (:'b) ==>
  w2n (smtfp_word_priority (dimindex (:'a))
    (w : 'a word) : 'b word) =
  if w = 0w then 0 else bit$LOG2 (w2n w)
Proof
  strip_tac >> rewrite_tac [smtfp_word_priority] >>
  Cases_on `w = 0w` >> simp [] >>
  `bit$LOG2 (w2n w) < dimindex (:'a)` by
    (`w2n w < dimword (:'a)` by MATCH_ACCEPT_TAC w2n_lt >>
     `w2n w <> 0` by simp [] >>
     fs [dimword_def, bitTheory.LT_TWOEXP]) >>
  simp [w2n_n2w, LESS_MOD]
QED

val _ = export_theory ();
