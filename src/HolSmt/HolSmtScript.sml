(* Copyright (c) 2009-2010 Tjark Weber. All rights reserved. *)

(* Various theorems for HolSmtLib *)
Theory HolSmt
Ancestors[qualified]
  bool realax real intreal integer combin words rich_list
Libs realLib

  val op >> = Tactical.>>

  val T = tautLib.TAUT_PROVE
  val P = bossLib.PROVE []
  val S = simpLib.SIMP_PROVE (simpLib.++ (simpLib.++ (simpLib.++
    (bossLib.list_ss, boolSimps.COND_elim_ss), wordsLib.WORD_ss),
    wordsLib.WORD_BIT_EQ_ss)) [boolTheory.EQ_SYM_EQ]
  val A = intLib.ARITH_PROVE
  val R = RealArith.REAL_ARITH
  val W = wordsLib.WORD_DECIDE
  val B = blastLib.BBLAST_PROVE
  val M = bossLib.METIS_PROVE
  val I = simpLib.SIMP_PROVE (simpLib.++ (simpLib.++
    (bossLib.arith_ss, intSimps.INT_RWTS_ss), intSimps.INT_ARITH_ss))

  (* simplify 't' using 'thms', then prove the simplified term using
     'TAUT_PROVE' *)
  fun U thms t =
  let
    val t_eq_t' = simpLib.SIMP_CONV (simpLib.++ (simpLib.++ (simpLib.++
      (bossLib.std_ss, boolSimps.COND_elim_ss), wordsLib.WORD_ss),
      wordsLib.WORD_BIT_EQ_ss)) thms t
    val t' = tautLib.TAUT_PROVE (boolSyntax.rhs (Thm.concl t_eq_t'))
  in
    Thm.EQ_MP (Thm.SYM t_eq_t') t'
  end

  val s = Theory.save_thm

  val _ = ParseExtras.temp_loose_equality()

(* Canonical polarity for conditionals.  This theorem is intentionally
   polymorphic: checked replay uses it below quantified formulas in every
   supported theory. *)
Theorem COND_NEG:
  (if ~p then x else y) = if p then y else x
Proof
  Cases_on `p` >> simp []
QED

  (* constants used by Z3 *)

  (* real division -- in SMT-LIB, division by zero is not defined,
     unlike in HOL4 *)
  val smt_rdiv_exists = P ``?f. !x y. (y <> 0r) ==> (f x y = x / y)``
  val smt_rdiv_def = bossLib.new_specification ("smt_rdiv", ["smt_rdiv"],
    smt_rdiv_exists)

  val _ = s ("real_div_smt_rdiv", M [realaxTheory.real_div,
    realTheory.REAL_INV_0, realTheory.REAL_MUL_RZERO, smt_rdiv_def]
    ``!x y. x / y = if y = 0 then 0 else smt_rdiv x y``)

Theorem smt_rdiv_zero:
  !y. y <> 0r ==> (smt_rdiv 0r y = 0r)
Proof
  simp [smt_rdiv_def, realTheory.REAL_DIV_LZERO]
QED

(* The solver-side division interface agrees with HOL division exactly away
   from zero.  Export this directional form for proof replayers, which must
   never unfold the unconstrained zero-divisor branch. *)
Theorem smt_rdiv_eq_div:
  !x y. y <> 0r ==> (smt_rdiv x y = x / y)
Proof
  simp [smt_rdiv_def]
QED

Theorem smt_rdiv_refl:
    !x. x <> 0r ==> (smt_rdiv x x = 1r)
Proof
    simp [smt_rdiv_def, realTheory.REAL_DIV_REFL]
QED

Theorem smt_rdiv_one:
    !x. smt_rdiv x 1r = x
Proof
    simp [smt_rdiv_def, realaxTheory.real_div,
          realTheory.REAL_INV_1, realTheory.REAL_MUL_RID]
QED

Theorem smt_rdiv_neg_refl:
    !x. x <> 0r ==> (smt_rdiv x (-x) = -1r)
Proof
    simp [smt_rdiv_def, realTheory.REAL_DIV_REFL,
          realTheory.REAL_DIV_RNEG]
QED

Theorem smt_rdiv_neg_one:
  !x. smt_rdiv x (-1r) = -x
Proof
  simp [smt_rdiv_def, realTheory.REAL_DIV_RNEG,
        realaxTheory.real_div, realTheory.REAL_INV_1]
QED

(* Sign normalization for totalized SMT division.  These are guarded exactly
   where the specification agrees with HOL division, so they are useful
   replay lemmas without assigning a meaning to division by zero. *)
Theorem smt_rdiv_lneg:
  !x y. y <> 0r ==> (smt_rdiv (-x) y = -smt_rdiv x y)
Proof
  simp [smt_rdiv_def, realTheory.REAL_DIV_LNEG]
QED

Theorem smt_rdiv_rneg:
  !x y. y <> 0r ==> (smt_rdiv x (-y) = -smt_rdiv x y)
Proof
  simp [smt_rdiv_def, realTheory.REAL_DIV_RNEG]
QED

(* Z3 represents inverse by this explicit totalization.  This boundary
   lemma identifies that macro with HOL's total inverse, including at zero. *)
Theorem smt_rinv_def:
  !x. (if x = 0r then 0r else 1r / x) = realinv x
Proof
  rw [GSYM realTheory.REAL_INV_1OVER] >>
  Cases_on `x = 0r` >> simp [realTheory.REAL_INV_0]
QED

(* SMT sequence access is specified only for in-range indices.  This
   polymorphic choice is deliberately introduced by specification, rather
   than defining an out-of-range value: the latter is solver-underspecified.
   It is the list counterpart of smtstringz3Theory.seq_nth_i. *)
Theorem smt_seq_nth_exists[local]:
  ?f : 'a list -> int -> 'a.
    !s i. (0 <= i /\ Num i < LENGTH s) ==>
      (f s i = EL (Num i) s)
Proof
  qexists `\s i.
    if 0 <= i /\ Num i < LENGTH s then EL (Num i) s else @x. T` >>
  simp []
QED

val smt_seq_nth_spec =
  new_specification
    ("smt_seq_nth_spec", ["smt_seq_nth"], smt_seq_nth_exists);

Theorem smt_seq_nth_def = smt_seq_nth_spec

(* Generic list counterparts of the shared SMT sequence operations whose
   semantics are not a single stock list constant. *)
Definition smt_seq_extract_def:
  smt_seq_extract (s : 'a list) (i : int) (n : int) =
    if i < 0 \/ n <= 0 \/ LENGTH s <= Num i then []
    else TAKE (Num n) (DROP (Num i) s)
End

Theorem smt_seq_extract_empty_start[local]:
  &(LENGTH (s : 'a list)) <= i ==> (smt_seq_extract s i n = [])
Proof
  rw [smt_seq_extract_def] >>
  `LENGTH s <= Num i` by intLib.ARITH_TAC >>
  simp []
QED

Theorem smt_seq_extract_empty_start_neg[local]:
  i < 0 ==> (smt_seq_extract (s : 'a list) i n = [])
Proof
  simp [smt_seq_extract_def]
QED

(* CPC's Seq dictionary exposes the defining conditional directly.  These
   body-form corollaries let replay consume the same checked bounds without
   depending on the surface spelling retained by a parser occurrence. *)
Theorem smt_seq_extract_body_empty_start:
  &(LENGTH (s : 'a list)) <= i ==>
  ((if i < 0 \/ n <= 0 \/ LENGTH s <= Num i then []
    else TAKE (Num n) (DROP (Num i) s)) = [])
Proof
  rw [] >>
  `LENGTH s <= Num i` by intLib.ARITH_TAC >>
  simp []
QED

Theorem smt_seq_extract_body_empty_start_neg:
  i < 0 ==>
  ((if i < 0 \/ n <= 0 \/ LENGTH (s : 'a list) <= Num i then []
    else TAKE (Num n) (DROP (Num i) s)) = [])
Proof
  simp []
QED

Theorem smt_seq_extract_nested_empty_start[local]:
  m1 <= n2 ==>
  (smt_seq_extract (smt_seq_extract (s : 'a list) n1 m1) n2 m2 = [])
Proof
  rw [smt_seq_extract_def] >>
  `Num m1 <= Num n2` by intLib.ARITH_TAC >>
  simp [listTheory.LENGTH_TAKE_EQ]
QED

Theorem smt_seq_extract_body_nested_empty_start:
  m1 <= n2 ==>
  ((if
      n2 < 0 \/ m2 <= 0 \/
      LENGTH
        (if n1 < 0 \/ m1 <= 0 \/ LENGTH (s : 'a list) <= Num n1 then
           []
         else TAKE (Num m1) (DROP (Num n1) s)) <= Num n2
    then []
    else
      TAKE (Num m2)
        (DROP (Num n2)
          (if n1 < 0 \/ m1 <= 0 \/ LENGTH s <= Num n1 then []
           else TAKE (Num m1) (DROP (Num n1) s)))) = [])
Proof
  simp [GSYM smt_seq_extract_def,
        smt_seq_extract_nested_empty_start]
QED

Theorem smt_seq_extract_zero_eq_empty[local]:
  (LENGTH (s : 'a list) <> 0) /\ (LENGTH r = 0) ==>
  ((smt_seq_extract s 0 m = r) <=> m <= 0)
Proof
  Cases_on `s` >- simp [] >>
  rw [smt_seq_extract_def] >>
  Cases_on `Num m` >-
    (simp [] >> intLib.ARITH_TAC) >>
  simp [] >>
  intLib.ARITH_TAC
QED

Theorem smt_seq_extract_zero_empty_iff:
  (0 < m) /\ (LENGTH (r : 'a list) = 0) ==>
  ((smt_seq_extract s 0 m = r) <=> (s = r))
Proof
  strip_tac >>
  Cases_on `LENGTH s = 0`
  >- fs [listTheory.LENGTH_EQ_0, smt_seq_extract_def] >>
  `(smt_seq_extract s 0 m = r) <=> (m <= 0)` by
    metis_tac [smt_seq_extract_zero_eq_empty] >>
  `s <> r` by metis_tac [] >>
  fs [integerTheory.INT_NOT_LE]
QED

Theorem smt_seq_extract_body_zero_eq_empty:
  (LENGTH (s : 'a list) <> 0) /\ (LENGTH r = 0) ==>
  (((if (0 : int) < 0 \/ m <= 0 \/ LENGTH s <= Num 0 then []
     else TAKE (Num m) (DROP (Num 0) s)) = r) <=> m <= 0)
Proof
  simp [GSYM smt_seq_extract_def, smt_seq_extract_zero_eq_empty]
QED

Theorem smt_seq_extract_eq_empty_length[local]:
  0 <= n /\ 0 < m /\ (LENGTH emp = 0) ==>
  ((smt_seq_extract (s : 'a list) n m = emp) <=> &(LENGTH s) <= n)
Proof
  rw [smt_seq_extract_def] >>
  Cases_on `DROP (Num n) s` >>
  fs [listTheory.DROP_EQ_NIL] >>
  Cases_on `Num m` >>
  fs [] >>
  intLib.ARITH_TAC
QED

Theorem smt_seq_extract_body_eq_empty_length:
  0 <= n /\ 0 < m /\ (LENGTH emp = 0) ==>
  (((if n < 0 \/ m <= 0 \/ LENGTH (s : 'a list) <= Num n then []
     else TAKE (Num m) (DROP (Num n) s)) = emp) <=> &(LENGTH s) <= n)
Proof
  simp [GSYM smt_seq_extract_def, smt_seq_extract_eq_empty_length]
QED

Theorem smt_seq_extract_positive[local]:
  0 <= i /\ 0 < n ==>
  (smt_seq_extract (s : 'a list) i n =
   TAKE (Num n) (DROP (Num i) s))
Proof
  strip_tac >>
  `~(i < 0) /\ ~(n <= 0)` by intLib.ARITH_TAC >>
  rw [smt_seq_extract_def] >>
  Cases_on `LENGTH s <= Num i` >>
  simp [listTheory.DROP_EQ_NIL]
QED

Theorem smt_seq_extract_nonpositive[local]:
  n <= 0 ==> (smt_seq_extract (s : 'a list) i n = [])
Proof
  simp [smt_seq_extract_def]
QED

Theorem TAKE_DROP_TAKE_RIGHT_BOUND_SEQ[local]:
  m1 - n2 <= m2 ==>
  (TAKE m2 (DROP n2 (TAKE m1 (DROP n1 xs))) =
   TAKE (m1 - n2) (DROP (n1 + n2) xs))
Proof
  strip_tac >>
  simp [listTheory.DROP_TAKE, rich_listTheory.DROP_DROP_T,
        listTheory.TAKE_TAKE_MIN, arithmeticTheory.MIN_DEF]
QED

Theorem TAKE_DROP_TAKE_LEFT_BOUND_SEQ[local]:
  m2 <= m1 - n2 ==>
  (TAKE m2 (DROP n2 (TAKE m1 (DROP n1 xs))) =
   TAKE m2 (DROP (n1 + n2) xs))
Proof
  strip_tac >>
  Cases_on `m2 < m1 - n2`
  >- simp [listTheory.DROP_TAKE, rich_listTheory.DROP_DROP_T,
           listTheory.TAKE_TAKE_MIN, arithmeticTheory.MIN_DEF] >>
  `m2 = m1 - n2` by decide_tac >>
  simp [listTheory.DROP_TAKE, rich_listTheory.DROP_DROP_T,
        listTheory.TAKE_TAKE_MIN]
QED

Theorem TAKE_DROP_TAKE_ACTUAL_BOUND_SEQ[local]:
  LENGTH (TAKE m1 (DROP n1 xs)) <= n2 + m2 ==>
  (TAKE m2 (DROP n2 (TAKE m1 (DROP n1 xs))) =
   TAKE (m1 - n2) (DROP (n1 + n2) xs))
Proof
  strip_tac >>
  Cases_on `m2 < m1 - n2`
  >- (`n2 + m2 < m1` by decide_tac >>
      `LENGTH (DROP n1 xs) < m1` by
        fs [listTheory.LENGTH_TAKE_EQ] >>
      `LENGTH (DROP n1 xs) <= m1` by decide_tac >>
      `TAKE m1 (DROP n1 xs) = DROP n1 xs` by
        simp [listTheory.TAKE_LENGTH_TOO_LONG] >>
      `LENGTH (DROP n1 xs) <= n2 + m2` by metis_tac [] >>
      `LENGTH (DROP (n1 + n2) xs) <= m2` by
        fs [listTheory.LENGTH_DROP] >>
      `TAKE m2 (DROP (n1 + n2) xs) = DROP (n1 + n2) xs` by
        simp [listTheory.TAKE_LENGTH_TOO_LONG] >>
      `LENGTH (DROP (n1 + n2) xs) <= m1 - n2` by decide_tac >>
      `TAKE (m1 - n2) (DROP (n1 + n2) xs) =
       DROP (n1 + n2) xs` by
        simp [listTheory.TAKE_LENGTH_TOO_LONG] >>
      simp [rich_listTheory.DROP_DROP_T]) >>
  `m1 - n2 <= m2` by decide_tac >>
  simp [listTheory.DROP_TAKE, rich_listTheory.DROP_DROP_T,
        listTheory.TAKE_TAKE_MIN, arithmeticTheory.MIN_DEF]
QED

Theorem smt_seq_extract_combine_right:
  0 <= n1 /\ 0 <= n2 /\ 0 <= m2 - (m1 - n2) ==>
  (smt_seq_extract (smt_seq_extract (s : 'a list) n1 m1) n2 m2 =
   smt_seq_extract s (n1 + n2) (m1 - n2))
Proof
  strip_tac >>
  Cases_on `m1 - n2 <= 0`
  >- (`m1 <= n2` by intLib.ARITH_TAC >>
      metis_tac [smt_seq_extract_nested_empty_start,
                 smt_seq_extract_nonpositive]) >>
  `0 < m1 - n2 /\ 0 < m1 /\ 0 < m2 /\ 0 <= n1 + n2` by
    intLib.ARITH_TAC >>
  `Num (n1 + n2) = Num n1 + Num n2` by intLib.ARITH_TAC >>
  `Num (m1 - n2) = Num m1 - Num n2` by intLib.ARITH_TAC >>
  `Num m1 - Num n2 <= Num m2` by intLib.ARITH_TAC >>
  simp [smt_seq_extract_positive] >>
  metis_tac [TAKE_DROP_TAKE_RIGHT_BOUND_SEQ]
QED

Theorem smt_seq_extract_combine_left:
  0 <= n1 /\ 0 <= n2 /\ 0 <= (m1 - n2) - m2 ==>
  (smt_seq_extract (smt_seq_extract (s : 'a list) n1 m1) n2 m2 =
   smt_seq_extract s (n1 + n2) m2)
Proof
  strip_tac >>
  Cases_on `m2 <= 0`
  >- metis_tac [smt_seq_extract_nonpositive] >>
  `0 < m2 /\ 0 < m1 - n2 /\ 0 < m1 /\ 0 <= n1 + n2` by
    intLib.ARITH_TAC >>
  `Num (n1 + n2) = Num n1 + Num n2` by intLib.ARITH_TAC >>
  `Num (m1 - n2) = Num m1 - Num n2` by intLib.ARITH_TAC >>
  `Num m2 <= Num m1 - Num n2` by intLib.ARITH_TAC >>
  simp [smt_seq_extract_positive] >>
  metis_tac [TAKE_DROP_TAKE_LEFT_BOUND_SEQ]
QED

Theorem smt_seq_extract_count_bound[local]:
  LENGTH (smt_seq_extract (s : 'a list) i n) <= Num n
Proof
  rw [smt_seq_extract_def, listTheory.LENGTH_TAKE_EQ] >>
  simp [arithmeticTheory.MIN_DEF]
QED

Theorem smt_seq_extract_positive_count[local]:
  0 <= (n2 : int) /\ 0 < m2 /\
  n2 + m2 <= &(LENGTH (smt_seq_extract (s : 'a list) n1 m1)) ==>
  0 < m1
Proof
  strip_tac >>
  Cases_on `m1 <= 0`
  >- (`smt_seq_extract s n1 m1 = []` by
        simp [smt_seq_extract_def] >>
      `n2 + m2 <= 0` by fs [] >>
      `0 < n2 + m2` by
        (match_mp_tac integerTheory.INT_LET_ADD >>
         asm_rewrite_tac []) >>
      qpat_x_assum `n2 + m2 <= 0`
        (assume_tac o
         REWRITE_RULE [GSYM integerTheory.INT_NOT_LT]) >>
      fs []) >>
  intLib.ARITH_TAC
QED

Theorem smt_seq_extract_combine_inner_bound:
  0 <= n1 /\ 0 <= n2 /\
  n2 + m2 <= &(LENGTH (smt_seq_extract (s : 'a list) n1 m1)) ==>
  (smt_seq_extract (smt_seq_extract s n1 m1) n2 m2 =
   smt_seq_extract s (n1 + n2) m2)
Proof
  strip_tac >>
  Cases_on `m2 <= 0`
  >- simp [smt_seq_extract_def] >>
  `0 < m2` by intLib.ARITH_TAC >>
  `0 < m1` by metis_tac [smt_seq_extract_positive_count] >>
  `&(Num m1) = m1` by intLib.ARITH_TAC >>
  `LENGTH (smt_seq_extract s n1 m1) <= Num m1` by
    metis_tac [smt_seq_extract_count_bound] >>
  `0 <= (m1 - n2) - m2` by intLib.ARITH_TAC >>
  metis_tac [smt_seq_extract_combine_left]
QED

Theorem smt_seq_extract_combine_actual_nonpositive[local]:
  0 <= n1 /\ 0 <= n2 /\ 0 < m1 /\ m2 <= 0 /\
  &(LENGTH (smt_seq_extract (s : 'a list) n1 m1)) <= n2 + m2 ==>
  (smt_seq_extract (smt_seq_extract s n1 m1) n2 m2 =
   smt_seq_extract s (n1 + n2) (m1 - n2))
Proof
  strip_tac >>
  `smt_seq_extract s n1 m1 = TAKE (Num m1) (DROP (Num n1) s)` by
    metis_tac [smt_seq_extract_positive] >>
  `&(Num n1) = n1` by intLib.ARITH_TAC >>
  `&(Num n2) = n2` by intLib.ARITH_TAC >>
  `LENGTH (smt_seq_extract s n1 m1) <= Num n2` by
    intLib.ARITH_TAC >>
  `LENGTH (TAKE (Num m1) (DROP (Num n1) s)) =
   LENGTH (smt_seq_extract s n1 m1)` by
    asm_rewrite_tac [] >>
  `LENGTH (TAKE (Num m1) (DROP (Num n1) s)) <= Num n2 + 0` by
    decide_tac >>
  `TAKE 0 (DROP (Num n2) (TAKE (Num m1) (DROP (Num n1) s))) =
   TAKE (Num m1 - Num n2)
     (DROP (Num n1 + Num n2) s)` by
    (match_mp_tac TAKE_DROP_TAKE_ACTUAL_BOUND_SEQ >>
     asm_rewrite_tac []) >>
  Cases_on `m1 - n2 <= 0`
  >- (`smt_seq_extract (smt_seq_extract s n1 m1) n2 m2 = []` by
        simp [smt_seq_extract_def] >>
      `smt_seq_extract s (n1 + n2) (m1 - n2) = []` by
        simp [smt_seq_extract_def] >>
      metis_tac []) >>
  `0 < m1 - n2 /\ 0 <= n1 + n2` by intLib.ARITH_TAC >>
  `Num (m1 - n2) = Num m1 - Num n2` by intLib.ARITH_TAC >>
  `Num (n1 + n2) = Num n1 + Num n2` by intLib.ARITH_TAC >>
  `TAKE (Num (m1 - n2)) (DROP (Num (n1 + n2)) s) = []` by
    metis_tac [listTheory.TAKE_0] >>
  `smt_seq_extract (smt_seq_extract s n1 m1) n2 m2 = []` by
    metis_tac [smt_seq_extract_nonpositive] >>
  `smt_seq_extract s (n1 + n2) (m1 - n2) = []` by
    metis_tac [smt_seq_extract_positive] >>
  metis_tac []
QED

Theorem smt_seq_extract_combine_actual_positive[local]:
  0 <= n1 /\ 0 <= n2 /\ 0 < m1 /\ 0 < m2 /\
  &(LENGTH (smt_seq_extract (s : 'a list) n1 m1)) <= n2 + m2 ==>
  (smt_seq_extract (smt_seq_extract s n1 m1) n2 m2 =
   smt_seq_extract s (n1 + n2) (m1 - n2))
Proof
  strip_tac >>
  `smt_seq_extract s n1 m1 = TAKE (Num m1) (DROP (Num n1) s)` by
    metis_tac [smt_seq_extract_positive] >>
  `&(Num n1) = n1` by intLib.ARITH_TAC >>
  `&(Num n2) = n2` by intLib.ARITH_TAC >>
  `&(Num m2) = m2` by intLib.ARITH_TAC >>
  `LENGTH (smt_seq_extract s n1 m1) <= Num n2 + Num m2` by
    intLib.ARITH_TAC >>
  `LENGTH (TAKE (Num m1) (DROP (Num n1) s)) =
   LENGTH (smt_seq_extract s n1 m1)` by
    asm_rewrite_tac [] >>
  `LENGTH (TAKE (Num m1) (DROP (Num n1) s)) <=
   Num n2 + Num m2` by decide_tac >>
  `TAKE (Num m2)
     (DROP (Num n2) (TAKE (Num m1) (DROP (Num n1) s))) =
   TAKE (Num m1 - Num n2)
     (DROP (Num n1 + Num n2) s)` by
    (match_mp_tac TAKE_DROP_TAKE_ACTUAL_BOUND_SEQ >>
     asm_rewrite_tac []) >>
  `smt_seq_extract (smt_seq_extract s n1 m1) n2 m2 =
   TAKE (Num m2)
     (DROP (Num n2) (TAKE (Num m1) (DROP (Num n1) s)))` by
    simp [smt_seq_extract_positive] >>
  Cases_on `m1 - n2 <= 0`
  >- (`Num m1 <= Num n2` by intLib.ARITH_TAC >>
      `Num m1 - Num n2 = 0` by decide_tac >>
      `smt_seq_extract (smt_seq_extract s n1 m1) n2 m2 = []` by
        metis_tac [listTheory.TAKE_0] >>
      `smt_seq_extract s (n1 + n2) (m1 - n2) = []` by
        simp [smt_seq_extract_def] >>
      metis_tac []) >>
  `0 < m1 - n2 /\ 0 <= n1 + n2` by intLib.ARITH_TAC >>
  `Num (m1 - n2) = Num m1 - Num n2` by intLib.ARITH_TAC >>
  `Num (n1 + n2) = Num n1 + Num n2` by intLib.ARITH_TAC >>
  `smt_seq_extract s (n1 + n2) (m1 - n2) =
   TAKE (Num (m1 - n2)) (DROP (Num (n1 + n2)) s)` by
    metis_tac [smt_seq_extract_positive] >>
  metis_tac []
QED

Theorem smt_seq_extract_combine_actual_bound:
  0 <= n1 /\ 0 <= n2 /\
  &(LENGTH (smt_seq_extract (s : 'a list) n1 m1)) <= n2 + m2 ==>
  (smt_seq_extract (smt_seq_extract s n1 m1) n2 m2 =
   smt_seq_extract s (n1 + n2) (m1 - n2))
Proof
  strip_tac >>
  Cases_on `m1 <= 0`
  >- (`~(n1 < 0) /\ ~(n2 < 0) /\ ~(n1 + n2 < 0) /\
       m1 - n2 <= 0` by intLib.ARITH_TAC >>
      simp [smt_seq_extract_def]) >>
  `0 < m1` by intLib.ARITH_TAC >>
  Cases_on `m2 <= 0`
  >- metis_tac [smt_seq_extract_combine_actual_nonpositive] >>
  `0 < m2` by intLib.ARITH_TAC >>
  metis_tac [smt_seq_extract_combine_actual_positive]
QED

Theorem smt_seq_extract_drop_concat_prefix[local]:
  &(LENGTH (s1 : 'a list)) <= n ==>
  (smt_seq_extract ((s1 ++ s2) ++ s3) n m =
   smt_seq_extract (s2 ++ s3) (n - &(LENGTH s1)) m)
Proof
  strip_tac >>
  `0 <= n` by intLib.ARITH_TAC >>
  `0 <= n - &(LENGTH s1)` by intLib.ARITH_TAC >>
  `&(Num n) = n` by intLib.ARITH_TAC >>
  `&(Num (n - &(LENGTH s1))) = n - &(LENGTH s1)` by
    intLib.ARITH_TAC >>
  `Num n = LENGTH s1 + Num (n - &(LENGTH s1))` by
    intLib.ARITH_TAC >>
  Cases_on `m <= 0`
  >- metis_tac [smt_seq_extract_nonpositive] >>
  `0 < m` by intLib.ARITH_TAC >>
  `smt_seq_extract ((s1 ++ s2) ++ s3) n m =
   TAKE (Num m) (DROP (Num n) ((s1 ++ s2) ++ s3))` by
    metis_tac [smt_seq_extract_positive] >>
  `smt_seq_extract (s2 ++ s3) (n - &(LENGTH s1)) m =
   TAKE (Num m)
     (DROP (Num (n - &(LENGTH s1))) (s2 ++ s3))` by
    metis_tac [smt_seq_extract_positive] >>
  `DROP (Num n) ((s1 ++ s2) ++ s3) =
   DROP (Num (n - &(LENGTH s1))) (s2 ++ s3)` by
    simp [listTheory.DROP_APPEND] >>
  metis_tac []
QED

Theorem smt_seq_extract_drop_concat_prefix_assoc[local]:
  &(LENGTH (s1 : 'a list)) <= n ==>
  (smt_seq_extract (s1 ++ (s2 ++ s3)) n m =
   smt_seq_extract (s2 ++ s3) (n - &(LENGTH s1)) m)
Proof
  metis_tac [smt_seq_extract_drop_concat_prefix,
             listTheory.APPEND_ASSOC]
QED

Theorem smt_seq_extract_drop_prefix:
  &(LENGTH (prefix : 'a list)) <= n ==>
  (smt_seq_extract (prefix ++ tail) n m =
   smt_seq_extract tail (n - &(LENGTH prefix)) m)
Proof
  metis_tac [smt_seq_extract_drop_concat_prefix,
             listTheory.APPEND_NIL]
QED

Theorem smt_seq_extract_full:
  &(LENGTH (s : 'a list)) <= n ==> (smt_seq_extract s 0 n = s)
Proof
  Cases_on `n` >> Cases_on `s` >>
  simp [smt_seq_extract_def, integerTheory.INT_OF_NUM_LE,
        integerTheory.INT_NOT_LE, listTheory.TAKE_LENGTH_TOO_LONG]
QED

Theorem smt_seq_extract_body_full_eq:
  (&(LENGTH (s : 'a list)) = n) ==>
  ((if (0 : int) < 0 \/ n <= 0 \/ LENGTH s <= Num 0 then []
    else TAKE (Num n) (DROP (Num 0) s)) = s)
Proof
  PURE_REWRITE_TAC [GSYM smt_seq_extract_def] >>
  strip_tac >>
  irule smt_seq_extract_full >>
  simp []
QED

Definition smt_seq_at_def:
  smt_seq_at (s : 'a list) (i : int) =
    if i < 0 \/ LENGTH s <= Num i then [] else [EL (Num i) s]
End

Theorem smt_seq_at_extract:
  smt_seq_at (s : 'a list) i = smt_seq_extract s i 1
Proof
  rw [smt_seq_at_def, smt_seq_extract_def, listTheory.TAKE1_DROP]
QED

Definition smt_seq_indexof_aux_def:
  (smt_seq_indexof_aux (t : 'a list) n [] =
     if t = [] then SOME n else NONE) /\
  (smt_seq_indexof_aux t n (h::s) =
     if IS_PREFIX (h::s) t then SOME n
     else smt_seq_indexof_aux t (SUC n) s)
End

Definition smt_seq_indexof_def:
  smt_seq_indexof (s : 'a list) t (i : int) : int =
    if i < 0 \/ LENGTH s < Num i then -1
    else
      case smt_seq_indexof_aux t (Num i) (DROP (Num i) s) of
        NONE => -1
      | SOME n => &n
End

Theorem smt_seq_indexof_aux_self[local]:
  smt_seq_indexof_aux (s : 'a list) 0 s = SOME 0
Proof
  Cases_on `s` >>
  simp [smt_seq_indexof_aux_def, rich_listTheory.IS_PREFIX]
QED

Theorem smt_seq_indexof_aux_empty[local]:
  !s n. smt_seq_indexof_aux ([] : 'a list) n s = SOME n
Proof
  Cases >>
  simp [smt_seq_indexof_aux_def, rich_listTheory.IS_PREFIX_NIL]
QED

Theorem smt_seq_indexof_aux_prefix[local]:
  !t rest n. smt_seq_indexof_aux (t : 'a list) n (t ++ rest) = SOME n
Proof
  Cases >>
  simp [smt_seq_indexof_aux_def, smt_seq_indexof_aux_empty,
        rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem smt_seq_indexof_aux_none[local]:
  !s t n.
    (smt_seq_indexof_aux (t : 'a list) n s = NONE) <=>
    ~IS_SUBLIST s t
Proof
  Induct
  >- simp [smt_seq_indexof_aux_def,
           rich_listTheory.IS_SUBLIST_APPEND] >>
  Cases_on `t` >>
  simp [smt_seq_indexof_aux_def, rich_listTheory.IS_SUBLIST] >>
  metis_tac []
QED

Theorem smt_seq_indexof_oob[local]:
  &(LENGTH (s : 'a list)) < n ==> (smt_seq_indexof s t n = -1)
Proof
  rw [smt_seq_indexof_def] >>
  intLib.ARITH_TAC
QED

Theorem smt_seq_indexof_negative_start[local]:
  n < 0 ==> (smt_seq_indexof (s : 'a list) t n = -1)
Proof
  simp [smt_seq_indexof_def]
QED

Theorem smt_seq_indexof_empty:
  ((e : 'a list) = []) /\ 0 <= n /\ n <= &(LENGTH s) ==>
  (smt_seq_indexof s e n = n)
Proof
  rw [smt_seq_indexof_def, smt_seq_indexof_aux_empty] >>
  intLib.ARITH_TAC
QED

Theorem smt_seq_drop_no_self_sublist[local]:
  0 < n /\ n <= LENGTH (s : 'a list) ==>
  ~IS_SUBLIST (DROP n s) s
Proof
  rw [rich_listTheory.IS_SUBLIST_APPEND] >>
  CCONTR_TAC >>
  fs [] >>
  qpat_x_assum `DROP n s = _` (mp_tac o AP_TERM ``LENGTH``) >>
  simp []
QED

Theorem smt_seq_indexof_self_zero[local]:
  smt_seq_indexof (s : 'a list) s 0 = smt_seq_indexof [] [] 0
Proof
  rw [smt_seq_indexof_def] >>
  simp [smt_seq_indexof_aux_self, smt_seq_indexof_aux_empty]
QED

Theorem smt_seq_indexof_self_positive[local]:
  smt_seq_indexof (s : 'a list) s (&(SUC n)) =
  smt_seq_indexof [] [] (&(SUC n))
Proof
  simp [smt_seq_indexof_def] >>
  Cases_on `LENGTH s < SUC n` >> simp [] >>
  `smt_seq_indexof_aux s (SUC n) (DROP (SUC n) s) = NONE` by
    (rw [smt_seq_indexof_aux_none] >>
     irule smt_seq_drop_no_self_sublist >> simp []) >>
  simp []
QED

Theorem smt_seq_indexof_self:
  smt_seq_indexof (s : 'a list) s n = smt_seq_indexof [] [] n
Proof
  Cases_on `n`
  >- (Cases_on `n'` >> fs [] >>
      ACCEPT_TAC smt_seq_indexof_self_positive)
  >- simp [smt_seq_indexof_negative_start]
  >- ACCEPT_TAC smt_seq_indexof_self_zero
QED

Theorem smt_seq_extract_suffix_inclusive[local]:
  0 <= n /\ n <= &(LENGTH (s : 'a list)) ==>
  (smt_seq_extract s n (&(LENGTH s)) = DROP (Num n) s)
Proof
  strip_tac >>
  `Num n <= LENGTH s` by intLib.ARITH_TAC >>
  Cases_on `Num n = LENGTH s`
  >- simp [smt_seq_extract_def] >>
  `Num n < LENGTH s` by decide_tac >>
  `~(n < 0)` by intLib.ARITH_TAC >>
  `s <> []` by (Cases_on `s` >> fs []) >>
  simp [smt_seq_extract_def, listTheory.TAKE_LENGTH_TOO_LONG]
QED

Theorem smt_seq_indexof_no_contains:
  ~IS_SUBLIST (smt_seq_extract (s : 'a list) n (&(LENGTH s))) t ==>
  (smt_seq_indexof s t n = -1)
Proof
  strip_tac >>
  Cases_on `n < 0`
  >- simp [smt_seq_indexof_negative_start] >>
  Cases_on `&(LENGTH s) < n`
  >- simp [smt_seq_indexof_oob] >>
  `0 <= n /\ n <= &(LENGTH s)` by intLib.ARITH_TAC >>
  `~IS_SUBLIST (DROP (Num n) s) t` by
    metis_tac [smt_seq_extract_suffix_inclusive] >>
  `smt_seq_indexof_aux t (Num n) (DROP (Num n) s) = NONE` by
    simp [smt_seq_indexof_aux_none] >>
  `~(LENGTH s < Num n)` by intLib.ARITH_TAC >>
  simp [smt_seq_indexof_def]
QED

Theorem smt_seq_contains_extract_bounds[local]:
  0 < LENGTH (t : 'a list) /\
  IS_SUBLIST (smt_seq_extract s n (&(LENGTH s))) t ==>
  0 <= n /\ n < &(LENGTH s)
Proof
  strip_tac >>
  `t <> []` by (Cases_on `t` >> fs []) >>
  Cases_on `n < 0`
  >- fs [smt_seq_extract_def, rich_listTheory.IS_SUBLIST_APPEND] >>
  Cases_on `&(LENGTH s) <= n`
  >- (`LENGTH s <= Num n` by intLib.ARITH_TAC >>
      fs [smt_seq_extract_def, rich_listTheory.IS_SUBLIST_APPEND]) >>
  intLib.ARITH_TAC
QED

Definition smt_seq_replace_raw_def:
  smt_seq_replace_raw (s : 'a list) t u =
    case smt_seq_indexof_aux t 0 s of
      NONE => s
    | SOME n => TAKE n s ++ u ++ DROP (n + LENGTH t) s
End

Definition smt_seq_replace_def:
  smt_seq_replace (s : 'a list) t u = smt_seq_replace_raw s t u
End

Theorem smt_seq_replace_self:
  smt_seq_replace (t : 'a list) t s = s
Proof
  simp [smt_seq_replace_def, smt_seq_replace_raw_def,
        smt_seq_indexof_aux_self]
QED

Theorem smt_seq_indexof_aux_split[local]:
  !s t n k.
    (smt_seq_indexof_aux (t : 'a list) n s = SOME k) ==>
    ?pre post. (s = pre ++ t ++ post) /\ (LENGTH pre + n = k)
Proof
  Induct
  >- (simp [smt_seq_indexof_aux_def] >> metis_tac []) >>
  rw [smt_seq_indexof_aux_def] >>
  Cases_on `IS_PREFIX (h::s) t`
  >- (fs [rich_listTheory.IS_PREFIX_APPEND] >>
      qexistsl [`[]`, `l`] >> simp []) >>
  fs [] >>
  first_x_assum drule >>
  strip_tac >>
  qexistsl [`h::pre`, `post`] >>
  simp []
QED

Theorem smt_seq_indexof_aux_pattern_length[local]:
  (smt_seq_indexof_aux (t : 'a list) n s = SOME k) ==>
  LENGTH t <= LENGTH s
Proof
  strip_tac >>
  drule smt_seq_indexof_aux_split >>
  strip_tac >>
  fs []
QED

Theorem smt_seq_is_prefix_append_short[local]:
  IS_PREFIX ((s : 'a list) ++ u) t /\ LENGTH t <= LENGTH s ==>
  IS_PREFIX s t
Proof
  metis_tac [rich_listTheory.IS_PREFIX_IMP_TAKE,
             rich_listTheory.IS_PREFIX_EQ_TAKE',
             listTheory.TAKE_APPEND1]
QED

Theorem smt_seq_is_prefix_append_right[local]:
  IS_PREFIX (s : 'a list) t ==> IS_PREFIX (s ++ u) t
Proof
  rw [rich_listTheory.IS_PREFIX_APPEND] >>
  qexists `l ++ u` >>
  simp [listTheory.APPEND_ASSOC]
QED

Theorem smt_seq_indexof_aux_append_some[local]:
  !s t n k u.
    (smt_seq_indexof_aux (t : 'a list) n s = SOME k) ==>
    (smt_seq_indexof_aux t n (s ++ u) = SOME k)
Proof
  rpt gen_tac >>
  qid_spec_tac `n` >>
  Induct_on `s` >>
  rw [smt_seq_indexof_aux_def]
  >- simp [smt_seq_indexof_aux_empty]
  >- (`IS_PREFIX ((h::s) ++ u) t` by
        metis_tac [smt_seq_is_prefix_append_right] >>
      fs [])
  >- (`LENGTH t <= LENGTH s` by
        metis_tac [smt_seq_indexof_aux_pattern_length] >>
      mp_tac (Q.INST
        [`s` |-> `h::s`, `u` |-> `u`, `t` |-> `t`]
        smt_seq_is_prefix_append_short) >>
      simp [])
QED

Theorem smt_seq_indexof_concat_preserve[local]:
  0 <= n /\ n <= &(LENGTH (s : 'a list)) /\
  IS_SUBLIST (smt_seq_extract s n (&(LENGTH s))) t ==>
  (smt_seq_indexof (s ++ u) t n = smt_seq_indexof s t n)
Proof
  strip_tac >>
  `smt_seq_extract s n (&(LENGTH s)) = DROP (Num n) s` by
    metis_tac [smt_seq_extract_suffix_inclusive] >>
  `IS_SUBLIST (DROP (Num n) s) t` by metis_tac [] >>
  `?k. smt_seq_indexof_aux t (Num n) (DROP (Num n) s) = SOME k` by
    (Cases_on `smt_seq_indexof_aux t (Num n) (DROP (Num n) s)` >>
     fs [smt_seq_indexof_aux_none]) >>
  `Num n <= LENGTH s` by intLib.ARITH_TAC >>
  `DROP (Num n) (s ++ u) = DROP (Num n) s ++ u` by
    simp [listTheory.DROP_APPEND1] >>
  `smt_seq_indexof_aux t (Num n) (DROP (Num n) (s ++ u)) = SOME k` by
    metis_tac [smt_seq_indexof_aux_append_some] >>
  `~(n < 0)` by intLib.ARITH_TAC >>
  `~(LENGTH s < Num n) /\ ~(LENGTH (s ++ u) < Num n)` by
    (simp [] >> decide_tac) >>
  simp [smt_seq_indexof_def]
QED

Theorem smt_seq_indexof_concat_contains[local]:
  0 < LENGTH (t : 'a list) /\
  IS_SUBLIST (smt_seq_extract s n (&(LENGTH s))) t ==>
  (smt_seq_indexof (s ++ u) t n = smt_seq_indexof s t n)
Proof
  strip_tac >>
  `0 <= n /\ n < &(LENGTH s)` by
    metis_tac [smt_seq_contains_extract_bounds] >>
  `smt_seq_extract s n (&(LENGTH s)) = DROP (Num n) s` by
    (irule smt_seq_extract_suffix_inclusive >> intLib.ARITH_TAC) >>
  `IS_SUBLIST (DROP (Num n) s) t` by metis_tac [] >>
  `?k. smt_seq_indexof_aux t (Num n) (DROP (Num n) s) = SOME k` by
    (Cases_on `smt_seq_indexof_aux t (Num n) (DROP (Num n) s)` >>
     fs [smt_seq_indexof_aux_none]) >>
  `Num n <= LENGTH s` by intLib.ARITH_TAC >>
  `DROP (Num n) (s ++ u) = DROP (Num n) s ++ u` by
    simp [listTheory.DROP_APPEND1] >>
  `smt_seq_indexof_aux t (Num n) (DROP (Num n) (s ++ u)) = SOME k` by
    metis_tac [smt_seq_indexof_aux_append_some] >>
  `~(n < 0)` by intLib.ARITH_TAC >>
  `~(LENGTH s < Num n) /\ ~(LENGTH (s ++ u) < Num n)` by
    (simp [] >> decide_tac) >>
  simp [smt_seq_indexof_def]
QED

Theorem smt_seq_indexof_concat_contains2:
  0 < LENGTH (t : 'a list) /\
  IS_SUBLIST (smt_seq_extract s n (&(LENGTH s))) t ==>
  (smt_seq_indexof ((s ++ u) ++ v) t n = smt_seq_indexof s t n)
Proof
  metis_tac [smt_seq_indexof_concat_contains, listTheory.APPEND_ASSOC]
QED

Theorem smt_seq_indexof_concat_occurrence[local]:
  smt_seq_indexof (((pre : 'a list) ++ t) ++ u) t 0 =
  smt_seq_indexof (pre ++ t) t 0
Proof
  irule smt_seq_indexof_concat_preserve >>
  conj_tac
  >-
   (`smt_seq_extract (pre ++ t) 0 (&(LENGTH (pre ++ t))) = pre ++ t` by
      (irule smt_seq_extract_full >> simp []) >>
    asm_rewrite_tac [] >>
    rw [rich_listTheory.IS_SUBLIST_APPEND] >>
    qexistsl [`pre`, `[]`] >>
    simp []) >>
  simp []
QED

Theorem smt_seq_indexof_concat_occurrence_segments[local]:
  smt_seq_indexof ((pre : 'a list) ++ t ++ u ++ v) t 0 =
  smt_seq_indexof (pre ++ t) t 0
Proof
  `pre ++ t ++ u ++ v = (pre ++ t) ++ (u ++ v)` by simp [] >>
  asm_rewrite_tac [] >>
  simp [smt_seq_indexof_concat_occurrence]
QED

Theorem smt_seq_indexof_known_occurrence_suffix:
  smt_seq_indexof (((pre : 'a list) ++ t) ++ suffix) t 0 =
  smt_seq_indexof (pre ++ t) t 0
Proof
  simp [smt_seq_indexof_concat_occurrence]
QED

Theorem smt_seq_indexof_suffix_equal:
  n <= &(LENGTH (s : 'a list)) /\ n <= &(LENGTH r) /\
  (smt_seq_extract s n (&(LENGTH s)) =
    smt_seq_extract r n (&(LENGTH r))) ==>
  (smt_seq_indexof s t n = smt_seq_indexof r t n)
Proof
  strip_tac >>
  Cases_on `n < 0`
  >- simp [smt_seq_indexof_negative_start] >>
  `0 <= n` by intLib.ARITH_TAC >>
  `smt_seq_extract s n (&(LENGTH s)) = DROP (Num n) s` by
    metis_tac [smt_seq_extract_suffix_inclusive] >>
  `smt_seq_extract r n (&(LENGTH r)) = DROP (Num n) r` by
    metis_tac [smt_seq_extract_suffix_inclusive] >>
  `DROP (Num n) s = DROP (Num n) r` by metis_tac [] >>
  `~(n < 0)` by intLib.ARITH_TAC >>
  `~(LENGTH s < Num n) /\ ~(LENGTH r < Num n)` by
    (simp [] >> intLib.ARITH_TAC) >>
  simp [smt_seq_indexof_def]
QED

Theorem smt_seq_contains_trans[local]:
  IS_SUBLIST (s : 'a list) t /\ IS_SUBLIST t u ==>
  IS_SUBLIST s u
Proof
  rw [rich_listTheory.IS_SUBLIST_APPEND] >>
  metis_tac [listTheory.APPEND_ASSOC]
QED

Theorem smt_seq_extract_sublist:
  IS_SUBLIST (s : 'a list) (smt_seq_extract s i n)
Proof
  rw [smt_seq_extract_def, rich_listTheory.IS_SUBLIST_APPEND]
  >- (qexistsl [`[]`, `s`] >> simp [])
  >- (qexistsl [`[]`, `s`] >> simp [])
  >- (qexistsl [`[]`, `s`] >> simp []) >>
  qexistsl [`TAKE (Num i) s`, `DROP (Num n) (DROP (Num i) s)`] >>
  metis_tac [listTheory.TAKE_DROP, listTheory.APPEND_ASSOC]
QED

Theorem smt_seq_extract_contains_contra:
  ~IS_SUBLIST (t : 'a list) s ==>
  ~IS_SUBLIST (smt_seq_extract t n m) s
Proof
  metis_tac [smt_seq_extract_sublist, smt_seq_contains_trans]
QED

Theorem smt_seq_extract_short_self_count:
  LENGTH (x : 'a list) <= 1 ==>
  (smt_seq_extract x n n = [])
Proof
  strip_tac >>
  Cases_on `n <= 0`
  >- simp [smt_seq_extract_def] >>
  `1 <= n` by intLib.ARITH_TAC >>
  `&(LENGTH x) <= n` by (simp [] >> intLib.ARITH_TAC) >>
  metis_tac [smt_seq_extract_empty_start]
QED

Theorem smt_seq_extract_concat_left_bound[local]:
  n + m <= &(LENGTH (s1 : 'a list)) ==>
  (smt_seq_extract (s1 ++ s2) n m = smt_seq_extract s1 n m)
Proof
  strip_tac >>
  Cases_on `n < 0 \/ m <= 0`
  >- fs [smt_seq_extract_def] >>
  `0 <= n /\ 0 < m` by intLib.ARITH_TAC >>
  `Num n + Num m <= LENGTH s1 /\ Num n <= LENGTH s1` by
    (simp [] >> intLib.ARITH_TAC) >>
  `Num n < LENGTH s1` by intLib.ARITH_TAC >>
  `Num m <= LENGTH (DROP (Num n) s1)` by
    simp [listTheory.LENGTH_DROP] >>
  simp [smt_seq_extract_def, listTheory.DROP_APPEND1,
        listTheory.TAKE_APPEND1]
QED

Theorem TAKE_NUM_INT_APPEND[local]:
  &(LENGTH (s1 : 'a list)) <= n ==>
  (TAKE (Num n) (s1 ++ tail) =
   s1 ++ TAKE (Num (n - &(LENGTH s1))) tail)
Proof
  strip_tac >>
  `0 <= n /\ 0 <= n - &(LENGTH s1)` by intLib.ARITH_TAC >>
  `LENGTH s1 <= Num n` by intLib.ARITH_TAC >>
  `Num n - LENGTH s1 = Num (n - &(LENGTH s1))` by
    intLib.ARITH_TAC >>
  simp [rich_listTheory.TAKE_APPEND,
        listTheory.TAKE_LENGTH_TOO_LONG]
QED

Theorem INT_EQ_ZERO_FROM_BOUNDS[local]:
  0 <= (x : int) /\ x <= 0 ==> (x = 0)
Proof
  intLib.ARITH_TAC
QED

Theorem INT_ZERO_LET_TRANS[local]:
  !x y : int. 0 <= x /\ x < y ==> 0 < y
Proof
  intLib.ARITH_TAC
QED

Theorem INT_ZERO_LTE_TRANS[local]:
  !x y : int. 0 < x /\ x <= y ==> 0 < y
Proof
  intLib.ARITH_TAC
QED

Theorem smt_seq_extract_concat_left_bound2:
  n + m <= &(LENGTH (s1 : 'a list)) ==>
  (smt_seq_extract ((s1 ++ s2) ++ s3) n m = smt_seq_extract s1 n m)
Proof
  metis_tac [smt_seq_extract_concat_left_bound,
             listTheory.APPEND_ASSOC]
QED

Theorem smt_seq_extract_body_concat_left_bound2:
  n + m <= &(LENGTH (s1 : 'a list)) ==>
  ((if n < 0 \/ m <= 0 \/ LENGTH ((s1 ++ s2) ++ s3) <= Num n
    then [] else TAKE (Num m) (DROP (Num n) ((s1 ++ s2) ++ s3))) =
   (if n < 0 \/ m <= 0 \/ LENGTH s1 <= Num n
    then [] else TAKE (Num m) (DROP (Num n) s1)))
Proof
  simp [GSYM smt_seq_extract_def,
        smt_seq_extract_concat_left_bound2]
QED

Theorem smt_seq_extract_concat_prefix_bound:
  &(LENGTH (s1 : 'a list)) <= n ==>
  (smt_seq_extract (s1 ++ tail) 0 n =
   s1 ++ smt_seq_extract tail 0 (n - &(LENGTH s1)))
Proof
  strip_tac >>
  Cases_on `s1`
  >- simp [smt_seq_extract_def] >>
  `0 < n` by
    (irule integerTheory.INT_LTE_TRANS >>
     qexists_tac `&(LENGTH (h::t))` >> simp []) >>
  `~(n <= 0)` by fs [integerTheory.INT_NOT_LE] >>
  `0 <= n - &(LENGTH (h::t))` by intLib.ARITH_TAC >>
  drule TAKE_NUM_INT_APPEND >>
  disch_then (qspec_then `tail` assume_tac) >>
  Cases_on `tail`
  >- fs [smt_seq_extract_def] >>
  Cases_on `n - &(LENGTH (h::t)) <= 0`
  >- (`n - &(LENGTH (h::t)) = 0` by
        metis_tac [INT_EQ_ZERO_FROM_BOUNDS] >>
      fs [smt_seq_extract_def]) >>
  fs [smt_seq_extract_def]
QED

Theorem smt_seq_extract_count_normalize:
  &(LENGTH (s : 'a list)) <= m ==>
  (smt_seq_extract s n m = smt_seq_extract s n (&(LENGTH s)))
Proof
  strip_tac >>
  Cases_on `n < 0`
  >- simp [smt_seq_extract_def] >>
  `0 <= n` by intLib.ARITH_TAC >>
  Cases_on `&(LENGTH s) <= n`
  >- simp [smt_seq_extract_empty_start] >>
  `n < &(LENGTH s)` by fs [integerTheory.INT_NOT_LE] >>
  `(0 : int) < &(LENGTH s)` by
    ACCEPT_TAC
      (MATCH_MP (Q.SPECL [`n`, `&(LENGTH s)`]
                   INT_ZERO_LET_TRANS)
         (CONJ (ASSUME ``(0 : int) <= n``)
               (ASSUME ``(n : int) < &(LENGTH s)``))) >>
  `0 < m` by
    ACCEPT_TAC
      (MATCH_MP (Q.SPECL [`&(LENGTH s)`, `m`]
                   INT_ZERO_LTE_TRANS)
         (CONJ (ASSUME ``(0 : int) < &(LENGTH s)``)
               (ASSUME ``&(LENGTH s) <= (m : int)``))) >>
  `LENGTH s <= Num m` by intLib.ARITH_TAC >>
  `LENGTH (DROP (Num n) s) <= Num m /\
   LENGTH (DROP (Num n) s) <= LENGTH s` by
    simp [listTheory.LENGTH_DROP] >>
  simp [smt_seq_extract_def, listTheory.TAKE_LENGTH_TOO_LONG] >>
  `~(m <= 0)` by intLib.ARITH_TAC >>
  `~(LENGTH s <= Num n)` by intLib.ARITH_TAC >>
  `s <> []` by (Cases_on `s` >> fs []) >>
  simp []
QED

Theorem smt_seq_replace_take_splice[local]:
  !pre t post. TAKE (LENGTH pre) (pre ++ t ++ post) = pre
Proof
  Induct >> simp []
QED

Theorem smt_seq_replace_drop_splice[local]:
  !pre t post.
    DROP (LENGTH pre + LENGTH t) (pre ++ t ++ post) = post
Proof
  metis_tac [listTheory.LENGTH_APPEND, listTheory.APPEND_ASSOC,
             rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem smt_seq_replace_splice_identity[local]:
  TAKE (LENGTH pre) (pre ++ t ++ post) ++ t ++
  DROP (LENGTH pre + LENGTH t) (pre ++ t ++ post) =
  pre ++ t ++ post
Proof
  simp [smt_seq_replace_take_splice, smt_seq_replace_drop_splice]
QED

Theorem smt_seq_replace_id:
  smt_seq_replace (s : 'a list) t t = s
Proof
  rw [smt_seq_replace_def, smt_seq_replace_raw_def] >>
  Cases_on `smt_seq_indexof_aux t 0 s` >> simp [] >>
  drule smt_seq_indexof_aux_split >>
  strip_tac >>
  qpat_x_assum `LENGTH pre + 0 = x` (SUBST_ALL_TAC o SYM) >>
  simp [smt_seq_replace_splice_identity]
QED

Theorem smt_seq_replace_prefix:
  smt_seq_replace ((t : 'a list) ++ rest) t r = r ++ rest
Proof
  simp [smt_seq_replace_def, smt_seq_replace_raw_def,
        smt_seq_indexof_aux_prefix,
        rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem smt_seq_replace_empty:
  smt_seq_replace (t : 'a list) [] s = s ++ t
Proof
  simp [smt_seq_replace_def, smt_seq_replace_raw_def,
        smt_seq_indexof_aux_empty]
QED

Theorem smt_seq_replace_absent:
  ~IS_SUBLIST (s : 'a list) t ==> (smt_seq_replace s t r = s)
Proof
  strip_tac >>
  `smt_seq_indexof_aux t 0 s = NONE` by
    metis_tac [smt_seq_indexof_aux_none] >>
  simp [smt_seq_replace_def, smt_seq_replace_raw_def]
QED

Theorem smt_seq_replace_raw_absent[local]:
  ~IS_SUBLIST (s : 'a list) t ==>
  (smt_seq_replace_raw s t u = s)
Proof
  strip_tac >>
  `smt_seq_indexof_aux t 0 s = NONE` by
    metis_tac [smt_seq_indexof_aux_none] >>
  simp [smt_seq_replace_raw_def]
QED

Theorem smt_seq_replace_raw_hit[local]:
  IS_SUBLIST (s : 'a list) t ==>
  ?pre post.
    (s = pre ++ t ++ post) /\
    (smt_seq_replace_raw s t u = pre ++ u ++ post)
Proof
  strip_tac >>
  Cases_on `smt_seq_indexof_aux t 0 s` >>
  fs [smt_seq_indexof_aux_none] >>
  drule smt_seq_indexof_aux_split >>
  strip_tac >>
  qpat_x_assum `LENGTH pre + 0 = x` (SUBST_ALL_TAC o SYM) >>
  qexistsl [`pre`, `post`] >>
  simp [smt_seq_replace_raw_def, smt_seq_replace_take_splice,
        smt_seq_replace_drop_splice]
QED

Theorem smt_seq_replace_contains_replacement:
  IS_SUBLIST (smt_seq_replace (s : 'a list) t u) u <=>
  IS_SUBLIST s t \/ IS_SUBLIST s u
Proof
  rw [smt_seq_replace_def] >>
  Cases_on `IS_SUBLIST s t`
  >- (drule_then (qspec_then `u` strip_assume_tac)
        smt_seq_replace_raw_hit >>
      rw [] >>
      rw [rich_listTheory.IS_SUBLIST_APPEND] >>
      qexistsl [`pre`, `post`] >> simp []) >>
  simp [smt_seq_replace_raw_absent]
QED

Theorem smt_seq_replace_preserves_contains:
  IS_SUBLIST (s : 'a list) u /\ IS_SUBLIST r u ==>
  IS_SUBLIST (smt_seq_replace s t r) u
Proof
  Cases_on `IS_SUBLIST s t`
  >- metis_tac [smt_seq_replace_contains_replacement,
                smt_seq_contains_trans] >>
  simp [smt_seq_replace_absent]
QED

Theorem smt_seq_replace_avoids_outer:
  ~IS_SUBLIST (s : 'a list) t /\ ~IS_SUBLIST s u ==>
  ~IS_SUBLIST s (smt_seq_replace t r u)
Proof
  strip_tac >>
  Cases_on `IS_SUBLIST t r`
  >- (CCONTR_TAC >>
      `IS_SUBLIST (smt_seq_replace t r u) u` by
        metis_tac [smt_seq_replace_contains_replacement] >>
      metis_tac [smt_seq_contains_trans]) >>
  simp [smt_seq_replace_absent]
QED

Theorem smt_seq_contains_refl[local]:
  IS_SUBLIST (s : 'a list) s
Proof
  rw [rich_listTheory.IS_SUBLIST_APPEND] >>
  qexistsl [`[]`, `[]`] >> simp []
QED

Theorem smt_seq_contains_length_bound[local]:
  IS_SUBLIST (s : 'a list) t ==> LENGTH t <= LENGTH s
Proof
  rw [rich_listTheory.IS_SUBLIST_APPEND] >> simp []
QED

Theorem smt_seq_contains_length_equal[local]:
  IS_SUBLIST (s : 'a list) t /\ (LENGTH s = LENGTH t) ==> (s = t)
Proof
  rw [rich_listTheory.IS_SUBLIST_APPEND] >>
  `!a b c : num.
     (a + (b + c) = c) ==> (a = 0) /\ (b = 0)` by decide_tac >>
  `(LENGTH l = 0) /\ (LENGTH l' = 0)` by
    (qpat_x_assum `!a b c. _` (mp_tac o
       Q.SPECL [`LENGTH l`, `LENGTH l'`, `LENGTH t`]) >>
     impl_tac >- fs [] >>
     simp []) >>
  fs []
QED

Theorem smt_seq_contains_antisym[local]:
  IS_SUBLIST (s : 'a list) t /\ IS_SUBLIST t s ==> (s = t)
Proof
  metis_tac [smt_seq_contains_length_bound,
             smt_seq_contains_length_equal,
             arithmeticTheory.LESS_EQUAL_ANTISYM]
QED

Theorem smt_seq_replace_self_nil_forward[local]:
  (smt_seq_replace (x : 'a list) y x = []) ==> (x = [])
Proof
  strip_tac >>
  `IS_SUBLIST (smt_seq_replace x y x) x` by
    simp [smt_seq_replace_contains_replacement,
          smt_seq_contains_refl] >>
  fs [rich_listTheory.IS_SUBLIST_APPEND] >>
  metis_tac [listTheory.APPEND_eq_NIL]
QED

Theorem smt_seq_replace_self_nil_reverse[local]:
  ((x : 'a list) = []) ==> (smt_seq_replace x y x = [])
Proof
  strip_tac >>
  simp [smt_seq_replace_def, smt_seq_replace_raw_def,
        smt_seq_indexof_aux_def] >>
  BasicProvers.every_case_tac >> simp []
QED

Theorem smt_seq_replace_self_empty_eq:
  (LENGTH (empty : 'a list) = 0) ==>
  ((smt_seq_replace x y x = empty) <=> (x = empty))
Proof
  Cases_on `empty` >>
  simp [] >>
  metis_tac [smt_seq_replace_self_nil_forward,
             smt_seq_replace_self_nil_reverse]
QED

Theorem smt_seq_replace_self_source_reverse[local]:
  (smt_seq_replace (x : 'a list) y x = y) ==> (x = y)
Proof
  strip_tac >>
  Cases_on `IS_SUBLIST x y`
  >- (`IS_SUBLIST (smt_seq_replace x y x) x` by
        metis_tac [smt_seq_replace_contains_replacement,
                   smt_seq_contains_refl] >>
      `IS_SUBLIST y x` by metis_tac [] >>
      metis_tac [smt_seq_contains_antisym]) >>
  fs [smt_seq_replace_absent]
QED

Theorem smt_seq_replace_self_source_eq:
  (smt_seq_replace (x : 'a list) y x = y) <=> (x = y)
Proof
  metis_tac [smt_seq_replace_self,
             smt_seq_replace_self_source_reverse]
QED

Theorem smt_seq_replace_self_contains:
  IS_SUBLIST (smt_seq_replace (x : 'a list) y x) y <=>
  IS_SUBLIST x y
Proof
  Cases_on `IS_SUBLIST x y`
  >- (`IS_SUBLIST (smt_seq_replace x y x) x` by
        metis_tac [smt_seq_replace_contains_replacement,
                   smt_seq_contains_refl] >>
      metis_tac [smt_seq_contains_trans]) >>
  simp [smt_seq_replace_absent]
QED

Theorem smt_seq_replace_self_target:
  LENGTH (x : 'a list) <= LENGTH y ==>
  (smt_seq_replace x y x = x)
Proof
  strip_tac >>
  Cases_on `IS_SUBLIST x y`
  >- (`x = y` by
        metis_tac [smt_seq_contains_length_bound,
                   smt_seq_contains_length_equal,
                   arithmeticTheory.LESS_EQUAL_ANTISYM] >>
      simp [smt_seq_replace_self]) >>
  simp [smt_seq_replace_absent]
QED

Theorem smt_seq_replace_nested_source_target_absent:
  ~IS_SUBLIST (z : 'a list) w ==>
  (smt_seq_replace x w (smt_seq_replace z x y) =
   smt_seq_replace x w z)
Proof
  strip_tac >>
  Cases_on `IS_SUBLIST x w`
  >- (`~IS_SUBLIST z x` by metis_tac [smt_seq_contains_trans] >>
      simp [smt_seq_replace_absent]) >>
  simp [smt_seq_replace_absent]
QED

Theorem smt_seq_replace_nested_target_self:
  smt_seq_replace (x : 'a list) y (smt_seq_replace y x y) = x
Proof
  Cases_on `IS_SUBLIST x y`
  >- (Cases_on `IS_SUBLIST y x`
      >- (`x = y` by metis_tac [smt_seq_contains_antisym] >>
          simp [smt_seq_replace_self]) >>
      simp [smt_seq_replace_absent, smt_seq_replace_id]) >>
  simp [smt_seq_replace_absent]
QED

Theorem smt_seq_replace_nested_target_absent:
  ~IS_SUBLIST (x : 'a list) z ==>
  (smt_seq_replace x y (smt_seq_replace y z w) = x)
Proof
  strip_tac >>
  Cases_on `IS_SUBLIST x y`
  >- (`~IS_SUBLIST y z` by
        (CCONTR_TAC >> metis_tac [smt_seq_contains_trans]) >>
      simp [smt_seq_replace_absent, smt_seq_replace_id]) >>
  simp [smt_seq_replace_absent]
QED

Theorem smt_seq_replace_nested_source_self:
  smt_seq_replace (x : 'a list) (smt_seq_replace y x y) z =
  smt_seq_replace x y z
Proof
  Cases_on `IS_SUBLIST x y`
  >- (`~IS_SUBLIST y x \/ (x = y)` by
        metis_tac [smt_seq_contains_antisym] >>
      fs [smt_seq_replace_absent, smt_seq_replace_self]) >>
  `IS_SUBLIST (smt_seq_replace y x y) y` by
    metis_tac [smt_seq_replace_contains_replacement,
               smt_seq_contains_refl] >>
  `~IS_SUBLIST x (smt_seq_replace y x y)` by
    (CCONTR_TAC >> metis_tac [smt_seq_contains_trans]) >>
  simp [smt_seq_replace_absent]
QED

Theorem smt_seq_replace_nested_source_inverse_absent1:
  ~IS_SUBLIST (y : 'a list) z ==>
  (smt_seq_replace x (smt_seq_replace y x z) y =
   smt_seq_replace x y y)
Proof
  strip_tac >>
  Cases_on `IS_SUBLIST y x`
  >- (`IS_SUBLIST (smt_seq_replace y x z) z` by
        metis_tac [smt_seq_replace_contains_replacement] >>
      `~IS_SUBLIST x (smt_seq_replace y x z)` by
        (CCONTR_TAC >>
         `IS_SUBLIST x z` by metis_tac [smt_seq_contains_trans] >>
         metis_tac [smt_seq_contains_trans]) >>
      `~IS_SUBLIST x y \/ (x = y)` by
        metis_tac [smt_seq_contains_antisym] >>
      fs [smt_seq_replace_absent, smt_seq_replace_id]) >>
  simp [smt_seq_replace_absent]
QED

Theorem smt_seq_replace_nested_source_inverse_absent2:
  ~IS_SUBLIST (y : 'a list) z ==>
  (smt_seq_replace x (smt_seq_replace y x z) x =
   smt_seq_replace x y x)
Proof
  strip_tac >>
  Cases_on `IS_SUBLIST y x`
  >- (`IS_SUBLIST (smt_seq_replace y x z) z` by
        metis_tac [smt_seq_replace_contains_replacement] >>
      `~IS_SUBLIST x (smt_seq_replace y x z)` by
        (CCONTR_TAC >>
         `IS_SUBLIST x z` by metis_tac [smt_seq_contains_trans] >>
         metis_tac [smt_seq_contains_trans]) >>
      `~IS_SUBLIST x y \/ (x = y)` by
        metis_tac [smt_seq_contains_antisym] >>
      fs [smt_seq_replace_absent, smt_seq_replace_self]) >>
  simp [smt_seq_replace_absent]
QED

Theorem smt_seq_replace_nested_source_inverse_absent3:
  ~IS_SUBLIST (x : 'a list) z /\ ~IS_SUBLIST x w ==>
  (smt_seq_replace x (smt_seq_replace y z w) u =
   smt_seq_replace x y u)
Proof
  strip_tac >>
  Cases_on `IS_SUBLIST y z`
  >- (`IS_SUBLIST (smt_seq_replace y z w) w` by
        metis_tac [smt_seq_replace_contains_replacement] >>
      `~IS_SUBLIST x (smt_seq_replace y z w)` by
        (CCONTR_TAC >> metis_tac [smt_seq_contains_trans]) >>
      `~IS_SUBLIST x y` by
        (CCONTR_TAC >> metis_tac [smt_seq_contains_trans]) >>
      simp [smt_seq_replace_absent]) >>
  simp [smt_seq_replace_absent]
QED

Theorem smt_seq_replace_nested_dual_self:
  smt_seq_replace (x : 'a list) (smt_seq_replace x y x) x = x
Proof
  irule smt_seq_replace_self_target >>
  `IS_SUBLIST (smt_seq_replace x y x) x` by
    metis_tac [smt_seq_replace_contains_replacement,
               smt_seq_contains_refl] >>
  metis_tac [smt_seq_contains_length_bound]
QED

Theorem smt_seq_replace_nested_dual_ite1:
  ~IS_SUBLIST (x : 'a list) z ==>
  (smt_seq_replace x (smt_seq_replace x y z) w =
   if IS_SUBLIST x y then x else w)
Proof
  strip_tac >>
  Cases_on `IS_SUBLIST x y`
  >- (`IS_SUBLIST (smt_seq_replace x y z) z` by
        metis_tac [smt_seq_replace_contains_replacement] >>
      `~IS_SUBLIST x (smt_seq_replace x y z)` by
        (CCONTR_TAC >> metis_tac [smt_seq_contains_trans]) >>
      simp [smt_seq_replace_absent]) >>
  simp [smt_seq_replace_absent, smt_seq_replace_self]
QED

Theorem smt_seq_append_prefix_of_length[local]:
  (a ++ b = c ++ d) /\ LENGTH c <= LENGTH a ==>
  ?e. a = c ++ e
Proof
  rw [listTheory.APPEND_EQ_APPEND] >>
  fs [] >>
  Cases_on `l` >>
  fs []
QED

Theorem smt_seq_suffix_factor_base[local]:
  (y ++ b = c ++ z ++ b ++ d) ==> IS_SUBLIST y z
Proof
  strip_tac >>
  `LENGTH (c ++ z) <= LENGTH y` by
    (qpat_x_assum `_ = _` (mp_tac o AP_TERM ``LENGTH``) >>
     simp [] >> decide_tac) >>
  `?e. y = (c ++ z) ++ e` by
    metis_tac [smt_seq_append_prefix_of_length,
               listTheory.APPEND_ASSOC] >>
  rw [rich_listTheory.IS_SUBLIST_APPEND] >>
  qexistsl [`c`, `e`] >>
  simp []
QED

Theorem smt_seq_replace_factor_comparable[local]:
  (a ++ y ++ b = c ++ a ++ z ++ b ++ d) ==>
  IS_SUBLIST y z \/ IS_SUBLIST z y
Proof
  qid_spec_tac `c` >>
  Induct_on `a`
  >- (gen_tac >>
      strip_tac >>
      `y ++ b = c ++ z ++ b ++ d` by
        (qpat_x_assum `_ = _` mp_tac >>
         simp [listTheory.APPEND_ASSOC]) >>
      disj1_tac >>
      irule smt_seq_suffix_factor_base >>
      qexistsl [`b`, `c`, `d`] >>
      simp []) >>
  rpt gen_tac >>
  Cases_on `c`
  >- (simp [listTheory.APPEND_ASSOC] >>
      strip_tac >>
      disj1_tac >>
      irule smt_seq_suffix_factor_base >>
      qexistsl [`b`, `[]`, `d`] >>
      simp []) >>
  strip_tac >>
  fs [listTheory.APPEND_ASSOC]
QED

Theorem smt_seq_replace_raw_incomparable[local]:
  IS_SUBLIST (s : 'a list) t /\ ~IS_SUBLIST t u /\ ~IS_SUBLIST u t ==>
  ~IS_SUBLIST s (smt_seq_replace_raw s t u)
Proof
  strip_tac >>
  drule_then (qspec_then `u` strip_assume_tac)
    smt_seq_replace_raw_hit >>
  CCONTR_TAC >>
  fs [] >>
  qpat_x_assum `IS_SUBLIST s (smt_seq_replace_raw s t u)`
    (mp_tac o REWRITE_RULE [rich_listTheory.IS_SUBLIST_APPEND]) >>
  strip_tac >>
  qpat_x_assum `s = pre ++ t ++ post` SUBST_ALL_TAC >>
  qpat_x_assum
    `smt_seq_replace_raw (pre ++ t ++ post) t u = pre ++ u ++ post`
    SUBST_ALL_TAC >>
  fs [listTheory.APPEND_ASSOC] >>
  qpat_x_assum
    `pre ++ t ++ post = _ ++ pre ++ u ++ post ++ _`
    (mp_tac o MATCH_MP smt_seq_replace_factor_comparable) >>
  simp [rich_listTheory.IS_SUBLIST_APPEND]
QED

Theorem smt_seq_replace_incomparable_not_contained[local]:
  IS_SUBLIST (x : 'a list) y /\
  ~IS_SUBLIST y z /\ ~IS_SUBLIST z y ==>
  ~IS_SUBLIST x (smt_seq_replace x y z)
Proof
  rw [smt_seq_replace_def] >>
  metis_tac [smt_seq_replace_raw_incomparable]
QED

Theorem smt_seq_replace_nested_dual_ite2:
  ~IS_SUBLIST (y : 'a list) z /\ ~IS_SUBLIST z y ==>
  (smt_seq_replace x (smt_seq_replace x y z) w =
   if IS_SUBLIST x y then x else w)
Proof
  strip_tac >>
  Cases_on `IS_SUBLIST x y`
  >- (`~IS_SUBLIST x (smt_seq_replace x y z)` by
        metis_tac [smt_seq_replace_incomparable_not_contained] >>
      simp [smt_seq_replace_absent]) >>
  simp [smt_seq_replace_absent, smt_seq_replace_self]
QED

Theorem smt_seq_replace_pattern_self_contains:
  IS_SUBLIST (s : 'a list) (smt_seq_replace t s t) <=>
  IS_SUBLIST s t
Proof
  Cases_on `IS_SUBLIST t s`
  >- (eq_tac
      >- (strip_tac >>
          `IS_SUBLIST (smt_seq_replace t s t) t` by
            metis_tac [smt_seq_replace_contains_replacement,
                       smt_seq_contains_refl] >>
          metis_tac [smt_seq_contains_trans]) >>
      strip_tac >>
      `s = t` by metis_tac [smt_seq_contains_antisym] >>
      simp [smt_seq_replace_self, smt_seq_contains_refl]) >>
  simp [smt_seq_replace_absent]
QED

Theorem smt_seq_replace_empty_source_contains:
  (LENGTH (empty : 'a list) = 0) ==>
  (IS_SUBLIST s (smt_seq_replace empty s t) <=>
   (empty = smt_seq_replace empty s t))
Proof
  rw [] >>
  Cases_on `s`
  >- simp [smt_seq_replace_def, smt_seq_replace_raw_def,
           smt_seq_indexof_aux_def, rich_listTheory.IS_SUBLIST_APPEND] >>
  simp [smt_seq_replace_def, smt_seq_replace_raw_def,
        smt_seq_indexof_aux_def, rich_listTheory.IS_SUBLIST_APPEND] >>
  qexistsl [`[]`, `h::t'`] >> simp []
QED

Theorem smt_seq_indexof_zero_nonnegative[local]:
  (0 <= smt_seq_indexof (s : 'a list) t 0 <=> IS_SUBLIST s t)
Proof
  rw [smt_seq_indexof_def] >>
  eq_tac
  >- (Cases_on `smt_seq_indexof_aux t 0 s` >>
      simp [] >>
      drule smt_seq_indexof_aux_split >>
      strip_tac >>
      rw [rich_listTheory.IS_SUBLIST_APPEND] >>
      qexistsl [`pre`, `post`] >>
      simp [])
  >- (strip_tac >>
      Cases_on `smt_seq_indexof_aux t 0 s` >>
      fs [smt_seq_indexof_aux_none])
QED

Theorem smt_seq_replace_raw_append_some[local]:
  (smt_seq_indexof_aux (t : 'a list) 0 s = SOME n) ==>
  (smt_seq_replace_raw (s ++ u) t r =
   smt_seq_replace_raw s t r ++ u)
Proof
  strip_tac >>
  `n + LENGTH t <= LENGTH s` by
    (drule smt_seq_indexof_aux_split >> strip_tac >> fs []) >>
  `smt_seq_indexof_aux t 0 (s ++ u) = SOME n` by
    metis_tac [smt_seq_indexof_aux_append_some] >>
  asm_rewrite_tac [smt_seq_replace_raw_def] >>
  simp [listTheory.TAKE_APPEND1, listTheory.DROP_APPEND1,
        listTheory.APPEND_ASSOC]
QED

Theorem smt_seq_replace_concat_after_match[local]:
  IS_SUBLIST (s : 'a list) t ==>
  (smt_seq_replace (s ++ u) t r = smt_seq_replace s t r ++ u)
Proof
  strip_tac >>
  Cases_on `smt_seq_indexof_aux t 0 s`
  >- fs [smt_seq_indexof_aux_none] >>
  simp [smt_seq_replace_def, smt_seq_replace_raw_append_some]
QED

Theorem smt_seq_replace_known_match_suffix:
  smt_seq_replace ((prefix ++ needle) ++ suffix) needle replacement =
  smt_seq_replace (prefix ++ needle) needle replacement ++ suffix
Proof
  irule smt_seq_replace_concat_after_match >>
  simp [rich_listTheory.IS_SUBLIST_APPEND] >>
  qexistsl [`prefix`, `[]`] >>
  simp []
QED

Theorem smt_seq_is_sublist_singleton[local]:
  IS_SUBLIST (s : 'a list) [h] <=> MEM h s
Proof
  Induct_on `s` >>
  simp [rich_listTheory.IS_SUBLIST, boolTheory.EQ_SYM_EQ]
QED

Theorem smt_seq_is_sublist_append_len_one[local]:
  (LENGTH (sub : 'a list) = 1) ==>
  (IS_SUBLIST (s ++ t) sub <=>
   IS_SUBLIST s sub \/ IS_SUBLIST t sub)
Proof
  Cases_on `sub` >> fs [] >>
  Cases_on `t'` >>
  simp [smt_seq_is_sublist_singleton]
QED

Theorem smt_seq_replace_raw_contains_len_one[local]:
  (LENGTH (w : 'a list) = 1) /\ ~IS_SUBLIST y w ==>
  (IS_SUBLIST (smt_seq_replace_raw x y z) w <=>
   IS_SUBLIST x w \/ (IS_SUBLIST x y /\ IS_SUBLIST z w))
Proof
  strip_tac >>
  Cases_on `IS_SUBLIST x y`
  >- (drule_then (qspec_then `z` strip_assume_tac)
        smt_seq_replace_raw_hit >>
      rw [] >>
      simp [smt_seq_is_sublist_append_len_one] >>
      tautLib.TAUT_TAC) >>
  simp [smt_seq_replace_raw_absent]
QED

Theorem smt_seq_replace_contains_len_one:
  (LENGTH (w : 'a list) = 1) /\ ~IS_SUBLIST y w ==>
  (IS_SUBLIST (smt_seq_replace x y z) w <=>
   IS_SUBLIST x w \/ (IS_SUBLIST x y /\ IS_SUBLIST z w))
Proof
  strip_tac >>
  rw [smt_seq_replace_def] >>
  metis_tac [smt_seq_replace_raw_contains_len_one]
QED

Theorem smt_seq_replace_self_contains_len_one:
  (LENGTH (w : 'a list) = 1) ==>
  (IS_SUBLIST (smt_seq_replace x y x) w <=> IS_SUBLIST x w)
Proof
  strip_tac >>
  Cases_on `IS_SUBLIST y w`
  >- (Cases_on `IS_SUBLIST x y`
      >- (`IS_SUBLIST x w` by metis_tac [smt_seq_contains_trans] >>
          `IS_SUBLIST (smt_seq_replace x y x) x` by
            metis_tac [smt_seq_replace_contains_replacement,
                       smt_seq_contains_refl] >>
          metis_tac [smt_seq_contains_trans]) >>
      simp [smt_seq_replace_absent]) >>
  metis_tac [smt_seq_replace_contains_len_one]
QED

Theorem smt_seq_replace_concat_contained_suffix[local]:
  (LENGTH (t : 'a list) = 1) /\ IS_SUBLIST s u ==>
  (smt_seq_replace (s ++ u) t r = smt_seq_replace s t r ++ u)
Proof
  strip_tac >>
  Cases_on `IS_SUBLIST s t`
  >- simp [smt_seq_replace_concat_after_match] >>
  Cases_on `t` >> fs [] >>
  qpat_x_assum `t' = []` SUBST_ALL_TAC >>
  fs [smt_seq_is_sublist_singleton,
      rich_listTheory.IS_SUBLIST_APPEND, listTheory.MEM_APPEND] >>
  qpat_x_assum `s = _` SUBST_ALL_TAC >>
  fs [listTheory.MEM_APPEND, smt_seq_replace_absent,
      smt_seq_is_sublist_singleton]
QED

Theorem smt_seq_replace_repeated_segment_suffix:
  (LENGTH (sub : 'a list) = 1) ==>
  (smt_seq_replace ((prefix ++ middle ++ suffix) ++ middle) sub replacement =
   smt_seq_replace (prefix ++ middle ++ suffix) sub replacement ++ middle)
Proof
  strip_tac >>
  irule smt_seq_replace_concat_contained_suffix >>
  simp [rich_listTheory.IS_SUBLIST_APPEND] >>
  qexistsl [`prefix`, `suffix`] >>
  simp [listTheory.APPEND_ASSOC]
QED

Theorem smt_seq_replace_find:
  0 <= smt_seq_indexof (s : 'a list) t 0 ==>
  (smt_seq_replace s t r =
   (smt_seq_extract s 0 (smt_seq_indexof s t 0) ++ r) ++
   smt_seq_extract s
     (smt_seq_indexof s t 0 + &(LENGTH t)) (&(LENGTH s)))
Proof
  strip_tac >>
  fs [smt_seq_indexof_def] >>
  Cases_on `smt_seq_indexof_aux t 0 s` >> fs [] >>
  drule smt_seq_indexof_aux_split >>
  strip_tac >>
  qpat_x_assum `LENGTH pre + 0 = x` (SUBST_ALL_TAC o SYM) >>
  fs [smt_seq_replace_def, smt_seq_replace_raw_def,
      smt_seq_extract_def, listTheory.TAKE_APPEND1,
      rich_listTheory.TAKE_LENGTH_APPEND,
      rich_listTheory.DROP_LENGTH_APPEND,
      listTheory.APPEND_ASSOC] >>
  Cases_on `pre` >> Cases_on `t` >> Cases_on `post` >>
  simp [smt_seq_extract_def, integerTheory.INT_OF_NUM_ADD,
        rich_listTheory.DROP_LENGTH_APPEND,
        listTheory.APPEND_ASSOC]
QED

Theorem smt_seq_replace_find_append:
  0 <= smt_seq_indexof (s : 'a list) t 0 ==>
  (smt_seq_replace (s ++ u) t r =
   smt_seq_extract s 0 (smt_seq_indexof s t 0) ++
   (r ++
    (smt_seq_extract s
       (smt_seq_indexof s t 0 + &(LENGTH t)) (&(LENGTH s)) ++ u)))
Proof
  metis_tac [smt_seq_indexof_zero_nonnegative,
             smt_seq_replace_concat_after_match,
             smt_seq_replace_find, listTheory.APPEND_ASSOC]
QED

Theorem smt_seq_indexof_aux_suc[local]:
  !s t n.
    smt_seq_indexof_aux t (SUC n) s =
    OPTION_MAP SUC (smt_seq_indexof_aux t n s)
Proof
  Induct >> Cases_on `t` >> rw [smt_seq_indexof_aux_def] >> simp []
QED

Theorem smt_seq_replace_raw_eq_source_pattern[local]:
  IS_SUBLIST (s : 'a list) t /\
  (smt_seq_replace_raw s t r = s) ==> (r = t)
Proof
  strip_tac >>
  drule_then (qspec_then `r` strip_assume_tac)
    smt_seq_replace_raw_hit >>
  `pre ++ r ++ post = pre ++ t ++ post` by metis_tac [] >>
  `r ++ post = t ++ post` by metis_tac [listTheory.APPEND_11] >>
  metis_tac [listTheory.APPEND_11]
QED

Theorem smt_seq_replace_no_change_reverse[local]:
  y <> (z : 'a list) /\ (smt_seq_replace x y z = x) ==>
  ~IS_SUBLIST x y
Proof
  strip_tac >> CCONTR_TAC >>
  `smt_seq_replace_raw x y z = x` by
    fs [smt_seq_replace_def] >>
  metis_tac [smt_seq_replace_raw_eq_source_pattern]
QED

Theorem smt_seq_replace_no_change_eq:
  y <> (z : 'a list) ==>
  ((smt_seq_replace x y z = x) <=> ~IS_SUBLIST x y)
Proof
  metis_tac [smt_seq_replace_absent,
             smt_seq_replace_no_change_reverse]
QED

Theorem smt_seq_replace_equal_length[local]:
  (LENGTH (t : 'a list) = LENGTH r) ==>
  (LENGTH (smt_seq_replace s t r) = LENGTH s)
Proof
  strip_tac >>
  Cases_on `IS_SUBLIST s t`
  >- (drule_then (qspec_then `r` strip_assume_tac)
        smt_seq_replace_raw_hit >>
      fs [smt_seq_replace_def]) >>
  simp [smt_seq_replace_absent]
QED

Theorem smt_seq_replace_target_equal_length_forward[local]:
  (LENGTH (y : 'a list) = LENGTH z) /\ ((x = y) \/ (x = z)) ==>
  (smt_seq_replace x y z = z)
Proof
  strip_tac >>
  fs [smt_seq_replace_self, smt_seq_replace_self_target]
QED

Theorem smt_seq_replace_target_equal_length_reverse[local]:
  (LENGTH (y : 'a list) = LENGTH z) /\
  (smt_seq_replace x y z = z) ==>
  ((x = y) \/ (x = z))
Proof
  strip_tac >>
  Cases_on `x = y` >> simp [] >>
  Cases_on `IS_SUBLIST x y` >> fs [smt_seq_replace_absent] >>
  `LENGTH (smt_seq_replace x y z) = LENGTH x` by
    metis_tac [smt_seq_replace_equal_length] >>
  `LENGTH x = LENGTH y` by metis_tac [] >>
  metis_tac [smt_seq_contains_length_equal]
QED

Theorem smt_seq_replace_target_equal_length_eq:
  (LENGTH (y : 'a list) = LENGTH z) ==>
  ((smt_seq_replace x y z = z) <=> ((x = y) \/ (x = z)))
Proof
  metis_tac [smt_seq_replace_target_equal_length_forward,
             smt_seq_replace_target_equal_length_reverse]
QED

Theorem smt_seq_indexof_aux_first[local]:
  !s t n.
    (smt_seq_indexof_aux t 0 s = SOME n) ==>
    IS_PREFIX (DROP n s) t /\
    !m. m < n ==> ~IS_PREFIX (DROP m s) t
Proof
  Induct
  >- simp [smt_seq_indexof_aux_def] >>
  rpt gen_tac >>
  rw [smt_seq_indexof_aux_def] >>
  assume_tac (Q.SPECL [`s`, `t`, `0`] smt_seq_indexof_aux_suc) >>
  Cases_on `smt_seq_indexof_aux t 0 s` >>
  fs [] >>
  Cases_on `m` >> fs []
QED

Theorem smt_seq_indexof_aux_first_intro[local]:
  !n s t.
    IS_PREFIX (DROP n s) t /\
    (!m. m < n ==> ~IS_PREFIX (DROP m s) t) ==>
    (smt_seq_indexof_aux t 0 s = SOME n)
Proof
  Induct THENL
  [Cases_on `s` >> rw [smt_seq_indexof_aux_def],
   rpt gen_tac >>
   (Cases_on `s` THENL
    [simp [] >> strip_tac >>
       first_x_assum (qspec_then `0` mp_tac) >> simp [],
     rw [smt_seq_indexof_aux_def] THENL
     [disj2_tac >> qexists_tac `0` >> simp [],
      qpat_x_assum `!s t. _`
        (qspecl_then [`t'`, `t`] mp_tac) >>
      impl_tac
      >- (simp [] >> rpt strip_tac >>
          first_x_assum (qspec_then `SUC m` mp_tac) >> simp []) >>
      strip_tac >>
      assume_tac
        (Q.SPECL [`t'`, `t`, `0`] smt_seq_indexof_aux_suc) >>
      fs []]])]
QED

Theorem smt_seq_inserted_source_no_early[local]:
  (y = pre ++ w ++ post) /\ (LENGTH pre = n) /\
  (!m. m < n ==> ~IS_PREFIX (DROP m y) w) ==>
  !m. m < n ==>
    ~IS_PREFIX (DROP m (pre ++ y ++ post)) y
Proof
  rpt strip_tac >>
  fs [rich_listTheory.IS_PREFIX_APPEND] >>
  qpat_x_assum `DROP m (pre ++ y ++ post) = y ++ l`
    (mp_tac o AP_TERM ``DROP n``) >>
  simp [listTheory.DROP_APPEND1, listTheory.DROP_APPEND2,
        listTheory.APPEND_ASSOC] >>
  strip_tac >>
  first_x_assum (qspec_then `m` mp_tac) >>
  simp [] >>
  `IS_PREFIX ((DROP m pre ++ w ++ post) ++ post) w` by
    (rw [rich_listTheory.IS_PREFIX_APPEND] >>
     qexists_tac `post ++ l` >> fs [listTheory.APPEND_ASSOC]) >>
  `LENGTH w <= LENGTH (DROP m pre ++ w ++ post)` by simp [] >>
  `IS_PREFIX (DROP m pre ++ w ++ post) w` by
    metis_tac [smt_seq_is_prefix_append_short] >>
  fs [rich_listTheory.IS_PREFIX_APPEND] >>
  qexists_tac `l''` >>
  simp [listTheory.DROP_APPEND1] >>
  decide_tac
QED

Theorem smt_seq_replace_raw_lookahead_hit[local]:
  IS_SUBLIST (y : 'a list) w ==>
  (smt_seq_replace_raw (smt_seq_replace_raw y w y) y z =
   smt_seq_replace_raw y w z)
Proof
  strip_tac >>
  Cases_on `smt_seq_indexof_aux w 0 y`
  >- fs [smt_seq_indexof_aux_none] >>
  drule smt_seq_indexof_aux_first >>
  strip_tac >>
  qpat_x_assum `smt_seq_indexof_aux w 0 y = SOME x`
    (fn th => assume_tac th >>
       mp_tac (MATCH_MP smt_seq_indexof_aux_split th)) >>
  strip_tac >>
  qpat_x_assum `LENGTH pre + 0 = x` (SUBST_ALL_TAC o SYM) >>
  `smt_seq_replace_raw y w y = pre ++ y ++ post` by
    simp [smt_seq_replace_raw_def, smt_seq_replace_take_splice,
          smt_seq_replace_drop_splice] >>
  `smt_seq_indexof_aux y 0 (pre ++ y ++ post) =
     SOME (LENGTH pre)` by
    (irule smt_seq_indexof_aux_first_intro >>
     conj_tac
     >- (match_mp_tac smt_seq_inserted_source_no_early >> fs []) >>
     simp [rich_listTheory.DROP_LENGTH_APPEND,
           rich_listTheory.IS_PREFIX_APPEND] >>
     qexists_tac `post` >>
     simp [listTheory.DROP_APPEND1, listTheory.APPEND_ASSOC]) >>
  qpat_x_assum `y = pre ++ w ++ post` SUBST_ALL_TAC >>
  fs [smt_seq_replace_raw_def, smt_seq_replace_take_splice,
      smt_seq_replace_drop_splice, listTheory.APPEND_ASSOC] >>
  simp [listTheory.TAKE_APPEND1, listTheory.DROP_APPEND1]
QED

Theorem smt_seq_replace_lookahead_hit[local]:
  IS_SUBLIST (y : 'a list) w ==>
  (smt_seq_replace (smt_seq_replace y w y) y z =
   smt_seq_replace y w z)
Proof
  rw [smt_seq_replace_def] >>
  metis_tac [smt_seq_replace_raw_lookahead_hit]
QED

Theorem smt_seq_replace_length_le[local]:
  IS_SUBLIST (s : 'a list) t /\ LENGTH r <= LENGTH t ==>
  LENGTH (smt_seq_replace s t r) <= LENGTH s
Proof
  strip_tac >>
  drule_then (qspec_then `r` strip_assume_tac)
    smt_seq_replace_raw_hit >>
  fs [smt_seq_replace_def]
QED

Theorem smt_seq_replace_nested_lookahead_id_simp:
  w <> (z : 'a list) /\ LENGTH z <= LENGTH w ==>
  (smt_seq_replace (smt_seq_replace y w y) y z =
   smt_seq_replace (smt_seq_replace y w z) y z)
Proof
  strip_tac >>
  Cases_on `IS_SUBLIST y w`
  >- (`smt_seq_replace (smt_seq_replace y w y) y z =
         smt_seq_replace y w z` by
        metis_tac [smt_seq_replace_lookahead_hit] >>
      `LENGTH (smt_seq_replace y w z) <= LENGTH y` by
        metis_tac [smt_seq_replace_length_le] >>
      `~IS_SUBLIST (smt_seq_replace y w z) y` by
        (CCONTR_TAC >>
         `LENGTH y <= LENGTH (smt_seq_replace y w z)` by
           metis_tac [smt_seq_contains_length_bound] >>
         `LENGTH (smt_seq_replace y w z) = LENGTH y` by
           decide_tac >>
         `smt_seq_replace y w z = y` by
           metis_tac [smt_seq_contains_length_equal] >>
         metis_tac [smt_seq_replace_no_change_eq]) >>
      simp [smt_seq_replace_absent]) >>
  simp [smt_seq_replace_absent, smt_seq_replace_self]
QED

Theorem smt_seq_replace_raw_singleton_cons[local]:
  smt_seq_replace_raw (h::s) [a] [b] =
  if h = a then b::s else h::smt_seq_replace_raw s [a] [b]
Proof
  simp [smt_seq_replace_raw_def, smt_seq_indexof_aux_def,
        rich_listTheory.IS_PREFIX] >>
  Cases_on `h = a` >> simp [smt_seq_indexof_aux_suc] >>
  assume_tac (SIMP_RULE (srw_ss()) []
    (ISPECL [``s:'a list``, ``[a:'a]``, ``0:num``]
      smt_seq_indexof_aux_suc)) >>
  Cases_on `smt_seq_indexof_aux [a] 0 s` >>
  fs [arithmeticTheory.ADD1]
QED

Theorem smt_seq_replace_raw_singleton_nil[local]:
  smt_seq_replace_raw ([] : 'a list) [a] [b] = []
Proof
  simp [smt_seq_replace_raw_def, smt_seq_indexof_aux_def]
QED

Theorem smt_seq_replace_raw_singleton_eq_nil[local]:
  (smt_seq_replace_raw (s : 'a list) [a] [b] = []) <=> (s = [])
Proof
  Cases_on `s` >>
  simp [smt_seq_replace_raw_singleton_nil,
        smt_seq_replace_raw_singleton_cons] >>
  Cases_on `h = a` >> simp []
QED

Theorem smt_seq_replace_raw_singleton_take[local]:
  !n s.
    TAKE n (smt_seq_replace_raw s [a] [b]) =
    smt_seq_replace_raw (TAKE n s) [a] [b]
Proof
  rpt gen_tac >> qid_spec_tac `s` >> Induct_on `n` >>
  Cases_on `s` >>
  simp [smt_seq_replace_raw_singleton_nil,
        smt_seq_replace_raw_singleton_cons] >>
  Cases_on `h = a` >> fs [boolTheory.EQ_SYM_EQ]
QED

Theorem smt_seq_replace_raw_length_one_take[local]:
  (LENGTH (t : 'a list) = 1) /\ (LENGTH r = 1) ==>
  (TAKE n (smt_seq_replace_raw s t r) =
   smt_seq_replace_raw (TAKE n s) t r)
Proof
  strip_tac >>
  Cases_on `t` >> fs [] >>
  Cases_on `r` >> fs [] >>
  MATCH_ACCEPT_TAC smt_seq_replace_raw_singleton_take
QED

Theorem smt_seq_extract_replace_len_one:
  (LENGTH (t : 'a list) = LENGTH r) /\ (LENGTH t = 1) ==>
  (smt_seq_extract (smt_seq_replace s t r) 0 n =
   smt_seq_replace (smt_seq_extract s 0 n) t r)
Proof
  strip_tac >>
  `LENGTH r = 1` by decide_tac >>
  fs [listTheory.LENGTH_EQ_1] >>
  Cases_on `n <= 0` >>
  Cases_on `s = []` >>
  simp [smt_seq_extract_def, smt_seq_replace_def,
        smt_seq_replace_raw_length_one_take,
        smt_seq_replace_raw_singleton_eq_nil,
        smt_seq_replace_raw_singleton_nil]
QED

Theorem smt_seq_replace_raw_empty_singleton[local]:
  (smt_seq_replace_raw (s : 'a list) [c] [] = []) <=>
  ((s = []) \/ (s = [c]))
Proof
  Cases_on `IS_SUBLIST s [c]`
  >- (drule_then (qspec_then `[]` strip_assume_tac)
        smt_seq_replace_raw_hit >>
      fs [] >>
      eq_tac >> strip_tac >> fs [] >>
      Cases_on `pre` >> Cases_on `post` >> fs []) >>
  `IS_SUBLIST [c] [c]` by
    (rw [rich_listTheory.IS_SUBLIST_APPEND] >>
     qexistsl [`[]`, `[]`] >> simp []) >>
  fs [smt_seq_replace_raw_absent] >>
  metis_tac []
QED

Theorem smt_seq_is_prefix_singleton[local]:
  (((s : 'a list) = []) \/ (s = [c])) <=> isPREFIX s [c]
Proof
  Cases_on `s` >> simp [listTheory.isPREFIX] >>
  Cases_on `t` >> simp [listTheory.isPREFIX]
QED

Theorem smt_seq_replace_empty_result_len_one:
  (LENGTH (empty : 'a list) = 0) /\ (LENGTH y = 1) ==>
  ((smt_seq_replace x y empty = empty) <=> isPREFIX x y)
Proof
  Cases_on `empty` >> fs [] >>
  Cases_on `y` >> fs [] >>
  Cases_on `t` >> fs [smt_seq_replace_def,
                       smt_seq_replace_raw_empty_singleton,
                       smt_seq_is_prefix_singleton]
QED

Theorem smt_seq_contains_empty_source[local]:
  IS_SUBLIST ([] : 'a list) s <=> (s = [])
Proof
  eq_tac >> simp [rich_listTheory.IS_SUBLIST_APPEND] >>
  strip_tac >>
  Cases_on `l` >> Cases_on `l'` >> fs []
QED

Theorem smt_seq_contains_empty_pattern[local]:
  IS_SUBLIST (s : 'a list) []
Proof
  rw [rich_listTheory.IS_SUBLIST_APPEND] >>
  qexistsl [`s`, `[]`] >> simp []
QED

Theorem smt_seq_replace_empty_result_nonempty_forward[local]:
  z <> ([] : 'a list) /\ (smt_seq_replace x y z = []) ==>
  ((x = []) /\ y <> [])
Proof
  strip_tac >>
  `~IS_SUBLIST x y` by
    (CCONTR_TAC >>
     `IS_SUBLIST (smt_seq_replace x y z) z` by
       metis_tac [smt_seq_replace_contains_replacement] >>
     qpat_x_assum `smt_seq_replace x y z = []` SUBST_ALL_TAC >>
     fs [smt_seq_contains_empty_source]) >>
  `x = []` by metis_tac [smt_seq_replace_absent] >>
  fs [smt_seq_contains_empty_source]
QED

Theorem smt_seq_replace_empty_result_nonempty_reverse[local]:
  (x = ([] : 'a list)) /\ y <> [] ==>
  (smt_seq_replace x y z = [])
Proof
  strip_tac >>
  `~IS_SUBLIST ([] : 'a list) y` by
    fs [smt_seq_contains_empty_source] >>
  simp [smt_seq_replace_absent]
QED

Theorem smt_seq_replace_empty_result_nonempty:
  (LENGTH (empty : 'a list) = 0) /\ z <> empty ==>
  ((smt_seq_replace x y z = empty) <=>
   ((x = empty) /\ y <> empty))
Proof
  Cases_on `empty` >> fs [] >>
  metis_tac [smt_seq_replace_empty_result_nonempty_forward,
             smt_seq_replace_empty_result_nonempty_reverse]
QED

Theorem smt_seq_replace_empty_source_nonempty:
  (LENGTH (empty : 'a list) = 0) /\ z <> empty ==>
  ((smt_seq_replace empty x y = z) <=>
   ((x = empty) /\ (y = z)))
Proof
  Cases_on `empty` >> fs [] >>
  Cases_on `x = []` >>
  simp [smt_seq_replace_empty, smt_seq_contains_empty_source,
        smt_seq_replace_absent]
QED

(* The all-occurrences variant consumes a matching source segment before
   continuing.  The fuel is structural: a nonempty match drops at least one
   element, while a mismatch consumes the head. *)
Definition smt_seq_replace_all_aux_def:
  (smt_seq_replace_all_aux 0 (s : 'a list) t u = s) /\
  (smt_seq_replace_all_aux (SUC fuel) [] t u = []) /\
  (smt_seq_replace_all_aux (SUC fuel) (h::s) t u =
     if IS_PREFIX (h::s) t then
       u ++ smt_seq_replace_all_aux fuel (DROP (LENGTH t) (h::s)) t u
     else h::smt_seq_replace_all_aux fuel s t u)
End

Definition smt_seq_replace_all_def:
  smt_seq_replace_all (s : 'a list) t u =
    if t = [] then s else smt_seq_replace_all_aux (LENGTH s) s t u
End

Theorem smt_seq_replace_all_empty:
  ((t : 'a list) = []) ==> (smt_seq_replace_all s t u = s)
Proof
  simp [smt_seq_replace_all_def]
QED

Theorem smt_seq_replace_all_aux_nil[local]:
  !fuel t u. smt_seq_replace_all_aux fuel ([] : 'a list) t u = []
Proof
  Cases >> simp [smt_seq_replace_all_aux_def]
QED

Theorem smt_seq_replace_all_self:
  (s : 'a list) <> [] ==> (smt_seq_replace_all s s u = u)
Proof
  Cases_on `s` >> fs [] >>
  simp [smt_seq_replace_all_def, smt_seq_replace_all_aux_def,
        smt_seq_replace_all_aux_nil,
        rich_listTheory.IS_PREFIX_REFL]
QED

Theorem smt_seq_replace_all_aux_absent[local]:
  !s t u. ~IS_SUBLIST (s : 'a list) t ==>
    (smt_seq_replace_all_aux (LENGTH s) s t u = s)
Proof
  Induct
  >- simp [smt_seq_replace_all_aux_def] >>
  rpt gen_tac >>
  strip_tac >>
  `smt_seq_indexof_aux t 0 (h::s) = NONE` by
    simp [smt_seq_indexof_aux_none] >>
  fs [smt_seq_indexof_aux_def] >>
  `~IS_SUBLIST s t` by
    metis_tac [smt_seq_indexof_aux_none] >>
  simp [smt_seq_replace_all_aux_def] >>
  first_x_assum irule
QED

Theorem smt_seq_replace_all_aux_id[local]:
  !fuel s t. LENGTH (s : 'a list) <= fuel /\ t <> [] ==>
    (smt_seq_replace_all_aux fuel s t t = s)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      `s = []` by (Cases_on `s` >> fs []) >>
      simp [smt_seq_replace_all_aux_def]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `s`
  >- simp [smt_seq_replace_all_aux_def] >>
  rw [smt_seq_replace_all_aux_def]
  >- (`LENGTH (DROP (LENGTH t) (h::t')) <= fuel` by
        (simp [listTheory.LENGTH_DROP] >>
         Cases_on `t` >> fs [] >> decide_tac) >>
      `smt_seq_replace_all_aux fuel
         (DROP (LENGTH t) (h::t')) t t =
       DROP (LENGTH t) (h::t')` by
        (first_x_assum irule >> simp []) >>
      `t ++ DROP (LENGTH t) (h::t') = h::t'` by
        (fs [rich_listTheory.IS_PREFIX_APPEND] >>
         simp [rich_listTheory.DROP_LENGTH_APPEND]) >>
      metis_tac []) >>
  first_x_assum irule >>
  fs [] >>
  decide_tac
QED

Theorem smt_seq_replace_all_absent:
  ~IS_SUBLIST (s : 'a list) t ==> (smt_seq_replace_all s t u = s)
Proof
  strip_tac >>
  rw [smt_seq_replace_all_def] >>
  simp [smt_seq_replace_all_aux_absent]
QED

Theorem smt_seq_replace_all_id:
  smt_seq_replace_all (s : 'a list) t t = s
Proof
  rw [smt_seq_replace_all_def] >>
  simp [smt_seq_replace_all_aux_id]
QED

(* cvc5's update replaces the segment beginning at i.  Like LUPDATE it is
   a no-op outside the source sequence; its replacement is clipped at the
   end of that source sequence. *)
Definition smt_seq_update_def:
  smt_seq_update (s : 'a list) (i : int) (t : 'a list) =
    if i < 0 \/ LENGTH s <= Num i then s
    else TAKE (Num i) s ++ TAKE (LENGTH s - Num i) t ++
      DROP (Num i + LENGTH t) s
End

Theorem smt_seq_update_concat_first:
  (0 <= i) /\ (i + &(LENGTH u) < &(LENGTH s)) ==>
  (smt_seq_update (s ++ tail) i (u : 'a list) =
    smt_seq_extract s 0 i ++ u ++
    smt_seq_extract s (i + &(LENGTH u)) (&(LENGTH s)) ++ tail)
Proof
  strip_tac >>
  `~(i < 0)` by intLib.ARITH_TAC >>
  `0 <= i + &(LENGTH u)` by intLib.ARITH_TAC >>
  `Num (i + &(LENGTH u)) = Num i + LENGTH u` by intLib.ARITH_TAC >>
  `Num (&(LENGTH s)) = LENGTH s` by intLib.ARITH_TAC >>
  `Num i + LENGTH u < LENGTH s` by intLib.ARITH_TAC >>
  `s <> []` by (Cases_on `s` >> fs []) >>
  Cases_on `i = 0` >-
    simp [smt_seq_extract_def, smt_seq_update_def,
          listTheory.TAKE_APPEND1, listTheory.DROP_APPEND1,
          listTheory.TAKE_LENGTH_TOO_LONG] >>
  `~(i <= 0)` by intLib.ARITH_TAC >>
  `~(i + &(LENGTH u) < 0)` by intLib.ARITH_TAC >>
  simp [smt_seq_extract_def, smt_seq_update_def,
        listTheory.TAKE_APPEND1, listTheory.DROP_APPEND1,
        listTheory.TAKE_LENGTH_TOO_LONG]
QED

Theorem list_eq_append_same_length[local]:
  (LENGTH (s : 'a list) = LENGTH t) ==>
  ((s = t ++ u) <=> (s = t) /\ (u = []))
Proof
  metis_tac [listTheory.APPEND_11_LENGTH, listTheory.APPEND_NIL]
QED

Theorem list_eq_prepend_same_length[local]:
  (LENGTH (s : 'a list) = LENGTH t) ==>
  ((s = u ++ t) <=> (s = t) /\ (u = []))
Proof
  metis_tac [listTheory.APPEND_11_LENGTH, listTheory.APPEND]
QED

Theorem list_append_neq_same_length:
  (LENGTH (s : 'a list) = LENGTH t) /\ s <> t ==>
  ((s ++ u = t ++ v) = F)
Proof
  simp [CONJUNCT1 listTheory.APPEND_11_LENGTH]
QED

Theorem list_neq_append_same_length[local]:
  (LENGTH (s : 'a list) = LENGTH t) /\ s <> t ==>
  ((s = t ++ u) = F)
Proof
  metis_tac [list_eq_append_same_length]
QED

Theorem list_neq_prepend_same_length[local]:
  (LENGTH (s : 'a list) = LENGTH t) /\ s <> t ==>
  ((s = u ++ t) = F)
Proof
  metis_tac [list_eq_prepend_same_length]
QED

Theorem list_neq_append_same_int_length[local]:
  (((s : 'a list) = t) <=> F) ==>
  ((&LENGTH s : int) = &LENGTH t) ==>
  ((s = t ++ u) <=> F)
Proof
  simp [list_eq_append_same_length]
QED

Theorem list_neq_prepend_same_int_length[local]:
  (((s : 'a list) = t) <=> F) ==>
  ((&LENGTH s : int) = &LENGTH t) ==>
  ((s = u ++ t) <=> F)
Proof
  simp [list_eq_prepend_same_length]
QED

Theorem list_neq_append2_same_int_length:
  (((s : 'a list) = t) <=> F) ==>
  ((&LENGTH s : int) = &LENGTH t) ==>
  ((s = t ++ u ++ v) <=> F)
Proof
  metis_tac [list_neq_append_same_int_length, listTheory.APPEND_ASSOC]
QED

Theorem list_neq_prepend2_same_int_length:
  (((s : 'a list) = t) <=> F) ==>
  ((&LENGTH s : int) = &LENGTH t) ==>
  ((s = (u ++ v) ++ t) <=> F)
Proof
  metis_tac [list_neq_prepend_same_int_length]
QED

Theorem list_is_suffix_drop[local]:
  IS_SUFFIX (t : 'a list) s <=>
  (s = DROP (LENGTH t - LENGTH s) t)
Proof
  metis_tac [rich_listTheory.IS_SUFFIX_IMP_DROP,
             rich_listTheory.IS_SUFFIX_EQ_DROP']
QED

Theorem smt_seq_suffix_extract:
  IS_SUFFIX (t : 'a list) s <=>
  (s = smt_seq_extract t (&(LENGTH t) - &(LENGTH s)) (&(LENGTH s)))
Proof
  Cases_on `s = []` >-
    simp [smt_seq_extract_def, list_is_suffix_drop] >>
  Cases_on `LENGTH s <= LENGTH t`
  >- (`0 < LENGTH s` by (Cases_on `s` >> fs []) >>
      `~(LENGTH t <= LENGTH t - LENGTH s)` by decide_tac >>
      `Num (&(LENGTH t) - &(LENGTH s)) = LENGTH t - LENGTH s`
        by intLib.ARITH_TAC >>
      `Num (&(LENGTH s)) = LENGTH s` by intLib.ARITH_TAC >>
      simp [list_is_suffix_drop, smt_seq_extract_def,
            integerTheory.INT_LT_SUB_RADD, listTheory.LENGTH_DROP,
            listTheory.TAKE_LENGTH_TOO_LONG]) >>
  `LENGTH t < LENGTH s` by decide_tac >>
  `~IS_SUFFIX t s` by
    (rw [rich_listTheory.IS_SUFFIX_APPEND] >>
     strip_tac >>
     fs [listTheory.LENGTH_APPEND]) >>
  simp [smt_seq_extract_def, integerTheory.INT_LT_SUB_RADD]
QED

Theorem list_suffix_equal_length:
  LENGTH (t : 'a list) <= LENGTH s ==>
  (IS_SUFFIX t s <=> (s = t))
Proof
  rw [rich_listTheory.IS_SUFFIX_APPEND] >>
  eq_tac
  >- (strip_tac >>
      fs [listTheory.LENGTH_APPEND] >>
      `LENGTH l = 0` by decide_tac >>
      fs []) >>
  strip_tac >>
  qexists `[]` >>
  simp []
QED

Theorem list_suffix_length_one:
  (LENGTH (t : 'a list) = 1) ==>
  (IS_SUFFIX t s <=> IS_SUBLIST t s)
Proof
  Cases_on `t` >> fs [] >>
  Cases_on `t'` >> fs [] >>
  rw [rich_listTheory.IS_SUFFIX_APPEND,
      rich_listTheory.IS_SUBLIST_APPEND] >>
  eq_tac
  >- (strip_tac >>
      qexists `l` >>
      qexists `[]` >>
      simp []) >>
  strip_tac >>
  Cases_on `s = []`
  >- (qexists `[h]` >> simp []) >>
  qexists `l` >>
  `0 < LENGTH s` by (Cases_on `s` >> fs []) >>
  `1 = LENGTH l + LENGTH s + LENGTH l'` by
    (qpat_x_assum `[h] = _`
       (assume_tac o AP_TERM ``LENGTH : 'a list -> num``) >>
     fs [listTheory.LENGTH_APPEND]) >>
  `LENGTH l' = 0` by
    decide_tac >>
  fs []
QED

(* cvc5's CPC proof format totalizes integer Euclidean division and modulus.
   Unlike HOL's ediv/emod, these operators have specified zero-divisor
   branches, so model them explicitly in the shared HolSmt theory. *)
Definition smt_ediv_total_def:
  smt_ediv_total a b = if b = 0 then 0 else ediv a b
End

Definition smt_emod_total_def:
  smt_emod_total a b = if b = 0 then a else emod a b
End

Theorem smt_ediv_total_compute[compute]:
  smt_ediv_total a b =
    if b = 0 then 0 else if 0 < b then a / b else -(a / -b)
Proof
  simp [smt_ediv_total_def, integerTheory.EDIV_DEF]
QED

Theorem smt_emod_total_compute[compute]:
  smt_emod_total a b = if b = 0 then a else a % ABS b
Proof
  simp [smt_emod_total_def, integerTheory.EMOD_DEF]
QED

Theorem smt_ediv_total_eq_ediv:
  !a b. b <> 0 ==> (smt_ediv_total a b = ediv a b)
Proof
  simp [smt_ediv_total_def]
QED

Theorem smt_emod_total_eq_emod:
  !a b. b <> 0 ==> (smt_emod_total a b = emod a b)
Proof
  simp [smt_emod_total_def]
QED

Theorem smt_ediv_total_one:
  !a. smt_ediv_total a 1 = a
Proof
  simp [smt_ediv_total_def, integerTheory.EDIV_DEF]
QED

Theorem smt_ediv_total_zero:
  !a. smt_ediv_total a 0 = 0
Proof
  simp [smt_ediv_total_def]
QED

Theorem smt_emod_total_one:
  !a. smt_emod_total a 1 = 0
Proof
  simp [smt_emod_total_def, integerTheory.EMOD_DEF,
        integerTheory.INT_MOD_1]
QED

Theorem smt_emod_total_zero:
  !a. smt_emod_total a 0 = a
Proof
  simp [smt_emod_total_def]
QED

Theorem smt_ediv_total_neg:
  !a b. b < 0 ==> (smt_ediv_total a b = -smt_ediv_total a (-b))
Proof
  rpt gen_tac >> strip_tac >>
  `b <> 0` by intLib.ARITH_TAC >>
  `0 < -b` by intLib.ARITH_TAC >>
  `~(0 < b)` by intLib.ARITH_TAC >>
  `-b <> 0` by intLib.ARITH_TAC >>
  ASM_SIMP_TAC bossLib.arith_ss [smt_ediv_total_def,
    integerTheory.EDIV_DEF]
QED

Theorem smt_emod_total_neg:
  !a b. b < 0 ==> (smt_emod_total a b = smt_emod_total a (-b))
Proof
  rpt gen_tac >> strip_tac >>
  `b <> 0` by intLib.ARITH_TAC >>
  `0 < -b` by intLib.ARITH_TAC >>
  `~(0 < b)` by intLib.ARITH_TAC >>
  `-b <> 0` by intLib.ARITH_TAC >>
  ASM_SIMP_TAC bossLib.arith_ss [smt_emod_total_def,
    integerTheory.EMOD_DEF, integerTheory.INT_ABS_NEG]
QED

Theorem smt_emod_ediv_neg:
  !a b. b < 0 ==> (emod a b = a - b * ediv a b)
Proof
  rpt gen_tac >> strip_tac >>
  SUBGOAL_THEN ``(-b:int) <> 0`` ASSUME_TAC THEN1 intLib.ARITH_TAC >>
  SUBGOAL_THEN ``(0:int) < -b`` ASSUME_TAC THEN1 intLib.ARITH_TAC >>
  SUBGOAL_THEN ``~((0:int) < b)`` ASSUME_TAC THEN1 intLib.ARITH_TAC >>
  MP_TAC (Q.SPEC `a:int`
    (MATCH_MP (Q.SPEC `-b:int` integerTheory.INT_DIVISION)
      (ASSUME ``(-b:int) <> 0``))) >>
  STRIP_TAC >>
  ASM_SIMP_TAC bossLib.arith_ss [integerTheory.EDIV_DEF,
    integerTheory.EMOD_DEF, integerTheory.INT_ABS] >>
  intLib.ARITH_TAC
QED

Theorem smt_emod_ediv_pos:
  !a b. 0 < b ==> (emod a b = a - b * ediv a b)
Proof
  rpt gen_tac >> strip_tac >>
  SUBGOAL_THEN ``(b:int) <> 0`` ASSUME_TAC THEN1 intLib.ARITH_TAC >>
  SUBGOAL_THEN ``~((b:int) < 0)`` ASSUME_TAC THEN1 intLib.ARITH_TAC >>
  MP_TAC (Q.SPEC `a:int`
    (MATCH_MP (Q.SPEC `b:int` integerTheory.INT_DIVISION)
      (ASSUME ``(b:int) <> 0``))) >>
  STRIP_TAC >>
  ASM_SIMP_TAC bossLib.arith_ss [integerTheory.EDIV_DEF,
    integerTheory.EMOD_DEF, integerTheory.INT_ABS] >>
  intLib.ARITH_TAC
QED

Theorem smt_ediv_bounds_pos_aux:
  !q r v:int. 0 < v /\ 0 <= r /\ r < v ==>
    v * q <= q * v + r /\ q * v + r < v * (q + 1)
Proof
  rpt gen_tac >> strip_tac >> CONJ_TAC
  >- (CONV_TAC (LAND_CONV (REWR_CONV
        (Q.SPECL [`q:int`, `v:int`] integerTheory.INT_MUL_COMM))) >>
      ASM_SIMP_TAC bossLib.arith_ss [integerTheory.INT_LE_ADDR])
  >- (CONV_TAC (RAND_CONV (REWR_CONV integerTheory.INT_LDISTRIB)) >>
      CONV_TAC (RAND_CONV (LAND_CONV (REWR_CONV
        (Q.SPECL [`q:int`, `v:int`] integerTheory.INT_MUL_COMM)))) >>
      ASM_SIMP_TAC bossLib.arith_ss [integerTheory.INT_LT_LADD,
        integerTheory.INT_MUL_RID])
QED

Theorem smt_ediv_bounds_neg_aux:
  !q r v:int. v < 0 /\ 0 <= r /\ r < -v ==>
    v * -q <= q * -v + r /\ q * -v + r < v * (-q - 1)
Proof
  rpt gen_tac >> strip_tac >> CONJ_TAC
  >- (REWRITE_TAC [integerTheory.INT_MUL_RNEG] >>
      CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV
        (Q.SPECL [`q:int`, `v:int`] integerTheory.INT_MUL_COMM)))) >>
      ASM_SIMP_TAC bossLib.arith_ss [integerTheory.INT_LE_ADDR])
  >- (REWRITE_TAC [integerTheory.INT_SUB_LDISTRIB,
        integerTheory.INT_MUL_RNEG, integerTheory.INT_MUL_RID] >>
      CONV_TAC (LAND_CONV (LAND_CONV (RAND_CONV (REWR_CONV
        (Q.SPECL [`v:int`, `q:int`] integerTheory.INT_MUL_COMM))))) >>
      ASM_SIMP_TAC bossLib.arith_ss [integerTheory.int_sub,
        integerTheory.INT_LT_LADD])
QED

Theorem smt_ediv_bounds_pos_bridge:
  !q r u v:int. 0 < v /\ 0 <= r /\ r < v /\
    (u = q * v + r) ==>
    v * q <= u /\ u < v * (q + 1)
Proof
  rpt gen_tac >> strip_tac >>
  METIS_TAC [smt_ediv_bounds_pos_aux]
QED

Theorem smt_ediv_bounds_neg_bridge:
  !q r u v:int. v < 0 /\ 0 <= r /\ r < -v /\
    (u = q * -v + r) ==>
    v * -q <= u /\ u < v * (-q - 1)
Proof
  rpt gen_tac >> strip_tac >>
  METIS_TAC [smt_ediv_bounds_neg_aux]
QED

Theorem smt_ediv_total_bounds:
  !u v.
    (0 < v ==> v * smt_ediv_total u v <= u /\
               u < v * (smt_ediv_total u v + 1)) /\
    (v < 0 ==> v * smt_ediv_total u v <= u /\
               u < v * (smt_ediv_total u v - 1))
Proof
  rpt gen_tac >> CONJ_TAC
  >- (strip_tac >>
      `v <> 0` by intLib.ARITH_TAC >>
      MP_TAC (Q.SPEC `u:int`
        (MATCH_MP (Q.SPEC `v:int` integerTheory.INT_DIVISION)
          (ASSUME ``(v:int) <> 0``))) >>
      STRIP_TAC >>
      `~((v:int) < 0)` by intLib.ARITH_TAC >>
      Q.PAT_X_ASSUM `if (v:int) < 0 then _ else _`
        (fn h => MP_TAC h >>
          ASM_SIMP_TAC bossLib.arith_ss [] >>
          STRIP_TAC >>
          ASM_SIMP_TAC bossLib.arith_ss [smt_ediv_total_def,
            integerTheory.EDIV_DEF] >>
          MATCH_MP_TAC (Q.SPECL
            [`u / v:int`, `u % v:int`, `u:int`, `v:int`]
            smt_ediv_bounds_pos_bridge) >>
          CONJ_TAC
          >- ACCEPT_TAC (ASSUME ``(0:int) < v``)
          >- (CONJ_TAC
              >- ACCEPT_TAC (ASSUME ``(0:int) <= u % v``)
              >- (CONJ_TAC
                  >- ACCEPT_TAC (ASSUME ``(u % v:int) < v``)
                  >- ACCEPT_TAC
                    (ASSUME ``(u:int) = u / v * v + u % v``)))))
  >- (strip_tac >>
      `(-v:int) <> 0` by intLib.ARITH_TAC >>
      `0 < (-v:int)` by intLib.ARITH_TAC >>
      `~((-v:int) < 0)` by intLib.ARITH_TAC >>
      `~((0:int) < v)` by intLib.ARITH_TAC >>
      `(v:int) <> 0` by intLib.ARITH_TAC >>
      MP_TAC (Q.SPEC `u:int`
        (MATCH_MP (Q.SPEC `-v:int` integerTheory.INT_DIVISION)
          (ASSUME ``(-v:int) <> 0``))) >>
      STRIP_TAC >>
      Q.PAT_X_ASSUM `if (-v:int) < 0 then _ else _`
        (fn h => MP_TAC h >>
          ASM_SIMP_TAC bossLib.arith_ss [] >>
          STRIP_TAC >>
          ASM_SIMP_TAC bossLib.arith_ss [smt_ediv_total_def,
            integerTheory.EDIV_DEF] >>
          MATCH_MP_TAC (Q.SPECL
            [`u / -v:int`, `u % -v:int`, `u:int`, `v:int`]
            smt_ediv_bounds_neg_bridge) >>
          CONJ_TAC
          >- ACCEPT_TAC (ASSUME ``(v:int) < 0``)
          >- (CONJ_TAC
              >- ACCEPT_TAC (ASSUME ``(0:int) <= u % -v``)
              >- (CONJ_TAC
                  >- ACCEPT_TAC (ASSUME ``(u % -v:int) < -v``)
                  >- ACCEPT_TAC
                    (ASSUME ``(u:int) = u / -v * -v + u % -v``)))))
QED

Theorem smt_emod_total_ediv:
  !a b. smt_emod_total a b = a - b * smt_ediv_total a b
Proof
  gen_tac >> gen_tac >> Cases_on `b = 0` THENL
  [ simp [smt_ediv_total_def, smt_emod_total_def],
    ASM_REWRITE_TAC [smt_ediv_total_def, smt_emod_total_def] >>
    Cases_on `b < 0` THENL
    [ ACCEPT_TAC (Q.SPEC `a:int`
        (MATCH_MP smt_emod_ediv_neg
          (ASSUME ``(b:int) < 0``))),
      `0 < b` by intLib.ARITH_TAC >>
      ACCEPT_TAC (Q.SPEC `a:int`
        (MATCH_MP smt_emod_ediv_pos
          (ASSUME ``(0:int) < b``))) ] ]
QED

Theorem smt_int_abs_gt:
  !x y : int.
    (ABS x > ABS y) =
    if x >= 0 then
      if y >= 0 then x > y else x > -y
    else if y >= 0 then -x > y else -x > -y
Proof
  rw [integerTheory.INT_ABS, integerTheory.INT_GT,
      integerTheory.INT_GE, integerTheory.int_le]
QED

Theorem smt_int_abs_mul_gt:
  !a b t u : int.
    (ABS a > ABS b) /\ (ABS t = ABS u) /\ t <> 0 ==>
    (ABS (a * t) > ABS (b * u))
Proof
  rpt strip_tac >>
  `0 < ABS t` by simp [] >>
  `0 < ABS a - ABS b` by
    fs [integerTheory.INT_SUB_LT, integerTheory.INT_GT] >>
  `0 < (ABS a - ABS b) * ABS t` by
    (match_mp_tac (REWRITE_RULE [integerTheory.INT_0]
       integerTheory.INT_LT_MUL) >> fs []) >>
  fs [GSYM integerTheory.INT_ABS_MUL, integerTheory.INT_GT,
      integerTheory.int_sub, integerTheory.INT_RDISTRIB,
      GSYM integerTheory.INT_NEG_LMUL] >>
  Q.PAT_X_ASSUM `ABS t = ABS u`
    (fn th => REWRITE_TAC [GSYM th]) >>
  intLib.ARITH_TAC
QED

  (* exclusive or *)
  val xor_def = bossLib.Define `xor x y = ~(x <=> y)`

  (* array_ext[T] yields an index i such that select A i <> select B i
     (provided A and B are different arrays of type T) *)
  val array_ext_def = bossLib.Define `array_ext A B = @i. A i <> B i`

  (* translation of HOL constants *)

  val int_ceiling_floor = s ("int_ceiling_floor",
    M [intrealTheory.INT_CEILING_NEG, realTheory.REAL_NEGNEG]
      ``!r. clgtoks r = -flrtoks (-r)``)

  (* used for Z3 proof reconstruction *)

  val _ = s ("ALL_DISTINCT_NIL", S ``ALL_DISTINCT [] = T``)
  val _ = s ("ALL_DISTINCT_CONS", S
    ``!h t. ALL_DISTINCT (h::t) = ~MEM h t /\ ALL_DISTINCT t``)
  val _ = s ("NOT_MEM_NIL", S ``!x. ~MEM x [] = T``)
  val _ = s ("NOT_MEM_CONS", S ``!x h t. ~MEM x (h::t) = (x <> h) /\ ~MEM x t``)
  val _ = s ("AND_T", T ``!p. p /\ T <=> p``)
  val _ = s ("T_AND", T ``(T /\ p <=> T /\ q) ==> (p <=> q)``)
  val _ = s ("F_OR", T ``(F \/ p <=> F \/ q) ==> (p <=> q)``)
  val _ = s ("CONJ_CONG", T ``(p <=> q) ==> (r <=> s) ==> (p /\ r <=> q /\ s)``)
  val _ = s ("NOT_NOT_ELIM", T ``!p. ~~p ==> p``)
  val _ = s ("NOT_NOT_INTRO", T ``!p. p <=> ~~p``)
  val _ = s ("NOT_REVERSE", T ``(p <=> ~q) ==> (q <=> ~p)``)
  val _ = s ("NOT_FALSE", T ``!p. p ==> ~p ==> F``)
  val _ = s ("NNF_CONJ", T
    ``!p q r s. (~p <=> r) ==> (~q <=> s) ==> (~(p /\ q) <=> r \/ s)``)
  val _ = s ("NNF_DISJ", T
    ``!p q r s. (~p <=> r) ==> (~q <=> s) ==> (~(p \/ q) <=> r /\ s)``)
  val _ = s ("NNF_NOT_NOT", T ``!p q. (p <=> q) ==> (~~p <=> q)``)
  val _ = s ("NEG_IFF_1_1", T ``(q <=> p) ==> ~(p <=> ~q)``)
  val _ = s ("NEG_IFF_1_2", T ``~(p <=> ~q) ==> (q <=> p)``)
  val _ = s ("NEG_IFF_2_1", T ``(p <=> ~q) ==> ~(p <=> q)``)
  val _ = s ("NEG_IFF_2_2", T ``~(p <=> q) ==> (p <=> ~q)``)
  val _ = s ("DISJ_ELIM_1", T ``!p q r. (p \/ q ==> r) ==> p ==> r``)
  val _ = s ("DISJ_ELIM_2", T ``!p q r. (p \/ q ==> r) ==> q ==> r``)
  val _ = s ("IMP_DISJ_1", T ``(p ==> q) ==> ~p \/ q``)
  val _ = s ("IMP_DISJ_2", T ``(~p ==> q) ==> p \/ q``)
  val _ = s ("IMP_FALSE", T ``!p. (~p ==> F) ==> p``)
  val _ = s ("AND_IMP_INTRO_SYM", T ``p /\ q ==> r <=> p ==> q ==> r``)
  val _ = s ("VALID_IFF_TRUE", T ``!p. p ==> (p <=> T)``)
  val _ = s ("NOT_P_OR_P", T ``~p \/ p``)
  val _ = s ("SKOLEM_FORALL", P ``?a. ~(!x. P x) <=> ~(P a)``)
  val _ = s ("SKOLEM_EXISTS", P ``?a. (?x. P x) <=> P a``)

  val _ = s ("NUM_FORALL_TO_INT",
    M [integerTheory.INT_POS, integerTheory.NUM_OF_INT,
       integerTheory.INT_OF_NUM]
      ``!P. (!n :num. P n) <=> (!i :int. 0 <= i ==> P (Num i))``)
  val _ = s ("NUM_EXISTS_TO_INT",
    M [integerTheory.INT_POS, integerTheory.NUM_OF_INT,
       integerTheory.INT_OF_NUM]
      ``!P. (?n :num. P n) <=> (?i :int. 0 <= i /\ P (Num i))``)

  val _ = s ("NUM_TO_INT_GUARDED",
    M [integerTheory.INT_OF_NUM]
      ``!i :int. 0 <= i ==> (integer$int_of_num (Num i) = i)``)

  (* Bags are functions into num.  Relativizing that codomain by the same
     proved R1 pass used for a bare num gives the Int-array representation
     exactly its required pointwise non-negativity condition. *)
Theorem BAG_FORALL_TO_INT:
  !P. (!b : 'a -> num. P b) <=>
      (!c : 'a -> int. (!x. 0 <= c x) ==> P (\x. Num (c x)))
Proof
  gen_tac >> eq_tac
  >- (strip_tac >> gen_tac >> strip_tac >>
      qpat_x_assum `!b. P b`
        (fn th => ACCEPT_TAC (Q.SPEC `\x. Num (c x)` th)))
  >> strip_tac >> gen_tac >>
     qpat_x_assum `!c. (!x. 0 <= c x) ==> P (\x. Num (c x))`
       (mp_tac o Q.SPEC `\x. &(b x)`) >>
     Q.SUBGOAL_THEN `(\x. b x) = b` (fn th => simp[th]) >>
     simp[boolTheory.FUN_EQ_THM]
QED

Theorem BAG_EXISTS_TO_INT:
  !P. (?b : 'a -> num. P b) <=>
      (?c : 'a -> int. (!x. 0 <= c x) /\ P (\x. Num (c x)))
Proof
  gen_tac >> eq_tac
  >- (strip_tac >> qexists_tac `\x. &(b x)` >>
      Q.SUBGOAL_THEN `(\x. b x) = b` (fn th => simp[th]) >>
      simp[boolTheory.FUN_EQ_THM])
  >> strip_tac >> qexists_tac `\x. Num (c x)` >>
     qpat_x_assum `P (\x. Num (c x))` ACCEPT_TAC
QED

  (* NUM_FLOOR is the natural-valued floor.  Below zero it is definitionally
     zero, so this closes the non-positive branch before num-to-int transfer
     instead of leaving a num-valued operator for the SMT encoder. *)
  val num_floor_nonpos = s ("num_floor_nonpos",
    M [realTheory.NUM_FLOOR_BASE, realTheory.REAL_LT_01,
       realTheory.REAL_LET_TRANS]
      ``!r. r <= 0 ==> (realax$NUM_FLOOR r = 0)``)

  (* Associativity of saturated natural subtraction.  Normalizing this
     identity before SMT translation avoids an otherwise large ite-expanded
     checked cvc5 arithmetic replay. *)
Theorem num_sub_assoc:
    !x y z:num. x - y - z = x - (y + z)
Proof
    Induct_on `x` >> simp[]
QED

Theorem num_floor_zero:
    realax$NUM_FLOOR 0r = 0n
Proof
    simp[]
QED

Theorem num_ceiling_zero:
    realax$NUM_CEILING 0r = 0n
Proof
    simp [int_ceiling_floor]
QED

  (* The cvc5 floor-introduction replay rule uses the remainder formulation
     of the floor
     bounds.  Derive it once from HOL's canonical floor interval theorem. *)
Theorem int_floor_remainder_bounds:
    !r.
      (0r <= r - real_of_int (intreal$INT_FLOOR r) /\
       r - real_of_int (intreal$INT_FLOOR r) < 1r)
Proof
    METIS_TAC [intrealTheory.INT_FLOOR_BOUNDS',
      R ``!r f:real.
          (r - 1r < f /\ f <= r) ==>
          (0r <= r - f /\ r - f < 1r)``]
QED

Theorem int_floor_zero[local]:
    intreal$INT_FLOOR 0r = 0i
Proof
    simp [intrealTheory.INT_FLOOR]
QED

Theorem int_floor_nonneg[local]:
    !r. 0r <= r ==> 0i <= intreal$INT_FLOOR r
Proof
    rpt strip_tac >> Cases_on `r = 0r` >- simp [int_floor_zero] >>
    `0r < r` by metis_tac [realTheory.REAL_LE_LT] >>
    `intreal$INT_FLOOR 0r <= intreal$INT_FLOOR r` by
      metis_tac [intrealTheory.INT_FLOOR_MONO] >>
    metis_tac [int_floor_zero]
QED

Theorem int_floor_nonpos[local]:
    !r. r <= 0r ==> intreal$INT_FLOOR r <= 0i
Proof
    rpt strip_tac >> Cases_on `r = 0r` >- simp [int_floor_zero] >>
    `r < 0r` by metis_tac [realTheory.REAL_LE_LT] >>
    `intreal$INT_FLOOR r <= intreal$INT_FLOOR 0r` by
      metis_tac [intrealTheory.INT_FLOOR_MONO] >>
    metis_tac [int_floor_zero]
QED

Theorem int_max_id[local]:
    !i:int. 0i <= i ==> (integer$int_max 0 i = i)
Proof
    rpt strip_tac >> simp [integerTheory.INT_MAX] >> intLib.ARITH_TAC
QED

Theorem int_max_zero[local]:
    !i:int. i <= 0i ==> (integer$int_max 0 i = 0)
Proof
    rpt strip_tac >> simp [integerTheory.INT_MAX] >> intLib.ARITH_TAC
QED

Theorem int_ceiling_nonneg[local]:
    !r. 0r <= r ==> 0i <= intreal$INT_CEILING r
Proof
    rpt strip_tac >>
    `-r <= 0r` by simp[] >>
    `intreal$INT_FLOOR (-r) <= 0i` by
      metis_tac [int_floor_nonpos] >>
    rw [int_ceiling_floor] >> intLib.ARITH_TAC
QED

Theorem int_ceiling_nonpos[local]:
    !r. r <= 0r ==> intreal$INT_CEILING r <= 0i
Proof
    rpt strip_tac >>
    `0r <= -r` by simp[] >>
    `0i <= intreal$INT_FLOOR (-r)` by
      metis_tac [int_floor_nonneg] >>
    rw [int_ceiling_floor] >> intLib.ARITH_TAC
QED

Theorem int_num_ceiling_total:
    !r. &(realax$NUM_CEILING r) =
        integer$int_max 0 (intreal$INT_CEILING r)
Proof
    gen_tac >> Cases_on `0r <= r`
    >- (rw [intrealTheory.INT_NUM_CEILING] >>
        sym_tac >> metis_tac [int_max_id, int_ceiling_nonneg])
    >- (`r <= 0r` by metis_tac [realTheory.REAL_NOT_LE,
                                 realTheory.REAL_LT_IMP_LE] >>
        rw [realTheory.NUM_CEILING_BASE] >>
        sym_tac >> metis_tac [int_max_zero, int_ceiling_nonpos,
                              int_ceiling_floor])
QED

  val _ = s ("num_ceiling_to_int_eq",
    M [int_num_ceiling_total, integerTheory.INT_INJ]
      ``!r n. (realax$NUM_CEILING r = n) <=>
          (integer$int_max 0 (intreal$INT_CEILING r) = &n)``)

Theorem int_num_floor_total:
    !r. &(realax$NUM_FLOOR r) =
        integer$int_max 0 (intreal$INT_FLOOR r)
Proof
    gen_tac >> Cases_on `0r <= r`
    >- (rw [intrealTheory.INT_NUM_FLOOR] >>
        sym_tac >> metis_tac [int_max_id, int_floor_nonneg])
    >- (`r <= 0r` by metis_tac [realTheory.REAL_NOT_LE,
                                 realTheory.REAL_LT_IMP_LE] >>
        rw [num_floor_nonpos] >>
        sym_tac >> metis_tac [int_max_zero, int_floor_nonpos])
QED

  val _ = s ("num_floor_to_int_eq",
    M [int_num_floor_total, integerTheory.INT_INJ]
      ``!r n. (realax$NUM_FLOOR r = n) <=>
          (integer$int_max 0 (intreal$INT_FLOOR r) = &n)``)

  val _ = s ("INT_NUM_EDIV",
    prove(
      ``!n m. integer$int_of_num (n DIV m) =
          if integer$int_of_num m = 0i then 0i
          else integer$ediv (integer$int_of_num n) (integer$int_of_num m)``,
      rpt strip_tac >> Cases_on `m` >- fs[] >>
      `integer$int_of_num (SUC n') <> 0i`
        by fs[integerTheory.INT_INJ] >>
      `0i < integer$int_of_num (SUC n')`
        by fs[integerTheory.INT_LT] >>
      metis_tac[integerTheory.INT_DIV, integerTheory.INT_DIV_EDIV]))

  val _ = s ("INT_NUM_EMOD",
    prove(
      ``!n m. integer$int_of_num (n MOD m) =
          if integer$int_of_num m = 0i then integer$int_of_num n
          else integer$emod (integer$int_of_num n) (integer$int_of_num m)``,
      rpt strip_tac >> Cases_on `m` >- fs[] >>
      `integer$int_of_num (SUC n') <> 0i`
        by fs[integerTheory.INT_INJ] >>
      `0i < integer$int_of_num (SUC n')`
        by fs[integerTheory.INT_LT] >>
      metis_tac[integerTheory.INT_MOD, integerTheory.INT_MOD_EMOD]))

  (* used for Z3's proof rule def-axiom *)

  val _ = s ("d001", T ``~(p <=> q) \/ ~p \/ q``)
  val _ = s ("d002", T ``~(p <=> q) \/ p \/ ~q``)
  val _ = s ("d003", T ``(p <=> ~q) \/ ~p \/ q``)
  val _ = s ("d004", T ``(~p <=> q) \/ p \/ ~q``)
  val _ = s ("d005", T ``(p <=> q) \/ ~p \/ ~q``)
  val _ = s ("d006", T ``(p <=> q) \/ p \/ q``)
  val _ = s ("d007", T ``~(~p <=> q) \/ p \/ q``)
  val _ = s ("d008", T ``~(p <=> ~q) \/ p \/ q``)
  val _ = s ("d009", T ``~p \/ q \/ ~(p <=> q)``)
  val _ = s ("d010", T ``p \/ ~q \/ ~(p <=> q)``)
  val _ = s ("d011", T ``p \/ q \/ ~(~p <=> q)``)
  val _ = s ("d012", T ``p \/ q \/ ~(p <=> ~q)``)
  val _ = s ("d013", T ``(~p /\ ~q) \/ p \/ q``)
  val _ = s ("d014", T ``(~p /\ q) \/ p \/ ~q``)
  val _ = s ("d015", T ``(p /\ ~q) \/ ~p \/ q``)
  val _ = s ("d016", T ``(p /\ q) \/ ~p \/ ~q``)
  val _ = s ("d017", P ``p \/ (y = if p then x else y)``)
  val _ = s ("d018", P ``~p \/ (x = if p then x else y)``)
  val _ = s ("d019", P ``p \/ ((if p then x else y) = y)``)
  val _ = s ("d020", P ``~p \/ ((if p then x else y) = x)``)
  val _ = s ("d021", P ``p \/ q \/ ~(if p then r else q)``)
  val _ = s ("d022", P ``~p \/ q \/ ~(if p then q else r)``)
  val _ = s ("d023", P ``(if p then q else r) \/ ~p \/ ~q``)
  val _ = s ("d024", P ``(if p then q else r) \/ p \/ ~r``)
  val _ = s ("d025", P ``(if p then ~q else r) \/ ~p \/ q``)
  val _ = s ("d026", P ``(if p then q else ~r) \/ p \/ r``)
  val _ = s ("d027", P ``~(if p then q else r) \/ ~p \/ q``)
  val _ = s ("d028", P ``~(if p then q else r) \/ p \/ r``)

  (* used for Z3's proof rule rewrite *)

  val _ = s ("r001", P ``(x = y) <=> (y = x)``)
  val _ = s ("r002", P ``(x = x) <=> T``)
  val _ = s ("r003", T ``(p <=> T) <=> p``)
  val _ = s ("r004", T ``(T <=> p) <=> p``)
  val _ = s ("r005", T ``(p <=> F) <=> ~p``)
  val _ = s ("r006", T ``(F <=> p) <=> ~p``)
  val _ = s ("r007", T ``(~p <=> ~q) <=> (p <=> q)``)
  val _ = s ("r008", T ``~(p <=> ~q) <=> (p <=> q)``)
  val _ = s ("r009", T ``~(~p <=> q) <=> (p <=> q)``)
  val _ = s ("r010", T ``(~p <=> q) <=> (p <=/=> q)``)

  val _ = s ("r011", P ``(if T then x else y) = x``)
  val _ = s ("r012", P ``(if F then x else y) = y``)
  val _ = s ("r014", T ``(if p then q else T) <=> (q \/ ~p)``)
  val _ = s ("r015", T ``(if p then q else ~q) <=> (p <=> q)``)
  val _ = s ("r016", T ``(if p then q else ~q) <=> (q <=> p)``)
  val _ = s ("r017", T ``(if p then ~q else q) <=> (p <=> ~q)``)
  val _ = s ("r018", T ``(if p then ~q else q) <=> (~q <=> p)``)
  val _ = s ("r019", P ``(if ~p then x else y) = (if p then y else x)``)
  val _ = s ("r020", P
    ``(if p then (if q then x else y) else x) = (if p /\ ~q then y else x)``)
  val _ = s ("r022", P
    ``(if p then (if q then x else y) else y) = (if p /\ q then x else y)``)
  val _ = s ("r024", P
    ``(if p then x else (if p then y else z)) = (if p then x else z)``)
  val _ = s ("r026", P
    ``(if p then x else (if q then x else y)) = (if q \/ p then x else y)``)
  val _ = s ("r027", P
    ``(if p then x = y else x = z) <=> (x = if p then y else z)``)
  val _ = s ("r028", P
    ``(if p then x = y else y = z) <=> (y = if p then x else z)``)
  val _ = s ("r029", P
    ``(if p then x = y else z = y) <=> (y = if p then x else z)``)

  val _ = s ("r031", T ``(~p ==> q) <=> (q \/ p)``)
  val _ = s ("r032", T ``~(p ==> q) <=> ~(~p \/ q)``)
  val _ = s ("r037", T ``(p ==> q) <=> (~p \/ q)``)
  val _ = s ("r038", T ``(p ==> q) <=> (q \/ ~p)``)
  val _ = s ("r039", T ``(T ==> p) <=> p``)
  val _ = s ("r040", T ``(p ==> T) <=> T``)
  val _ = s ("r041", T ``(F ==> p) <=> T``)
  val _ = s ("r042", T ``(p ==> p) <=> T``)
  val _ = s ("r043", T ``((p <=> q) ==> r) <=> (r \/ (q <=> ~p))``)

  val _ = s ("r044", T ``~T <=> F``)
  val _ = s ("r045", T ``~F <=> T``)
  val _ = s ("r046", T ``~~p <=> p``)

  val _ = s ("r047", T ``p \/ q <=> q \/ p``)
  val _ = s ("r048", T ``p \/ T <=> T``)
  val _ = s ("r049", T ``p \/ ~p <=> T``)
  val _ = s ("r050", T ``~p \/ p <=> T``)
  val _ = s ("r051", T ``T \/ p <=> T``)
  val _ = s ("r052", T ``p \/ F <=> p``)
  val _ = s ("r053", T ``F \/ p <=> p``)

  val _ = s ("r054", T ``p /\ q <=> q /\ p``)
  val _ = s ("r055", T ``p /\ T <=> p``)
  val _ = s ("r056", T ``T /\ p <=> p``)
  val _ = s ("r057", T ``p /\ F <=> F``)
  val _ = s ("r058", T ``F /\ p <=> F``)
  val _ = s ("r059", T ``p /\ q <=> ~(~p \/ ~q)``)
  val _ = s ("r060", T ``~p /\ q <=> ~(p \/ ~q)``)
  val _ = s ("r061", T ``p /\ ~q <=> ~(~p \/ q)``)
  val _ = s ("r062", T ``~p /\ ~q <=> ~(p \/ q)``)

  val _ = s ("r067", U [combinTheory.APPLY_UPDATE_ID] ``(x =+ f x) f = f``)

  val _ = s ("r068", S ``ALL_DISTINCT [x; x] <=> F``)

  val _ = s ("r219", R ``0 + (x :real) = x``)
  val _ = s ("r220", R ``(x :real) + 0 = x``)
  val _ = s ("r221", R ``(x :real) + y = y + x``)
  val _ = s ("r222", R ``(x :real) + x = 2 * x``)
  val _ = s ("r223", R ``(x :real) + y + z = x + (y + z)``)
  val _ = s ("r224", R ``(x :real) + y + z = x + (z + y)``)
  val _ = s ("r225", R ``(x :real) + (y + z) = y + (z + x)``)
  val _ = s ("r226", R ``(x :real) + (y + z) = y + (x + z)``)

  val _ = s ("r227", R ``0 - (x :real) = -x``)
  val _ = s ("r228", R ``0 - u * (x :real) = -u * x``)
  val _ = s ("r229", R ``(x :real) - 0 = x``)
  val _ = s ("r230", R ``(x :real) - y = x + -1 * y``)
  val _ = s ("r231", R ``(x :real) - y = -1 * y + x``)
  val _ = s ("r232", R ``(x :real) - u * y = x + -u * y``)
  val _ = s ("r233", R ``(x :real) - u * y = -u * y + x``)
  val _ = s ("r234", R ``(x :real) + y - z = x + (y + -1 * z)``)
  val _ = s ("r235", R ``(x :real) + y - z = x + (-1 * z + y)``)
  val _ = s ("r236", R ``(x :real) + y - u * z = -u * z + (x + y)``)
  val _ = s ("r237", R ``(x :real) + y - u * z = x + (-u * z + y)``)
  val _ = s ("r238", R ``(x :real) + y - u * z = x + (y + -u * z)``)

  val _ = s ("r239", R ``0 * (x :real) = 0``)
  val _ = s ("r240", R ``1 * (x :real) = x``)

  val _ = s ("r241", W ``0w + x = x``)
  val _ = s ("r242", W ``(x :'a word) + y = y + x``)
  val _ = s ("r243", W ``1w + (1w + x) = 2w + x``)
  val _ = s ("r244", Drule.EQT_ELIM
    (wordsLib.WORD_ARITH_CONV ``((x :'a word) + z = y + x) <=> (y = z)``))

  (* E1(c)/D1: ten public-family repeats took 1.539s through these
     width-specific rewrite caches versus 6.197s through general BBLAST
     (75.2% win).  rewrite(9)(proforma) require_fastpath-gates the family. *)
  val _ = s ("r245", Drule.UNDISCH_ALL (bossLib.PROVE
    [wordsTheory.word_concat_0] ``FINITE univ(:'a) ==> x < dimword(:'b) ==>
      ((0w :'a word) @@ (n2w x :'b word) = (n2w x :'c word))``))
  val _ = s ("r246", Drule.UNDISCH (simpLib.SIMP_PROVE bossLib.std_ss
    [wordsTheory.w2w_n2w, Thm.SYM (Drule.SPEC_ALL wordsTheory.MOD_DIMINDEX)]
    ``x < dimword(:'a) ==> (w2w (n2w x :'a word) = (n2w x :'b word))``))
  val _ = s ("r247", Drule.UNDISCH_ALL (bossLib.PROVE
    [wordsTheory.word_concat_0_eq] ``FINITE univ(:'a) ==>
      dimindex(:'b) <= dimindex(:'c) ==> y < dimword(:'b) ==>
      (((0w :'a word) @@ (x :'b word) = (n2w y :'c word)) <=> (x = n2w y))``))
  val _ = s ("r248", Drule.UNDISCH_ALL (bossLib.PROVE
      [wordsTheory.word_concat_0_eq] ``FINITE univ(:'a) ==>
      dimindex(:'b) <= dimindex(:'c) ==> y < dimword(:'b) ==>
      (((0w :'a word) @@ (x :'b word) = (n2w y :'c word)) <=> (n2w y = x))``))
  val _ = s ("r249", Drule.UNDISCH_ALL (bossLib.PROVE
    [wordsTheory.word_concat_0_eq] ``FINITE univ(:'a) ==>
      dimindex(:'b) <= dimindex(:'c) ==> y < dimword(:'b) ==>
      (((n2w y :'c word) = (0w :'a word) @@ (x :'b word)) <=> (x = n2w y))``))
  val _ = s ("r250", Drule.UNDISCH_ALL (bossLib.PROVE
    [wordsTheory.word_concat_0_eq] ``FINITE univ(:'a) ==>
      dimindex(:'b) <= dimindex(:'c) ==> y < dimword(:'b) ==>
      (((n2w y :'c word) = (0w :'a word) @@ (x :'b word)) <=> (n2w y = x))``))

  val _ = s ("r251", W ``x && y = y && x``)
  val _ = s ("r252", W ``x && y && z = y && x && z``)
  val _ = s ("r253", W ``x && y && z = (x && y) && z``)
  val _ = s ("r254", W ``(1w = (x :word1) && y) <=> (1w = x) /\ (1w = y)``)
  val _ = s ("r255", W ``(1w = (x :word1) && y) <=> (1w = y) /\ (1w = x)``)
  val _ = s ("r256", W ``(7 >< 0) (x :word8) = x``)
  val _ = s ("r257", W ``x <+ y <=> ~(y <=+ x)``)
  val _ = s ("r258", W ``(x :'a word) * y = y * x``)
  val _ = s ("r259", W ``(0 >< 0) (x :word1) = x``)
  val _ = s ("r260", W ``(x && y) && z = x && y && z``)
  val _ = s ("r261", W ``0w || x = x``)

  (* used for Z3's proof rule th_lemma *)

  val _ = s ("t001", U [boolTheory.EQ_SYM_EQ, combinTheory.UPDATE_def]
    ``(x = y) \/ (f x = (y =+ z) f x)``)
  val _ = s ("t002", U [boolTheory.EQ_SYM_EQ, combinTheory.UPDATE_def]
    ``(x = y) \/ (f y = (x =+ z) f y)``)
  val _ = s ("t003", U [boolTheory.EQ_SYM_EQ, combinTheory.UPDATE_def]
    ``(x = y) \/ ((y =+ z) f x = f x)``)
  val _ = s ("t004", U [boolTheory.EQ_SYM_EQ, combinTheory.UPDATE_def]
    ``(x = y) \/ ((x =+ z) f y = f y)``)
  val _ = s ("t005", Tactical.prove
    (``(f = g) \/ (f (array_ext f g) <> g (array_ext f g))``,
      Tactic.DISJ_CASES_TAC
        (Thm.SPEC ``?x. f x <> g x`` boolTheory.EXCLUDED_MIDDLE)
      >> Rewrite.REWRITE_TAC [array_ext_def]
      >> bossLib.METIS_TAC []))

  val _ = s ("t006", A ``((x :int) <> y) \/ (x <= y)``)
  val _ = s ("t007", A ``((x :int) <> y) \/ (x >= y)``)
  val _ = s ("t008", A ``((x :int) <> y) \/ (x + -1 * y >= 0)``)
  val _ = s ("t009", A ``((x :int) <> y) \/ (x + -1 * y <= 0)``)
  val _ = s ("t010", A ``((x :int) = y) \/ ~(x <= y) \/ ~(x >= y)``)
  val _ = s ("t011", A ``~((x :int) <= 0) \/ x <= 1``)
  val _ = s ("t012", A ``~((x :int) <= -1) \/ x <= 0``)
  val _ = s ("t013", A ``~((x :int) >= 0) \/ x >= -1``)
  val _ = s ("t014", A ``~((x :int) >= 0) \/ ~(x <= -1)``)
  val _ = s ("t015", A ``(x :int) >= y \/ x <= y``)

  val _ = s ("t016", R ``(x :real) <> y \/ x + -1 * y >= 0``)

  val _ = s ("t017", Tactical.prove (``(x :'a word) <> ~x``,
    let
      val RW = bossLib.RW_TAC (bossLib.++ (bossLib.bool_ss, fcpLib.FCP_ss))
    in
      RW []
      >> Tactic.EXISTS_TAC ``0 :num``
      >> RW [wordsTheory.DIMINDEX_GT_0, wordsTheory.word_1comp_def]
      >> tautLib.TAUT_TAC
    end))
  val _ = s ("t018", W ``(x = y) ==> x ' i ==> y ' i``)
  val _ = s ("t019", S ``(1w = ~(x :word1)) \/ x ' 0``)
  val _ = s ("t020", S ``(x :word1) ' 0 ==> (0w = ~x)``)
  val _ = s ("t021", S ``(x :word1) ' 0 ==> (1w = x)``)
  val _ = s ("t022", S ``~((x :word1) ' 0) ==> (0w = x)``)
  val _ = s ("t023", S ``~((x :word1) ' 0) ==> (1w = ~x)``)
  val _ = s ("t024", S ``(0w = ~(x :word1)) \/ ~(x ' 0)``)
  val _ = s ("t025", U []
    ``(1w = ~(x :word1) || ~y) \/ ~(~(x ' 0) \/ ~(y ' 0))``)
  (* E1(c)/D1: ten public-family repeats took 0.139s through these
     width-specific th-lemma caches versus 1.500s through the general
     arith-to-BV route (90.7% win).  The th-lemma proforma rung is gated. *)
  val _ = s ("t026", U []
    ``(0w = (x :word8)) \/ x ' 0 \/ x ' 1 \/ x ' 2 \/ x ' 3 \/ x ' 4 \/ x ' 5 \/ x ' 6 \/ x ' 7``)
  val _ = s ("t027", S
    ``(((x :word1) = 1w) <=> p) <=> (x = if p then 1w else 0w)``)
  val _ = s ("t028", S
    ``((1w = (x :word1)) <=> p) <=> (x = if p then 1w else 0w)``)
  val _ = s ("t029", S
    ``(p <=> ((x :word1) = 1w)) <=> (x = if p then 1w else 0w)``)
  val _ = s ("t030", S
    ``(p <=> (1w = (x :word1))) <=> (x = if p then 1w else 0w)``)
  val _ = s ("t031", B
    ``(0w:word32 = 0xFFFFFFFFw * sw2sw (x :word8)) ==> ~(x ' 0)``)
  val _ = s ("t032", B
    ``(0w:word32 = 0xFFFFFFFFw * sw2sw (x :word8)) ==> ~(x ' 1 <=> ~(x ' 0))``)
  val _ = s ("t033", B ``(0w:word32 = 0xFFFFFFFFw * sw2sw (x :word8)) ==>
      ~(x ' 2 <=> ~(x ' 0) /\ ~(x ' 1))``)
  val _ = s ("t034", M [
      simpLib.SIMP_PROVE bossLib.bool_ss [
        wordsTheory.WORD_ADD_BIT0, wordsLib.WORD_DECIDE ``1w :'a word ' 0``
      ] ``x ' 0 ==> ~(1w + (x :'a word)) ' 0``
    ] ``(1w + (x :'a word) = y) ==> x ' 0 ==> ~(y ' 0)``)
  val _ = s ("t035", S ``(1w = x :word1) \/ (0 >< 0) x <> (1w :word1)``)

  (* used to prove hypotheses of other proforma theorems (recursively) *)

  val _ = s ("p001", wordsTheory.ZERO_LT_dimword)  (* ``0 < dimword(:'a)`` *)
  val _ = s ("p002", wordsTheory.ONE_LT_dimword)  (* ``1 < dimword(:'a)`` *)

  val _ = s ("TO_WORD_EXTRACT", boolLib.TAC_PROOF (([],
        “(!w : 'a word.
            dimindex(:'b) < dimindex(:'a) ==>
            (w2w w : 'b word = (dimindex(:'b) - 1 >< 0) w)) /\
         (!w : 'a word.
            dimindex(:'b) < dimindex(:'a) ==>
            (sw2sw w : 'b word = (dimindex(:'b) - 1 >< 0) w))”),
        BasicProvers.SRW_TAC [wordsLib.WORD_BIT_EQ_ss] []))
