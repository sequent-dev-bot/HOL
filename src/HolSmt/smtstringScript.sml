(* Copyright (c) 2026 The HOL4 contributors. *)

(* SMT-LIB Unicode strings wrap lists of Unicode code points so the SMT sort
   is carried by the HOL type rather than reconstructed from wfstr guards.
   The carrier is a type definition rather than a free datatype precisely so
   that the code-point bound is an inhabitant property: every ':smtstr' is
   wellformed, so the HOL universe of the type is exactly the SMT-LIB String
   universe and binders need no relativization in either direction. *)
Theory smtstring
Ancestors[qualified]
  ASCIInumbers integer rich_list

Theorem SMTSTR_EXISTS[local]:
  ?l. (\l. EVERY (\c : num. c <= 196607) l) l
Proof
  Q.EXISTS_TAC `[]` >>
  simp []
QED

val smtstr_tyax = new_type_definition ("smtstr", SMTSTR_EXISTS)

val smtstr_bij = define_new_type_bijections {
  name = "smtstr_BIJ",
  ABS = "SmtStr",
  REP = "smtstr_rep",
  tyax = smtstr_tyax}

Theorem SmtStr_smtstr_rep[simp] = CONJUNCT1 smtstr_bij

Theorem smtstr_rep_SmtStr = BETA_RULE (CONJUNCT2 smtstr_bij)

(* Kept under its historical name: every rewrite that used to unfold the
   datatype's representation function now discharges the code-point bound
   as a side condition instead. *)
Theorem smtstr_rep_def[simp]:
  !l. EVERY (\c. c <= 196607) l ==> (smtstr_rep (SmtStr l) = l)
Proof
  simp [smtstr_rep_SmtStr]
QED

Theorem smtstr_rep_bound[simp]:
  EVERY (\c. c <= 196607) (smtstr_rep s)
Proof
  simp [smtstr_rep_SmtStr]
QED

(* Every substring of a representation is again a legal representation; the
   substring operators below rely on this to re-abstract their results. *)
Theorem smtstr_rep_bound_substr[simp]:
  EVERY (\c. c <= 196607) (TAKE n (DROP m (smtstr_rep s)))
Proof
  irule rich_listTheory.EVERY_TAKE >>
  irule rich_listTheory.EVERY_DROP >>
  simp []
QED

(* Out-of-range code points have no ':smtstr' image, so ground evaluation
   must report the violation rather than silently pick a representative. *)
Theorem smtstr_rep_compute[compute]:
  !l. smtstr_rep (SmtStr l) =
      if EVERY (\c. c <= 196607) l then l
      else FAIL smtstr_rep ^(mk_var ("code point out of range", bool))
        (SmtStr l)
Proof
  rw [combinTheory.FAIL_THM]
QED

Theorem smtstr_rep_11[simp]:
  (smtstr_rep s = smtstr_rep t) <=> (s = t)
Proof
  metis_tac [SmtStr_smtstr_rep]
QED

Theorem smtstr_eq_SmtStr:
  EVERY (\c. c <= 196607) l ==>
  ((s = SmtStr l <=> smtstr_rep s = l) /\
   (SmtStr l = s <=> l = smtstr_rep s))
Proof
  strip_tac >>
  metis_tac [SmtStr_smtstr_rep, smtstr_rep_def]
QED

Theorem smtstr_rep_eq_nil:
  (smtstr_rep s = []) <=> (s = SmtStr [])
Proof
  eq_tac
  >- metis_tac [SmtStr_smtstr_rep]
  >> strip_tac >>
  simp []
QED

(* ':smtstr' is a type definition rather than a datatype, so the compute set
   gets no constructor injectivity theorem.  Routing ground equality through
   the representation restores it: 'smtstr_rep_compute' reduces each side to
   its code-point list, or reports the out-of-range violation. *)
Theorem SmtStr_eq_compute[compute]:
  (SmtStr u = SmtStr v) <=>
    (smtstr_rep (SmtStr u) = smtstr_rep (SmtStr v))
Proof
  simp []
QED

Theorem SmtStr_11:
  EVERY (\c. c <= 196607) u /\ EVERY (\c. c <= 196607) v ==>
  ((SmtStr u = SmtStr v) <=> (u = v))
Proof
  strip_tac >>
  metis_tac [smtstr_rep_def]
QED

Theorem smtstr_eq_singleton:
  c <= 196607 ==> ((s = SmtStr [c]) <=> (smtstr_rep s = [c]))
Proof
  strip_tac >>
  `EVERY (\c. c <= 196607) [c]` by simp [] >>
  metis_tac [smtstr_eq_SmtStr]
QED

Theorem ranged_smtstr_nchotomy:
  !s. ?l. (s = SmtStr l) /\ EVERY (\c. c <= 196607) l
Proof
  gen_tac >>
  qexists_tac `smtstr_rep s` >>
  simp []
QED

Definition smtstr_size_def:
  smtstr_size (s : smtstr) : num = 0
End

(* Registering the ranged nchotomy keeps 'Cases_on' usable on ':smtstr' and
   makes it deliver the code-point bound alongside the representation. *)
val _ = TypeBase.export [
  TypeBasePure.mk_nondatatype_info (
    ``:smtstr``,
    {nchotomy = SOME ranged_smtstr_nchotomy,
     induction = NONE,
     size = SOME (``smtstr_size``, smtstr_size_def),
     encode = NONE})]

Definition wfstr_def:
  wfstr s <=> EVERY (\c. c <= 196607) (smtstr_rep s)
End

(* The bound is now carried by the type, so wellformedness is a theorem.
   'wfstr' survives as a constant because the SMT-LIB regex semantics below
   are stated in terms of it. *)
Theorem wfstr[simp]:
  wfstr s
Proof
  simp [wfstr_def]
QED

Definition smtstr_concat_def:
  smtstr_concat s t = SmtStr (smtstr_rep s ++ smtstr_rep t)
End

Definition smtstr_len_def:
  smtstr_len s : int = &(LENGTH (smtstr_rep s))
End

Definition smtstr_substr_def:
  smtstr_substr s (i : int) (n : int) =
    if i < 0 \/ n <= 0 \/ LENGTH (smtstr_rep s) <= Num i then
      SmtStr []
    else
      SmtStr (TAKE (Num n) (DROP (Num i) (smtstr_rep s)))
End

Definition smtstr_at_def:
  smtstr_at s (i : int) = smtstr_substr s i 1
End

Theorem smtstr_rep_substr:
  smtstr_rep (smtstr_substr s i n) =
  if i < 0 \/ n <= 0 \/ LENGTH (smtstr_rep s) <= Num i then []
  else TAKE (Num n) (DROP (Num i) (smtstr_rep s))
Proof
  rw [smtstr_substr_def] >>
  simp [smtstr_rep_def, rich_listTheory.EVERY_TAKE,
        rich_listTheory.EVERY_DROP]
QED

Theorem smtstr_rep_substr_positive:
  0 <= i /\ 0 < n ==>
  smtstr_rep (smtstr_substr s i n) =
    TAKE (Num n) (DROP (Num i) (smtstr_rep s))
Proof
  strip_tac >>
  rw [smtstr_rep_substr] >>
  `~(i < 0) /\ ~(n <= 0)` by intLib.ARITH_TAC >>
  Cases_on `LENGTH (smtstr_rep s) <= Num i` >>
  simp [listTheory.DROP_EQ_NIL]
QED

Theorem smtstr_rep_substr_nonpositive:
  n <= 0 ==>
  smtstr_rep (smtstr_substr s i n) = []
Proof
  simp [smtstr_rep_substr]
QED

Theorem TAKE_DROP_TAKE_RIGHT_BOUND[local]:
  m1 - n2 <= m2 ==>
  TAKE m2 (DROP n2 (TAKE m1 (DROP n1 xs))) =
  TAKE (m1 - n2) (DROP (n1 + n2) xs)
Proof
  strip_tac >>
  simp [listTheory.DROP_TAKE, rich_listTheory.DROP_DROP_T,
        listTheory.TAKE_TAKE_MIN, arithmeticTheory.MIN_DEF]
QED

Theorem TAKE_DROP_TAKE_LEFT_BOUND[local]:
  m2 <= m1 - n2 ==>
  TAKE m2 (DROP n2 (TAKE m1 (DROP n1 xs))) =
  TAKE m2 (DROP (n1 + n2) xs)
Proof
  strip_tac >>
  Cases_on `m2 < m1 - n2`
  >- simp [listTheory.DROP_TAKE, rich_listTheory.DROP_DROP_T,
           listTheory.TAKE_TAKE_MIN, arithmeticTheory.MIN_DEF] >>
  `m2 = m1 - n2` by decide_tac >>
  simp [listTheory.DROP_TAKE, rich_listTheory.DROP_DROP_T,
        listTheory.TAKE_TAKE_MIN]
QED

Theorem TAKE_DROP_TAKE_ACTUAL_BOUND[local]:
  LENGTH (TAKE m1 (DROP n1 xs)) <= n2 + m2 ==>
  TAKE m2 (DROP n2 (TAKE m1 (DROP n1 xs))) =
  TAKE (m1 - n2) (DROP (n1 + n2) xs)
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

Theorem smtstr_substr_combine_right:
  0 <= n1 /\ 0 <= n2 /\ 0 <= m2 - (m1 - n2) ==>
  smtstr_substr (smtstr_substr s n1 m1) n2 m2 =
  smtstr_substr s (n1 + n2) (m1 - n2)
Proof
  strip_tac >>
  irule (iffLR smtstr_rep_11) >>
  Cases_on `m1 - n2 <= 0`
  >- (`m1 <= n2` by intLib.ARITH_TAC >>
      `smtstr_rep
         (smtstr_substr s (n1 + n2) (m1 - n2)) = []` by
        simp [smtstr_rep_substr_nonpositive] >>
      Cases_on `m2 <= 0`
      >- (`smtstr_rep
             (smtstr_substr
                (smtstr_substr s n1 m1) n2 m2) = []` by
            metis_tac [smtstr_rep_substr_nonpositive] >>
          metis_tac []) >>
      `0 < m2` by intLib.ARITH_TAC >>
      Cases_on `m1 <= 0`
      >- (`smtstr_rep (smtstr_substr s n1 m1) = []` by
            metis_tac [smtstr_rep_substr_nonpositive] >>
          `smtstr_rep
             (smtstr_substr
                (smtstr_substr s n1 m1) n2 m2) =
           TAKE (Num m2)
             (DROP (Num n2)
               (smtstr_rep (smtstr_substr s n1 m1)))` by
            metis_tac [smtstr_rep_substr_positive] >>
          `TAKE (Num m2)
             (DROP (Num n2)
               (smtstr_rep (smtstr_substr s n1 m1))) = []` by
            simp [] >>
          metis_tac []) >>
      `0 < m1` by intLib.ARITH_TAC >>
      `Num m1 <= Num n2` by intLib.ARITH_TAC >>
      `smtstr_rep (smtstr_substr s n1 m1) =
         TAKE (Num m1) (DROP (Num n1) (smtstr_rep s))` by
        metis_tac [smtstr_rep_substr_positive] >>
      `smtstr_rep
         (smtstr_substr (smtstr_substr s n1 m1) n2 m2) =
       TAKE (Num m2)
         (DROP (Num n2)
           (smtstr_rep (smtstr_substr s n1 m1)))` by
        metis_tac [smtstr_rep_substr_positive] >>
      `TAKE (Num m2)
         (DROP (Num n2)
           (TAKE (Num m1) (DROP (Num n1) (smtstr_rep s)))) =
       TAKE (Num m1 - Num n2)
         (DROP (Num n1 + Num n2) (smtstr_rep s))` by
        simp [listTheory.DROP_TAKE, rich_listTheory.DROP_DROP_T,
              listTheory.TAKE_TAKE_MIN,
              arithmeticTheory.MIN_DEF] >>
      `TAKE (Num m1 - Num n2)
         (DROP (Num n1 + Num n2) (smtstr_rep s)) = []` by
        simp [] >>
      `TAKE (Num m2)
         (DROP (Num n2)
           (TAKE (Num m1) (DROP (Num n1) (smtstr_rep s)))) = []` by
        metis_tac [] >>
      metis_tac []) >>
  `0 < m1 - n2` by intLib.ARITH_TAC >>
  `0 < m1` by intLib.ARITH_TAC >>
  `0 < m2` by intLib.ARITH_TAC >>
  `0 <= n1 + n2` by intLib.ARITH_TAC >>
  `Num (n1 + n2) = Num n1 + Num n2` by intLib.ARITH_TAC >>
  `Num (m1 - n2) = Num m1 - Num n2` by intLib.ARITH_TAC >>
  `Num m1 - Num n2 <= Num m2` by intLib.ARITH_TAC >>
  `smtstr_rep (smtstr_substr s n1 m1) =
     TAKE (Num m1) (DROP (Num n1) (smtstr_rep s))` by
    metis_tac [smtstr_rep_substr_positive] >>
  `smtstr_rep
     (smtstr_substr (smtstr_substr s n1 m1) n2 m2) =
   TAKE (Num m2)
     (DROP (Num n2) (smtstr_rep (smtstr_substr s n1 m1)))` by
    metis_tac [smtstr_rep_substr_positive] >>
  `smtstr_rep (smtstr_substr s (n1 + n2) (m1 - n2)) =
     TAKE (Num (m1 - n2))
       (DROP (Num (n1 + n2)) (smtstr_rep s))` by
    metis_tac [smtstr_rep_substr_positive] >>
  `TAKE (Num m2)
     (DROP (Num n2)
       (TAKE (Num m1) (DROP (Num n1) (smtstr_rep s)))) =
   TAKE (Num (m1 - n2))
     (DROP (Num (n1 + n2)) (smtstr_rep s))` by
    metis_tac [TAKE_DROP_TAKE_RIGHT_BOUND] >>
  metis_tac []
QED

Theorem smtstr_substr_combine_left:
  0 <= n1 /\ 0 <= n2 /\ 0 <= (m1 - n2) - m2 ==>
  smtstr_substr (smtstr_substr s n1 m1) n2 m2 =
  smtstr_substr s (n1 + n2) m2
Proof
  strip_tac >>
  irule (iffLR smtstr_rep_11) >>
  Cases_on `m2 <= 0`
  >- (`smtstr_rep
         (smtstr_substr (smtstr_substr s n1 m1) n2 m2) = []` by
        metis_tac [smtstr_rep_substr_nonpositive] >>
      `smtstr_rep (smtstr_substr s (n1 + n2) m2) = []` by
        metis_tac [smtstr_rep_substr_nonpositive] >>
      metis_tac []) >>
  `0 < m2` by intLib.ARITH_TAC >>
  `0 < m1 - n2` by intLib.ARITH_TAC >>
  `0 < m1` by intLib.ARITH_TAC >>
  `0 <= n1 + n2` by intLib.ARITH_TAC >>
  `Num (n1 + n2) = Num n1 + Num n2` by intLib.ARITH_TAC >>
  `Num (m1 - n2) = Num m1 - Num n2` by intLib.ARITH_TAC >>
  `Num m2 <= Num m1 - Num n2` by intLib.ARITH_TAC >>
  `smtstr_rep (smtstr_substr s n1 m1) =
     TAKE (Num m1) (DROP (Num n1) (smtstr_rep s))` by
    metis_tac [smtstr_rep_substr_positive] >>
  `smtstr_rep
     (smtstr_substr (smtstr_substr s n1 m1) n2 m2) =
   TAKE (Num m2)
     (DROP (Num n2) (smtstr_rep (smtstr_substr s n1 m1)))` by
    metis_tac [smtstr_rep_substr_positive] >>
  `smtstr_rep (smtstr_substr s (n1 + n2) m2) =
     TAKE (Num m2) (DROP (Num (n1 + n2)) (smtstr_rep s))` by
    metis_tac [smtstr_rep_substr_positive] >>
  metis_tac [TAKE_DROP_TAKE_LEFT_BOUND]
QED

Theorem smtstr_substr_full:
  smtstr_substr s 0 (smtstr_len s) = s
Proof
  qspec_then `s` strip_assume_tac ranged_smtstr_nchotomy >>
  Cases_on `l` >>
  simp [smtstr_substr_def, smtstr_len_def]
QED

Theorem smtstr_substr_empty_start:
  smtstr_len s <= i ==> smtstr_substr s i n = SmtStr []
Proof
  simp [smtstr_substr_def, smtstr_len_def] >>
  strip_tac >>
  `LENGTH (smtstr_rep s) <= Num i` by intLib.ARITH_TAC >>
  simp []
QED

Theorem smtstr_substr_empty_start_neg:
  i < 0 ==> smtstr_substr s i n = SmtStr []
Proof
  simp [smtstr_substr_def]
QED

Definition smtstr_update_def:
  smtstr_update s (i : int) t =
    if i < 0 \/ LENGTH (smtstr_rep s) <= Num i then s
    else SmtStr (TAKE (Num i) (smtstr_rep s) ++
      TAKE (LENGTH (smtstr_rep s) - Num i) (smtstr_rep t) ++
      DROP (Num i + LENGTH (smtstr_rep t)) (smtstr_rep s))
End

Definition smtstr_rev_def:
  smtstr_rev s = SmtStr (REVERSE (smtstr_rep s))
End

Theorem smtstr_rev_rev:
  smtstr_rev (smtstr_rev s) = s
Proof
  qspec_then `s` strip_assume_tac ranged_smtstr_nchotomy >>
  simp [smtstr_rev_def]
QED

Theorem smtstr_len_rev:
  smtstr_len (smtstr_rev s) = smtstr_len s
Proof
  simp [smtstr_rev_def, smtstr_len_def, smtstr_rep_def]
QED

Theorem smtstr_rev_concat:
  smtstr_rev (smtstr_concat s t) =
  smtstr_concat (smtstr_rev t) (smtstr_rev s)
Proof
  qspec_then `s` strip_assume_tac ranged_smtstr_nchotomy >>
  qspec_then `t` strip_assume_tac ranged_smtstr_nchotomy >>
  simp [smtstr_rev_def, smtstr_concat_def,
        listTheory.REVERSE_APPEND]
QED

Definition smtstr_prefixof_def:
  smtstr_prefixof s t <=>
    IS_PREFIX (smtstr_rep t) (smtstr_rep s)
End

Definition smtstr_suffixof_def:
  smtstr_suffixof s t <=>
    IS_SUFFIX (smtstr_rep t) (smtstr_rep s)
End

Definition smtstr_contains_def:
  smtstr_contains s t <=>
    IS_SUBLIST (smtstr_rep s) (smtstr_rep t)
End

Definition smtstr_indexof_aux_def:
  (smtstr_indexof_aux t n [] =
     if t = [] then SOME n else NONE) /\
  (smtstr_indexof_aux t n (h::s) =
     if IS_PREFIX (h::s) t then SOME n
     else smtstr_indexof_aux t (SUC n) s)
End

Definition smtstr_indexof_def:
  smtstr_indexof s t (i : int) =
    if i < 0 \/ LENGTH (smtstr_rep s) < Num i then -1
    else
      case smtstr_indexof_aux (smtstr_rep t) (Num i)
        (DROP (Num i) (smtstr_rep s)) of
        NONE => -1
      | SOME n => &n
End

Definition smtstr_lt_def:
  smtstr_lt s t <=> LLEX $< (smtstr_rep s) (smtstr_rep t)
End

Definition smtstr_le_def:
  smtstr_le s t <=> smtstr_lt s t \/ s = t
End

Theorem smtstr_le_empty_left:
  smtstr_le (SmtStr []) s
Proof
  Cases_on `smtstr_rep s = []`
  >- fs [smtstr_rep_eq_nil, smtstr_le_def] >>
  simp [smtstr_le_def, smtstr_lt_def, listTheory.LLEX_def]
QED

Theorem smtstr_le_empty_right:
  smtstr_le s (SmtStr []) <=> s = SmtStr []
Proof
  simp [smtstr_le_def, smtstr_lt_def, smtstr_rep_eq_nil]
QED

Definition smtstr_char_def:
  smtstr_char (c : num) = SmtStr [c]
End

Definition str_inj_def:
  str_inj (s : string) = SmtStr (MAP ORD (EXPLODE s))
End

(* SMT-LIB regular languages over Unicode code points. *)

Datatype:
  reglan
    = reglan_none
    | reglan_all
    | reglan_allchar
    | reglan_to_re smtstr
    | reglan_range smtstr smtstr
    | reglan_concat reglan reglan
    | reglan_union reglan reglan
    | reglan_inter reglan reglan
    | reglan_diff reglan reglan
    | reglan_comp reglan
    | reglan_star reglan
    | reglan_plus reglan
    | reglan_opt reglan
    | reglan_power reglan num
    | reglan_loop reglan num num
End

Definition reglan_dot_def:
  reglan_dot (p : num list -> bool) q s <=>
    ?u v. p u /\ q v /\ s = u ++ v
End

Definition reglan_kstar_def:
  reglan_kstar (p : num list -> bool) s <=>
    ?ss. EVERY (\u. p u /\ u <> []) ss /\ s = FLAT ss
End

Definition reglan_repeat_def:
  reglan_repeat (p : num list -> bool) n s <=>
    ?ss. LENGTH ss = n /\ EVERY p ss /\ s = FLAT ss
End

Definition reglan_loop_lang_def:
  (reglan_loop_lang (p : num list -> bool) i 0 s <=>
     if i = 0 then reglan_repeat p 0 s else F) /\
  (reglan_loop_lang p i (SUC n) s <=>
     (i <= SUC n /\ reglan_repeat p (SUC n) s) \/
     reglan_loop_lang p i n s)
End

val reglan_loop_lang_compute_thm =
  DB.fetch "smtstring" "reglan_loop_lang_compute";

(* The word-level semantics.  The auxiliary language operators decompose a
   word into arbitrary 'num list' pieces, so the recursive clauses cannot be
   phrased as 'smt_in_re (SmtStr u) r': 'SmtStr u' is unconstrained when 'u'
   leaves the code-point range, whereas the pieces a decomposition produces
   are always sublists of a wellformed word.  're_lang' carries the semantics
   over raw words, and 'smt_in_re' reads it off the representation. *)

Definition re_lang_def:
  (re_lang reglan_none (u : num list) <=> F) /\
  (re_lang reglan_all u <=> EVERY (\c. c <= 196607) u) /\
  (re_lang reglan_allchar u <=> ?c. c <= 196607 /\ u = [c]) /\
  (re_lang (reglan_to_re t) u <=> u = smtstr_rep t) /\
  (re_lang (reglan_range lo hi) u <=>
     ?a b c.
       smtstr_rep lo = [a] /\ smtstr_rep hi = [b] /\ a <= c /\ c <= b /\
       c <= 196607 /\ u = [c]) /\
  (re_lang (reglan_concat r1 r2) u <=>
     reglan_dot (\x. re_lang r1 x) (\y. re_lang r2 y) u) /\
  (re_lang (reglan_union r1 r2) u <=>
     re_lang r1 u \/ re_lang r2 u) /\
  (re_lang (reglan_inter r1 r2) u <=>
     re_lang r1 u /\ re_lang r2 u) /\
  (re_lang (reglan_diff r1 r2) u <=>
     re_lang r1 u /\ ~re_lang r2 u) /\
  (re_lang (reglan_comp r) u <=>
     EVERY (\c. c <= 196607) u /\ ~re_lang r u) /\
  (re_lang (reglan_star r) u <=>
     reglan_kstar (\x. re_lang r x) u) /\
  (re_lang (reglan_plus r) u <=>
     reglan_dot
       (\x. re_lang r x)
       (reglan_kstar (\x. re_lang r x))
       u) /\
  (re_lang (reglan_opt r) u <=> u = [] \/ re_lang r u) /\
  (re_lang (reglan_power r n) u <=>
     reglan_repeat (\x. re_lang r x) n u) /\
  (re_lang (reglan_loop r i n) u <=>
     reglan_loop_lang (\x. re_lang r x) i n u)
End

(* SMT-LIB regular-expression equality is equality of languages.  Keep that
   proof-certificate relation separate from HOL's constructor equality: the
   source translator must never turn a user theorem about [reglan] equality
   into this weaker relation. *)
Definition reglan_equiv_def:
  reglan_equiv r s <=> !u. re_lang r u <=> re_lang s u
End

Theorem reglan_equiv_refl:
  reglan_equiv r r
Proof
  simp [reglan_equiv_def]
QED

Theorem reglan_equiv_sym:
  reglan_equiv r s ==> reglan_equiv s r
Proof
  simp [reglan_equiv_def] >> metis_tac []
QED

Theorem reglan_equiv_trans:
  reglan_equiv r s /\ reglan_equiv s t ==> reglan_equiv r t
Proof
  simp [reglan_equiv_def] >> metis_tac []
QED

Theorem reglan_equiv_equiv_eq:
  reglan_equiv r r' /\ reglan_equiv s s' ==>
  (reglan_equiv r s = reglan_equiv r' s')
Proof
  simp [reglan_equiv_def] >> metis_tac []
QED

Triviality reglan_dot_cong:
  (!u. p u <=> p' u) /\ (!u. q u <=> q' u) ==>
  (reglan_dot p q u <=> reglan_dot p' q' u)
Proof
  rw [reglan_dot_def] >> metis_tac []
QED

Triviality reglan_kstar_cong:
  (!u. p u <=> q u) ==>
  (reglan_kstar p u <=> reglan_kstar q u)
Proof
  rw [reglan_kstar_def] >>
  `!ss. EVERY (\x. p x /\ x <> []) ss <=>
        EVERY (\x. q x /\ x <> []) ss` by
    (Induct >> simp []) >>
  metis_tac []
QED

Triviality reglan_repeat_cong:
  (!u. p u <=> q u) ==>
  (reglan_repeat p n u <=> reglan_repeat q n u)
Proof
  rw [reglan_repeat_def] >>
  `!ss. EVERY p ss <=> EVERY q ss` by (Induct >> simp []) >>
  metis_tac []
QED

Triviality reglan_loop_lang_cong:
  (!u. p u <=> q u) ==>
  (reglan_loop_lang p i n u <=> reglan_loop_lang q i n u)
Proof
  strip_tac >> Induct_on `n` >>
  simp [reglan_loop_lang_def] >> metis_tac [reglan_repeat_cong]
QED

Theorem reglan_concat_equiv:
  reglan_equiv r r' /\ reglan_equiv s s' ==>
  reglan_equiv (reglan_concat r s) (reglan_concat r' s')
Proof
  simp [reglan_equiv_def, re_lang_def] >>
  metis_tac [reglan_dot_cong]
QED

Theorem reglan_union_equiv:
  reglan_equiv r r' /\ reglan_equiv s s' ==>
  reglan_equiv (reglan_union r s) (reglan_union r' s')
Proof
  simp [reglan_equiv_def, re_lang_def] >> metis_tac []
QED

Theorem reglan_inter_equiv:
  reglan_equiv r r' /\ reglan_equiv s s' ==>
  reglan_equiv (reglan_inter r s) (reglan_inter r' s')
Proof
  simp [reglan_equiv_def, re_lang_def] >> metis_tac []
QED

Theorem reglan_diff_equiv:
  reglan_equiv r r' /\ reglan_equiv s s' ==>
  reglan_equiv (reglan_diff r s) (reglan_diff r' s')
Proof
  simp [reglan_equiv_def, re_lang_def] >> metis_tac []
QED

Theorem reglan_comp_equiv:
  reglan_equiv r s ==> reglan_equiv (reglan_comp r) (reglan_comp s)
Proof
  simp [reglan_equiv_def, re_lang_def] >> metis_tac []
QED

Theorem reglan_star_equiv:
  reglan_equiv r s ==> reglan_equiv (reglan_star r) (reglan_star s)
Proof
  simp [reglan_equiv_def, re_lang_def] >>
  metis_tac [reglan_kstar_cong]
QED

Theorem reglan_plus_equiv:
  reglan_equiv r s ==> reglan_equiv (reglan_plus r) (reglan_plus s)
Proof
  simp [reglan_equiv_def, re_lang_def] >>
  metis_tac [reglan_dot_cong, reglan_kstar_cong]
QED

Theorem reglan_opt_equiv:
  reglan_equiv r s ==> reglan_equiv (reglan_opt r) (reglan_opt s)
Proof
  simp [reglan_equiv_def, re_lang_def] >> metis_tac []
QED

Theorem reglan_power_equiv:
  reglan_equiv r s ==>
  reglan_equiv (reglan_power r n) (reglan_power s n)
Proof
  simp [reglan_equiv_def, re_lang_def] >>
  metis_tac [reglan_repeat_cong]
QED

Theorem reglan_loop_equiv:
  reglan_equiv r s ==>
  reglan_equiv (reglan_loop r i n) (reglan_loop s i n)
Proof
  simp [reglan_equiv_def, re_lang_def] >>
  metis_tac [reglan_loop_lang_cong]
QED

Definition smt_in_re_def:
  (smt_in_re s reglan_none <=> F) /\
  (smt_in_re s reglan_all <=> wfstr s) /\
  (smt_in_re s reglan_allchar <=>
     ?c. c <= 196607 /\ s = SmtStr [c]) /\
  (smt_in_re s (reglan_to_re t) <=> s = t) /\
  (smt_in_re s (reglan_range lo hi) <=>
     ?a b c.
       smtstr_rep lo = [a] /\ smtstr_rep hi = [b] /\ a <= c /\ c <= b /\
       c <= 196607 /\ s = SmtStr [c]) /\
  (smt_in_re s (reglan_concat r1 r2) <=>
     reglan_dot
       (\u. re_lang r1 u)
       (\v. re_lang r2 v)
       (smtstr_rep s)) /\
  (smt_in_re s (reglan_union r1 r2) <=>
     smt_in_re s r1 \/ smt_in_re s r2) /\
  (smt_in_re s (reglan_inter r1 r2) <=>
     smt_in_re s r1 /\ smt_in_re s r2) /\
  (smt_in_re s (reglan_diff r1 r2) <=>
     smt_in_re s r1 /\ ~smt_in_re s r2) /\
  (smt_in_re s (reglan_comp r) <=>
     wfstr s /\ ~smt_in_re s r) /\
  (smt_in_re s (reglan_star r) <=>
     reglan_kstar (\u. re_lang r u) (smtstr_rep s)) /\
  (smt_in_re s (reglan_plus r) <=>
     reglan_dot
       (\u. re_lang r u)
       (reglan_kstar (\u. re_lang r u))
       (smtstr_rep s)) /\
  (smt_in_re s (reglan_opt r) <=>
     s = SmtStr [] \/ smt_in_re s r) /\
  (smt_in_re s (reglan_power r n) <=>
     reglan_repeat (\u. re_lang r u) n (smtstr_rep s)) /\
  (smt_in_re s (reglan_loop r i n) <=>
     reglan_loop_lang (\u. re_lang r u) i n (smtstr_rep s))
End

Theorem smt_in_re_to_re:
  smt_in_re s (reglan_to_re t) <=> s = t
Proof
  simp [smt_in_re_def]
QED

Theorem smt_in_re_to_re_length:
  smt_in_re s (reglan_to_re t) ==> smtstr_len s = smtstr_len t
Proof
  simp [smt_in_re_to_re]
QED

Theorem smt_in_re_allchar_len:
  smt_in_re s reglan_allchar <=> smtstr_len s = 1
Proof
  rw [smt_in_re_def, smtstr_len_def,
      listTheory.LENGTH_EQ_1] >>
  eq_tac
  >- (strip_tac >> qexists_tac `c` >>
      metis_tac [smtstr_eq_singleton]) >>
  strip_tac >>
  `x <= 196607` by
    (qpat_x_assum `smtstr_rep s = [x]`
       (fn th => mp_tac (REWRITE_RULE [th]
         (Q.INST [`s` |-> `s`] smtstr_rep_bound))) >>
     simp []) >>
  qexists_tac `x` >> simp [] >>
  metis_tac [smtstr_eq_singleton]
QED

Theorem smt_in_re_range_length:
  smt_in_re s (reglan_range lo hi) ==> smtstr_len s = 1
Proof
  rw [smt_in_re_def, re_lang_def, smtstr_len_def] >>
  fs [smtstr_rep_def]
QED

Theorem smt_in_re_rep:
  smt_in_re s r <=> re_lang r (smtstr_rep s)
Proof
  qid_spec_tac `s` >>
  Induct_on `r` >>
  simp [smt_in_re_def, re_lang_def, wfstr_def] >>
  metis_tac [smtstr_eq_singleton, smtstr_rep_eq_nil]
QED

Theorem reglan_eq_imp_equiv:
  r = s ==> reglan_equiv r s
Proof
  simp [reglan_equiv_refl]
QED

Theorem smt_in_re_equiv:
  reglan_equiv r s ==>
  (smt_in_re t r <=> smt_in_re t s)
Proof
  simp [smt_in_re_rep, reglan_equiv_def]
QED

Theorem smt_in_re_equiv_eq:
  reglan_equiv r s ==>
  (smt_in_re t r = smt_in_re t s)
Proof
  simp [smt_in_re_equiv]
QED

Theorem reglan_cond_equiv:
  reglan_equiv r r' /\ reglan_equiv s s' ==>
  reglan_equiv (if b then r else s) (if b then r' else s')
Proof
  Cases_on `b` >> simp [reglan_equiv_refl]
QED

Definition re_nullable_def:
  (re_nullable reglan_none = F) /\
  (re_nullable reglan_all = T) /\
  (re_nullable reglan_allchar = F) /\
  (re_nullable (reglan_to_re s) <=> s = SmtStr []) /\
  (re_nullable (reglan_range lo hi) = F) /\
  (re_nullable (reglan_concat r1 r2) <=>
     re_nullable r1 /\ re_nullable r2) /\
  (re_nullable (reglan_union r1 r2) <=>
     re_nullable r1 \/ re_nullable r2) /\
  (re_nullable (reglan_inter r1 r2) <=>
     re_nullable r1 /\ re_nullable r2) /\
  (re_nullable (reglan_diff r1 r2) <=>
     re_nullable r1 /\ ~re_nullable r2) /\
  (re_nullable (reglan_comp r) <=> ~re_nullable r) /\
  (re_nullable (reglan_star r) = T) /\
  (re_nullable (reglan_plus r) <=> re_nullable r) /\
  (re_nullable (reglan_opt r) = T) /\
  (re_nullable (reglan_power r n) <=> n = 0 \/ re_nullable r) /\
  (re_nullable (reglan_loop r i n) <=>
     i <= n /\ (i = 0 \/ re_nullable r))
End

Definition reglan_power_deriv_def:
  (reglan_power_deriv dr nullable r 0 = reglan_none) /\
  (reglan_power_deriv dr nullable r (SUC n) =
     let head = reglan_concat dr (reglan_power r n)
     in
       if nullable then
         reglan_union head (reglan_power_deriv dr nullable r n)
       else head)
End

Definition reglan_loop_deriv_def:
  (reglan_loop_deriv dr nullable r i 0 = reglan_none) /\
  (reglan_loop_deriv dr nullable r i (SUC n) =
     if i <= SUC n then
       reglan_union
         (reglan_power_deriv dr nullable r (SUC n))
         (reglan_loop_deriv dr nullable r i n)
     else reglan_none)
End

Definition re_deriv_def:
  (re_deriv c reglan_none = reglan_none) /\
  (re_deriv c reglan_all =
     if c <= 196607 then reglan_all else reglan_none) /\
  (re_deriv c reglan_allchar =
     if c <= 196607 then reglan_to_re (SmtStr []) else reglan_none) /\
  (re_deriv c (reglan_to_re s) =
     case smtstr_rep s of
       [] => reglan_none
     | h::t =>
         if c = h then reglan_to_re (SmtStr t) else reglan_none) /\
  (re_deriv c (reglan_range lo hi) =
     case smtstr_rep lo of
       [a] =>
         (case smtstr_rep hi of
            [b] =>
              if a <= c /\ c <= b /\ c <= 196607 then
                reglan_to_re (SmtStr [])
              else reglan_none
          | _ => reglan_none)
     | _ => reglan_none) /\
  (re_deriv c (reglan_concat r1 r2) =
     let head = reglan_concat (re_deriv c r1) r2
     in
       if re_nullable r1 then
         reglan_union head (re_deriv c r2)
       else head) /\
  (re_deriv c (reglan_union r1 r2) =
     reglan_union (re_deriv c r1) (re_deriv c r2)) /\
  (re_deriv c (reglan_inter r1 r2) =
     reglan_inter (re_deriv c r1) (re_deriv c r2)) /\
  (re_deriv c (reglan_diff r1 r2) =
     reglan_diff (re_deriv c r1) (re_deriv c r2)) /\
  (re_deriv c (reglan_comp r) =
     if c <= 196607 then reglan_comp (re_deriv c r)
     else reglan_none) /\
  (re_deriv c (reglan_star r) =
     reglan_concat (re_deriv c r) (reglan_star r)) /\
  (re_deriv c (reglan_plus r) =
     reglan_concat (re_deriv c r) (reglan_star r)) /\
  (re_deriv c (reglan_opt r) = re_deriv c r) /\
  (re_deriv c (reglan_power r n) =
     reglan_power_deriv (re_deriv c r) (re_nullable r) r n) /\
  (re_deriv c (reglan_loop r i n) =
     reglan_loop_deriv (re_deriv c r) (re_nullable r) r i n)
End

(* Evaluation-ready characterizations for the persistent compute set.
   'smtstr_concat_def', 'smtstr_len_def' and 'smtstr_lt_def' are already
   persistent compute rules, and 'smtstr_rep_compute' evaluates the
   representation of a literal, so ground evaluation needs no
   constructor-recursive equations.  Such equations would in any case be
   unsound now: 'SmtStr (h::s)' constrains nothing unless 'h' is in range. *)

Theorem smtstr_rep_concat[simp]:
  smtstr_rep (smtstr_concat s t) = smtstr_rep s ++ smtstr_rep t
Proof
  simp [smtstr_concat_def, smtstr_rep_def]
QED

(* Injection from native HOL strings. *)

Theorem ORD_unicode_bound[simp]:
  ORD c <= 196607
Proof
  `ORD c < 256` by simp [stringTheory.ORD_BOUND] >>
  decide_tac
QED

Theorem EVERY_MAP_ORD_bound[simp]:
  EVERY (\c. c <= 196607) (MAP ORD l)
Proof
  simp [listTheory.EVERY_MAP]
QED

Theorem smtstr_rep_str_inj[simp]:
  smtstr_rep (str_inj s) = MAP ORD (EXPLODE s)
Proof
  simp [str_inj_def, smtstr_rep_def]
QED

Theorem str_inj_compute[compute]:
  (str_inj "" = SmtStr []) /\
  (str_inj (STRING c s) =
     SmtStr (ORD c::smtstr_rep (str_inj s)))
Proof
  simp [str_inj_def]
QED

Theorem MAP_ORD_11:
  MAP ORD s = MAP ORD t <=> s = t
Proof
  qid_spec_tac `t` >>
  Induct_on `s` >>
  Cases_on `t` >>
  simp [stringTheory.ORD_11]
QED

Theorem str_inj_11[simp]:
  str_inj s = str_inj t <=> s = t
Proof
  simp [str_inj_def, SmtStr_11, MAP_ORD_11]
QED

Theorem str_inj_STRCAT:
  str_inj (STRCAT s t) =
    smtstr_concat (str_inj s) (str_inj t)
Proof
  simp [str_inj_def, smtstr_concat_def, smtstr_rep_def,
        stringTheory.IMPLODE_EXPLODE_I]
QED

Theorem str_inj_STRLEN:
  smtstr_len (str_inj s) = &(STRLEN s)
Proof
  simp [smtstr_len_def, str_inj_def, smtstr_rep_def,
        stringTheory.IMPLODE_EXPLODE_I]
QED

Theorem str_inj_isPREFIX:
  isPREFIX s t <=>
    smtstr_prefixof (str_inj s) (str_inj t)
Proof
  qid_spec_tac `t` >>
  Induct_on `s` >>
  Cases_on `t` >>
  simp [str_inj_compute, smtstr_prefixof_def,
        smtstr_rep_def,
        rich_listTheory.IS_PREFIX, stringTheory.ORD_11]
QED

Theorem LLEX_MAP_ORD:
  LLEX $< (MAP ORD s) (MAP ORD t) <=>
    LLEX char_lt s t
Proof
  qid_spec_tac `t` >>
  Induct_on `s` >>
  Cases_on `t` >>
  simp [listTheory.LLEX_THM, stringTheory.char_lt_def,
        stringTheory.ORD_11]
QED

Theorem str_inj_string_lt:
  string_lt s t <=>
    smtstr_lt (str_inj s) (str_inj t)
Proof
  simp [stringTheory.string_lt_LLEX, smtstr_lt_def, str_inj_def,
        smtstr_rep_def,
        stringTheory.IMPLODE_EXPLODE_I, LLEX_MAP_ORD]
QED

Theorem str_inj_string_le:
  string_le s t <=>
    smtstr_le (str_inj s) (str_inj t)
Proof
  simp [stringTheory.string_le_def, smtstr_le_def,
        str_inj_string_lt] >>
  metis_tac []
QED

(* Language-algebra facts used by the derivative proof. *)

Theorem reglan_repeat_zero:
  reglan_repeat p 0 s <=> s = []
Proof
  simp [reglan_repeat_def]
QED

Theorem reglan_repeat_suc:
  reglan_repeat p (SUC n) s <=>
    reglan_dot p (reglan_repeat p n) s
Proof
  rw [reglan_repeat_def, reglan_dot_def, EQ_IMP_THM]
  >- (Cases_on `ss` >>
      fs [] >>
      qexistsl [`h`, `FLAT t`] >>
      simp [] >>
      qexists `t` >>
      simp [])
  >- (qexists `u::ss` >>
      simp [])
QED

Theorem reglan_repeat_one:
  reglan_repeat p (SUC 0) s <=> p s
Proof
  simp [reglan_repeat_suc, reglan_repeat_zero, reglan_dot_def]
QED

Theorem reglan_repeat_singleton:
  reglan_repeat (\u. u = [c]) n s <=> s = REPLICATE n c
Proof
  qid_spec_tac `s` >>
  Induct_on `n` >>
  simp [reglan_repeat_zero, reglan_repeat_suc, reglan_dot_def]
QED

Triviality singleton_parts_flat:
  EVERY (\u. ?c. p c /\ u = [c]) ss ==>
  LENGTH (FLAT ss) = LENGTH ss /\ EVERY p (FLAT ss)
Proof
  Induct_on `ss` >> simp [] >>
  rw [] >> fs []
QED

Triviality flat_map_singleton:
  FLAT (MAP (\c. [c]) s) = s
Proof
  Induct_on `s` >> simp []
QED

Triviality every_map_singleton:
  EVERY (\u. ?c. p c /\ u = [c]) (MAP (\c. [c]) s) <=> EVERY p s
Proof
  simp [listTheory.EVERY_MAP, ETA_AX]
QED

Theorem reglan_repeat_singletons:
  reglan_repeat (\u. ?c. p c /\ u = [c]) n s <=>
  LENGTH s = n /\ EVERY p s
Proof
  PURE_REWRITE_TAC [reglan_repeat_def] >>
  eq_tac
  >- (rw [] >>
      imp_res_tac singleton_parts_flat >>
      fs [])
  >> strip_tac >>
  qexists_tac `MAP (\c. [c]) s` >>
  simp [flat_map_singleton, every_map_singleton]
QED

Theorem REPLICATE_small[local]:
  REPLICATE 1 c = [c] /\
  REPLICATE 2 c = [c; c] /\
  REPLICATE 3 c = [c; c; c]
Proof
  EVAL_TAC
QED

Theorem REPLICATE_eq_cons[local]:
  (d::u = REPLICATE j c) <=>
  ?m. j = SUC m /\ d = c /\ u = REPLICATE m c
Proof
  Cases_on `j` >>
  simp [] >>
  metis_tac []
QED

(* A loop language is the union of the powers between its two bounds.  Every
   loop fact below is an instance of this equation, so none of them has to
   fix the bounds to the ones a particular benchmark happens to use. *)

Theorem reglan_loop_lang_bounds:
  reglan_loop_lang p i n s <=>
  ?j. i <= j /\ j <= n /\ reglan_repeat p j s
Proof
  Induct_on `n` >>
  rw [reglan_loop_lang_def] >>
  eq_tac >> rw []
  >- (qexists `SUC n` >> simp [])
  >- (qexists `j` >> simp [])
  >> Cases_on `j = SUC n` >>
  fs [] >>
  disj2_tac >>
  qexists `j` >>
  simp []
QED

Triviality one_bounds:
  1 <= (j : num) /\ j <= 1 <=> 1 = j
Proof
  ACCEPT_TAC (Q.SPECL [`1`, `j`] arithmeticTheory.LE_ANTISYM)
QED

Triviality one_bounds_extra:
  1 <= (j : num) /\ j <= 1 /\ q <=> j = 1 /\ q
Proof
  metis_tac [one_bounds]
QED

Theorem reglan_loop_lang_once:
  reglan_loop_lang p 1 1 s <=> p s
Proof
  simp [reglan_loop_lang_bounds] >>
  simp [one_bounds_extra] >>
  `(1 : num) = SUC 0` by EVAL_TAC >>
  pop_assum SUBST1_TAC >>
  PURE_REWRITE_TAC [reglan_repeat_one] >>
  REFL_TAC
QED

Theorem smt_in_re_power_loop:
  smt_in_re s (reglan_power r n) <=>
  smt_in_re s (reglan_loop r n n)
Proof
  simp [smt_in_re_def, re_lang_def, reglan_loop_lang_bounds] >>
  metis_tac [arithmeticTheory.LE_ANTISYM]
QED

Triviality singleton_parts_flat3:
  EVERY (\u. ?c. p c /\ q c /\ r c /\ u = [c]) ss ==>
  LENGTH (FLAT ss) = LENGTH ss /\
  EVERY (\c. p c /\ q c /\ r c) (FLAT ss)
Proof
  Induct_on `ss` >> simp [] >>
  rw [] >> fs []
QED

Triviality every_map_singleton3:
  EVERY (\u. ?c. p c /\ q c /\ r c /\ u = [c])
    (MAP (\c. [c]) s) <=>
  EVERY (\c. p c /\ q c /\ r c) s
Proof
  Induct_on `s` >> simp []
QED

Theorem reglan_repeat_singletons3:
  reglan_repeat
    (\u. ?c. p c /\ q c /\ r c /\ u = [c]) n s <=>
  LENGTH s = n /\ EVERY (\c. p c /\ q c /\ r c) s
Proof
  PURE_REWRITE_TAC [reglan_repeat_def] >>
  eq_tac
  >- (rw [] >>
      imp_res_tac singleton_parts_flat3 >>
      fs [])
  >> strip_tac >>
  qexists_tac `MAP (\c. [c]) s` >>
  simp [flat_map_singleton, every_map_singleton3]
QED

Theorem reglan_loop_lang_singletons:
  reglan_loop_lang (\u. ?c. p c /\ u = [c]) i n s <=>
  ?j. i <= j /\ j <= n /\ LENGTH s = j /\ EVERY p s
Proof
  simp [reglan_loop_lang_bounds, reglan_repeat_singletons]
QED

Theorem reglan_loop_lang_singleton:
  reglan_loop_lang (\u. u = [c]) i n s <=>
  ?j. i <= j /\ j <= n /\ s = REPLICATE j c
Proof
  simp [reglan_loop_lang_bounds, reglan_repeat_singleton]
QED

Theorem reglan_repeat_nullable_singleton:
  reglan_repeat (\u. u = [c] \/ u = []) n s <=>
  ?m. m <= n /\ s = REPLICATE m c
Proof
  qid_spec_tac `s` >>
  Induct_on `n`
  >- simp [reglan_repeat_zero]
  >> rpt strip_tac >>
  simp [reglan_repeat_suc, reglan_dot_def] >>
  eq_tac
  >- (rw []
      >- (qexists `SUC m` >> simp [])
      >> qexists `m` >>
      simp [])
  >> rw [] >>
  Cases_on `m` >>
  fs [] >>
  qexistsl [`[c]`, `REPLICATE n' c`] >>
  simp [] >>
  qexists `n'` >>
  simp []
QED

Theorem reglan_loop_lang_nullable_singleton:
  reglan_loop_lang (\u. u = [c] \/ u = []) i n s <=>
  i <= n /\ ?m. m <= n /\ s = REPLICATE m c
Proof
  simp [reglan_loop_lang_bounds, reglan_repeat_nullable_singleton] >>
  eq_tac >> rw []
  >- decide_tac
  >- (qexists `m` >> simp [])
  >> qexists `n` >>
  simp [] >>
  qexists `m` >>
  simp []
QED

(* 'SmtStr [c]' pins down a one-character language only when 'c' is a real
   code point: out of range it is an unconstrained element of ':smtstr', so
   for instance 'SmtStr [c]' and 'SmtStr [c; c]' need not differ.  Every
   singleton-language fact below therefore carries the code-point bound. *)

Theorem smt_in_re_loop_singleton:
  c <= 196607 ==>
  (smt_in_re s (reglan_loop (reglan_to_re (SmtStr [c])) i n) <=>
   ?j. i <= j /\ j <= n /\ s = SmtStr (REPLICATE j c))
Proof
  strip_tac >>
  simp [smt_in_re_def, re_lang_def, smtstr_rep_def,
        reglan_loop_lang_singleton] >>
  `!j. EVERY (\c. c <= 196607) (REPLICATE j c)` by
    simp [rich_listTheory.EVERY_REPLICATE] >>
  metis_tac [smtstr_eq_SmtStr]
QED

Theorem smt_in_re_loop_nullable_singleton:
  c <= 196607 ==>
  (smt_in_re s
     (reglan_loop
       (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
       i n) <=>
   i <= n /\ ?m. m <= n /\ s = SmtStr (REPLICATE m c))
Proof
  strip_tac >>
  simp [smt_in_re_def, re_lang_def, smtstr_rep_def,
        reglan_loop_lang_nullable_singleton] >>
  `!j. EVERY (\c. c <= 196607) (REPLICATE j c)` by
    simp [rich_listTheory.EVERY_REPLICATE] >>
  metis_tac [smtstr_eq_SmtStr]
QED

(* A loop with both bounds zero is the empty-word language; the derivative
   lemmas below use this to hand the terminal state back in the shape the
   replay path expects. *)

Theorem smt_in_re_loop_empty:
  smt_in_re s (reglan_loop r 0 0) <=>
  smt_in_re s (reglan_to_re (SmtStr []))
Proof
  simp [smt_in_re_def, reglan_loop_lang_def, reglan_repeat_zero,
        smtstr_rep_eq_nil]
QED

(* Named instances for the bounds the recorded Z3 corpus uses.  They are
   corollaries of the general lemmas above, not independent proofs. *)

Theorem smt_in_re_loop_singleton_0_1:
  c <= 196607 ==>
  (smt_in_re s (reglan_loop (reglan_to_re (SmtStr [c])) 0 1) <=>
   s = SmtStr [] \/ s = SmtStr [c])
Proof
  rw [smt_in_re_loop_singleton] >>
  eq_tac >> rw []
  >- (`j = 0 \/ j = 1` by decide_tac >> fs [REPLICATE_small])
  >- (qexists `0` >> simp [])
  >> qexists `1` >>
  simp [REPLICATE_small]
QED

Theorem smt_in_re_loop_singleton_0_2:
  c <= 196607 ==>
  (smt_in_re s (reglan_loop (reglan_to_re (SmtStr [c])) 0 2) <=>
   s = SmtStr [] \/ s = SmtStr [c] \/ s = SmtStr [c; c])
Proof
  rw [smt_in_re_loop_singleton] >>
  eq_tac >> rw []
  >- (`j = 0 \/ j = 1 \/ j = 2` by decide_tac >> fs [REPLICATE_small])
  >- (qexists `0` >> simp [])
  >- (qexists `1` >> simp [REPLICATE_small])
  >> qexists `2` >>
  simp [REPLICATE_small]
QED

Theorem smt_in_re_loop_singleton_1_3:
  c <= 196607 ==>
  (smt_in_re s (reglan_loop (reglan_to_re (SmtStr [c])) 1 3) <=>
   s = SmtStr [c] \/ s = SmtStr [c; c] \/ s = SmtStr [c; c; c])
Proof
  rw [smt_in_re_loop_singleton] >>
  eq_tac >> rw []
  >- (`j = 1 \/ j = 2 \/ j = 3` by decide_tac >> fs [REPLICATE_small])
  >- (qexists `1` >> simp [REPLICATE_small])
  >- (qexists `2` >> simp [REPLICATE_small])
  >> qexists `3` >>
  simp [REPLICATE_small]
QED

Theorem smt_in_re_loop_nullable_singleton_0_1:
  c <= 196607 ==>
  (smt_in_re s
      (reglan_loop
        (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
        0 1) <=>
   s = SmtStr [] \/ s = SmtStr [c])
Proof
  rw [smt_in_re_loop_nullable_singleton] >>
  eq_tac >> rw []
  >- (`m = 0 \/ m = 1` by decide_tac >> fs [REPLICATE_small])
  >- (qexists `0` >> simp [])
  >> qexists `1` >>
  simp [REPLICATE_small]
QED

Theorem smt_in_re_loop_nullable_singleton_1_2:
  c <= 196607 ==>
  (smt_in_re s
      (reglan_loop
        (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
        1 2) <=>
   s = SmtStr [] \/ s = SmtStr [c] \/ s = SmtStr [c; c])
Proof
  rw [smt_in_re_loop_nullable_singleton] >>
  eq_tac >> rw []
  >- (`m = 0 \/ m = 1 \/ m = 2` by decide_tac >> fs [REPLICATE_small])
  >- (qexists `0` >> simp [])
  >- (qexists `1` >> simp [REPLICATE_small])
  >> qexists `2` >>
  simp [REPLICATE_small]
QED

Theorem reglan_repeat_nil:
  reglan_repeat p n [] <=> n = 0 \/ p []
Proof
  Induct_on `n` >>
  simp [reglan_repeat_zero, reglan_repeat_suc, reglan_dot_def] >>
  metis_tac []
QED

Theorem reglan_loop_lang_too_large:
  n < i ==> ~reglan_loop_lang p i n s
Proof
  Induct_on `n` >>
  simp [reglan_loop_lang_def]
QED

Theorem reglan_loop_lang_nil:
  reglan_loop_lang p i n [] <=>
    i <= n /\ (i = 0 \/ p [])
Proof
  Induct_on `n` >>
  simp [reglan_loop_lang_def, reglan_repeat_nil] >>
  numLib.ARITH_TAC
QED

Theorem reglan_dot_cons:
  (!t. p (c::t) <=> dp t) /\
  (!t. q (c::t) <=> dq t) ==>
  (reglan_dot p q (c::s) <=>
   reglan_dot dp q s \/ p [] /\ dq s)
Proof
  rw [reglan_dot_def] >>
  metis_tac [listTheory.APPEND_EQ_CONS]
QED

Theorem reglan_dot_cons_unfold:
  reglan_dot p q (c::s) <=>
    reglan_dot (\t. p (c::t)) q s \/ p [] /\ q (c::s)
Proof
  rw [reglan_dot_def] >>
  metis_tac [listTheory.APPEND_EQ_CONS]
QED

Theorem reglan_kstar_nil:
  reglan_kstar p []
Proof
  simp [reglan_kstar_def] >>
  qexists `[]` >>
  simp []
QED

Theorem reglan_kstar_cons:
  (!t. p (c::t) <=> dp t) ==>
  (reglan_kstar p (c::s) <=>
   reglan_dot dp (reglan_kstar p) s)
Proof
  rw [reglan_kstar_def, reglan_dot_def, EQ_IMP_THM]
  >- (Cases_on `ss` >>
      fs [] >>
      Cases_on `h` >>
      fs [] >>
      metis_tac [])
  >- (qexists `(c::u)::ss` >>
      simp [])
QED

Theorem reglan_kstar_cons_unfold:
  reglan_kstar p (c::s) <=>
    reglan_dot (\t. p (c::t)) (reglan_kstar p) s
Proof
  irule reglan_kstar_cons >>
  simp []
QED

Theorem reglan_kstar_cvc_unfold:
  reglan_kstar p s ==>
    s = [] \/ p s \/
    ?u v w.
      p u /\ reglan_kstar p v /\ p w /\
      u <> [] /\ w <> [] /\ s = (u ++ v) ++ w
Proof
  rw [reglan_kstar_def] >>
  Cases_on `ss`
  >- simp [] >>
  Cases_on `t` using listTheory.SNOC_CASES
  >- fs [] >>
  disj2_tac >> disj2_tac >>
  qexistsl [`h`, `FLAT l`, `x`] >>
  fs [rich_listTheory.FLAT_SNOC, listTheory.EVERY_SNOC,
      listTheory.APPEND_ASSOC] >>
  simp [reglan_kstar_def] >>
  qexists `l` >>
  simp []
QED

Theorem re_nullable_lang:
  re_nullable r <=> re_lang r []
Proof
  Induct_on `r` >>
  simp [re_nullable_def, re_lang_def,
        reglan_dot_def, reglan_kstar_nil, reglan_repeat_nil,
        reglan_loop_lang_nil, smtstr_rep_eq_nil] >>
  metis_tac []
QED

Theorem re_nullable_correct:
  re_nullable r <=> smt_in_re (SmtStr []) r
Proof
  simp [smt_in_re_rep, re_nullable_lang]
QED

Theorem reglan_power_deriv_correct:
  (!t. re_lang dr t <=> re_lang r (c::t)) /\
  (nullable <=> re_lang r []) ==>
  (re_lang (reglan_power_deriv dr nullable r n) s <=>
   reglan_repeat (\u. re_lang r u) n (c::s))
Proof
  strip_tac >>
  qid_spec_tac `s` >>
  Induct_on `n`
  >- simp [reglan_power_deriv_def, re_lang_def, reglan_repeat_zero]
  >> rpt strip_tac >>
  Cases_on `nullable` >>
  fs [reglan_power_deriv_def, re_lang_def,
      reglan_repeat_suc, reglan_dot_cons_unfold] >>
  metis_tac []
QED

Theorem reglan_loop_deriv_correct:
  (!t. re_lang dr t <=> re_lang r (c::t)) /\
  (nullable <=> re_lang r []) ==>
  (re_lang (reglan_loop_deriv dr nullable r i n) s <=>
   reglan_loop_lang (\u. re_lang r u) i n (c::s))
Proof
  strip_tac >>
  fs [] >>
  qid_spec_tac `s` >>
  Induct_on `n`
  >- simp [reglan_loop_deriv_def, re_lang_def,
           reglan_loop_lang_def, reglan_repeat_zero]
  >> rpt strip_tac >>
  Cases_on `i <= SUC n`
  >- (`re_lang (reglan_power_deriv dr (re_lang r []) r (SUC n)) s <=>
       reglan_repeat (\u. re_lang r u) (SUC n) (c::s)` by
        (irule reglan_power_deriv_correct >>
         simp []) >>
      simp [reglan_loop_deriv_def, re_lang_def, reglan_loop_lang_def])
  >- (`n < i` by fs [] >>
      simp [reglan_loop_deriv_def, re_lang_def,
            reglan_loop_lang_def, reglan_loop_lang_too_large])
QED

Theorem re_deriv_lang:
  re_lang r (c::u) <=> re_lang (re_deriv c r) u
Proof
  qid_spec_tac `u` >>
  Induct_on `r` >>
  rpt strip_tac
  >- simp [re_deriv_def, re_lang_def]
  >- (Cases_on `c <= 196607` >>
      simp [re_deriv_def, re_lang_def])
  >- (Cases_on `c <= 196607` >>
      simp [re_deriv_def, re_lang_def] >>
      metis_tac [])
  >- (Cases_on `s` >>
      Cases_on `l` >>
      simp [re_deriv_def, re_lang_def, smtstr_rep_def] >>
      Cases_on `c = h` >>
      fs [re_lang_def, smtstr_rep_def])
  >- (Cases_on `smtstr_rep s` >>
      simp [re_deriv_def, re_lang_def] >>
      Cases_on `t` >>
      simp [re_lang_def] >>
      Cases_on `smtstr_rep s0` >>
      simp [re_lang_def] >>
      Cases_on `t` >>
      simp [re_lang_def] >>
      Cases_on `h <= c /\ c <= h' /\ c <= 196607` >>
      simp [re_lang_def])
  >- (`reglan_dot (\x. re_lang r x) (\y. re_lang r' y) (c::u) <=>
       reglan_dot
         (\x. re_lang (re_deriv c r) x) (\y. re_lang r' y) u \/
       re_lang r [] /\ re_lang (re_deriv c r') u` by
        (rw [reglan_dot_def] >>
         metis_tac [listTheory.APPEND_EQ_CONS]) >>
      PURE_REWRITE_TAC [re_deriv_def, re_lang_def, re_nullable_lang] >>
      Cases_on `re_lang r []` >>
      fs [re_lang_def])
  >- simp [re_deriv_def, re_lang_def]
  >- simp [re_deriv_def, re_lang_def]
  >- simp [re_deriv_def, re_lang_def]
  >- (Cases_on `c <= 196607` >>
      simp [re_deriv_def, re_lang_def])
  >- simp [re_deriv_def, re_lang_def, reglan_kstar_cons_unfold,
           reglan_dot_def]
  >- (simp [re_deriv_def, re_lang_def,
            reglan_dot_cons_unfold,
            reglan_kstar_cons_unfold] >>
      simp [reglan_dot_def] >>
      metis_tac [])
  >- simp [re_deriv_def, re_lang_def]
  >- simp [re_deriv_def, re_lang_def, re_nullable_lang,
           reglan_power_deriv_correct]
  >- simp [re_deriv_def, re_lang_def, re_nullable_lang,
           reglan_loop_deriv_correct]
QED

(* The word-level statement above is unconditional; its ':smtstr' reading
   needs the leading character and the tail to be genuine code points,
   because 'SmtStr (c::s)' is otherwise unconstrained. *)

Theorem re_deriv_correct:
  EVERY (\x. x <= 196607) (c::s) ==>
  (smt_in_re (SmtStr (c::s)) r <=>
   smt_in_re (SmtStr s) (re_deriv c r))
Proof
  strip_tac >>
  fs [smt_in_re_rep, smtstr_rep_def, re_deriv_lang]
QED

Theorem reglan_kstar_singleton_gen[local]:
  (!u. p u <=> ?c. q c /\ u = [c]) ==>
  !s. reglan_kstar p s <=> EVERY q s
Proof
  strip_tac >>
  Induct
  >- simp [reglan_kstar_nil] >>
  rpt strip_tac >>
  PURE_REWRITE_TAC [reglan_kstar_cons_unfold] >>
  simp [reglan_dot_def] >>
  metis_tac []
QED

Theorem reglan_kstar_allchar_gen[local]:
  (!u. p u <=> ?c. c <= 196607 /\ u = [c]) ==>
  !s. reglan_kstar p s <=> EVERY (\c. c <= 196607) s
Proof
  strip_tac >>
  Induct
  >- simp [reglan_kstar_nil]
  >> rpt strip_tac >>
  PURE_REWRITE_TAC [reglan_kstar_cons_unfold] >>
  simp [reglan_dot_def] >>
  metis_tac []
QED

Theorem reglan_kstar_allchar:
  reglan_kstar (\u. ?c. c <= 196607 /\ u = [c]) s <=>
  EVERY (\c. c <= 196607) s
Proof
  irule reglan_kstar_allchar_gen >>
  simp []
QED

Theorem re_lang_wf:
  re_lang r u ==> EVERY (\c. c <= 196607) u
Proof
  qid_spec_tac `u` >> Induct_on `r` >>
  simp [re_lang_def, reglan_dot_def, reglan_kstar_def,
        reglan_repeat_def, reglan_loop_lang_bounds] >>
  rw [] >>
  fs [listTheory.EVERY_FLAT, listTheory.EVERY_MEM] >>
  metis_tac []
QED

Triviality flat_filter_nonempty:
  FLAT (FILTER (\u. u <> []) ss) = FLAT ss
Proof
  Induct_on `ss` >> simp [] >> rw [] >> simp []
QED

Theorem reglan_kstar_relaxed:
  reglan_kstar p s <=> ?ss. EVERY p ss /\ s = FLAT ss
Proof
  PURE_REWRITE_TAC [reglan_kstar_def] >> eq_tac >> strip_tac
  >> qexists `FILTER (\u. u <> []) ss` >>
  simp [listTheory.EVERY_FILTER, flat_filter_nonempty] >>
  fs [listTheory.EVERY_MEM]
QED

Theorem reglan_kstar_append:
  reglan_kstar p u /\ reglan_kstar p v ==>
  reglan_kstar p (u ++ v)
Proof
  rw [reglan_kstar_relaxed] >>
  qexists `ss ++ ss'` >> simp []
QED

Theorem reglan_kstar_single:
  p u ==> reglan_kstar p u
Proof
  strip_tac >> simp [reglan_kstar_relaxed] >>
  qexists `[u]` >> simp []
QED

Theorem reglan_dot_assoc:
  reglan_dot (reglan_dot p q) r s <=>
  reglan_dot p (reglan_dot q r) s
Proof
  rw [reglan_dot_def] >> metis_tac [listTheory.APPEND_ASSOC]
QED

Triviality reglan_kstar_flat:
  EVERY (reglan_kstar p) ss ==> reglan_kstar p (FLAT ss)
Proof
  Induct_on `ss` >> simp [reglan_kstar_nil] >>
  metis_tac [reglan_kstar_append]
QED

Triviality reglan_dot_kstar_characterization:
  reglan_dot p (reglan_kstar p) s <=>
  ?xs. xs <> [] /\ EVERY p xs /\ s = FLAT xs
Proof
  simp [reglan_dot_def, reglan_kstar_relaxed] >> eq_tac
  >- (rw [] >> qexists `u::ss` >> simp []) >>
  rw [] >> Cases_on `xs` >> fs [] >>
  qexistsl [`h`, `FLAT t`] >> simp [] >>
  qexists `t` >> simp []
QED

Triviality reglan_kstar_dot_characterization:
  reglan_dot (reglan_kstar p) p s <=>
  ?xs. xs <> [] /\ EVERY p xs /\ s = FLAT xs
Proof
  simp [reglan_dot_def, reglan_kstar_relaxed] >> eq_tac
  >- (rw [] >> qexists `ss ++ [v]` >>
      simp [rich_listTheory.FLAT_SNOC]) >>
  rw [] >> Cases_on `xs` using listTheory.SNOC_CASES >>
  fs [listTheory.EVERY_SNOC, rich_listTheory.FLAT_SNOC] >>
  qexistsl [`FLAT l`, `x`] >> simp [] >>
  qexists `l` >> simp []
QED

Theorem reglan_kstar_dot_comm:
  reglan_dot (reglan_kstar p) p s <=>
  reglan_dot p (reglan_kstar p) s
Proof
  simp [reglan_dot_kstar_characterization,
        reglan_kstar_dot_characterization]
QED

Theorem reglan_kstar_idem:
  reglan_kstar (reglan_kstar p) s <=> reglan_kstar p s
Proof
  eq_tac
  >- (strip_tac >> fs [reglan_kstar_relaxed] >>
      imp_res_tac reglan_kstar_flat >>
      fs [reglan_kstar_relaxed] >> metis_tac []) >>
  strip_tac >> simp [reglan_kstar_relaxed] >>
  qexists `[s]` >> simp []
QED

Theorem reglan_kstar_epsilon:
  reglan_kstar (\u. u = []) s <=> s = []
Proof
  eq_tac
  >- (rw [reglan_kstar_relaxed] >>
      Induct_on `ss` >> fs []) >>
  strip_tac >> simp [reglan_kstar_nil]
QED

Theorem reglan_kstar_none:
  reglan_kstar (\u. F) s <=> s = []
Proof
  simp [reglan_kstar_relaxed] >> metis_tac []
QED

Theorem reglan_kstar_drop_epsilon:
  reglan_kstar (\u. p u \/ u = []) s <=> reglan_kstar p s
Proof
  eq_tac
  >- (rw [reglan_kstar_relaxed] >>
      qexists `FILTER (\u. u <> []) ss` >>
      simp [listTheory.EVERY_FILTER, flat_filter_nonempty] >>
      fs [listTheory.EVERY_MEM] >> metis_tac []) >>
  rw [reglan_kstar_relaxed] >> qexists `ss` >>
  fs [listTheory.EVERY_MEM] >> metis_tac []
QED

Theorem reglan_kstar_cong:
  (!u. p u <=> q u) ==>
  (reglan_kstar p s <=> reglan_kstar q s)
Proof
  simp [reglan_kstar_relaxed, listTheory.EVERY_MEM] >> metis_tac []
QED

Theorem reglan_kstar_epsilon_invariant:
  (!u. p u <=> q u \/ u = []) ==>
  (reglan_kstar p s <=> reglan_kstar q s)
Proof
  strip_tac >>
  `reglan_kstar p s <=>
   reglan_kstar (\u. q u \/ u = []) s` by
    (irule reglan_kstar_cong >> simp [] >> metis_tac []) >>
  fs [reglan_kstar_drop_epsilon]
QED

Theorem reglan_kstar_mono:
  (!u. p u ==> q u) ==> reglan_kstar p s ==> reglan_kstar q s
Proof
  simp [reglan_kstar_relaxed, listTheory.EVERY_MEM] >> metis_tac []
QED

Theorem reglan_kstar_wf:
  (!u. p u ==> EVERY (\c. c <= 196607) u) /\
  reglan_kstar p s ==>
  EVERY (\c. c <= 196607) s
Proof
  rw [reglan_kstar_relaxed] >>
  fs [listTheory.EVERY_FLAT, listTheory.EVERY_MEM] >> metis_tac []
QED

Theorem reglan_kstar_allchar_sandwich:
  (!u. p u ==> EVERY (\c. c <= 196607) u) /\
  (!c. c <= 196607 ==> p [c]) ==>
  (reglan_kstar p s <=> EVERY (\c. c <= 196607) s)
Proof
  strip_tac >> eq_tac
  >- (strip_tac >> irule reglan_kstar_wf >> metis_tac []) >>
  strip_tac >>
  `reglan_kstar (\u. ?c. c <= 196607 /\ u = [c]) s` by
    fs [reglan_kstar_allchar] >>
  irule reglan_kstar_mono >>
  qexists `\u. ?c. c <= 196607 /\ u = [c]` >>
  simp [] >> metis_tac []
QED

Theorem reglan_kstar_dot_subsume:
  (!u. p u ==> q u) ==>
  (reglan_dot (reglan_kstar p) (reglan_kstar q) s <=>
   reglan_kstar q s)
Proof
  strip_tac >> eq_tac
  >- (rw [reglan_dot_def] >>
      metis_tac [reglan_kstar_append, reglan_kstar_mono]) >>
  strip_tac >> rw [reglan_dot_def] >>
  qexistsl [`[]`, `s`] >> simp [reglan_kstar_nil]
QED

Theorem reglan_equiv_star_swap:
  reglan_equiv
    (reglan_concat (reglan_star r) r)
    (reglan_concat r (reglan_star r))
Proof
  simp [reglan_equiv_def, re_lang_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp [reglan_kstar_dot_comm]
QED

Theorem reglan_equiv_star_repeat:
  reglan_equiv
    (reglan_concat (reglan_star r) (reglan_star r))
    (reglan_star r)
Proof
  simp [reglan_equiv_def, re_lang_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp [reglan_kstar_dot_subsume]
QED

Theorem reglan_equiv_star_none:
  reglan_equiv (reglan_star reglan_none)
    (reglan_to_re (SmtStr []))
Proof
  simp [reglan_equiv_def, re_lang_def, reglan_kstar_none,
        smtstr_rep_def]
QED

Theorem reglan_equiv_star_epsilon:
  reglan_equiv (reglan_star (reglan_to_re (SmtStr [])))
    (reglan_to_re (SmtStr []))
Proof
  simp [reglan_equiv_def, re_lang_def, reglan_kstar_epsilon,
        smtstr_rep_def]
QED

Theorem reglan_equiv_star_star:
  reglan_equiv (reglan_star (reglan_star r)) (reglan_star r)
Proof
  simp [reglan_equiv_def, re_lang_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp [reglan_kstar_idem]
QED

Theorem reglan_equiv_star_drop_epsilon:
  reglan_equiv
    (reglan_star (reglan_union r (reglan_to_re (SmtStr []))))
    (reglan_star r)
Proof
  simp [reglan_equiv_def, re_lang_def, reglan_kstar_drop_epsilon,
        smtstr_rep_def]
QED

Theorem reglan_equiv_star_subsume_right:
  reglan_equiv
    (reglan_concat (reglan_star r)
      (reglan_star reglan_allchar))
    (reglan_star reglan_allchar)
Proof
  simp [reglan_equiv_def, re_lang_def, reglan_dot_def,
        reglan_kstar_allchar] >> gen_tac >> eq_tac
  >- (rw [] >>
      `EVERY (\c. c <= 196607) x` by
        (irule reglan_kstar_wf >> simp [] >> metis_tac [re_lang_wf]) >>
      simp []) >>
  strip_tac >> qexistsl [`[]`, `u`] >> simp [reglan_kstar_nil]
QED

Theorem reglan_equiv_star_subsume_left:
  reglan_equiv
    (reglan_concat (reglan_star reglan_allchar)
      (reglan_star r))
    (reglan_star reglan_allchar)
Proof
  simp [reglan_equiv_def, re_lang_def, reglan_dot_def,
        reglan_kstar_allchar] >> gen_tac >> eq_tac
  >- (rw [] >>
      `EVERY (\c. c <= 196607) y` by
        (irule reglan_kstar_wf >> simp [] >> metis_tac [re_lang_wf]) >>
      simp []) >>
  strip_tac >> qexistsl [`u`, `[]`] >> simp [reglan_kstar_nil]
QED

Theorem reglan_star_subsume_right_lang:
  reglan_dot
    (reglan_kstar (re_lang r))
    (reglan_kstar (\u. ?c. c <= 196607 /\ u = [c])) s <=>
  reglan_kstar (\u. ?c. c <= 196607 /\ u = [c]) s
Proof
  simp [re_lang_def, reglan_dot_def, reglan_kstar_allchar] >> eq_tac
  >- (rw [] >>
      `EVERY (\c. c <= 196607) u` by
        (irule reglan_kstar_wf >> simp [] >> metis_tac [re_lang_wf]) >>
      simp []) >>
  strip_tac >> qexistsl [`[]`, `s`] >> simp [reglan_kstar_nil]
QED

Theorem reglan_star_subsume_left_lang:
  reglan_dot
    (reglan_kstar (\u. ?c. c <= 196607 /\ u = [c]))
    (reglan_kstar (re_lang r)) s <=>
  reglan_kstar (\u. ?c. c <= 196607 /\ u = [c]) s
Proof
  simp [re_lang_def, reglan_dot_def, reglan_kstar_allchar] >> eq_tac
  >- (rw [] >>
      `EVERY (\c. c <= 196607) v` by
        (irule reglan_kstar_wf >> simp [] >> metis_tac [re_lang_wf]) >>
      simp []) >>
  strip_tac >> qexistsl [`s`, `[]`] >> simp [reglan_kstar_nil]
QED

Theorem reglan_dot_left_cong:
  (!u. p u <=> q u) ==>
  (reglan_dot p r s <=> reglan_dot q r s)
Proof
  simp [reglan_dot_def] >> metis_tac []
QED

Theorem reglan_star_swap_suffix:
  reglan_dot (reglan_kstar p) (reglan_dot p q) s <=>
  reglan_dot p (reglan_dot (reglan_kstar p) q) s
Proof
  Rewrite.PURE_REWRITE_TAC [GSYM reglan_dot_assoc] >>
  irule reglan_dot_left_cong >> simp [reglan_kstar_dot_comm]
QED

Theorem reglan_star_repeat_suffix:
  reglan_dot (reglan_kstar p) (reglan_dot (reglan_kstar p) q) s <=>
  reglan_dot (reglan_kstar p) q s
Proof
  Rewrite.PURE_REWRITE_TAC [GSYM reglan_dot_assoc] >>
  irule reglan_dot_left_cong >> simp [reglan_kstar_dot_subsume]
QED

Theorem reglan_star_subsume_right_suffix:
  reglan_dot (reglan_kstar (re_lang r))
    (reglan_dot (reglan_kstar
      (\u. ?c. c <= 196607 /\ u = [c])) q) s <=>
  reglan_dot (reglan_kstar
    (\u. ?c. c <= 196607 /\ u = [c])) q s
Proof
  Rewrite.PURE_REWRITE_TAC [GSYM reglan_dot_assoc] >>
  irule reglan_dot_left_cong >>
  MATCH_ACCEPT_TAC
    (CONV_RULE (DEPTH_CONV ETA_CONV)
      reglan_star_subsume_right_lang)
QED

Theorem reglan_star_subsume_left_suffix:
  reglan_dot (reglan_kstar
      (\u. ?c. c <= 196607 /\ u = [c]))
    (reglan_dot (reglan_kstar (re_lang r)) q) s <=>
  reglan_dot (reglan_kstar
    (\u. ?c. c <= 196607 /\ u = [c])) q s
Proof
  Rewrite.PURE_REWRITE_TAC [GSYM reglan_dot_assoc] >>
  irule reglan_dot_left_cong >>
  MATCH_ACCEPT_TAC
    (CONV_RULE (DEPTH_CONV ETA_CONV)
      reglan_star_subsume_left_lang)
QED

Theorem reglan_star_swap_suffix_fun:
  reglan_dot (reglan_kstar p) (reglan_dot p q) =
  reglan_dot p (reglan_dot (reglan_kstar p) q)
Proof
  simp [FUN_EQ_THM, reglan_star_swap_suffix]
QED

Theorem reglan_star_repeat_suffix_fun:
  reglan_dot (reglan_kstar p) (reglan_dot (reglan_kstar p) q) =
  reglan_dot (reglan_kstar p) q
Proof
  simp [FUN_EQ_THM, reglan_star_repeat_suffix]
QED

Theorem reglan_star_subsume_right_suffix_fun:
  reglan_dot (reglan_kstar (re_lang r))
    (reglan_dot (reglan_kstar
      (\u. ?c. c <= 196607 /\ u = [c])) q) =
  reglan_dot (reglan_kstar
    (\u. ?c. c <= 196607 /\ u = [c])) q
Proof
  simp [FUN_EQ_THM] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp [reglan_star_subsume_right_suffix]
QED

Theorem reglan_star_subsume_left_suffix_fun:
  reglan_dot (reglan_kstar
      (\u. ?c. c <= 196607 /\ u = [c]))
    (reglan_dot (reglan_kstar (re_lang r)) q) =
  reglan_dot (reglan_kstar
    (\u. ?c. c <= 196607 /\ u = [c])) q
Proof
  simp [FUN_EQ_THM] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp [reglan_star_subsume_left_suffix]
QED

Theorem reglan_equiv_star_subsume_right_suffix:
  reglan_equiv
    (reglan_concat (reglan_star r)
      (reglan_concat (reglan_star reglan_allchar) q))
    (reglan_concat (reglan_star reglan_allchar) q)
Proof
  simp [reglan_equiv_def, re_lang_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp [reglan_star_subsume_right_suffix]
QED

Theorem reglan_equiv_star_subsume_left_suffix:
  reglan_equiv
    (reglan_concat (reglan_star reglan_allchar)
      (reglan_concat (reglan_star r) q))
    (reglan_concat (reglan_star reglan_allchar) q)
Proof
  simp [reglan_equiv_def, re_lang_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp [reglan_star_subsume_left_suffix]
QED

Theorem reglan_concat_literals_suffix_fun:
  reglan_dot (re_lang (reglan_to_re s))
    (reglan_dot (re_lang (reglan_to_re t)) q) =
  reglan_dot (re_lang (reglan_to_re (smtstr_concat s t))) q
Proof
  simp [FUN_EQ_THM, re_lang_def, smtstr_rep_def,
        smtstr_concat_def, reglan_dot_def] >>
  metis_tac [listTheory.APPEND_ASSOC]
QED

Theorem reglan_concat_literals_suffix_rep_fun:
  reglan_dot (\u. u = smtstr_rep s)
    (reglan_dot (\u. u = smtstr_rep t) q) =
  reglan_dot (\u. u = smtstr_rep (smtstr_concat s t)) q
Proof
  simp [FUN_EQ_THM, smtstr_rep_def, smtstr_concat_def,
        reglan_dot_def] >>
  metis_tac [listTheory.APPEND_ASSOC]
QED

Theorem reglan_equiv_star_union_allchar:
  reglan_equiv
    (reglan_star (reglan_union r reglan_allchar))
    (reglan_star reglan_allchar)
Proof
  simp [reglan_equiv_def, re_lang_def, reglan_kstar_allchar] >>
  gen_tac >> eq_tac >> strip_tac
  >- (irule reglan_kstar_wf >>
      qexists `\x. re_lang r x \/
        ?c. c <= 196607 /\ x = [c]` >>
      conj_tac
      >- (gen_tac >> strip_tac >> fs [] >>
          metis_tac [re_lang_wf]) >>
      first_assum ACCEPT_TAC) >>
  fs [reglan_kstar_relaxed] >>
  qexists `MAP (\c. [c]) u` >>
  simp [listTheory.EVERY_MAP, flat_map_singleton] >>
  fs [listTheory.EVERY_MEM] >> metis_tac []
QED

Theorem reglan_star_union_allchar_lang:
  reglan_kstar
    (\u. re_lang r u \/ re_lang reglan_allchar u) s <=>
  reglan_kstar (\u. re_lang reglan_allchar u) s
Proof
  simp [re_lang_def, reglan_kstar_allchar] >> eq_tac >> strip_tac
  >- (irule reglan_kstar_wf >>
      qexists `\x. re_lang r x \/
        ?c. c <= 196607 /\ x = [c]` >>
      conj_tac
      >- (gen_tac >> strip_tac >> fs [] >>
          metis_tac [re_lang_wf]) >>
      first_assum ACCEPT_TAC) >>
  fs [reglan_kstar_relaxed] >>
  qexists `MAP (\c. [c]) s` >>
  simp [listTheory.EVERY_MAP, flat_map_singleton] >>
  fs [listTheory.EVERY_MEM] >> metis_tac []
QED

Theorem reglan_equiv_union_const:
  smt_in_re s r ==>
  reglan_equiv (reglan_union (reglan_to_re s) r) r
Proof
  simp [reglan_equiv_def, re_lang_def, smt_in_re_rep] >> metis_tac []
QED

Theorem reglan_equiv_inter_cstring:
  smt_in_re s r ==>
  reglan_equiv (reglan_inter (reglan_to_re s) r)
    (reglan_to_re s)
Proof
  simp [reglan_equiv_def, re_lang_def, smt_in_re_rep] >> metis_tac []
QED

Theorem reglan_equiv_inter_cstring_none:
  ~smt_in_re s r ==>
  reglan_equiv (reglan_inter (reglan_to_re s) r) reglan_none
Proof
  simp [reglan_equiv_def, re_lang_def, smt_in_re_rep] >> metis_tac []
QED

Theorem smt_in_re_inter_left:
  smt_in_re s (reglan_inter r q) ==> smt_in_re s r
Proof
  simp [smt_in_re_def]
QED

Theorem reglan_equiv_inter_cstring_step:
  smt_in_re s (reglan_inter r q) /\
  reglan_equiv r (reglan_to_re s) ==>
  reglan_equiv (reglan_inter r q) (reglan_to_re s)
Proof
  simp [reglan_equiv_def, re_lang_def, smt_in_re_rep] >> metis_tac []
QED

Theorem reglan_equiv_power_loop:
  reglan_equiv (reglan_power r n) (reglan_loop r n n)
Proof
  simp [reglan_equiv_def, re_lang_def, reglan_loop_lang_bounds] >>
  metis_tac [arithmeticTheory.LE_ANTISYM]
QED

Theorem reglan_equiv_power_zero:
  reglan_equiv (reglan_power r 0) (reglan_to_re (SmtStr []))
Proof
  simp [reglan_equiv_def, re_lang_def, reglan_repeat_zero,
        smtstr_rep_def]
QED

Theorem reglan_equiv_power_one:
  reglan_equiv (reglan_power r 1) r
Proof
  simp [reglan_equiv_def, re_lang_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  PURE_REWRITE_TAC [arithmeticTheory.ONE, reglan_repeat_one] >>
  simp []
QED

Theorem reglan_equiv_power_suc:
  reglan_equiv (reglan_power r (SUC n))
    (reglan_concat r (reglan_power r n))
Proof
  simp [reglan_equiv_def, re_lang_def, reglan_repeat_suc] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp []
QED

Theorem reglan_equiv_plus:
  reglan_equiv (reglan_plus r)
    (reglan_concat r (reglan_star r))
Proof
  simp [reglan_equiv_def, re_lang_def, reglan_dot_def]
QED

Theorem reglan_equiv_opt:
  reglan_equiv (reglan_opt r)
    (reglan_union (reglan_to_re (SmtStr [])) r)
Proof
  simp [reglan_equiv_def, re_lang_def, smtstr_rep_def]
QED

Theorem reglan_equiv_diff:
  reglan_equiv (reglan_diff r s)
    (reglan_inter r (reglan_comp s))
Proof
  simp [reglan_equiv_def, re_lang_def] >>
  metis_tac [re_lang_wf]
QED

Theorem reglan_equiv_all:
  reglan_equiv reglan_all (reglan_star reglan_allchar)
Proof
  simp [reglan_equiv_def, re_lang_def, reglan_kstar_allchar]
QED

Theorem reglan_equiv_union_all:
  reglan_equiv (reglan_union r reglan_all) reglan_all
Proof
  simp [reglan_equiv_def, re_lang_def] >> metis_tac [re_lang_wf]
QED

Theorem reglan_equiv_inter_all:
  reglan_equiv (reglan_inter r reglan_all) r
Proof
  simp [reglan_equiv_def, re_lang_def] >> metis_tac [re_lang_wf]
QED

Theorem reglan_equiv_union_all_left:
  reglan_equiv (reglan_union reglan_all r) reglan_all
Proof
  simp [reglan_equiv_def, re_lang_def] >> metis_tac [re_lang_wf]
QED

Theorem reglan_equiv_inter_all_left:
  reglan_equiv (reglan_inter reglan_all r) r
Proof
  simp [reglan_equiv_def, re_lang_def] >> metis_tac [re_lang_wf]
QED

Theorem reglan_equiv_union_star_all:
  reglan_equiv
    (reglan_union r (reglan_star reglan_allchar))
    (reglan_star reglan_allchar)
Proof
  simp [reglan_equiv_def, re_lang_def, reglan_kstar_allchar] >>
  metis_tac [re_lang_wf]
QED

Theorem reglan_equiv_union_star_all_left:
  reglan_equiv
    (reglan_union (reglan_star reglan_allchar) r)
    (reglan_star reglan_allchar)
Proof
  simp [reglan_equiv_def, re_lang_def, reglan_kstar_allchar] >>
  metis_tac [re_lang_wf]
QED

Theorem reglan_equiv_inter_star_all:
  reglan_equiv
    (reglan_inter r (reglan_star reglan_allchar)) r
Proof
  simp [reglan_equiv_def, re_lang_def, reglan_kstar_allchar] >>
  metis_tac [re_lang_wf]
QED

Theorem reglan_equiv_inter_star_all_left:
  reglan_equiv
    (reglan_inter (reglan_star reglan_allchar) r) r
Proof
  simp [reglan_equiv_def, re_lang_def, reglan_kstar_allchar] >>
  metis_tac [re_lang_wf]
QED

Theorem reglan_equiv_concat_assoc:
  reglan_equiv
    (reglan_concat (reglan_concat r s) t)
    (reglan_concat r (reglan_concat s t))
Proof
  simp [reglan_equiv_def, re_lang_def, reglan_dot_def] >>
  metis_tac [listTheory.APPEND_ASSOC]
QED

Theorem reglan_equiv_star_subsume_right_context:
  reglan_equiv
    (reglan_concat
      (reglan_concat
        (reglan_concat p (reglan_star r))
        (reglan_star reglan_allchar)) q)
    (reglan_concat
      (reglan_concat p (reglan_star reglan_allchar)) q)
Proof
  irule reglan_concat_equiv >> conj_tac
  >- (irule reglan_equiv_trans >>
      qexists_tac
        `reglan_concat p
          (reglan_concat (reglan_star r)
            (reglan_star reglan_allchar))` >>
      conj_tac
      >- simp [reglan_equiv_concat_assoc] >>
      irule reglan_concat_equiv >>
      simp [reglan_equiv_refl, reglan_equiv_star_subsume_right]) >>
  simp [reglan_equiv_refl]
QED

Theorem reglan_equiv_star_subsume_left_context:
  reglan_equiv
    (reglan_concat
      (reglan_concat
        (reglan_concat p (reglan_star reglan_allchar))
        (reglan_star r)) q)
    (reglan_concat
      (reglan_concat p (reglan_star reglan_allchar)) q)
Proof
  irule reglan_concat_equiv >> conj_tac
  >- (irule reglan_equiv_trans >>
      qexists_tac
        `reglan_concat p
          (reglan_concat (reglan_star reglan_allchar)
            (reglan_star r))` >>
      conj_tac
      >- simp [reglan_equiv_concat_assoc] >>
      irule reglan_concat_equiv >>
      simp [reglan_equiv_refl, reglan_equiv_star_subsume_left]) >>
  simp [reglan_equiv_refl]
QED

Theorem reglan_equiv_union_assoc:
  reglan_equiv
    (reglan_union (reglan_union r s) t)
    (reglan_union r (reglan_union s t))
Proof
  simp [reglan_equiv_def, re_lang_def] >> metis_tac []
QED

Theorem reglan_equiv_union_comm:
  reglan_equiv (reglan_union r s) (reglan_union s r)
Proof
  simp [reglan_equiv_def, re_lang_def] >> metis_tac []
QED

Theorem reglan_equiv_inter_assoc:
  reglan_equiv
    (reglan_inter (reglan_inter r s) t)
    (reglan_inter r (reglan_inter s t))
Proof
  simp [reglan_equiv_def, re_lang_def] >> metis_tac []
QED

Theorem reglan_equiv_inter_comm:
  reglan_equiv (reglan_inter r s) (reglan_inter s r)
Proof
  simp [reglan_equiv_def, re_lang_def] >> metis_tac []
QED

Theorem reglan_equiv_concat_literals:
  reglan_equiv
    (reglan_concat (reglan_to_re s) (reglan_to_re t))
    (reglan_to_re (smtstr_concat s t))
Proof
  simp [reglan_equiv_def, re_lang_def, reglan_dot_def,
        smtstr_concat_def, smtstr_rep_def]
QED

Theorem reglan_equiv_loop_empty:
  hi < lo ==> reglan_equiv (reglan_loop r lo hi) reglan_none
Proof
  simp [reglan_equiv_def, re_lang_def, reglan_loop_lang_bounds] >>
  decide_tac
QED

Theorem smt_in_re_star_allchar:
  smt_in_re s (reglan_star reglan_allchar) <=> wfstr s
Proof
  simp [smt_in_re_def, re_lang_def, reglan_kstar_allchar]
QED

Theorem reglan_kstar_digit:
  reglan_kstar
    (\u. ?c. 48 <= c /\ c <= 57 /\ c <= 196607 /\ u = [c]) s <=>
  EVERY (\c. 48 <= c /\ c <= 57) s
Proof
  irule reglan_kstar_singleton_gen >>
  gen_tac >> eq_tac >> rw [] >> qexists `c` >> simp [] >> decide_tac
QED

Theorem smtstr_len_one_form:
  smtstr_len s = 1 ==> ?c. c <= 196607 /\ s = SmtStr [c]
Proof
  metis_tac [smt_in_re_allchar_len, smt_in_re_def]
QED

Theorem reglan_equiv_range_refl:
  smtstr_len s = 1 ==>
  reglan_equiv (reglan_range s s) (reglan_to_re s)
Proof
  strip_tac >> drule smtstr_len_one_form >> rw [] >>
  simp [reglan_equiv_def, re_lang_def, smtstr_rep_def] >>
  metis_tac [arithmeticTheory.LE_ANTISYM]
QED

Theorem reglan_equiv_range_non_singleton_left:
  smtstr_len s <> 1 ==>
  reglan_equiv (reglan_range s t) reglan_none
Proof
  simp [reglan_equiv_def, re_lang_def, smtstr_len_def,
        listTheory.LENGTH_EQ_1] >> metis_tac []
QED

Theorem reglan_equiv_range_non_singleton_right:
  smtstr_len t <> 1 ==>
  reglan_equiv (reglan_range s t) reglan_none
Proof
  simp [reglan_equiv_def, re_lang_def, smtstr_len_def,
        listTheory.LENGTH_EQ_1] >> metis_tac []
QED

Theorem smt_in_re_allchar_contains:
  smt_in_re t
    (reglan_concat
       (reglan_concat (reglan_star reglan_allchar) (reglan_to_re s))
       (reglan_star reglan_allchar)) <=>
  smtstr_contains t s
Proof
  simp [smt_in_re_def, re_lang_def, reglan_dot_def,
        reglan_kstar_allchar, wfstr_def, smtstr_contains_def,
        rich_listTheory.IS_SUBLIST_APPEND] >>
  eq_tac >> strip_tac >> fs []
  >- (qexistsl [`x`, `v`] >> simp []) >>
  `EVERY (\c. c <= 196607) (l ++ smtstr_rep s ++ l')` by
    (qpat_x_assum `smtstr_rep t = _` (SUBST1_TAC o SYM) >> simp []) >>
  qexistsl [`l ++ smtstr_rep s`, `l'`] >> simp [] >> fs []
QED

Theorem smt_in_re_plus_allchar:
  smt_in_re s (reglan_plus reglan_allchar) <=>
  wfstr s /\ s <> SmtStr []
Proof
  `EVERY (\c. c <= 196607) (smtstr_rep s)` by simp [] >>
  Cases_on `smtstr_rep s` >>
  fs [smt_in_re_def, re_lang_def, reglan_kstar_allchar,
      reglan_dot_def, GSYM smtstr_rep_eq_nil] >>
  qexistsl [`[h]`, `t`] >>
  simp []
QED

(* Derivatives of a bounded loop over a one-character language, for arbitrary
   bounds: consuming one character lowers both bounds by one.  The named
   instances below are corollaries. *)

Theorem re_deriv_loop_range:
  lo <= 196607 /\ hi <= 196607 ==>
  (smt_in_re s
      (re_deriv d
        (reglan_loop (reglan_range (SmtStr [lo]) (SmtStr [hi])) i n)) <=>
   n <> 0 /\ lo <= d /\ d <= hi /\
   smt_in_re s
     (reglan_loop (reglan_range (SmtStr [lo]) (SmtStr [hi]))
       (i - 1) (n - 1)))
Proof
  strip_tac >>
  simp [smt_in_re_rep, GSYM re_deriv_lang, re_lang_def,
        smtstr_rep_def] >>
  `(\x. ?c. lo <= c /\ c <= hi /\ c <= 196607 /\ x = [c]) =
   (\x. ?c. (lo <= c /\ c <= hi /\ c <= 196607) /\ x = [c])` by
    (rw [FUN_EQ_THM] >> metis_tac []) >>
  pop_assum (fn th => PURE_REWRITE_TAC [th]) >>
  simp [reglan_loop_lang_bounds, reglan_repeat_singletons] >>
  eq_tac >> rw [] >> decide_tac
QED

Theorem re_deriv_loop_singleton:
  c <= 196607 ==>
  (smt_in_re s (re_deriv d (reglan_loop (reglan_to_re (SmtStr [c])) i n)) <=>
   n <> 0 /\ d = c /\
   smt_in_re s (reglan_loop (reglan_to_re (SmtStr [c])) (i - 1) (n - 1)))
Proof
  strip_tac >>
  simp [smt_in_re_rep, GSYM re_deriv_lang, re_lang_def, smtstr_rep_def,
        reglan_loop_lang_singleton, REPLICATE_eq_cons] >>
  eq_tac >> rw []
  >- decide_tac
  >- (qexists `m` >> simp [])
  >> qexists `SUC j` >>
  simp [] >>
  qexists `j` >>
  simp []
QED

(* The nullable variant collapses the lower bound: once the body accepts the
   empty word every repetition count below the upper bound is reachable. *)

Theorem re_deriv_loop_nullable_singleton:
  c <= 196607 ==>
  (smt_in_re s
     (re_deriv d
       (reglan_loop
         (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
         i n)) <=>
   i <= n /\ n <> 0 /\ d = c /\
   smt_in_re s
     (reglan_loop
       (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
       0 (n - 1)))
Proof
  strip_tac >>
  simp [smt_in_re_rep, GSYM re_deriv_lang, re_lang_def, smtstr_rep_def,
        reglan_loop_lang_nullable_singleton, REPLICATE_eq_cons] >>
  eq_tac >> rw []
  >- decide_tac
  >- (qexists `m'` >> simp [])
  >> qexists `SUC m` >>
  simp [] >>
  qexists `m` >>
  simp []
QED

Theorem re_deriv_loop_singleton_1_3:
  c <= 196607 ==>
  (smt_in_re s
      (re_deriv d (reglan_loop (reglan_to_re (SmtStr [c])) 1 3)) <=>
   d = c /\ smt_in_re s (reglan_loop (reglan_to_re (SmtStr [c])) 0 2))
Proof
  rw [re_deriv_loop_singleton]
QED

Theorem re_deriv_loop_singleton_0_2:
  c <= 196607 ==>
  (smt_in_re s
      (re_deriv d (reglan_loop (reglan_to_re (SmtStr [c])) 0 2)) <=>
   d = c /\ smt_in_re s (reglan_loop (reglan_to_re (SmtStr [c])) 0 1))
Proof
  rw [re_deriv_loop_singleton]
QED

Theorem re_deriv_loop_singleton_0_1:
  c <= 196607 ==>
  (smt_in_re s
      (re_deriv d (reglan_loop (reglan_to_re (SmtStr [c])) 0 1)) <=>
   d = c /\ smt_in_re s (reglan_to_re (SmtStr [])))
Proof
  rw [re_deriv_loop_singleton, smt_in_re_loop_empty]
QED

Theorem re_deriv_loop_nullable_singleton_1_2:
  c <= 196607 ==>
  (smt_in_re s
      (re_deriv d
        (reglan_loop
          (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
          1 2)) <=>
   d = c /\
   smt_in_re s
     (reglan_loop
       (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
       0 1))
Proof
  rw [re_deriv_loop_nullable_singleton]
QED

Theorem re_deriv_loop_nullable_singleton_0_1:
  c <= 196607 ==>
  (smt_in_re s
      (re_deriv d
        (reglan_loop
          (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
          0 1)) <=>
   d = c /\ smt_in_re s (reglan_to_re (SmtStr [])))
Proof
  rw [re_deriv_loop_nullable_singleton, smt_in_re_loop_empty]
QED

Theorem smt_in_re_deriv[compute]:
  smt_in_re s r <=>
    re_nullable (FOLDL (\r c. re_deriv c r) r (smtstr_rep s))
Proof
  `!u r. re_lang r u <=>
         re_nullable (FOLDL (\r c. re_deriv c r) r u)` by
    (Induct >>
     simp [re_nullable_lang, re_deriv_lang]) >>
  simp [smt_in_re_rep]
QED

(* Leftmost string and regular-language replacement. *)

Definition smtstr_replace_raw_def:
  smtstr_replace_raw (s : num list) t u =
    case smtstr_indexof_aux t 0 s of
      NONE => s
    | SOME n =>
        TAKE n s ++ u ++ DROP (n + LENGTH t) s
End

Definition smtstr_replace_def:
  smtstr_replace s t u =
    SmtStr
      (smtstr_replace_raw
         (smtstr_rep s) (smtstr_rep t) (smtstr_rep u))
End

Theorem smtstr_indexof_aux_self[local]:
  !s n. smtstr_indexof_aux s n s = SOME n
Proof
  Cases >> simp [smtstr_indexof_aux_def,
                 rich_listTheory.IS_PREFIX_REFL]
QED

Theorem smtstr_indexof_aux_empty[local]:
  !s n. smtstr_indexof_aux [] n s = SOME n
Proof
  Cases >> simp [smtstr_indexof_aux_def,
                 rich_listTheory.IS_PREFIX_NIL]
QED

Theorem smtstr_indexof_aux_none[local]:
  !s t n. smtstr_indexof_aux t n s = NONE <=> ~IS_SUBLIST s t
Proof
  Induct
  >- simp [smtstr_indexof_aux_def,
           rich_listTheory.IS_SUBLIST_APPEND] >>
  Cases_on `t` >>
  simp [smtstr_indexof_aux_def, rich_listTheory.IS_SUBLIST] >>
  metis_tac []
QED

Theorem smtstr_indexof_aux_split[local]:
  !s t n k.
    smtstr_indexof_aux t n s = SOME k ==>
    ?pre post. s = pre ++ t ++ post /\ LENGTH pre + n = k
Proof
  Induct
  >- (simp [smtstr_indexof_aux_def] >> metis_tac []) >>
  rw [smtstr_indexof_aux_def] >>
  Cases_on `IS_PREFIX (h::s) t`
  >- (fs [rich_listTheory.IS_PREFIX_APPEND] >>
      qexistsl [`[]`, `l`] >> simp []) >>
  fs [] >>
  first_x_assum drule >>
  strip_tac >>
  qexistsl [`h::pre`, `post`] >>
  simp []
QED

Theorem smtstr_indexof_aux_prefix[local]:
  !t rest n. smtstr_indexof_aux t n (t ++ rest) = SOME n
Proof
  Cases >>
  simp [smtstr_indexof_aux_def, smtstr_indexof_aux_empty,
        rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem smtstr_indexof_oob:
  smtstr_len s < n ==> smtstr_indexof s t n = -1
Proof
  rw [smtstr_indexof_def, smtstr_len_def] >>
  intLib.ARITH_TAC
QED

Theorem smtstr_indexof_negative_start:
  n < 0 ==> smtstr_indexof s t n = -1
Proof
  simp [smtstr_indexof_def]
QED

Theorem smtstr_indexof_empty:
  smtstr_len e = 0 /\ 0 <= n /\ n <= smtstr_len s ==>
    smtstr_indexof s e n = n
Proof
  rw [smtstr_indexof_def, smtstr_len_def] >>
  fs [smtstr_rep_eq_nil, smtstr_indexof_aux_empty] >>
  intLib.ARITH_TAC
QED

Theorem drop_no_self_sublist[local]:
  0 < n /\ n <= LENGTH s ==> ~IS_SUBLIST (DROP n s) s
Proof
  rw [rich_listTheory.IS_SUBLIST_APPEND] >>
  CCONTR_TAC >>
  fs [] >>
  qpat_x_assum `DROP n s = _` (mp_tac o AP_TERM ``LENGTH``) >>
  simp []
QED

Theorem smtstr_indexof_self_zero[local]:
  smtstr_indexof s s 0 =
    smtstr_indexof (SmtStr []) (SmtStr []) 0
Proof
  rw [smtstr_indexof_def, smtstr_rep_def] >>
  simp [smtstr_indexof_aux_self, smtstr_indexof_aux_empty]
QED

Theorem smtstr_indexof_self_positive[local]:
  smtstr_indexof s s (&(SUC n)) =
    smtstr_indexof (SmtStr []) (SmtStr []) (&(SUC n))
Proof
  simp [smtstr_indexof_def, smtstr_rep_def] >>
  Cases_on `LENGTH (smtstr_rep s) < SUC n` >> simp [] >>
  `smtstr_indexof_aux (smtstr_rep s) (SUC n)
     (DROP (SUC n) (smtstr_rep s)) = NONE` by
    (rw [smtstr_indexof_aux_none] >>
     irule drop_no_self_sublist >> simp []) >>
  simp []
QED

Theorem smtstr_indexof_self:
  smtstr_indexof s s n =
    smtstr_indexof (SmtStr []) (SmtStr []) n
Proof
  Cases_on `n`
  >- (Cases_on `n'` >> fs [] >>
      ACCEPT_TAC smtstr_indexof_self_positive)
  >- simp [smtstr_indexof_negative_start]
  >- ACCEPT_TAC smtstr_indexof_self_zero
QED

Theorem smtstr_indexof_aux_pattern_length[local]:
  smtstr_indexof_aux t n s = SOME k ==> LENGTH t <= LENGTH s
Proof
  strip_tac >>
  drule smtstr_indexof_aux_split >>
  strip_tac >>
  fs []
QED

Theorem is_prefix_append_short[local]:
  IS_PREFIX (s ++ u) t /\ LENGTH t <= LENGTH s ==>
    IS_PREFIX s t
Proof
  metis_tac [rich_listTheory.IS_PREFIX_IMP_TAKE,
             rich_listTheory.IS_PREFIX_EQ_TAKE',
             listTheory.TAKE_APPEND1]
QED

Theorem is_prefix_append_right[local]:
  IS_PREFIX s t ==> IS_PREFIX (s ++ u) t
Proof
  rw [rich_listTheory.IS_PREFIX_APPEND] >>
  qexists `l ++ u` >>
  simp [listTheory.APPEND_ASSOC]
QED

Theorem smtstr_indexof_aux_append_some[local]:
  !s t n k u.
    smtstr_indexof_aux t n s = SOME k ==>
    smtstr_indexof_aux t n (s ++ u) = SOME k
Proof
  rpt gen_tac >>
  qid_spec_tac `n` >>
  Induct_on `s` >>
  rw [smtstr_indexof_aux_def]
  >- simp [smtstr_indexof_aux_empty]
  >- (`IS_PREFIX ((h::s) ++ u) t` by
        metis_tac [is_prefix_append_right] >>
      fs [])
  >- (`LENGTH t <= LENGTH s` by
        metis_tac [smtstr_indexof_aux_pattern_length] >>
      mp_tac (Q.INST
        [`s` |-> `h::s`, `u` |-> `u`, `t` |-> `t`]
        is_prefix_append_short) >>
      simp [])
QED

Theorem smtstr_rep_substr_suffix_inclusive[local]:
  0 <= n /\ n <= smtstr_len s ==>
    smtstr_rep (smtstr_substr s n (smtstr_len s)) =
    DROP (Num n) (smtstr_rep s)
Proof
  strip_tac >>
  `Num n <= LENGTH (smtstr_rep s)` by
    (fs [smtstr_len_def] >> intLib.ARITH_TAC) >>
  Cases_on `Num n = LENGTH (smtstr_rep s)`
  >- (fs [smtstr_len_def] >>
      simp [smtstr_rep_substr, smtstr_len_def]) >>
  `Num n < LENGTH (smtstr_rep s)` by decide_tac >>
  `~(n < 0)` by intLib.ARITH_TAC >>
  `smtstr_rep s <> []` by
    (Cases_on `smtstr_rep s` >> fs []) >>
  simp [smtstr_rep_substr, smtstr_len_def,
        listTheory.TAKE_LENGTH_TOO_LONG]
QED

Theorem smtstr_rep_substr_prefix_split[local]:
  smtstr_rep s = pre ++ rest ==>
  smtstr_rep (smtstr_substr s 0 (&(LENGTH pre))) = pre
Proof
  strip_tac >>
  Cases_on `pre` >>
  simp [smtstr_rep_substr, rich_listTheory.TAKE_LENGTH_APPEND]
QED

Theorem smtstr_rep_substr_suffix_split[local]:
  smtstr_rep s = pre ++ middle ++ post ==>
  smtstr_rep
    (smtstr_substr s (&(LENGTH pre + LENGTH middle))
      (smtstr_len s)) = post
Proof
  strip_tac >>
  Cases_on `pre` >> Cases_on `middle` >> Cases_on `post` >>
  fs [smtstr_rep_substr, smtstr_len_def,
      rich_listTheory.DROP_LENGTH_APPEND,
      listTheory.TAKE_LENGTH_TOO_LONG] >>
  ONCE_REWRITE_TAC [GSYM listTheory.APPEND_ASSOC] >>
  simp [rich_listTheory.DROP_LENGTH_APPEND,
        listTheory.DROP_APPEND1]
QED

Theorem smtstr_contains_substr_bounds[local]:
  0 < smtstr_len t /\
  smtstr_contains (smtstr_substr s n (smtstr_len s)) t ==>
  0 <= n /\ n < smtstr_len s
Proof
  strip_tac >>
  `smtstr_rep t <> []` by
    (Cases_on `smtstr_rep t` >> fs [smtstr_len_def]) >>
  Cases_on `n < 0`
  >- fs [smtstr_contains_def, smtstr_rep_substr,
         rich_listTheory.IS_SUBLIST_APPEND] >>
  Cases_on `smtstr_len s <= n`
  >- (`LENGTH (smtstr_rep s) <= Num n` by
        (fs [smtstr_len_def] >> intLib.ARITH_TAC) >>
      fs [smtstr_contains_def, smtstr_rep_substr,
          rich_listTheory.IS_SUBLIST_APPEND]) >>
  intLib.ARITH_TAC
QED

Theorem smtstr_indexof_suffix_equal:
  n <= smtstr_len s /\ n <= smtstr_len r /\
  smtstr_substr s n (smtstr_len s) =
    smtstr_substr r n (smtstr_len r) ==>
  smtstr_indexof s t n = smtstr_indexof r t n
Proof
  strip_tac >>
  Cases_on `n < 0`
  >- simp [smtstr_indexof_negative_start] >>
  `0 <= n` by intLib.ARITH_TAC >>
  `smtstr_rep (smtstr_substr s n (smtstr_len s)) =
   DROP (Num n) (smtstr_rep s)` by
    metis_tac [smtstr_rep_substr_suffix_inclusive] >>
  `smtstr_rep (smtstr_substr r n (smtstr_len r)) =
   DROP (Num n) (smtstr_rep r)` by
    metis_tac [smtstr_rep_substr_suffix_inclusive] >>
  `DROP (Num n) (smtstr_rep s) =
   DROP (Num n) (smtstr_rep r)` by metis_tac [] >>
  `~(n < 0)` by intLib.ARITH_TAC >>
  `~(LENGTH (smtstr_rep s) < Num n) /\
   ~(LENGTH (smtstr_rep r) < Num n)` by
    (fs [smtstr_len_def] >> intLib.ARITH_TAC) >>
  simp [smtstr_indexof_def]
QED

Theorem smtstr_indexof_no_contains:
  ~smtstr_contains (smtstr_substr s n (smtstr_len s)) t ==>
    smtstr_indexof s t n = -1
Proof
  strip_tac >>
  Cases_on `n < 0`
  >- simp [smtstr_indexof_negative_start] >>
  Cases_on `smtstr_len s < n`
  >- simp [smtstr_indexof_oob] >>
  `0 <= n /\ n <= smtstr_len s` by intLib.ARITH_TAC >>
  `~IS_SUBLIST (DROP (Num n) (smtstr_rep s))
      (smtstr_rep t)` by
    (fs [smtstr_contains_def,
         smtstr_rep_substr_suffix_inclusive]) >>
  `smtstr_indexof_aux (smtstr_rep t) (Num n)
      (DROP (Num n) (smtstr_rep s)) = NONE` by
    simp [smtstr_indexof_aux_none] >>
  `~(LENGTH (smtstr_rep s) < Num n)` by
    (fs [smtstr_len_def] >> intLib.ARITH_TAC) >>
  simp [smtstr_indexof_def]
QED

Theorem smtstr_indexof_concat_preserve:
  0 <= n /\ n <= smtstr_len s /\
  smtstr_contains (smtstr_substr s n (smtstr_len s)) t ==>
    smtstr_indexof (smtstr_concat s u) t n =
    smtstr_indexof s t n
Proof
  strip_tac >>
  `smtstr_rep (smtstr_substr s n (smtstr_len s)) =
   DROP (Num n) (smtstr_rep s)` by
    metis_tac [smtstr_rep_substr_suffix_inclusive] >>
  `IS_SUBLIST
      (smtstr_rep (smtstr_substr s n (smtstr_len s)))
      (smtstr_rep t)` by fs [smtstr_contains_def] >>
  `IS_SUBLIST (DROP (Num n) (smtstr_rep s))
      (smtstr_rep t)` by metis_tac [] >>
  `?k. smtstr_indexof_aux (smtstr_rep t) (Num n)
       (DROP (Num n) (smtstr_rep s)) = SOME k` by
    (Cases_on `smtstr_indexof_aux (smtstr_rep t) (Num n)
       (DROP (Num n) (smtstr_rep s))` >>
     fs [smtstr_indexof_aux_none]) >>
  `Num n <= LENGTH (smtstr_rep s)` by
    (fs [smtstr_len_def] >> intLib.ARITH_TAC) >>
  `DROP (Num n) (smtstr_rep (smtstr_concat s u)) =
   DROP (Num n) (smtstr_rep s) ++ smtstr_rep u` by
    simp [listTheory.DROP_APPEND1] >>
  `smtstr_indexof_aux (smtstr_rep t) (Num n)
      (DROP (Num n) (smtstr_rep (smtstr_concat s u))) = SOME k` by
    metis_tac [smtstr_indexof_aux_append_some] >>
  `~(n < 0)` by intLib.ARITH_TAC >>
  `~(LENGTH (smtstr_rep s) < Num n) /\
   ~(LENGTH (smtstr_rep (smtstr_concat s u)) < Num n)` by
    (simp [] >> decide_tac) >>
  simp [smtstr_indexof_def]
QED

Theorem smtstr_indexof_concat_contains:
  0 < smtstr_len t /\
  smtstr_contains (smtstr_substr s n (smtstr_len s)) t ==>
  smtstr_indexof (smtstr_concat s u) t n =
    smtstr_indexof s t n
Proof
  strip_tac >>
  `0 <= n /\ n < smtstr_len s` by
    metis_tac [smtstr_contains_substr_bounds] >>
  irule smtstr_indexof_concat_preserve >>
  simp []
QED

Theorem smtstr_rep_substr_full[local]:
  smtstr_rep (smtstr_substr s 0 (smtstr_len s)) = smtstr_rep s
Proof
  Cases_on `smtstr_rep s` >>
  simp [smtstr_rep_substr, smtstr_len_def,
        listTheory.TAKE_LENGTH_TOO_LONG]
QED

Theorem smtstr_indexof_zero_nonnegative:
  (0 <= smtstr_indexof s t 0 <=> smtstr_contains s t)
Proof
  rw [smtstr_indexof_def, smtstr_contains_def] >>
  eq_tac
  >- (Cases_on
        `smtstr_indexof_aux (smtstr_rep t) 0 (smtstr_rep s)` >>
      simp [] >>
      drule smtstr_indexof_aux_split >>
      strip_tac >>
      rw [rich_listTheory.IS_SUBLIST_APPEND] >>
      qexistsl [`pre`, `post`] >>
      simp [])
  >- (strip_tac >>
      Cases_on
        `smtstr_indexof_aux (smtstr_rep t) 0 (smtstr_rep s)` >>
      fs [smtstr_indexof_aux_none])
QED

Theorem smtstr_indexof_concat_occurrence:
  smtstr_indexof
      (smtstr_concat (smtstr_concat pre t) u) t 0 =
    smtstr_indexof (smtstr_concat pre t) t 0
Proof
  irule smtstr_indexof_concat_preserve >>
  conj_tac
  >- simp [smtstr_len_def] >>
  conj_tac
  >- simp [] >>
  simp [smtstr_contains_def, smtstr_rep_substr_full,
        rich_listTheory.IS_SUBLIST_APPEND] >>
  qexistsl [`smtstr_rep pre`, `[]`] >>
  simp []
QED

Theorem smtstr_indexof_concat_occurrence_right:
  smtstr_indexof (smtstr_concat pre (smtstr_concat t u)) t 0 =
    smtstr_indexof (smtstr_concat pre t) t 0
Proof
  `smtstr_concat pre (smtstr_concat t u) =
   smtstr_concat (smtstr_concat pre t) u` by
    simp [smtstr_concat_def, listTheory.APPEND_ASSOC] >>
  metis_tac [smtstr_indexof_concat_occurrence]
QED

Theorem take_splice[local]:
  !pre t post. TAKE (LENGTH pre) (pre ++ t ++ post) = pre
Proof
  Induct >> simp []
QED

Theorem drop_splice[local]:
  !pre t post.
    DROP (LENGTH pre + LENGTH t) (pre ++ t ++ post) = post
Proof
  metis_tac [listTheory.LENGTH_APPEND, listTheory.APPEND_ASSOC,
             rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem replace_splice_identity[local]:
  TAKE (LENGTH pre) (pre ++ t ++ post) ++ t ++
  DROP (LENGTH pre + LENGTH t) (pre ++ t ++ post) =
  pre ++ t ++ post
Proof
  simp [take_splice, drop_splice]
QED

Theorem smtstr_replace_raw_id[local]:
  smtstr_replace_raw s t t = s
Proof
  rw [smtstr_replace_raw_def] >>
  Cases_on `smtstr_indexof_aux t 0 s` >> simp [] >>
  drule smtstr_indexof_aux_split >>
  strip_tac >>
  qpat_x_assum `LENGTH pre + 0 = x` (SUBST_ALL_TAC o SYM) >>
  simp [replace_splice_identity]
QED

Theorem smtstr_replace_raw_absent[local]:
  ~IS_SUBLIST s t ==> smtstr_replace_raw s t u = s
Proof
  strip_tac >>
  `smtstr_indexof_aux t 0 s = NONE` by
    metis_tac [smtstr_indexof_aux_none] >>
  simp [smtstr_replace_raw_def]
QED

Theorem smtstr_replace_raw_hit[local]:
  IS_SUBLIST s t ==>
  ?pre post.
    s = pre ++ t ++ post /\
    smtstr_replace_raw s t u = pre ++ u ++ post
Proof
  strip_tac >>
  Cases_on `smtstr_indexof_aux t 0 s` >>
  fs [smtstr_indexof_aux_none] >>
  drule smtstr_indexof_aux_split >>
  strip_tac >>
  qpat_x_assum `LENGTH pre + 0 = x` (SUBST_ALL_TAC o SYM) >>
  qexistsl [`pre`, `post`] >>
  simp [smtstr_replace_raw_def, take_splice, drop_splice]
QED

Theorem smtstr_replace_raw_bound[local]:
  EVERY P s /\ EVERY P u ==>
  EVERY P (smtstr_replace_raw s t u)
Proof
  rw [smtstr_replace_raw_def] >>
  BasicProvers.every_case_tac >>
  simp [rich_listTheory.EVERY_TAKE,
        rich_listTheory.EVERY_DROP]
QED

Theorem smtstr_rep_replace[simp]:
  smtstr_rep (smtstr_replace s t u) =
  smtstr_replace_raw
    (smtstr_rep s) (smtstr_rep t) (smtstr_rep u)
Proof
  simp [smtstr_replace_def, smtstr_rep_def,
        smtstr_replace_raw_bound]
QED

Theorem smtstr_replace_contains_replacement:
  smtstr_contains (smtstr_replace s t u) u <=>
  smtstr_contains s t \/ smtstr_contains s u
Proof
  rw [smtstr_contains_def, smtstr_rep_replace] >>
  Cases_on `IS_SUBLIST (smtstr_rep s) (smtstr_rep t)`
  >- (drule_then
        (qspec_then `smtstr_rep u` strip_assume_tac)
        smtstr_replace_raw_hit >>
      rw [] >>
      rw [rich_listTheory.IS_SUBLIST_APPEND] >>
      qexistsl [`pre`, `post`] >> simp []) >>
  simp [smtstr_replace_raw_absent]
QED

Theorem smtstr_replace_self:
  smtstr_replace t t s = s
Proof
  irule (iffLR smtstr_rep_11) >>
  PURE_REWRITE_TAC [smtstr_replace_def, smtstr_replace_raw_def] >>
  simp [smtstr_indexof_aux_self]
QED

Theorem smtstr_replace_empty:
  smtstr_replace t (SmtStr []) s = smtstr_concat s t
Proof
  irule (iffLR smtstr_rep_11) >>
  PURE_REWRITE_TAC
    [smtstr_replace_def, smtstr_replace_raw_def,
     smtstr_concat_def] >>
  simp [smtstr_indexof_aux_empty, smtstr_rep_def]
QED

Theorem smtstr_replace_id:
  smtstr_replace t s s = t
Proof
  irule (iffLR smtstr_rep_11) >>
  PURE_REWRITE_TAC [smtstr_replace_def] >>
  simp [smtstr_replace_raw_id]
QED

Theorem smtstr_replace_absent:
  ~smtstr_contains t s ==> smtstr_replace t s r = t
Proof
  strip_tac >>
  fs [smtstr_contains_def] >>
  irule (iffLR smtstr_rep_11) >>
  PURE_REWRITE_TAC [smtstr_replace_def] >>
  simp [smtstr_replace_raw_absent]
QED

Theorem smtstr_replace_prefix:
  smtstr_replace (smtstr_concat t rest) t r =
  smtstr_concat r rest
Proof
  irule (iffLR smtstr_rep_11) >>
  PURE_REWRITE_TAC
    [smtstr_replace_def, smtstr_replace_raw_def,
     smtstr_concat_def] >>
  simp [smtstr_indexof_aux_prefix,
        rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem smtstr_replace_raw_append_some[local]:
  smtstr_indexof_aux t 0 s = SOME n ==>
  smtstr_replace_raw (s ++ u) t r =
  smtstr_replace_raw s t r ++ u
Proof
  strip_tac >>
  `n + LENGTH t <= LENGTH s` by
    (drule smtstr_indexof_aux_split >> strip_tac >> fs []) >>
  `smtstr_indexof_aux t 0 (s ++ u) = SOME n` by
    metis_tac [smtstr_indexof_aux_append_some] >>
  asm_rewrite_tac [smtstr_replace_raw_def] >>
  simp [listTheory.TAKE_APPEND1, listTheory.DROP_APPEND1,
        listTheory.APPEND_ASSOC]
QED

Theorem smtstr_replace_concat_after_match:
  smtstr_contains s t ==>
  smtstr_replace (smtstr_concat s u) t r =
  smtstr_concat (smtstr_replace s t r) u
Proof
  strip_tac >>
  Cases_on `smtstr_indexof_aux (smtstr_rep t) 0 (smtstr_rep s)`
  >- fs [smtstr_contains_def, smtstr_indexof_aux_none] >>
  irule (iffLR smtstr_rep_11) >>
  PURE_REWRITE_TAC [smtstr_rep_replace, smtstr_rep_concat] >>
  metis_tac [smtstr_replace_raw_append_some]
QED

Definition smtstr_replace_all_aux_def:
  (smtstr_replace_all_aux 0 (s : num list) t u = s) /\
  (smtstr_replace_all_aux (SUC fuel) [] t u = []) /\
  (smtstr_replace_all_aux (SUC fuel) (h::s) t u =
     if IS_PREFIX (h::s) t then
       u ++ smtstr_replace_all_aux fuel
         (DROP (LENGTH t) (h::s)) t u
     else h::smtstr_replace_all_aux fuel s t u)
End

Definition smtstr_replace_all_def:
  smtstr_replace_all s t u =
    if smtstr_rep t = [] then s
    else
      SmtStr
        (smtstr_replace_all_aux (LENGTH (smtstr_rep s))
           (smtstr_rep s) (smtstr_rep t) (smtstr_rep u))
End

Theorem smtstr_replace_all_empty:
  smtstr_len t = 0 ==> smtstr_replace_all s t u = s
Proof
  strip_tac >>
  `smtstr_rep t = []` by
    (Cases_on `smtstr_rep t` >> fs [smtstr_len_def]) >>
  simp [smtstr_replace_all_def]
QED

Theorem smtstr_replace_all_aux_nil[local]:
  !fuel t u. smtstr_replace_all_aux fuel [] t u = []
Proof
  Cases >> simp [smtstr_replace_all_aux_def]
QED

Theorem smtstr_replace_all_self:
  smtstr_len s <> 0 ==> smtstr_replace_all s s u = u
Proof
  strip_tac >>
  irule (iffLR smtstr_rep_11) >>
  Cases_on `smtstr_rep s` >>
  fs [smtstr_len_def] >>
  simp [smtstr_replace_all_def, smtstr_replace_all_aux_def,
        smtstr_replace_all_aux_nil,
        rich_listTheory.IS_PREFIX_REFL]
QED

Theorem smtstr_replace_all_aux_absent[local]:
  !s t u. ~IS_SUBLIST s t ==>
    smtstr_replace_all_aux (LENGTH s) s t u = s
Proof
  Induct
  >- simp [smtstr_replace_all_aux_def] >>
  rpt gen_tac >>
  strip_tac >>
  `smtstr_indexof_aux t 0 (h::s) = NONE` by
    simp [smtstr_indexof_aux_none] >>
  fs [smtstr_indexof_aux_def] >>
  `~IS_SUBLIST s t` by
    metis_tac [smtstr_indexof_aux_none] >>
  simp [smtstr_replace_all_aux_def] >>
  first_x_assum irule
QED

Theorem smtstr_replace_all_aux_id[local]:
  !fuel s t. LENGTH s <= fuel /\ t <> [] ==>
    smtstr_replace_all_aux fuel s t t = s
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      `s = []` by (Cases_on `s` >> fs []) >>
      simp [smtstr_replace_all_aux_def]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `s`
  >- simp [smtstr_replace_all_aux_def] >>
  rw [smtstr_replace_all_aux_def]
  >- (`LENGTH (DROP (LENGTH t) (h::t')) <= fuel` by
        (simp [listTheory.LENGTH_DROP] >>
         Cases_on `t` >> fs [] >> decide_tac) >>
      `smtstr_replace_all_aux fuel
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

Theorem smtstr_replace_all_absent:
  ~smtstr_contains s t ==> smtstr_replace_all s t u = s
Proof
  strip_tac >>
  fs [smtstr_contains_def] >>
  rw [smtstr_replace_all_def] >>
  irule (iffLR smtstr_rep_11) >>
  simp [smtstr_replace_all_aux_absent]
QED

Theorem smtstr_replace_all_id:
  smtstr_replace_all s t t = s
Proof
  rw [smtstr_replace_all_def] >>
  irule (iffLR smtstr_rep_11) >>
  simp [smtstr_replace_all_aux_id]
QED

Definition smtstr_shortest_re_aux_def:
  (smtstr_shortest_re_aux r s n 0 =
     if smt_in_re (SmtStr (TAKE n s)) r then SOME n else NONE) /\
  (smtstr_shortest_re_aux r s n (SUC k) =
     if smt_in_re (SmtStr (TAKE n s)) r then SOME n
     else smtstr_shortest_re_aux r s (SUC n) k)
End

Definition smtstr_shortest_re_def:
  smtstr_shortest_re allow_empty r (s : num list) =
    if allow_empty then
      smtstr_shortest_re_aux r s 0 (LENGTH s)
    else
      case s of
        [] => NONE
      | h::t => smtstr_shortest_re_aux r s 1 (LENGTH t)
End

Definition smtstr_find_re_aux_def:
  (smtstr_find_re_aux allow_empty r n ([] : num list) =
     case smtstr_shortest_re allow_empty r [] of
       NONE => NONE
     | SOME m => SOME (n, m)) /\
  (smtstr_find_re_aux allow_empty r n (h::s) =
     case smtstr_shortest_re allow_empty r (h::s) of
       NONE => smtstr_find_re_aux allow_empty r (SUC n) s
     | SOME m => SOME (n, m))
End

Definition smtstr_find_re_def:
  smtstr_find_re allow_empty r s =
    smtstr_find_re_aux allow_empty r 0 s
End

Definition smtstr_replace_re_raw_def:
  smtstr_replace_re_raw (s : num list) r u =
    case smtstr_find_re T r s of
      NONE => s
    | SOME (i, n) => TAKE i s ++ u ++ DROP (i + n) s
End

Definition smtstr_replace_re_def:
  smtstr_replace_re s r u =
    SmtStr
      (smtstr_replace_re_raw
         (smtstr_rep s) r (smtstr_rep u))
End

Theorem smtstr_shortest_re_none[local]:
  !fuel s n. smtstr_shortest_re_aux reglan_none s n fuel = NONE
Proof
  Induct >> simp [smtstr_shortest_re_aux_def, smt_in_re_def]
QED

Theorem smtstr_find_re_none[local]:
  !s n. smtstr_find_re_aux allow_empty reglan_none n s = NONE
Proof
  Induct >>
  simp [smtstr_find_re_aux_def, smtstr_shortest_re_def,
        smtstr_shortest_re_none]
QED

Theorem smtstr_replace_re_none:
  smtstr_replace_re s reglan_none u = s
Proof
  irule (iffLR smtstr_rep_11) >>
  PURE_REWRITE_TAC
    [smtstr_replace_re_def, smtstr_replace_re_raw_def,
     smtstr_find_re_def] >>
  simp [smtstr_find_re_none]
QED

Theorem smtstr_shortest_re_aux_lower:
  smtstr_shortest_re_aux r s n k = SOME m ==> n <= m
Proof
  qid_spec_tac `n` >>
  Induct_on `k` >>
  simp [smtstr_shortest_re_aux_def] >>
  rw [] >>
  res_tac >>
  decide_tac
QED

Theorem smtstr_shortest_re_nonempty:
  smtstr_shortest_re F r s = SOME n ==> 0 < n
Proof
  Cases_on `s` >>
  simp [smtstr_shortest_re_def] >>
  strip_tac >>
  drule smtstr_shortest_re_aux_lower >>
  decide_tac
QED

Theorem smtstr_find_re_aux_nonempty:
  smtstr_find_re_aux F r i s = SOME (j, n) ==> 0 < n
Proof
  qid_spec_tac `i` >>
  Induct_on `s` >>
  rw [smtstr_find_re_aux_def] >>
  BasicProvers.every_case_tac >>
  fs [] >>
  metis_tac [smtstr_shortest_re_nonempty]
QED

Theorem smtstr_find_re_nonempty:
  smtstr_find_re F r s = SOME (i, n) ==> 0 < n
Proof
  metis_tac [smtstr_find_re_def, smtstr_find_re_aux_nonempty]
QED

Definition smtstr_replace_re_all_aux_def:
  (smtstr_replace_re_all_aux 0 (s : num list) r u = s) /\
  (smtstr_replace_re_all_aux (SUC fuel) s r u =
    case smtstr_find_re F r s of
      NONE => s
    | SOME (i, n) =>
        TAKE i s ++ u ++
        smtstr_replace_re_all_aux fuel (DROP (i + n) s) r u)
End

Definition smtstr_replace_re_all_def:
  smtstr_replace_re_all s r u =
    SmtStr
      (smtstr_replace_re_all_aux (LENGTH (smtstr_rep s))
         (smtstr_rep s) r (smtstr_rep u))
End

Theorem smtstr_replace_re_all_none:
  smtstr_replace_re_all s reglan_none u = s
Proof
  qspec_then `s` strip_assume_tac ranged_smtstr_nchotomy >>
  Cases_on `LENGTH l` >>
  simp [smtstr_replace_re_all_def, smtstr_replace_re_all_aux_def,
        smtstr_find_re_def, smtstr_find_re_none]
QED

(* SMT-LIB character and decimal conversions. *)

Definition smtstr_is_digit_def:
  smtstr_is_digit s <=>
    ?c. smtstr_rep s = [c] /\ 48 <= c /\ c <= 57
End

Definition smtstr_to_code_def:
  smtstr_to_code s =
    case smtstr_rep s of
      [c] => &c
    | _ => -1
End

(* This is cvc5's STRING_EAGER_REDUCTION predicate for [str.to_code].
   Keeping the statement independent of parser skolems makes the replay
   adapter applicable to every string term, including components introduced
   by regular-expression unfolding. *)
Theorem smtstr_to_code_eager_reduction:
  if smtstr_len s = 1 then
    0 <= smtstr_to_code s /\ smtstr_to_code s < 196608
  else
    smtstr_to_code s = -1
Proof
  qspec_then `s` strip_assume_tac ranged_smtstr_nchotomy >>
  gvs [smtstr_len_def, smtstr_to_code_def, smtstr_rep_def] >>
  Cases_on `l` >> gvs [] >>
  Cases_on `t` >> gvs [] >>
  Cases_on `t'` >> gvs []
QED

Theorem reglan_equiv_range_empty:
  smtstr_len s = 1 /\ smtstr_len t = 1 /\
  smtstr_to_code t < smtstr_to_code s ==>
  reglan_equiv (reglan_range s t) reglan_none
Proof
  strip_tac >>
  qpat_x_assum `smtstr_len s = 1`
    (strip_assume_tac o MATCH_MP smtstr_len_one_form) >>
  qpat_x_assum `smtstr_len t = 1`
    (strip_assume_tac o MATCH_MP smtstr_len_one_form) >>
  fs [reglan_equiv_def, re_lang_def, smtstr_to_code_def,
      smtstr_rep_def] >> decide_tac
QED

Theorem num_not_le_neg_one[local]:
  !n. ~((&n : int) <= -1)
Proof
  intLib.ARITH_TAC
QED

Theorem smt_in_re_range_elim:
  smtstr_len lo = 1 /\ smtstr_len hi = 1 ==>
  (smt_in_re s (reglan_range lo hi) <=>
   smtstr_to_code lo <= smtstr_to_code s /\
   smtstr_to_code s <= smtstr_to_code hi)
Proof
  strip_tac >>
  qpat_x_assum `smtstr_len lo = 1`
    (strip_assume_tac o MATCH_MP smtstr_len_one_form) >>
  qpat_x_assum `smtstr_len hi = 1`
    (strip_assume_tac o MATCH_MP smtstr_len_one_form) >>
  gvs [] >>
  eq_tac
  >- (strip_tac >> fs [smt_in_re_def, smtstr_to_code_def]) >>
  qspec_then `s` strip_assume_tac ranged_smtstr_nchotomy >>
  gvs [] >>
  rename1 `EVERY (\c. c <= 196607) chars` >>
  Cases_on `chars`
  >- (strip_tac >>
      gvs [smtstr_to_code_def, smtstr_rep_def] >>
      metis_tac [num_not_le_neg_one]) >>
  Cases_on `t`
  >- (strip_tac >>
      gvs [smt_in_re_def, smtstr_to_code_def, smtstr_rep_def] >>
      qexists_tac `h` >> simp [] >> decide_tac) >>
  Cases_on `t'` >> strip_tac >>
  gvs [smtstr_to_code_def, smtstr_rep_def] >>
  metis_tac [num_not_le_neg_one]
QED

Theorem smtstr_is_digit_elim:
  smtstr_is_digit s <=>
  48 <= smtstr_to_code s /\ smtstr_to_code s <= 57
Proof
  qspec_then `s` strip_assume_tac ranged_smtstr_nchotomy >>
  gvs [] >>
  rename1 `EVERY (\c. c <= 196607) chars` >>
  Cases_on `chars` >>
  gvs [smtstr_is_digit_def, smtstr_to_code_def, smtstr_rep_def] >>
  Cases_on `t` >>
  gvs [smtstr_is_digit_def, smtstr_to_code_def, smtstr_rep_def] >>
  Cases_on `t'` >>
  gvs [smtstr_is_digit_def, smtstr_to_code_def, smtstr_rep_def]
QED

Definition smtstr_from_code_def:
  smtstr_from_code (n : int) =
    if n < 0 \/ 196607 < Num n then SmtStr []
    else SmtStr [Num n]
End

Definition smtstr_digits_def:
  smtstr_digits s <=>
    EVERY (\c. 48 <= c /\ c <= 57) (smtstr_rep s)
End

Theorem smt_in_re_star_digit:
  smt_in_re s
    (reglan_star (reglan_range (SmtStr [48]) (SmtStr [57]))) <=>
  smtstr_digits s
Proof
  simp [smt_in_re_def, re_lang_def, reglan_kstar_digit,
        smtstr_digits_def, smtstr_rep_def]
QED

Theorem smt_in_re_plus_digit:
  smt_in_re s
    (reglan_concat
       (reglan_range (SmtStr [48]) (SmtStr [57]))
       (reglan_star (reglan_range (SmtStr [48]) (SmtStr [57])))) <=>
  s <> SmtStr [] /\ smtstr_digits s
Proof
  simp [smt_in_re_def, re_lang_def, reglan_dot_def,
        reglan_kstar_digit, smtstr_digits_def, smtstr_rep_def,
        smtstr_rep_eq_nil] >>
  Cases_on `smtstr_rep s`
  >- fs [smtstr_rep_eq_nil] >>
  `s <> SmtStr []` by (strip_tac >> fs [smtstr_rep_def]) >>
  eq_tac >> strip_tac >> fs []
  >- (qpat_x_assum `u = [c]` SUBST_ALL_TAC >> fs []) >>
  qexists `[h]` >> qexists `t` >> simp [] >> decide_tac
QED

Definition smtstr_to_int_def:
  smtstr_to_int s =
    if s = SmtStr [] \/ ~smtstr_digits s then -1
    else
      &ASCIInumbers$num_from_dec_string (MAP CHR (smtstr_rep s))
End

Definition smtstr_from_int_def:
  smtstr_from_int (n : int) =
    if n < 0 then SmtStr []
    else
      SmtStr (MAP ORD (ASCIInumbers$num_to_dec_string (Num n)))
End

(* Public computation equations. *)

(* 'smtstr_to_code_def' and 'smtstr_digits_def' are directly executable, so
   they serve as their own compute rules; 'smtstr_is_digit_def' is stated
   with an existential and needs the case-split form below. *)

Theorem smtstr_is_digit_compute[compute]:
  smtstr_is_digit s <=>
    case smtstr_rep s of
      [c] => 48 <= c /\ c <= 57
    | _ => F
Proof
  simp [smtstr_is_digit_def] >>
  Cases_on `smtstr_rep s` >>
  simp [] >>
  Cases_on `t` >>
  simp []
QED

(* The ASCIInumbers bridge and SMT-LIB's divergent error cases. *)

Theorem smtstr_to_int_ascii:
  s <> SmtStr [] /\ smtstr_digits s ==>
  smtstr_to_int s =
    &ASCIInumbers$num_from_dec_string (MAP CHR (smtstr_rep s))
Proof
  simp [smtstr_to_int_def]
QED

Theorem smtstr_to_int_empty:
  smtstr_to_int (SmtStr []) = -1
Proof
  simp [smtstr_to_int_def]
QED

Theorem smtstr_to_int_nondigit:
  ~smtstr_digits s ==> smtstr_to_int s = -1
Proof
  simp [smtstr_to_int_def]
QED

Theorem smtstr_to_int_neg_one_nonempty:
  s <> SmtStr [] /\ smtstr_to_int s = -1 ==>
  ~smtstr_digits s
Proof
  rw [smtstr_to_int_def] >>
  intLib.ARITH_TAC
QED

Theorem smtstr_to_int_concat_nondigit:
  s <> SmtStr [] /\ smtstr_to_int s = -1 ==>
  smtstr_to_int
    (smtstr_concat left (smtstr_concat s right)) = -1
Proof
  strip_tac >>
  `~smtstr_digits s` by
    metis_tac [smtstr_to_int_neg_one_nonempty] >>
  `~smtstr_digits
      (smtstr_concat left (smtstr_concat s right))` by
    fs [smtstr_digits_def, smtstr_concat_def, smtstr_rep_def] >>
  metis_tac [smtstr_to_int_nondigit]
QED

Theorem smtstr_from_int_ascii:
  0 <= n ==>
  smtstr_from_int n =
    SmtStr (MAP ORD (ASCIInumbers$num_to_dec_string (Num n)))
Proof
  strip_tac >>
  `~(n < 0)` by intLib.ARITH_TAC >>
  simp [smtstr_from_int_def]
QED

Theorem smtstr_from_int_negative:
  n < 0 ==> smtstr_from_int n = SmtStr []
Proof
  simp [smtstr_from_int_def, smtstr_rep_def]
QED

Theorem smtstr_digits_num_to_dec_string:
  smtstr_digits
    (SmtStr (MAP ORD (ASCIInumbers$num_to_dec_string n)))
Proof
  rw [smtstr_digits_def, smtstr_rep_def,
      listTheory.EVERY_MAP] >>
  mp_tac
    (ASCIInumbersTheory.EVERY_isDigit_num_to_dec_string
       |> Q.SPEC `n`) >>
  simp [listTheory.EVERY_MEM, stringTheory.isDigit_def]
QED

Theorem smtstr_from_int_nonempty:
  0 <= n ==> smtstr_from_int n <> SmtStr []
Proof
  strip_tac >>
  `~(n < 0)` by intLib.ARITH_TAC >>
  simp [smtstr_from_int_def, smtstr_eq_SmtStr,
        ASCIInumbersTheory.num_to_dec_string_nil]
QED

Theorem smtstr_from_int_digits:
  smtstr_digits (smtstr_from_int n)
Proof
  Cases_on `n < 0`
  >- simp [smtstr_from_int_negative, smtstr_digits_def,
           smtstr_rep_def] >>
  `0 <= n` by intLib.ARITH_TAC >>
  simp [smtstr_from_int_ascii, smtstr_digits_num_to_dec_string]
QED

Theorem smtstr_contains_preserves_digits:
  smtstr_digits source /\ smtstr_contains source sub ==>
  smtstr_digits sub
Proof
  rw [smtstr_digits_def, smtstr_contains_def,
      rich_listTheory.IS_SUBLIST_APPEND] >>
  fs []
QED

Theorem smtstr_from_int_no_nondigit_substring:
  s <> SmtStr [] /\ smtstr_to_int s = -1 ==>
  ~smtstr_contains (smtstr_from_int n) s
Proof
  strip_tac >>
  `~smtstr_digits s` by
    metis_tac [smtstr_to_int_neg_one_nonempty] >>
  Cases_on `n < 0`
  >- fs [smtstr_from_int_negative, smtstr_contains_def,
         smtstr_rep_def, rich_listTheory.IS_SUBLIST_APPEND,
         smtstr_rep_eq_nil] >>
  `0 <= n` by intLib.ARITH_TAC >>
  `smtstr_digits (smtstr_from_int n)` by
    simp [smtstr_from_int_ascii, smtstr_digits_num_to_dec_string] >>
  metis_tac [smtstr_contains_preserves_digits]
QED

Theorem smtstr_to_int_from_int:
  0 <= n ==> smtstr_to_int (smtstr_from_int n) = n
Proof
  strip_tac >>
  `smtstr_from_int n =
     SmtStr (MAP ORD (ASCIInumbers$num_to_dec_string (Num n)))` by
    metis_tac [smtstr_from_int_ascii] >>
  `smtstr_digits (smtstr_from_int n)` by
    simp [smtstr_digits_num_to_dec_string] >>
  `smtstr_from_int n <> SmtStr []` by
    metis_tac [smtstr_from_int_nonempty] >>
  simp [smtstr_to_int_def, smtstr_rep_def,
        listTheory.MAP_MAP_o,
        combinTheory.o_DEF, ASCIInumbersTheory.toNum_toString,
        integerTheory.INT_OF_NUM]
QED

(* Replay algebra.  The TASK_02 draft_length recording rewrites "abc" to a
   seq.unit/Char chain and uses concat unit, associativity, and length. *)

Theorem smtstr_concat_assoc:
  smtstr_concat (smtstr_concat s t) u =
    smtstr_concat s (smtstr_concat t u)
Proof
  simp [smtstr_concat_def, smtstr_rep_def,
        listTheory.APPEND_ASSOC]
QED

Theorem smtstr_concat_nil_left:
  smtstr_concat (SmtStr []) s = s
Proof
  Cases_on `s` >>
  simp [smtstr_concat_def, smtstr_rep_def]
QED

Theorem smtstr_concat_nil_right:
  smtstr_concat s (SmtStr []) = s
Proof
  Cases_on `s` >>
  simp [smtstr_concat_def, smtstr_rep_def]
QED

(* TASK_02 draft_regex_membership compares a concat with a singleton and
   concludes that the distinguished middle character is that singleton. *)

Theorem smtstr_concat_middle_singleton:
  c <= 196607 /\ d <= 196607 /\
  smtstr_concat p (smtstr_concat (SmtStr [c]) q) = SmtStr [d] ==>
  c = d
Proof
  rpt strip_tac >>
  `smtstr_rep p ++ [c] ++ smtstr_rep q = [d]` by
    (pop_assum mp_tac >>
     simp [smtstr_concat_def, smtstr_rep_def, SmtStr_11]) >>
  Cases_on `smtstr_rep p` >>
  fs []
QED

Theorem smtstr_singleton_concat_middle:
  c <= 196607 /\ d <= 196607 /\
  SmtStr [d] = smtstr_concat p (smtstr_concat (SmtStr [c]) q) ==>
  d = c
Proof
  metis_tac [smtstr_concat_middle_singleton]
QED

Theorem smtstr_len_concat:
  smtstr_len (smtstr_concat s t) =
    smtstr_len s + smtstr_len t
Proof
  simp [smtstr_concat_def, smtstr_len_def,
        smtstr_rep_def,
        integerTheory.INT_OF_NUM_ADD]
QED

Theorem smtstr_len_concat_rec:
  smtstr_len (smtstr_concat (smtstr_concat s t) u) =
    smtstr_len s + smtstr_len (smtstr_concat t u)
Proof
  simp [smtstr_len_concat, integerTheory.INT_ADD_ASSOC]
QED

(* TASK_02 draft_regex_membership, draft_substr, and draft_re_comp use
   zero length as the empty-string branch of their sequence clauses. *)

Theorem smtstr_len_nonnegative:
  0 <= smtstr_len s
Proof
  simp [smtstr_len_def, smtstr_rep_def]
QED

Theorem smtstr_len_eq_zero:
  smtstr_len s = 0 <=> s = SmtStr []
Proof
  simp [smtstr_len_def, smtstr_rep_eq_nil]
QED

Theorem smtstr_length_positive_split:
  (smtstr_len s = 0 /\ s = SmtStr []) \/ 0 < smtstr_len s
Proof
  rw [smtstr_len_def] >>
  Cases_on `LENGTH (smtstr_rep s) = 0` >>
  fs [smtstr_rep_eq_nil, arithmeticTheory.NOT_ZERO_LT_ZERO]
QED

Theorem smtstr_substr_full_bound:
  smtstr_len s <= n ==> smtstr_substr s 0 n = s
Proof
  strip_tac >>
  Cases_on `s = SmtStr []`
  >- simp [smtstr_substr_def] >>
  `smtstr_len s <> 0` by metis_tac [smtstr_len_eq_zero] >>
  `0 <= smtstr_len s` by metis_tac [smtstr_len_nonnegative] >>
  `0 < smtstr_len s` by intLib.ARITH_TAC >>
  `0 < n` by intLib.ARITH_TAC >>
  `smtstr_rep s <> []` by metis_tac [smtstr_rep_eq_nil] >>
  irule (iffLR smtstr_rep_11) >>
  PURE_REWRITE_TAC [smtstr_rep_substr] >>
  simp [smtstr_len_def] >>
  `~(n <= 0)` by intLib.ARITH_TAC >>
  asm_simp_tac (srw_ss()) [] >>
  PURE_REWRITE_TAC [GSYM integerTheory.INT_OF_NUM_LE] >>
  `&(Num n) = n` by intLib.ARITH_TAC >>
  asm_rewrite_tac [] >>
  PURE_REWRITE_TAC [GSYM smtstr_len_def] >>
  first_assum ACCEPT_TAC
QED

(* 'smtstr_char c' is the SMT-LIB one-character string only for a genuine
   code point; out of range it is an unconstrained ':smtstr'. *)

Theorem smtstr_rep_char:
  c <= 196607 ==> smtstr_rep (smtstr_char c) = [c]
Proof
  simp [smtstr_char_def, smtstr_rep_def]
QED

Theorem smtstr_len_char:
  c <= 196607 ==> smtstr_len (smtstr_char c) = 1
Proof
  simp [smtstr_len_def, smtstr_rep_char]
QED

Theorem smtstr_unit_concat:
  c <= 196607 ==>
  smtstr_concat (smtstr_char c) s = SmtStr (c::smtstr_rep s)
Proof
  simp [smtstr_concat_def, smtstr_rep_char]
QED

Theorem smtstr_literal3_units:
  a <= 196607 /\ b <= 196607 /\ c <= 196607 ==>
  smtstr_concat (smtstr_char a)
    (smtstr_concat (smtstr_char b) (smtstr_char c)) =
      SmtStr [a; b; c]
Proof
  strip_tac >>
  simp [smtstr_concat_def, smtstr_rep_char, smtstr_rep_def]
QED

(* TASK_02 draft_regex_membership uses prefix witnesses; the contains and
   suffix operator recordings use the same append decompositions. *)

Theorem smtstr_prefixof_decompose:
  smtstr_prefixof s t <=>
    ?u. t = smtstr_concat s u
Proof
  simp [smtstr_prefixof_def, smtstr_concat_def,
        rich_listTheory.IS_PREFIX_APPEND] >>
  eq_tac
  >- (strip_tac >>
      `EVERY (\c. c <= 196607) (smtstr_rep s ++ l)` by
        metis_tac [smtstr_rep_bound] >>
      `EVERY (\c. c <= 196607) l` by fs [] >>
      qexists `SmtStr l` >>
      simp [smtstr_rep_def] >>
      metis_tac [SmtStr_smtstr_rep])
  >- (strip_tac >>
      qexists `smtstr_rep u` >>
      simp [smtstr_rep_def])
QED

Theorem smtstr_suffixof_decompose:
  smtstr_suffixof s t <=>
    ?u. t = smtstr_concat u s
Proof
  simp [smtstr_suffixof_def, smtstr_concat_def,
        rich_listTheory.IS_SUFFIX_APPEND] >>
  eq_tac
  >- (strip_tac >>
      `EVERY (\c. c <= 196607) (l ++ smtstr_rep s)` by
        metis_tac [smtstr_rep_bound] >>
      `EVERY (\c. c <= 196607) l` by fs [] >>
      qexists `SmtStr l` >>
      simp [smtstr_rep_def] >>
      metis_tac [SmtStr_smtstr_rep])
  >- (strip_tac >>
      qexists `smtstr_rep u` >>
      simp [smtstr_rep_def])
QED

Theorem smtstr_contains_decompose:
  smtstr_contains s t <=>
    ?u v. s = smtstr_concat u (smtstr_concat t v)
Proof
  simp [smtstr_contains_def, smtstr_concat_def,
        rich_listTheory.IS_SUBLIST_APPEND] >>
  eq_tac
  >- (strip_tac >>
      `EVERY (\c. c <= 196607) (l ++ smtstr_rep t ++ l')` by
        (qpat_x_assum `smtstr_rep s = _` (SUBST1_TAC o SYM) >>
         simp []) >>
      `EVERY (\c. c <= 196607) l /\ EVERY (\c. c <= 196607) l'` by fs [] >>
      qexistsl [`SmtStr l`, `SmtStr l'`] >>
      simp [smtstr_rep_def] >>
      metis_tac [SmtStr_smtstr_rep])
  >- (strip_tac >>
      qexistsl [`smtstr_rep u`, `smtstr_rep v`] >>
      simp [smtstr_rep_def])
QED

Theorem IS_SUBLIST_APPEND_DECOMPOSE[local]:
  IS_SUBLIST (l1 ++ l2) sub <=>
    IS_SUBLIST l1 sub \/ IS_SUBLIST l2 sub \/
    ?p q. sub = p ++ q /\ p <> [] /\ q <> [] /\
          IS_SUFFIX l1 p /\ IS_PREFIX l2 q
Proof
  simp [rich_listTheory.IS_SUBLIST_APPEND,
        rich_listTheory.IS_SUFFIX_APPEND,
        rich_listTheory.IS_PREFIX_APPEND] >>
  eq_tac
  >- (strip_tac >>
      qpat_x_assum `l1 ++ l2 = _` mp_tac >>
      ONCE_REWRITE_TAC [listTheory.APPEND_EQ_APPEND] >>
      strip_tac
      >- (rename1 `l1 = before ++ sub ++ after` >>
          disj1_tac >>
          qexistsl [`before`, `after`] >>
          simp [])
      >- (rename1 `before ++ sub = l1 ++ crossing` >>
          rename1 `l2 = crossing ++ after` >>
          qpat_x_assum `before ++ sub = l1 ++ crossing` mp_tac >>
          ONCE_REWRITE_TAC [listTheory.APPEND_EQ_APPEND] >>
          strip_tac
          >- (rename1 `before = l1 ++ middle` >>
              disj2_tac >> disj1_tac >>
              qexistsl [`middle`, `after`] >>
              fs [listTheory.APPEND_ASSOC])
          >- (rename1 `sub = middle ++ crossing` >>
              rename1 `l1 = before ++ middle` >>
              Cases_on `middle`
              >- (disj2_tac >> disj1_tac >>
                  qexistsl [`[]`, `after`] >> fs [])
              >> Cases_on `crossing`
              >- (disj1_tac >>
                  qexistsl [`before`, `[]`] >> fs [])
              >- (disj2_tac >> disj2_tac >>
                  qexistsl [`h::t`, `h'::t'`] >>
                  simp [] >>
                  qexistsl [`before`, `after`] >>
                  simp []))))
  >- (strip_tac
      >- (rename1 `l1 = before ++ sub ++ after` >>
          qexistsl [`before`, `after ++ l2`] >>
          simp [listTheory.APPEND_ASSOC])
      >- (rename1 `l2 = before ++ sub ++ after` >>
          qexistsl [`l1 ++ before`, `after`] >>
          simp [listTheory.APPEND_ASSOC])
      >- (rename1 `sub = p ++ q` >>
          rename1 `l1 = before ++ p` >>
          rename1 `l2 = q ++ after` >>
          qexistsl [`before`, `after`] >>
          simp [listTheory.APPEND_ASSOC]))
QED

Theorem smtstr_contains_concat:
  smtstr_contains (smtstr_concat s t) sub <=>
    smtstr_contains s sub \/ smtstr_contains t sub \/
    ?p q.
      sub = smtstr_concat p q /\
      p <> SmtStr [] /\ q <> SmtStr [] /\
      smtstr_suffixof p s /\ smtstr_prefixof q t
Proof
  simp [smtstr_contains_def, smtstr_concat_def, smtstr_suffixof_def,
        smtstr_prefixof_def, smtstr_rep_def,
        IS_SUBLIST_APPEND_DECOMPOSE] >>
  eq_tac
  >- (strip_tac
      >- (disj1_tac >> first_assum ACCEPT_TAC)
      >- (disj2_tac >> disj1_tac >> first_assum ACCEPT_TAC)
      >- (disj2_tac >> disj2_tac >>
          `EVERY (\c. c <= 196607) (p ++ q)` by
            metis_tac [smtstr_rep_bound] >>
          fs [] >>
          qexistsl [`SmtStr p`, `SmtStr q`] >>
          simp [smtstr_rep_def, smtstr_eq_SmtStr] >>
          metis_tac [SmtStr_smtstr_rep]))
  >- (strip_tac
      >- (disj1_tac >> first_assum ACCEPT_TAC)
      >- (disj2_tac >> disj1_tac >> first_assum ACCEPT_TAC)
      >- (disj2_tac >> disj2_tac >>
          qexistsl [`smtstr_rep p`, `smtstr_rep q`] >>
          fs [smtstr_rep_eq_nil, smtstr_rep_def]))
QED

Theorem smtstr_contains_concat_straddling:
  p <> SmtStr [] /\ q <> SmtStr [] /\
  smtstr_suffixof p s /\ smtstr_prefixof q t ==>
  smtstr_contains (smtstr_concat s t) (smtstr_concat p q)
Proof
  rw [smtstr_contains_concat] >>
  disj2_tac >> disj2_tac >>
  qexistsl [`p`, `q`] >>
  simp []
QED

Theorem smtstr_contains_concat_len_one:
  smtstr_len sub = 1 ==>
  (smtstr_contains (smtstr_concat s t) sub <=>
   smtstr_contains s sub \/ smtstr_contains t sub)
Proof
  rw [smtstr_contains_concat] >>
  eq_tac >> strip_tac >> simp [] >>
  `0 <= smtstr_len p /\ 0 <= smtstr_len q` by
    simp [smtstr_len_nonnegative] >>
  `smtstr_len p <> 0 /\ smtstr_len q <> 0` by
    metis_tac [smtstr_len_eq_zero] >>
  `~(smtstr_len p + smtstr_len q = 1)` by intLib.ARITH_TAC >>
  fs [smtstr_len_concat]
QED

Theorem IS_SUBLIST_APPEND_len_one:
  LENGTH sub = 1 ==>
  (IS_SUBLIST (s ++ t) sub <=>
   IS_SUBLIST s sub \/ IS_SUBLIST t sub)
Proof
  rw [IS_SUBLIST_APPEND_DECOMPOSE] >>
  eq_tac >> strip_tac >> simp [] >>
  `LENGTH p <> 0 /\ LENGTH q <> 0` by
    fs [listTheory.LENGTH_NIL] >>
  `LENGTH p + LENGTH q = 1` by fs [] >>
  decide_tac
QED

(* TASK_02 draft_regex_membership records reflexive prefix clauses.  The
   suffix and contains variants complete the same symbolic A6 family used by
   the TASK_02 per-operator recordings. *)

Theorem smtstr_prefixof_refl:
  smtstr_prefixof s s
Proof
  simp [smtstr_prefixof_decompose] >>
  qexists `SmtStr []` >>
  simp [smtstr_concat_nil_right]
QED

Theorem smtstr_suffixof_refl:
  smtstr_suffixof s s
Proof
  simp [smtstr_suffixof_decompose] >>
  qexists `SmtStr []` >>
  simp [smtstr_concat_nil_left]
QED

Theorem smtstr_contains_refl:
  smtstr_contains s s
Proof
  simp [smtstr_contains_decompose] >>
  qexistsl [`SmtStr []`, `SmtStr []`] >>
  simp [smtstr_concat_nil_left, smtstr_concat_nil_right]
QED

(* TASK_02 draft_regex_membership repeatedly specializes prefix reasoning to
   a one-character right operand.  The implication lemmas connect the
   TASK_02 prefix/suffix recordings to their contains consequences. *)

Theorem smtstr_prefixof_singleton:
  c <= 196607 ==>
  (smtstr_prefixof s (SmtStr [c]) <=>
   s = SmtStr [] \/ s = SmtStr [c])
Proof
  strip_tac >>
  Cases_on `smtstr_rep s`
  >- fs [smtstr_prefixof_def, smtstr_rep_def, smtstr_eq_SmtStr]
  >> Cases_on `t` >>
  fs [smtstr_prefixof_def, smtstr_rep_def, smtstr_eq_SmtStr,
      rich_listTheory.IS_PREFIX]
QED

Theorem smtstr_prefixof_imp_contains:
  smtstr_prefixof s t ==> smtstr_contains t s
Proof
  simp [smtstr_prefixof_decompose, smtstr_contains_decompose] >>
  metis_tac [smtstr_concat_nil_left]
QED

Theorem smtstr_suffixof_imp_contains:
  smtstr_suffixof s t ==> smtstr_contains t s
Proof
  simp [smtstr_suffixof_decompose, smtstr_contains_decompose] >>
  metis_tac [smtstr_concat_nil_right]
QED

Theorem smtstr_prefixof_trans:
  smtstr_prefixof s t /\ smtstr_prefixof t u ==>
    smtstr_prefixof s u
Proof
  simp [smtstr_prefixof_decompose] >>
  metis_tac [smtstr_concat_assoc]
QED

Theorem smtstr_suffixof_trans:
  smtstr_suffixof s t /\ smtstr_suffixof t u ==>
    smtstr_suffixof s u
Proof
  simp [smtstr_suffixof_decompose] >>
  metis_tac [smtstr_concat_assoc]
QED

Theorem smtstr_contains_trans:
  smtstr_contains s t /\ smtstr_contains t u ==>
    smtstr_contains s u
Proof
  simp [smtstr_contains_decompose] >>
  metis_tac [smtstr_concat_assoc]
QED

Theorem smtstr_replace_concat_contained_suffix:
  smtstr_len t = 1 /\ smtstr_contains s u ==>
  smtstr_replace (smtstr_concat s u) t r =
  smtstr_concat (smtstr_replace s t r) u
Proof
  strip_tac >>
  Cases_on `smtstr_contains s t`
  >- simp [smtstr_replace_concat_after_match] >>
  `~smtstr_contains u t` by
    metis_tac [smtstr_contains_trans] >>
  `~smtstr_contains (smtstr_concat s u) t` by
    simp [smtstr_contains_concat_len_one] >>
  simp [smtstr_replace_absent]
QED

Theorem smtstr_contains_length_bound:
  smtstr_contains s t ==> smtstr_len t <= smtstr_len s
Proof
  rw [smtstr_contains_decompose] >>
  `0 <= smtstr_len u /\ 0 <= smtstr_len v` by
    simp [smtstr_len_nonnegative] >>
  fs [smtstr_len_concat] >>
  intLib.ARITH_TAC
QED

Theorem smtstr_contains_length_equal:
  smtstr_len s <= smtstr_len t ==>
  (smtstr_contains s t <=> s = t)
Proof
  strip_tac >>
  rw [smtstr_contains_decompose] >>
  eq_tac
  >- (strip_tac >>
      `smtstr_len u = 0 /\ smtstr_len v = 0` by
        (`0 <= smtstr_len u /\ 0 <= smtstr_len v` by
           simp [smtstr_len_nonnegative] >>
         fs [smtstr_len_concat] >>
         intLib.ARITH_TAC) >>
      fs [smtstr_len_eq_zero, smtstr_concat_nil_left,
          smtstr_concat_nil_right]) >>
  strip_tac >> qexistsl [`SmtStr []`, `SmtStr []`] >>
  simp [smtstr_concat_nil_left, smtstr_concat_nil_right]
QED

Theorem smtstr_contains_antisym:
  smtstr_contains s t /\ smtstr_contains t s ==> s = t
Proof
  metis_tac [smtstr_contains_length_bound,
             smtstr_contains_length_equal]
QED

Theorem smtstr_replace_preserves_contains:
  smtstr_contains s u /\ smtstr_contains r u ==>
  smtstr_contains (smtstr_replace s t r) u
Proof
  Cases_on `smtstr_contains s t`
  >- metis_tac [smtstr_replace_contains_replacement,
                smtstr_contains_trans] >>
  simp [smtstr_replace_absent]
QED

Theorem smtstr_replace_avoids_outer:
  ~smtstr_contains s t /\ ~smtstr_contains s u ==>
  ~smtstr_contains s (smtstr_replace t r u)
Proof
  strip_tac >>
  Cases_on `smtstr_contains t r`
  >- (CCONTR_TAC >>
      `smtstr_contains (smtstr_replace t r u) u` by
        metis_tac [smtstr_replace_contains_replacement] >>
      metis_tac [smtstr_contains_trans]) >>
  simp [smtstr_replace_absent]
QED

Theorem smtstr_replace_self_contains:
  smtstr_contains (smtstr_replace x y x) y <=>
  smtstr_contains x y
Proof
  Cases_on `smtstr_contains x y`
  >- (`smtstr_contains (smtstr_replace x y x) x` by
        metis_tac [smtstr_replace_contains_replacement,
                   smtstr_contains_refl] >>
      metis_tac [smtstr_contains_trans]) >>
  simp [smtstr_replace_absent]
QED

Theorem smtstr_replace_self_target:
  smtstr_len x <= smtstr_len y ==>
  smtstr_replace x y x = x
Proof
  strip_tac >>
  Cases_on `smtstr_contains x y`
  >- (`x = y` by
        metis_tac [smtstr_contains_length_equal] >>
      simp [smtstr_replace_self]) >>
  simp [smtstr_replace_absent]
QED

Theorem smtstr_replace_raw_contains_len_one[local]:
  LENGTH w = 1 /\ ~IS_SUBLIST y w ==>
  (IS_SUBLIST (smtstr_replace_raw x y z) w <=>
   IS_SUBLIST x w \/ (IS_SUBLIST x y /\ IS_SUBLIST z w))
Proof
  strip_tac >>
  Cases_on `IS_SUBLIST x y`
  >- (drule_then (qspec_then `z` strip_assume_tac)
        smtstr_replace_raw_hit >>
      rw [] >>
      simp [IS_SUBLIST_APPEND_len_one] >>
      tautLib.TAUT_TAC) >>
  simp [smtstr_replace_raw_absent]
QED

Theorem smtstr_replace_contains_len_one:
  smtstr_len w = 1 /\ ~smtstr_contains y w ==>
  (smtstr_contains (smtstr_replace x y z) w <=>
   smtstr_contains x w \/
   (smtstr_contains x y /\ smtstr_contains z w))
Proof
  strip_tac >>
  rw [smtstr_contains_def, smtstr_rep_replace] >>
  irule smtstr_replace_raw_contains_len_one >>
  fs [smtstr_contains_def, smtstr_len_def] >>
  intLib.ARITH_TAC
QED

Theorem smtstr_replace_self_contains_len_one:
  smtstr_len w = 1 ==>
  (smtstr_contains (smtstr_replace x y x) w <=>
   smtstr_contains x w)
Proof
  strip_tac >>
  Cases_on `smtstr_contains y w`
  >- (Cases_on `smtstr_contains x y`
      >- (`smtstr_contains x w` by
            metis_tac [smtstr_contains_trans] >>
          `smtstr_contains (smtstr_replace x y x) x` by
            metis_tac [smtstr_replace_contains_replacement,
                       smtstr_contains_refl] >>
          metis_tac [smtstr_contains_trans]) >>
      simp [smtstr_replace_absent]) >>
  metis_tac [smtstr_replace_contains_len_one]
QED

Theorem smtstr_replace_pattern_self_contains:
  smtstr_contains s (smtstr_replace t s t) <=>
  smtstr_contains s t
Proof
  Cases_on `smtstr_contains t s`
  >- (eq_tac
      >- (strip_tac >>
          `smtstr_contains (smtstr_replace t s t) t` by
            metis_tac [smtstr_replace_contains_replacement,
                       smtstr_contains_refl] >>
          metis_tac [smtstr_contains_trans]) >>
      strip_tac >>
      `s = t` by metis_tac [smtstr_contains_antisym] >>
      simp [smtstr_replace_self, smtstr_contains_refl]) >>
  simp [smtstr_replace_absent]
QED

Theorem smtstr_replace_empty_source_contains:
  smtstr_len empty = 0 ==>
  (smtstr_contains s (smtstr_replace empty s t) <=>
   empty = smtstr_replace empty s t)
Proof
  rw [smtstr_len_eq_zero] >>
  Cases_on `smtstr_rep s`
  >- simp [smtstr_replace_def, smtstr_replace_raw_def,
           smtstr_indexof_aux_def, smtstr_contains_def,
           smtstr_rep_def, rich_listTheory.IS_SUBLIST_APPEND,
           smtstr_rep_eq_nil] >>
  `s = SmtStr (h::t')` by metis_tac [SmtStr_smtstr_rep] >>
  simp [smtstr_replace_def, smtstr_replace_raw_def,
        smtstr_indexof_aux_def, smtstr_contains_def,
        smtstr_rep_def, rich_listTheory.IS_SUBLIST_APPEND] >>
  qexistsl [`[]`, `h::t'`] >> simp []
QED

Theorem smtstr_replace_self_empty_forward[local]:
  x = SmtStr [] ==>
  smtstr_replace x y x = SmtStr []
Proof
  strip_tac >>
  fs [smtstr_replace_def, smtstr_replace_raw_def,
      smtstr_rep_def, smtstr_indexof_aux_def] >>
  BasicProvers.every_case_tac >> simp []
QED

Theorem smtstr_replace_self_empty_reverse[local]:
  smtstr_replace x y x = SmtStr [] ==>
  x = SmtStr []
Proof
  strip_tac >>
  `smtstr_contains (smtstr_replace x y x) x` by
    metis_tac [smtstr_replace_contains_replacement,
               smtstr_contains_refl] >>
  `smtstr_contains (SmtStr []) x` by
    (qpat_x_assum `smtstr_replace x y x = SmtStr []`
       (fn th => ONCE_REWRITE_TAC [GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  `smtstr_contains x (SmtStr [])` by
    (rw [smtstr_contains_def, smtstr_rep_def,
         rich_listTheory.IS_SUBLIST_APPEND] >>
     qexistsl [`smtstr_rep x`, `[]`] >> simp []) >>
  metis_tac [smtstr_contains_antisym]
QED

Theorem smtstr_replace_self_empty_eq:
  smtstr_len empty = 0 ==>
  (smtstr_replace x y x = empty <=> x = empty)
Proof
  rw [smtstr_len_eq_zero] >>
  metis_tac [smtstr_replace_self_empty_forward,
             smtstr_replace_self_empty_reverse]
QED

Theorem smtstr_replace_self_source_reverse[local]:
  smtstr_replace x y x = y ==> x = y
Proof
  strip_tac >>
  Cases_on `smtstr_contains x y`
  >- (`smtstr_contains (smtstr_replace x y x) x` by
        metis_tac [smtstr_replace_contains_replacement,
                   smtstr_contains_refl] >>
      `smtstr_contains y x` by
        (qpat_x_assum `smtstr_replace x y x = y`
           (fn th => ONCE_REWRITE_TAC [GSYM th]) >>
         first_assum ACCEPT_TAC) >>
      metis_tac [smtstr_contains_antisym])
  >- fs [smtstr_replace_absent]
QED

Theorem smtstr_replace_self_source_eq:
  (smtstr_replace x y x = y <=> x = y)
Proof
  metis_tac [smtstr_replace_self,
             smtstr_replace_self_source_reverse]
QED

Theorem smtstr_replace_raw_eq_source_pattern[local]:
  IS_SUBLIST s t /\ smtstr_replace_raw s t r = s ==> r = t
Proof
  strip_tac >>
  drule_then (qspec_then `r` strip_assume_tac)
    smtstr_replace_raw_hit >>
  `pre ++ r ++ post = pre ++ t ++ post` by metis_tac [] >>
  `r ++ post = t ++ post` by
    metis_tac [listTheory.APPEND_11] >>
  metis_tac [listTheory.APPEND_11]
QED

Theorem smtstr_replace_no_change_reverse[local]:
  y <> z /\ smtstr_replace x y z = x ==>
  ~smtstr_contains x y
Proof
  strip_tac >> CCONTR_TAC >>
  `smtstr_replace_raw (smtstr_rep x) (smtstr_rep y)
      (smtstr_rep z) = smtstr_rep x` by
    (qpat_x_assum `smtstr_replace x y z = x`
       (fn th => ACCEPT_TAC
          (REWRITE_RULE [smtstr_rep_replace]
            (AP_TERM ``smtstr_rep`` th)))) >>
  fs [] >>
  `IS_SUBLIST (smtstr_rep x) (smtstr_rep y)` by
    fs [smtstr_contains_def] >>
  `smtstr_rep z = smtstr_rep y` by
    metis_tac [smtstr_replace_raw_eq_source_pattern] >>
  metis_tac [smtstr_rep_11]
QED

Theorem smtstr_replace_no_change_eq:
  y <> z ==>
  (smtstr_replace x y z = x <=> ~smtstr_contains x y)
Proof
  metis_tac [smtstr_replace_absent,
             smtstr_replace_no_change_reverse]
QED

Theorem smtstr_replace_equal_length:
  smtstr_len t = smtstr_len r ==>
  smtstr_len (smtstr_replace s t r) = smtstr_len s
Proof
  strip_tac >>
  Cases_on `smtstr_contains s t`
  >- (`IS_SUBLIST (smtstr_rep s) (smtstr_rep t)` by
        fs [smtstr_contains_def] >>
      drule_then (qspec_then `smtstr_rep r` strip_assume_tac)
        smtstr_replace_raw_hit >>
      fs [smtstr_contains_def, smtstr_len_def])
  >- simp [smtstr_replace_absent]
QED

Theorem smtstr_replace_target_equal_length_forward[local]:
  smtstr_len y = smtstr_len z /\ (x = y \/ x = z) ==>
  smtstr_replace x y z = z
Proof
  strip_tac >> fs [smtstr_replace_self, smtstr_replace_self_target]
QED

Theorem smtstr_replace_target_equal_length_reverse[local]:
  smtstr_len y = smtstr_len z /\ smtstr_replace x y z = z ==>
  x = y \/ x = z
Proof
  strip_tac >>
  Cases_on `x = y` >> simp [] >>
  Cases_on `smtstr_contains x y` >> fs [smtstr_replace_absent] >>
  `smtstr_len (smtstr_replace x y z) = smtstr_len x` by
    metis_tac [smtstr_replace_equal_length] >>
  `smtstr_len x = smtstr_len y` by metis_tac [] >>
  mp_tac (Q.INST [`s` |-> `x`, `t` |-> `y`]
    smtstr_contains_length_equal) >>
  simp []
QED

Theorem smtstr_replace_target_equal_length_eq:
  smtstr_len y = smtstr_len z ==>
  (smtstr_replace x y z = z <=> x = y \/ x = z)
Proof
  metis_tac [smtstr_replace_target_equal_length_forward,
             smtstr_replace_target_equal_length_reverse]
QED

Theorem smtstr_replace_raw_empty_singleton[local]:
  smtstr_replace_raw s [c] [] = [] <=> s = [] \/ s = [c]
Proof
  Cases_on `IS_SUBLIST s [c]`
  >- (drule_then (qspec_then `[]` strip_assume_tac)
        smtstr_replace_raw_hit >>
      fs [] >>
      eq_tac >> strip_tac >> fs [] >>
      Cases_on `pre` >> Cases_on `post` >> fs [])
      >- (`IS_SUBLIST [c] [c]` by
        (rw [rich_listTheory.IS_SUBLIST_APPEND] >>
         qexistsl [`[]`, `[]`] >> simp []) >>
      fs [smtstr_replace_raw_absent] >>
      metis_tac [])
QED

Theorem smtstr_indexof_aux_suc[local]:
  !s t n.
    smtstr_indexof_aux t (SUC n) s =
    OPTION_MAP SUC (smtstr_indexof_aux t n s)
Proof
  Induct >> Cases_on `t` >> rw [smtstr_indexof_aux_def] >> simp []
QED

Theorem smtstr_indexof_aux_first[local]:
  !s t n.
    smtstr_indexof_aux t 0 s = SOME n ==>
    IS_PREFIX (DROP n s) t /\
    !m. m < n ==> ~IS_PREFIX (DROP m s) t
Proof
  Induct
  >- simp [smtstr_indexof_aux_def] >>
  rpt gen_tac >>
  rw [smtstr_indexof_aux_def] >>
  assume_tac (Q.SPECL [`s`, `t`, `0`] smtstr_indexof_aux_suc) >>
  Cases_on `smtstr_indexof_aux t 0 s` >>
  fs [] >>
  Cases_on `m` >> fs []
QED

Theorem smtstr_indexof_aux_first_intro[local]:
  !n s t.
    IS_PREFIX (DROP n s) t /\
    (!m. m < n ==> ~IS_PREFIX (DROP m s) t) ==>
    smtstr_indexof_aux t 0 s = SOME n
Proof
  Induct THENL
  [Cases_on `s` >> rw [smtstr_indexof_aux_def],
   rpt gen_tac >>
   (Cases_on `s` THENL
    [simp [] >> strip_tac >>
       first_x_assum (qspec_then `0` mp_tac) >> simp [],
     rw [smtstr_indexof_aux_def] THENL
     [disj2_tac >> qexists_tac `0` >> simp [],
      qpat_x_assum `!s t. _`
        (qspecl_then [`t'`, `t`] mp_tac) >>
      impl_tac
      >- (simp [] >> rpt strip_tac >>
          first_x_assum (qspec_then `SUC m` mp_tac) >> simp []) >>
      strip_tac >>
      assume_tac
        (Q.SPECL [`t'`, `t`, `0`] smtstr_indexof_aux_suc) >>
      fs []]])]
QED

Theorem smtstr_inserted_source_no_early[local]:
  y = pre ++ w ++ post /\ LENGTH pre = n /\
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
    metis_tac [is_prefix_append_short] >>
  fs [rich_listTheory.IS_PREFIX_APPEND] >>
  qexists_tac `l''` >>
  simp [listTheory.DROP_APPEND1] >>
  decide_tac
QED

Theorem smtstr_replace_raw_lookahead_hit[local]:
  IS_SUBLIST y w ==>
  smtstr_replace_raw (smtstr_replace_raw y w y) y z =
  smtstr_replace_raw y w z
Proof
  strip_tac >>
  Cases_on `smtstr_indexof_aux w 0 y`
  >- fs [smtstr_indexof_aux_none] >>
  drule smtstr_indexof_aux_first >>
  strip_tac >>
  qpat_x_assum `smtstr_indexof_aux w 0 y = SOME x`
    (fn th => assume_tac th >>
       mp_tac (MATCH_MP smtstr_indexof_aux_split th)) >>
  strip_tac >>
  qpat_x_assum `LENGTH pre + 0 = x` (SUBST_ALL_TAC o SYM) >>
  `smtstr_replace_raw y w y = pre ++ y ++ post` by
    simp [smtstr_replace_raw_def, take_splice, drop_splice] >>
  `smtstr_indexof_aux y 0 (pre ++ y ++ post) =
     SOME (LENGTH pre)` by
    (irule smtstr_indexof_aux_first_intro >>
     conj_tac
     >- (match_mp_tac smtstr_inserted_source_no_early >> fs []) >>
     simp [rich_listTheory.DROP_LENGTH_APPEND,
           rich_listTheory.IS_PREFIX_APPEND] >>
     qexists_tac `post` >>
     simp [listTheory.DROP_APPEND1, listTheory.APPEND_ASSOC]) >>
  qpat_x_assum `y = pre ++ w ++ post` SUBST_ALL_TAC >>
  fs [smtstr_replace_raw_def, take_splice, drop_splice,
      listTheory.APPEND_ASSOC] >>
  simp [listTheory.TAKE_APPEND1, listTheory.DROP_APPEND1]
QED

Theorem smtstr_replace_lookahead_hit[local]:
  smtstr_contains y w ==>
  smtstr_replace (smtstr_replace y w y) y z =
  smtstr_replace y w z
Proof
  rw [smtstr_contains_def] >>
  irule (iffLR smtstr_rep_11) >>
  PURE_REWRITE_TAC [smtstr_rep_replace] >>
  metis_tac [smtstr_replace_raw_lookahead_hit]
QED

Theorem smtstr_replace_length_le[local]:
  smtstr_contains s t /\ smtstr_len r <= smtstr_len t ==>
  smtstr_len (smtstr_replace s t r) <= smtstr_len s
Proof
  strip_tac >>
  fs [smtstr_contains_def] >>
  drule_then (qspec_then `smtstr_rep r` strip_assume_tac)
    smtstr_replace_raw_hit >>
  fs [smtstr_len_def, smtstr_rep_replace] >>
  intLib.ARITH_TAC
QED

Theorem smtstr_replace_nested_lookahead_id_simp:
  w <> z /\ smtstr_len z <= smtstr_len w ==>
  smtstr_replace (smtstr_replace y w y) y z =
  smtstr_replace (smtstr_replace y w z) y z
Proof
  strip_tac >>
  Cases_on `smtstr_contains y w`
  >- (`smtstr_replace (smtstr_replace y w y) y z =
         smtstr_replace y w z` by
        metis_tac [smtstr_replace_lookahead_hit] >>
      `smtstr_len (smtstr_replace y w z) <= smtstr_len y` by
        metis_tac [smtstr_replace_length_le] >>
      `~smtstr_contains (smtstr_replace y w z) y` by
        (CCONTR_TAC >>
         `smtstr_len y <= smtstr_len (smtstr_replace y w z)` by
           metis_tac [smtstr_contains_length_bound] >>
         `smtstr_replace y w z = y` by
           metis_tac [smtstr_contains_length_equal] >>
         metis_tac [smtstr_replace_no_change_eq]) >>
      simp [smtstr_replace_absent]) >>
  simp [smtstr_replace_absent, smtstr_replace_self]
QED

Theorem smtstr_replace_raw_singleton_cons[local]:
  smtstr_replace_raw (h::s) [a] [b] =
    if h = a then b::s
    else h::smtstr_replace_raw s [a] [b]
Proof
  simp [smtstr_replace_raw_def, smtstr_indexof_aux_def,
        rich_listTheory.IS_PREFIX] >>
  Cases_on `h = a` >> simp [smtstr_indexof_aux_suc] >>
  assume_tac (SIMP_RULE (srw_ss()) []
    (ISPECL [``s:num list``, ``[a:num]``, ``0:num``]
      smtstr_indexof_aux_suc)) >>
  Cases_on `smtstr_indexof_aux [a] 0 s` >>
  fs [arithmeticTheory.ADD1]
QED

Theorem smtstr_replace_raw_singleton_nil[local]:
  smtstr_replace_raw [] [a] [b] = []
Proof
  simp [smtstr_replace_raw_def, smtstr_indexof_aux_def]
QED

Theorem smtstr_replace_raw_singleton_take[local]:
  !n s.
    TAKE n (smtstr_replace_raw s [a] [b]) =
    smtstr_replace_raw (TAKE n s) [a] [b]
Proof
  rpt gen_tac >> qid_spec_tac `s` >> Induct_on `n` >>
  Cases_on `s` >>
  simp [smtstr_replace_raw_singleton_nil,
        smtstr_replace_raw_singleton_cons] >>
  Cases_on `h = a` >> fs [boolTheory.EQ_SYM_EQ]
QED

Theorem smtstr_replace_raw_length_one_take[local]:
  LENGTH t = 1 /\ LENGTH r = 1 ==>
  TAKE n (smtstr_replace_raw s t r) =
  smtstr_replace_raw (TAKE n s) t r
Proof
  strip_tac >>
  Cases_on `t` >> fs [] >>
  Cases_on `r` >> fs [] >>
  MATCH_ACCEPT_TAC smtstr_replace_raw_singleton_take
QED

Theorem smtstr_substr_replace_len_one:
  smtstr_len t = smtstr_len r /\ smtstr_len t = 1 ==>
  smtstr_substr (smtstr_replace s t r) 0 n =
  smtstr_replace (smtstr_substr s 0 n) t r
Proof
  strip_tac >>
  `LENGTH (smtstr_rep t) = 1 /\ LENGTH (smtstr_rep r) = 1` by
    fs [smtstr_len_def] >>
  Cases_on `0 < n`
  >- (irule (iffLR smtstr_rep_11) >>
      PURE_REWRITE_TAC [smtstr_rep_replace] >>
      imp_res_tac smtstr_rep_substr_positive >>
      fs [smtstr_replace_raw_length_one_take, smtstr_len_def])
  >- (`n <= 0` by intLib.ARITH_TAC >>
      `t <> SmtStr []` by
        (CCONTR_TAC >> fs [smtstr_len_def, smtstr_rep_def]) >>
      simp [smtstr_substr_def] >>
      `smtstr_rep t <> []` by metis_tac [SmtStr_smtstr_rep] >>
      simp [smtstr_replace_def, smtstr_replace_raw_def,
            smtstr_indexof_aux_def, smtstr_rep_def])
QED

Theorem smtstr_replace_empty_result_len_one:
  smtstr_len empty = 0 /\ smtstr_len y = 1 ==>
  (smtstr_replace x y empty = empty <=> smtstr_prefixof x y)
Proof
  rw [smtstr_len_eq_zero] >>
  Cases_on `smtstr_rep y` >> fs [smtstr_len_def] >>
  Cases_on `t` >> fs [smtstr_len_def] >>
  `y = SmtStr [h]` by metis_tac [SmtStr_smtstr_rep] >>
  `h <= 196607` by
    (mp_tac (Q.INST [`s` |-> `y`] smtstr_rep_bound) >>
     asm_rewrite_tac [] >> simp []) >>
  rw [smtstr_prefixof_singleton] >>
  eq_tac
  >- (strip_tac >>
      qpat_x_assum
        `smtstr_replace x (SmtStr [h]) (SmtStr []) = SmtStr []`
        (fn th => assume_tac (MATCH_MP (iffRL smtstr_rep_11) th)) >>
      qpat_x_assum
        `smtstr_rep (smtstr_replace x (SmtStr [h]) (SmtStr [])) =
         smtstr_rep (SmtStr [])`
        (fn th => assume_tac
          (PURE_REWRITE_RULE [smtstr_rep_replace] th)) >>
      `smtstr_rep (SmtStr [h]) = [h]` by
        simp [smtstr_rep_def] >>
      qpat_x_assum
        `smtstr_replace_raw (smtstr_rep x)
           (smtstr_rep (SmtStr [h])) (smtstr_rep (SmtStr [])) =
         smtstr_rep (SmtStr [])`
        (fn th => assume_tac (REWRITE_RULE
          [ASSUME ``smtstr_rep (SmtStr [h]) = [h]``,
           smtstr_rep_def] th)) >>
      fs [smtstr_replace_raw_empty_singleton] >>
      metis_tac [SmtStr_smtstr_rep])
  >- (strip_tac >> fs [smtstr_replace_self] >>
      simp [smtstr_replace_def, smtstr_replace_raw_def,
            smtstr_indexof_aux_def, smtstr_rep_def])
QED

Theorem smtstr_contains_empty_pattern:
  smtstr_contains s (SmtStr [])
Proof
  rw [smtstr_contains_def, smtstr_rep_def,
      rich_listTheory.IS_SUBLIST_APPEND] >>
  qexistsl [`smtstr_rep s`, `[]`] >> simp []
QED

Theorem smtstr_contains_empty_source:
  smtstr_contains (SmtStr []) s <=> s = SmtStr []
Proof
  mp_tac (Q.INST [`s` |-> `SmtStr []`, `t` |-> `s`]
    smtstr_contains_length_equal) >>
  simp [smtstr_len_def, smtstr_rep_def,
        smtstr_len_nonnegative]
QED

Theorem smtstr_replace_empty_result_nonempty:
  smtstr_len empty = 0 /\ z <> empty ==>
  (smtstr_replace x y z = empty <=> x = empty /\ y <> empty)
Proof
  rw [smtstr_len_eq_zero] >>
  eq_tac
  >- (strip_tac >>
      Cases_on `smtstr_contains x y`
      >- (`smtstr_contains (smtstr_replace x y z) z` by
            metis_tac [smtstr_replace_contains_replacement] >>
          `smtstr_contains (SmtStr []) z` by metis_tac [] >>
          fs [smtstr_contains_empty_source])
      >- (`x = SmtStr []` by
            fs [smtstr_replace_absent] >>
          metis_tac [smtstr_contains_empty_source]))
  >- (strip_tac >> fs [] >>
      `~smtstr_contains (SmtStr []) y` by
        metis_tac [smtstr_contains_empty_source] >>
      simp [smtstr_replace_absent])
QED

Theorem smtstr_replace_empty_source_nonempty:
  smtstr_len empty = 0 /\ z <> empty ==>
  (smtstr_replace empty x y = z <=> x = empty /\ y = z)
Proof
  rw [smtstr_len_eq_zero] >>
  Cases_on `x = SmtStr []` >>
  simp [smtstr_replace_empty, smtstr_concat_nil_right,
        smtstr_contains_empty_source, smtstr_replace_absent]
QED

Theorem smtstr_replace_nested_source_target_absent:
  ~smtstr_contains z w ==>
  smtstr_replace x w (smtstr_replace z x y) =
  smtstr_replace x w z
Proof
  strip_tac >>
  Cases_on `smtstr_contains x w`
  >- (`~smtstr_contains z x` by
        metis_tac [smtstr_contains_trans] >>
      simp [smtstr_replace_absent]) >>
  simp [smtstr_replace_absent]
QED

Theorem smtstr_replace_nested_target_self:
  smtstr_replace x y (smtstr_replace y x y) = x
Proof
  Cases_on `smtstr_contains x y`
  >- (Cases_on `smtstr_contains y x`
      >- (`x = y` by metis_tac [smtstr_contains_antisym] >>
          simp [smtstr_replace_self]) >>
      simp [smtstr_replace_absent, smtstr_replace_id]) >>
  simp [smtstr_replace_absent]
QED

Theorem smtstr_replace_nested_target_absent:
  ~smtstr_contains x z ==>
  smtstr_replace x y (smtstr_replace y z w) = x
Proof
  strip_tac >>
  Cases_on `smtstr_contains x y`
  >- (`~smtstr_contains y z` by
        (CCONTR_TAC >>
         metis_tac [smtstr_contains_trans]) >>
      simp [smtstr_replace_absent, smtstr_replace_id]) >>
  simp [smtstr_replace_absent]
QED

Theorem smtstr_replace_nested_source_self:
  smtstr_replace x (smtstr_replace y x y) z =
  smtstr_replace x y z
Proof
  Cases_on `smtstr_contains x y`
  >- (`~smtstr_contains y x \/ x = y` by
        metis_tac [smtstr_contains_antisym] >>
      fs [smtstr_replace_absent, smtstr_replace_self]) >>
  `smtstr_contains (smtstr_replace y x y) y` by
    metis_tac [smtstr_replace_contains_replacement,
               smtstr_contains_refl] >>
  `~smtstr_contains x (smtstr_replace y x y)` by
    (CCONTR_TAC >>
     metis_tac [smtstr_contains_trans]) >>
  simp [smtstr_replace_absent]
QED

Theorem smtstr_replace_nested_source_inverse_absent1:
  ~smtstr_contains y z ==>
  smtstr_replace x (smtstr_replace y x z) y =
  smtstr_replace x y y
Proof
  strip_tac >>
  Cases_on `smtstr_contains y x`
  >- (`smtstr_contains (smtstr_replace y x z) z` by
        metis_tac [smtstr_replace_contains_replacement] >>
      `~smtstr_contains x (smtstr_replace y x z)` by
        (CCONTR_TAC >>
         `smtstr_contains x z` by
           metis_tac [smtstr_contains_trans] >>
         metis_tac [smtstr_contains_trans]) >>
      `~smtstr_contains x y \/ x = y` by
        metis_tac [smtstr_contains_antisym] >>
      fs [smtstr_replace_absent, smtstr_replace_id]) >>
  simp [smtstr_replace_absent]
QED

Theorem smtstr_replace_nested_source_inverse_absent2:
  ~smtstr_contains y z ==>
  smtstr_replace x (smtstr_replace y x z) x =
  smtstr_replace x y x
Proof
  strip_tac >>
  Cases_on `smtstr_contains y x`
  >- (`smtstr_contains (smtstr_replace y x z) z` by
        metis_tac [smtstr_replace_contains_replacement] >>
      `~smtstr_contains x (smtstr_replace y x z)` by
        (CCONTR_TAC >>
         `smtstr_contains x z` by
           metis_tac [smtstr_contains_trans] >>
         metis_tac [smtstr_contains_trans]) >>
      `~smtstr_contains x y \/ x = y` by
        metis_tac [smtstr_contains_antisym] >>
      fs [smtstr_replace_absent, smtstr_replace_self]) >>
  simp [smtstr_replace_absent]
QED

Theorem smtstr_replace_nested_source_inverse_absent3:
  ~smtstr_contains x z /\ ~smtstr_contains x w ==>
  smtstr_replace x (smtstr_replace y z w) u =
  smtstr_replace x y u
Proof
  strip_tac >>
  Cases_on `smtstr_contains y z`
  >- (`smtstr_contains (smtstr_replace y z w) w` by
        metis_tac [smtstr_replace_contains_replacement] >>
      `~smtstr_contains x (smtstr_replace y z w)` by
        (CCONTR_TAC >> metis_tac [smtstr_contains_trans]) >>
      `~smtstr_contains x y` by
        (CCONTR_TAC >> metis_tac [smtstr_contains_trans]) >>
      simp [smtstr_replace_absent]) >>
  simp [smtstr_replace_absent]
QED

Theorem smtstr_replace_nested_dual_self:
  smtstr_replace x (smtstr_replace x y x) x = x
Proof
  irule smtstr_replace_self_target >>
  `smtstr_contains (smtstr_replace x y x) x` by
    metis_tac [smtstr_replace_contains_replacement,
               smtstr_contains_refl] >>
  metis_tac [smtstr_contains_length_bound]
QED

Theorem append_prefix_of_length[local]:
  a ++ b = c ++ d /\ LENGTH c <= LENGTH a ==>
  ?e. a = c ++ e
Proof
  rw [listTheory.APPEND_EQ_APPEND] >>
  fs [] >>
  Cases_on `l` >>
  fs []
QED

Theorem suffix_factor_base[local]:
  y ++ b = c ++ z ++ b ++ d ==> IS_SUBLIST y z
Proof
  strip_tac >>
  `LENGTH (c ++ z) <= LENGTH y` by
    (qpat_x_assum `_ = _` (mp_tac o AP_TERM ``LENGTH``) >>
     simp [] >>
     decide_tac) >>
  `?e. y = (c ++ z) ++ e` by
    metis_tac [append_prefix_of_length, listTheory.APPEND_ASSOC] >>
  rw [rich_listTheory.IS_SUBLIST_APPEND] >>
  qexistsl [`c`, `e`] >>
  simp []
QED

Theorem replace_factor_comparable[local]:
  a ++ y ++ b = c ++ a ++ z ++ b ++ d ==>
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
      irule suffix_factor_base >>
      qexistsl [`b`, `c`, `d`] >>
      simp []) >>
  rpt gen_tac >>
  Cases_on `c`
  >- (simp [listTheory.APPEND_ASSOC] >>
      strip_tac >>
      disj1_tac >>
      irule suffix_factor_base >>
      qexistsl [`b`, `[]`, `d`] >>
      simp []) >>
  strip_tac >>
  fs [listTheory.APPEND_ASSOC]
QED

Theorem smtstr_replace_raw_incomparable[local]:
  IS_SUBLIST s t /\ ~IS_SUBLIST t u /\ ~IS_SUBLIST u t ==>
  ~IS_SUBLIST s (smtstr_replace_raw s t u)
Proof
  strip_tac >>
  drule_then (qspec_then `u` strip_assume_tac)
    smtstr_replace_raw_hit >>
  CCONTR_TAC >>
  fs [] >>
  qpat_x_assum `IS_SUBLIST s (smtstr_replace_raw s t u)`
    (mp_tac o REWRITE_RULE [rich_listTheory.IS_SUBLIST_APPEND]) >>
  strip_tac >>
  qpat_x_assum `s = pre ++ t ++ post` SUBST_ALL_TAC >>
  qpat_x_assum
    `smtstr_replace_raw (pre ++ t ++ post) t u = pre ++ u ++ post`
    SUBST_ALL_TAC >>
  fs [listTheory.APPEND_ASSOC] >>
  qpat_x_assum
    `pre ++ t ++ post = _ ++ pre ++ u ++ post ++ _`
    (mp_tac o MATCH_MP replace_factor_comparable) >>
  simp [rich_listTheory.IS_SUBLIST_APPEND]
QED

Theorem smtstr_replace_incomparable_not_contained:
  smtstr_contains x y /\
  ~smtstr_contains y z /\
  ~smtstr_contains z y ==>
  ~smtstr_contains x (smtstr_replace x y z)
Proof
  rw [smtstr_contains_def, smtstr_rep_replace] >>
  metis_tac [smtstr_replace_raw_incomparable]
QED

Theorem smtstr_replace_nested_dual_ite1:
  ~smtstr_contains x z ==>
  smtstr_replace x (smtstr_replace x y z) w =
    if smtstr_contains x y then x else w
Proof
  strip_tac >>
  Cases_on `smtstr_contains x y`
  >- (`smtstr_contains (smtstr_replace x y z) z` by
        metis_tac [smtstr_replace_contains_replacement] >>
      `~smtstr_contains x (smtstr_replace x y z)` by
        (CCONTR_TAC >> metis_tac [smtstr_contains_trans]) >>
      simp [smtstr_replace_absent]) >>
  simp [smtstr_replace_absent, smtstr_replace_self]
QED

Theorem smtstr_replace_nested_dual_ite2:
  ~smtstr_contains y z /\ ~smtstr_contains z y ==>
  smtstr_replace x (smtstr_replace x y z) w =
    if smtstr_contains x y then x else w
Proof
  strip_tac >>
  Cases_on `smtstr_contains x y`
  >- (`~smtstr_contains x (smtstr_replace x y z)` by
        metis_tac [smtstr_replace_incomparable_not_contained] >>
      simp [smtstr_replace_absent]) >>
  simp [smtstr_replace_absent, smtstr_replace_self]
QED

(* TASK_02 draft_str_lt records irreflexivity and the two-direction
   comparison clause.  These facts give the strict/non-strict order kit. *)

Theorem LLEX_num_irrefl[local]:
  !l : num list. ~LLEX $< l l
Proof
  Induct >>
  simp [listTheory.LLEX_THM]
QED

Theorem LLEX_num_trichotomy[local]:
  !l1 l2 : num list. LLEX $< l1 l2 \/ l1 = l2 \/ LLEX $< l2 l1
Proof
  Induct >>
  Cases_on `l2` >>
  simp [listTheory.LLEX_THM] >>
  metis_tac [arithmeticTheory.LESS_LESS_CASES]
QED

Theorem smtstr_lt_irrefl:
  ~smtstr_lt s s
Proof
  simp [smtstr_lt_def, LLEX_num_irrefl]
QED

Theorem smtstr_lt_elim:
  smtstr_lt s t <=> ~(s = t) /\ smtstr_le s t
Proof
  simp [smtstr_le_def] >>
  metis_tac [smtstr_lt_irrefl]
QED

Theorem smtstr_lt_trans:
  smtstr_lt s t /\ smtstr_lt t u ==> smtstr_lt s u
Proof
  `transitive (LLEX ($< : num -> num -> bool))` by
    (irule listTheory.LLEX_transitive >>
     simp [relationTheory.transitive_def] >>
     decide_tac) >>
  fs [smtstr_lt_def] >>
  metis_tac [relationTheory.transitive_def]
QED

Theorem smtstr_lt_trichotomy:
  smtstr_lt s t \/ s = t \/ smtstr_lt t s
Proof
  simp [smtstr_lt_def] >>
  metis_tac [LLEX_num_trichotomy, smtstr_rep_11]
QED

Theorem smtstr_le_refl:
  smtstr_le s s
Proof
  simp [smtstr_le_def]
QED

Theorem smtstr_lt_imp_le:
  smtstr_lt s t ==> smtstr_le s t
Proof
  simp [smtstr_le_def]
QED

Theorem smtstr_le_trans:
  smtstr_le s t /\ smtstr_le t u ==> smtstr_le s u
Proof
  rw [smtstr_le_def] >>
  metis_tac [smtstr_lt_trans]
QED

Theorem smtstr_le_total:
  smtstr_le s t \/ smtstr_le t s
Proof
  metis_tac [smtstr_lt_trichotomy, smtstr_le_def]
QED

Theorem LLEX_num_common_prefix[local]:
  !p x y : num list.
    LLEX $< (p ++ x) (p ++ y) <=> LLEX $< x y
Proof
  Induct >> simp [listTheory.LLEX_def]
QED

Theorem LLEX_num_equal_length_tail[local]:
  !a b x y : num list.
    LENGTH a = LENGTH b /\ a <> b ==>
    (LLEX $< (a ++ x) (b ++ y) <=> LLEX $< a b)
Proof
  Induct >> Cases_on `b` >>
  simp [listTheory.LLEX_def] >>
  rw [] >>
  metis_tac []
QED

(* TASK_02 draft_substr couples str.at/substr with concat lengths and
   nonnegative tail lengths.  The following boundary lemmas expose all
   totalization branches without unfolding smtstr_substr in consumers. *)

Theorem smtstr_len_substr:
  smtstr_len (smtstr_substr s i n) =
    if i < 0 \/ n <= 0 \/ LENGTH (smtstr_rep s) <= Num i then 0
    else &(MIN (Num n) (LENGTH (smtstr_rep s) - Num i))
Proof
  rw [smtstr_len_def, smtstr_substr_def,
      smtstr_rep_def,
      listTheory.LENGTH_TAKE_EQ] >>
  simp [arithmeticTheory.MIN_DEF]
QED

Theorem smtstr_len_substr_source_bound:
  smtstr_len (smtstr_substr s i n) <= smtstr_len s
Proof
  rw [smtstr_len_substr, smtstr_len_def] >>
  simp [arithmeticTheory.MIN_DEF]
QED

Theorem smtstr_len_substr_count_bound:
  smtstr_len (smtstr_substr s i n) <= &(Num n)
Proof
  rw [smtstr_len_substr] >>
  simp [arithmeticTheory.MIN_DEF]
QED

Theorem smtstr_substr_positive_count[local]:
  0 <= n2 /\ 0 < m2 /\
  n2 + m2 <= smtstr_len (smtstr_substr s n1 m1) ==>
  0 < m1
Proof
  strip_tac >>
  Cases_on `m1 <= 0`
  >- (`smtstr_substr s n1 m1 = SmtStr []` by
        simp [smtstr_substr_def] >>
      `smtstr_len (smtstr_substr s n1 m1) = 0` by
        simp [smtstr_len_def, smtstr_rep_def] >>
      intLib.ARITH_TAC) >>
  intLib.ARITH_TAC
QED

Theorem smtstr_substr_combine_inner_bound:
  0 <= n1 /\ 0 <= n2 /\
  n2 + m2 <= smtstr_len (smtstr_substr s n1 m1) ==>
  smtstr_substr (smtstr_substr s n1 m1) n2 m2 =
  smtstr_substr s (n1 + n2) m2
Proof
  strip_tac >>
  Cases_on `m2 <= 0`
  >- simp [smtstr_substr_def] >>
  `0 < m2` by intLib.ARITH_TAC >>
  `0 < m1` by metis_tac [smtstr_substr_positive_count] >>
  `&(Num m1) = m1` by intLib.ARITH_TAC >>
  `smtstr_len (smtstr_substr s n1 m1) <= &(Num m1)` by
    metis_tac [smtstr_len_substr_count_bound] >>
  `0 <= (m1 - n2) - m2` by intLib.ARITH_TAC >>
  metis_tac [smtstr_substr_combine_left]
QED

Theorem smtstr_substr_combine_actual_nonpositive[local]:
  0 <= n1 /\ 0 <= n2 /\ 0 < m1 /\ m2 <= 0 /\
  smtstr_len (smtstr_substr s n1 m1) <= n2 + m2 ==>
  smtstr_substr (smtstr_substr s n1 m1) n2 m2 =
  smtstr_substr s (n1 + n2) (m1 - n2)
Proof
  strip_tac >>
  `smtstr_rep (smtstr_substr s n1 m1) =
     TAKE (Num m1) (DROP (Num n1) (smtstr_rep s))` by
    metis_tac [smtstr_rep_substr_positive] >>
  `smtstr_len (smtstr_substr s n1 m1) =
     &(LENGTH (smtstr_rep (smtstr_substr s n1 m1)))` by
    simp [smtstr_len_def] >>
  `&(Num n1) = n1 /\ &(Num n2) = n2` by intLib.ARITH_TAC >>
  `LENGTH (smtstr_rep (smtstr_substr s n1 m1)) <= Num n2` by
    intLib.ARITH_TAC >>
  `LENGTH (TAKE (Num m1) (DROP (Num n1) (smtstr_rep s))) =
   LENGTH (smtstr_rep (smtstr_substr s n1 m1))` by
    asm_rewrite_tac [] >>
  `LENGTH (TAKE (Num m1) (DROP (Num n1) (smtstr_rep s))) <=
   Num n2 + 0` by decide_tac >>
  `TAKE 0
     (DROP (Num n2)
       (TAKE (Num m1) (DROP (Num n1) (smtstr_rep s)))) =
   TAKE (Num m1 - Num n2)
     (DROP (Num n1 + Num n2) (smtstr_rep s))` by
    metis_tac [TAKE_DROP_TAKE_ACTUAL_BOUND] >>
  Cases_on `m1 - n2 <= 0`
  >- (`~(n1 + n2 < 0)` by intLib.ARITH_TAC >>
      `smtstr_substr (smtstr_substr s n1 m1) n2 m2 =
       SmtStr []` by simp [smtstr_substr_def] >>
      `smtstr_substr s (n1 + n2) (m1 - n2) = SmtStr []` by
        simp [smtstr_substr_def] >>
      metis_tac []) >>
  `0 < m1 - n2 /\ 0 <= n1 + n2` by intLib.ARITH_TAC >>
  `Num (m1 - n2) = Num m1 - Num n2 /\
   Num (n1 + n2) = Num n1 + Num n2` by intLib.ARITH_TAC >>
  `smtstr_rep (smtstr_substr s (n1 + n2) (m1 - n2)) =
     TAKE (Num (m1 - n2))
       (DROP (Num (n1 + n2)) (smtstr_rep s))` by
    metis_tac [smtstr_rep_substr_positive] >>
  `TAKE (Num m1 - Num n2)
     (DROP (Num n1 + Num n2) (smtstr_rep s)) = []` by
    metis_tac [listTheory.TAKE_0] >>
  `smtstr_rep
     (smtstr_substr (smtstr_substr s n1 m1) n2 m2) = []` by
    metis_tac [smtstr_rep_substr_nonpositive] >>
  irule (iffLR smtstr_rep_11) >>
  metis_tac []
QED

Theorem smtstr_substr_combine_actual_positive[local]:
  0 <= n1 /\ 0 <= n2 /\ 0 < m1 /\ 0 < m2 /\
  smtstr_len (smtstr_substr s n1 m1) <= n2 + m2 ==>
  smtstr_substr (smtstr_substr s n1 m1) n2 m2 =
  smtstr_substr s (n1 + n2) (m1 - n2)
Proof
  strip_tac >>
  `smtstr_rep (smtstr_substr s n1 m1) =
     TAKE (Num m1) (DROP (Num n1) (smtstr_rep s))` by
    metis_tac [smtstr_rep_substr_positive] >>
  `smtstr_len (smtstr_substr s n1 m1) =
     &(LENGTH (smtstr_rep (smtstr_substr s n1 m1)))` by
    simp [smtstr_len_def] >>
  `&(Num n1) = n1 /\ &(Num n2) = n2 /\ &(Num m2) = m2` by
    intLib.ARITH_TAC >>
  `LENGTH (smtstr_rep (smtstr_substr s n1 m1)) <=
   Num n2 + Num m2` by intLib.ARITH_TAC >>
  `LENGTH (TAKE (Num m1) (DROP (Num n1) (smtstr_rep s))) =
   LENGTH (smtstr_rep (smtstr_substr s n1 m1))` by
    asm_rewrite_tac [] >>
  `LENGTH (TAKE (Num m1) (DROP (Num n1) (smtstr_rep s))) <=
   Num n2 + Num m2` by decide_tac >>
  `smtstr_rep
     (smtstr_substr (smtstr_substr s n1 m1) n2 m2) =
   TAKE (Num m2)
     (DROP (Num n2) (smtstr_rep (smtstr_substr s n1 m1)))` by
    metis_tac [smtstr_rep_substr_positive] >>
  `TAKE (Num m2)
     (DROP (Num n2)
       (TAKE (Num m1) (DROP (Num n1) (smtstr_rep s)))) =
   TAKE (Num m1 - Num n2)
     (DROP (Num n1 + Num n2) (smtstr_rep s))` by
    metis_tac [TAKE_DROP_TAKE_ACTUAL_BOUND] >>
  Cases_on `m1 - n2 <= 0`
  >- (`Num m1 <= Num n2` by intLib.ARITH_TAC >>
      `Num m1 - Num n2 = 0` by decide_tac >>
      `smtstr_rep
         (smtstr_substr s (n1 + n2) (m1 - n2)) = []` by
        metis_tac [smtstr_rep_substr_nonpositive] >>
      irule (iffLR smtstr_rep_11) >>
      metis_tac [listTheory.TAKE_0]) >>
  `0 < m1 - n2 /\ 0 <= n1 + n2` by intLib.ARITH_TAC >>
  `Num (m1 - n2) = Num m1 - Num n2 /\
   Num (n1 + n2) = Num n1 + Num n2` by intLib.ARITH_TAC >>
  `smtstr_rep (smtstr_substr s (n1 + n2) (m1 - n2)) =
     TAKE (Num (m1 - n2))
       (DROP (Num (n1 + n2)) (smtstr_rep s))` by
    metis_tac [smtstr_rep_substr_positive] >>
  irule (iffLR smtstr_rep_11) >>
  metis_tac []
QED

Theorem smtstr_substr_combine_actual_bound:
  0 <= n1 /\ 0 <= n2 /\
  smtstr_len (smtstr_substr s n1 m1) <= n2 + m2 ==>
  smtstr_substr (smtstr_substr s n1 m1) n2 m2 =
  smtstr_substr s (n1 + n2) (m1 - n2)
Proof
  strip_tac >>
  Cases_on `m1 <= 0`
  >- (`~(n1 < 0) /\ ~(n2 < 0) /\ ~(n1 + n2 < 0) /\
       m1 - n2 <= 0` by intLib.ARITH_TAC >>
      simp [smtstr_substr_def]) >>
  `0 < m1` by intLib.ARITH_TAC >>
  Cases_on `m2 <= 0`
  >- metis_tac [smtstr_substr_combine_actual_nonpositive] >>
  `0 < m2` by intLib.ARITH_TAC >>
  metis_tac [smtstr_substr_combine_actual_positive]
QED

Theorem smtstr_substr_drop_concat_prefix:
  smtstr_len s1 <= n ==>
  smtstr_substr (smtstr_concat (smtstr_concat s1 s2) s3) n m =
  smtstr_substr (smtstr_concat s2 s3) (n - smtstr_len s1) m
Proof
  strip_tac >>
  `smtstr_len s1 = &(LENGTH (smtstr_rep s1))` by
    simp [smtstr_len_def] >>
  `0 <= n /\ 0 <= n - smtstr_len s1` by intLib.ARITH_TAC >>
  `&(Num n) = n /\
   &(Num (n - smtstr_len s1)) = n - smtstr_len s1` by
    intLib.ARITH_TAC >>
  `Num n = LENGTH (smtstr_rep s1) +
     Num (n - smtstr_len s1)` by intLib.ARITH_TAC >>
  irule (iffLR smtstr_rep_11) >>
  Cases_on `m <= 0`
  >- (`smtstr_rep
         (smtstr_substr
           (smtstr_concat (smtstr_concat s1 s2) s3) n m) = []` by
        metis_tac [smtstr_rep_substr_nonpositive] >>
      `smtstr_rep
         (smtstr_substr (smtstr_concat s2 s3)
           (n - smtstr_len s1) m) = []` by
        metis_tac [smtstr_rep_substr_nonpositive] >>
      metis_tac []) >>
  `0 < m` by intLib.ARITH_TAC >>
  `smtstr_rep
     (smtstr_substr
       (smtstr_concat (smtstr_concat s1 s2) s3) n m) =
   TAKE (Num m)
     (DROP (Num n)
       (smtstr_rep
         (smtstr_concat (smtstr_concat s1 s2) s3)))` by
    metis_tac [smtstr_rep_substr_positive] >>
  `smtstr_rep
     (smtstr_substr (smtstr_concat s2 s3)
       (n - smtstr_len s1) m) =
   TAKE (Num m)
     (DROP (Num (n - smtstr_len s1))
       (smtstr_rep (smtstr_concat s2 s3)))` by
    metis_tac [smtstr_rep_substr_positive] >>
  `smtstr_rep (smtstr_concat (smtstr_concat s1 s2) s3) =
     smtstr_rep s1 ++ smtstr_rep s2 ++ smtstr_rep s3` by
    simp [smtstr_concat_def, smtstr_rep_def] >>
  `smtstr_rep (smtstr_concat s2 s3) =
     smtstr_rep s2 ++ smtstr_rep s3` by
    simp [smtstr_concat_def, smtstr_rep_def] >>
  `DROP (Num n)
     (smtstr_rep s1 ++ smtstr_rep s2 ++ smtstr_rep s3) =
   DROP (Num (n - smtstr_len s1))
     (smtstr_rep s2 ++ smtstr_rep s3)` by
    simp [listTheory.DROP_APPEND] >>
  metis_tac []
QED

Theorem smtstr_substr_concat_left_bound:
  n + m <= smtstr_len s1 ==>
  smtstr_substr (smtstr_concat s1 s2) n m =
  smtstr_substr s1 n m
Proof
  strip_tac >>
  Cases_on `n < 0 \/ m <= 0`
  >- fs [smtstr_substr_def] >>
  `0 <= n /\ 0 < m` by intLib.ARITH_TAC >>
  `Num n + Num m <= LENGTH (smtstr_rep s1) /\
   Num n <= LENGTH (smtstr_rep s1)` by
    (fs [smtstr_len_def] >> intLib.ARITH_TAC) >>
  `Num n < LENGTH (smtstr_rep s1)` by intLib.ARITH_TAC >>
  `Num m <= LENGTH (DROP (Num n) (smtstr_rep s1))` by
    simp [listTheory.LENGTH_DROP] >>
  simp [smtstr_substr_def, smtstr_concat_def, smtstr_rep_def,
        listTheory.DROP_APPEND1, listTheory.TAKE_APPEND1]
QED

Theorem smtstr_substr_nested_empty:
  n <= i ==>
  smtstr_substr (smtstr_substr s j n) i k = SmtStr []
Proof
  strip_tac >>
  Cases_on `n <= 0`
  >- simp [smtstr_substr_def] >>
  `0 < n` by intLib.ARITH_TAC >>
  `&(Num n) = n` by intLib.ARITH_TAC >>
  irule smtstr_substr_empty_start >>
  irule integerTheory.INT_LE_TRANS >>
  qexists_tac `&(Num n)` >>
  simp [smtstr_len_substr_count_bound] >>
  intLib.ARITH_TAC
QED

Theorem smtstr_substr_zero_eq_empty:
  smtstr_len s <> 0 /\ smtstr_len r = 0 ==>
  (smtstr_substr s 0 m = r <=> m <= 0)
Proof
  rw [smtstr_len_eq_zero] >>
  eq_tac
  >- (strip_tac >>
      CCONTR_TAC >>
      fs [] >>
      `0 < Num m` by intLib.ARITH_TAC >>
      `0 < LENGTH (smtstr_rep s)` by
        (Cases_on `smtstr_rep s` >> fs [smtstr_rep_eq_nil]) >>
      qpat_x_assum `smtstr_substr s 0 m = SmtStr []`
        (assume_tac o AP_TERM ``smtstr_len``) >>
      fs [smtstr_len_substr, smtstr_rep_eq_nil,
          smtstr_len_def, arithmeticTheory.MIN_DEF] >>
      Cases_on `Num m < LENGTH (smtstr_rep s)` >> rfs [])
  >- (strip_tac >>
      simp [smtstr_substr_def])
QED

Theorem smtstr_substr_zero_empty_iff:
  0 < m /\ smtstr_len r = 0 ==>
  (smtstr_substr s 0 m = r <=> s = r)
Proof
  strip_tac >>
  Cases_on `smtstr_len s = 0`
  >- fs [smtstr_len_eq_zero, smtstr_substr_def] >>
  `smtstr_substr s 0 m = r <=> m <= 0` by
    metis_tac [smtstr_substr_zero_eq_empty] >>
  `s <> r` by metis_tac [] >>
  fs [integerTheory.INT_NOT_LE]
QED

Theorem smtstr_substr_eq_empty_start:
  0 <= i /\ 0 < n ==>
  (smtstr_substr s i n = SmtStr [] <=> smtstr_len s <= i)
Proof
  strip_tac >>
  rw [GSYM smtstr_len_eq_zero, smtstr_len_substr,
      smtstr_len_def] >>
  `~(i < 0) /\ ~(n <= 0) /\ &(Num i) = i /\ &(Num n) = n` by
    intLib.ARITH_TAC >>
  simp [arithmeticTheory.MIN_EQ_0] >>
  intLib.ARITH_TAC
QED

Theorem smtstr_substr_eq_empty:
  0 <= i ==> 0 < n ==> smtstr_len empty = 0 ==>
  (smtstr_substr s i n = empty <=> smtstr_len s <= i)
Proof
  rw [smtstr_len_eq_zero, smtstr_substr_eq_empty_start]
QED

Theorem smtstr_substr_prefix:
  0 <= n ==>
  smtstr_substr s 0 n = SmtStr (TAKE (Num n) (smtstr_rep s))
Proof
  strip_tac >>
  Cases_on `n = 0`
  >- simp [smtstr_substr_def] >>
  `~(n <= 0)` by intLib.ARITH_TAC >>
  Cases_on `smtstr_rep s` >> simp [smtstr_substr_def]
QED

Theorem smtstr_substr_concat_prefix_bound:
  smtstr_len s1 <= n ==>
  smtstr_substr (smtstr_concat s1 tail) 0 n =
  smtstr_concat s1
    (smtstr_substr tail 0 (n - smtstr_len s1))
Proof
  strip_tac >>
  `0 <= smtstr_len s1` by metis_tac [smtstr_len_nonnegative] >>
  `0 <= n /\ 0 <= n - smtstr_len s1` by intLib.ARITH_TAC >>
  `Num n = LENGTH (smtstr_rep s1) +
     Num (n - smtstr_len s1)` by
    (fs [smtstr_len_def] >> intLib.ARITH_TAC) >>
  simp [smtstr_substr_prefix, smtstr_concat_def,
        smtstr_rep_def, rich_listTheory.TAKE_APPEND,
        rich_listTheory.EVERY_TAKE,
        listTheory.TAKE_LENGTH_TOO_LONG]
QED

Theorem smtstr_substr_suffix:
  0 <= i /\ i < smtstr_len s ==>
  smtstr_substr s i (smtstr_len s) =
    SmtStr (DROP (Num i) (smtstr_rep s))
Proof
  strip_tac >>
  `~(i < 0) /\ 0 < smtstr_len s /\
   Num i < LENGTH (smtstr_rep s)` by
    (fs [smtstr_len_def] >> intLib.ARITH_TAC) >>
  `smtstr_rep s <> []` by
    (Cases_on `smtstr_rep s` >> fs [smtstr_len_def]) >>
  simp [smtstr_substr_def, smtstr_len_def,
        listTheory.TAKE_LENGTH_TOO_LONG]
QED

Theorem smtstr_substr_count_normalize:
  smtstr_len s <= m ==>
  smtstr_substr s n m =
  smtstr_substr s n (smtstr_len s)
Proof
  strip_tac >>
  Cases_on `n < 0`
  >- simp [smtstr_substr_def] >>
  `0 <= n` by intLib.ARITH_TAC >>
  Cases_on `smtstr_len s <= n`
  >- simp [smtstr_substr_empty_start] >>
  `0 <= smtstr_len s` by metis_tac [smtstr_len_nonnegative] >>
  `n < smtstr_len s /\ 0 < smtstr_len s /\ 0 < m` by
    intLib.ARITH_TAC >>
  `&(Num m) = m` by intLib.ARITH_TAC >>
  `LENGTH (smtstr_rep s) <= Num m` by
    (fs [smtstr_len_def] >> intLib.ARITH_TAC) >>
  `LENGTH (DROP (Num n) (smtstr_rep s)) <= Num m` by
    simp [listTheory.LENGTH_DROP] >>
  `smtstr_rep (smtstr_substr s n m) =
   DROP (Num n) (smtstr_rep s)` by
    metis_tac [smtstr_rep_substr_positive,
               listTheory.TAKE_LENGTH_TOO_LONG] >>
  `smtstr_substr s n m =
   SmtStr (DROP (Num n) (smtstr_rep s))` by
    metis_tac [SmtStr_smtstr_rep] >>
  metis_tac [smtstr_substr_suffix]
QED

Theorem smtstr_replace_find:
  0 <= smtstr_indexof s t 0 ==>
  smtstr_replace s t r =
  smtstr_concat (smtstr_substr s 0 (smtstr_indexof s t 0))
    (smtstr_concat r
      (smtstr_substr s
        (smtstr_indexof s t 0 + smtstr_len t)
        (smtstr_len s)))
Proof
  strip_tac >>
  fs [smtstr_indexof_def] >>
  Cases_on `smtstr_indexof_aux (smtstr_rep t) 0 (smtstr_rep s)` >>
  fs [] >>
  drule smtstr_indexof_aux_split >>
  strip_tac >>
  qpat_x_assum `LENGTH pre + 0 = x` (SUBST_ALL_TAC o SYM) >>
  fs [] >>
  `smtstr_rep (smtstr_substr s 0 (&(LENGTH pre))) = pre` by
    (irule smtstr_rep_substr_prefix_split >>
     qexists_tac `smtstr_rep t ++ post` >>
     simp []) >>
  `smtstr_rep
     (smtstr_substr s
       (&(LENGTH pre) + smtstr_len t) (smtstr_len s)) = post` by
    (`&(LENGTH pre) + smtstr_len t =
      &(LENGTH pre + LENGTH (smtstr_rep t))` by
        (simp [smtstr_len_def] >> intLib.ARITH_TAC) >>
     metis_tac [smtstr_rep_substr_suffix_split]) >>
  irule (iffLR smtstr_rep_11) >>
  PURE_REWRITE_TAC [smtstr_rep_replace, smtstr_rep_concat] >>
  asm_rewrite_tac [] >>
  simp [smtstr_replace_raw_def, listTheory.TAKE_APPEND1,
        rich_listTheory.TAKE_LENGTH_APPEND,
        rich_listTheory.DROP_LENGTH_APPEND] >>
  `LENGTH pre + LENGTH (smtstr_rep t) =
   LENGTH (pre ++ smtstr_rep t)` by simp [] >>
  asm_rewrite_tac [] >>
  simp [rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem smtstr_substr_to_end:
  0 <= i /\ i < smtstr_len s ==>
  smtstr_substr s i (smtstr_len s - i) =
    SmtStr (DROP (Num i) (smtstr_rep s))
Proof
  strip_tac >>
  `~(i < 0) /\ 0 < smtstr_len s - i /\
   Num i < LENGTH (smtstr_rep s)` by
    (fs [smtstr_len_def] >> intLib.ARITH_TAC) >>
  `Num (smtstr_len s - i) =
   LENGTH (smtstr_rep s) - Num i` by
    (fs [smtstr_len_def] >> intLib.ARITH_TAC) >>
  `~(smtstr_len s - i <= 0)` by intLib.ARITH_TAC >>
  simp [smtstr_substr_def, listTheory.TAKE_LENGTH_TOO_LONG]
QED

Triviality take_drop_split3:
  TAKE i xs ++ TAKE n (DROP i xs) ++ DROP (i + n) xs = xs
Proof
  rpt gen_tac >>
  `DROP (i + n) xs = DROP n (DROP i xs)` by
    simp [rich_listTheory.DROP_DROP_T, arithmeticTheory.ADD_COMM] >>
  asm_rewrite_tac [] >>
  metis_tac [listTheory.TAKE_DROP, listTheory.APPEND_ASSOC]
QED

Triviality smtstr_substr_reduction_partition:
  0 <= i /\ smtstr_len s > i /\ 0 < n ==>
  s =
    smtstr_concat
      (smtstr_concat (smtstr_substr s 0 i) (smtstr_substr s i n))
      (smtstr_substr s (i + n) (smtstr_len s - (i + n)))
Proof
  strip_tac >>
  `~(i < 0) /\ ~(n <= 0) /\ 0 <= i + n` by intLib.ARITH_TAC >>
  `&(Num i) = i /\ &(Num n) = n /\
   Num i < LENGTH (smtstr_rep s)` by
    (fs [smtstr_len_def] >> intLib.ARITH_TAC) >>
  `Num (i + n) = Num i + Num n` by intLib.ARITH_TAC >>
  `smtstr_substr s 0 i = SmtStr (TAKE (Num i) (smtstr_rep s))` by
    metis_tac [smtstr_substr_prefix] >>
  `smtstr_substr s i n =
     SmtStr (TAKE (Num n) (DROP (Num i) (smtstr_rep s)))` by
    simp [smtstr_substr_def] >>
  `smtstr_substr s (i + n) (smtstr_len s - (i + n)) =
     SmtStr (DROP (Num (i + n)) (smtstr_rep s))` by
    (Cases_on `i + n < smtstr_len s`
     >- metis_tac [smtstr_substr_to_end]
     >> `smtstr_len s <= i + n` by intLib.ARITH_TAC >>
        `smtstr_substr s (i + n) (smtstr_len s - (i + n)) =
           SmtStr []` by metis_tac [smtstr_substr_empty_start] >>
        `LENGTH (smtstr_rep s) <= Num (i + n)` by
          (fs [smtstr_len_def] >> intLib.ARITH_TAC) >>
        simp [listTheory.DROP_LENGTH_TOO_LONG]) >>
  `EVERY (\c. c <= 196607) (TAKE (Num i) (smtstr_rep s)) /\
   EVERY (\c. c <= 196607)
     (DROP (Num i + Num n) (smtstr_rep s))` by
    simp [rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP] >>
  irule (iffLR smtstr_rep_11) >>
  simp [smtstr_concat_def, smtstr_rep_def,
        rich_listTheory.DROP_DROP_T, take_drop_split3]
QED

(* Checked counterpart of cvc5's STRING_REDUCTION rule for substring.
   The CPC parser represents each proof-local purification skolem by the
   substring that witnesses it, so the reduction becomes this semantic
   decomposition theorem. *)
Theorem smtstr_substr_reduction:
  (if 0 <= i /\ smtstr_len s > i /\ 0 < n then
     s =
       smtstr_concat
         (smtstr_concat (smtstr_substr s 0 i)
           (smtstr_substr s i n))
         (smtstr_substr s (i + n) (smtstr_len s - (i + n))) /\
     smtstr_len (smtstr_substr s 0 i) = i /\
     (smtstr_len
        (smtstr_substr s (i + n) (smtstr_len s - (i + n))) =
          smtstr_len s - (i + n) \/
      smtstr_len
        (smtstr_substr s (i + n) (smtstr_len s - (i + n))) = 0) /\
     smtstr_len (smtstr_substr s i n) <= n
   else
     smtstr_substr s i n = SmtStr []) /\
  smtstr_substr s i n = smtstr_substr s i n
Proof
  rw []
  >- metis_tac [smtstr_substr_reduction_partition]
  >- (`Num i < LENGTH (smtstr_rep s)` by
        (fs [smtstr_len_def] >> intLib.ARITH_TAC) >>
      simp [smtstr_substr_prefix, smtstr_len_def, smtstr_rep_def,
            rich_listTheory.EVERY_TAKE, listTheory.LENGTH_TAKE,
            arithmeticTheory.MIN_DEF])
  >- (Cases_on `i + n < smtstr_len s`
      >- (disj1_tac >>
          `0 <= i + n /\ 0 < smtstr_len s - (i + n) /\
           Num (i + n) < LENGTH (smtstr_rep s)` by
            (fs [smtstr_len_def] >> intLib.ARITH_TAC) >>
          `Num (smtstr_len s - (i + n)) =
           LENGTH (smtstr_rep s) - Num (i + n)` by
            (fs [smtstr_len_def] >> intLib.ARITH_TAC) >>
          simp [smtstr_len_substr, smtstr_len_def,
                arithmeticTheory.MIN_DEF] >>
          intLib.ARITH_TAC)
      >> disj2_tac >>
         `smtstr_len s <= i + n` by intLib.ARITH_TAC >>
         `smtstr_substr s (i + n) (smtstr_len s - (i + n)) =
          SmtStr []` by metis_tac [smtstr_substr_empty_start] >>
         simp [smtstr_len_def, smtstr_rep_def])
  >- (`&(Num n) = n` by intLib.ARITH_TAC >>
      metis_tac [smtstr_len_substr_count_bound])
  >> Cases_on `i < 0`
  >- simp [smtstr_substr_def]
  >> Cases_on `n <= 0`
  >- simp [smtstr_substr_def]
  >> `smtstr_len s <= i` by intLib.ARITH_TAC >>
     metis_tac [smtstr_substr_empty_start]
QED

Theorem smtstr_contains_substr:
  smtstr_contains s (smtstr_substr s i n)
Proof
  rw [smtstr_contains_def, smtstr_rep_substr,
      rich_listTheory.IS_SUBLIST_APPEND]
  >- (qexistsl [`[]`, `smtstr_rep s`] >> simp [])
  >- (qexistsl [`[]`, `smtstr_rep s`] >> simp [])
  >- (qexistsl [`[]`, `smtstr_rep s`] >> simp []) >>
  qexistsl [`TAKE (Num i) (smtstr_rep s)`,
            `DROP (Num n) (DROP (Num i) (smtstr_rep s))`] >>
  metis_tac [listTheory.TAKE_DROP, listTheory.APPEND_ASSOC]
QED

Theorem smtstr_substr_contains_contra:
  ~smtstr_contains t s ==>
  ~smtstr_contains (smtstr_substr t n m) s
Proof
  metis_tac [smtstr_contains_substr, smtstr_contains_trans]
QED

Theorem smtstr_substr_short_self_count:
  smtstr_len x <= 1 ==>
  smtstr_substr x n n = SmtStr []
Proof
  strip_tac >>
  Cases_on `n <= 0`
  >- simp [smtstr_substr_def] >>
  `1 <= n` by intLib.ARITH_TAC >>
  `smtstr_len x <= n` by intLib.ARITH_TAC >>
  metis_tac [smtstr_substr_empty_start]
QED

Theorem smtstr_suffixof_substr:
  smtstr_suffixof s t <=>
  (s = smtstr_substr t (smtstr_len t - smtstr_len s)
    (smtstr_len s))
Proof
  eq_tac
  >- (rw [smtstr_suffixof_decompose] >>
      simp [smtstr_substr_def, smtstr_len_def,
            smtstr_concat_def, smtstr_rep_def] >>
      `(&(LENGTH (smtstr_rep s) + LENGTH (smtstr_rep u)) : int) -
       &(LENGTH (smtstr_rep s)) = &(LENGTH (smtstr_rep u))` by
        intLib.ARITH_TAC >>
      Cases_on `smtstr_rep s` >>
      simp [smtstr_rep_eq_nil, rich_listTheory.DROP_LENGTH_APPEND] >>
      metis_tac [SmtStr_smtstr_rep]) >>
  strip_tac >>
  Cases_on `s = SmtStr []`
  >- (simp [smtstr_suffixof_decompose] >>
      qexists `t` >> simp [smtstr_concat_nil_right]) >>
  `0 < smtstr_len s` by
    (`0 <= smtstr_len s` by simp [smtstr_len_nonnegative] >>
     `smtstr_len s <> 0` by metis_tac [smtstr_len_eq_zero] >>
     intLib.ARITH_TAC) >>
  `smtstr_len s <= smtstr_len t` by
    (spose_not_then assume_tac >>
     `smtstr_len t - smtstr_len s < 0` by intLib.ARITH_TAC >>
     fs [smtstr_substr_empty_start_neg]) >>
  `0 <= smtstr_len t - smtstr_len s /\
   smtstr_len t - smtstr_len s < smtstr_len t` by
    intLib.ARITH_TAC >>
  `smtstr_len s =
   smtstr_len t - (smtstr_len t - smtstr_len s)` by
    intLib.ARITH_TAC >>
  `s = SmtStr (DROP (Num (smtstr_len t - smtstr_len s))
     (smtstr_rep t))` by
    metis_tac [smtstr_substr_to_end] >>
  `EVERY (\c. c <= 196607)
     (DROP (Num (smtstr_len t - smtstr_len s)) (smtstr_rep t))` by
    simp [rich_listTheory.EVERY_DROP] >>
  `smtstr_rep s = DROP (Num (smtstr_len t - smtstr_len s))
     (smtstr_rep t)` by
    metis_tac [smtstr_rep_def] >>
  rw [smtstr_suffixof_decompose] >>
  qexists `SmtStr (TAKE (Num (smtstr_len t - smtstr_len s))
    (smtstr_rep t))` >>
  simp [smtstr_concat_def, smtstr_rep_def,
        rich_listTheory.EVERY_TAKE, listTheory.TAKE_DROP] >>
  metis_tac [SmtStr_smtstr_rep]
QED

Theorem smtstr_suffixof_length_bound:
  smtstr_len t <= smtstr_len s ==>
  (smtstr_suffixof s t <=> s = t)
Proof
  strip_tac >>
  rw [smtstr_suffixof_decompose] >>
  eq_tac
  >- (strip_tac >>
      `smtstr_len t = smtstr_len u + smtstr_len s` by
        simp [smtstr_len_concat] >>
      `smtstr_len u = 0` by
        (`0 <= smtstr_len u` by
           simp [smtstr_len_nonnegative] >>
         intLib.ARITH_TAC) >>
      fs [smtstr_len_eq_zero, smtstr_concat_nil_left]) >>
  strip_tac >>
  qexists `SmtStr []` >>
  simp [smtstr_concat_nil_left]
QED

Theorem smtstr_suffixof_length_one:
  smtstr_len t = 1 ==>
  (smtstr_suffixof s t <=> smtstr_contains t s)
Proof
  strip_tac >>
  eq_tac
  >- metis_tac [smtstr_suffixof_imp_contains] >>
  rw [smtstr_contains_decompose] >>
  Cases_on `s = SmtStr []`
  >- (simp [smtstr_suffixof_decompose] >>
      qexists `smtstr_concat u v` >>
      simp [smtstr_concat_nil_left, smtstr_concat_nil_right]) >>
  `0 < smtstr_len s` by
    (`0 <= smtstr_len s` by simp [smtstr_len_nonnegative] >>
     `smtstr_len s <> 0` by metis_tac [smtstr_len_eq_zero] >>
     intLib.ARITH_TAC) >>
  `1 = smtstr_len u + smtstr_len s + smtstr_len v` by
    (fs [smtstr_len_concat] >> intLib.ARITH_TAC) >>
  `0 <= smtstr_len u /\ 0 <= smtstr_len v` by
    simp [smtstr_len_nonnegative] >>
  `smtstr_len u = 0 /\ smtstr_len v = 0` by intLib.ARITH_TAC >>
  fs [smtstr_len_eq_zero, smtstr_concat_nil_left,
      smtstr_concat_nil_right, smtstr_suffixof_refl]
QED

Theorem smtstr_update_concat_first:
  0 <= i /\ i + smtstr_len u < smtstr_len s ==>
  smtstr_update (smtstr_concat s tail) i u =
    smtstr_concat
      (smtstr_concat
        (smtstr_concat (smtstr_substr s 0 i) u)
        (smtstr_substr s (i + smtstr_len u) (smtstr_len s)))
      tail
Proof
  strip_tac >>
  `~(i < 0) /\ 0 <= i + smtstr_len u /\
   Num (i + smtstr_len u) = Num i + LENGTH (smtstr_rep u) /\
   Num (smtstr_len s) = LENGTH (smtstr_rep s) /\
   Num i + LENGTH (smtstr_rep u) < LENGTH (smtstr_rep s)` by
    (fs [smtstr_len_def] >> intLib.ARITH_TAC) >>
  simp [smtstr_substr_prefix, smtstr_substr_suffix] >>
  simp [smtstr_update_def, smtstr_concat_def, smtstr_rep_def] >>
  simp [smtstr_rep_def, rich_listTheory.EVERY_TAKE,
        rich_listTheory.EVERY_DROP, listTheory.TAKE_APPEND1,
        listTheory.DROP_APPEND1, listTheory.TAKE_LENGTH_TOO_LONG]
QED

Theorem smtstr_concat_left_cancel:
  (smtstr_concat s x = smtstr_concat s y) <=> (x = y)
Proof
  eq_tac
  >- (strip_tac >>
      pop_assum (assume_tac o AP_TERM ``smtstr_rep``) >>
      qpat_x_assum `smtstr_rep (smtstr_concat s x) =
        smtstr_rep (smtstr_concat s y)` mp_tac >>
      PURE_REWRITE_TAC [smtstr_rep_concat,
        CONJUNCT1 listTheory.APPEND_11] >>
      REWRITE_TAC [smtstr_rep_11])
  >- simp []
QED

Theorem smtstr_concat_right_cancel:
  (smtstr_concat x s = smtstr_concat y s) <=> (x = y)
Proof
  eq_tac
  >- (strip_tac >>
      pop_assum (assume_tac o AP_TERM ``smtstr_rep``) >>
      qpat_x_assum `smtstr_rep (smtstr_concat x s) =
        smtstr_rep (smtstr_concat y s)` mp_tac >>
      PURE_REWRITE_TAC [smtstr_rep_concat,
        CONJUNCT2 listTheory.APPEND_11] >>
      REWRITE_TAC [smtstr_rep_11])
  >- simp []
QED

Theorem smtstr_concat_equal_prefix_lengths:
  smtstr_len s = smtstr_len t ==>
  ((smtstr_concat s x = smtstr_concat t y) <=>
   (s = t) /\ (x = y))
Proof
  strip_tac >>
  `LENGTH (smtstr_rep s) = LENGTH (smtstr_rep t)` by
    fs [smtstr_len_def] >>
  `(smtstr_rep s ++ smtstr_rep x = smtstr_rep t ++ smtstr_rep y) <=>
   (smtstr_rep s = smtstr_rep t) /\
   (smtstr_rep x = smtstr_rep y)` by
    (irule (CONJUNCT1 listTheory.APPEND_11_LENGTH) >> simp []) >>
  eq_tac
  >- (strip_tac >>
      pop_assum (assume_tac o AP_TERM ``smtstr_rep``) >>
      qpat_x_assum `smtstr_rep (smtstr_concat s x) =
        smtstr_rep (smtstr_concat t y)` mp_tac >>
      PURE_REWRITE_TAC [smtstr_rep_concat] >>
      strip_tac >>
      metis_tac [smtstr_rep_11])
  >- simp []
QED

Theorem smtstr_concat_equal_suffix_lengths:
  smtstr_len s = smtstr_len t ==>
  ((smtstr_concat x s = smtstr_concat y t) <=>
   (x = y) /\ (s = t))
Proof
  strip_tac >>
  `LENGTH (smtstr_rep s) = LENGTH (smtstr_rep t)` by
    fs [smtstr_len_def] >>
  `(smtstr_rep x ++ smtstr_rep s =
    smtstr_rep y ++ smtstr_rep t) <=>
   (smtstr_rep x = smtstr_rep y) /\
   (smtstr_rep s = smtstr_rep t)` by
    (irule (CONJUNCT2 listTheory.APPEND_11_LENGTH) >> simp []) >>
  eq_tac
  >- (strip_tac >>
      pop_assum (assume_tac o AP_TERM ``smtstr_rep``) >>
      qpat_x_assum `smtstr_rep (smtstr_concat x s) =
        smtstr_rep (smtstr_concat y t)` mp_tac >>
      PURE_REWRITE_TAC [smtstr_rep_concat] >>
      strip_tac >>
      metis_tac [smtstr_rep_11])
  >- simp []
QED

Theorem smtstr_equal_concat_same_prefix_length:
  smtstr_len s = smtstr_len t ==>
  ((s = smtstr_concat t y) <=>
   (s = t) /\ (y = SmtStr []))
Proof
  strip_tac >>
  `LENGTH (smtstr_rep s) = LENGTH (smtstr_rep t)` by
    fs [smtstr_len_def] >>
  `(smtstr_rep s ++ [] = smtstr_rep t ++ smtstr_rep y) <=>
   (smtstr_rep s = smtstr_rep t) /\
   ([] = smtstr_rep y)` by
    (irule (CONJUNCT1 listTheory.APPEND_11_LENGTH) >> simp []) >>
  eq_tac
  >- (strip_tac >>
      pop_assum (assume_tac o AP_TERM ``smtstr_rep``) >>
      `smtstr_rep s ++ [] = smtstr_rep t ++ smtstr_rep y` by
        fs [] >>
      metis_tac [smtstr_rep_11, smtstr_rep_eq_nil])
  >- simp [smtstr_concat_nil_right]
QED

Theorem smtstr_equal_concat_same_suffix_length:
  smtstr_len s = smtstr_len t ==>
  ((s = smtstr_concat y t) <=>
   (s = t) /\ (y = SmtStr []))
Proof
  strip_tac >>
  `LENGTH (smtstr_rep s) = LENGTH (smtstr_rep t)` by
    fs [smtstr_len_def] >>
  `([] ++ smtstr_rep s = smtstr_rep y ++ smtstr_rep t) <=>
   ([] = smtstr_rep y) /\
   (smtstr_rep s = smtstr_rep t)` by
    (irule (CONJUNCT2 listTheory.APPEND_11_LENGTH) >> simp []) >>
  eq_tac
  >- (strip_tac >>
      pop_assum (assume_tac o AP_TERM ``smtstr_rep``) >>
      `[] ++ smtstr_rep s = smtstr_rep y ++ smtstr_rep t` by
        fs [] >>
      metis_tac [smtstr_rep_11, smtstr_rep_eq_nil])
  >- simp [smtstr_concat_nil_left]
QED

Theorem smtstr_concat_common_prefix:
  (smtstr_concat (smtstr_concat s x) y =
   smtstr_concat (smtstr_concat s u) v) <=>
  (smtstr_concat x y = smtstr_concat u v)
Proof
  simp [smtstr_concat_assoc, smtstr_concat_left_cancel]
QED

Theorem smtstr_concat_self_prefix:
  (s = smtstr_concat (smtstr_concat s x) y) <=>
  (SmtStr [] = smtstr_concat x y)
Proof
  simp [smtstr_concat_assoc,
        smtstr_equal_concat_same_prefix_length]
QED

Theorem smtstr_concat_self_suffix:
  (s = smtstr_concat (smtstr_concat x y) s) <=>
  (SmtStr [] = smtstr_concat x y)
Proof
  simp [smtstr_equal_concat_same_suffix_length]
QED

Theorem smtstr_le_common_prefix:
  smtstr_le (smtstr_concat p x) (smtstr_concat p y) <=>
  smtstr_le x y
Proof
  rw [smtstr_le_def, smtstr_lt_def, smtstr_rep_concat,
      LLEX_num_common_prefix, smtstr_concat_left_cancel]
QED

Theorem smtstr_le_equal_length_tail:
  smtstr_len a = smtstr_len b /\ a <> b ==>
  (smtstr_le (smtstr_concat a x) (smtstr_concat b y) <=>
   smtstr_le a b)
Proof
  strip_tac >>
  `LENGTH (smtstr_rep a) = LENGTH (smtstr_rep b)` by
    fs [smtstr_len_def] >>
  `smtstr_rep a <> smtstr_rep b` by
    metis_tac [smtstr_rep_11] >>
  simp [smtstr_le_def, smtstr_lt_def, smtstr_rep_concat,
        LLEX_num_equal_length_tail,
        smtstr_concat_equal_prefix_lengths]
QED

Theorem smtstr_le_equal_length_left_tail:
  smtstr_len a = smtstr_len b /\ a <> b ==>
  (smtstr_le (smtstr_concat a x) b <=> smtstr_le a b)
Proof
  metis_tac [smtstr_le_equal_length_tail,
             smtstr_concat_nil_right]
QED

Theorem smtstr_le_equal_length_right_tail:
  smtstr_len a = smtstr_len b /\ a <> b ==>
  (smtstr_le a (smtstr_concat b y) <=> smtstr_le a b)
Proof
  metis_tac [smtstr_le_equal_length_tail,
             smtstr_concat_nil_right]
QED

Theorem smtstr_at_in_range:
  0 <= i /\ Num i < LENGTH (smtstr_rep s) ==>
    smtstr_at s i = SmtStr [EL (Num i) (smtstr_rep s)]
Proof
  strip_tac >>
  `~(i < 0)` by intLib.ARITH_TAC >>
  fs [smtstr_at_def, smtstr_substr_def,
      smtstr_rep_def,
      listTheory.TAKE1_DROP]
QED

Theorem smtstr_len_at:
  smtstr_len (smtstr_at s i) =
    if i < 0 \/ LENGTH (smtstr_rep s) <= Num i then 0 else 1
Proof
  Cases_on `i < 0 \/ LENGTH (smtstr_rep s) <= Num i`
  >- simp [smtstr_at_def, smtstr_len_substr]
  >> fs [] >>
  `0 < LENGTH (smtstr_rep s) - Num i` by decide_tac >>
  simp [smtstr_at_def, smtstr_len_substr,
        arithmeticTheory.MIN_DEF]
QED

Theorem smtstr_len_at_bound:
  smtstr_len (smtstr_at s i) <= 1
Proof
  rw [smtstr_len_at]
QED

Theorem smtstr_at_zero:
  s = SmtStr [] \/
  smtstr_at s 0 = SmtStr [EL 0 (smtstr_rep s)]
Proof
  Cases_on `smtstr_rep s` >>
  fs [smtstr_rep_eq_nil, smtstr_at_in_range]
QED

Theorem smtstr_substr_zero_one:
  smtstr_substr s 0 1 = smtstr_at s 0
Proof
  simp [smtstr_at_def]
QED

Theorem smtstr_indexof_aux_bounds:
  smtstr_indexof_aux t n s = SOME k ==>
    n <= k /\ k <= n + LENGTH s
Proof
  qid_spec_tac `n` >>
  Induct_on `s` >>
  rw [smtstr_indexof_aux_def] >>
  res_tac >>
  decide_tac
QED

Theorem smtstr_indexof_lower_bound:
  0 <= smtstr_indexof s t i ==> i <= smtstr_indexof s t i
Proof
  rw [smtstr_indexof_def] >>
  BasicProvers.every_case_tac >>
  fs [] >>
  drule smtstr_indexof_aux_bounds >>
  intLib.ARITH_TAC
QED

Theorem smtstr_indexof_upper_bound:
  0 <= smtstr_indexof s t i ==>
    smtstr_indexof s t i <= smtstr_len s
Proof
  rw [smtstr_indexof_def, smtstr_len_def] >>
  BasicProvers.every_case_tac >>
  fs [] >>
  drule smtstr_indexof_aux_bounds >>
  simp [] >>
  intLib.ARITH_TAC
QED

Theorem smtstr_indexof_negative:
  smtstr_indexof s t i < 0 <=> smtstr_indexof s t i = -1
Proof
  rw [smtstr_indexof_def] >>
  BasicProvers.every_case_tac >>
  simp []
QED

(* TASK_02 draft_str_to_int records digit2int values 0--9.  These official
   conversion facts expose the corresponding code-point and digit bounds. *)

Theorem smtstr_is_digit_to_code_bounds:
  smtstr_is_digit s ==>
    48 <= smtstr_to_code s /\ smtstr_to_code s <= 57
Proof
  strip_tac >>
  fs [smtstr_is_digit_def, smtstr_to_code_def]
QED

Theorem smtstr_from_code_to_code:
  0 <= n /\ Num n <= 196607 ==>
    smtstr_to_code (smtstr_from_code n) = n
Proof
  rw [smtstr_from_code_def, smtstr_to_code_def,
      smtstr_rep_def] >>
  intLib.ARITH_TAC
QED

(* TASK_02 draft_re_comp/draft_re_loop aut.accept clauses unfold one
   character at a time.  Package the concat and star derivative equations
   at the semantic boundary used by the replay prover. *)

Theorem smt_in_re_concat:
  smt_in_re s (reglan_concat r1 r2) <=>
    ?u v.
      smt_in_re u r1 /\ smt_in_re v r2 /\
      s = smtstr_concat u v
Proof
  simp [smt_in_re_rep, re_lang_def, reglan_dot_def,
        smtstr_concat_def] >>
  eq_tac
  >- (strip_tac >>
      `EVERY (\c. c <= 196607) (x ++ y)` by
        (qpat_x_assum `smtstr_rep s = _` (SUBST1_TAC o SYM) >>
         simp []) >>
      `EVERY (\c. c <= 196607) x /\ EVERY (\c. c <= 196607) y` by fs [] >>
      qexistsl [`SmtStr x`, `SmtStr y`] >>
      simp [smtstr_rep_def] >>
      metis_tac [SmtStr_smtstr_rep])
  >- (strip_tac >>
      qexistsl [`smtstr_rep u`, `smtstr_rep v`] >>
      simp [smtstr_rep_def])
QED

Theorem smt_in_re_concat_fixed_length:
  (!u. smt_in_re u r1 ==> smtstr_len u = m) /\
  (!v. smt_in_re v r2 ==> smtstr_len v = n) ==>
  smt_in_re s (reglan_concat r1 r2) ==>
  smtstr_len s = m + n
Proof
  rw [smt_in_re_concat] >>
  simp [smtstr_len_concat]
QED

Theorem smt_in_re_concat_assoc:
  smt_in_re s (reglan_concat (reglan_concat r1 r2) r3) <=>
  smt_in_re s (reglan_concat r1 (reglan_concat r2 r3))
Proof
  simp [smt_in_re_concat] >>
  metis_tac [smtstr_concat_assoc]
QED

Theorem smt_in_re_concat_assoc_all:
  !r1 r2 r3 s.
    smt_in_re s (reglan_concat (reglan_concat r1 r2) r3) <=>
    smt_in_re s (reglan_concat r1 (reglan_concat r2 r3))
Proof
  simp [smt_in_re_concat_assoc]
QED

Theorem smt_in_re_concat_language_cong:
  !r1 r1' r2 r2'.
    (!s. smt_in_re s r1 <=> smt_in_re s r1') /\
    (!s. smt_in_re s r2 <=> smt_in_re s r2') ==>
    !s. smt_in_re s (reglan_concat r1 r2) <=>
        smt_in_re s (reglan_concat r1' r2')
Proof
  simp [smt_in_re_concat] >>
  metis_tac []
QED

Theorem smt_in_re_star_cvc_unfold:
  smt_in_re s (reglan_star r) ==>
    s = SmtStr [] \/ smt_in_re s r \/
    ?u v w.
      smt_in_re u r /\ smt_in_re v (reglan_star r) /\
      smt_in_re w r /\ u <> SmtStr [] /\ w <> SmtStr [] /\
      s = smtstr_concat (smtstr_concat u v) w
Proof
  strip_tac >>
  fs [smt_in_re_def] >>
  drule reglan_kstar_cvc_unfold >>
  strip_tac
  >- (disj1_tac >>
      metis_tac [smtstr_rep_eq_nil])
  >- (disj2_tac >> disj1_tac >>
      fs [smt_in_re_rep]) >>
  disj2_tac >> disj2_tac >>
  `EVERY (\c. c <= 196607) ((u ++ v) ++ w)` by
    metis_tac [smtstr_rep_bound] >>
  `EVERY (\c. c <= 196607) u /\
   EVERY (\c. c <= 196607) v /\
   EVERY (\c. c <= 196607) w` by fs [] >>
  qexistsl [`SmtStr u`, `SmtStr v`, `SmtStr w`] >>
  simp [smt_in_re_rep, smt_in_re_def, smtstr_rep_def,
        smtstr_concat_def, SmtStr_11] >>
  metis_tac [SmtStr_smtstr_rep]
QED

(* CPC's RE_UNFOLD_POS rule flattens an arbitrarily associated, nonempty
   concatenation and uses one shared choice for all components.  These list
   folds state that contract once, independently of parser association. *)
Definition smtstr_concat_list_def:
  (smtstr_concat_list [] = SmtStr []) /\
  (smtstr_concat_list (s::ss) =
    case ss of [] => s | _ => smtstr_concat s (smtstr_concat_list ss))
End

Definition reglan_concat_list_def:
  (reglan_concat_list [] = reglan_none) /\
  (reglan_concat_list (r::rs) =
    case rs of [] => r | _ => reglan_concat r (reglan_concat_list rs))
End

Definition cpc_re_unfold_pos_ordinary_def:
  cpc_re_unfold_pos_ordinary s rs pieces <=>
    LENGTH pieces = LENGTH rs /\
    s = smtstr_concat_list
      (GENLIST (\i. EL i pieces) (LENGTH rs)) /\
    EVERY2 smt_in_re
      (GENLIST (\i. EL i pieces) (LENGTH rs)) rs
End

Definition cpc_re_unfold_pos_endpoints_def:
  cpc_re_unfold_pos_endpoints rs pieces <=>
    EL 0 pieces <> SmtStr [] /\
    EL (PRE (LENGTH rs)) pieces <> SmtStr []
End

Definition cpc_re_unfold_pos_preferred_def:
  cpc_re_unfold_pos_preferred s rs =
    @pieces.
      cpc_re_unfold_pos_ordinary s rs pieces /\
      ((?other.
          cpc_re_unfold_pos_ordinary s rs other /\
          cpc_re_unfold_pos_endpoints rs other) ==>
       cpc_re_unfold_pos_endpoints rs pieces)
End

Theorem cpc_preferred_choice_ordinary:
  (?x:'a. ordinary x) ==>
  ordinary
    (@x. ordinary x /\ ((?y. ordinary y /\ endpoints y) ==> endpoints x))
Proof
  strip_tac >> SELECT_ELIM_TAC >> metis_tac []
QED

Theorem cpc_preferred_choice_guarded:
  (?x:'a. ordinary x /\ endpoints x) ==>
  let selected =
    @x. ordinary x /\ ((?y. ordinary y /\ endpoints y) ==> endpoints x)
  in ordinary selected /\ endpoints selected
Proof
  strip_tac >> PURE_REWRITE_TAC [LET_THM] >>
  SELECT_ELIM_TAC >> metis_tac []
QED

Theorem smt_in_re_concat_list:
  !rs s. rs <> [] /\ smt_in_re s (reglan_concat_list rs) ==>
    ?pieces. LENGTH pieces = LENGTH rs /\
      s = smtstr_concat_list pieces /\
      EVERY2 smt_in_re pieces rs
Proof
  Induct >> simp [reglan_concat_list_def, smtstr_concat_list_def] >>
  Cases_on `rs` >>
  simp [reglan_concat_list_def, smtstr_concat_list_def]
  >- (rpt gen_tac >> strip_tac >> qexists_tac `[s]` >>
      simp [smtstr_concat_list_def]) >>
  rpt gen_tac >> strip_tac >>
  drule (iffLR smt_in_re_concat) >> strip_tac >>
  qpat_x_assum `!s. _` (qspec_then `v` mp_tac) >>
  impl_tac >- simp [reglan_concat_list_def] >>
  strip_tac >>
  qexists_tac `u::pieces` >>
  simp [smtstr_concat_list_def] >>
  Cases_on `pieces` >> fs []
QED

Theorem smt_in_re_concat_list_cpc_preferred:
  rs <> [] /\ smt_in_re s (reglan_concat_list rs) ==>
  cpc_re_unfold_pos_ordinary s rs
    (cpc_re_unfold_pos_preferred s rs)
Proof
  strip_tac >>
  simp [cpc_re_unfold_pos_preferred_def] >>
  irule cpc_preferred_choice_ordinary >>
  qspec_then `s` mp_tac (Q.SPEC `rs` smt_in_re_concat_list) >>
  impl_tac >- simp [] >> strip_tac >>
  qexists_tac `pieces` >>
  simp [cpc_re_unfold_pos_ordinary_def] >>
  `GENLIST (\i. EL i pieces) (LENGTH rs) = pieces` by
    (irule listTheory.GENLIST_EL >> simp []) >>
  simp []
QED

Theorem smt_in_re_star_cpc_preferred:
  smt_in_re s (reglan_star r) ==>
  let rs = [r; reglan_star r; r] in
  s = SmtStr [] \/ smt_in_re s r \/
  (cpc_re_unfold_pos_ordinary s rs
      (cpc_re_unfold_pos_preferred s rs) /\
   cpc_re_unfold_pos_endpoints rs
      (cpc_re_unfold_pos_preferred s rs))
Proof
  strip_tac >> drule smt_in_re_star_cvc_unfold >>
  disch_then (fn theorem => DISJ_CASES_TAC theorem)
  >- simp []
  >- (qpat_x_assum `_ \/ _` DISJ_CASES_TAC
      >- simp []
      >- (qpat_x_assum `?u v w. _` strip_assume_tac >>
          PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >>
          `?pieces.
             cpc_re_unfold_pos_ordinary s
               [r; reglan_star r; r] pieces /\
             cpc_re_unfold_pos_endpoints
               [r; reglan_star r; r] pieces` by
            (qexists_tac `[u; v; w]` >>
             simp [cpc_re_unfold_pos_ordinary_def,
                   cpc_re_unfold_pos_endpoints_def,
                   smtstr_concat_list_def] >>
             metis_tac [smtstr_concat_assoc]) >>
          disj2_tac >> disj2_tac >>
          PURE_REWRITE_TAC [cpc_re_unfold_pos_preferred_def] >>
          irule (Conv.BETA_RULE (PURE_REWRITE_RULE [LET_THM]
            cpc_preferred_choice_guarded)) >>
          qexists_tac `pieces` >> fs []))
QED

Theorem smt_in_re_concat_cons:
  EVERY (\x. x <= 196607) (c::s) ==>
  (smt_in_re (SmtStr (c::s)) (reglan_concat r1 r2) <=>
   smt_in_re (SmtStr s) (reglan_concat (re_deriv c r1) r2) \/
   re_nullable r1 /\ smt_in_re (SmtStr s) (re_deriv c r2))
Proof
  strip_tac >>
  `smt_in_re (SmtStr (c::s)) (reglan_concat r1 r2) <=>
   smt_in_re (SmtStr s) (re_deriv c (reglan_concat r1 r2))` by
    simp [re_deriv_correct] >>
  pop_assum SUBST1_TAC >>
  Cases_on `re_nullable r1` >>
  simp [re_deriv_def, smt_in_re_def]
QED

Theorem smt_in_re_star_cons:
  EVERY (\x. x <= 196607) (c::s) ==>
  (smt_in_re (SmtStr (c::s)) (reglan_star r) <=>
   smt_in_re (SmtStr s)
     (reglan_concat (re_deriv c r) (reglan_star r)))
Proof
  strip_tac >>
  `smt_in_re (SmtStr (c::s)) (reglan_star r) <=>
   smt_in_re (SmtStr s) (re_deriv c (reglan_star r))` by
    simp [re_deriv_correct] >>
  pop_assum SUBST1_TAC >>
  simp [re_deriv_def]
QED

(* Ground checks pin the SMT-LIB totalization and empty-string cases. *)

Triviality smtstr_core_eval:
  smtstr_concat (SmtStr [1; 2]) (SmtStr [3]) =
    SmtStr [1; 2; 3] /\
  smtstr_len (SmtStr [10; 20; 30]) = 3 /\
  smtstr_at (SmtStr [10; 20]) (-1) = SmtStr [] /\
  smtstr_at (SmtStr [10; 20]) 0 = SmtStr [10] /\
  smtstr_at (SmtStr [10; 20]) 2 = SmtStr [] /\
  smtstr_at (SmtStr []) 0 = SmtStr [] /\
  smtstr_substr (SmtStr [10; 20; 30]) (-1) 2 = SmtStr [] /\
  smtstr_substr (SmtStr [10; 20; 30]) 1 0 = SmtStr [] /\
  smtstr_substr (SmtStr [10; 20; 30]) 1 (-1) = SmtStr [] /\
  smtstr_substr (SmtStr [10; 20; 30]) 3 1 = SmtStr [] /\
  smtstr_substr (SmtStr [10; 20; 30]) 1 5 =
    SmtStr [20; 30] /\
  smtstr_prefixof (SmtStr []) (SmtStr [1; 2]) /\
  smtstr_prefixof (SmtStr [1]) (SmtStr [1; 2]) /\
  smtstr_suffixof (SmtStr []) (SmtStr [1; 2]) /\
  smtstr_suffixof (SmtStr [2]) (SmtStr [1; 2]) /\
  smtstr_contains (SmtStr [1; 2; 3]) (SmtStr [2; 3]) /\
  smtstr_contains (SmtStr [1; 2; 3]) (SmtStr []) /\
  smtstr_indexof (SmtStr [1; 2; 1; 2]) (SmtStr [1; 2]) 1 = 2 /\
  smtstr_indexof (SmtStr [1; 2]) (SmtStr [3]) 0 = -1 /\
  smtstr_indexof (SmtStr [1; 2]) (SmtStr [1]) (-1) = -1 /\
  smtstr_indexof (SmtStr [1; 2]) (SmtStr []) 2 = 2 /\
  smtstr_indexof (SmtStr [1; 2]) (SmtStr []) 3 = -1 /\
  smtstr_indexof (SmtStr []) (SmtStr []) 0 = 0 /\
  smtstr_lt (SmtStr [1; 2]) (SmtStr [1; 3]) /\
  ~smtstr_lt (SmtStr [1; 2]) (SmtStr [1; 2]) /\
  smtstr_le (SmtStr [1; 2]) (SmtStr [1; 2]) /\
  smtstr_char 196607 = SmtStr [196607] /\
  str_inj "Az" = SmtStr [65; 122] /\
  smtstr_rep (SmtStr [196607]) = [196607]
Proof
  EVAL_TAC
QED

Triviality smtstr_a2_eval:
  smtstr_replace (SmtStr [97; 98; 99; 97; 98; 99])
    (SmtStr [98; 99]) (SmtStr [88]) =
      SmtStr [97; 88; 97; 98; 99] /\
  smtstr_replace (SmtStr [97; 98]) (SmtStr []) (SmtStr [88]) =
    SmtStr [88; 97; 98] /\
  smtstr_replace (SmtStr [97; 98]) (SmtStr [99]) (SmtStr [88]) =
    SmtStr [97; 98] /\
  smtstr_replace_all (SmtStr [97; 98; 97]) (SmtStr [97])
    (SmtStr [99]) = SmtStr [99; 98; 99] /\
  smtstr_replace_all (SmtStr [97; 98]) (SmtStr [])
    (SmtStr [99]) = SmtStr [97; 98] /\
  smtstr_replace_all (SmtStr [97; 97; 97]) (SmtStr [97; 97])
    (SmtStr [98]) = SmtStr [98; 97] /\
  smtstr_replace_re (SmtStr [97; 98])
    (reglan_union (reglan_to_re (SmtStr [97]))
                  (reglan_to_re (SmtStr [97; 98]))) (SmtStr [120]) =
    SmtStr [120; 98] /\
  smtstr_replace_re (SmtStr [97; 98])
    (reglan_union (reglan_to_re (SmtStr [98]))
                  (reglan_to_re (SmtStr [97; 98]))) (SmtStr [120]) =
    SmtStr [120] /\
  smtstr_replace_re (SmtStr [97; 98])
    (reglan_to_re (SmtStr [])) (SmtStr [120]) =
      SmtStr [120; 97; 98] /\
  smtstr_replace_re_all (SmtStr [97; 98; 97])
    (reglan_union (reglan_to_re (SmtStr []))
                  (reglan_to_re (SmtStr [97]))) (SmtStr [120]) =
    SmtStr [120; 98; 120] /\
  smtstr_replace_re_all (SmtStr [97; 98])
    (reglan_to_re (SmtStr [])) (SmtStr [120]) =
      SmtStr [97; 98] /\
  smtstr_replace_re_all (SmtStr [97; 98]) reglan_allchar
    (SmtStr [120]) = SmtStr [120; 120] /\
  smtstr_is_digit (SmtStr [48]) /\
  smtstr_is_digit (SmtStr [57]) /\
  ~smtstr_is_digit (SmtStr []) /\
  ~smtstr_is_digit (SmtStr [48; 49]) /\
  ~smtstr_is_digit (SmtStr [47]) /\
  smtstr_to_code (SmtStr [196607]) = 196607 /\
  smtstr_to_code (SmtStr []) = -1 /\
  smtstr_to_code (SmtStr [1; 2]) = -1 /\
  smtstr_from_code 0 = SmtStr [0] /\
  smtstr_from_code 196607 = SmtStr [196607] /\
  smtstr_from_code (-1) = SmtStr [] /\
  smtstr_from_code 196608 = SmtStr [] /\
  smtstr_to_int (SmtStr [48; 48; 49; 50; 51]) = 123 /\
  smtstr_to_int (SmtStr []) = -1 /\
  smtstr_to_int (SmtStr [45; 49]) = -1 /\
  smtstr_from_int 0 = SmtStr [48] /\
  smtstr_from_int 123 = SmtStr [49; 50; 51] /\
  smtstr_from_int (-123) = SmtStr [] /\
  smtstr_to_int (smtstr_from_int 9876) = 9876
Proof
  EVAL_TAC
QED

Triviality reglan_eval:
  ~smt_in_re (SmtStr []) reglan_none /\
  smt_in_re (SmtStr [1; 196607]) reglan_all /\
  smt_in_re (SmtStr [65]) reglan_allchar /\
  ~smt_in_re (SmtStr [65; 66]) reglan_allchar /\
  smt_in_re (SmtStr [1; 2]) (reglan_to_re (SmtStr [1; 2])) /\
  smt_in_re (SmtStr [66])
    (reglan_range (SmtStr [65]) (SmtStr [67])) /\
  ~smt_in_re (SmtStr [68])
    (reglan_range (SmtStr [65]) (SmtStr [67])) /\
  ~smt_in_re (SmtStr [66])
    (reglan_range (SmtStr [65; 66]) (SmtStr [67])) /\
  smt_in_re (SmtStr [1; 2])
    (reglan_concat (reglan_to_re (SmtStr [1])) (reglan_to_re (SmtStr [2]))) /\
  smt_in_re (SmtStr [2])
    (reglan_union (reglan_to_re (SmtStr [1])) (reglan_to_re (SmtStr [2]))) /\
  smt_in_re (SmtStr [2])
    (reglan_inter
       (reglan_range (SmtStr [1]) (SmtStr [3])) (reglan_range (SmtStr [2]) (SmtStr [4]))) /\
  smt_in_re (SmtStr [1])
    (reglan_diff (reglan_range (SmtStr [1]) (SmtStr [3])) (reglan_to_re (SmtStr [2]))) /\
  ~smt_in_re (SmtStr [2])
    (reglan_diff (reglan_range (SmtStr [1]) (SmtStr [3])) (reglan_to_re (SmtStr [2]))) /\
  smt_in_re (SmtStr [2]) (reglan_comp (reglan_to_re (SmtStr [1]))) /\
  ~smt_in_re (SmtStr [1]) (reglan_comp (reglan_to_re (SmtStr [1]))) /\
  smt_in_re (SmtStr [196607]) (reglan_comp reglan_none) /\
  smt_in_re (SmtStr [1; 1]) (reglan_star (reglan_to_re (SmtStr [1]))) /\
  smt_in_re (SmtStr []) (reglan_star (reglan_to_re (SmtStr [1]))) /\
  smt_in_re (SmtStr [1]) (reglan_plus (reglan_to_re (SmtStr [1]))) /\
  ~smt_in_re (SmtStr []) (reglan_plus (reglan_to_re (SmtStr [1]))) /\
  smt_in_re (SmtStr []) (reglan_opt (reglan_to_re (SmtStr [1]))) /\
  smt_in_re (SmtStr [1]) (reglan_opt (reglan_to_re (SmtStr [1]))) /\
  smt_in_re (SmtStr [1; 1])
    (reglan_power (reglan_to_re (SmtStr [1])) 2) /\
  ~smt_in_re (SmtStr [1])
    (reglan_power (reglan_to_re (SmtStr [1])) 2) /\
  smt_in_re (SmtStr [])
    (reglan_loop (reglan_to_re (SmtStr [1])) 0 0) /\
  ~smt_in_re (SmtStr [])
    (reglan_loop (reglan_to_re (SmtStr [1])) 1 0) /\
  smt_in_re (SmtStr [1])
    (reglan_loop (reglan_to_re (SmtStr [1])) 1 3) /\
  smt_in_re (SmtStr [1; 1; 1])
    (reglan_loop (reglan_to_re (SmtStr [1])) 1 3) /\
  ~smt_in_re (SmtStr [1; 1; 1; 1])
    (reglan_loop (reglan_to_re (SmtStr [1])) 1 3)
Proof
  EVAL_TAC
QED
