Theory arithmeticAutoSeed
Ancestors
  arithmetic
Libs
  clasetLib clasimpLib seedCollections

(* src/HOL/Nat.thy:303-769 @ f7e02b7e;
   src/HOL/Orderings.thy:208-228 @ f7e02b7e *)
Theorem ADD_EQ_0_AUTO[iff] = arithmeticTheory.ADD_EQ_0
Theorem ZERO_LESS_EQ_AUTO[iff] = arithmeticTheory.ZERO_LESS_EQ
Theorem LESS_EQ_MONO_AUTO[iff] = arithmeticTheory.LESS_EQ_MONO
Theorem LESS_EQ_0_AUTO[iff] = arithmeticTheory.LESS_EQ_0
Theorem NOT_LESS_0_AUTO[iff] = prim_recTheory.NOT_LESS_0
Theorem LESS_MONO_EQ_AUTO[iff] = arithmeticTheory.LESS_MONO_EQ
Theorem LESS_SUC_REFL_AUTO[iff] = prim_recTheory.LESS_SUC_REFL
Theorem LESS_0_AUTO[iff] = prim_recTheory.LESS_0
Theorem NOT_ZERO_AUTO[iff] = arithmeticTheory.NOT_ZERO
Theorem NOT_LT_ZERO_EQ_ZERO_AUTO[iff] = arithmeticTheory.NOT_LT_ZERO_EQ_ZERO
Theorem ZERO_LESS_ADD_AUTO[iff] = arithmeticTheory.ZERO_LESS_ADD
Theorem LESS_EQ_REFL_AUTO[iff] = arithmeticTheory.LESS_EQ_REFL
Theorem LESS_REFL_AUTO[iff] = prim_recTheory.LESS_REFL

Theorem LESS_ONE_AUTO[iff]:
  !n. n < 1 <=> n = 0
Proof
  Cases_on `n` >> simp []
QED

Theorem ZERO_LT_IMP_OR_ZERO_AUTO:
  !n proposition.
    ((0 < n ==> proposition) <=> proposition \/ n = 0)
Proof
  Cases_on `n` >> simp[]
QED

(* src/HOL/Nat.thy:2632 @ f7e02b7e.  [diff_diff_left] is simp there:
   two subtractions in a row are one subtraction of a sum, which is
   where an AC normalisation of the addition reaches the two
   subtrahends.  HOL4 agrees on the normal form and puts it in
   ARITH_ss, which this layer's ambient simpset does not carry, so
   [a - b - 1] and [a - 1 - b] stay two terms with nothing between
   them.  Declared in ARITH_ss's orientation, which is the source's:
   the opposite reading is HOL4's own SUB_PLUS, and a simpset holding
   both does not terminate. *)
Theorem SUB_SUB_LEFT_AUTO[simp] = GSYM arithmeticTheory.SUB_PLUS

(* Isabelle has no predecessor constant: src/HOL/Nat.thy writes the
   predecessor as [n - 1] throughout, so every goal translated from the
   source spells an index one below another that way, while HOL4's own
   rules about the same index -- EL_CONS, LAST_EL, the LUPDATE and TAKE
   rules -- spell it [PRE n].  Neither simpset carries a step between
   the two spellings, and a goal and the rule that would settle it then
   stand side by side unrelated: [EL (PRE n) xs = EL (n - 1) xs] is
   what an index characterisation with every other part in place is
   left holding.  Declared towards the source's spelling, which is
   also the one the layer's linear arithmetic decomposes: the num
   instance splits a subtraction and has no rule for PRE, which is an
   atom to it. *)
Theorem PRE_SUB1_AUTO[simp] = arithmeticTheory.PRE_SUB1

(* src/HOL/Lattices.thy:556-557 @ f7e02b7e.  Isabelle declares
   [min.absorb1] and [min.absorb2] simp with their [max] counterparts:
   a MIN whose comparison the context settles is one of its arguments.
   HOL4 states both pairs and declares neither, so a MIN left by a
   rule that formed it -- a take of a take is a take of the smaller
   length -- stands with nothing to reduce it, although the comparison
   is one linear-arithmetic step away.  Isabelle's companion
   declarations for the comparisons against a MIN ([le_inf_iff],
   [min_less_iff_conj] and their MAX halves) need no analogue: the
   layer's side-condition solver reads a bound against a MIN without
   them. *)
Theorem MIN_EQ_LE_AUTO[simp] = arithmeticTheory.MIN_EQ_LE
Theorem MAX_EQ_GE_AUTO[simp] = arithmeticTheory.MAX_EQ_GE

(* src/HOL/Groups.thy:221-341 @ f7e02b7e *)
Theorem ADD_ASSOC_ALGEBRA[algebra_simps, field_simps] =
  arithmeticTheory.ADD_ASSOC

Theorem ADD_COMM_ALGEBRA[algebra_simps, field_simps] =
  arithmeticTheory.ADD_COMM

Theorem MULT_ASSOC_ALGEBRA[algebra_simps, field_simps] =
  arithmeticTheory.MULT_ASSOC

Theorem MULT_COMM_ALGEBRA[algebra_simps, field_simps] =
  arithmeticTheory.MULT_COMM

Theorem MULT_LEFT_COMMUTE_ALGEBRA[algebra_simps, field_simps] =
  arithmeticTheory.MULT_COMM_ASSOC

Theorem SUB_RIGHT_SUB_ALGEBRA[algebra_simps, field_simps] =
  arithmeticTheory.SUB_RIGHT_SUB

Theorem ADD_LEFT_COMMUTE_ALGEBRA[algebra_simps, field_simps]:
  !a b c : num. a + (b + c) = b + (a + c)
Proof
  simp [AC ADD_ASSOC ADD_COMM]
QED

(* src/HOL/Nat.thy:1470-1472 @ f7e02b7e.  [funpow] is a primrec there,
   so its own two equations are simp, and the successor clause
   associates the new application outermost:
   [(f ^^ Suc n) x = f ((f ^^ n) x)].  HOL4 defines FUNPOW with the
   other association -- [FUNPOW f (SUC n) x = FUNPOW f n (f x)], which
   is Isabelle's [funpow_Suc_right] and is deliberately not simp there
   -- and states the source's form as arithmetic's FUNPOW_SUC,
   declared to no simpset.  Measured, the ambient layer leaves
   [FUNPOW f (SUC n) x] untouched in either association, so an
   iteration at a successor is inert and no fact about the iterated
   function reaches the application the successor adds.  Declared here
   in the source's association alone: the other one is HOL4's
   definition and stays where HOL4 put it, or the two would rewrite
   against each other.

   The zero clause needs nothing -- FUNPOW_0 is already ambient. *)
Theorem FUNPOW_SUC_AUTO[simp]:
  !f n x. FUNPOW f (SUC n) x = f (FUNPOW f n x)
Proof
  REWRITE_TAC [arithmeticTheory.FUNPOW_SUC]
QED

(* src/HOL/Wellfounded.thy:975 @ f7e02b7e.  [wf_less_than] is [iff], so
   Isabelle's claset carries the fact as well as its simpset.  prim_rec
   declares WF_LESS to the simpset alone, and a tableau leg that
   reaches [WF $<] -- the last of the three steps Isabelle's
   [wf_measures] takes -- has no simpset to close it with. *)
Theorem WF_LESS_AUTO[sintro] = prim_recTheory.WF_LESS
