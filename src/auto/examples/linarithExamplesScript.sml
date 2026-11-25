(* ==========================================================================
   Examples: linear arithmetic (linarithLib)

   LINARITH_TAC is a generic linear-arithmetic decision procedure in
   the style of Isabelle/HOL's arith: a Fourier-Motzkin core over any
   ordered carrier type with registered instances, preprocessing that
   splits operators like MIN/MAX/ABS and conditionals on demand, and
   support for goals mixing several carriers through the registered
   injections (num into int, int into real, ...).

     LINARITH_TAC ths          full procedure: splitting, injections,
                               [arith] facts
     SIMPLE_LINARITH_TAC ths   additive core only -- faster, no
                               operator splitting
     CFG_LINARITH_TAC cfg ths  explicit configuration
     LINARITH_PROVE tm         forward-rule form, returns the theorem
     LINARITH_CONV             conversion deciding a relation
     LINARITH_ss               simpset fragment: the simplifier decides
                               an arithmetic atom wherever it meets one

   The num instance is built in; loading intLinarith, realLinarith and
   ratLinarith (as this theory's Libs line does) registers the int,
   real and rat instances.  Facts are supplied per-invocation via the
   [thm list] or persistently via the [arith] attribute; [arith_split]
   registers a P-form splitting rule for a new operator.
   ========================================================================== *)

Theory linarithExamples
Ancestors
  arithmetic integer real intreal rat linarithSeed linarithInst
Libs
  linarithLib intLinarith realLinarith ratLinarith

(* --------------------------------------------------------------------------
   Natural numbers.  Truncated subtraction, MIN/MAX, SUC and literal
   MOD/DIV are all understood.
   -------------------------------------------------------------------------- *)

Theorem num_min_max:
  MIN m n + MAX m n = m + n
Proof
  LINARITH_TAC []
QED

Theorem num_truncated_sub:
  (m:num) <= n <=> m - n = 0
Proof
  LINARITH_TAC []
QED

Theorem num_suc_le:
  (m:num) < SUC n <=> m <= n
Proof
  LINARITH_TAC []
QED

Theorem num_mod_bound:
  (m:num) MOD 42 <= 41
Proof
  LINARITH_TAC []
QED

(* SIMPLE_LINARITH_TAC: no operator splitting, just the additive core
   on the goal's assumptions and conclusion -- cheaper on goals that
   do not need more.  Unlike LINARITH_TAC it does not preprocess the
   goal's structure, so strip the implication first. *)

Theorem num_simple_chain:
  (a:num) < b /\ b < c ==> a + 1 < c + 1
Proof
  strip_tac >> SIMPLE_LINARITH_TAC []
QED

(* --------------------------------------------------------------------------
   Integers: signed arithmetic, ABS/int_min/int_max splitting, and the
   euclidean facts for division and remainder by literals.
   -------------------------------------------------------------------------- *)

Theorem int_abs_nonneg:
  0 <= ABS (i:int)
Proof
  LINARITH_TAC []
QED

Theorem int_discrete:
  (i:int) < j ==> i + 1 <= j
Proof
  strip_tac >> SIMPLE_LINARITH_TAC []
QED

Theorem int_div_mod:
  (i:int) = i / 3 * 3 + i % 3
Proof
  LINARITH_TAC []
QED

Theorem int_mod_range:
  0 <= (i:int) % 3 /\ i % 3 < 3
Proof
  LINARITH_TAC []
QED

(* --------------------------------------------------------------------------
   Reals and rationals: dense orders, with division by literals.
   -------------------------------------------------------------------------- *)

Theorem real_midpoint:
  (x:real) < y ==> x < (x + y) / 2 /\ (x + y) / 2 < y
Proof
  LINARITH_TAC []
QED

Theorem real_abs_triangle_ish:
  (x:real) <= abs x
Proof
  LINARITH_TAC []
QED

Theorem rat_transitivity:
  (a:rat) <= b /\ b < c ==> a < c
Proof
  LINARITH_TAC []
QED

Theorem rat_midpoint:
  (a:rat) < b ==> a < (a + b) / 2
Proof
  LINARITH_TAC []
QED

(* --------------------------------------------------------------------------
   Mixed-carrier goals: the registered injections connect num, int,
   real and rat atoms occurring in one goal.
   -------------------------------------------------------------------------- *)

Theorem mixed_num_int:
  (m:num) <= n /\ &n <= (i:int) ==> &m <= i
Proof
  LINARITH_TAC []
QED

Theorem mixed_int_real:
  (i:int) < j ==> real_of_int i + 1 <= real_of_int j
Proof
  LINARITH_TAC []
QED

(* --------------------------------------------------------------------------
   Forward-rule and conversion forms.
   -------------------------------------------------------------------------- *)

Theorem forward_form_demo =
  LINARITH_PROVE “(x:int) < y /\ y < z ==> x < z”

Theorem conversion_demo:
  (x:real) + y < y + x + 1
Proof
  CONV_TAC LINARITH_CONV
QED

(* --------------------------------------------------------------------------
   LINARITH_ss: linear arithmetic inside the simplifier.  Added to a
   simpset, the procedure is asked about an arithmetic atom wherever
   the traversal meets one: the atom rewriting has left standing, and
   the side condition of a conditional rewrite, which is simplified
   with the same simpset.  Here EL_TAKE's guard [x < n] follows from
   the assumption [x + 1 < n] only by linear reasoning, which bool_ss
   alone cannot supply.
   -------------------------------------------------------------------------- *)

Theorem simp_fragment_demo:
  x + 1 < n ==> EL x (TAKE n l) = EL x (l:'a list)
Proof
  strip_tac >>
  ASM_SIMP_TAC (bool_ss ++ LINARITH_ss) [listTheory.EL_TAKE]
QED

(* --------------------------------------------------------------------------
   The [arith] attribute: persistent facts about atoms.

   LINARITH_TAC treats an application it cannot decompose -- here
   [weight l] -- as an opaque atom.  A theorem declared [arith] is
   inserted as a fact into every LINARITH_TAC call from now on
   (including in importing theories), so bounds on user functions can
   be stated once and used implicitly.  State the fact with free
   variables, in the style of arithmetic's X_LE_X_SQUARED: facts are
   inserted as they stand, not instantiated, so a free variable that
   lines up with the goal's atom is what makes the fact connect.
   linarithData.remove_arith retracts.
   -------------------------------------------------------------------------- *)

Definition weight_def:
  weight (l : 'a list) = 2 * LENGTH l + 1
End

Theorem weight_pos[arith]:
  0 < weight (l : 'a list)
Proof
  simp [weight_def]
QED

Theorem weight_lower_bound:
  (k:num) <= n ==> k < n + weight (l:'a list)
Proof
  LINARITH_TAC []
QED

(* --------------------------------------------------------------------------
   The [arith_split] attribute: P-form splitting rules.

   A splitting rule teaches the preprocessor to eliminate an operator
   by case analysis, in the same P-form shape the built-in MIN/MAX/ABS
   splits use.  [clamp n] caps a number at 9; after the split the two
   branches are linear.
   -------------------------------------------------------------------------- *)

Definition clamp_def:
  clamp (n:num) = if n <= 9 then n else 9
End

Theorem clamp_split[arith_split]:
  !P n. P (clamp n) <=> (n <= 9 ==> P n) /\ (9 < n ==> P 9)
Proof
  rw [clamp_def, arithmeticTheory.NOT_LESS_EQUAL] >>
  metis_tac [arithmeticTheory.NOT_LESS_EQUAL]
QED

Theorem clamp_bounds:
  clamp n <= 9 /\ clamp n <= n
Proof
  LINARITH_TAC []
QED

Theorem clamp_mono:
  m <= n ==> clamp m <= clamp n
Proof
  LINARITH_TAC []
QED
