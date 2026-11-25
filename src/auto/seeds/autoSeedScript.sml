Theory autoSeed
Ancestors
  clasetSeed pairAutoSeed sumAutoSeed optionAutoSeed listAutoSeed
  pred_setAutoSeed arithmeticAutoSeed finite_mapAutoSeed integerAutoSeed
  realAutoSeed stringAutoSeed rich_listAutoSeed sortingAutoSeed
  relationAutoSeed set_relationAutoSeed
Libs
  clasimpLib splitPersistLib

(* Declarations stay in their per-theory promotion units. *)

(* src/HOL/HOL.thy:1161,1448 @ f7e02b7e. *)
Theorem BOOL_AUTO_COND_P_SPLIT[split]:
  !P b x y.
    P (if b then x else y) <=>
    (b ==> P x) /\ (~b ==> P y)
Proof
  Cases_on `b` >> simp []
QED

(* src/HOL/HOL.thy:1396-1414,1442-1443 @ f7e02b7e.  Isabelle declares
   the twelve miniscoping laws -- [ex_simps] and [all_simps] -- simp, so
   a quantifier whose body has a conjunct, disjunct or side of an
   implication the bound variable does not occur in ends up inside that
   side, and a rule stated of the smaller scope meets it.  HOL4 proves
   all twelve and declares none, which leaves the quantifier outermost
   and every such rule short of its redex.  The reverse readings are
   HOL4's own LEFT_AND_FORALL_THM, RIGHT_AND_FORALL_THM,
   LEFT_OR_EXISTS_THM and RIGHT_OR_EXISTS_THM; none is ambient, so the
   pairs cannot loop.

   Declared [simp_bottom_up] rather than [simp] because the subject is a
   quantifier whose body has to be normal first: HOL4 reaches the
   quantifier before the body, and a law fired there pushes the
   quantifier past a side the body's own antecedent had not yet been read
   with -- an option split's [x = SOME item] leaves [x = NONE] standing
   where the unmoved quantifier settles it.  Isabelle's innermost-first
   order offers these laws a normalised body always, which is what the
   reducer offers them here. *)
Theorem BOOL_AUTO_ALL_AND_LEFT[simp_bottom_up] =
  GSYM boolTheory.LEFT_AND_FORALL_THM

Theorem BOOL_AUTO_ALL_AND_RIGHT[simp_bottom_up] =
  GSYM boolTheory.RIGHT_AND_FORALL_THM

Theorem BOOL_AUTO_ALL_OR_LEFT[simp_bottom_up] = boolTheory.LEFT_FORALL_OR_THM
Theorem BOOL_AUTO_ALL_OR_RIGHT[simp_bottom_up] = boolTheory.RIGHT_FORALL_OR_THM
Theorem BOOL_AUTO_ALL_IMP_LEFT[simp_bottom_up] = boolTheory.LEFT_FORALL_IMP_THM

Theorem BOOL_AUTO_ALL_IMP_RIGHT[simp_bottom_up] =
  boolTheory.RIGHT_FORALL_IMP_THM

Theorem BOOL_AUTO_EX_AND_LEFT[simp_bottom_up] = boolTheory.LEFT_EXISTS_AND_THM

Theorem BOOL_AUTO_EX_AND_RIGHT[simp_bottom_up] =
  boolTheory.RIGHT_EXISTS_AND_THM

Theorem BOOL_AUTO_EX_OR_LEFT[simp_bottom_up] =
  GSYM boolTheory.LEFT_OR_EXISTS_THM

Theorem BOOL_AUTO_EX_OR_RIGHT[simp_bottom_up] =
  GSYM boolTheory.RIGHT_OR_EXISTS_THM

Theorem BOOL_AUTO_EX_IMP_LEFT[simp_bottom_up] = boolTheory.LEFT_EXISTS_IMP_THM

Theorem BOOL_AUTO_EX_IMP_RIGHT[simp_bottom_up] =
  boolTheory.RIGHT_EXISTS_IMP_THM
