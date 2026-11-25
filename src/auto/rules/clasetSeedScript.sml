Theory clasetSeed

Libs
  clasetLib

val sintro_spec =
  {kind = clasetRules.Intro, safe = true, prio = NONE};
val intro_spec =
  {kind = clasetRules.Intro, safe = false, prio = NONE};
val selim_spec =
  {kind = clasetRules.Elim, safe = true, prio = NONE};

val _ = List.app (fn name => export_rule sintro_spec name)
  ["bool.EQ_REFL", "bool.TRUTH", "bool.IMP_ANTISYM_AX", "bool.IMP_F",
   "bool.AND_INTRO_THM"];

val _ = List.app (fn name => export_rule selim_spec name)
  ["bool.FALSITY", "bool.OR_ELIM_THM"];

val _ = export_rule intro_spec "bool.EQ_EXT";

Theorem DISJ_CINTRO_THM[sintro]:
  !p q. (~q ==> p) ==> p \/ q
Proof
  BasicProvers.PROVE_TAC [boolTheory.EXCLUDED_MIDDLE]
QED

Theorem CONJ_ELIM_THM[selim]:
  !p q r. p /\ q ==> (p ==> q ==> r) ==> r
Proof
  BasicProvers.PROVE_TAC []
QED

Theorem IMP_CELIM_THM[selim]:
  !p q r. (p ==> q) ==> (~p ==> r) ==> (q ==> r) ==> r
Proof
  BasicProvers.PROVE_TAC [boolTheory.EXCLUDED_MIDDLE]
QED

Theorem IFF_CELIM_THM[selim]:
  !p q r. (p <=> q) ==> (p ==> q ==> r) ==> (~p ==> ~q ==> r) ==> r
Proof
  BasicProvers.PROVE_TAC [boolTheory.EXCLUDED_MIDDLE]
QED

Theorem NOT_IMP_CELIM_THM:
  !p q r. ~(p ==> q) ==> (p ==> ~q ==> r) ==> r
Proof
  BasicProvers.PROVE_TAC []
QED

Theorem NOT_FORALL_CELIM_THM:
  !P r. ~(!x. P x) ==> (!x. ~P x ==> r) ==> r
Proof
  BasicProvers.PROVE_TAC []
QED

Theorem EXISTS_ELIM_THM[selim]:
  !P q. (?x. P x) ==> (!x. P x ==> q) ==> q
Proof
  BasicProvers.PROVE_TAC []
QED

Theorem EX1_ELIM_THM[selim]:
  !P r. (?!x. P x) ==>
        (!x. P x /\ (!y z. P y /\ P z ==> y = z) ==> r) ==> r
Proof
  BasicProvers.PROVE_TAC [boolTheory.EXISTS_UNIQUE_THM]
QED

Theorem EXISTS_INTRO_THM[intro]:
  !P x. P x ==> ?y. P y
Proof
  BasicProvers.PROVE_TAC []
QED

Theorem EX1_INTRO_THM[intro]:
  !P a. P a ==> (!x. P x ==> x = a) ==> ?!x. P x
Proof
  BasicProvers.PROVE_TAC [boolTheory.EXISTS_UNIQUE_THM]
QED

Theorem EX_EX1_INTRO_THM[sintro]:
  !P. (?x. P x) ==> (!x y. P x /\ P y ==> x = y) ==> ?!x. P x
Proof
  BasicProvers.PROVE_TAC [boolTheory.EXISTS_UNIQUE_THM]
QED

Theorem FORALL_ELIM_THM[elim=75]:
  !P x r. (!y. P y) ==> (P x ==> r) ==> r
Proof
  BasicProvers.PROVE_TAC []
QED

Theorem NOT_ELIM_THM:
  !p r. ~p ==> p ==> r
Proof
  BasicProvers.PROVE_TAC []
QED
