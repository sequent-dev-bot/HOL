Theory orderRules
Ancestors
  relation

(* The chaining steps an order refutation is built from.  Each is stated
   with its axioms as separate antecedents, because the procedure has
   the axioms one at a time -- a goal may carry [transitive] without
   [antisymmetric] -- and a lemma that asked for a named order would
   refuse a context that has what the step needs. *)

Theorem order_weak_trans:
  !R x y z. transitive R ==> R x y ==> R y z ==> R x z
Proof
  SRW_TAC [] [transitive_def] THEN METIS_TAC []
QED

Theorem order_strict_weak:
  !R x y. STRORD R x y ==> R x y
Proof
  SRW_TAC [] [STRORD]
QED

Theorem order_strict_distinct:
  !R x y. STRORD R x y ==> x <> y
Proof
  SRW_TAC [] [STRORD]
QED

Theorem order_strict_intro:
  !R x y. R x y ==> x <> y ==> STRORD R x y
Proof
  SRW_TAC [] [STRORD]
QED

Theorem order_weak_antisymmetric:
  !R x y. antisymmetric R ==> R x y ==> R y x ==> x = y
Proof
  SRW_TAC [] [antisymmetric_def] THEN METIS_TAC []
QED

Theorem order_weak_of_equal:
  !R x y. reflexive R ==> (x = y) ==> R x y
Proof
  SRW_TAC [] [reflexive_def]
QED

(* The two negative readings.  Totality turns a refused weak step round;
   reflexivity is what makes the refusal strict, since [x = y] would
   give the step back. *)
Theorem order_not_weak:
  !R x y. reflexive R ==> total R ==> ~R x y ==> STRORD R y x
Proof
  SRW_TAC [] [STRORD, reflexive_def, total_def] THEN METIS_TAC []
QED

Theorem order_not_strict:
  !R x y. reflexive R ==> total R ==> ~STRORD R x y ==> R y x
Proof
  SRW_TAC [] [STRORD, reflexive_def, total_def] THEN METIS_TAC []
QED

Theorem order_total_of_trichotomous:
  !R. reflexive R ==> trichotomous R ==> total R
Proof
  SRW_TAC [] [reflexive_def, trichotomous, total_def] THEN METIS_TAC []
QED

(* A strict primitive is read as the strict part of its own reflexive
   closure, which is what [STRORD_RC] says, so the procedure works with
   one shape of context and the reduction happens on the way in. *)
Theorem order_weak_of_strong:
  !R. StrongOrder R ==> WeakOrder (RC R)
Proof
  METIS_TAC [StrongOrd_Ord, RC_Weak]
QED

Theorem order_strict_of_strong:
  !R. StrongOrder R ==> (R = STRORD (RC R))
Proof
  METIS_TAC [STRORD_RC]
QED

(* The two library facts restated as implications with the relation
   universally quantified.  The procedure builds every step with
   [MATCH_MP], which instantiates a bound variable and would have to
   match a free one by hand. *)
Theorem order_strong_of_parts:
  !R. irreflexive R ==> transitive R ==> StrongOrder R
Proof
  SRW_TAC [] [StrongOrder]
QED

Theorem order_trichotomous_of_RC:
  !R. trichotomous R ==> trichotomous (RC R)
Proof
  METIS_TAC [trichotomous_RC]
QED
