Theory relationAutoSeed
Ancestors
  relation
Libs
  clasetLib

(* src/HOL/Orderings.thy:620-658 @ f7e02b7e.  Isabelle reads the order
   axioms off the linorder class, so its simplifier is never told that
   the order is transitive: the class fact is in scope wherever the type
   is, and its order solver takes it from there.  A translated goal
   states the order as a premise about the relation instead, and a
   conditional rewrite whose side condition is [transitive R] -- the
   sorted_wrt bridge is one -- then stalls with the premise sitting
   unused beside it.  These take an order premise apart into the
   component the side condition asks for.

   Stated as implications rather than equivalences: the components do
   not reconstitute the order -- reflexivity, antisymmetry and
   transitivity are WeakOrder, but the simplifier would have to find all
   three to rewrite back -- and an equivalence would put the order
   predicate back on the goal it was just taken off.

   Declared to the claset as well, because a rewrite reaches a
   conditional rewrite's side condition and nothing else.  A rule the
   search applies asks for the component as a premise of its own, and
   a premise is not a subterm of the goal: where the rule is a cited
   fact quantifying its own order variable -- the sorted-unique chain
   of list_L6138 is the shape this was found on -- the component the
   goal owes it stands under that binder, which no rewrite of the
   goal's assumptions can reach.  Measured on that chain, with the
   citations declared: the goal fails at 0.110s with these simp-only
   and closes at 1.155s with them declared.

   Unsafe, and destruction rules: a [forward] declaration, which would
   leave the order premise standing where a destruction takes it
   apart, delivers nothing -- measured, the same goal fails at 0.110s
   with it -- and a safe declaration would take every order premise
   apart on every goal carrying one, wanted or not, for a difference
   this chain does not show (1.100s against 1.155s). *)

Theorem PreOrder_components_AUTO[simp, dest]:
  !R : 'a -> 'a -> bool.
    PreOrder R ==> reflexive R /\ transitive R
Proof
  simp[relationTheory.PreOrder]
QED

Theorem Order_components_AUTO[simp, dest]:
  !R : 'a -> 'a -> bool.
    Order R ==> antisymmetric R /\ transitive R
Proof
  simp[relationTheory.Order]
QED

Theorem WeakOrder_components_AUTO[simp, dest]:
  !R : 'a -> 'a -> bool.
    WeakOrder R ==> reflexive R /\ antisymmetric R /\ transitive R
Proof
  simp[relationTheory.WeakOrder]
QED

Theorem StrongOrder_components_AUTO[simp, dest]:
  !R : 'a -> 'a -> bool.
    StrongOrder R ==> irreflexive R /\ transitive R
Proof
  simp[relationTheory.StrongOrder]
QED

Theorem LinearOrder_components_AUTO[simp, dest]:
  !R : 'a -> 'a -> bool.
    LinearOrder R ==>
    antisymmetric R /\ transitive R /\ trichotomous R
Proof
  simp[relationTheory.LinearOrder, relationTheory.Order]
QED

Theorem StrongLinearOrder_components_AUTO[simp, dest]:
  !R : 'a -> 'a -> bool.
    StrongLinearOrder R ==>
    irreflexive R /\ transitive R /\ trichotomous R
Proof
  simp[relationTheory.StrongLinearOrder, relationTheory.StrongOrder]
QED

Theorem WeakLinearOrder_components_AUTO[simp, dest]:
  !R : 'a -> 'a -> bool.
    WeakLinearOrder R ==>
    reflexive R /\ antisymmetric R /\ transitive R /\ trichotomous R
Proof
  simp[relationTheory.WeakLinearOrder, relationTheory.WeakOrder]
QED

(* src/HOL/Wellfounded.thy:1136 @ f7e02b7e.  [wf_inv_image] is a [simp]
   rule and a safe [intro] there; relation states the same content as
   WF_inv_image and declares it to neither, so a well-foundedness goal
   about an inverse image is inert in both halves of the layer.
   Declared unsafe rather than [sintro]: a safe introduction owes
   seedAudit the inversion WF (inv_image R f) ==> WF R, which is false
   -- a constant f empties the inverse image whatever R is. *)
Theorem WF_inv_image_AUTO[simp, intro]:
  !relation function.
    WF relation ==> WF (inv_image relation function)
Proof
  METIS_TAC [relationTheory.WF_inv_image]
QED

(* src/HOL/Relation.thy:1680 @ f7e02b7e.  [in_inv_image] is simp there:
   Isabelle's simpset reads an inverse image at a pair without being
   told to, which is how a proof that unfolds a definition built on
   [inv_image] carries on into the underlying relation.  relation
   states the same content unapplied, as the constant's definition,
   and declares it to no simpset. *)
Theorem IN_INV_IMAGE_AUTO[simp]:
  !relation function left right.
    inv_image relation function left right <=>
    relation (function left) (function right)
Proof
  simp[relationTheory.inv_image_def]
QED

(* src/HOL/Set.thy:484,493,501 @ f7e02b7e.  Isabelle has one inclusion
   for both encodings -- a relation is a set of pairs there, so
   [subsetI] [intro!] and the unsafe eliminations [subsetD] (:493) and
   [subsetCE] (:501) settle a relation inclusion as they settle any
   other.  HOL4 splits the encoding: pred_set carries the same three
   for SUBSET, and a curried relation's inclusion is RSUBSET, which is
   declared to neither half.  The membership reading, RSUBSET itself,
   stays out of the simpset for the reason recorded at SUBSET_I_AUTO --
   an inclusion among the assumptions would become a conditional
   rewrite matching every application of its left side. *)

Theorem RSUBSET_I_AUTO[sintro]:
  !left right.
    (!x y. left x y ==> right x y) ==> left RSUBSET right
Proof
  REWRITE_TAC [relationTheory.RSUBSET]
QED

Theorem RSUBSET_D_AUTO[elim]:
  !left right x y.
    left RSUBSET right ==> left x y ==> right x y
Proof
  REWRITE_TAC [relationTheory.RSUBSET] THEN METIS_TAC []
QED

Theorem RSUBSET_CE_AUTO[elim]:
  !left right x y conclusion.
    left RSUBSET right ==>
    (~left x y ==> conclusion) ==>
    (right x y ==> conclusion) ==>
    conclusion
Proof
  REWRITE_TAC [relationTheory.RSUBSET] THEN METIS_TAC []
QED
