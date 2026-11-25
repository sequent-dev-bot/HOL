(* ==========================================================================
   Examples: the tableau prover (tableauLib)

   BLAST_TAC is the HOL4 analogue of Isabelle/HOL's blast: a
   first-order tableau prover in the style of Paulson's "A Generic
   Tableau Prover and its Integration with Isabelle" (1999).  It
   searches on its own compact representation of the goal -- with
   metavariables for unknown witnesses -- and, when a tableau proof is
   found, replays it through the kernel, so soundness never depends on
   the search.

   Compared with FAST_TAC's goal-state search, the tableau
   representation makes blast much faster on hard first-order
   problems, at the price of a less predictable relationship to the
   original goal when it fails.  Like the classical tactics it uses
   the ambient claset plus its [thm list] argument (facts and
   Intro/Elim/Dest/... markers -- see clasetExamplesScript).

     BLAST_TAC ths            search with iterative deepening up to
                              !tableauLib.depth_limit (default 20)
     BLAST_DEPTH_TAC n ths    search to exactly depth n

   CS_BLAST_DEPTH_TAC takes an explicit claset instead of the ambient
   one, and tableauLib.tryIt runs the search alone -- returning the
   proof, if any, together with the full branch trace -- which is the
   way to see what a failing search did.
   ========================================================================== *)

Theory blastExamples
Ancestors
  clasetSeed
Libs
  clasetLib tableauLib

(* --------------------------------------------------------------------------
   Propositional goals.
   -------------------------------------------------------------------------- *)

(* Pelletier problem 9 *)
Theorem blast_pelletier_9:
  (p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~p \/ ~q)
Proof
  BLAST_TAC []
QED

(* Pelletier problem 17 *)
Theorem blast_pelletier_17:
  ((p /\ (q ==> r)) ==> s) <=>
  ((~p \/ q \/ s) /\ (~p \/ ~r \/ s))
Proof
  BLAST_TAC []
QED

(* --------------------------------------------------------------------------
   First-order goals.  These are the problems tableau search is built
   for: the blast selftest closes all of Pelletier 1-46, 52 and 62
   with BLAST_TAC, each within a 30-second budget.
   -------------------------------------------------------------------------- *)

(* Pelletier problem 29 *)
Theorem blast_pelletier_29:
  (?x:'a. f x) /\ (?y. g y) ==>
  (((!x. f x ==> h x) /\ (!y. g y ==> j y)) <=>
   (!x y. f x /\ g y ==> h x /\ j y))
Proof
  BLAST_TAC []
QED

(* Pelletier problem 36 *)
Theorem blast_pelletier_36:
  (!x:'a. ?y. j x y) /\
  (!x. ?y. g x y) /\
  (!x y. j x y \/ g x y ==> !z. j y z \/ g y z ==> h x z) ==>
  !x. ?y. h x y
Proof
  BLAST_TAC []
QED

(* Pelletier problem 39: no set contains exactly the sets that do not
   contain themselves (Russell's paradox). *)
Theorem blast_russell:
  ~(?x:'a. !y. f y x <=> ~f y y)
Proof
  BLAST_TAC []
QED

(* Pelletier problem 34, "Andrews's challenge": a stack of
   equivalences whose truth-table explosion defeats naive search. *)
Theorem blast_andrews_challenge:
  ((?x:'a. !y. p x <=> p y) <=>
   ((?x. q x) <=> (!y. p y))) <=>
  ((?x. !y. q x <=> q y) <=>
   ((?x. p x) <=> (!y. q y)))
Proof
  BLAST_TAC []
QED

(* Pelletier problem 43 *)
Theorem blast_pelletier_43:
  (!x:'a y. q x y <=> (!z. p z x <=> p z y)) ==>
  (!x y. q x y <=> q y x)
Proof
  BLAST_TAC []
QED

(* --------------------------------------------------------------------------
   Facts and markers work as for the classical tactics.
   -------------------------------------------------------------------------- *)

Definition confluent_def:
  confluent R <=>
  !x y z:'a. R x y /\ R x z ==> ?w. R y w /\ R z w
End

Theorem blast_with_marker:
  confluent R /\ R a b /\ R a c ==> ?w. R b w /\ R c w
Proof
  BLAST_TAC [Dest (iffLR confluent_def)]
QED

(* --------------------------------------------------------------------------
   Depth control.  BLAST_TAC deepens iteratively up to
   !tableauLib.depth_limit (default 20), so an explicit bound is
   needed only to cap a search known to blow up, or to document how
   deep a proof is: Pelletier 36 above is closed at tableau depth 9.
   -------------------------------------------------------------------------- *)

Theorem blast_depth_demo:
  (!x:'a. ?y. j x y) /\
  (!x. ?y. g x y) /\
  (!x y. j x y \/ g x y ==> !z. j y z \/ g y z ==> h x z) ==>
  !x. ?y. h x y
Proof
  BLAST_DEPTH_TAC 9 []
QED
