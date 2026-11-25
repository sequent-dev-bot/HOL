Theory set_relationAutoSeed
Ancestors
  set_relation
Libs
  clasetLib

(* src/HOL/Transitive_Closure.thy:32-40,1603-1606 @ f7e02b7e.  Isabelle
   declares [r_into_trancl] [intro] where it defines the closure, and
   adds four unsafe simp solvers beside it -- the decision procedure of
   src/Provers/trancl.ML -- which discharge a closure literal from the
   edges standing in the context.  HOL4 declares nothing about
   [transitive_closure] at all: no rewrite, no claset rule, no solver,
   so the literal is inert and a goal that has to build one has no
   route.

   The two rules are the inductive definition's own, in the membership
   spelling [tc_rules] states and the goals are written in.  The join
   is the second rule where Isabelle's is the solver: declared
   [Pure.intro] there, it is not in its claset, and without a solver of
   ours a chained closure is out of reach entirely.  Both are unsafe --
   the join has to guess its midpoint, which is what an unsafe rule is
   for.

   What they close is measured on
   [list_L7054_set_trans_list_step_subset_trancl] of the list/map
   corpus, and only beside the safe mapped-membership elimination
   listAutoSeed declares: with that elimination and without these rules
   the family run leaves [MEM (x',item_2) pairs, MEM (item_1,x') pairs
   |- (item_1,item_2) IN transitive_closure (set pairs)] -- the two
   edges found and the closure they have to be built into standing --
   and with both the goal closes.  Either alone leaves the goal open,
   at the decomposition without the elimination and at the join without
   these. *)

Theorem TC_STEP_AUTO[intro]:
  !r x y. (x,y) IN r ==> (x,y) IN transitive_closure r
Proof
  MATCH_ACCEPT_TAC (CONJUNCT1 (SPEC_ALL set_relationTheory.tc_rules))
QED

Theorem TC_JOIN_AUTO[intro]:
  !r x y.
    (?z. (x,z) IN transitive_closure r /\ (z,y) IN transitive_closure r) ==>
    (x,y) IN transitive_closure r
Proof
  MATCH_ACCEPT_TAC (CONJUNCT2 (SPEC_ALL set_relationTheory.tc_rules))
QED
