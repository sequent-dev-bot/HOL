(* ==========================================================================
   Examples: classical proof search (classicalLib)

   The tactics of src/auto/classical are the HOL4 analogues of
   Isabelle/HOL's classical reasoner:

     FAST_TAC        depth-first search           (Isabelle: fast)
     BEST_TAC        best-first search            (Isabelle: best)
     SLOW_TAC        FAST with more backtracking  (Isabelle: slow)
     SLOW_BEST_TAC   BEST with more backtracking  (Isabelle: slow_best)
     FIRST_BEST_TAC  BEST expanding any subgoal   (Isabelle: first_best)
     ASTAR_TAC       A*-weighted best-first       (Isabelle: astar)
     SLOW_ASTAR_TAC  ASTAR with more backtracking (Isabelle: slow_astar)
     DEEPEN_TAC      iterative deepening          (Isabelle: deepen)
     SAFE_TAC        all safe steps, may split    (Isabelle: safe)
     CLARIFY_TAC     safe steps, no splitting     (Isabelle: clarify)

   All of them search with the ambient claset (see
   clasetExamplesScript for how rules are declared) and take a
   [thm list]: plain theorems are inserted as facts, marker-wrapped
   theorems (Intro, Dest, ...) become invocation-scoped rules.

   The step tactics SAFE_STEP_TAC, CLARIFY_STEP_TAC, STEP_TAC,
   SLOW_STEP_TAC and INST_STEP_TAC expose single search steps for
   building custom loops and are not shown here.  Each tactic also has
   a CS_ variant taking an explicit claset instead of the ambient one.
   ========================================================================== *)

Theory classicalExamples
Ancestors
  clasetSeed
Libs
  clasetLib classicalLib

(* --------------------------------------------------------------------------
   FAST_TAC on propositional logic.  These need genuinely classical
   reasoning -- there is no intuitionistic proof of any of them.
   -------------------------------------------------------------------------- *)

Theorem fast_excluded_middle:
  p \/ ~p
Proof
  FAST_TAC []
QED

Theorem fast_peirce:
  ((p ==> q) ==> p) ==> p
Proof
  FAST_TAC []
QED

(* Pelletier problem 16 *)
Theorem fast_imp_total:
  (p ==> q) \/ (q ==> p)
Proof
  FAST_TAC []
QED

(* Pelletier problem 12: associativity of <=> *)
Theorem fast_iff_assoc:
  ((p <=> q) <=> r) <=> (p <=> (q <=> r))
Proof
  FAST_TAC []
QED

(* --------------------------------------------------------------------------
   FAST_TAC on quantified goals.  Unsafe quantifier rules guess their
   instantiations by unification during the search; the found proof is
   replayed through the kernel, so nothing rests on the search itself.
   -------------------------------------------------------------------------- *)

(* Pelletier problem 24 *)
Theorem fast_pelletier_24:
  ~(?x:'a. s x /\ q x) /\
  (!x. p x ==> q x \/ r x) /\
  (~(?x. p x) ==> ?x. q x) /\
  (!x. q x \/ r x ==> s x) ==>
  ?x. p x /\ r x
Proof
  FAST_TAC []
QED

(* Pelletier problem 28 *)
Theorem fast_pelletier_28:
  (!x:'a. p x ==> (!y. q y)) /\
  ((!x. q x \/ r x) ==> ?x. q x /\ s x) /\
  ((?x. s x) ==> !x. l x ==> m x) ==>
  (!x. p x /\ l x ==> m x)
Proof
  FAST_TAC []
QED

(* --------------------------------------------------------------------------
   Invocation-scoped rules.  [sym R] has no rules in the ambient
   claset, so the definition's two directions are passed as markers:
   Dest turns a [sym R] assumption into its pointwise content, Intro
   proves a [sym R] goal from it.
   -------------------------------------------------------------------------- *)

Definition sym_def:
  sym R <=> !x y:'a. R x y ==> R y x
End

Theorem sym_flip:
  sym R /\ R a b ==> R b a
Proof
  FAST_TAC [Dest (iffLR sym_def)]
QED

Theorem sym_pointwise:
  (!x y:'a. R x y ==> R y x) ==> sym R
Proof
  FAST_TAC [Intro (iffRL sym_def)]
QED

(* --------------------------------------------------------------------------
   SAFE_TAC and CLARIFY_TAC: the non-search fragment.

   SAFE_TAC performs every safe step it can -- stripping, splitting
   conjunctions and case-splitting assumptions -- and never needs to
   backtrack, so it is a sound opening move for manual proofs.  It can
   close purely "safe" goals outright:
   -------------------------------------------------------------------------- *)

Theorem safe_closes_case_analysis:
  p \/ q ==> (p ==> r) ==> (q ==> r) ==> r
Proof
  SAFE_TAC []
QED

(* Where an unsafe step (here: a witness for the existential) is
   required, SAFE_TAC stops and leaves the decomposed goal for the
   user. *)

Theorem safe_stops_at_witness:
  P a ==> ?x:'a. P x
Proof
  SAFE_TAC [] >>
  qexists_tac ‘a’ >>
  FIRST_ASSUM ACCEPT_TAC
QED

(* CLARIFY_TAC performs only safe steps that do not split the goal --
   useful when a case split would obscure what remains to be proved. *)

Theorem clarify_then_finish:
  (!x:'a. P x ==> Q x) ==> P a ==> Q a
Proof
  CLARIFY_TAC [] >>
  FIRST_X_ASSUM MATCH_MP_TAC >>
  FIRST_ASSUM ACCEPT_TAC
QED

(* --------------------------------------------------------------------------
   The search variants.  On small goals they are interchangeable; they
   differ in how they explore the search space, and each dominates on
   some class of larger problems:

     BEST_TAC     expands the smallest open goal first, so it recovers
                  from a locally bad rule choice that would send
                  depth-first search down a long blind alley;
     SLOW_TAC     backtracks over more alternatives than FAST_TAC
                  (including how assumptions pair with rules), trading
                  time for coverage;
     ASTAR_TAC    best-first, weighting goal size against proof depth;
     DEEPEN_TAC   complete for its rule set: searches to depth 1, 2,
                  ... so it cannot diverge down an infinite branch.

   SLOW_BEST_TAC and SLOW_ASTAR_TAC are BEST_TAC and ASTAR_TAC run
   with SLOW_TAC's wider step, and FIRST_BEST_TAC is BEST_TAC free to
   expand whichever subgoal a rule applies to rather than always the
   leftmost -- the right choice when the leftmost subgoal is the one
   that needs a witness the others would have supplied.
   -------------------------------------------------------------------------- *)

(* Pelletier problem 26 *)
Theorem best_pelletier_26:
  ((?x:'a. p x) <=> (?x. q x)) /\
  (!x y. p x /\ q y ==> (r x <=> s y)) ==>
  ((!x. p x ==> r x) <=> (!x. q x ==> s x))
Proof
  BEST_TAC []
QED

(* Pelletier problem 18: the witness has to serve for every [x], so a
   depth-first searcher that commits to the first candidate never
   recovers; iterative deepening finds the two-step proof. *)
Theorem deepen_pelletier_18:
  ?y:'a. !x. P y ==> P x
Proof
  DEEPEN_TAC []
QED

(* Pelletier problem 24 *)
Theorem astar_pelletier_24:
  ~(?x:'a. s x /\ q x) /\ (!x. p x ==> q x \/ r x) /\
  (~(?x. p x) ==> ?x. q x) /\ (!x. q x \/ r x ==> s x) ==>
  ?x. p x /\ r x
Proof
  ASTAR_TAC []
QED

(* Pelletier problem 10 *)
Theorem slow_pelletier_10:
  (q ==> r) /\ (r ==> p /\ q) /\ (p ==> q \/ r) ==> (p <=> q)
Proof
  SLOW_TAC []
QED

(* Pelletier problem 25 *)
Theorem slow_best_pelletier_25:
  (?x:'a. p x) /\ (!x. f x ==> ~g x /\ r x) /\
  (!x. p x ==> g x /\ f x) /\
  ((!x. p x ==> q x) \/ ?x. q x /\ p x) ==>
  ?x. q x /\ p x
Proof
  SLOW_BEST_TAC []
QED

(* Pelletier problem 20 *)
Theorem first_best_pelletier_20:
  (!x y:'a. ?z. !w. p x /\ q y ==> r z /\ s w) ==>
  (?x y. p x /\ q y) ==> ?z. r z
Proof
  FIRST_BEST_TAC []
QED

(* Pelletier problem 41 *)
Theorem slow_astar_pelletier_41:
  (!z:'a. ?y. !x. (f x y <=> f x z /\ ~f x x)) ==> ~?z. !x. f x z
Proof
  SLOW_ASTAR_TAC []
QED
