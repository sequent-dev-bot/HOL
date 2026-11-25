(* ==========================================================================
   Examples: combined classical reasoning and simplification
   (clasimpLib)

   The tactics of src/auto/clasimp interleave claset search with the
   simplifier, as Isabelle/HOL's clasimp methods do:

     AUTO_TAC        simplify + classical search on all subgoals,
                     keeping whatever progress it makes  (auto)
     FORCE_TAC       everything AUTO_TAC has plus depth-search;
                     closes the goal or fails            (force)
     FASTFORCE_TAC   depth-first search with full
                     simplification at every node        (fastforce)
     SLOWSIMP_TAC    FASTFORCE with more backtracking    (slowsimp)
     BESTSIMP_TAC    best-first FASTFORCE                (bestsimp)
     CLARSIMP_TAC    safe steps + simplification only;
                     no unsafe search                    (clarsimp)

   The simplifier side uses the ambient srw_ss() simpset, lifted into
   the extension engine, so everything a bare simp[] knows is
   available, and the claset side uses the ambient claset
   (clasetExamplesScript).  Beyond facts and the claset markers, the
   [thm list] accepts:

     Simp th      use th as a rewrite for this invocation
     Iff th       install th as claset rules AND rewrite, both ways
     markerLib controls (NoAsms, literal Excl "name", ...)
     simpLib.Split and ExclX for extension controls

   and the [iff] theorem attribute is the persistent form of Iff.
   ========================================================================== *)

Theory clasimpExamples
Ancestors
  clasetSeed list
Libs
  clasetLib clasimpLib

(* --------------------------------------------------------------------------
   AUTO_TAC: simplification and classical search in one call, so goals
   mixing rewriting (list, option, set membership) with logical steps
   go through without choosing between simp and the classical
   searchers.
   -------------------------------------------------------------------------- *)

Theorem auto_mem_append:
  MEM (x:'a) l ==> MEM x (l ++ [y])
Proof
  AUTO_TAC []
QED

Theorem auto_union_lemma:
  (x:'a) IN (s UNION t) /\ x NOTIN s ==> x IN t
Proof
  AUTO_TAC []
QED

(* AUTO_TAC splits conditionals and datatype case expressions where
   plain simplification stalls. *)

Theorem auto_cond_split:
  (if b then x = (1:num) else x = 2) ==> x <> 0
Proof
  AUTO_TAC []
QED

Datatype:
  signal = Stop | Wait | Go
End

Theorem auto_case_split:
  (case s of Stop => (x:'a) | Wait => x | Go => y) = z ==>
  z = x \/ z = y
Proof
  AUTO_TAC []
QED

(* --------------------------------------------------------------------------
   FORCE_TAC and FASTFORCE_TAC: all-or-nothing versions.  Use them
   when a partial simplification would be useless: they either close
   the goal or fail cleanly, never leaving a half-simplified state.
   -------------------------------------------------------------------------- *)

Theorem force_mem_bound:
  (!x:num. MEM x l ==> x < 7) /\ MEM y l ==> y < 7
Proof
  FORCE_TAC []
QED

Theorem fastforce_filter_nil:
  EVERY P (l:'a list) ==> FILTER (\x. ~P x) l = []
Proof
  FASTFORCE_TAC [Simp listTheory.FILTER_EQ_NIL,
                 Simp listTheory.EVERY_MEM]
QED

(* SLOWSIMP_TAC backtracks over more alternatives than FASTFORCE_TAC,
   and BESTSIMP_TAC searches best-first; both are drop-in
   replacements to reach for when FASTFORCE_TAC gives up. *)

Theorem slowsimp_demo:
  (x:'a) IN (s DIFF t) ==> x IN s
Proof
  SLOWSIMP_TAC []
QED

Theorem bestsimp_demo:
  MEM (y:'a) [x] ==> y = x
Proof
  BESTSIMP_TAC []
QED

(* --------------------------------------------------------------------------
   CLARSIMP_TAC: clarify + simplify, no unsafe steps.  It leaves a
   deterministic residue for the user to finish -- the workhorse
   opening move of interactive proofs.
   -------------------------------------------------------------------------- *)

Theorem clarsimp_then_finish:
  ~NULL (l:'a list) ==> ?x xs. l = x::xs
Proof
  CLARSIMP_TAC [listTheory.NULL_EQ] >>
  Cases_on ‘l’ >> AUTO_TAC []
QED

(* --------------------------------------------------------------------------
   The [iff] attribute: the analogue of Isabelle's [iff] declarations.

   Declaring an equivalence [iff] installs it both as a rewrite in the
   ambient simpset and as introduction/elimination rules in the
   claset, so every tactic in this layer can use it in whichever form
   fits.  Like the claset attributes it persists into importing
   theories; clasimpLib.remove_iff retracts it.
   -------------------------------------------------------------------------- *)

Definition tagged_def:
  tagged (l:'a list) <=> l <> []
End

Theorem tagged_iff[iff]:
  !l:'a list. tagged l <=> l <> []
Proof
  simp [tagged_def]
QED

Theorem tagged_cons:
  tagged ((x:'a)::xs)
Proof
  AUTO_TAC []
QED

Theorem tagged_append:
  tagged (l1:'a list) ==> tagged (l1 ++ l2)
Proof
  AUTO_TAC []
QED

(* The Iff marker is the invocation-scoped form of the same
   declaration: AUTO_TAC [Iff someEquivalence] installs the rules and
   the rewrite for that call only, and nothing persists. *)

(* --------------------------------------------------------------------------
   Simp markers and simplifier controls.  A Simp-wrapped theorem joins
   the invocation simpset -- the counterpart of simp[th] -- and the
   generic simplifier controls (markerLib.NoAsms, Excl, ...) are
   forwarded to the simplifier inside these tactics exactly as they
   are inside simp[].
   -------------------------------------------------------------------------- *)

Definition swap_def:
  swap (p : 'a # 'b) = (SND p, FST p)
End

Theorem swap_swap:
  swap (swap (p : 'a # 'b)) = p
Proof
  AUTO_TAC [Simp swap_def]
QED

Theorem simp_marker_demo:
  EVERY (\x. 0 < x) l ==> ~MEM (0:num) l
Proof
  AUTO_TAC [Simp listTheory.EVERY_MEM]
QED
