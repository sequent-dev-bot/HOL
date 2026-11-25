(* ==========================================================================
   Examples: best-first proof search (aesopLib)

   AESOP_TAC is a best-first search engine in the style of Lean's
   Aesop: it treats claset rules, normalisation and the simplifier as
   moves in a single prioritised search tree.  Each expansion
   normalises the goal, applies safe rules to saturation, and then
   branches on unsafe rules ordered by their declared success
   probability.

     AESOP_TAC ths        close the goal or fail
     AESOP_SAFE_TAC ths   normalisation and safe rules only; keeps
                          progress and leaves the residue

   Both use the ambient claset and simpset and accept the same
   [thm list] as the clasimp tactics: facts, claset markers (Intro,
   Dest, Forward, ...), Simp/Iff markers and simplifier controls.

   The CS_ variants take an explicit aesop_config, claset and simpset;
   augment_aesop and augment_aesop_rule add session-local rules with
   custom tactics -- see aesopLib.sig.

   This theory imports clasetExamplesTheory, so the [sintro]/[dest]/
   [forward] declarations made there for [subp] and [inhab] are in
   force here -- persistence of declarations across the theory
   hierarchy is itself part of the design.
   ========================================================================== *)

Theory aesopExamples
Ancestors
  clasetExamples list
Libs
  clasetLib aesopLib

(* --------------------------------------------------------------------------
   Propositional reasoning.
   -------------------------------------------------------------------------- *)

(* Pelletier problem 12 *)
Theorem aesop_iff_assoc:
  ((p <=> q) <=> r) <=> (p <=> (q <=> r))
Proof
  AESOP_TAC []
QED

(* Pelletier problem 13 *)
Theorem aesop_distrib:
  p \/ q /\ r <=> (p \/ q) /\ (p \/ r)
Proof
  AESOP_TAC []
QED

(* Pelletier problem 17 *)
Theorem aesop_pelletier_17:
  ((p /\ (q ==> r)) ==> s) <=>
  ((~p \/ q \/ s) /\ (~p \/ ~r \/ s))
Proof
  AESOP_TAC []
QED

(* --------------------------------------------------------------------------
   Rules declared in ancestor theories are found automatically: the
   [sintro]/[dest] rules for [subp] and the [forward] rule connecting
   it to [inhab] were declared in clasetExamplesScript, one theory
   below this one.
   -------------------------------------------------------------------------- *)

Theorem aesop_subp_refl:
  subp s s
Proof
  AESOP_TAC []
QED

Theorem aesop_inhab_mono:
  subp r s /\ inhab r ==> inhab s
Proof
  AESOP_TAC []
QED

(* --------------------------------------------------------------------------
   Simplification is interleaved with the search, so goals mixing
   rewriting with logical steps go through in one call.
   -------------------------------------------------------------------------- *)

Theorem aesop_the_some:
  THE (SOME (x:'a)) = x
Proof
  AESOP_TAC []
QED

Theorem aesop_mem_append:
  MEM (x:'a) l ==> MEM x (l ++ [y])
Proof
  AESOP_TAC []
QED

Theorem aesop_every_append:
  EVERY P l1 /\ EVERY P (l2:'a list) ==> EVERY P (l1 ++ l2)
Proof
  AESOP_TAC []
QED

(* --------------------------------------------------------------------------
   AESOP_SAFE_TAC: the safe fragment, for use mid-proof.  It applies
   normalisation and safe rules only, so its output is a deterministic
   simplified residue -- like SAFE_TAC with the simplifier's power.
   -------------------------------------------------------------------------- *)

Theorem aesop_safe_then_finish:
  P a ==> ?x:'a. P x
Proof
  AESOP_SAFE_TAC [] >>
  qexists_tac ‘a’ >>
  FIRST_ASSUM ACCEPT_TAC
QED

(* --------------------------------------------------------------------------
   Markers.  A Forward marker turns a theorem into an invocation-only
   forward rule.  [covers] has no declared rules, so the marker is
   what lets the search saturate the assumptions with [inhab s].
   -------------------------------------------------------------------------- *)

Definition covers_def:
  covers s t <=> !x:'a. t x ==> s x
End

Theorem covers_inhab:
  !s t:'a->bool. covers s t ==> inhab t ==> inhab s
Proof
  metis_tac [covers_def, clasetExamplesTheory.inhab_def]
QED

Theorem aesop_forward_marker:
  covers s r /\ inhab r ==> inhab s
Proof
  AESOP_TAC [Forward covers_inhab]
QED
