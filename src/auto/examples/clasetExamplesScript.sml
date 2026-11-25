(* ==========================================================================
   Examples: declaring classical rules (clasetLib)

   The tactics of src/auto -- FAST_TAC, BLAST_TAC, AUTO_TAC, AESOP_TAC
   and friends -- search with the rules of the ambient *claset*, the
   rule database maintained by clasetLib.  A rule is a theorem together
   with a kind (introduction, elimination, destruction, forward, or
   normalisation) and a safety classification:

     safe rules    are applied eagerly and never need to be undone --
                   applying one preserves provability;
     unsafe rules  may need backtracking (they can lose provability or
                   require a witness), so only the search tactics try
                   them, and only inside their search.

   This theory shows the user-level declaration interface: theorem
   attributes ([sintro], [intro], [selim], [elim], [sdest], [dest],
   [sforward], [forward], [norm]), unsafe-rule priorities, the
   invocation-scoped markers (Intro, Dest, Del, ...), and the
   management API.  Rules declared with attributes persist: any theory
   importing this one inherits them, and the automation there finds
   them without further setup (aesopExamplesTheory relies on that).
   ========================================================================== *)

Theory clasetExamples
Ancestors
  clasetSeed
Libs
  clasetLib classicalLib aesopLib

(* --------------------------------------------------------------------------
   A tiny running example: predicates as sets.  [subp s t] is the subset
   relation on predicates and [inhab s] means [s] is inhabited.
   -------------------------------------------------------------------------- *)

Definition subp_def:
  subp s t <=> !x:'a. s x ==> t x
End

Definition inhab_def:
  inhab (s : 'a -> bool) <=> ?x. s x
End

(* --------------------------------------------------------------------------
   Safe introduction: [sintro].

   To prove [subp s t] it is always safe to prove the pointwise
   inclusion -- the two are equivalent, so no provability is lost.
   Declaring the rule [sintro] makes every claset-based tactic apply it
   eagerly whenever the goal's conclusion matches [subp s t].

   Note the explicit outer quantifiers: a declared rule must be a
   closed theorem.  The quantified variables are the rule's schematic
   ones -- a free variable would be treated as a fixed constant and
   the rule would only ever match itself.
   -------------------------------------------------------------------------- *)

Theorem subp_I[sintro]:
  !s t. (!x. s x ==> t x) ==> subp s t
Proof
  simp [subp_def]
QED

(* --------------------------------------------------------------------------
   Unsafe destruction: [dest].

   A destruction rule turns a matching assumption into its consequence:
   from [subp s t] the search may derive [s x ==> t x].  It is unsafe
   because the instantiation of [x] is a guess the search may have to
   revisit -- exactly like Isabelle's [dest] declarations.

   Unsafe declarations take an optional priority, a predicted success
   percentage from 1 to 100 (higher = tried earlier); [dest] alone
   uses the default ordering.
   -------------------------------------------------------------------------- *)

Theorem subp_D[dest]:
  !s t x. subp s t ==> s x ==> t x
Proof
  simp [subp_def]
QED

(* --------------------------------------------------------------------------
   Unsafe forward reasoning: [forward].

   A forward rule saturates the assumptions: whenever both premises are
   present, its conclusion is added as a new fact.  Here inhabitation
   propagates along inclusions.  Forward rules are consumed by the
   aesop engine (AESOP_TAC, aesopExamplesScript); the classical
   netpair-based searchers do not run them.
   -------------------------------------------------------------------------- *)

Theorem subp_inhab[forward]:
  !s t. subp s t ==> inhab s ==> inhab t
Proof
  simp [subp_def, inhab_def] >> metis_tac []
QED

(* --------------------------------------------------------------------------
   The declared rules at work.  The proofs below are pure claset
   search: FAST_TAC knows nothing about [subp] or [inhab] beyond the
   three declarations above.
   -------------------------------------------------------------------------- *)

Theorem subp_refl:
  subp s s
Proof
  FAST_TAC []
QED

Theorem subp_trans:
  subp r s /\ subp s t ==> subp r t
Proof
  FAST_TAC []
QED

Theorem inhab_mono_chain:
  subp r s /\ subp s t /\ inhab r ==> inhab t
Proof
  AESOP_TAC []
QED

(* --------------------------------------------------------------------------
   Invocation-scoped rules: the markers.

   Wrapping a theorem in one of the clasetLib markers inside a tactic's
   theorem-list argument adds it as a rule for that invocation only --
   nothing is installed in the global claset.  The markers mirror the
   attributes: SIntro, Intro, SElim, Elim, SDest, Dest, SForward,
   Forward, Norm, plus Simp/Iff (see clasimpExamplesScript) and
   Del "name", which hides a named rule for the invocation.

   Here the pointwise reading of [subp] is supplied as a one-off
   destruction rule derived from the definition, with the permanent
   [subp_D] rule switched off, so the proof exercises the marker rather
   than the declaration.
   -------------------------------------------------------------------------- *)

Theorem subp_D_marker_demo:
  subp s t /\ s x ==> t x
Proof
  FAST_TAC [Del "clasetExamples.subp_D", Dest (iffLR subp_def)]
QED

(* An Intro marker: introducing [inhab] needs a witness, so the rule is
   unsafe, and no permanent declaration was made for it above -- the
   marker supplies it just for this proof. *)

Theorem inhab_eq:
  inhab (\x. x = (a:'a))
Proof
  FAST_TAC [Intro (iffRL inhab_def)]
QED

(* A plain theorem in the list is inserted as a fact (an extra
   assumption) rather than as a rule.  Here the fact [inhab_sing]
   feeds the [forward] declaration [subp_inhab]: without it the claset
   has no way to establish inhabitation. *)

Definition sing_def:
  sing (a:'a) = \x. x = a
End

Theorem inhab_sing:
  inhab (sing (a:'a))
Proof
  simp [inhab_def, sing_def]
QED

Theorem inhab_fact_demo:
  subp (sing (a:'a)) s ==> inhab s
Proof
  AESOP_TAC [inhab_sing]
QED

(* --------------------------------------------------------------------------
   Priorities on unsafe declarations.

   An unsafe attribute may carry a number from 1 to 100: the predicted
   percentage of goals on which trying the rule pays off.  Candidates
   are tried in decreasing order of it, so a cheap, usually-right rule
   can be put ahead of a speculative one.  Introducing [inhab s]
   requires inventing a witness, which succeeds only when the witness
   is already in reach, hence the modest 40 below.  (Safe declarations
   are applied eagerly and unconditionally, so a priority on one is
   ignored.)
   -------------------------------------------------------------------------- *)

Theorem inhab_I[intro=40]:
  !s x. s x ==> inhab (s:'a -> bool)
Proof
  simp [inhab_def] >> metis_tac []
QED

Theorem inhab_of_member:
  s (a:'a) ==> inhab s
Proof
  FAST_TAC []
QED

(* --------------------------------------------------------------------------
   Safe elimination: [selim].

   An elimination rule consumes a matching assumption and continues
   with the goal in a context where the assumption has been taken
   apart; unlike a destruction rule it may bind fresh variables.
   Taking apart [meets s t] -- the two predicates share an element --
   gives that element, which is safe: the assumption says one exists.
   So the rule is declared [selim] and the searchers apply it eagerly.
   The unsafe variant is [elim], with the same optional priority as
   [dest] and [intro].

   With the elimination and introduction rules both declared, the
   proof below is entirely automatic: eliminate the assumption to get
   the shared element, then introduce the conclusion with it.
   -------------------------------------------------------------------------- *)

Definition meets_def:
  meets s t <=> ?x:'a. s x /\ t x
End

Theorem meets_E[selim]:
  !s t P. meets s t ==> (!x:'a. s x ==> t x ==> P) ==> P
Proof
  simp [meets_def] >> metis_tac []
QED

Theorem meets_I[intro]:
  !s t x. s x ==> t x ==> meets (s:'a -> bool) t
Proof
  simp [meets_def] >> metis_tac []
QED

Theorem meets_sym:
  meets s t ==> meets t (s:'a -> bool)
Proof
  FAST_TAC []
QED

(* --------------------------------------------------------------------------
   Normalisation rules: [norm].

   A [norm] rule is applied to every goal in the normalisation phase
   that precedes search, repeatedly until nothing changes -- the place
   for canonicalising a spelling rather than reasoning about it.  Here
   [nonempty] is a synonym users write, and the [norm] rule rewrites it
   away so the search only ever sees [inhab].  Normalisation rules are
   consumed by the aesop engine; the classical searchers ignore them.

   [norm] also accepts a number -- an ordering penalty rather than a
   success percentage, so it may be negative and is written [norm=~3]
   in HOL4's numeric syntax.  Rules run in increasing penalty order,
   with 0 the default, which lets a cheap rewrite be forced ahead of
   an expensive one.
   -------------------------------------------------------------------------- *)

Definition nonempty_def:
  nonempty (s : 'a -> bool) <=> inhab s
End

Theorem nonempty_norm[norm]:
  !s. inhab s ==> nonempty (s:'a -> bool)
Proof
  simp [nonempty_def]
QED

(* The same goal as [inhab_of_member] above, written in the synonym:
   normalisation turns it back into the [inhab] form, and the search
   then closes it with the [intro=40] rule as before. *)

Theorem nonempty_of_member:
  s (a:'a) ==> nonempty s
Proof
  AESOP_TAC []
QED

(* --------------------------------------------------------------------------
   Management API (a tour; nothing below changes this theory's
   declarations):

     export_rule spec "thy.name"   declare a stored theorem, persistently;
                                   the attribute form above is preferred
     temp_add_rule spec (n, th)    session-local declaration
     delrule "thy.name"            retract a declaration, persistently
     temp_delrule "thy.name"       retract for this session only
     the_claset ()                 the ambient claset
     rules_of cs                   every declaration, in canonical order
     pp_claset                     pretty-printer for clasets

   Rule names: an attribute declaration is recorded under
   "<theory>.<theorem-name>"; those are the names Del and delrule take.

   A retracted declaration disappears for descendant theories too.  The
   theorem below is declared and immediately retracted, so importing
   theories never see it as a rule.
   -------------------------------------------------------------------------- *)

Theorem subp_retracted[dest]:
  !s (b:'a) x. subp s ((=) b) ==> s x ==> x = b
Proof
  simp [subp_def]
QED

val _ = delrule "clasetExamples.subp_retracted"
