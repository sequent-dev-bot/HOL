Theory pairAutoSeed
Ancestors
  pair
Libs
  clasetLib clasimpLib

(* src/HOL/Product_Type.thy:520,524 @ f7e02b7e.  [split_paired_All] and
   [split_paired_Ex] are simp there and declared to no simpset here, so
   a quantifier over a pair is never taken apart.  Declared [iff] and
   not [simp]: as a rewrite it fires on every pair quantifier, and the
   translated goals quantify over pairs constantly -- measured, that
   stalls the list/map family.  As an iff rule it reaches the classical
   search, which applies it to a goal rather than to every subterm. *)
Theorem FORALL_PROD_AUTO[iff] = pairTheory.FORALL_PROD
Theorem EXISTS_PROD_AUTO[iff] = pairTheory.EXISTS_PROD

(* src/HOL/Product_Type.thy:604-637 @ f7e02b7e *)
Theorem UNCURRY_AUTO_IFF[iff]:
  !c p. UNCURRY c p <=> !x y. p = (x,y) ==> c x y
Proof
  Cases_on `p` >> simp [UNCURRY_DEF]
QED

(* src/HOL/Product_Type.thy:600,607 @ f7e02b7e.  Isabelle states
   [case_prodI2'] and [case_prodE'] separately from the two above, and
   declares both safe, because a paired abstraction can be applied to
   further arguments: the rule above is about a proposition and this one
   about a predicate.  The two do not overlap -- [UNCURRY c p] there is
   a boolean and here it is a function. *)
Theorem UNCURRY_APPLIED_AUTO_IFF[iff]:
  !c p z. UNCURRY c p z <=> !x y. p = (x,y) ==> c x y z
Proof
  Cases_on `p` >> simp [UNCURRY_DEF]
QED

(* src/HOL/Product_Type.thy:788-791 @ f7e02b7e *)
Theorem CURRY_AUTO_IFF[iff]:
  !f x y. CURRY f x y <=> f (x,y)
Proof
  simp [pairTheory.CURRY_DEF]
QED

(* src/HOL/Wellfounded.thy:1239,1291 @ f7e02b7e.  [in_lex_prod] is simp
   there and [wf_lex_prod] a safe intro, so a source proof that unfolds
   a definition built on the pair lexicographic product -- [lenlex] is
   one -- never names either.  pair states both and declares neither.

   [wf_lex_prod] is declared unsafe against Isabelle's [intro!]: the
   inversion seedAudit owes a safe intro is WF (R LEX Q) ==> WF R /\
   WF Q, which the audit's prover stack does not close. *)
Theorem LEX_APPLIED_AUTO[simp] = pairTheory.LEX_DEF_THM

Theorem WF_LEX_AUTO[intro] = pairTheory.WF_LEX
