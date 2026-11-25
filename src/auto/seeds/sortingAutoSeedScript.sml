Theory sortingAutoSeed
Ancestors
  sorting
Libs
  clasetLib clasimpLib

val sintro_spec =
  {kind = clasetRules.Intro, safe = true, prio = NONE}
val intro_spec =
  {kind = clasetRules.Intro, safe = false, prio = NONE}
val dest_spec =
  {kind = clasetRules.Dest, safe = false, prio = NONE}
val forward_spec =
  {kind = clasetRules.Forward, safe = false, prio = SOME 10}

(* src/HOL/List.thy:5900-6433 @ f7e02b7e. *)
Theorem SORTED_EQ_AUTO[iff] = sortingTheory.SORTED_EQ
Theorem SORTED_APPEND_AUTO[iff] = sortingTheory.SORTED_APPEND

Theorem PERM_NIL_1_AUTO[iff] =
  GEN_ALL (CONJUNCT1 (SPEC_ALL sortingTheory.PERM_NIL))

Theorem PERM_NIL_2_AUTO[iff] =
  GEN_ALL (CONJUNCT2 (SPEC_ALL sortingTheory.PERM_NIL))

Theorem PERM_SING_1_AUTO[iff] =
  GEN_ALL (CONJUNCT1 (SPEC_ALL sortingTheory.PERM_SING))

Theorem PERM_SING_2_AUTO[iff] =
  GEN_ALL (CONJUNCT2 (SPEC_ALL sortingTheory.PERM_SING))

Theorem PERM_CONS_IFF_AUTO[iff] = sortingTheory.PERM_CONS_IFF

Theorem PERM_APPEND_IFF_1_AUTO[iff] =
  GEN_ALL (CONJUNCT1 (SPEC_ALL sortingTheory.PERM_APPEND_IFF))

Theorem PERM_APPEND_IFF_2_AUTO[iff] =
  GEN_ALL (CONJUNCT2 (SPEC_ALL sortingTheory.PERM_APPEND_IFF))

val _ =
  List.app (clasetLib.export_rule sintro_spec)
    ["sorting.SORTED_NIL", "sorting.SORTED_SING",
     "sorting.PERM_REFL"]

val _ =
  List.app (clasetLib.export_rule intro_spec)
    ["sorting.SORTED_FILTER", "sorting.QSORT_SORTED",
     "sorting.QSORT_PERM"]

val _ = clasetLib.export_rule dest_spec "sorting.SORTED_TL"

val _ =
  List.app (clasetLib.export_rule forward_spec)
    ["sorting.SORTED_ALL_DISTINCT", "sorting.PERM_TRANS",
     "sorting.MEM_PERM", "sorting.PERM_EVERY",
     "sorting.ALL_DISTINCT_PERM", "sorting.SORTED_PERM_EQ"]

(* src/HOL/List.thy:6208 @ f7e02b7e.  [sorted_upt] is simp there.  HOL4
   states the strict form, SORTED_GENLIST_PLUS, and declares it nowhere;
   Isabelle's [sorted] is the reflexive order, which is the form a goal
   about an interval of indices arrives in. *)
Theorem SORTED_GENLIST_INTERVAL_AUTO[simp]:
  !start count. SORTED $<= (GENLIST ($+ start) count)
Proof
  rw[sortingTheory.SORTED_EL_SUC] >> simp[]
QED

(* src/HOL/List.thy:5882 @ f7e02b7e.  [sorted_wrt_take] and
   [sorted_wrt_drop] are simp there.  HOL4 states neither.  Isabelle's
   sorted_wrt is all-pairs and HOL4's SORTED adjacent, but a segment of a
   SORTED list is SORTED for the adjacent reading too, with no side
   condition on the relation. *)
Theorem SORTED_TAKE_AUTO[simp]:
  !relation elements count. SORTED relation elements ==>
                            SORTED relation (TAKE count elements)
Proof
  metis_tac[sortingTheory.SORTED_APPEND_GEN, listTheory.TAKE_DROP]
QED

Theorem SORTED_DROP_AUTO[simp]:
  !relation elements count. SORTED relation elements ==>
                            SORTED relation (DROP count elements)
Proof
  metis_tac[sortingTheory.SORTED_APPEND_GEN, listTheory.TAKE_DROP]
QED
