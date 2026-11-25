Theory finite_mapAutoSeed
Ancestors
  finite_map alist
Libs
  clasetLib clasimpLib

val sintro_spec =
  {kind = clasetRules.Intro, safe = true, prio = NONE}

(* src/HOL/Map.thy:354-396,565-575,854-931 @ f7e02b7e.
   Isabelle map addition is right-biased, whereas FUNION is left-biased. *)
Theorem FMAP_AUTO_FUNION_SOME[iff]:
  FLOOKUP (FUNION n m) k = SOME x <=>
  FLOOKUP n k = SOME x \/
  FLOOKUP n k = NONE /\ FLOOKUP m k = SOME x
Proof
  Cases_on `FLOOKUP n k` >>
  simp [finite_mapTheory.FLOOKUP_FUNION]
QED

Theorem FMAP_AUTO_FUNION_NONE[iff]:
  FLOOKUP (FUNION n m) k = NONE <=>
  FLOOKUP n k = NONE /\ FLOOKUP m k = NONE
Proof
  Cases_on `FLOOKUP n k` >>
  simp [finite_mapTheory.FLOOKUP_FUNION]
QED

Theorem FMAP_AUTO_FLOOKUP_DOM[iff]:
  k IN FDOM f <=> FLOOKUP f k <> NONE
Proof
  simp [finite_mapTheory.FLOOKUP_DEF]
QED

Theorem OPTION_DOMAIN_NEQ_NONE_AUTO[iff]:
  !mapping missing key.
    mapping missing = NONE ==>
    (((?value. mapping key = SOME value) /\ key <> missing) <=>
     ?value. mapping key = SOME value)
Proof
  rw[EQ_IMP_THM]
  >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem OPTION_DOMAIN_NEQ_NONE_CONJ_AUTO[iff]:
  !mapping missing key guard.
    mapping missing = NONE ==>
    (((?value. mapping key = SOME value) /\ key <> missing /\ guard) <=>
     (?value. mapping key = SOME value) /\ guard)
Proof
  rw[EQ_IMP_THM]
  >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

(* A successful lookup is the canonical simplifier consequence of a
   distinct association-list membership.  This is Isabelle Map.thy's
   map_of_is_SomeI rule in HOL4's ALOOKUP representation. *)
Theorem ALOOKUP_ALL_DISTINCT_MEM_AUTO[simp]:
  !association key value.
    ALL_DISTINCT (MAP FST association) /\
    MEM (key, value) association ==>
    ALOOKUP association key = SOME value
Proof
  rpt gen_tac
  >> MATCH_ACCEPT_TAC alistTheory.ALOOKUP_ALL_DISTINCT_MEM
QED

Theorem ALOOKUP_EQ_SOME_DISTINCT_AUTO[iff]:
  !association key value.
    ALL_DISTINCT (MAP FST association) ==>
    (ALOOKUP association key = SOME value <=>
     MEM (key, value) association)
Proof
  rw[boolTheory.EQ_IMP_THM]
  >- metis_tac[alistTheory.ALOOKUP_MEM]
  >> metis_tac[alistTheory.ALOOKUP_ALL_DISTINCT_MEM]
QED

Theorem ALOOKUP_MEM_DISTINCT_AUTO:
  !association key value.
    ALL_DISTINCT (MAP FST association) ==>
    (MEM (key, value) association <=>
     ALOOKUP association key = SOME value)
Proof
  simp[ALOOKUP_EQ_SOME_DISTINCT_AUTO]
QED

(* Pointwise form of set_map[symmetric] after MAP SND (ZIP (xs,ys)) = ys. *)
Theorem MEM_SND_ZIP_AUTO:
  !keys values value.
    LENGTH keys = LENGTH values ==>
    (MEM value values <=>
     ?key. MEM (key, value) (ZIP (keys, values)))
Proof
  Induct
  >> Cases_on `values`
  >> simp[]
  >> metis_tac[]
QED

Theorem FDOM_EQ_EMPTY_AUTO[iff] = finite_mapTheory.FDOM_EQ_EMPTY
Theorem FDOM_EQ_EMPTY_SYM_AUTO[iff] = finite_mapTheory.FDOM_EQ_EMPTY_SYM
Theorem FEMPTY_SUBMAP_AUTO[iff] = finite_mapTheory.FEMPTY_SUBMAP
Theorem SUBMAP_ANTISYM_AUTO[iff] = finite_mapTheory.SUBMAP_ANTISYM

val _ =
  List.app (clasetLib.export_rule sintro_spec)
    ["finite_map.SUBMAP_FEMPTY", "finite_map.SUBMAP_REFL"]

val _ =
  clasetLib.export_rule
    {kind = clasetRules.Forward, safe = false, prio = SOME 10}
    "finite_map.SUBMAP_TRANS"
