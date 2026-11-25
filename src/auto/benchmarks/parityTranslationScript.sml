Theory parityTranslation
Ancestors
  sorting relation integer string alist set_relation monoid bit

(* Isabelle/HOL src/HOL/List.thy:5911-5974.  Unlike HOL4's adjacent
   SORTED predicate, sorted_wrt relates every earlier element to every
   later element. *)
Definition source_sorted_wrt_def:
  (source_sorted_wrt relation ([] : 'a list) <=> T) /\
  (source_sorted_wrt relation (head::tail) <=>
     (!item. MEM item tail ==> relation head item) /\
     source_sorted_wrt relation tail)
End

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/List.thy:399-442.  A source linorder is represented by its
   explicit weak ordering relation.  Isabelle's [sorted] is
   [sorted_wrt (<=)] -- the all-pairs reading, not HOL4's adjacent
   SORTED, which the two agree with only for a transitive relation.
   Isabelle's strict operation is HOL4's STRORD construction on that
   relation. *)
Definition source_sorted_def:
  source_sorted le (xs : 'a list) = source_sorted_wrt le xs
End

(* Isabelle has no [strict_sorted] constant: it writes [sorted_wrt (<)]
   inline, so its goals carry [sorted_wrt]'s own equations and nothing
   else.  Reading the notation onto SORTED instead would hand a goal the
   adjacent predicate where the source had the all-pairs one, and the
   cons equation Isabelle proves [strict_sorted_simps] from would not be
   there. *)
Definition source_strict_sorted_def:
  source_strict_sorted le (xs : 'a list) =
    source_sorted_wrt (relation$STRORD le) xs
End

Theorem source_sorted_wrt_bridge:
  !relation xs.
    relation$transitive relation ==>
    (source_sorted_wrt relation xs <=>
     sorting$SORTED relation xs)
Proof
  gen_tac
  >> Induct
  >- simp[source_sorted_wrt_def]
  >> simp[source_sorted_wrt_def, sortingTheory.SORTED_EQ,
          CONJ_COMM]
QED

(* [sorted] and HOL4's SORTED agree exactly when the relation is
   transitive, which is what the source linorder always supplies. *)
Theorem source_sorted_bridge:
  !le xs : 'a list.
    relation$transitive le ==>
    (source_sorted le xs <=> sorting$SORTED le xs)
Proof
  simp[source_sorted_def, source_sorted_wrt_bridge]
QED

Theorem source_strict_sorted_bridge:
  !le xs : 'a list.
    relation$transitive (relation$STRORD le) ==>
    (source_strict_sorted le xs <=>
     sorting$SORTED (relation$STRORD le) xs)
Proof
  simp[source_strict_sorted_def, source_sorted_wrt_bridge]
QED

Theorem source_sorted_wrt_nth_less:
  !relation xs.
    source_sorted_wrt relation xs <=>
    !left right.
      left < right ==> right < LENGTH xs ==>
      relation (EL left xs) (EL right xs)
Proof
  gen_tac
  >> Induct
  >- simp[source_sorted_wrt_def]
  >> simp[source_sorted_wrt_def, listTheory.MEM_EL]
  >> gen_tac
  >> eq_tac
  >- (strip_tac
      >> rpt gen_tac
      >> strip_tac
      >> Cases_on `left`
      >> Cases_on `right`
      >> fs[]
      >> metis_tac[])
  >> strip_tac
  >> conj_tac
  >- (rpt gen_tac
      >> strip_tac
      >> fs[]
      >> qpat_x_assum `!left right. _`
           (qspecl_then [`0`, `SUC n`] mp_tac)
      >> simp[])
  >> rpt gen_tac
  >> strip_tac
  >> qpat_x_assum `!left right. _`
       (qspecl_then [`SUC left`, `SUC right`] mp_tac)
  >> simp[]
QED

Theorem source_sorted_wrt_not_adjacent:
  sorting$SORTED
    (\left right : num. right = SUC left) [0; 1; 2] /\
  ~source_sorted_wrt
    (\left right : num. right = SUC left) [0; 1; 2]
Proof
  simp[source_sorted_wrt_def]
QED

Theorem source_weak_linear_transitive:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==> relation$transitive le
Proof
  simp[relationTheory.WeakLinearOrder,
       relationTheory.WeakOrder]
QED

Theorem source_weak_linear_reflexive:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==> relation$reflexive le
Proof
  simp[relationTheory.WeakLinearOrder,
       relationTheory.WeakOrder]
QED

Theorem source_weak_linear_antisymmetric:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    relation$antisymmetric le
Proof
  simp[relationTheory.WeakLinearOrder,
       relationTheory.WeakOrder]
QED

Theorem source_weak_linear_refl:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==> !value. le value value
Proof
  rpt strip_tac
  >> drule source_weak_linear_reflexive
  >> simp[relationTheory.reflexive_def]
QED

Theorem source_sorted_wrt_dropWhile:
  !relation predicate xs.
    source_sorted_wrt relation xs ==>
    source_sorted_wrt relation (dropWhile predicate xs)
Proof
  Induct_on `xs`
  >- simp[source_sorted_wrt_def, listTheory.dropWhile_def]
  >> rpt gen_tac
  >> Cases_on `predicate h`
  >- simp[source_sorted_wrt_def, listTheory.dropWhile_def]
  >> simp[source_sorted_wrt_def, listTheory.dropWhile_def]
QED

Theorem source_sorted_wrt_length01:
  !relation xs.
    LENGTH xs <= 1 ==> source_sorted_wrt relation xs
Proof
  rpt gen_tac
  >> Cases_on `xs`
  >- simp[source_sorted_wrt_def]
  >> Cases_on `t`
  >> simp[source_sorted_wrt_def]
QED

Theorem source_sorted_wrt_drop:
  !relation count xs.
    source_sorted_wrt relation xs ==>
    source_sorted_wrt relation (DROP count xs)
Proof
  gen_tac
  >> Induct
  >- simp[]
  >> Cases_on `xs`
  >> simp[source_sorted_wrt_def]
QED

Theorem source_sorted_wrt_append:
  !relation xs ys.
    source_sorted_wrt relation (xs ++ ys) <=>
    source_sorted_wrt relation xs /\ source_sorted_wrt relation ys /\
    (!left right. MEM left xs ==> MEM right ys ==> relation left right)
Proof
  gen_tac
  >> Induct
  >- simp[source_sorted_wrt_def]
  >> simp[source_sorted_wrt_def]
  >> metis_tac[]
QED

Theorem source_sorted_wrt_map:
  !relation function xs.
    source_sorted_wrt relation (MAP function xs) <=>
    source_sorted_wrt
      (\left right. relation (function left) (function right)) xs
Proof
  ntac 2 gen_tac
  >> Induct
  >> simp[source_sorted_wrt_def, listTheory.MEM_MAP]
  >> metis_tac[]
QED

Theorem source_sorted_wrt_mono_rel:
  !weaker stronger xs.
    (!left right.
       MEM left xs ==> MEM right xs ==> stronger left right ==>
       weaker left right) ==>
    source_sorted_wrt stronger xs ==> source_sorted_wrt weaker xs
Proof
  ntac 2 gen_tac
  >> Induct
  >> simp[source_sorted_wrt_def]
  >> metis_tac[]
QED

Theorem source_sorted_wrt_iff_nth_Suc_transp:
  !relation xs.
    relation$transitive relation ==>
    (source_sorted_wrt relation xs <=>
     !index. SUC index < LENGTH xs ==>
             relation (EL index xs) (EL (SUC index) xs))
Proof
  rpt strip_tac
  >> simp[source_sorted_wrt_bridge, sortingTheory.SORTED_EL_SUC]
QED

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/List.thy:6049.  The [<] characterisation of [sorted], with
   its two antecedents curried; sorting$SORTED_EL_LESS conjoins them
   and is stated on HOL4's own SORTED. *)
Theorem source_sorted_iff_nth_mono_less:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !xs.
      (source_sorted le xs <=>
       !left right.
         left < right ==> right < LENGTH xs ==>
         le (EL left xs) (EL right xs))
Proof
  rpt strip_tac
  >> drule source_weak_linear_transitive
  >> strip_tac
  >> simp[source_sorted_bridge, sortingTheory.SORTED_EL_LESS]
  >> metis_tac[]
QED

Theorem source_sorted_iff_nth_mono:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !xs.
      (source_sorted le xs <=>
       !left right.
         left <= right ==> right < LENGTH xs ==>
         le (EL left xs) (EL right xs))
Proof
  rpt strip_tac
  >> drule source_weak_linear_transitive
  >> strip_tac
  >> drule source_weak_linear_refl
  >> strip_tac
  >> simp[source_sorted_bridge, sortingTheory.SORTED_EL_LESS]
  >> eq_tac
  >> rpt strip_tac
  >- (Cases_on `left = right` >> simp[] >> first_x_assum irule >> simp[])
  >> first_x_assum irule
  >> simp[]
QED

Theorem source_sorted_same:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !value xs.
      source_sorted le (FILTER (\item. item = value) xs)
Proof
  rpt strip_tac
  >> Induct_on `xs`
  >- simp[source_sorted_def, source_sorted_wrt_def]
  >> simp[source_sorted_def]
  >> Cases_on `h = value`
  >> fs[source_sorted_def, source_sorted_wrt_def, listTheory.MEM_FILTER]
  >> metis_tac[source_weak_linear_refl]
QED

Theorem source_genlist_el_take:
  !xs count.
    count <= LENGTH xs ==>
    GENLIST (\index. EL index xs) count = TAKE count xs
Proof
  rw[listTheory.LIST_EQ_REWRITE, listTheory.EL_GENLIST,
     listTheory.EL_TAKE]
QED

Theorem source_strord_transitive:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    relation$transitive (relation$STRORD le)
Proof
  rpt strip_tac
  >> `relation$WeakOrder le` by
       fs[relationTheory.WeakLinearOrder]
  >> `relation$Order le` by
       metis_tac[relationTheory.WeakOrd_Ord]
  >> `relation$StrongOrder (relation$STRORD le)` by
       metis_tac[relationTheory.STRORD_Strong]
  >> fs[relationTheory.StrongOrder]
QED

Theorem source_strord_subset:
  !le (x : 'a) y. relation$STRORD le x y ==> le x y
Proof
  simp[relationTheory.STRORD]
QED

Theorem source_strict_sorted_iff:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !xs.
      (source_strict_sorted le xs <=>
       source_sorted le xs /\ ALL_DISTINCT xs)
Proof
  rpt strip_tac
  >> drule source_weak_linear_transitive
  >> strip_tac
  >> `relation$transitive (relation$STRORD le)`
       by metis_tac[source_strord_transitive]
  >> simp[source_sorted_bridge, source_strict_sorted_bridge]
  >> Induct_on `xs`
  >- simp[]
  >> rw[sortingTheory.SORTED_EQ, relationTheory.STRORD,
        boolTheory.FORALL_AND_THM]
  >> metis_tac[]
QED

Theorem source_strict_sorted_equal_unique:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !domain xs ys.
      source_strict_sorted le xs /\
      LIST_TO_SET xs = domain /\
      source_strict_sorted le ys /\
      LIST_TO_SET ys = domain ==>
      xs = ys
Proof
  metis_tac[source_strict_sorted_iff, source_sorted_bridge,
            source_weak_linear_transitive,
            source_weak_linear_antisymmetric,
            sortingTheory.SORTED_ALL_DISTINCT_LIST_TO_SET_EQ]
QED

Theorem source_sorted_all_distinct_unique:
  !le : 'a -> 'a -> bool.
    relation$transitive le ==>
    relation$antisymmetric le ==>
    !xs ys.
      source_sorted le xs ==>
      ALL_DISTINCT xs ==>
      source_sorted le ys ==>
      ALL_DISTINCT ys ==>
      LIST_TO_SET xs = LIST_TO_SET ys ==>
      xs = ys
Proof
  metis_tac[source_sorted_bridge,
            sortingTheory.SORTED_ALL_DISTINCT_LIST_TO_SET_EQ]
QED

Theorem source_sorted_all_distinct_unique_exists:
  !xs ys.
    (?le : 'a -> 'a -> bool.
       relation$transitive le /\
       relation$antisymmetric le /\
       source_sorted le xs /\
       ALL_DISTINCT xs /\
       source_sorted le ys /\
       ALL_DISTINCT ys) ==>
    LIST_TO_SET xs = LIST_TO_SET ys ==>
    xs = ys
Proof
  metis_tac[source_sorted_all_distinct_unique]
QED

(* Isabelle/HOL src/HOL/List.thy:6222-6400.  The source insertion
   sort is parameterized here by its weak linear order. *)
Definition source_insort_key_def:
  (source_insort_key le function value [] = [value]) /\
  (source_insort_key le function value (head::tail) =
     if le (function value) (function head) then
       value::head::tail
     else
       head::source_insort_key le function value tail)
End

Definition source_insort_def:
  source_insort le value xs =
    source_insort_key le I value xs
End

Definition source_sort_key_def:
  (source_sort_key le function [] = []) /\
  (source_sort_key le function (head::tail) =
     source_insort_key le function head
       (source_sort_key le function tail))
End

Definition source_sort_def:
  source_sort le xs = source_sort_key le I xs
End

Definition source_insort_insert_key_def:
  source_insort_insert_key le function value xs =
    if function value IN IMAGE function (LIST_TO_SET xs) then xs
    else source_insort_key le function value xs
End

Definition source_insort_insert_def:
  source_insort_insert le value xs =
    source_insort_insert_key le I value xs
End

Theorem source_set_insort_key:
  !le function value xs.
    LIST_TO_SET (source_insort_key le function value xs) =
    value INSERT LIST_TO_SET xs
Proof
  rpt gen_tac
  >> Induct_on `xs`
  >> simp[source_insort_key_def]
  >> gen_tac
  >> IF_CASES_TAC
  >> simp[pred_setTheory.EXTENSION]
  >> metis_tac[]
QED

Theorem source_map_insort_key:
  !le function value xs.
    MAP function (source_insort_key le function value xs) =
    source_insort le (function value) (MAP function xs)
Proof
  rpt gen_tac
  >> Induct_on `xs`
  >> simp[source_insort_def, source_insort_key_def,
          combinTheory.I_THM]
  >> Cases_on `le (function value) (function h)`
  >> simp[source_insort_def, source_insort_key_def,
          combinTheory.I_THM]
QED

Theorem source_set_insort:
  !le value xs.
    LIST_TO_SET (source_insort le value xs) =
    value INSERT LIST_TO_SET xs
Proof
  simp[source_insort_def, source_set_insort_key]
QED

Theorem source_sorted_insort_identity:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !value xs.
      (source_sorted le
         (source_insort_key le I value xs) <=>
       source_sorted le xs)
Proof
  gen_tac
  >> strip_tac
  >> drule source_weak_linear_transitive
  >> strip_tac
  >> gen_tac
  >> Induct_on `xs`
  >- simp[source_sorted_def, source_sorted_wrt_def,
          source_insort_key_def]
  >> rw[source_insort_key_def]
  >> fs[source_sorted_bridge, sortingTheory.SORTED_EQ,
        source_set_insort_key, combinTheory.I_THM,
        relationTheory.WeakLinearOrder_dichotomy,
        relationTheory.WeakOrder]
  >> rfs[source_sorted_bridge]
  >> metis_tac[]
QED

Theorem source_sorted_insort:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !value xs.
      (source_sorted le (source_insort le value xs) <=>
       source_sorted le xs)
Proof
  simp[source_insort_def, source_sorted_insort_identity]
QED

Theorem source_sorted_insort_key:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !function value xs.
      (source_sorted le
         (MAP function
           (source_insort_key le function value xs)) <=>
       source_sorted le (MAP function xs))
Proof
  simp[source_map_insort_key, source_sorted_insort]
QED

Theorem source_sorted_sort_key:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !function xs.
      source_sorted le (MAP function
        (source_sort_key le function xs))
Proof
  rpt strip_tac
  >> drule source_weak_linear_transitive
  >> strip_tac
  >> Induct_on `xs`
  >- simp[source_sort_key_def, source_sorted_bridge]
  >> simp[source_sort_key_def, source_sorted_insort_key]
QED

Theorem source_sorted_sort_key_identity:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !xs. source_sorted le (source_sort_key le I xs)
Proof
  rpt strip_tac
  >> `source_sorted le (MAP I (source_sort_key le I xs))` by
       metis_tac[source_sorted_sort_key]
  >> fs[]
QED

Theorem source_sorted_sort:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !xs. source_sorted le (source_sort le xs)
Proof
  gen_tac
  >> strip_tac
  >> gen_tac
  >> simp[source_sort_def]
  >> drule source_sorted_sort_key
  >> strip_tac
  >> first_x_assum (qspecl_then [`I`, `xs`] mp_tac)
  >> simp[]
QED

Theorem source_insort_key_is_cons:
  !le function value xs.
    (!item.
       MEM item xs ==>
       le (function value) (function item)) ==>
    source_insort_key le function value xs = value::xs
Proof
  rpt gen_tac
  >> Cases_on `xs`
  >> simp[source_insort_key_def]
QED

Theorem source_sort_key_id_if_sorted:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !function xs.
      source_sorted le (MAP function xs) ==>
      source_sort_key le function xs = xs
Proof
  gen_tac
  >> strip_tac
  >> gen_tac
  >> Induct_on `xs`
  >- simp[source_sort_key_def]
  >> rpt strip_tac
  >> `source_sorted le (MAP function xs)` by
       fs[source_sorted_def, source_sorted_wrt_def]
  >> `source_sort_key le function xs = xs` by metis_tac[]
  >> `!mapped.
        MEM mapped (MAP function xs) ==>
        le (function h) mapped` by
       fs[source_sorted_def, source_sorted_wrt_def]
  >> simp[source_sort_key_def]
  >> irule source_insort_key_is_cons
  >> rpt strip_tac
  >> qpat_x_assum
       `!mapped.
          MEM mapped (MAP function xs) ==>
          le (function h) mapped`
       (qspec_then `function item` mp_tac)
  >> disch_then match_mp_tac
  >> simp[listTheory.MEM_MAP]
  >> qexists_tac `item`
  >> simp[]
QED

Theorem source_sorted_sort_id:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !xs.
      source_sorted le xs ==>
      source_sort le xs = xs
Proof
  simp[source_sort_def]
  >> metis_tac[source_sort_key_id_if_sorted,
               listTheory.MAP_ID]
QED

Theorem source_sorted_replicate:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !n value.
      source_sorted le (REPLICATE n value)
Proof
  gen_tac
  >> strip_tac
  >> drule source_sorted_same
  >> strip_tac
  >> rpt gen_tac
  >> `FILTER (\item. item = value) (REPLICATE n value) =
      REPLICATE n value` by
       (Induct_on `n` >> simp[])
  >> first_x_assum
       (qspecl_then [`value`, `REPLICATE n value`] mp_tac)
  >> simp[]
QED

Theorem source_sort_replicate:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !count value.
      source_sort le (REPLICATE count value) =
      REPLICATE count value
Proof
  metis_tac[source_sorted_sort_id,
            source_sorted_replicate]
QED

Theorem source_insort_insert_key_triv:
  !le function value xs.
    function value IN IMAGE function (LIST_TO_SET xs) ==>
    source_insort_insert_key le function value xs = xs
Proof
  simp[source_insort_insert_key_def]
  >> metis_tac[]
QED

Theorem source_insort_insert_triv:
  !le value xs.
    value IN LIST_TO_SET xs ==>
    source_insort_insert le value xs = xs
Proof
  simp[source_insort_insert_def,
       source_insort_insert_key_def]
QED

Theorem source_insort_insert_insort_key:
  !le function value xs.
    function value NOTIN IMAGE function (LIST_TO_SET xs) ==>
    source_insort_insert_key le function value xs =
    source_insort_key le function value xs
Proof
  simp[source_insort_insert_key_def]
  >> metis_tac[]
QED

Theorem source_insort_insert_insort:
  !le value xs.
    value NOTIN LIST_TO_SET xs ==>
    source_insort_insert le value xs =
    source_insort le value xs
Proof
  simp[source_insort_insert_def,
       source_insort_insert_key_def,
       source_insort_def]
  >> metis_tac[]
QED

Theorem source_set_insort_insert:
  !le value xs.
    LIST_TO_SET (source_insort_insert le value xs) =
    value INSERT LIST_TO_SET xs
Proof
  rpt gen_tac
  >> Cases_on `value IN LIST_TO_SET xs`
  >> simp[source_insort_insert_def,
          source_insort_insert_key_def,
          source_set_insort_key,
          pred_setTheory.EXTENSION]
  >> metis_tac[]
QED

Theorem source_sorted_insort_insert_key:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !function value xs.
      source_sorted le (MAP function xs) ==>
      source_sorted le
        (MAP function
          (source_insort_insert_key le function value xs))
Proof
  simp[source_insort_insert_key_def]
  >> metis_tac[source_sorted_insort_key]
QED

Theorem source_sorted_insort_insert:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !value xs.
      source_sorted le xs ==>
      source_sorted le (source_insort_insert le value xs)
Proof
  simp[source_insort_insert_def,
       source_insort_insert_key_def,
       source_insort_def]
  >> metis_tac[source_sorted_insort_identity]
QED

Definition source_stable_sort_key_def:
  source_stable_sort_key le sorter <=>
    !function xs key.
      FILTER (\value. function value = key)
        (sorter le function xs) =
      FILTER (\value. function value = key) xs
End

Theorem source_filter_insort_key:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !function value xs key.
      FILTER (\item. function item = key)
        (source_insort_key le function value xs) =
      if function value = key then
        value::FILTER (\item. function item = key) xs
      else
        FILTER (\item. function item = key) xs
Proof
  gen_tac
  >> strip_tac
  >> gen_tac
  >> gen_tac
  >> Induct_on `xs`
  >- simp[source_insort_key_def]
  >> rpt gen_tac
  >> rw[source_insort_key_def]
  >> Cases_on `function value = key`
  >> Cases_on `function h = key`
  >> fs[]
  >> metis_tac[source_weak_linear_refl]
QED

Theorem source_sort_key_stable:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !function xs key.
      FILTER (\value. function value = key)
        (source_sort_key le function xs) =
      FILTER (\value. function value = key) xs
Proof
  gen_tac
  >> strip_tac
  >> gen_tac
  >> Induct_on `xs`
  >- simp[source_sort_key_def]
  >> gen_tac
  >> simp[source_sort_key_def, source_filter_insort_key]
QED

Theorem source_stable_sort_key_sort_key:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    source_stable_sort_key le source_sort_key
Proof
  simp[source_stable_sort_key_def, source_sort_key_stable]
QED

Definition source_transpose_def:
  source_transpose rows =
    GENLIST
      (\index.
         MAP (\row. EL index row)
           (FILTER (\row. index < LENGTH row) rows))
      (rich_list$MAX_LIST (MAP LENGTH rows))
End

Theorem source_sorted_reverse_filter_lengths:
  !items : 'a list. !bound predicate.
    (!left right item.
       left < right ==>
       predicate right item ==>
       predicate left item) ==>
    sorting$SORTED ($<=)
      (REVERSE
        (GENLIST
          (\index. LENGTH (FILTER (predicate index) items)) bound))
Proof
  simp[sortingTheory.SORTED_EL_LESS,
       relationTheory.transitive_def]
  >> rpt strip_tac
  >> simp[listTheory.EL_REVERSE, listTheory.EL_GENLIST]
  >> irule listTheory.LENGTH_FILTER_LEQ_MONO
  >> simp[]
  >> rpt strip_tac
  >> qsuff_tac
       `PRE (bound - n) < PRE (bound - m)`
  >- metis_tac[]
  >> decide_tac
QED

Theorem source_length_threshold_antitone:
  !left right (items : 'a list).
    left < right ==>
    right < LENGTH items ==>
    left < LENGTH items
Proof
  rpt strip_tac
  >> decide_tac
QED

Theorem source_sorted_reverse_length_thresholds:
  !v_rows0 : 'a list list. !v_bound0.
    sorting$SORTED ($<=)
      (REVERSE
        (GENLIST
          (\v_index0.
             LENGTH
               (FILTER
                 (\v_row0. v_index0 < LENGTH v_row0) v_rows0))
          v_bound0))
Proof
  rpt gen_tac
  >> match_mp_tac
       (BETA_RULE
         (Q.ISPEC
           `\v_index0 v_row0. v_index0 < LENGTH v_row0`
           (Q.SPECL [`v_rows0`, `v_bound0`]
              source_sorted_reverse_filter_lengths)))
  >> rpt strip_tac
  >> decide_tac
QED

Theorem source_sorted_transpose:
  !rows : 'a list list.
    source_sorted ($<=)
      (REVERSE (MAP LENGTH (source_transpose rows)))
Proof
  gen_tac
  >> simp[source_sorted_bridge, sortingTheory.SORTED_EL_LESS,
          relationTheory.transitive_def]
  >> rpt strip_tac
  >> simp[source_transpose_def, listTheory.MAP_GENLIST,
          listTheory.EL_REVERSE]
  >> fs[source_transpose_def]
  >> simp[listTheory.EL_REVERSE]
  >> irule listTheory.LENGTH_FILTER_LEQ_MONO
  >> simp[]
  >> decide_tac
QED

Theorem source_sorted_reverse_lengths_mono:
  !rows : 'a list list.
    source_sorted ($<=) (REVERSE (MAP LENGTH rows)) ==>
    !left right.
      left < right ==>
      right < LENGTH rows ==>
      LENGTH (EL right rows) <= LENGTH (EL left rows)
Proof
  rpt strip_tac
  >> fs[source_sorted_bridge,
        sortingTheory.SORTED_EL_LESS,
        relationTheory.transitive_def]
  >> first_x_assum
       (qspecl_then
          [`PRE (LENGTH rows - right)`,
           `PRE (LENGTH rows - left)`]
          mp_tac)
  >> simp[listTheory.EL_REVERSE]
  >> `PRE (LENGTH rows - PRE (LENGTH rows - right)) = right` by
       decide_tac
  >> `PRE (LENGTH rows - PRE (LENGTH rows - left)) = left` by
       decide_tac
  >> simp[listTheory.EL_MAP]
  >> qsuff_tac
       `PRE (LENGTH rows - right) < PRE (LENGTH rows - left)`
  >- simp[]
  >> decide_tac
QED

Theorem source_el_filter_prefix:
  !predicate (xs : 'a list) index.
    (!left right.
       left < right ==>
       right < LENGTH xs ==>
       predicate (EL right xs) ==>
       predicate (EL left xs)) ==>
    index < LENGTH (FILTER predicate xs) ==>
    EL index (FILTER predicate xs) = EL index xs
Proof
  gen_tac
  >> Induct_on `xs`
  >- simp[]
  >> gen_tac
  >> rpt strip_tac
  >> Cases_on `predicate h`
  >- (Cases_on `index`
      >- simp[]
      >> simp[]
      >> first_x_assum irule
      >> rpt strip_tac
      >> first_x_assum
           (qspecl_then [`SUC left`, `SUC right`] mp_tac)
      >> simp[]
      >> strip_tac
      >> fs[])
  >> `FILTER predicate xs = []` by
       (simp[listTheory.FILTER_EQ_NIL,
             listTheory.EVERY_MEM]
        >> rpt strip_tac
        >> `?offset. offset < LENGTH xs /\ EL offset xs = x` by
             metis_tac[listTheory.MEM_EL]
        >> first_x_assum
             (qspecl_then [`0`, `SUC offset`] mp_tac)
        >> simp[])
  >> fs[]
QED

Theorem source_transpose_lookup_length_mono:
  !rows : 'a list list.
    (!left right.
       left < right ==>
       right < LENGTH rows ==>
       LENGTH (EL right rows) <= LENGTH (EL left rows)) ==>
    !column row.
      column < LENGTH (source_transpose rows) ==>
      row < LENGTH
        (FILTER (\items. column < LENGTH items) rows) ==>
      EL row (EL column (source_transpose rows)) =
      EL column (EL row rows)
Proof
  rpt strip_tac
  >> simp[source_transpose_def]
  >> fs[source_transpose_def]
  >> simp[listTheory.EL_GENLIST, listTheory.EL_MAP]
  >> qsuff_tac
       `EL row
          (FILTER (\items. column < LENGTH items) rows) =
        EL row rows`
  >- simp[]
  >> irule source_el_filter_prefix
  >> conj_tac
  >- (rpt strip_tac
      >> qpat_x_assum `!left right. _`
           (qspecl_then [`left`, `right`] mp_tac)
      >> fs[])
  >> simp[]
QED

Theorem source_nth_transpose:
  !rows : 'a list list.
    !index.
      index < LENGTH (source_transpose rows) ==>
      EL index (source_transpose rows) =
      MAP (\row. EL index row) (FILTER (\row. index < LENGTH row) rows)
Proof
  rw[source_transpose_def]
QED

Theorem source_nth_nth_transpose_sorted:
  !rows : 'a list list.
    source_sorted ($<=) (REVERSE (MAP LENGTH rows)) ==>
    !column row.
      column < LENGTH (source_transpose rows) ==>
      row < LENGTH
        (FILTER (\items. column < LENGTH items) rows) ==>
      EL row (EL column (source_transpose rows)) =
      EL column (EL row rows)
Proof
  rpt strip_tac
  >> simp[source_transpose_def]
  >> fs[source_transpose_def]
  >> simp[listTheory.EL_GENLIST, listTheory.EL_MAP]
  >> qsuff_tac
       `EL row
          (FILTER (\items. column < LENGTH items) rows) =
        EL row rows`
  >- simp[]
  >> irule source_el_filter_prefix
  >> conj_tac
  >- (rpt strip_tac
      >> drule source_sorted_reverse_lengths_mono
      >> strip_tac
      >> fs[]
      >> first_x_assum
           (qspecl_then [`left`, `right`] mp_tac)
      >> decide_tac)
  >> simp[]
QED

Theorem source_length_insort_key:
  !le function value xs.
    LENGTH (source_insort_key le function value xs) =
    SUC (LENGTH xs)
Proof
  rpt gen_tac
  >> Induct_on `xs`
  >> simp[source_insort_key_def]
  >> Cases_on `le (function value) (function h)`
  >> simp[]
QED

Theorem source_set_sort_key:
  !le function xs.
    LIST_TO_SET (source_sort_key le function xs) =
    LIST_TO_SET xs
Proof
  rpt gen_tac
  >> Induct_on `xs`
  >> simp[source_sort_key_def, source_set_insort_key]
QED

Theorem source_length_sort_key:
  !le function xs.
    LENGTH (source_sort_key le function xs) = LENGTH xs
Proof
  rpt gen_tac
  >> Induct_on `xs`
  >> simp[source_sort_key_def, source_length_insort_key]
QED

Theorem source_all_distinct_insort_key:
  !le function value xs.
    (ALL_DISTINCT (source_insort_key le function value xs) <=>
     value NOTIN LIST_TO_SET xs /\ ALL_DISTINCT xs)
Proof
  rpt gen_tac
  >> Induct_on `xs`
  >- simp[source_insort_key_def]
  >> rw[source_insort_key_def]
  >> simp[source_set_insort_key]
  >> metis_tac[]
QED

Theorem source_all_distinct_sort_key:
  !le function xs.
    (ALL_DISTINCT (source_sort_key le function xs) <=>
     ALL_DISTINCT xs)
Proof
  rpt gen_tac
  >> Induct_on `xs`
  >> simp[source_sort_key_def,
          source_all_distinct_insort_key,
          source_set_sort_key]
QED

Theorem source_insort_key_not_nil:
  !le function value xs.
    source_insort_key le function value xs <> []
Proof
  rpt gen_tac
  >> Cases_on `xs`
  >- simp[source_insort_key_def]
  >> (simp[source_insort_key_def]
      THEN IF_CASES_TAC
      THEN simp[])
QED

Theorem source_sort_key_eq_nil:
  !le function xs.
    (source_sort_key le function xs = [] <=> xs = [])
Proof
  rpt gen_tac
  >> Cases_on `xs`
  >> simp[source_sort_key_def, source_insort_key_not_nil]
QED

Definition source_sorted_key_list_of_set_def:
  source_sorted_key_list_of_set le function domain =
    source_sort_key le function (SET_TO_LIST domain)
End

Definition source_sorted_list_of_set_def:
  source_sorted_list_of_set le domain =
    source_sort le (SET_TO_LIST domain)
End

Theorem source_set_sorted_key_list_of_set:
  !le function domain.
    FINITE domain ==>
    LIST_TO_SET
      (source_sorted_key_list_of_set le function domain) = domain
Proof
  simp[source_sorted_key_list_of_set_def,
       source_set_sort_key, listTheory.SET_TO_LIST_INV]
QED

Theorem source_length_sorted_key_list_of_set:
  !le function domain.
    FINITE domain ==>
    LENGTH (source_sorted_key_list_of_set le function domain) =
    CARD domain
Proof
  simp[source_sorted_key_list_of_set_def,
       source_length_sort_key, listTheory.SET_TO_LIST_CARD]
QED

Theorem source_all_distinct_sorted_key_list_of_set:
  !le function domain.
    FINITE domain ==>
    ALL_DISTINCT
      (source_sorted_key_list_of_set le function domain)
Proof
  simp[source_sorted_key_list_of_set_def,
       source_all_distinct_sort_key,
       listTheory.ALL_DISTINCT_SET_TO_LIST]
QED

Theorem source_sorted_sorted_key_list_of_set:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !function domain.
      source_sorted le
        (MAP function
          (source_sorted_key_list_of_set le function domain))
Proof
  simp[source_sorted_key_list_of_set_def,
       source_sorted_sort_key]
QED

Theorem source_set_sorted_list_of_set:
  !le domain.
    FINITE domain ==>
    LIST_TO_SET (source_sorted_list_of_set le domain) = domain
Proof
  simp[source_sorted_list_of_set_def, source_sort_def,
       source_set_sort_key, listTheory.SET_TO_LIST_INV]
QED

Theorem source_length_sorted_list_of_set:
  !le domain.
    FINITE domain ==>
    LENGTH (source_sorted_list_of_set le domain) = CARD domain
Proof
  simp[source_sorted_list_of_set_def, source_sort_def,
       source_length_sort_key, listTheory.SET_TO_LIST_CARD]
QED

Theorem source_all_distinct_sorted_list_of_set:
  !le domain.
    FINITE domain ==>
    ALL_DISTINCT (source_sorted_list_of_set le domain)
Proof
  simp[source_sorted_list_of_set_def, source_sort_def,
       source_all_distinct_sort_key,
       listTheory.ALL_DISTINCT_SET_TO_LIST]
QED

Theorem source_sorted_sorted_list_of_set:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !domain. source_sorted le (source_sorted_list_of_set le domain)
Proof
  simp[source_sorted_list_of_set_def, source_sorted_sort]
QED

Theorem source_sorted_list_of_set_unique:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !domain target.
      FINITE domain ==>
      source_sorted le target ==>
      ALL_DISTINCT target ==>
      LIST_TO_SET target = domain ==>
      source_sorted_list_of_set le domain = target
Proof
  metis_tac[source_sorted_bridge,
            source_weak_linear_transitive,
            source_weak_linear_antisymmetric,
            source_sorted_sorted_list_of_set,
            source_all_distinct_sorted_list_of_set,
            source_set_sorted_list_of_set,
            sortingTheory.SORTED_ALL_DISTINCT_LIST_TO_SET_EQ]
QED

Theorem source_sorted_key_list_of_set_eq_nil:
  !le function domain.
    FINITE domain ==>
    (source_sorted_key_list_of_set le function domain = [] <=>
     domain = EMPTY)
Proof
  simp[source_sorted_key_list_of_set_def,
       source_sort_key_eq_nil,
       listTheory.SET_TO_LIST_EMPTY_IFF]
QED

Definition source_minimum_def:
  source_minimum le domain =
    HD (source_sorted_list_of_set le domain)
End

Theorem source_sorted_list_of_set_nonempty:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !items.
      FINITE items ==>
      items <> EMPTY ==>
      source_sorted_list_of_set le items =
      source_minimum le items ::
        source_sorted_list_of_set le
          (items DELETE source_minimum le items)
Proof
  rpt strip_tac
  >> drule source_weak_linear_transitive
  >> strip_tac
  >> qabbrev_tac `xs = source_sorted_list_of_set le items`
  >> Cases_on `xs`
  >- metis_tac[source_sorted_key_list_of_set_eq_nil,
                source_sorted_list_of_set_def,
                source_sort_def,
                source_sorted_key_list_of_set_def]
  >> `source_minimum le items = h` by
       simp[source_minimum_def]
  >> simp[]
  >> qsuff_tac
       `source_sorted_list_of_set le (items DELETE h) = t`
  >- simp[]
  >> irule source_sorted_list_of_set_unique
  >> fs[source_sorted_bridge]
  >> `ALL_DISTINCT (h::t)` by
       metis_tac[source_all_distinct_sorted_list_of_set]
  >> `LIST_TO_SET (h::t) = items` by
       metis_tac[source_set_sorted_list_of_set]
  >> `source_sorted le (h::t)` by
       metis_tac[source_sorted_sorted_list_of_set]
  >> fs[source_sorted_def, source_sorted_wrt_def]
  >> rw[]
  >- (rw[pred_setTheory.EXTENSION] >> metis_tac[])
  >> metis_tac[source_sorted_wrt_bridge]
QED

Theorem source_sorted_list_of_set_head_tail:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !items.
      FINITE items ==>
      items <> EMPTY ==>
      source_sorted_list_of_set le items <> [] /\
      HD (source_sorted_list_of_set le items) =
        source_minimum le items /\
      TL (source_sorted_list_of_set le items) =
        source_sorted_list_of_set le
          (items DELETE source_minimum le items)
Proof
  gen_tac
  >> disch_tac
  >> gen_tac
  >> rpt disch_tac
  >> `source_sorted_list_of_set le items =
      source_minimum le items ::
        source_sorted_list_of_set le
          (items DELETE source_minimum le items)` by
       metis_tac[source_sorted_list_of_set_nonempty]
  >> asm_rewrite_tac[]
  >> simp[]
QED

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/List.thy:3581-3700.  Isabelle's internal numeral type
   denotes positive numerals; SUC is its total HOL4 representation.
   The inclusive integer interval is kept benchmark-local. *)
Definition source_numeral_def:
  source_numeral n = SUC n
End

Theorem source_numeral_bridge:
  !m. 0 < m <=> ?n. m = source_numeral n
Proof
  Cases
  >> simp[source_numeral_def]
QED

Definition source_upto_def:
  source_upto (i : int) j =
    if j < i then [] else i :: source_upto (i + 1) j
Termination
  WF_REL_TAC `measure (\(i,j). Num (j - i + 1))`
  >> simp[]
  >> intLib.ARITH_TAC
End

Theorem source_upto_empty:
  !i j. j < i ==> source_upto i j = []
Proof
  rpt strip_tac
  >> rw[Once source_upto_def]
  >> intLib.ARITH_TAC
QED

Theorem source_upto_single:
  !i. source_upto i i = [i]
Proof
  rw[Once source_upto_def]
  >> simp[source_upto_empty]
QED

Theorem source_upto_nil:
  !i j. source_upto i j = [] <=> j < i
Proof
  rw[Once source_upto_def]
QED

Theorem source_upto_rec1:
  !i j. i <= j ==>
    source_upto i j = i :: source_upto (i + 1) j
Proof
  rpt strip_tac
  >> rw[Once source_upto_def]
  >> intLib.ARITH_TAC
QED

Theorem source_upto_rec2:
  !i j. i <= j ==>
    source_upto i j = source_upto i (j - 1) ++ [j]
Proof
  ho_match_mp_tac source_upto_ind
  >> rw[Once source_upto_def]
  >- (`i = j` by intLib.ARITH_TAC
      >> `source_upto i (j - 1) = []` by
           (irule source_upto_empty >> intLib.ARITH_TAC)
      >> fs[source_upto_single])
  >> `i + 1 <= j` by intLib.ARITH_TAC
  >> `~(j < i)` by intLib.ARITH_TAC
  >> `source_upto i (j - 1) =
      i :: source_upto (i + 1) (j - 1)` by
       (irule source_upto_rec1 >> intLib.ARITH_TAC)
  >> rw[Once source_upto_rec1]
  >> fs[]
  >> rw[Once source_upto_rec1]
  >> fs[]
QED

Theorem source_num_step:
  !i j : int. i < j ==>
    Num (j - i) = SUC (Num (j - (i + 1)))
Proof
  rpt strip_tac
  >> `0 <= j - i` by intLib.ARITH_TAC
  >> `0 <= j - (i + 1)` by intLib.ARITH_TAC
  >> `&(Num (j - i)) = j - i` by
       simp[integerTheory.INT_OF_NUM]
  >> `&(Num (j - (i + 1))) = j - (i + 1)` by
       simp[integerTheory.INT_OF_NUM]
  >> intLib.ARITH_TAC
QED

Theorem source_int_genlist_cons:
  !i : int. !n.
    GENLIST (\k. i + &k) (SUC n) =
    i :: GENLIST (\k. i + 1 + &k) n
Proof
  rw[listTheory.GENLIST_CONS, combinTheory.o_DEF]
  >> rw[listTheory.GENLIST_FUN_EQ]
  >> intLib.ARITH_TAC
QED

Theorem source_int_lt_add1:
  !x y : int. x < y + 1 <=> x <= y
Proof
  intLib.ARITH_TAC
QED

Theorem source_int_le_antisym_imp:
  !x y : int. x <= y ==> y <= x ==> x = y
Proof
  intLib.ARITH_TAC
QED

Theorem source_int_le_cases:
  !x y : int. x <= y ==> x = y \/ x + 1 <= y
Proof
  intLib.ARITH_TAC
QED

Theorem source_upto_closed:
  !i j.
    source_upto i j =
    if j < i then []
    else GENLIST (\n. i + &n) (SUC (Num (j - i)))
Proof
  ho_match_mp_tac source_upto_ind
  >> rw[Once source_upto_def]
  >> TRY (qpat_x_assum `j < i` mp_tac
          >> simp[source_upto_empty])
  >> TRY (`i = j` by intLib.ARITH_TAC
          >> fs[source_upto_single, listTheory.GENLIST_CONS])
  >> `i < j` by intLib.ARITH_TAC
  >> `Num (j - i) = SUC (Num (j - (i + 1)))` by
       metis_tac[source_num_step]
  >> `i + 1 <= j` by intLib.ARITH_TAC
  >> fs[listTheory.GENLIST_CONS, combinTheory.o_DEF]
  >> `source_upto (i + 1) j =
      (i + 1) :: source_upto (i + 1 + 1) j` by
       metis_tac[source_upto_rec1]
  >> `source_upto i j = i :: source_upto (i + 1) j` by
       (irule source_upto_rec1 >> intLib.ARITH_TAC)
  >> fs[]
  >> rw[listTheory.GENLIST_FUN_EQ]
  >> intLib.ARITH_TAC
QED

Theorem source_upto_split1:
  !i j. !k. i <= j ==> j <= k ==>
    source_upto i k =
    source_upto i (j - 1) ++ source_upto j k
Proof
  ho_match_mp_tac source_upto_ind
  >> rw[]
  >> Cases_on `i = j`
  >- (`source_upto i (j - 1) = []` by
        (irule source_upto_empty >> intLib.ARITH_TAC)
      >> fs[])
  >> `i + 1 <= j` by intLib.ARITH_TAC
  >> `~(j < i)` by intLib.ARITH_TAC
  >> `source_upto i k = i :: source_upto (i + 1) k` by
       (irule source_upto_rec1 >> intLib.ARITH_TAC)
  >> `source_upto i (j - 1) =
      i :: source_upto (i + 1) (j - 1)` by
       (irule source_upto_rec1 >> intLib.ARITH_TAC)
  >> `source_upto (i + 1) k =
      source_upto (i + 1) (j - 1) ++ source_upto j k` by
       metis_tac[]
  >> metis_tac[listTheory.APPEND]
QED

(* An explicit name for the predecessor lets the classical rule matcher
   choose a split point before integer normalization discharges the side
   equation. *)
Theorem source_upto_split_boundary:
  !i left pivot k : int.
    i <= pivot ==> pivot <= k ==> left = pivot - 1 ==>
    source_upto i k =
    source_upto i left ++ source_upto pivot k
Proof
  metis_tac[source_upto_split1]
QED

(* src/HOL/List.thy:1036 @ f7e02b7e.  [append_eq_appendI] is the
   introduction a proof uses to build an equation between two appends
   out of a cut of one side: the source's [append_listrel1I] names it,
   as the rule that lets the search choose where the shared part ends.
   HOL4 states the associativity it rests on and nothing of this
   shape. *)
Theorem source_append_eq_appendI:
  !xs middle zs ys us.
    xs ++ middle = zs ==> ys = middle ++ us ==> xs ++ ys = zs ++ us
Proof
  metis_tac[listTheory.APPEND_ASSOC]
QED

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/List.thy:4241-4252 and 4314-4451. *)
Definition source_successively_def:
  source_successively relation xs =
    !left right. adjacent xs left right ==> relation left right
End

Definition source_distinct_adj_def:
  source_distinct_adj xs =
    source_successively (\left right. left <> right) xs
End

Definition source_inj_on_def:
  source_inj_on function set =
    !left right.
      left IN set ==> right IN set ==>
      function left = function right ==> left = right
End

Theorem source_inj_on_bridge:
  !function set.
    source_inj_on function set <=>
    !left right.
      left IN set ==> right IN set ==>
      function left = function right ==> left = right
Proof
  simp[source_inj_on_def]
QED

Theorem source_all_distinct_map_sorted_key_list_of_set:
  !le function source domain.
    source_inj_on function source ==>
    domain SUBSET source ==>
    FINITE domain ==>
    ALL_DISTINCT
      (MAP function
        (source_sorted_key_list_of_set le function domain))
Proof
  rpt strip_tac
  >> irule listTheory.ALL_DISTINCT_MAP_INJ
  >> conj_tac
  >- (rpt strip_tac
      >> fs[source_inj_on_def]
      >> first_x_assum irule
      >> fs[pred_setTheory.SUBSET_DEF]
      >> metis_tac[source_set_sorted_key_list_of_set])
  >> simp[source_all_distinct_sorted_key_list_of_set]
QED

Theorem source_map_sorted_distinct_set_unique:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !function xs ys.
      source_inj_on function
        (LIST_TO_SET xs UNION LIST_TO_SET ys) ==>
      source_sorted le (MAP function xs) ==>
      ALL_DISTINCT (MAP function xs) ==>
      source_sorted le (MAP function ys) ==>
      ALL_DISTINCT (MAP function ys) ==>
      LIST_TO_SET xs = LIST_TO_SET ys ==>
      xs = ys
Proof
  rpt strip_tac
  >> drule source_weak_linear_transitive
  >> strip_tac
  >> irule listTheory.INJ_MAP_EQ
  >> qexists_tac `function`
  >> conj_tac
  >- (irule sortingTheory.SORTED_ALL_DISTINCT_LIST_TO_SET_EQ
      >> simp[listTheory.LIST_TO_SET_MAP]
      >> qexists_tac `le`
      >> fs[source_sorted_bridge,
            source_weak_linear_transitive,
            source_weak_linear_antisymmetric])
  >> fs[pred_setTheory.INJ_DEF, source_inj_on_def]
QED

Theorem source_inj_on_union_subset:
  !function source left right.
    source_inj_on function source ==>
    left SUBSET source ==>
    right SUBSET source ==>
    source_inj_on function (left UNION right)
Proof
  simp[source_inj_on_def, pred_setTheory.SUBSET_DEF]
  >> metis_tac[]
QED

Theorem source_mapped_sorted_distinct_unique:
  !le : 'b -> 'b -> bool.
    relation$transitive le ==>
    relation$antisymmetric le ==>
    !function xs ys.
      source_inj_on function
        (LIST_TO_SET xs UNION LIST_TO_SET ys) ==>
      source_sorted le (MAP function xs) ==>
      ALL_DISTINCT (MAP function xs) ==>
      source_sorted le (MAP function ys) ==>
      ALL_DISTINCT (MAP function ys) ==>
      LIST_TO_SET xs = LIST_TO_SET ys ==>
      xs = ys
Proof
  rpt strip_tac
  >> qsuff_tac `MAP function xs = MAP function ys`
  >- (strip_tac
      >> irule listTheory.INJ_MAP_EQ
      >> qexists_tac `function`
      >> simp[]
      >> fs[pred_setTheory.INJ_DEF, source_inj_on_def])
  >> irule source_sorted_all_distinct_unique
  >> simp[listTheory.LIST_TO_SET_MAP]
  >> qexists_tac `le`
  >> simp[]
QED

Theorem source_mapped_sorted_distinct_unique_exists:
  !xs ys.
    (?le : 'b -> 'b -> bool. ?function.
       relation$transitive le /\
       relation$antisymmetric le /\
       source_inj_on function
         (LIST_TO_SET xs UNION LIST_TO_SET ys) /\
       source_sorted le (MAP function xs) /\
       ALL_DISTINCT (MAP function xs) /\
       source_sorted le (MAP function ys) /\
       ALL_DISTINCT (MAP function ys)) ==>
    LIST_TO_SET xs = LIST_TO_SET ys ==>
    xs = ys
Proof
  metis_tac[source_mapped_sorted_distinct_unique]
QED

Theorem source_distinct_map_index_injective:
  !function xs left right.
    ALL_DISTINCT (MAP function xs) ==>
    left < LENGTH xs ==>
    right < LENGTH xs ==>
    EL left xs = EL right xs ==>
    left = right
Proof
  metis_tac[listTheory.ALL_DISTINCT_MAP,
            listTheory.EL_ALL_DISTINCT_EL_EQ]
QED

Theorem source_distinct_map_index_injective_exists:
  !xs left right.
    (?function. ALL_DISTINCT (MAP function xs)) ==>
    left < LENGTH xs ==>
    right < LENGTH xs ==>
    EL left xs = EL right xs ==>
    left = right
Proof
  metis_tac[source_distinct_map_index_injective]
QED

Theorem source_inj_on_subset_exists:
  !function domain.
    (?source.
       source_inj_on function source /\
       domain SUBSET source) ==>
    source_inj_on function domain
Proof
  simp[source_inj_on_def, pred_setTheory.SUBSET_DEF]
  >> metis_tac[]
QED

Theorem source_sorted_key_list_of_set_eq:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !source function domain target.
      source_inj_on function source ==>
      domain SUBSET source ==>
      FINITE domain ==>
      source_sorted le (MAP function target) ==>
      ALL_DISTINCT (MAP function target) ==>
      LIST_TO_SET target = domain ==>
      source_sorted_key_list_of_set le function domain = target
Proof
  rpt strip_tac
  >> irule source_map_sorted_distinct_set_unique
  >> conj_tac
  >- metis_tac[source_set_sorted_key_list_of_set]
  >> qexists_tac `function`
  >> qexists_tac `le`
  >> metis_tac[source_inj_on_union_subset,
                source_all_distinct_map_sorted_key_list_of_set,
                source_sorted_sorted_key_list_of_set,
                source_set_sorted_key_list_of_set]
QED

Theorem source_sorted_key_list_of_set_unique:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !source function domain target.
      source_inj_on function source ==>
      domain SUBSET source ==>
      FINITE domain ==>
      (source_strict_sorted le (MAP function target) /\
       LIST_TO_SET target = domain /\
       LENGTH target = CARD domain <=>
       source_sorted_key_list_of_set le function domain = target)
Proof
  rpt strip_tac
  >> eq_tac
  >- (strip_tac
      >> metis_tac[source_strict_sorted_iff,
                    source_sorted_key_list_of_set_eq])
  >> strip_tac
  >> fs[]
  >> metis_tac[source_strict_sorted_iff,
                source_all_distinct_map_sorted_key_list_of_set,
                source_sorted_sorted_key_list_of_set,
                source_set_sorted_key_list_of_set,
                source_length_sorted_key_list_of_set]
QED

Theorem source_sorted_key_list_of_set_canonical:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !source function domain.
      source_inj_on function source ==>
      domain SUBSET source ==>
      FINITE domain ==>
      source_strict_sorted le
        (MAP function
          (source_sorted_key_list_of_set le function domain)) /\
      LIST_TO_SET
        (source_sorted_key_list_of_set le function domain) = domain /\
      LENGTH
        (source_sorted_key_list_of_set le function domain) = CARD domain
Proof
  rpt strip_tac
  >> simp[source_strict_sorted_iff]
  >> metis_tac[source_all_distinct_map_sorted_key_list_of_set,
                source_sorted_sorted_key_list_of_set,
                source_set_sorted_key_list_of_set,
                source_length_sorted_key_list_of_set]
QED

Theorem source_sorted_key_list_of_set_eq_on:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !function domain target.
      source_inj_on function domain ==>
      FINITE domain ==>
      source_sorted le (MAP function target) ==>
      ALL_DISTINCT (MAP function target) ==>
      LIST_TO_SET target = domain ==>
      source_sorted_key_list_of_set le function domain = target
Proof
  metis_tac[source_sorted_key_list_of_set_eq,
            pred_setTheory.SUBSET_REFL]
QED

Theorem source_sorted_key_list_of_set_canonical_on:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !function domain.
      source_inj_on function domain ==>
      FINITE domain ==>
      source_strict_sorted le
        (MAP function
          (source_sorted_key_list_of_set le function domain)) /\
      LIST_TO_SET
        (source_sorted_key_list_of_set le function domain) = domain /\
      LENGTH
        (source_sorted_key_list_of_set le function domain) = CARD domain
Proof
  metis_tac[source_sorted_key_list_of_set_canonical,
            pred_setTheory.SUBSET_REFL]
QED

Theorem source_sorted_key_list_of_set_unique_forward_on:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !function domain target.
      source_inj_on function domain ==>
      FINITE domain ==>
      source_strict_sorted le (MAP function target) ==>
      LIST_TO_SET target = domain ==>
      LENGTH target = CARD domain ==>
      source_sorted_key_list_of_set le function domain = target
Proof
  metis_tac[source_strict_sorted_iff,
            source_sorted_key_list_of_set_eq_on]
QED

Theorem source_sorted_key_list_of_set_unique_backward_on:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !function domain target.
      source_inj_on function domain ==>
      FINITE domain ==>
      source_sorted_key_list_of_set le function domain = target ==>
      source_strict_sorted le (MAP function target) /\
      LIST_TO_SET target = domain /\
      LENGTH target = CARD domain
Proof
  metis_tac[source_sorted_key_list_of_set_canonical_on]
QED

Theorem source_sorted_key_list_of_set_unique_on:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !function domain target.
      source_inj_on function domain ==>
      FINITE domain ==>
      (source_strict_sorted le (MAP function target) /\
       LIST_TO_SET target = domain /\
       LENGTH target = CARD domain <=>
       source_sorted_key_list_of_set le function domain = target)
Proof
  metis_tac[source_sorted_key_list_of_set_unique_forward_on,
            source_sorted_key_list_of_set_unique_backward_on]
QED

Theorem source_successively_bridge:
  !relation xs.
    source_successively relation xs <=>
    !left right. adjacent xs left right ==> relation left right
Proof
  simp[source_successively_def]
QED

Theorem source_successively_nil:
  !relation. source_successively relation []
Proof
  simp[source_successively_def]
QED

Theorem source_successively_singleton:
  !relation x. source_successively relation [x]
Proof
  simp[source_successively_def]
QED

Theorem source_successively_cons_cons:
  !relation x y xs.
    source_successively relation (x::y::xs) <=>
    relation x y /\ source_successively relation (y::xs)
Proof
  simp[source_successively_def, listTheory.adjacent_iff]
  >> metis_tac[]
QED

Theorem source_successively_conv_nth:
  !relation xs.
    source_successively relation xs <=>
    !i. i + 1 < LENGTH xs ==>
      relation (EL i xs) (EL (i + 1) xs)
Proof
  simp[source_successively_def, listTheory.adjacent_EL]
  >> metis_tac[]
QED

Theorem source_adjacent_append:
  !xs ys left right.
    adjacent (xs ++ ys) left right <=>
    adjacent xs left right \/ adjacent ys left right \/
    (xs <> [] /\ ys <> [] /\
     left = LAST xs /\ right = HD ys)
Proof
  Induct
  >- simp[]
  >> Cases_on `xs`
  >- (Cases_on `ys`
      >> simp[listTheory.adjacent_iff]
      >> metis_tac[])
  >> simp[listTheory.adjacent_iff]
  >> rpt gen_tac
  >> first_x_assum
       (qspecl_then [`ys`, `left`, `right`] mp_tac)
  >> simp[]
  >> metis_tac[]
QED

Theorem source_successively_append_iff:
  !relation xs ys.
    source_successively relation (xs ++ ys) <=>
    source_successively relation xs /\
    source_successively relation ys /\
    (xs = [] \/ ys = [] \/ relation (LAST xs) (HD ys))
Proof
  simp[source_successively_def, source_adjacent_append]
  >> metis_tac[]
QED

Theorem source_successively_map:
  !relation function xs.
    source_successively relation (MAP function xs) <=>
    !left right. adjacent xs left right ==>
      relation (function left) (function right)
Proof
  simp[source_successively_def, listTheory.adjacent_MAP]
  >> metis_tac[]
QED

Theorem source_distinct_adj_mapI:
  !function xs.
    source_distinct_adj xs ==>
    source_inj_on function (LIST_TO_SET xs) ==>
    source_distinct_adj (MAP function xs)
Proof
  simp[source_distinct_adj_def, source_successively_map,
       source_successively_def, source_inj_on_def]
  >> metis_tac[listTheory.adjacent_MEM]
QED

Theorem source_distinct_adj_mapD:
  !function xs.
    source_distinct_adj (MAP function xs) ==>
    source_distinct_adj xs
Proof
  simp[source_distinct_adj_def, source_successively_map,
       source_successively_def]
  >> metis_tac[]
QED

Theorem source_distinct_adj_conv_nth:
  !xs.
    source_distinct_adj xs <=>
    !i. i + 1 < LENGTH xs ==> EL i xs <> EL (i + 1) xs
Proof
  simp[source_distinct_adj_def, source_successively_conv_nth]
QED

Theorem source_distinct_adj_append_iff:
  !xs ys.
    source_distinct_adj (xs ++ ys) <=>
    source_distinct_adj xs /\ source_distinct_adj ys /\
    (xs = [] \/ ys = [] \/ LAST xs <> HD ys)
Proof
  simp[source_distinct_adj_def, source_successively_append_iff]
QED

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/List.thy:233-245 and 4654-4858. *)
Definition source_remove1_def:
  (source_remove1 value [] = []) /\
  (source_remove1 value (head::tail) =
     if value = head then tail
     else head::source_remove1 value tail)
End

Definition source_removeAll_def:
  (source_removeAll value [] = []) /\
  (source_removeAll value (head::tail) =
     if value = head then source_removeAll value tail
     else head::source_removeAll value tail)
End

Theorem source_removeAll_bridge:
  !value xs.
    source_removeAll value xs =
    rich_list$DELETE_ELEMENT value xs
Proof
  Induct_on `xs`
  >> simp[source_removeAll_def, rich_listTheory.DELETE_ELEMENT]
QED

Theorem source_remove1_mem:
  !removed xs value.
    MEM value (source_remove1 removed xs) ==>
    MEM value xs
Proof
  Induct_on `xs`
  >- simp[source_remove1_def]
  >> simp[source_remove1_def]
  >> rpt gen_tac
  >> Cases_on `removed = h`
  >> simp[]
  >> metis_tac[]
QED

Theorem source_sorted_map_remove1:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !function value xs.
      source_sorted le (MAP function xs) ==>
      source_sorted le (MAP function (source_remove1 value xs))
Proof
  rpt strip_tac
  >> drule source_weak_linear_transitive
  >> strip_tac
  >> drule source_weak_linear_transitive
  >> strip_tac
  >> ntac 2 (pop_assum mp_tac)
  >> qid_spec_tac `xs`
  >> Induct
  >- simp[source_remove1_def]
  >> rpt strip_tac
  >> rw[source_remove1_def]
  >> fs[source_sorted_bridge, sortingTheory.SORTED_EQ, listTheory.MEM_MAP]
  >> metis_tac[source_remove1_mem]
QED

Theorem source_removeAll_filter:
  !value xs.
    source_removeAll value xs = FILTER ((<>) value) xs
Proof
  simp[source_removeAll_bridge,
       rich_listTheory.DELETE_ELEMENT_FILTER]
QED

Theorem source_remove1_commute:
  !left right xs.
    source_remove1 left (source_remove1 right xs) =
    source_remove1 right (source_remove1 left xs)
Proof
  Induct_on `xs`
  >> rw[source_remove1_def]
  >> metis_tac[]
QED

Theorem source_removeAll_commute:
  !left right xs.
    source_removeAll left (source_removeAll right xs) =
    source_removeAll right (source_removeAll left xs)
Proof
  Induct_on `xs`
  >> rw[source_removeAll_def]
  >> metis_tac[]
QED

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/List.thy:113-115.  [foldr] is a primrec there, so what its
   simpset carries is the recursion, not an equation collapsing the
   constant into another combinator: a goal stated at [foldr] over a
   variable list stays at [foldr], which is what lets a cited
   [foldr_fold] reach it.  [source_foldr_FOLDR] is the characterisation
   the results below are proved through. *)
Definition source_foldr_def:
  source_foldr operation [] initial = initial /\
  source_foldr operation (value :: values) initial =
    operation value (source_foldr operation values initial)
End

Theorem source_foldr_FOLDR:
  !operation xs initial.
    source_foldr operation xs initial = FOLDR operation initial xs
Proof
  gen_tac >> Induct >> simp[source_foldr_def]
QED

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/List.thy:109-111.  [fold] is a primrec there, which is why
   [foldl_conv_fold] can be simp alongside it: the equation that
   rewrites a foldl into a fold meets a constant that unfolds down the
   list rather than back into a foldl.  Stating it by its own recursion
   keeps that, and [source_fold_FOLDL] is the characterisation the
   results below are proved through. *)
Definition source_fold_def:
  source_fold operation [] initial = initial /\
  source_fold operation (value :: values) initial =
    source_fold operation values (operation value initial)
End

Theorem source_fold_FOLDL:
  !operation xs initial.
    source_fold operation xs initial =
    FOLDL (\current element. operation element current) initial xs
Proof
  gen_tac >> Induct >> simp[source_fold_def]
QED

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/List.thy:3400-3438. *)
Theorem source_foldr_conv_fold:
  !operation xs initial.
    FOLDR operation initial xs =
    source_fold operation (REVERSE xs) initial
Proof
  simp[source_fold_FOLDL,
       rich_listTheory.FOLDR_FOLDL_REVERSE]
QED

Theorem source_foldl_conv_fold:
  !operation xs initial.
    FOLDL operation initial xs =
    source_fold
      (\value current. operation current value) xs initial
Proof
  rpt gen_tac
  >> rw[source_fold_FOLDL]
  >> `(\current value. operation current value) = operation` by
       simp[FUN_EQ_THM]
  >> simp[]
QED

Theorem source_fold_eta:
  !operation xs initial.
    source_fold
      (\value current. operation value current) xs initial =
    source_fold operation xs initial
Proof
  rpt gen_tac
  >> `(\value current. operation value current) = operation` by
       simp[FUN_EQ_THM]
  >> simp[]
QED

Theorem source_fold_append:
  !operation xs ys initial.
    source_fold operation (xs ++ ys) initial =
    source_fold operation ys (source_fold operation xs initial)
Proof
  simp[source_fold_FOLDL, rich_listTheory.FOLDL_APPEND]
QED

(* src/HOL/List.thy:3283-3287, fold_Cons_rev. *)
Theorem source_fold_Cons_rev:
  !xs initial.
    source_fold CONS xs initial = REVERSE xs ++ initial
Proof
  `(\element current. element::current) = CONS` by
    simp[FUN_EQ_THM]
  >> simp[source_fold_FOLDL,
          rich_listTheory.FOLDL_FOLDR_REVERSE,
          rich_listTheory.APPEND_FOLDR]
QED

Theorem source_fold_filter:
  !operation predicate xs initial.
    source_fold operation (FILTER predicate xs) initial =
    source_fold
      (\value current.
         if predicate value then operation value current else current)
      xs initial
Proof
  simp[source_fold_FOLDL, rich_listTheory.FOLDL_FILTER]
QED

Theorem source_fold_map_eta:
  !operation function xs initial.
    source_fold
      (\value current. operation (function value) current) xs initial =
    source_fold (\value. operation (function value)) xs initial
Proof
  rpt gen_tac
  >> `(\value current. operation (function value) current) =
      (\value. operation (function value))` by
       simp[FUN_EQ_THM]
  >> simp[]
QED

Theorem source_fold_filter_eta:
  !operation predicate xs initial.
    source_fold
      (\value current.
         if predicate value then operation value current else current)
      xs initial =
    source_fold
      (\value. if predicate value then operation value else I)
      xs initial
Proof
  rpt gen_tac
  >> `(\value current.
         if predicate value then operation value current else current) =
      (\value. if predicate value then operation value else I)` by
       (rw[FUN_EQ_THM]
        >> Cases_on `predicate value`
        >> simp[])
  >> simp[]
QED

Theorem source_fold_cong:
  !left right xs initial.
    (!current value.
       MEM value xs ==>
       left value current = right value current) ==>
    source_fold left xs initial = source_fold right xs initial
Proof
  rpt strip_tac
  >> rw[source_fold_FOLDL]
  >> irule listTheory.FOLDL_CONG
  >> simp[]
QED

Theorem source_fold_append_concat_rev:
  !xss.
    FLAT xss = source_fold APPEND (REVERSE xss) []
Proof
  Induct
  >- simp[source_fold_FOLDL]
  >> simp[source_fold_FOLDL, listTheory.REVERSE_DEF,
          rich_listTheory.FOLDL_APPEND]
QED

Definition source_INF_def:
  source_INF aggregate function domain =
    aggregate (IMAGE function domain)
End

Definition source_SUP_def:
  source_SUP aggregate function domain =
    aggregate (IMAGE function domain)
End

Theorem source_fold_map:
  !operation function xs initial.
    source_fold operation (MAP function xs) initial =
    source_fold
      (\value current. operation (function value) current)
      xs initial
Proof
  simp[source_fold_FOLDL, rich_listTheory.FOLDL_MAP]
QED

Theorem source_aggregate_image_set_fold:
  !aggregate operation initial function xs.
    (!ys.
       aggregate (LIST_TO_SET ys) =
       source_fold operation ys initial) ==>
    aggregate (IMAGE function (LIST_TO_SET xs)) =
    source_fold
      (\value current. operation (function value) current)
      xs initial
Proof
  rpt strip_tac
  >> first_x_assum (qspec_then `MAP function xs` mp_tac)
  >> simp[listTheory.LIST_TO_SET_MAP, source_fold_map]
QED

Theorem source_INF_set_fold:
  !aggregate operation top function xs.
    (!ys.
       aggregate (LIST_TO_SET ys) =
       source_fold operation ys top) ==>
    source_INF aggregate function (LIST_TO_SET xs) =
    source_fold
      (\value current. operation (function value) current)
      xs top
Proof
  rpt strip_tac
  >> first_x_assum (qspec_then `MAP function xs` mp_tac)
  >> simp[source_INF_def, listTheory.LIST_TO_SET_MAP,
          source_fold_map]
QED

Theorem source_SUP_set_fold:
  !aggregate operation bottom function xs.
    (!ys.
       aggregate (LIST_TO_SET ys) =
       source_fold operation ys bottom) ==>
    source_SUP aggregate function (LIST_TO_SET xs) =
    source_fold
      (\value current. operation (function value) current)
      xs bottom
Proof
  rpt strip_tac
  >> first_x_assum (qspec_then `MAP function xs` mp_tac)
  >> simp[source_SUP_def, listTheory.LIST_TO_SET_MAP,
          source_fold_map]
QED

Theorem source_fold_commute:
  !operation xs value.
    (!element current.
       MEM element xs ==>
       operation element (operation value current) =
       operation value (operation element current)) ==>
    !current.
      source_fold operation xs (operation value current) =
      operation value (source_fold operation xs current)
Proof
  gen_tac
  >> Induct
  >> rpt strip_tac
  >> fs[source_fold_FOLDL]
  >> `operation h (operation value current) =
      operation value (operation h current)`
       by (first_assum irule >> simp[])
  >> pop_assum SUBST1_TAC
  >> first_x_assum irule
  >> rpt strip_tac
  >> first_x_assum irule
  >> simp[]
QED

Theorem source_foldr_fold:
  !operation xs.
    (!left right.
       MEM left xs ==> MEM right xs ==>
       operation right o operation left =
       operation left o operation right) ==>
    source_foldr operation xs = source_fold operation xs
Proof
  gen_tac
  >> Induct
  >- simp[source_foldr_def, source_fold_FOLDL, FUN_EQ_THM]
  >> rpt strip_tac
  >> `!element current.
        MEM element xs ==>
        operation element (operation h current) =
        operation h (operation element current)`
       by (rpt strip_tac
           >> qpat_assum `!left right. MEM left (h::xs) ==> _`
                (qspecl_then [`h`, `element`] mp_tac)
           >> simp[FUN_EQ_THM]
           >> disch_then (qspec_then `current` ACCEPT_TAC))
  >> `!left right.
        MEM left xs ==> MEM right xs ==>
        operation right o operation left =
        operation left o operation right`
       by (rpt strip_tac
           >> qpat_assum `!left right. MEM left (h::xs) ==> _` irule
           >> simp[])
  >> fs[]
  >> rw[FUN_EQ_THM]
  >> `source_foldr operation (h::xs) x =
      operation h (source_foldr operation xs x)`
       by simp[source_foldr_def]
  >> `source_fold operation (h::xs) x =
      source_fold operation xs (operation h x)`
       by simp[source_fold_FOLDL]
  >> ASM_REWRITE_TAC []
  >> irule EQ_SYM
  >> irule source_fold_commute
  >> first_assum ACCEPT_TAC
QED

Definition source_minus_list_mset_def:
  source_minus_list_mset xs ys =
    source_foldr source_remove1 ys xs
End

Definition source_minus_list_set_def:
  source_minus_list_set xs ys =
    source_foldr source_removeAll ys xs
End

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/List.thy:226-231.  The source decomposes the list with
   dropWhile and takeWhile, and the results about extract are proved by
   rewriting with those two; a paraphrase in terms of any other
   decomposition -- SPLITP was the earlier one -- states the same
   function but leaves the source's own proofs without their rewrites. *)
Definition source_extract_def:
  source_extract predicate xs =
    case dropWhile ($~ o predicate) xs of
      [] => NONE
    | head::tail =>
        SOME (takeWhile ($~ o predicate) xs, head, tail)
End

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/List.thy:247-248 and 5125-5182. *)
Definition source_indexed_from_def:
  (source_indexed_from (start : num) [] = []) /\
  (source_indexed_from (start : num) (head::tail) =
     (start, head)::source_indexed_from (start + 1) tail)
End

Theorem source_indexed_from_bridge:
  !start xs.
    source_indexed_from start xs =
    ZIP (GENLIST (\offset. start + offset) (LENGTH xs), xs)
Proof
  Induct_on `xs`
  >> simp[source_indexed_from_def, listTheory.GENLIST_CONS,
          combinTheory.o_DEF]
  >> gen_tac
  >> AP_TERM_TAC
  >> simp[]
  >> rw[listTheory.GENLIST_FUN_EQ]
  >> decide_tac
QED

Theorem source_indexed_from_append_bridge:
  !start xs ys.
    source_indexed_from start (xs ++ ys) =
    source_indexed_from start xs ++
    source_indexed_from (start + LENGTH xs) ys
Proof
  Induct_on `xs`
  >- simp[source_indexed_from_def]
  >> rpt gen_tac
  >> simp_tac bool_ss
       [listTheory.APPEND, source_indexed_from_def, listTheory.LENGTH]
  >> asm_rewrite_tac[]
  >> ntac 2 AP_TERM_TAC
  >> AP_THM_TAC
  >> AP_TERM_TAC
  >> decide_tac
QED

Theorem source_num_genlist_append:
  !start left right.
    GENLIST (\offset. start + offset) (left + right) =
    GENLIST (\offset. start + offset) left ++
    GENLIST (\offset. start + left + offset) right
Proof
  rpt gen_tac
  >> SUBST1_TAC
       (SPECL [``left : num``, ``right : num``]
          arithmeticTheory.ADD_COMM)
  >> rw[listTheory.GENLIST_APPEND, listTheory.GENLIST_FUN_EQ]
QED

Theorem source_num_genlist_distinct:
  !start count.
    ALL_DISTINCT (GENLIST (\offset. start + offset) count)
Proof
  simp[listTheory.ALL_DISTINCT_GENLIST]
  >> decide_tac
QED

Theorem source_num_genlist_zip_distinct:
  !start xs.
    ALL_DISTINCT
      (ZIP (GENLIST (\offset. start + offset) (LENGTH xs), xs))
Proof
  rpt gen_tac
  >> irule listTheory.ALL_DISTINCT_ZIP
  >> simp[source_num_genlist_distinct]
QED

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/List.thy, [zip_append1] and [zip_append2].  Isabelle's [zip]
   truncates against the shorter list and so does HOL4's -- ZIP is
   specified by [ZIP ([], l) = []], [ZIP (l, []) = []] and the cons
   clause -- so the two lemmas translate as stated.  The equal-length
   [zip_append] they are cited to prove is the goal of
   [list_L2786_zip_append]; stating either of these as that one would
   hand the goal back to itself as a fact. *)
Theorem source_zip_append1:
  !xs ys zs.
    ZIP (xs ++ ys, zs) =
    ZIP (xs, TAKE (LENGTH xs) zs) ++ ZIP (ys, DROP (LENGTH xs) zs)
Proof
  Induct
  >> rpt gen_tac
  >> Cases_on `zs`
  >> simp[listTheory.ZIP_def]
QED

Theorem source_zip_append2:
  !ys xs zs.
    ZIP (xs, ys ++ zs) =
    ZIP (TAKE (LENGTH ys) xs, ys) ++ ZIP (DROP (LENGTH ys) xs, zs)
Proof
  Induct
  >> rpt gen_tac
  >> Cases_on `xs`
  >> simp[listTheory.ZIP_def]
QED

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/List.thy:2794-2804.  The following zip-map lemmas use this
   independently proved, more general result through a `using` fact. *)
(* Isabelle writes the image as the paired abstraction
   [%(x, y). (f x, g y)], which the translation spells UNCURRY, as
   [source_zip_map1] and [source_zip_map2] below already do.  Stated
   with FST and SND instead it is the same theorem in a spelling no
   translated goal arrives in. *)
Theorem source_zip_map_map:
  !xs ys f g.
    ZIP (MAP f xs, MAP g ys) =
    MAP (UNCURRY (\x y. (f x, g y))) (ZIP (xs, ys))
Proof
  Induct_on `xs`
  >- simp[listTheory.ZIP_def]
  >> Cases_on `ys`
  >> simp[listTheory.ZIP_def]
QED

Theorem source_zip_map1:
  !xs ys f.
    ZIP (MAP f xs, ys) =
    MAP (UNCURRY (\x y. (f x, y))) (ZIP (xs, ys))
Proof
  Induct_on `xs`
  >- simp[listTheory.ZIP_def]
  >> Cases_on `ys`
  >> simp[listTheory.ZIP_def]
QED

Theorem source_zip_map2:
  !xs ys f.
    ZIP (xs, MAP f ys) =
    MAP (UNCURRY (\x y. (x, f y))) (ZIP (xs, ys))
Proof
  Induct_on `xs`
  >- simp[listTheory.ZIP_def]
  >> Cases_on `ys`
  >> simp[listTheory.ZIP_def]
QED

Theorem source_zip_rev:
  !xs ys.
    LENGTH xs = LENGTH ys ==>
    ZIP (REVERSE xs, REVERSE ys) = REVERSE (ZIP (xs, ys))
Proof
  metis_tac[rich_listTheory.REVERSE_ZIP]
QED

Theorem source_el_zip_min:
  !xs ys index.
    index < MIN (LENGTH xs) (LENGTH ys) ==>
    EL index (ZIP (xs, ys)) = (EL index xs, EL index ys)
Proof
  Induct_on `xs`
  >- simp[]
  >> Cases_on `ys`
  >- simp[]
  >> Cases_on `index`
  >> simp[listTheory.ZIP_def]
QED

Theorem source_fst_el_zip_min:
  !xs ys index.
    index < LENGTH xs /\ index < LENGTH ys ==>
    FST (EL index (ZIP (xs, ys))) = EL index xs
Proof
  rpt strip_tac
  >> `index < MIN (LENGTH xs) (LENGTH ys)` by simp[]
  >> simp[source_el_zip_min]
QED

Theorem source_snd_el_zip_min:
  !xs ys index.
    index < LENGTH xs /\ index < LENGTH ys ==>
    SND (EL index (ZIP (xs, ys))) = EL index ys
Proof
  rpt strip_tac
  >> `index < MIN (LENGTH xs) (LENGTH ys)` by simp[]
  >> simp[source_el_zip_min]
QED

(* Isabelle/HOL src/HOL/List.thy:2789 [nth_zip], declared [simp]: the
   simpset takes an index through a zip with no method naming it.
   Stated with two bounds, as Isabelle states it -- HOL4's [EL_ZIP]
   asks instead for equal lengths, which the truncating ZIP does not
   need. *)
Theorem source_nth_zip:
  !xs ys index.
    index < LENGTH xs ==> index < LENGTH ys ==>
    EL index (ZIP (xs, ys)) = (EL index xs, EL index ys)
Proof
  rpt strip_tac
  >> `index < MIN (LENGTH xs) (LENGTH ys)` by simp[]
  >> simp[source_el_zip_min]
QED

(* Stated as membership rather than as the set applied to a point.
   Isabelle's [set_conv_nth] is a rewrite the source proofs hand to
   [auto]; a set-applied statement matches nothing in a goal that says
   [MEM], so the citation would be carried and never fire. *)
Theorem source_set_conv_nth:
  !xs value.
    MEM value xs <=>
    ?index. value = EL index xs /\ index < LENGTH xs
Proof
  ACCEPT_TAC
    (PURE_ONCE_REWRITE_RULE [boolTheory.CONJ_COMM] listTheory.MEM_EL)
QED

Theorem source_update_zip:
  !xs ys index pair.
    LUPDATE pair index (ZIP (xs, ys)) =
    ZIP (LUPDATE (FST pair) index xs,
         LUPDATE (SND pair) index ys)
Proof
  Induct_on `ys`
  >> Cases_on `xs`
  >> Cases_on `index`
  >> Cases_on `pair`
  >> simp[listTheory.ZIP_def, listTheory.LUPDATE_def]
QED

Theorem source_set_zip_leftD:
  !xs ys left right.
    (left, right) IN LIST_TO_SET (ZIP (xs, ys)) ==>
    left IN LIST_TO_SET xs
Proof
  simp[source_set_conv_nth]
  >> rpt gen_tac
  >> strip_tac
  >> qexists_tac `index`
  >> fs[]
  >> `EL index (ZIP (xs, ys)) =
      (EL index xs, EL index ys)` by
       (irule source_el_zip_min >> simp[])
  >> fs[]
QED

Theorem source_set_zip_rightD:
  !xs ys left right.
    (left, right) IN LIST_TO_SET (ZIP (xs, ys)) ==>
    right IN LIST_TO_SET ys
Proof
  simp[source_set_conv_nth]
  >> rpt gen_tac
  >> strip_tac
  >> qexists_tac `index`
  >> fs[]
  >> `EL index (ZIP (xs, ys)) =
      (EL index xs, EL index ys)` by
       (irule source_el_zip_min >> simp[])
  >> fs[]
QED

Theorem source_inj_on_nth:
  !xs indices.
    ALL_DISTINCT xs ==>
    (!index. index IN indices ==> index < LENGTH xs) ==>
    INJ (\index. EL index xs) indices UNIV
Proof
  simp[pred_setTheory.INJ_DEF]
  >> metis_tac[listTheory.ALL_DISTINCT_EL_IMP]
QED

Theorem source_nth_eq_iff_index_eq:
  !xs first second.
    ALL_DISTINCT xs ==>
    first < LENGTH xs ==>
    second < LENGTH xs ==>
    (EL first xs = EL second xs <=> first = second)
Proof
  metis_tac[listTheory.ALL_DISTINCT_EL_IMP]
QED

Theorem source_set_update_subset_insert:
  !xs index replacement value.
    value IN LIST_TO_SET (LUPDATE replacement index xs) ==>
    value = replacement \/ value IN LIST_TO_SET xs
Proof
  metis_tac[listTheory.MEM_LUPDATE_E]
QED

Theorem source_subsetD:
  !source target value.
    source SUBSET target ==>
    value IN source ==>
    value IN target
Proof
  simp[pred_setTheory.SUBSET_DEF]
QED

(* Removing an element keeps a list sorted.  Under the all-pairs
   reading this needs no order assumption, where the adjacent reading
   needed transitivity to re-relate the two neighbours of the gap. *)
Theorem source_sorted_wrt_remove1:
  !relation value xs : 'a list.
    source_sorted_wrt relation xs ==>
    source_sorted_wrt relation (source_remove1 value xs)
Proof
  ntac 2 gen_tac
  >> Induct
  >> rw[source_sorted_wrt_def, source_remove1_def]
  >> fs[source_sorted_wrt_def]
  >> metis_tac[source_remove1_mem]
QED

Theorem source_sorted_indexed_from:
  !start xs.
    source_sorted ($<=)
      (MAP FST (source_indexed_from start xs))
Proof
  rpt gen_tac
  >> rw[source_indexed_from_bridge]
  >> simp[source_sorted_bridge, listTheory.MAP_ZIP]
  >> irule sortingTheory.SORTED_weaken
  >> qexists_tac `$<`
  >> simp[]
  >> `(\offset. offset + start) = $+ start` by
       simp[FUN_EQ_THM, arithmeticTheory.ADD_COMM]
  >> simp[sortingTheory.SORTED_GENLIST_PLUS]
QED

(* Isabelle/HOL src/HOL/List.thy:6208-6212. *)
Definition source_num_upto_def:
  source_num_upto lower upper =
    if upper < lower then []
    else GENLIST ($+ lower) (SUC (upper - lower))
End

Theorem source_sorted_num_upto:
  !lower upper.
    source_sorted ($<=) (source_num_upto lower upper)
Proof
  rw[source_num_upto_def, source_sorted_bridge]
  >> irule sortingTheory.SORTED_weaken
  >> qexists_tac `$<`
  >> simp[sortingTheory.SORTED_GENLIST_PLUS]
QED

Theorem source_sorted_upt_weaken:
  !relation.
    (!left right : num. left < right ==> relation left right) ==>
    !start length.
      sorting$SORTED relation
        (GENLIST (\offset. start + offset) length)
Proof
  rpt strip_tac
  >> `sorting$SORTED ($<)
        (GENLIST (\offset. start + offset) length)` by
       (`(\offset. start + offset) = $+ start` by
          simp[FUN_EQ_THM]
        >> simp[sortingTheory.SORTED_GENLIST_PLUS])
  >> irule sortingTheory.SORTED_weaken
  >> qexists_tac `$<`
  >> simp[]
QED

Theorem source_sorted_upt:
  !start length.
    sorting$SORTED (\left right : num. left <= right)
      (GENLIST (\offset. start + offset) length)
Proof
  rpt gen_tac
  >> irule source_sorted_upt_weaken
  >> simp[]
QED

Theorem source_sorted_upt_section:
  !start length.
    sorting$SORTED ($<=) (GENLIST ($+ start) length)
Proof
  rpt gen_tac
  >> irule sortingTheory.SORTED_weaken
  >> qexists_tac `$<`
  >> simp[sortingTheory.SORTED_GENLIST_PLUS]
QED

Theorem source_sorted_upt_operator:
  !start length.
    sorting$SORTED ($<=)
      (GENLIST (\offset. start + offset) length)
Proof
  rpt gen_tac
  >> irule source_sorted_upt_weaken
  >> simp[]
QED

Theorem source_sorted_wrt_upt:
  !start length.
    source_sorted_wrt (\left right : num. left <= right)
      (GENLIST (\offset. start + offset) length)
Proof
  rpt gen_tac
  >> `relation$transitive
        (\left right : num. left <= right)` by
       simp[relationTheory.transitive_def]
  >> metis_tac[source_sorted_wrt_bridge, source_sorted_upt]
QED

(* Isabelle cites [sorted_wrt_mono_rel] with its second premise already
   discharged, by [sorted_wrt_upt] here and by [sorted_wrt_upto] below.
   An instance reached that way is its own citation, so it is stated as
   its own theorem rather than left to be recombined.  The interval is
   written [$+ start], the eta-contracted form the goals arrive in. *)
Theorem source_sorted_wrt_mono_rel_upt:
  !relation start length.
    (!left right.
       MEM left (GENLIST ($+ start) length) ==>
       MEM right (GENLIST ($+ start) length) ==>
       left < right ==> relation left right) ==>
    source_sorted_wrt relation (GENLIST ($+ start) length)
Proof
  rpt strip_tac
  >> irule source_sorted_wrt_mono_rel
  >> qexists_tac `$<`
  >> `relation$transitive ($< : num -> num -> bool)`
       by simp[relationTheory.transitive_def]
  >> simp[source_sorted_wrt_bridge, sortingTheory.SORTED_GENLIST_PLUS]
  >> metis_tac[]
QED

Theorem source_sorted_wrt_mono_rel_upto:
  !relation lower upper.
    (!left right.
       MEM left (source_num_upto lower upper) ==>
       MEM right (source_num_upto lower upper) ==>
       left < right ==> relation left right) ==>
    source_sorted_wrt relation (source_num_upto lower upper)
Proof
  rpt strip_tac
  >> irule source_sorted_wrt_mono_rel
  >> qexists_tac `$<`
  >> `relation$transitive ($< : num -> num -> bool)`
       by simp[relationTheory.transitive_def]
  >> simp[source_sorted_wrt_bridge, source_num_upto_def]
  >> rw[sortingTheory.SORTED_GENLIST_PLUS]
  >> metis_tac[]
QED

(* Isabelle/HOL src/HOL/List.thy:5185-5327. *)
Definition source_rotate1_def:
  (source_rotate1 ([] : 'a list) = []) /\
  (source_rotate1 (head::tail) = tail ++ [head])
End

Definition source_rotate_def:
  source_rotate count (xs : 'a list) =
    FUNPOW source_rotate1 count xs
End

(* Isabelle/HOL src/HOL/List.thy:5141 [rotate_add].  Stated on
   [source_rotate], as Isabelle states it: a method citing it reads a
   fact about rotation, not one about FUNPOW that only reaches the
   goal once the definition is unfolded. *)
Theorem source_rotate_add:
  !left right.
    source_rotate (left + right) =
    source_rotate left o source_rotate right
Proof
  simp[FUN_EQ_THM, source_rotate_def, arithmeticTheory.FUNPOW_ADD]
QED

Theorem source_rotate1_length:
  !xs. LENGTH (source_rotate1 xs) = LENGTH xs
Proof
  Cases
  >> simp[source_rotate1_def]
QED

Theorem source_rotate1_drop_take_bridge:
  !xs.
    source_rotate1 xs = DROP 1 xs ++ TAKE 1 xs
Proof
  Cases
  >> simp[source_rotate1_def]
QED

Theorem source_tail_snoc_el:
  !head tail index.
    index < LENGTH (head::tail) ==>
    EL index (tail ++ [head]) =
    EL (SUC index MOD LENGTH (head::tail)) (head::tail)
Proof
  rpt strip_tac
  >> Cases_on `index < LENGTH tail`
  >- simp[listTheory.EL_APPEND_EQN]
  >> fs[]
  >> `index = LENGTH tail` by decide_tac
  >> simp[listTheory.EL_APPEND_EQN]
QED

Theorem source_drop1_take1_el:
  !xs index.
    index < LENGTH xs ==>
    EL index (DROP 1 xs ++ TAKE 1 xs) =
    EL (SUC index MOD LENGTH xs) xs
Proof
  Cases_on `xs`
  >> simp[source_tail_snoc_el]
QED

Theorem source_rotate_length:
  !count xs. LENGTH (source_rotate count xs) = LENGTH xs
Proof
  Induct
  >- simp[source_rotate_def]
  >> gen_tac
  >> rw[source_rotate_def, arithmeticTheory.FUNPOW_SUC,
        source_rotate1_length]
  >> rw[GSYM source_rotate_def]
QED

Theorem source_rotate1_map:
  !function xs.
    source_rotate1 (MAP function xs) =
    MAP function (source_rotate1 xs)
Proof
  Cases_on `xs`
  >> simp[source_rotate1_def]
QED

Theorem source_funpow_rotate1_map:
  !count function xs.
    FUNPOW source_rotate1 count (MAP function xs) =
    MAP function (FUNPOW source_rotate1 count xs)
Proof
  Induct
  >> simp[arithmeticTheory.FUNPOW_SUC, source_rotate1_map]
QED

Theorem source_funpow_rotate1_swap:
  !count xs.
    source_rotate1 (FUNPOW source_rotate1 count xs) =
    FUNPOW source_rotate1 count (source_rotate1 xs)
Proof
  Induct
  >> simp[arithmeticTheory.FUNPOW_SUC]
QED

Theorem source_rotate_split_period:
  !left right.
    source_rotate (LENGTH left) (left ++ right) = right ++ left
Proof
  Induct
  >- simp[source_rotate_def]
  >> rpt gen_tac
  >> simp[source_rotate_def, arithmeticTheory.FUNPOW_SUC,
          source_funpow_rotate1_swap, source_rotate1_def]
  >> first_x_assum
       (qspec_then `right ++ [h]` mp_tac)
  >> simp[source_rotate_def, listTheory.APPEND_ASSOC]
QED

Theorem source_rotate_period:
  !xs. source_rotate (LENGTH xs) xs = xs
Proof
  gen_tac
  >> qspecl_then [`xs`, `[]`] mp_tac source_rotate_split_period
  >> simp[]
QED

Theorem source_funpow_mod_periodic:
  !v_iteration0 v_period0 v_value0 v_count0.
    FUNPOW v_iteration0 v_period0 v_value0 = v_value0 ==>
    FUNPOW v_iteration0 v_count0 v_value0 =
    FUNPOW v_iteration0 (v_count0 MOD v_period0) v_value0
Proof
  rpt strip_tac
  >> Cases_on `v_period0`
  >- simp[arithmeticTheory.MOD_0]
  >> mp_tac
       (Q.SPECL [`v_iteration0`, `SUC n`, `v_value0`]
          numberTheory.FUNPOW_MOD)
  >> impl_tac
  >- simp[]
  >> disch_then (qspec_then `v_count0` mp_tac)
  >> simp[]
QED

Theorem source_funpow_mod_zero_imp_normalize:
  !iteration period value count.
    FUNPOW iteration period value = value ==>
    ((count MOD period = 0 ==>
      FUNPOW iteration count value = value) <=>
     (count MOD period = 0 ==>
      FUNPOW iteration (count MOD period) value = value))
Proof
  metis_tac[source_funpow_mod_periodic]
QED

Theorem source_funpow_rotate1_period:
  !xs. FUNPOW source_rotate1 (LENGTH xs) xs = xs
Proof
  simp[GSYM source_rotate_def, source_rotate_period]
QED

Theorem source_rotate_conv_mod:
  !count xs.
    source_rotate count xs =
    source_rotate (count MOD LENGTH xs) xs
Proof
  rpt gen_tac
  >> Cases_on `xs`
  >- simp[source_rotate_def, source_rotate1_def]
  >> fs[source_rotate_def]
  >> irule numberTheory.FUNPOW_MOD
  >> conj_tac
  >- simp[]
  >> qspec_then `h::t` mp_tac source_rotate_period
  >> simp[source_rotate_def]
QED

Theorem source_rotate_map_bridge:
  !count function xs.
    source_rotate count (MAP function xs) =
    MAP function (source_rotate count xs)
Proof
  simp[source_rotate_def, source_funpow_rotate1_map]
QED

(* Rotating the empty list is the identity however often it is done,
   which is what makes [source_rotate_drop_take] unconditional: the
   modulus below is taken by a length that can be zero. *)
Theorem source_rotate_nil:
  !steps. source_rotate steps ([] : 'a list) = []
Proof
  Induct
  >- simp[source_rotate_def]
  >> simp[source_rotate_def, arithmeticTheory.FUNPOW_SUC]
  >> fs[source_rotate_def]
  >> simp[source_rotate1_def]
QED

Theorem source_rotate_drop_take_bounded:
  !steps xs.
    steps <= LENGTH xs ==>
    source_rotate steps xs = DROP steps xs ++ TAKE steps xs
Proof
  rpt strip_tac
  >> qspecl_then [`TAKE steps xs`, `DROP steps xs`] mp_tac
       source_rotate_split_period
  >> simp[]
QED

Theorem source_rotate_drop_take:
  !steps xs.
    source_rotate steps xs =
    DROP (steps MOD LENGTH xs) xs ++ TAKE (steps MOD LENGTH xs) xs
Proof
  rpt strip_tac
  >> Cases_on `xs`
  >- simp[source_rotate_nil]
  >> qabbrev_tac `ys = h::t`
  >> `0 < LENGTH ys` by simp[Abbr `ys`]
  >> `steps MOD LENGTH ys < LENGTH ys` by simp[]
  >> ONCE_REWRITE_TAC [source_rotate_conv_mod]
  >> irule source_rotate_drop_take_bounded
  >> simp[]
QED

Theorem source_nth_rotate:
  !steps xs index.
    index < LENGTH xs ==>
    EL index (source_rotate steps xs) =
    EL ((steps + index) MOD LENGTH xs) xs
Proof
  rpt strip_tac
  >> `0 < LENGTH xs` by simp[]
  >> `steps MOD LENGTH xs < LENGTH xs` by simp[]
  >> `(steps + index) MOD LENGTH xs =
      (steps MOD LENGTH xs + index) MOD LENGTH xs`
       by metis_tac[arithmeticTheory.MOD_PLUS, arithmeticTheory.LESS_MOD]
  >> qabbrev_tac `offset = steps MOD LENGTH xs`
  >> simp[source_rotate_drop_take]
  >> Cases_on `index < LENGTH xs - offset`
  >- simp[rich_listTheory.EL_APPEND1, listTheory.EL_DROP]
  >> simp[rich_listTheory.EL_APPEND2, listTheory.EL_TAKE]
  >> `LENGTH xs <= index + offset` by simp[]
  >> `index + offset - LENGTH xs < LENGTH xs` by simp[]
  >> `(index + offset) MOD LENGTH xs = index + offset - LENGTH xs`
       by metis_tac[arithmeticTheory.SUB_MOD, arithmeticTheory.LESS_MOD]
  >> simp[]
QED

Definition source_unrotate1_def:
  source_unrotate1 (xs : 'a list) =
    if NULL xs then [] else LAST xs :: FRONT xs
End

Theorem source_rotate1_inverse:
  !xs.
    source_rotate1 (source_unrotate1 xs) = xs /\
    source_unrotate1 (source_rotate1 xs) = xs
Proof
  Cases
  >> simp[source_rotate1_def, source_unrotate1_def,
          listTheory.APPEND_FRONT_LAST,
          GSYM listTheory.SNOC_APPEND]
QED

(* Isabelle's [inj], [surj] and [bij] are [inj_on f UNIV], [range f =
   UNIV] and [bij_betw f UNIV UNIV]; the HOL4 library states all three
   of a function between two sets, so the three read [INJ], [SURJ] and
   [BIJ] at [UNIV], which is what the [bij_rotate1] goal is stated
   with.  A [blast] that is handed the two of them and [bijI] matches
   atoms, exactly as the source method's does. *)
Theorem source_rotate1_inj:
  INJ source_rotate1 UNIV UNIV
Proof
  simp[pred_setTheory.INJ_DEF]
  >> metis_tac[source_rotate1_inverse]
QED

Theorem source_rotate1_surj:
  SURJ source_rotate1 UNIV UNIV
Proof
  simp[pred_setTheory.SURJ_DEF]
  >> metis_tac[source_rotate1_inverse]
QED

(* Isabelle/HOL src/HOL/Fun.thy:376.  HOL4 states the same content as
   the definition of [BIJ], an equivalence the claset cannot take as
   the introduction the method asks for. *)
Theorem source_bijI:
  !function source target.
    INJ function source target ==>
    SURJ function source target ==>
    BIJ function source target
Proof
  simp[pred_setTheory.BIJ_DEF]
QED

(* Isabelle/HOL src/HOL/List.thy:5329-5411. *)
(* [0..<size xs] is written GENLIST rather than COUNT_LIST: both denote
   the index list, but GENLIST's base case is a simp rule, so a [nths]
   at a known list reduces the way Isabelle's does. *)
Definition source_nths_def:
  source_nths (xs : 'a list) (indices : num set) =
    MAP FST
      (FILTER (\pair. SND pair IN indices)
        (ZIP (xs, GENLIST (\index. index) (LENGTH xs))))
End

Theorem source_nths_index_zip:
  !xs : 'a list.
    ZIP (xs, GENLIST (\index. index) (LENGTH xs)) =
    MAP (\index. (EL index xs, index))
      (GENLIST (\index. index) (LENGTH xs))
Proof
  simp[listTheory.LIST_EQ_REWRITE, listTheory.LENGTH_ZIP,
       listTheory.EL_ZIP, listTheory.EL_MAP, listTheory.EL_GENLIST]
QED

Theorem source_nths_filter_bridge:
  !xs indices.
    source_nths xs indices =
    MAP (\index. EL index xs)
      (FILTER (\index. index IN indices)
        (rich_list$COUNT_LIST (LENGTH xs)))
Proof
  simp[source_nths_def, source_nths_index_zip,
       rich_listTheory.FILTER_MAP, listTheory.MAP_MAP_o,
       combinTheory.o_DEF, rich_listTheory.COUNT_LIST_GENLIST,
       combinTheory.I_DEF, combinTheory.S_DEF, combinTheory.K_DEF]
QED

(* The recursion Isabelle does not state.  It is where the primitive
   equations went: consumers that take a [nths] apart one element at a
   time use this, and the definition stays the one the source writes. *)
Theorem source_nths_recursion:
  (!indices. source_nths ([] : 'a list) indices = []) /\
  (!head tail indices.
     source_nths (head::tail) indices =
     (if 0 IN indices then [head] else []) ++
     source_nths tail {index | SUC index IN indices})
Proof
  conj_tac
  >- simp[source_nths_filter_bridge, rich_listTheory.COUNT_LIST_def]
  >> rpt gen_tac
  >> Cases_on `0 IN indices`
  >> simp[source_nths_filter_bridge, rich_listTheory.COUNT_LIST_def,
          rich_listTheory.FILTER_MAP, listTheory.MAP_MAP_o,
          combinTheory.o_DEF, listTheory.EL]
QED

Theorem source_nths_set_subset:
  !xs indices value.
    MEM value (source_nths xs indices) ==> MEM value xs
Proof
  Induct_on `xs`
  >- simp[source_nths_recursion]
  >> rpt gen_tac
  >> rw[source_nths_recursion]
  >> first_x_assum drule
  >> simp[]
QED

Theorem source_set_nths:
  !xs indices.
    LIST_TO_SET (source_nths xs indices) =
    {value | ?index. index < LENGTH xs /\ index IN indices /\
                     value = EL index xs}
Proof
  rw[source_nths_filter_bridge, pred_setTheory.EXTENSION,
     listTheory.MEM_MAP, listTheory.MEM_FILTER,
     rich_listTheory.MEM_COUNT_LIST]
  >> metis_tac[]
QED

Theorem source_map_el_filter_count_mem:
  !xs predicate value.
    MEM value
      (MAP (\index. EL index xs)
        (FILTER predicate
          (rich_list$COUNT_LIST (LENGTH xs)))) ==>
    MEM value xs
Proof
  simp[listTheory.MEM_MAP, listTheory.MEM_FILTER,
       rich_listTheory.MEM_COUNT_LIST]
  >> metis_tac[listTheory.EL_MEM]
QED

Theorem source_nths_length_bridge:
  !xs indices.
    LENGTH (source_nths xs indices) =
    CARD {index | index < LENGTH xs /\ index IN indices}
Proof
  rpt gen_tac
  >> rw[source_nths_filter_bridge]
  >> qabbrev_tac
       `selected =
          FILTER (\index. index IN indices)
            (rich_list$COUNT_LIST (LENGTH xs))`
  >> `ALL_DISTINCT selected`
       by simp[Abbr `selected`, listTheory.FILTER_ALL_DISTINCT,
               rich_listTheory.all_distinct_count_list]
  >> drule listTheory.ALL_DISTINCT_CARD_LIST_TO_SET
  >> strip_tac
  >> fs[Abbr `selected`, listTheory.LIST_TO_SET_FILTER,
        rich_listTheory.COUNT_LIST_COUNT]
  >> `indices INTER count (LENGTH xs) =
      {index | index < LENGTH xs /\ index IN indices}`
       by (rw[pred_setTheory.EXTENSION, pred_setTheory.IN_COUNT]
           >> metis_tac[])
  >> fs[]
QED

(* The index-list case, from which the general statement below follows. *)
Theorem source_length_filter_count_index:
  !predicate size.
    LENGTH
      (FILTER predicate (rich_list$COUNT_LIST size)) =
    CARD {index | index < size /\ predicate index}
Proof
  rpt gen_tac
  >> qabbrev_tac
       `selected = FILTER predicate (rich_list$COUNT_LIST size)`
  >> `ALL_DISTINCT selected`
       by simp[Abbr `selected`, listTheory.FILTER_ALL_DISTINCT,
               rich_listTheory.all_distinct_count_list]
  >> drule listTheory.ALL_DISTINCT_CARD_LIST_TO_SET
  >> strip_tac
  >> fs[Abbr `selected`, listTheory.LIST_TO_SET_FILTER,
        rich_listTheory.COUNT_LIST_COUNT]
  >> `{index | predicate index} INTER count size =
      {index | index < size /\ predicate index}`
       by (rw[pred_setTheory.EXTENSION, pred_setTheory.IN_COUNT]
           >> metis_tac[])
  >> fs[]
QED

(* src/HOL/List.thy: length_filter_conv_card.  Isabelle states it for
   any list; the index list is the special case above. *)
Theorem source_length_filter_count:
  !predicate xs : 'a list.
    LENGTH (FILTER predicate xs) =
    CARD {index | index < LENGTH xs /\ predicate (EL index xs)}
Proof
  rpt gen_tac
  >> `LENGTH (FILTER predicate xs) =
      LENGTH (FILTER (\index. predicate (EL index xs))
                (rich_list$COUNT_LIST (LENGTH xs)))`
       by (Induct_on `xs`
           >> simp[rich_listTheory.COUNT_LIST_def,
                   rich_listTheory.FILTER_MAP, listTheory.EL,
                   combinTheory.o_DEF]
           >> rw[])
  >> simp[source_length_filter_count_index]
QED

(* src/HOL/List.thy:1664 @ f7e02b7e: [length_filter_less].  HOL4's
   rich_listTheory.LENGTH_FILTER_LESS carries the same content with the
   premise packed as an EXISTS over the negated predicate; Isabelle
   names the element the predicate fails at, and states the two
   premises as a meta-implication chain rather than a conjunction, so a
   destruction rule built from it matches the membership alone. *)
Theorem source_length_filter_less:
  !value xs predicate.
    MEM value xs ==>
    ~predicate value ==>
    LENGTH (FILTER predicate xs) < LENGTH xs
Proof
  rpt strip_tac
  >> irule rich_listTheory.LENGTH_FILTER_LESS
  >> simp[listTheory.EXISTS_MEM, combinTheory.o_THM]
  >> metis_tac[]
QED

Theorem source_shift_image:
  !count indices.
    {index |
       SUC index IN
       IMAGE (\value. SUC count + value) indices} =
    IMAGE (\value. count + value) indices
Proof
  rw[pred_setTheory.EXTENSION]
  >> eq_tac
  >> rw[]
  >- (qexists_tac `value`
      >> fs[]
      >> decide_tac)
  >> qexists_tac `value`
  >> fs[]
  >> decide_tac
QED

Theorem source_nths_drop:
  !count xs indices.
    source_nths (DROP count xs) indices =
    source_nths xs (IMAGE (\index. count + index) indices)
Proof
  Induct
  >- simp[source_nths_recursion, pred_setTheory.EXTENSION]
  >> Cases_on `xs`
  >> simp[source_nths_recursion, source_shift_image]
QED

Theorem source_selected_drop_shift:
  !count xs selected.
    MAP (\index. EL index (DROP count xs))
      (FILTER (\index. index IN selected)
        (rich_list$COUNT_LIST (LENGTH (DROP count xs)))) =
    MAP (\index. EL index xs)
      (FILTER
        (\index.
           index IN
             IMAGE (\offset. count + offset)
               selected)
        (rich_list$COUNT_LIST (LENGTH xs)))
Proof
  rpt gen_tac
  >> PURE_REWRITE_TAC [GSYM source_nths_filter_bridge]
  >> simp[source_nths_drop]
QED

(* Isabelle/HOL src/HOL/List.thy:8287-8321. *)
Definition source_atMost_def:
  source_atMost le bound = {value | le value bound}
End

Definition source_lessThan_def:
  source_lessThan lt bound = {value | lt value bound}
End

Definition source_atLeast_def:
  source_atLeast le bound = {value | le bound value}
End

Definition source_greaterThan_def:
  source_greaterThan lt bound = {value | lt bound value}
End

Definition source_atLeastAtMost_def:
  source_atLeastAtMost le lower upper =
    {value | le lower value /\ le value upper}
End

Definition source_greaterThanAtMost_def:
  source_greaterThanAtMost le lt lower upper =
    {value | lt lower value /\ le value upper}
End

Definition source_atLeastLessThan_def:
  source_atLeastLessThan le lt lower upper =
    {value | le lower value /\ lt value upper}
End

Theorem source_interval_membership:
  (!le bound value.
     value IN source_atMost le bound <=> le value bound) /\
  (!lt bound value.
     value IN source_lessThan lt bound <=> lt value bound) /\
  (!le bound value.
     value IN source_atLeast le bound <=> le bound value) /\
  (!lt bound value.
     value IN source_greaterThan lt bound <=> lt bound value)
Proof
  simp[source_atMost_def, source_lessThan_def,
       source_atLeast_def, source_greaterThan_def]
QED

Theorem source_bounded_interval_membership:
  (!le lower upper value.
     value IN source_atLeastAtMost le lower upper <=>
     le lower value /\ le value upper) /\
  (!le lt lower upper value.
     value IN source_greaterThanAtMost le lt lower upper <=>
     lt lower value /\ le value upper) /\
  (!le lt lower upper value.
     value IN source_atLeastLessThan le lt lower upper <=>
     le lower value /\ lt value upper)
Proof
  simp[source_atLeastAtMost_def, source_greaterThanAtMost_def,
       source_atLeastLessThan_def]
QED

Theorem source_num_weak_linear_order:
  relation$WeakLinearOrder ($<= : num -> num -> bool)
Proof
  simp[relationTheory.WeakLinearOrder,
       relationTheory.WeakOrder,
       relationTheory.reflexive_def,
       relationTheory.transitive_def,
       relationTheory.antisymmetric_def,
       relationTheory.trichotomous]
QED

Theorem source_less_than_count:
  !bound.
    source_lessThan ($<) bound = pred_set$count bound
Proof
  simp[source_lessThan_def, pred_setTheory.count_def,
       pred_setTheory.EXTENSION]
QED

(* src/HOL/Set_Interval.thy: lessThan_atLeast0. *)
Theorem source_lessThan_atLeast0:
  !bound : num.
    source_lessThan ($< : num -> num -> bool) bound =
    source_atLeastLessThan ($<= : num -> num -> bool)
      ($< : num -> num -> bool) 0 bound
Proof
  simp[source_lessThan_def, source_atLeastLessThan_def,
       pred_setTheory.EXTENSION]
QED

(* src/HOL/List.thy:6775 @ f7e02b7e.  [sorted_list_of_set_range] is simp
   there.  Its three side conditions -- the interval is finite, the
   interval list is sorted and repeats nothing, and it enumerates the
   interval -- are what the uniqueness theorem asks for, and are stated
   separately here because each is about the interval alone. *)
Theorem source_atLeastLessThan_finite:
  !lower upper : num.
    FINITE (source_atLeastLessThan ($<=) ($<) lower upper)
Proof
  rw[source_atLeastLessThan_def]
  >> irule pred_setTheory.SUBSET_FINITE
  >> qexists `pred_set$count upper`
  >> rw[pred_setTheory.SUBSET_DEF, pred_setTheory.count_def]
QED

(* src/HOL/List.thy:1381 @ f7e02b7e: set_upt. *)
Theorem source_set_atLeastLessThan:
  !lower upper : num.
    LIST_TO_SET (GENLIST ($+ lower) (upper - lower)) =
    source_atLeastLessThan ($<=) ($<) lower upper
Proof
  rw[source_atLeastLessThan_def, pred_setTheory.EXTENSION,
     listTheory.MEM_GENLIST]
  >> eq_tac
  >- (strip_tac >> simp[])
  >> strip_tac >> qexists_tac `x - lower` >> simp[]
QED

Theorem source_sorted_list_of_set_range:
  !lower upper : num.
    source_sorted_list_of_set ($<=)
      (source_atLeastLessThan ($<=) ($<) lower upper) =
    GENLIST ($+ lower) (upper - lower)
Proof
  rpt gen_tac
  >> irule source_sorted_list_of_set_unique
  >> rw[source_atLeastLessThan_finite, source_set_atLeastLessThan,
        source_sorted_bridge, sortingTheory.SORTED_EL_SUC,
        listTheory.ALL_DISTINCT_GENLIST,
        relationTheory.WeakLinearOrder, relationTheory.WeakOrder,
        relationTheory.trichotomous, relationTheory.reflexive_def,
        relationTheory.antisymmetric_def]
  >> simp[]
QED

Theorem source_lessThan_Suc_atMost:
  !bound.
    source_lessThan ($<) (SUC bound) = source_atMost ($<=) bound
Proof
  rw[source_lessThan_def, source_atMost_def, pred_setTheory.EXTENSION]
QED

Theorem source_at_most_count:
  !bound.
    source_atMost ($<=) bound = pred_set$count (SUC bound)
Proof
  simp[source_atMost_def, pred_setTheory.count_def,
       pred_setTheory.EXTENSION]
QED

Theorem source_sorted_list_of_count:
  !bound.
    source_sorted_list_of_set ($<=) (pred_set$count bound) =
    rich_list$COUNT_LIST bound
Proof
  gen_tac
  >> irule source_sorted_list_of_set_unique
  >> simp[source_num_weak_linear_order,
          source_sorted_bridge,
          sortingTheory.sorted_count_list,
          rich_listTheory.all_distinct_count_list,
          rich_listTheory.COUNT_LIST_COUNT]
QED

Theorem source_sorted_list_of_set_less_than_suc:
  !bound.
    source_sorted_list_of_set ($<=)
      (source_lessThan ($<) (SUC bound)) =
    source_sorted_list_of_set ($<=)
      (source_lessThan ($<) bound) ++ [bound]
Proof
  simp[source_less_than_count,
       source_sorted_list_of_count,
       rich_listTheory.COUNT_LIST_SNOC,
       listTheory.SNOC_APPEND]
QED

Theorem source_sorted_list_of_set_at_most_suc:
  !bound.
    source_sorted_list_of_set ($<=)
      (source_atMost ($<=) (SUC bound)) =
    source_sorted_list_of_set ($<=)
      (source_atMost ($<=) bound) ++ [SUC bound]
Proof
  simp[source_at_most_count,
       source_sorted_list_of_count,
       rich_listTheory.COUNT_LIST_SNOC,
       listTheory.SNOC_APPEND]
QED

Theorem source_sorted_list_of_set_greater_than_at_most:
  !lower upper.
    lower < upper ==>
    source_sorted_list_of_set ($<=)
      (source_greaterThanAtMost ($<=) ($<) lower upper) =
    GENLIST ($+ (SUC lower)) (upper - lower)
Proof
  rpt strip_tac
  >> irule source_sorted_list_of_set_unique
  >> simp[source_num_weak_linear_order,
          source_sorted_bridge,
          sortingTheory.SORTED_GENLIST_PLUS,
          listTheory.ALL_DISTINCT_GENLIST,
          listTheory.LIST_TO_SET_GENLIST,
          source_greaterThanAtMost_def,
          pred_setTheory.EXTENSION,
          pred_setTheory.FINITE_COUNT,
          pred_setTheory.SUBSET_DEF]
  >> conj_tac
  >- (irule pred_setTheory.SUBSET_FINITE
      >> qexists_tac `pred_set$count (SUC upper)`
      >> simp[pred_setTheory.SUBSET_DEF,
              pred_setTheory.count_def])
  >> conj_tac
  >- (gen_tac
      >> eq_tac
      >- (strip_tac >> decide_tac)
      >> strip_tac
      >> qexists_tac `x - SUC lower`
      >> decide_tac)
  >> irule sortingTheory.SORTED_weaken
  >> qexists_tac `$<`
  >> simp[sortingTheory.SORTED_GENLIST_PLUS]
QED

Theorem source_el_genlist_suc_add:
  !index lower length.
    index < length ==>
    EL index (GENLIST ($+ (SUC lower)) length) =
    SUC (lower + index)
Proof
  simp[listTheory.EL_GENLIST]
QED

Theorem source_index_bound_positive:
  !v_index0 v_bound0 : num.
    v_index0 < v_bound0 ==> 0 < v_bound0
Proof
  rpt strip_tac
  >> decide_tac
QED

Theorem source_sorted_list_of_set_greater_than_at_most_positive:
  !v_lower0 v_upper0.
    0 < v_upper0 - v_lower0 ==>
    source_sorted_list_of_set ($<=)
      (source_greaterThanAtMost ($<=) ($<) v_lower0 v_upper0) =
    GENLIST ($+ (SUC v_lower0)) (v_upper0 - v_lower0)
Proof
  rpt strip_tac
  >> irule source_sorted_list_of_set_greater_than_at_most
  >> match_mp_tac
       (iffRL
         (Q.SPECL [`v_upper0`, `v_lower0`]
            arithmeticTheory.SUB_LESS_0))
  >> simp[]
QED

Theorem source_nth_sorted_list_of_set_greater_than_at_most:
  !index lower upper.
    index < upper - lower ==>
    EL index
      (source_sorted_list_of_set ($<=)
        (source_greaterThanAtMost ($<=) ($<) lower upper)) =
    SUC (lower + index)
Proof
  rpt strip_tac
  >> `lower < upper` by decide_tac
  >> simp[source_sorted_list_of_set_greater_than_at_most,
          listTheory.EL_GENLIST]
QED

(* Isabelle/HOL src/HOL/List.thy:8527-8548. *)
Definition source_map_filter_def:
  source_map_filter function xs =
    MAP (THE o function)
      (FILTER (\value. function value <> NONE) xs)
End

Theorem source_map_filter_bridge:
  (!function. source_map_filter function [] = []) /\
  (!function head tail.
     source_map_filter function (head::tail) =
     case function head of
       NONE => source_map_filter function tail
     | SOME value => value::source_map_filter function tail)
Proof
  conj_tac
  >- simp[source_map_filter_def, combinTheory.o_DEF]
  >> rpt gen_tac
  >> Cases_on `function head`
  >> simp[source_map_filter_def, combinTheory.o_DEF]
QED

Theorem source_mem_map_filter:
  !function xs value.
    MEM value (source_map_filter function xs) <=>
    ?item. MEM item xs /\ function item = SOME value
Proof
  gen_tac
  >> Induct
  >- simp[source_map_filter_bridge]
  >> gen_tac
  >> Cases_on `function h`
  >> simp[source_map_filter_bridge, RIGHT_AND_OVER_OR,
          EXISTS_OR_THM, EQ_SYM_EQ]
QED

Theorem source_map_filter_some_filter:
  !function predicate xs.
    MAP
      (\value.
         THE
           (if predicate value then SOME (function value) else NONE))
      (FILTER predicate xs) =
    MAP function (FILTER predicate xs)
Proof
  rpt gen_tac
  >> Induct_on `xs`
  >- simp[combinTheory.o_DEF]
  >> gen_tac
  >> Cases_on `predicate h`
  >> fs[combinTheory.o_DEF]
QED

(* Isabelle/HOL src/HOL/List.thy:8199-8206, 8673-8694. *)
Definition source_can_select_def:
  source_can_select predicate domain <=>
    ?value.
      value IN domain /\ predicate value /\
      !other.
        other IN domain /\ predicate other ==> other = value
End

Definition source_list_ex1_def:
  source_list_ex1 predicate xs <=>
    source_can_select predicate (LIST_TO_SET xs)
End

Definition source_list_all_def:
  source_list_all predicate xs <=> EVERY predicate xs
End

Definition source_these_def:
  source_these domain = {value | SOME value IN domain}
End

Theorem source_these_list_to_set:
  !xs.
    source_these (LIST_TO_SET xs) =
    LIST_TO_SET (source_map_filter I xs)
Proof
  Induct
  >- simp[source_these_def, source_map_filter_def]
  >> Cases_on `h`
  >> fs[source_these_def, source_map_filter_def,
        combinTheory.o_DEF, pred_setTheory.EXTENSION]
QED

Definition source_Id_on_def:
  source_Id_on domain =
    {pair | ?value. value IN domain /\ pair = (value, value)}
End

(* Isabelle/HOL src/HOL/List.thy:7790-7870.  A set of pairs is
   represented as its curried membership predicate.

   The equation is stated at the argument the source's own definition
   is stated at -- [listrel1 r = {(xs, ys). ...}] names the set, not
   its membership -- and not at the two points the membership adds.  A
   citation of it is an [unfolding], which rewrites the goal before the
   search sees it, and a goal that equates two relations has no
   occurrence of the constant applied to a point for a pointwise
   equation to meet: [list_L7861_listrel1_converse] is
   [source_listrel1 (\left right. relation right left) = _], where the
   pointwise form rewrites nothing at all and the search is then left
   with an opaque constant on both sides. *)
Definition source_listrel1_def:
  source_listrel1 relation =
    \xs ys.
      ?prefix left right suffix.
        xs = prefix ++ left::suffix /\
        relation left right /\
        ys = prefix ++ right::suffix
End

(* src/HOL/List.thy: listrel1E.  The definition is an equivalence, which
   the claset cannot take as the elimination the method asks for. *)
Theorem source_listrel1E:
  !relation xs ys conclusion.
    source_listrel1 relation xs ys ==>
    (!prefix left right suffix.
       xs = prefix ++ left::suffix ==>
       ys = prefix ++ right::suffix ==>
       relation left right ==>
       conclusion) ==>
    conclusion
Proof
  metis_tac[source_listrel1_def]
QED

(* src/HOL/List.thy:7750 [not_Nil_listrel1] and :7753
   [not_listrel1_Nil], both declared [iff].  A one-step rewrite of a
   list is a rewrite of one of its positions, so neither end of it can
   be empty. *)
Theorem source_not_Nil_listrel1:
  !relation ys. ~source_listrel1 relation [] ys
Proof
  rpt gen_tac
  >> simp[source_listrel1_def]
  >> rpt strip_tac
  >> Cases_on `prefix`
  >> fs[]
QED

Theorem source_not_listrel1_Nil:
  !relation xs. ~source_listrel1 relation xs []
Proof
  rpt gen_tac
  >> simp[source_listrel1_def]
  >> rpt strip_tac
  >> Cases_on `prefix`
  >> fs[]
QED

(* src/HOL/List.thy:7756 [Cons_listrel1_Cons], declared [iff]: the step
   is either at the head or inside the tail. *)
Theorem source_Cons_listrel1_Cons:
  !relation x xs y ys.
    source_listrel1 relation (x::xs) (y::ys) <=>
    relation x y /\ xs = ys \/ x = y /\ source_listrel1 relation xs ys
Proof
  rpt gen_tac
  >> eq_tac
  >- (strip_tac
      >> fs[source_listrel1_def]
      >> Cases_on `prefix`
      >> fs[]
      >> metis_tac[])
  >> strip_tac
  >> fs[source_listrel1_def]
  >- (map_every qexists_tac [`[]`, `x`, `y`, `ys`] >> simp[])
  >> map_every qexists_tac [`y::prefix`, `left`, `right`, `suffix`]
  >> simp[]
QED

(* src/HOL/List.thy:7773 [Cons_listrel1E1] and :7780 [Cons_listrel1E2],
   both declared [elim!]: the two case splits the equivalence above
   supports when only one side is known to be a cons. *)
Theorem source_Cons_listrel1E1:
  !relation x xs ys conclusion.
    source_listrel1 relation (x::xs) ys ==>
    (!y. ys = y::xs ==> relation x y ==> conclusion) ==>
    (!zs. ys = x::zs ==> source_listrel1 relation xs zs ==> conclusion) ==>
    conclusion
Proof
  rpt gen_tac
  >> Cases_on `ys`
  >> fs[source_not_listrel1_Nil, source_Cons_listrel1_Cons]
  >> rpt strip_tac
  >> fs[]
  >> metis_tac[]
QED

Theorem source_Cons_listrel1E2:
  !relation xs y ys conclusion.
    source_listrel1 relation xs (y::ys) ==>
    (!x. xs = x::ys ==> relation x y ==> conclusion) ==>
    (!zs. xs = y::zs ==> source_listrel1 relation zs ys ==> conclusion) ==>
    conclusion
Proof
  rpt gen_tac
  >> Cases_on `xs`
  >> fs[source_not_Nil_listrel1, source_Cons_listrel1_Cons]
  >> rpt strip_tac
  >> fs[]
  >> metis_tac[]
QED

(* Isabelle/HOL src/HOL/List.thy:7247-7760.  Isabelle's [lex] is
   equal-length lexicographic order, [lenlex] is shortlex, and
   [lexord] is the prefix-aware lexicographic order. *)
Definition source_lex_def:
  source_lex relation xs ys <=>
    LENGTH xs = LENGTH ys /\ list$LLEX relation xs ys
End

(* Isabelle/HOL src/HOL/List.thy:7064.  [lenlex] composes there -- two
   lists are compared by their lengths and, at equal length, by [lex]
   -- and every source result about it is proved by unfolding this one
   definition.  Stated as SHORTLEX -- the same order -- the citation
   those proofs name would have nothing to unfold: the length
   comparison would be HOL4's recursion instead. *)
Definition source_lenlex_def:
  source_lenlex relation =
    relation$inv_image
      (pair$LEX (($<) : num -> num -> bool) (source_lex relation))
      (\xs. (LENGTH xs, xs))
End

Definition source_lexord_def:
  source_lexord relation xs ys <=> list$LLEX relation xs ys
End

(* Isabelle/HOL src/HOL/List.thy:7361.  Isabelle introduces [lexord] by
   this comprehension; HOL4 already has the relation as [LLEX], so the
   closed form is a theorem here rather than the definition. *)
Theorem source_lexord_conv:
  !relation xs ys.
    (source_lexord relation xs ys <=>
     (?item rest. ys = xs ++ item::rest) \/
     (?prefix left right xs' ys'.
        relation left right /\
        xs = prefix ++ left::xs' /\
        ys = prefix ++ right::ys'))
Proof
  simp[source_lexord_def]
  >> gen_tac
  >> Induct
  >- (Cases >> rw[listTheory.LLEX_def] >> metis_tac[listTheory.APPEND])
  >> rpt gen_tac
  >> Cases_on `ys`
  >> rw[listTheory.LLEX_def, listTheory.APPEND_EQ_CONS]
  >> metis_tac[listTheory.APPEND, listTheory.CONS_11]
QED

(* Isabelle/HOL src/HOL/List.thy:7478, by Rene Thiemann.  Transitivity
   is required only at the elements of [xs].  The form with a global
   [transitive] premise is the corpus goal at line 7508. *)
Theorem source_lexord_partial_trans:
  !relation xs ys zs.
    (!x y z. MEM x xs /\ relation x y /\ relation y z ==> relation x z) ==>
    source_lexord relation xs ys ==>
    source_lexord relation ys zs ==>
    source_lexord relation xs zs
Proof
  simp[source_lexord_def]
  >> gen_tac
  >> Induct
  >- (rw[]
      >> Cases_on `ys`
      >> Cases_on `zs`
      >> fs[listTheory.LLEX_def])
  >> rpt gen_tac
  >> Cases_on `ys`
  >> Cases_on `zs`
  >> rw[listTheory.LLEX_def]
  >> gvs[]
  >> metis_tac[listTheory.MEM]
QED

(* Isabelle/HOL src/HOL/List.thy:7612, by Andreas Lochbihler.  The
   predicate form of the lexicographic order, defined inductively; the
   equations below are Isabelle's [lexordp_simps], which it marks [simp].
   Where the set form compares equal heads with [x = y], this one asks
   [~relation y x]; the two agree only in the linear order this is
   stated in, so results relating the two carry that premise. *)
Definition source_lexordp_def:
  (source_lexordp relation [] ys <=> ys <> []) /\
  (source_lexordp relation (x::xs) [] <=> F) /\
  (source_lexordp relation (x::xs) (y::ys) <=>
     relation x y \/ (~relation y x /\ source_lexordp relation xs ys))
End

(* Isabelle/HOL src/HOL/List.thy:7627.  The reflexive closure, likewise
   inductive rather than [xs = ys \/ source_lexordp relation xs ys]. *)
Definition source_lexordp_eq_def:
  (source_lexordp_eq relation [] ys <=> T) /\
  (source_lexordp_eq relation (x::xs) [] <=> F) /\
  (source_lexordp_eq relation (x::xs) (y::ys) <=>
     relation x y \/ (~relation y x /\ source_lexordp_eq relation xs ys))
End

(* Isabelle/HOL src/HOL/List.thy:7703.  The closed form of the predicate
   order.  Isabelle proves it inside [context linorder]; the premise here
   is what that context supplies. *)
Theorem source_lexordp_iff:
  !relation xs ys.
    relation$StrongLinearOrder relation ==>
    (source_lexordp relation xs ys <=>
     (?item rest. ys = xs ++ item::rest) \/
     (?prefix left right xs' ys'.
        relation left right /\
        xs = prefix ++ left::xs' /\
        ys = prefix ++ right::ys'))
Proof
  rpt gen_tac
  >> strip_tac
  >> `!x y. ~relation x y /\ ~relation y x <=> x = y`
       by (fs[relationTheory.StrongLinearOrder, relationTheory.StrongOrder,
              relationTheory.irreflexive_def, relationTheory.trichotomous]
           >> metis_tac[])
  >> qid_spec_tac `ys`
  >> Induct_on `xs`
  >- (Cases >> rw[source_lexordp_def] >> metis_tac[listTheory.APPEND])
  >> rpt gen_tac
  >> Cases_on `ys`
  >> rw[source_lexordp_def, listTheory.APPEND_EQ_CONS]
  >> metis_tac[listTheory.APPEND, listTheory.CONS_11]
QED

(* Isabelle/HOL src/HOL/List.thy:7644.  No order is needed: the equal-heads
   clause of [source_lexordp_eq] holds whatever [relation] does at [x]. *)
Theorem source_lexordp_eq_refl:
  !relation xs. source_lexordp_eq relation xs xs
Proof
  gen_tac >> Induct >> rw[source_lexordp_eq_def]
QED

(* Isabelle/HOL src/HOL/List.thy:7719. *)
Theorem source_lexordp_eq_antisym:
  !relation xs ys.
    relation$StrongLinearOrder relation ==>
    source_lexordp_eq relation xs ys ==>
    source_lexordp_eq relation ys xs ==>
    xs = ys
Proof
  rpt gen_tac
  >> strip_tac
  >> `(!x y. ~relation x y /\ ~relation y x <=> x = y) /\
      (!x y. relation x y ==> ~relation y x)`
       by (fs[relationTheory.StrongLinearOrder, relationTheory.StrongOrder,
              relationTheory.irreflexive_def, relationTheory.trichotomous,
              relationTheory.transitive_def]
           >> metis_tac[])
  >> qid_spec_tac `ys`
  >> Induct_on `xs`
  >- (Cases >> rw[source_lexordp_eq_def])
  >> rpt gen_tac
  >> Cases_on `ys`
  >> rw[source_lexordp_eq_def]
  >> metis_tac[]
QED

(* Isabelle/HOL src/HOL/List.thy:7740. *)
Theorem source_lexordp_conv_lexordp_eq:
  !relation xs ys.
    relation$StrongLinearOrder relation ==>
    (source_lexordp relation xs ys <=>
     source_lexordp_eq relation xs ys /\
     ~source_lexordp_eq relation ys xs)
Proof
  rpt gen_tac
  >> strip_tac
  >> `(!x y. ~relation x y /\ ~relation y x <=> x = y) /\
      (!x y. relation x y ==> ~relation y x)`
       by (fs[relationTheory.StrongLinearOrder, relationTheory.StrongOrder,
              relationTheory.irreflexive_def, relationTheory.trichotomous,
              relationTheory.transitive_def]
           >> metis_tac[])
  >> qid_spec_tac `ys`
  >> Induct_on `xs`
  >- (Cases >> rw[source_lexordp_def, source_lexordp_eq_def])
  >> rpt gen_tac
  >> Cases_on `ys`
  >> rw[source_lexordp_def, source_lexordp_eq_def]
  >> metis_tac[]
QED

Theorem source_lex_conv:
  !relation xs ys.
    source_lex relation xs ys <=>
    LENGTH xs = LENGTH ys /\
    ?prefix left right xs' ys'.
      xs = prefix ++ (left::xs') /\
      ys = prefix ++ (right::ys') /\
      relation left right
Proof
  rpt gen_tac
  >> eq_tac
  >- (rw[source_lex_def, listTheory.LLEX_EL_THM]
      >> `n < LENGTH xs` by fs[]
      >> map_every qexists_tac
           [`TAKE n xs`, `EL n xs`, `EL n ys`,
            `DROP (SUC n) xs`, `DROP (SUC n) ys`]
      >> simp[rich_listTheory.TAKE_DROP_SUC])
  >> rw[source_lex_def, listTheory.LLEX_EL_THM]
  >> qexists_tac `LENGTH prefix`
  >> simp[listTheory.EL_APPEND_EQN,
          rich_listTheory.TAKE_APPEND1,
          rich_listTheory.TAKE_LENGTH_APPEND]
QED

Theorem source_shortlex_equal_length:
  !relation xs ys.
    LENGTH xs = LENGTH ys ==>
    (list$SHORTLEX relation xs ys <=> list$LLEX relation xs ys)
Proof
  gen_tac
  >> Induct
  >> Cases_on `ys`
  >> simp[listTheory.SHORTLEX_def, listTheory.LLEX_def]
  >> metis_tac[]
QED

Theorem source_shortlex_length_llex:
  !relation xs ys.
    list$SHORTLEX relation xs ys <=>
    LENGTH xs < LENGTH ys \/
    (LENGTH xs = LENGTH ys /\ list$LLEX relation xs ys)
Proof
  metis_tac[source_shortlex_equal_length,
            listTheory.LENGTH_LT_SHORTLEX,
            listTheory.SHORTLEX_LENGTH_LE,
            arithmeticTheory.LESS_OR_EQ]
QED

(* Isabelle/HOL src/HOL/List.thy:7227, 7230, 7233 and 7295.  Everything
   Isabelle's ambient context carries about [lex]: two [iff] rules, a
   [simp] rule taking a pair of conses apart, and the irreflexive
   reading.  HOL4 has no equal-length lexicographic order for them to
   be stated about, so they are stated here, as [source_wf_lex] is. *)
Theorem source_Nil_notin_lex:
  !relation ys. ~source_lex relation [] ys
Proof
  rpt gen_tac
  >> Cases_on `ys`
  >> simp[source_lex_def]
QED

Theorem source_Nil2_notin_lex:
  !relation xs. ~source_lex relation xs []
Proof
  rpt gen_tac
  >> Cases_on `xs`
  >> simp[source_lex_def]
QED

Theorem source_Cons_in_lex:
  !relation left lefts right rights.
    source_lex relation (left::lefts) (right::rights) <=>
    (relation left right /\ LENGTH lefts = LENGTH rights) \/
    (left = right /\ source_lex relation lefts rights)
Proof
  rw[source_lex_def]
  >> metis_tac[]
QED

Theorem source_lexl_not_refl:
  !relation xs.
    relation$irreflexive relation ==> ~source_lex relation xs xs
Proof
  rpt gen_tac
  >> strip_tac
  >> simp[source_lex_def]
  >> Induct_on `xs`
  >> fs[relationTheory.irreflexive_def, listTheory.LLEX_THM]
QED

(* Isabelle/HOL src/HOL/List.thy:7083 [wf_lex], a safe introduction
   there.  HOL4 has no equal-length lexicographic order of its own to
   carry the rule, so the translation states it about [source_lex];
   SHORTLEX is the same order once the lengths agree. *)
Theorem source_wf_lex:
  !relation.
    relation$WF relation ==> relation$WF (source_lex relation)
Proof
  rpt strip_tac
  >> irule relationTheory.WF_SUBSET
  >> qexists_tac `list$SHORTLEX relation`
  >> simp[listTheory.WF_SHORTLEX, source_lex_def]
  >> metis_tac[source_shortlex_equal_length]
QED

Theorem source_lenlex_conv:
  !relation xs ys.
    source_lenlex relation xs ys <=>
    LENGTH xs < LENGTH ys \/
    (LENGTH xs = LENGTH ys /\ source_lex relation xs ys)
Proof
  simp[source_lenlex_def, relationTheory.inv_image_def,
       pairTheory.LEX_DEF_THM]
QED

Theorem source_lenlex_shortlex:
  !relation xs ys.
    source_lenlex relation xs ys <=> list$SHORTLEX relation xs ys
Proof
  simp[source_lenlex_conv, source_lex_def]
  >> metis_tac[source_shortlex_equal_length,
                listTheory.LENGTH_LT_SHORTLEX,
                listTheory.SHORTLEX_LENGTH_LE,
                arithmeticTheory.LESS_OR_EQ]
QED

(* Isabelle/HOL src/HOL/List.thy:7189 [lex_transI], which carries no
   attribute there: it is what [lenlex_transI] below is proved from. *)
Theorem source_lex_transI:
  !relation.
    relation$transitive relation ==>
    relation$transitive (source_lex relation)
Proof
  rpt strip_tac
  >> `relation$transitive (list$LLEX relation)` by
       simp[listTheory.LLEX_transitive]
  >> fs[relationTheory.transitive_def, source_lex_def]
  >> metis_tac[]
QED

(* Isabelle/HOL src/HOL/List.thy:7197 [wf_lenlex], a safe introduction
   there, and :7223 [lenlex_transI], an unsafe one. *)
Theorem source_wf_lenlex:
  !relation.
    relation$WF relation ==> relation$WF (source_lenlex relation)
Proof
  rpt strip_tac
  >> simp[source_lenlex_def]
  >> irule relationTheory.WF_inv_image
  >> irule pairTheory.WF_LEX
  >> simp[prim_recTheory.WF_LESS, source_wf_lex]
QED

Theorem source_lenlex_transI:
  !relation.
    relation$transitive relation ==>
    relation$transitive (source_lenlex relation)
Proof
  rpt strip_tac
  >> simp[source_lenlex_def]
  >> irule relationTheory.transitive_inv_image
  >> irule pairTheory.transitive_LEX
  >> simp[source_lex_transI, relationTheory.transitive_def]
QED

(* Isabelle/HOL src/HOL/List.thy:7244 and :7245, both simp. *)
Theorem source_Nil_lenlex_iff1:
  !relation xs. source_lenlex relation [] xs <=> xs <> []
Proof
  rpt gen_tac
  >> Cases_on `xs`
  >> simp[source_lenlex_conv, source_Nil_notin_lex]
QED

Theorem source_Nil_lenlex_iff2:
  !relation xs. ~source_lenlex relation xs []
Proof
  simp[source_lenlex_conv, source_Nil2_notin_lex]
QED

Definition source_asym_def:
  source_asym relation <=>
    !left right. relation left right ==> ~relation right left
End

Theorem source_shortlex_asym:
  !relation.
    source_asym relation ==>
    source_asym (list$SHORTLEX relation)
Proof
  simp[source_asym_def]
  >> gen_tac
  >> strip_tac
  >> Induct_on `left`
  >> Cases_on `right`
  >> simp[listTheory.SHORTLEX_def]
  >> rpt strip_tac
  >> TRY decide_tac
  >> metis_tac[]
QED

(* Isabelle/HOL src/HOL/Relation.thy:1677 [asym_inv_image],
   src/HOL/Wellfounded.thy:987 [asym_less_than] and
   src/HOL/List.thy:7511 [asym_lex] -- the three facts the source
   proves [asym_lenlex] from, none of them attributed there -- and
   src/HOL/Wellfounded.thy:1318 [asym_lex_prod], which is simp and is
   what carries those three across the pair product [lenlex] composes
   over. *)
Theorem source_asym_inv_image:
  !relation function.
    source_asym relation ==>
    source_asym (relation$inv_image relation function)
Proof
  simp[source_asym_def, relationTheory.inv_image_def]
QED

Theorem source_asym_less_than:
  source_asym (($<) : num -> num -> bool)
Proof
  simp[source_asym_def]
QED

Theorem source_asym_lex:
  !relation.
    source_asym relation ==> source_asym (source_lex relation)
Proof
  simp[source_asym_def, source_lex_def]
  >> gen_tac
  >> strip_tac
  >> Induct_on `left`
  >> Cases_on `right`
  >> simp[listTheory.LLEX_THM]
  >> metis_tac[]
QED

Theorem source_asym_lex_prod:
  !left right.
    source_asym left ==> source_asym right ==>
    source_asym (pair$LEX left right)
Proof
  simp[source_asym_def, pairTheory.FORALL_PROD, pairTheory.LEX_DEF_THM]
  >> metis_tac[]
QED

Theorem source_asym_lenlex:
  !relation.
    source_asym relation ==>
    source_asym (source_lenlex relation)
Proof
  rpt strip_tac
  >> simp[source_lenlex_def]
  >> irule source_asym_inv_image
  >> irule source_asym_lex_prod
  >> simp[source_asym_less_than, source_asym_lex]
QED

(* Isabelle/HOL src/HOL/List.thy:7385.  Unconditional: reflexivity of
   [relation] somewhere in the prefix is a disjunct, not a premise.  The
   form that assumes irreflexivity is the corpus goal at line 7387. *)
Theorem source_lexord_same_prefix_iff:
  !relation prefix xs ys.
    (source_lexord relation (prefix ++ xs) (prefix ++ ys) <=>
     (?item. MEM item prefix /\ relation item item) \/
     source_lexord relation xs ys)
Proof
  simp[source_lexord_def]
  >> gen_tac
  >> Induct
  >> rw[listTheory.LLEX_def]
  >> metis_tac[]
QED

(* Isabelle/HOL src/HOL/List.thy:7474.  Pointwise: no list is below
   itself when no element is.  That [source_lexord] preserves
   irreflexivity is the corpus goal at line 7537. *)
Theorem source_lexord_irreflexive:
  !relation xs.
    (!x. ~relation x x) ==> ~source_lexord relation xs xs
Proof
  simp[source_lexord_def]
  >> gen_tac
  >> Induct
  >> rw[listTheory.LLEX_def]
  >> metis_tac[]
QED

(* Isabelle/HOL src/HOL/List.thy:7713.  The source composes: a list of
   measure functions is read off a value and the readings are compared
   by [lex less_than], so what settles the well-foundedness of
   [measures] is the ambient [wf_inv_image], [wf_lex] and
   [wf_less_than], each stated about one of the three constants. *)
Definition source_measures_def:
  source_measures (functions : ('a -> num) list) =
    relation$inv_image (source_lex (($<) : num -> num -> bool))
      (\value. MAP (\function. function value) functions)
End

(* Isabelle/HOL src/HOL/List.thy:7719 [in_measures], declared simp:
   the recursion clauses are a consequence of the composite and not
   the definition. *)
Theorem source_in_measures:
  (!left right. ~source_measures [] left right) /\
  (!function functions left right.
     source_measures (function::functions) left right <=>
     function left < function right \/
     (function left = function right /\
      source_measures functions left right))
Proof
  simp[source_measures_def, relationTheory.inv_image_def,
       source_lex_def, listTheory.LLEX_THM]
  >> metis_tac[]
QED

Theorem source_measures_WF:
  !functions. relation$WF (source_measures functions)
Proof
  simp[source_measures_def]
  >> rpt strip_tac
  >> irule relationTheory.WF_inv_image
  >> irule source_wf_lex
  >> simp[prim_recTheory.WF_LESS]
QED

(* Isabelle/HOL src/HOL/List.thy:7954-8275. *)
Definition source_rel_image_def:
  source_rel_image relation domain =
    {right | ?left. left IN domain /\ relation left right}
End

(* Isabelle/HOL src/HOL/Relation.thy:1572 [Image_singleton_iff],
   declared [iff]: the simpset takes a relational image of a singleton
   apart without being told, though [Image] itself stays folded. *)
Theorem source_rel_image_singleton:
  !relation left right.
    right IN source_rel_image relation {left} <=> relation left right
Proof
  simp[source_rel_image_def]
QED

Definition source_set_Cons_def:
  source_set_Cons heads tails =
    {result |
       ?head tail.
         head IN heads /\ tail IN tails /\ result = head::tail}
End

Definition source_superset_def:
  source_superset xs ys <=>
    LIST_TO_SET ys SUBSET LIST_TO_SET xs
End

Theorem source_listrel1_subset_LIST_REL:
  !left_relation right_relation xs ys.
    (!left right.
       left_relation left right ==> right_relation left right) ==>
    relation$reflexive right_relation ==>
    source_listrel1 left_relation xs ys ==>
    LIST_REL right_relation xs ys
Proof
  rpt strip_tac
  >> fs[source_listrel1_def]
  >> irule listTheory.LIST_REL_APPEND_suff
  >> conj_tac
  >- (irule listTheory.LIST_REL_APPEND_suff
      >> conj_tac
      >- (irule listTheory.LIST_REL_refl
          >> fs[relationTheory.reflexive_def])
      >> simp[])
  >> irule listTheory.LIST_REL_refl
  >> fs[relationTheory.reflexive_def]
QED

(* Isabelle/HOL src/HOL/Relation.thy, [refl_on_def].  It carries no
   range condition; [equiv] states [r SUBSET A * A] as a conjunct of
   its own. *)
Definition source_refl_on_def:
  source_refl_on domain relation <=>
    !value. value IN domain ==> relation value value
End

(* Isabelle/HOL src/HOL/Relation.thy:456, [sym_def].  Isabelle states
   symmetry as an implication where HOL4's [symmetric_def] states it as
   an equivalence.  The two predicates agree, but a method that rewrites
   with the equivalence gets a goal whose two sides are one statement
   under two spellings, and no simplifier reads one side of an
   equivalence as context for the other; an implication hands its
   antecedent to its consequent, which both do.  So the citation is
   rendered as the source states it rather than as HOL4 defines the
   predicate. *)
Theorem source_sym_def:
  !relation.
    relation$symmetric relation <=>
    !left right. relation left right ==> relation right left
Proof
  simp[relationTheory.symmetric_def]
  >> metis_tac[]
QED

(* Isabelle/HOL src/HOL/Equiv_Relations.thy, [equiv_def]. *)
Definition source_equiv_def:
  source_equiv domain relation <=>
    (!left right.
       relation left right ==>
       left IN domain /\ right IN domain) /\
    source_refl_on domain relation /\
    relation$symmetric relation /\
    relation$transitive relation
End

Definition source_lists_def:
  source_lists domain =
    {xs | EVERY (\value. value IN domain) xs}
End

(* Isabelle introduces [lists] as an inductive set and declares what its
   simpset and claset carry about it separately from the definition,
   which stays folded: the clauses below are those declarations, stated
   over the translation's encoding. *)

(* src/HOL/List.thy:6861, [lists.Nil], declared [intro!, simp]. *)
Theorem source_lists_Nil:
  !domain. [] IN source_lists domain
Proof
  simp[source_lists_def]
QED

(* src/HOL/List.thy:6892, [Cons_in_lists_iff], declared [simp]; its two
   halves are src/HOL/List.thy:6862 [lists.Cons], declared [intro!], and
   src/HOL/List.thy:6864 [listsE], declared [elim!]. *)
Theorem source_Cons_in_lists_iff:
  !item items domain.
    item::items IN source_lists domain <=>
    item IN domain /\ items IN source_lists domain
Proof
  simp[source_lists_def] >> metis_tac[]
QED

(* src/HOL/List.thy:6898, [append_in_lists_conv], declared [iff]. *)
Theorem source_append_in_lists_conv:
  !left right domain.
    left ++ right IN source_lists domain <=>
    left IN source_lists domain /\ right IN source_lists domain
Proof
  simp[source_lists_def] >> metis_tac[]
QED

(* src/HOL/List.thy:6909, [in_listsD], declared [dest!]. *)
Theorem source_in_listsD:
  !domain items.
    items IN source_lists domain ==>
    !item. MEM item items ==> item IN domain
Proof
  simp[source_lists_def, listTheory.EVERY_MEM]
QED

(* src/HOL/List.thy:6914, [in_listsI], declared [intro!]. *)
Theorem source_in_listsI:
  !domain items.
    (!item. MEM item items ==> item IN domain) ==>
    items IN source_lists domain
Proof
  simp[source_lists_def, listTheory.EVERY_MEM]
QED

(* src/HOL/List.thy:6890, [lists_Int_eq], declared [simp]. *)
Theorem source_lists_Int_eq:
  !left right.
    source_lists (left INTER right) =
    source_lists left INTER source_lists right
Proof
  simp[source_lists_def, pred_setTheory.EXTENSION,
       listTheory.EVERY_MEM]
  >> metis_tac[]
QED

(* src/HOL/List.thy:6922, [lists_empty], declared [simp]. *)
Theorem source_lists_empty:
  source_lists {} = {[]}
Proof
  simp[source_lists_def, pred_setTheory.EXTENSION]
  >> Cases
  >> simp[]
  >> metis_tac[]
QED

(* src/HOL/List.thy:6925, [lists_UNIV], declared [simp]. *)
Theorem source_lists_UNIV:
  source_lists UNIV = UNIV
Proof
  simp[source_lists_def, pred_setTheory.EXTENSION]
QED

Theorem source_mono_lists:
  !left right.
    left SUBSET right ==>
    source_lists left SUBSET source_lists right
Proof
  simp[source_lists_def, pred_setTheory.SUBSET_DEF,
       listTheory.EVERY_MEM]
  >> metis_tac[]
QED

(* Isabelle/HOL src/HOL/List.thy:7831, "Accessible part and
   wellfoundedness".  [Wellfounded.acc] is [relationTheory.WFP]: both
   read as "every predecessor is accessible", and both are what their
   library's well-foundedness characterisation -- Isabelle's
   [wf_iff_acc], HOL4's [WF_EQ_WFP] -- turns a well-foundedness
   statement into.  The three results below are stated in the source
   over its [lists] set, and the pointwise [source_lists] is that set. *)

(* src/HOL/List.thy:7834 [Cons_acc_listrel1I], declared [intro!]. *)
Theorem source_Cons_acc_listrel1I:
  !relation item items.
    relation$WFP relation item ==>
    relation$WFP (source_listrel1 relation) items ==>
    relation$WFP (source_listrel1 relation) (item::items)
Proof
  gen_tac
  >> `!item.
        relation$WFP relation item ==>
        !items.
          relation$WFP (source_listrel1 relation) items ==>
          relation$WFP (source_listrel1 relation) (item::items)`
       suffices_by metis_tac[]
  >> ho_match_mp_tac relationTheory.WFP_INDUCT
  >> rpt strip_tac
  >> qpat_x_assum `relation$WFP (source_listrel1 relation) items` mp_tac
  >> qid_spec_tac `items`
  >> ho_match_mp_tac relationTheory.WFP_STRONG_INDUCT
  >> rpt strip_tac
  >> irule relationTheory.WFP_RULES
  >> rpt strip_tac
  >> rename1 `source_listrel1 relation candidate (item::_)`
  >> Cases_on `candidate`
  >> fs[source_not_Nil_listrel1, source_Cons_listrel1_Cons]
  >> metis_tac[]
QED

(* src/HOL/List.thy:7846 [lists_accD], attributed to no set. *)
Theorem source_lists_accD:
  !relation items.
    items IN source_lists {value | relation$WFP relation value} ==>
    relation$WFP (source_listrel1 relation) items
Proof
  gen_tac
  >> Induct
  >- (strip_tac
      >> irule relationTheory.WFP_RULES
      >> simp[source_not_listrel1_Nil])
  >> rpt strip_tac
  >> fs[source_Cons_in_lists_iff]
  >> irule source_Cons_acc_listrel1I
  >> fs[]
QED

(* src/HOL/List.thy:7857 [lists_accI], attributed to no set.  A
   predecessor of a list under [listrel1] is that list with one member
   replaced by something the relation puts below it, so the induction
   hypothesis reaches every member. *)
Theorem source_lists_accI_lists:
  !relation items.
    relation$WFP (source_listrel1 relation) items ==>
    items IN source_lists {value | relation$WFP relation value}
Proof
  gen_tac
  >> ho_match_mp_tac relationTheory.WFP_INDUCT
  >> rpt strip_tac
  >> simp[source_lists_def, listTheory.EVERY_MEM]
  >> rpt strip_tac
  >> irule relationTheory.WFP_RULES
  >> rpt strip_tac
  >> rename1 `relation lower element`
  >> rename1 `MEM element collection`
  >> `?prefix suffix. collection = prefix ++ element::suffix`
       by metis_tac[listTheory.MEM_SPLIT]
  >> `source_listrel1 relation (prefix ++ lower::suffix) collection`
       by (simp[source_listrel1_def] >> metis_tac[])
  >> first_x_assum drule
  >> simp[source_lists_def, listTheory.EVERY_MEM]
  >> disch_then (qspec_then `lower` mp_tac)
  >> simp[]
QED

(* [lists_accI] resolved through :6892 [Cons_in_lists_iff], which is
   how src/HOL/List.thy:7866 [wf_listrel1_iff] cites it: read at a cons,
   it says the head of an accessible list is itself accessible. *)
Theorem source_lists_accI:
  !relation item items.
    relation$WFP (source_listrel1 relation) (item::items) ==>
    relation$WFP relation item
Proof
  rpt strip_tac
  >> drule source_lists_accI_lists
  >> simp[source_Cons_in_lists_iff]
QED

(* Isabelle states this as [listrel r <= lists A <*> lists A], and the
   pointwise rendering of that conclusion is membership: the applied form
   [source_lists carrier xs] is the same term through [IN_DEF] but is not
   the one [source_equiv_def] and [source_LIST_REL_refl_on] spell, so no
   goal stated in this theory's own vocabulary ever met it. *)
Theorem source_LIST_REL_in_lists:
  !carrier relation xs ys.
    (!left right.
       relation left right ==>
       left IN carrier /\ right IN carrier) ==>
    LIST_REL relation xs ys ==>
    xs IN source_lists carrier /\ ys IN source_lists carrier
Proof
  simp[source_lists_def, listTheory.LIST_REL_EL_EQN,
       listTheory.EVERY_EL]
  >> metis_tac[]
QED

Theorem source_LIST_REL_refl_on:
  !carrier relation xs.
    (!value. value IN carrier ==> relation value value) ==>
    xs IN source_lists carrier ==>
    LIST_REL relation xs xs
Proof
  rpt gen_tac
  >> strip_tac
  >> Induct_on `xs`
  >> simp[source_lists_def]
QED

Theorem source_LIST_REL_refl_on_preserve:
  !carrier relation.
    source_refl_on carrier relation ==>
    source_refl_on (source_lists carrier) (LIST_REL relation)
Proof
  simp[source_refl_on_def]
  >> rpt strip_tac
  >> irule source_LIST_REL_refl_on
  >> qexists_tac `carrier`
  >> fs[source_lists_def]
QED

(* Isabelle cites [listrel_refl_on] at [UNIV] with its premise already
   discharged by [refl_rtrancl].  An instance reached that way is its
   own citation, so it is stated as its own theorem rather than left to
   be recombined: the carrier the instantiation fixes occurs in neither
   side of the conclusion, so nothing in a goal determines it. *)
Theorem source_LIST_REL_rtrancl_refl_on:
  !relation.
    source_refl_on (source_lists UNIV)
      (LIST_REL (relation$RTC relation))
Proof
  gen_tac
  >> irule source_LIST_REL_refl_on_preserve
  >> simp[source_refl_on_def, relationTheory.RTC_REFL]
QED

Theorem source_LIST_REL_symmetric:
  !relation.
    relation$symmetric relation ==>
    relation$symmetric (LIST_REL relation)
Proof
  simp[relationTheory.symmetric_def]
  >> metis_tac[listTheory.LIST_REL_sym]
QED

Theorem source_LIST_REL_transitive:
  !relation.
    relation$transitive relation ==>
    relation$transitive (LIST_REL relation)
Proof
  simp[relationTheory.transitive_def]
  >> metis_tac[listTheory.LIST_REL_trans_same]
QED

Theorem source_every_zip_nth:
  !relation xs ys.
    LENGTH xs = LENGTH ys ==>
    (EVERY (UNCURRY relation) (ZIP (xs,ys)) <=>
     !index.
       index < LENGTH xs ==>
       relation (EL index xs) (EL index ys))
Proof
  rpt gen_tac
  >> strip_tac
  >> rw[listTheory.EVERY_EL]
  >> eq_tac
  >- (rpt strip_tac
      >> first_x_assum (qspec_then `index` mp_tac)
      >> impl_tac
      >- metis_tac[listTheory.LENGTH_ZIP]
      >> simp[listTheory.EL_ZIP])
  >> rpt strip_tac
  >> first_x_assum (qspec_then `n` mp_tac)
  >> impl_tac
  >- metis_tac[listTheory.LENGTH_ZIP]
  >> simp[listTheory.EL_ZIP]
QED

Theorem source_every_zip_nth_conj:
  !relation xs ys.
    (LENGTH xs = LENGTH ys /\
     EVERY (UNCURRY relation) (ZIP (xs,ys)) <=>
     LENGTH xs = LENGTH ys /\
     !index.
       index < LENGTH xs ==>
       relation (EL index xs) (EL index ys))
Proof
  metis_tac[source_every_zip_nth]
QED

Theorem source_equiv_LIST_REL:
  !carrier relation.
    source_equiv carrier relation ==>
    source_equiv (source_lists carrier) (LIST_REL relation)
Proof
  rpt gen_tac
  >> strip_tac
  >> fs[source_equiv_def, source_refl_on_def]
  >> rw[source_equiv_def, source_refl_on_def]
  >- (qspecl_then [`carrier`, `relation`, `left`, `right`]
        mp_tac source_LIST_REL_in_lists
      >> simp[source_lists_def]
      >> metis_tac[])
  >- (qspecl_then [`carrier`, `relation`, `left`, `right`]
        mp_tac source_LIST_REL_in_lists
      >> simp[source_lists_def]
      >> metis_tac[])
  >- (irule
        (Q.SPECL [`carrier`, `relation`, `value`]
           source_LIST_REL_refl_on)
      >> qexists_tac `carrier`
      >> fs[source_lists_def])
  >- (fs[relationTheory.symmetric_def]
      >> rw[relationTheory.symmetric_def]
      >> eq_tac
      >> metis_tac[listTheory.LIST_REL_sym])
  >> fs[relationTheory.transitive_def]
  >> rw[relationTheory.transitive_def]
  >> irule listTheory.LIST_REL_trans_same
  >> metis_tac[]
QED

(* Isabelle/HOL src/HOL/List.thy:8999-9003. *)
Theorem source_set_Cons_transfer:
  !relation.
    (list$SET_REL relation ===>
      list$SET_REL (LIST_REL relation) ===>
      list$SET_REL (LIST_REL relation))
      source_set_Cons source_set_Cons
Proof
  simp[transferTheory.FUN_REL_def, listTheory.SET_REL_THM,
       source_set_Cons_def]
  >> rpt strip_tac
  >> metis_tac[listTheory.LIST_REL_CONS1]
QED

(* Isabelle/HOL src/HOL/List.thy:8709-8711. *)
Theorem source_finite_wf_acyclic:
  !pairs : ('a # 'a) set.
    FINITE pairs ==>
    (relation$WF (set_relation$reln_to_rel pairs) <=>
     set_relation$acyclic pairs)
Proof
  rpt strip_tac
  >> eq_tac
  >- metis_tac[set_relationTheory.WF_acyclic]
  >> strip_tac
  >> irule set_relationTheory.acyclic_WF
  >> conj_tac
  >- simp[]
  >> qexists_tac `IMAGE FST pairs UNION IMAGE SND pairs`
  >> simp[set_relationTheory.domain_def,
          set_relationTheory.range_def,
          pred_setTheory.SUBSET_DEF]
  >> conj_tac
  >- (rpt strip_tac
      >> disj1_tac
      >> qexists_tac `(x,y)`
      >> simp[])
  >> rpt strip_tac
  >> disj2_tac
  >> qexists_tac `(x',x)`
  >> simp[]
QED

Theorem source_wf_list_set:
  !pairs.
    relation$WF
      (set_relation$reln_to_rel (LIST_TO_SET pairs)) <=>
    set_relation$acyclic (LIST_TO_SET pairs)
Proof
  gen_tac
  >> eq_tac
  >- metis_tac[set_relationTheory.WF_acyclic]
  >> strip_tac
  >> irule set_relationTheory.acyclic_WF
  >> conj_tac
  >- simp[]
  >> qexists_tac
       `IMAGE FST (LIST_TO_SET pairs) UNION
        IMAGE SND (LIST_TO_SET pairs)`
  >> simp[set_relationTheory.domain_def,
          set_relationTheory.range_def,
          pred_setTheory.SUBSET_DEF]
  >> conj_tac
  >- (rpt strip_tac
      >> disj1_tac
      >> qexists_tac `(x,y)`
      >> simp[])
  >> rpt strip_tac
  >> disj2_tac
  >> qexists_tac `(x',x)`
  >> simp[]
QED

(* Isabelle/HOL src/HOL/List.thy:7052-7055. *)
Definition source_trans_list_step_def:
  source_trans_list_step pairs =
    FLAT
      (MAP
        (\left.
           MAP (\right. (FST left, SND right))
             (FILTER (\right. SND left = FST right) pairs))
        pairs)
End

Theorem source_trans_list_step_member:
  !pairs left right.
    MEM (left,right) (source_trans_list_step pairs) ==>
    ?middle. MEM (left,middle) pairs /\ MEM (middle,right) pairs
Proof
  simp[source_trans_list_step_def, listTheory.MEM_FLAT,
       listTheory.MEM_MAP, listTheory.MEM_FILTER, PULL_EXISTS]
  >> rpt strip_tac
  >> qexists_tac `SND left'`
  >> Cases_on `left'`
  >> Cases_on `right'`
  >> fs[]
QED

Theorem source_tc_two_step:
  !pairs left middle right.
    MEM (left,middle) pairs ==>
    MEM (middle,right) pairs ==>
    (left,right) IN
      set_relation$transitive_closure (LIST_TO_SET pairs)
Proof
  metis_tac[set_relationTheory.tc_rules]
QED

Theorem source_trans_list_step_subset_tc:
  !pairs.
    LIST_TO_SET (source_trans_list_step pairs) SUBSET
    set_relation$transitive_closure (LIST_TO_SET pairs)
Proof
  simp[source_trans_list_step_def, pred_setTheory.SUBSET_DEF,
       listTheory.MEM_FLAT, listTheory.MEM_MAP,
       listTheory.MEM_FILTER, PULL_EXISTS]
  >> rpt strip_tac
  >> Cases_on `left`
  >> Cases_on `right`
  >> fs[]
  >> metis_tac[set_relationTheory.tc_rules]
QED

(* Isabelle/HOL src/HOL/List.thy:313-318.  The source introduces
   [shuffles] by a [function] and proves its termination in the same
   block, so these three equations are what its simpset carries. *)
Definition source_shuffles_def:
  (source_shuffles [] ys = {ys}) /\
  (source_shuffles (left::xs) [] = {left::xs}) /\
  (source_shuffles (left::xs) (right::ys) =
     IMAGE (CONS left) (source_shuffles xs (right::ys)) UNION
     IMAGE (CONS right) (source_shuffles (left::xs) ys))
Termination
  WF_REL_TAC `measure (\(xs,ys). LENGTH xs + LENGTH ys)`
  >> simp[]
End

(* src/HOL/List.thy:315, the second of those equations.  The source
   states it at a list variable, and HOL4 takes the rows apart to make
   them disjoint, so the equation it keeps is the cons case and the
   variable case is a consequence. *)
Theorem source_shuffles_nil_right:
  !xs. source_shuffles xs [] = {xs}
Proof
  Cases >> simp[source_shuffles_def]
QED

(* Isabelle/HOL src/HOL/List.thy:5415-5480. *)
Definition source_subseqs_def:
  (source_subseqs ([] : 'a list) = [[]]) /\
  (source_subseqs (head::tail) =
     source_subseqs tail ++
     MAP (CONS head) (source_subseqs tail))
End

Theorem source_subseqs_member_subset:
  !xs ys.
    MEM ys (source_subseqs xs) ==>
    LIST_TO_SET ys SUBSET LIST_TO_SET xs
Proof
  Induct
  >> simp[source_subseqs_def, pred_setTheory.SUBSET_DEF,
          listTheory.MEM_MAP]
  >> rpt strip_tac
  >> Cases_on `ys`
  >> fs[]
  >> first_x_assum drule
  >> simp[pred_setTheory.SUBSET_DEF]
  >> metis_tac[]
QED

Theorem source_subset_subseqs:
  !xs subset.
    subset SUBSET LIST_TO_SET xs ==>
    subset IN IMAGE LIST_TO_SET (LIST_TO_SET (source_subseqs xs))
Proof
  Induct
  >- simp[source_subseqs_def, pred_setTheory.SUBSET_EMPTY]
  >> rpt strip_tac
  >> Cases_on `h IN subset`
  >- (qpat_x_assum `subset SUBSET LIST_TO_SET (h::xs)`
        mp_tac
      >> simp[pred_setTheory.SUBSET_DEF]
      >> strip_tac
      >> `subset DELETE h SUBSET LIST_TO_SET xs` by
           (rw[pred_setTheory.SUBSET_DEF,
               pred_setTheory.IN_DELETE]
            >> metis_tac[])
      >> qpat_x_assum
           `!candidate. candidate SUBSET LIST_TO_SET xs ==> _`
           (qspec_then `subset DELETE h` mp_tac)
      >> simp[]
      >> strip_tac
      >> qexists_tac `h::x`
      >> simp[source_subseqs_def, listTheory.MEM_MAP,
              pred_setTheory.EXTENSION]
      >> gen_tac
      >> eq_tac
      >> strip_tac
      >> fs[pred_setTheory.EXTENSION,
            pred_setTheory.IN_DELETE]
      >> metis_tac[])
  >> `subset SUBSET LIST_TO_SET xs` by
       (rw[pred_setTheory.SUBSET_DEF]
        >> fs[pred_setTheory.SUBSET_DEF]
        >> metis_tac[])
  >> first_x_assum drule
  >> simp[source_subseqs_def]
  >> metis_tac[]
QED

Theorem source_subseqs_powset:
  !xs.
    IMAGE LIST_TO_SET (LIST_TO_SET (source_subseqs xs)) =
    POW (LIST_TO_SET xs)
Proof
  rw[pred_setTheory.EXTENSION]
  >> eq_tac
  >- (strip_tac
      >> fs[]
      >> rw[pred_setTheory.IN_POW, pred_setTheory.SUBSET_DEF]
      >> metis_tac[source_subseqs_member_subset,
                   pred_setTheory.SUBSET_DEF])
  >> strip_tac
  >> fs[pred_setTheory.IN_POW]
  >> drule source_subset_subseqs
  >> simp[pred_setTheory.IN_IMAGE]
  >> metis_tac[pred_setTheory.EXTENSION]
QED

Theorem source_subseqs_powset_member:
  !xs subset.
    subset IN IMAGE LIST_TO_SET (LIST_TO_SET (source_subseqs xs)) <=>
    subset SUBSET LIST_TO_SET xs
Proof
  metis_tac[source_subseqs_powset, pred_setTheory.IN_POW]
QED

Theorem source_length_subseqs:
  !xs. LENGTH (source_subseqs xs) = 2 EXP LENGTH xs
Proof
  Induct
  >> simp[source_subseqs_def, arithmeticTheory.EXP]
QED

Theorem source_all_distinct_card:
  !xs.
    ALL_DISTINCT xs <=> CARD (LIST_TO_SET xs) = LENGTH xs
Proof
  metis_tac[listTheory.ALL_DISTINCT_CARD_LIST_TO_SET,
            listTheory.CARD_LIST_TO_SET_ALL_DISTINCT]
QED

Theorem source_all_distinct_subseq_sets:
  !xs.
    ALL_DISTINCT xs ==>
    ALL_DISTINCT (MAP LIST_TO_SET (source_subseqs xs))
Proof
  Induct
  >- simp[source_subseqs_def]
  >> simp[source_subseqs_def]
  >> rpt strip_tac
  >> simp[listTheory.ALL_DISTINCT_APPEND]
  >> conj_tac
  >- (`MAP LIST_TO_SET
         (MAP (CONS h) (source_subseqs xs)) =
       MAP (pred_set$INSERT h)
         (MAP LIST_TO_SET (source_subseqs xs))` by
        simp[listTheory.MAP_MAP_o, combinTheory.o_DEF]
      >> pop_assum SUBST1_TAC
      >> irule listTheory.ALL_DISTINCT_MAP_INJ
      >> conj_tac
      >- (rpt strip_tac
          >> fs[listTheory.MEM_MAP]
          >> `h NOTIN x /\ h NOTIN y` by
               metis_tac[source_subseqs_member_subset,
                          pred_setTheory.SUBSET_DEF]
          >> fs[pred_setTheory.EXTENSION]
          >> metis_tac[])
      >> metis_tac[])
  >> simp[listTheory.MEM_MAP]
  >> rpt strip_tac
  >> `h NOTIN LIST_TO_SET y` by
       metis_tac[source_subseqs_member_subset,
                  pred_setTheory.SUBSET_DEF]
  >> fs[pred_setTheory.EXTENSION]
  >> metis_tac[]
QED

Theorem source_upto_split2:
  !i j k. i <= j ==> j <= k ==>
    source_upto i k =
    source_upto i j ++ source_upto (j + 1) k
Proof
  rpt strip_tac
  >> Cases_on `j = k`
  >- (`source_upto (j + 1) k = []` by
        (irule source_upto_empty >> intLib.ARITH_TAC)
      >> fs[])
  >> `i <= j + 1` by intLib.ARITH_TAC
  >> `j + 1 <= k` by intLib.ARITH_TAC
  >> `j + 1 - 1 = j` by intLib.ARITH_TAC
  >> metis_tac[source_upto_split1]
QED

Theorem source_upto_split3:
  !i j k. i <= j ==> j <= k ==>
    source_upto i k =
    source_upto i (j - 1) ++ j :: source_upto (j + 1) k
Proof
  rpt strip_tac
  >> `source_upto i k =
      source_upto i (j - 1) ++ source_upto j k` by
       metis_tac[source_upto_split1]
  >> `source_upto j k = j :: source_upto (j + 1) k` by
       metis_tac[source_upto_rec1]
  >> metis_tac[]
QED

Definition source_upto_aux_def:
  source_upto_aux i j js = source_upto i j ++ js
End

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/Product_Type.thy:135-147.  HOL4 deliberately has no global
   order instance for unit; these operations are the benchmark-local
   interpretation of that source instance. *)
Definition source_unit_le_def:
  source_unit_le (_ : unit) (_ : unit) = T
End

Definition source_unit_lt_def:
  source_unit_lt (_ : unit) (_ : unit) = F
End

Theorem source_unit_le_bridge:
  !u v : unit. source_unit_le u v <=> T
Proof
  simp[source_unit_le_def]
QED

Theorem source_unit_lt_bridge:
  !u v : unit. source_unit_lt u v <=> F
Proof
  simp[source_unit_lt_def]
QED

Theorem source_unit_le_unique:
  !relation : unit -> unit -> bool.
    (!u. relation u u) ==> relation = source_unit_le
Proof
  simp[FUN_EQ_THM, oneTheory.FORALL_ONE, source_unit_le_def]
QED

Theorem source_unit_lt_unique:
  !relation : unit -> unit -> bool.
    (!u. ~relation u u) ==> relation = source_unit_lt
Proof
  simp[FUN_EQ_THM, oneTheory.FORALL_ONE, source_unit_lt_def]
QED

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/Set.thy:456-473 and 967-975.  Isabelle's [=simp=>]
   connective has ordinary implication as its logical content.  Its
   operational congruence role is represented by invocation-local Cong
   recipe arguments, not by an additional Boolean connective. *)
Definition source_ball_def:
  source_ball (set : 'a set) predicate =
    !x. x IN set ==> predicate x
End

Definition source_bex_def:
  source_bex (set : 'a set) predicate =
    ?x. x IN set /\ predicate x
End

Definition source_image_def:
  source_image (function : 'a -> 'b) set = IMAGE function set
End

(* Isabelle/HOL src/HOL/Set.thy:883-884.  Isabelle's image definition
   exposes the bounded-domain premise before the value equality. *)
Theorem source_image_expansion:
  !function set.
    IMAGE function set =
    (\value. ?argument. argument IN set /\ value = function argument)
Proof
  simp[pred_setTheory.EXTENSION, pred_setTheory.IN_IMAGE,
       boolTheory.CONJ_COMM]
QED

Theorem source_ball_bridge:
  !set predicate.
    source_ball set predicate <=>
    !x. x IN set ==> predicate x
Proof
  simp[source_ball_def]
QED

Theorem source_bex_bridge:
  !set predicate.
    source_bex set predicate <=>
    ?x. x IN set /\ predicate x
Proof
  rw[source_bex_def]
  >> metis_tac[]
QED

Theorem source_image_bridge:
  !function set. source_image function set = IMAGE function set
Proof
  simp[source_image_def]
QED

Theorem source_ball_cong_simp:
  !left right predicate predicate'.
    left = right ==>
    (!x. x IN right ==> (predicate x <=> predicate' x)) ==>
    (source_ball left predicate <=> source_ball right predicate')
Proof
  simp[source_ball_def]
QED

Theorem source_bex_cong_simp:
  !left right predicate predicate'.
    left = right ==>
    (!x. x IN right ==> (predicate x <=> predicate' x)) ==>
    (source_bex left predicate <=> source_bex right predicate')
Proof
  rw[source_bex_def]
  >> metis_tac[]
QED

Theorem source_image_cong_simp:
  !left right function function'.
    left = right ==>
    (!x. x IN right ==> function x = function' x) ==>
    source_image function left = source_image function' right
Proof
  rw[source_image_def]
  >> irule pred_setTheory.IMAGE_CONG
  >> simp[]
QED

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/Set.thy:994-995.  The source comm_monoid_add constraint is
   interpreted by HOL4's explicit AbelianMonoid record. *)
Definition source_add_image_def:
  source_add_image (g : 'a monoid) set =
    IMAGE (g.op g.id) set
End

Theorem source_add_image_bridge:
  !g set.
    source_add_image g set =
    IMAGE (g.op g.id) set
Proof
  simp[source_add_image_def]
QED

Theorem source_add_image_preimage:
  !g : 'a monoid.
    Monoid g ==>
    !set. set SUBSET g.carrier ==>
    !x. x IN set ==>
      ?y. x = g.op g.id y /\ y IN set
Proof
  rpt strip_tac
  >> qexists_tac `x`
  >> metis_tac[monoidTheory.monoid_lid,
               pred_setTheory.SUBSET_DEF]
QED

Theorem source_abelian_monoid_is_monoid:
  !g : 'a monoid. AbelianMonoid g ==> Monoid g
Proof
  simp[monoidTheory.AbelianMonoid_def]
QED

Theorem source_image_add_zero:
  !g : 'a monoid.
    AbelianMonoid g ==>
    !set. set SUBSET g.carrier ==>
      source_add_image g set = set
Proof
  rw[source_add_image_def, pred_setTheory.EXTENSION,
     pred_setTheory.IN_IMAGE]
  >> metis_tac[monoidTheory.AbelianMonoid_def,
               monoidTheory.monoid_lid,
               pred_setTheory.SUBSET_DEF]
QED

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/String.thy:24-137 and 366-730.  Isabelle's char is an
   eight-bit datatype.  HOL4's char is the isomorphic subtype of
   naturals below 256, so the source operations stay local to this
   translation boundary. *)
Definition source_bool_num_def:
  source_bool_num bit : num = if bit then 1 else 0
End

Definition source_horner8_def:
  source_horner8 b0 b1 b2 b3 b4 b5 b6 b7 =
    source_bool_num b0 +
    2 * (source_bool_num b1 +
    2 * (source_bool_num b2 +
    2 * (source_bool_num b3 +
    2 * (source_bool_num b4 +
    2 * (source_bool_num b5 +
    2 * (source_bool_num b6 +
    2 * source_bool_num b7))))))
End

Theorem source_horner8_bound:
  !b0 b1 b2 b3 b4 b5 b6 b7.
    source_horner8 b0 b1 b2 b3 b4 b5 b6 b7 < 256
Proof
  rpt Cases
  >> simp[source_horner8_def, source_bool_num_def]
QED

Theorem source_horner7_bound:
  !b0 b1 b2 b3 b4 b5 b6.
    source_horner8 b0 b1 b2 b3 b4 b5 b6 F < 128
Proof
  rpt Cases
  >> simp[source_horner8_def, source_bool_num_def]
QED

Definition source_Char_def:
  source_Char b0 b1 b2 b3 b4 b5 b6 b7 =
    CHR (source_horner8 b0 b1 b2 b3 b4 b5 b6 b7)
End

Theorem source_Char_ascii_bound:
  !b0 b1 b2 b3 b4 b5 b6.
    ORD (source_Char b0 b1 b2 b3 b4 b5 b6 F) < 128
Proof
  rpt Cases
  >> simp[source_Char_def, source_horner8_def,
          source_bool_num_def, stringTheory.ORD_CHR_RWT]
QED

Definition source_of_char_def:
  source_of_char (character : char) = ORD character
End

Definition source_char_of_def:
  source_char_of number = CHR (number MOD 256)
End

Definition source_take_bit_def:
  source_take_bit width number = number MOD (2 ** width)
End

Definition source_ascii_of_def:
  source_ascii_of character = CHR (ORD character MOD 128)
End

Theorem source_of_char_Char:
  !b0 b1 b2 b3 b4 b5 b6 b7.
    source_of_char (source_Char b0 b1 b2 b3 b4 b5 b6 b7) =
    source_horner8 b0 b1 b2 b3 b4 b5 b6 b7
Proof
  simp[source_of_char_def, source_Char_def, source_horner8_bound]
QED

Theorem source_char_roundtrip:
  !character. source_char_of (source_of_char character) = character
Proof
  simp[source_char_of_def, source_of_char_def,
       arithmeticTheory.LESS_MOD, stringTheory.ORD_BOUND]
QED

Theorem source_code_roundtrip:
  !number. source_of_char (source_char_of number) = number MOD 256
Proof
  simp[source_char_of_def, source_of_char_def,
       stringTheory.ORD_CHR_RWT, arithmeticTheory.MOD_LESS]
QED

Theorem source_char_of_take_bit_eq:
  !width number.
    8 <= width ==>
    source_char_of (source_take_bit width number) =
    source_char_of number
Proof
  rw[source_char_of_def, source_take_bit_def]
  >> fs[arithmeticTheory.LESS_EQ_EXISTS]
  >> simp[arithmeticTheory.EXP_ADD, arithmeticTheory.MOD_MULT_MOD]
QED

Theorem source_take_bit_mod_256:
  !width number.
    8 <= width ==>
    source_take_bit width number MOD 256 = number MOD 256
Proof
  rw[source_take_bit_def]
  >> fs[arithmeticTheory.LESS_EQ_EXISTS]
  >> simp[arithmeticTheory.EXP_ADD, arithmeticTheory.MOD_MULT_MOD]
QED

Theorem source_char_of_comp_of_char:
  source_char_of o source_of_char = I
Proof
  simp[FUN_EQ_THM, source_char_roundtrip]
QED

Theorem source_of_char_eqI:
  !left right.
    source_of_char left = source_of_char right ==> left = right
Proof
  simp[source_of_char_def, stringTheory.ORD_11]
QED

Theorem source_char_eq_by_ord:
  !left right : char. ORD left = ORD right ==> left = right
Proof
  simp[stringTheory.ORD_11]
QED

Theorem source_of_char_eq_iff:
  !left right.
    source_of_char left = source_of_char right <=> left = right
Proof
  simp[source_of_char_def, stringTheory.ORD_11]
QED

Theorem source_char_of_eq_iff:
  !number character.
    source_char_of number = character <=>
    source_take_bit 8 number = source_of_char character
Proof
  simp[source_char_of_def, source_take_bit_def, source_of_char_def,
       GSYM stringTheory.ORD_11, stringTheory.ORD_CHR_RWT,
       arithmeticTheory.MOD_LESS]
QED

Definition source_of_nat_def:
  source_of_nat number = number
End

Theorem source_char_of_nat:
  !number.
    source_char_of (source_of_nat number) = source_char_of number
Proof
  simp[source_of_nat_def]
QED

Theorem source_ascii_of_bound:
  !character. ORD (source_ascii_of character) < 128
Proof
  gen_tac
  >> `ORD character MOD 128 < 128`
       by simp[arithmeticTheory.MOD_LESS]
  >> `ORD character MOD 128 < 256` by decide_tac
  >> simp[source_ascii_of_def, stringTheory.ORD_CHR_RWT]
QED

Theorem source_ascii_of_idem:
  !character.
    ORD character < 128 ==> source_ascii_of character = character
Proof
  simp[source_ascii_of_def, arithmeticTheory.LESS_MOD,
       stringTheory.CHR_ORD]
QED

Definition source_literal_valid_def:
  source_literal_valid characters =
    EVERY (\character. ORD character < 128) characters
End

val source_literal_tydef = new_type_definition
  ("source_literal",
   prove(``?characters : char list. source_literal_valid characters``,
         qexists_tac `[]` >> simp[source_literal_valid_def]))

val source_literal_bij = define_new_type_bijections
  {ABS = "source_literal_abs", REP = "source_literal_explode",
   name = "source_literal_bij", tyax = source_literal_tydef}

Theorem source_literal_explode_valid:
  !literal. source_literal_valid (source_literal_explode literal)
Proof
  metis_tac[source_literal_bij]
QED

Theorem source_literal_abs_explode:
  !literal.
    source_literal_abs (source_literal_explode literal) = literal
Proof
  metis_tac[source_literal_bij]
QED

Theorem source_literal_explode_abs:
  !characters.
    source_literal_valid characters ==>
    source_literal_explode (source_literal_abs characters) = characters
Proof
  metis_tac[source_literal_bij]
QED

Theorem source_literal_abs_11:
  !left right.
    source_literal_valid left /\ source_literal_valid right ==>
    (source_literal_abs left = source_literal_abs right <=> left = right)
Proof
  metis_tac[source_literal_bij]
QED

Theorem source_literal_explode_11:
  !left right.
    (source_literal_explode left = source_literal_explode right <=>
     left = right)
Proof
  metis_tac[source_literal_bij]
QED

Theorem source_literal_eq_iff_explode:
  !left right.
    (left = right <=>
     source_literal_explode left = source_literal_explode right)
Proof
  simp[source_literal_explode_11]
QED

Definition source_literal_implode_def:
  source_literal_implode characters =
    source_literal_abs (MAP source_ascii_of characters)
End

Theorem source_literal_implode_valid:
  !characters.
    source_literal_valid (MAP source_ascii_of characters)
Proof
  simp[source_literal_valid_def, listTheory.EVERY_MAP,
       source_ascii_of_bound]
QED

Theorem source_ascii_map_id:
  !characters.
    source_literal_valid characters ==>
    MAP source_ascii_of characters = characters
Proof
  Induct_on `characters`
  >> simp[source_literal_valid_def, source_ascii_of_idem]
QED

Theorem source_literal_implode_explode:
  !literal.
    source_literal_implode (source_literal_explode literal) = literal
Proof
  rw[source_literal_implode_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `source_literal_abs (source_literal_explode literal)`
  >> conj_tac
  >- simp[source_ascii_map_id, source_literal_explode_valid]
  >> simp[source_literal_abs_explode]
QED

Theorem source_literal_explode_implode:
  !characters.
    source_literal_explode (source_literal_implode characters) =
    MAP source_ascii_of characters
Proof
  simp[source_literal_implode_def, source_literal_explode_abs,
       source_literal_implode_valid]
QED

Definition source_literal_empty_def:
  source_literal_empty = source_literal_abs []
End

Definition source_Literal_def:
  source_Literal b0 b1 b2 b3 b4 b5 b6 literal =
    source_literal_abs
      (source_Char b0 b1 b2 b3 b4 b5 b6 F ::
       source_literal_explode literal)
End

Theorem source_Literal_valid:
  !b0 b1 b2 b3 b4 b5 b6 literal.
    source_literal_valid
      (source_Char b0 b1 b2 b3 b4 b5 b6 F ::
       source_literal_explode literal)
Proof
  rpt gen_tac
  >> rw[source_literal_valid_def]
  >- simp[source_Char_ascii_bound]
  >> mp_tac (SPEC ``literal : source_literal``
       source_literal_explode_valid)
  >> simp[source_literal_valid_def]
QED

Theorem source_Char_ascii_bits:
  !b0 b1 b2 b3 b4 b5 b6.
    (BIT 0 (ORD (source_Char b0 b1 b2 b3 b4 b5 b6 F)) = b0) /\
    (BIT 1 (ORD (source_Char b0 b1 b2 b3 b4 b5 b6 F)) = b1) /\
    (BIT 2 (ORD (source_Char b0 b1 b2 b3 b4 b5 b6 F)) = b2) /\
    (BIT 3 (ORD (source_Char b0 b1 b2 b3 b4 b5 b6 F)) = b3) /\
    (BIT 4 (ORD (source_Char b0 b1 b2 b3 b4 b5 b6 F)) = b4) /\
    (BIT 5 (ORD (source_Char b0 b1 b2 b3 b4 b5 b6 F)) = b5) /\
    (BIT 6 (ORD (source_Char b0 b1 b2 b3 b4 b5 b6 F)) = b6)
Proof
  rpt Cases
  >> simp[source_Char_def, source_horner8_def,
          source_bool_num_def, stringTheory.ORD_CHR_RWT,
          bitTheory.BIT_def, bitTheory.BITS_THM]
QED

Theorem source_Char_ascii_eq_iff:
  !b0 b1 b2 b3 b4 b5 b6 c0 c1 c2 c3 c4 c5 c6.
    (source_Char b0 b1 b2 b3 b4 b5 b6 F =
     source_Char c0 c1 c2 c3 c4 c5 c6 F) <=>
    (b0 = c0) /\ (b1 = c1) /\ (b2 = c2) /\ (b3 = c3) /\
    (b4 = c4) /\ (b5 = c5) /\ (b6 = c6)
Proof
  rpt gen_tac
  >> eq_tac
  >- (strip_tac
      >> qspecl_then
           [`b0`, `b1`, `b2`, `b3`, `b4`, `b5`, `b6`]
           strip_assume_tac source_Char_ascii_bits
      >> qspecl_then
           [`c0`, `c1`, `c2`, `c3`, `c4`, `c5`, `c6`]
           strip_assume_tac source_Char_ascii_bits
      >> fs[]
      >> metis_tac[])
  >> simp[]
QED

Theorem source_Literal_eq_iff:
  !b0 b1 b2 b3 b4 b5 b6 s c0 c1 c2 c3 c4 c5 c6 t.
    (source_Literal b0 b1 b2 b3 b4 b5 b6 s =
     source_Literal c0 c1 c2 c3 c4 c5 c6 t) <=>
    (b0 = c0) /\ (b1 = c1) /\ (b2 = c2) /\ (b3 = c3) /\
    (b4 = c4) /\ (b5 = c5) /\ (b6 = c6) /\ (s = t)
Proof
  simp[source_Literal_def, source_literal_abs_11,
       source_Literal_valid, source_Char_ascii_eq_iff,
       source_literal_explode_11, boolTheory.CONJ_ASSOC]
QED

Theorem source_literal_empty_neq_Literal:
  !b0 b1 b2 b3 b4 b5 b6 literal.
    source_literal_empty <>
    source_Literal b0 b1 b2 b3 b4 b5 b6 literal
Proof
  rpt gen_tac
  >> strip_tac
  >> first_x_assum (mp_tac o AP_TERM ``source_literal_explode``)
  >> simp[source_literal_empty_def, source_Literal_def,
          source_literal_explode_abs, source_Literal_valid,
          source_literal_valid_def]
QED

Theorem source_Literal_neq_empty:
  !b0 b1 b2 b3 b4 b5 b6 literal.
    source_Literal b0 b1 b2 b3 b4 b5 b6 literal <>
    source_literal_empty
Proof
  metis_tac[source_literal_empty_neq_Literal]
QED

Definition source_Literal_prime_def:
  source_Literal_prime = source_Literal
End

Theorem source_Literal_code_computation_unfold:
  source_Literal = source_Literal_prime
Proof
  simp[source_Literal_prime_def]
QED

Definition source_literal_append_def:
  source_literal_append left right =
    source_literal_abs
      (source_literal_explode left ++ source_literal_explode right)
End

Theorem source_literal_append_valid:
  !left right.
    source_literal_valid
      (source_literal_explode left ++ source_literal_explode right)
Proof
  rw[source_literal_valid_def]
  >> metis_tac[source_literal_explode_valid,
               source_literal_valid_def]
QED

Theorem source_literal_explode_append:
  !left right.
    source_literal_explode (source_literal_append left right) =
    source_literal_explode left ++ source_literal_explode right
Proof
  simp[source_literal_append_def, source_literal_explode_abs,
       source_literal_append_valid]
QED

(* The source code-generator integer is represented by HOL4's signed
   integers.  Euclidean division by two exposes one low bit at a time,
   including for negative inputs. *)
Definition source_bit_cut_integer_def:
  source_bit_cut_integer (number : int) =
    (number / 2, number % 2 = 1)
End

Definition source_char_of_integer_def:
  source_char_of_integer (number : int) =
    CHR (Num (number % 256))
End

Definition source_integer_of_char_def:
  source_integer_of_char character = &(ORD character)
End

Theorem source_integer_byte_bounds:
  !number : int.
    Num (number % 256) < 256
Proof
  gen_tac
  >> `0 <= number % 256 /\ number % 256 < (256 : int)`
       by (mp_tac (Q.SPECL [`number`, `256`]
             integerTheory.INT_MOD_BOUNDS)
           >> simp[])
  >> `Num (number % 256) < Num (&(256 : num))`
       by simp[integerTheory.NUM_LT]
  >> fs[integerTheory.NUM_OF_INT]
QED

Theorem source_integer_low_bit:
  !number : int.
    &source_bool_num (number % 2 = 1) = number % 2
Proof
  gen_tac
  >> `0 <= number % 2 /\ number % 2 < (2 : int)`
       by (mp_tac (Q.SPECL [`number`, `2`]
             integerTheory.INT_MOD_BOUNDS)
           >> simp[])
  >> `number % 2 = 0 \/ number % 2 = 1`
       by intLib.COOPER_TAC
  >> fs[source_bool_num_def]
QED

Theorem source_integer_division_two:
  !number : int.
    number = (number / 2) * 2 + number % 2 /\
    0 <= number % 2 /\ number % 2 < 2
Proof
  gen_tac
  >> mp_tac (Q.SPEC `2` integerTheory.INT_DIVISION)
  >> simp[]
QED

Theorem source_integer_remainder_two_bounds:
  !number : int. 0 <= number % 2 /\ number % 2 < 2
Proof
  simp[source_integer_division_two]
QED

Definition source_int_horner8_def:
  source_int_horner8 r0 r1 r2 r3 r4 r5 r6 r7 =
    r0 + 2 * (r1 + 2 * (r2 + 2 * (r3 + 2 *
      (r4 + 2 * (r5 + 2 * (r6 + 2 * r7))))))
End

Theorem source_horner8_int:
  !b0 b1 b2 b3 b4 b5 b6 b7.
    &source_horner8 b0 b1 b2 b3 b4 b5 b6 b7 =
    source_int_horner8
      (&source_bool_num b0) (&source_bool_num b1)
      (&source_bool_num b2) (&source_bool_num b3)
      (&source_bool_num b4) (&source_bool_num b5)
      (&source_bool_num b6) (&source_bool_num b7)
Proof
  rpt Cases
  >> simp[source_horner8_def, source_int_horner8_def,
          source_bool_num_def]
QED

Theorem source_int_horner8_bounds:
  !r0 r1 r2 r3 r4 r5 r6 r7 : int.
    0 <= r0 /\ r0 < 2 ==>
    0 <= r1 /\ r1 < 2 ==>
    0 <= r2 /\ r2 < 2 ==>
    0 <= r3 /\ r3 < 2 ==>
    0 <= r4 /\ r4 < 2 ==>
    0 <= r5 /\ r5 < 2 ==>
    0 <= r6 /\ r6 < 2 ==>
    0 <= r7 /\ r7 < 2 ==>
    0 <= source_int_horner8 r0 r1 r2 r3 r4 r5 r6 r7 /\
    source_int_horner8 r0 r1 r2 r3 r4 r5 r6 r7 < 256
Proof
  rpt strip_tac
  >> simp[source_int_horner8_def]
  >> intLib.COOPER_TAC
QED

Theorem source_integer_eight_step:
  !number q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 : int.
    number = q1 * 2 + r0 ==>
    q1 = q2 * 2 + r1 ==>
    q2 = q3 * 2 + r2 ==>
    q3 = q4 * 2 + r3 ==>
    q4 = q5 * 2 + r4 ==>
    q5 = q6 * 2 + r5 ==>
    q6 = q7 * 2 + r6 ==>
    q7 = q8 * 2 + r7 ==>
    number = q8 * 256 +
      source_int_horner8 r0 r1 r2 r3 r4 r5 r6 r7
Proof
  rpt strip_tac
  >> fs[]
  >> simp[source_int_horner8_def]
  >> intLib.INT_RING_TAC
QED

Theorem source_integer_eight_bit_expansion:
  !number : int.
    number =
    (number / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2) * 256 +
    source_int_horner8
      (number % 2) ((number / 2) % 2)
      ((number / 2 / 2) % 2) ((number / 2 / 2 / 2) % 2)
      ((number / 2 / 2 / 2 / 2) % 2)
      ((number / 2 / 2 / 2 / 2 / 2) % 2)
      ((number / 2 / 2 / 2 / 2 / 2 / 2) % 2)
      ((number / 2 / 2 / 2 / 2 / 2 / 2 / 2) % 2)
Proof
  gen_tac
  >> irule
       (Q.SPECL
          [`number`,
           `number / 2`, `number / 2 / 2`,
           `number / 2 / 2 / 2`,
           `number / 2 / 2 / 2 / 2`,
           `number / 2 / 2 / 2 / 2 / 2`,
           `number / 2 / 2 / 2 / 2 / 2 / 2`,
           `number / 2 / 2 / 2 / 2 / 2 / 2 / 2`,
           `number / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2`,
           `number % 2`, `(number / 2) % 2`,
           `(number / 2 / 2) % 2`,
           `(number / 2 / 2 / 2) % 2`,
           `(number / 2 / 2 / 2 / 2) % 2`,
           `(number / 2 / 2 / 2 / 2 / 2) % 2`,
           `(number / 2 / 2 / 2 / 2 / 2 / 2) % 2`,
           `(number / 2 / 2 / 2 / 2 / 2 / 2 / 2) % 2`]
          source_integer_eight_step)
  >> simp[source_integer_division_two]
QED

Theorem source_integer_mod_256_horner:
  !number : int.
    number % 256 =
    source_int_horner8
      (number % 2) ((number / 2) % 2)
      ((number / 2 / 2) % 2) ((number / 2 / 2 / 2) % 2)
      ((number / 2 / 2 / 2 / 2) % 2)
      ((number / 2 / 2 / 2 / 2 / 2) % 2)
      ((number / 2 / 2 / 2 / 2 / 2 / 2) % 2)
      ((number / 2 / 2 / 2 / 2 / 2 / 2 / 2) % 2)
Proof
  gen_tac
  >> irule integerTheory.INT_MOD_UNIQUE
  >> qexists_tac
       `number / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2`
  >> simp[]
  >> conj_tac
  >- simp[source_integer_eight_bit_expansion]
  >> irule source_int_horner8_bounds
  >> simp[source_integer_remainder_two_bounds]
QED

Theorem source_num_mod_256_horner:
  !number : int.
    Num (number % 256) =
    source_horner8
      (number % 2 = 1) ((number / 2) % 2 = 1)
      ((number / 2 / 2) % 2 = 1)
      ((number / 2 / 2 / 2) % 2 = 1)
      ((number / 2 / 2 / 2 / 2) % 2 = 1)
      ((number / 2 / 2 / 2 / 2 / 2) % 2 = 1)
      ((number / 2 / 2 / 2 / 2 / 2 / 2) % 2 = 1)
      ((number / 2 / 2 / 2 / 2 / 2 / 2 / 2) % 2 = 1)
Proof
  gen_tac
  >> SIMP_TAC bool_ss [GSYM integerTheory.INT_INJ]
  >> `0 <= number % 256`
       by (mp_tac (Q.SPECL [`number`, `256`]
             integerTheory.INT_MOD_BOUNDS)
           >> simp[])
  >> `&Num (number % 256) = number % 256`
       by metis_tac[integerTheory.INT_OF_NUM]
  >> pop_assum (fn theorem => ONCE_REWRITE_TAC [theorem])
  >> simp[source_horner8_int, source_integer_low_bit,
          source_integer_mod_256_horner]
QED

Theorem source_char_of_integer_eq_iff:
  !number b0 b1 b2 b3 b4 b5 b6 b7.
    source_char_of_integer number =
    source_Char b0 b1 b2 b3 b4 b5 b6 b7 <=>
    Num (number % 256) =
    source_horner8 b0 b1 b2 b3 b4 b5 b6 b7
Proof
  simp[source_char_of_integer_def, source_Char_def,
       GSYM stringTheory.ORD_11, stringTheory.ORD_CHR_RWT,
       source_integer_byte_bounds, source_horner8_bound]
QED

Theorem source_char_of_integer_code:
  !number : int.
    source_char_of_integer number =
    (let (q0, b0) = source_bit_cut_integer number in
     let (q1, b1) = source_bit_cut_integer q0 in
     let (q2, b2) = source_bit_cut_integer q1 in
     let (q3, b3) = source_bit_cut_integer q2 in
     let (q4, b4) = source_bit_cut_integer q3 in
     let (q5, b5) = source_bit_cut_integer q4 in
     let (q6, b6) = source_bit_cut_integer q5 in
     let (q7, b7) = source_bit_cut_integer q6 in
       source_Char b0 b1 b2 b3 b4 b5 b6 b7)
Proof
  gen_tac
  >> simp[source_char_of_integer_def, source_bit_cut_integer_def,
          source_Char_def, GSYM stringTheory.ORD_11,
          stringTheory.ORD_CHR_RWT, source_horner8_bound,
          source_integer_byte_bounds]
  >> SIMP_TAC bool_ss [GSYM integerTheory.INT_INJ]
  >> `0 <= number % 256`
       by (mp_tac (Q.SPECL [`number`, `256`]
             integerTheory.INT_MOD_BOUNDS)
           >> simp[])
  >> `&Num (number % 256) = number % 256`
       by metis_tac[integerTheory.INT_OF_NUM]
  >> pop_assum (fn theorem => ONCE_REWRITE_TAC [theorem])
  >> SIMP_TAC bool_ss
       [source_horner8_int, source_integer_low_bit]
  >> simp[source_integer_mod_256_horner]
QED

Theorem source_integer_of_char_code:
  !b0 b1 b2 b3 b4 b5 b6 b7.
    source_integer_of_char
      (source_Char b0 b1 b2 b3 b4 b5 b6 b7) =
    &source_horner8 b0 b1 b2 b3 b4 b5 b6 b7
Proof
  simp[source_integer_of_char_def, source_Char_def,
       source_horner8_bound, stringTheory.ORD_CHR_RWT]
QED

Theorem source_char_of_integer_of_char:
  !character.
    source_char_of_integer (&source_of_char character) = character
Proof
  simp[source_char_of_integer_def, source_of_char_def,
       integerTheory.INT_MOD, arithmeticTheory.LESS_MOD,
       stringTheory.ORD_BOUND, stringTheory.CHR_ORD]
QED

Definition source_literal_asciis_def:
  source_literal_asciis literal =
    MAP source_integer_of_char (source_literal_explode literal)
End

Definition source_literal_of_asciis_def:
  source_literal_of_asciis numbers =
    source_literal_abs
      (MAP (source_ascii_of o source_char_of_integer) numbers)
End

Theorem source_literal_of_asciis_valid:
  !numbers.
    source_literal_valid
      (MAP (source_ascii_of o source_char_of_integer) numbers)
Proof
  simp[source_literal_valid_def, listTheory.EVERY_MAP,
       source_ascii_of_bound]
QED

Theorem source_literal_explode_bound:
  !literal character.
    MEM character (source_literal_explode literal) ==>
    ORD character < 128
Proof
  rpt strip_tac
  >> mp_tac (SPEC ``literal : source_literal``
       source_literal_explode_valid)
  >> simp[source_literal_valid_def, listTheory.EVERY_MEM]
  >> metis_tac[]
QED

Theorem source_literal_character_code_roundtrip:
  !character.
    ORD character < 128 ==>
    source_ascii_of
      (source_char_of_integer (source_integer_of_char character)) =
    character
Proof
  simp[source_integer_of_char_def, GSYM source_of_char_def,
       source_char_of_integer_of_char, source_ascii_of_idem]
QED

Theorem source_literal_roundtrip_map_valid:
  !literal.
    source_literal_valid
      (MAP
        (source_ascii_of o source_char_of_integer o
         source_integer_of_char)
        (source_literal_explode literal))
Proof
  simp[source_literal_valid_def, listTheory.EVERY_MAP,
       source_ascii_of_bound]
QED

Theorem source_literal_roundtrip_map:
  !characters.
    source_literal_valid characters ==>
    MAP
      (source_ascii_of o source_char_of_integer o
       source_integer_of_char)
      characters = characters
Proof
  Induct
  >> simp[source_literal_valid_def,
          source_literal_character_code_roundtrip]
QED

Theorem source_literal_of_asciis_asciis:
  !literal.
    source_literal_of_asciis (source_literal_asciis literal) = literal
Proof
  gen_tac
  >> rw[GSYM source_literal_explode_11,
        source_literal_of_asciis_def, source_literal_asciis_def]
  >> rw[source_literal_explode_abs,
        source_literal_of_asciis_valid,
        source_literal_roundtrip_map_valid]
  >> simp[listTheory.MAP_MAP_o]
  >> irule source_literal_roundtrip_map
  >> simp[source_literal_explode_valid]
QED

(* Isabelle/HOL src/HOL/String.thy:914-921.  Code.abort has this
   ordinary logical meaning; the target-language exception hook is not
   part of the theorem statement. *)
Definition source_abort_def:
  source_abort (_ : source_literal) (function : unit -> 'a) = function ()
End

(* Isabelle/HOL src/HOL/List.thy:3345-3351.  The code-abort declaration
   affects extraction only; logically this is application to EMPTY. *)
Definition source_abort_empty_set_def:
  source_abort_empty_set (function : 'a set -> 'a) = function EMPTY
End

(* Isabelle/HOL src/HOL/List.thy:2088.  Isabelle's partial list selectors
   use the same polymorphic undefined value on the empty list, whereas
   HOL4's independently specified HD and LAST need not agree there. *)
Definition source_hd_def:
  source_hd ([] : 'a list) = ARB /\
  source_hd (head::tail) = head
End

Definition source_last_def:
  source_last ([] : 'a list) = ARB /\
  source_last (head::tail) =
    if tail = [] then head else source_last tail
End

Theorem source_hd_nonempty:
  !items : 'a list.
    items <> [] ==> source_hd items = HD items
Proof
  Cases >> simp[source_hd_def]
QED

Theorem source_last_nonempty:
  !items : 'a list.
    items <> [] ==> source_last items = LAST items
Proof
  Induct >> simp[source_last_def, listTheory.LAST_DEF]
QED

Theorem source_hd_nil_eq_last_nil:
  source_hd ([] : 'a list) = source_last []
Proof
  simp[source_hd_def, source_last_def]
QED

Theorem source_set_empty_abort:
  !function.
    function (LIST_TO_SET []) = source_abort_empty_set function
Proof
  simp[source_abort_empty_set_def]
QED

(* Isabelle/HOL src/HOL/List.thy:994-1011. *)
Theorem source_hd_append:
  !xs ys : 'a list.
    HD (xs ++ ys) = if xs = [] then HD ys else HD xs
Proof
  Cases
  >> simp[]
QED

Theorem source_last_append:
  !xs ys : 'a list.
    LAST (xs ++ ys) = if ys = [] then LAST xs else LAST ys
Proof
  Cases_on `ys`
  >> simp[listTheory.LAST_APPEND_CONS]
QED

Theorem source_front_append:
  !xs ys : 'a list.
    FRONT (xs ++ ys) = if ys = [] then FRONT xs else xs ++ FRONT ys
Proof
  Cases_on `ys` THENL
    [simp[],
     REWRITE_TAC [listTheory.NOT_CONS_NIL, boolTheory.COND_CLAUSES]
     >> MATCH_ACCEPT_TAC
          (Q.SPECL [`xs : 'a list`, `t : 'a list`, `h : 'a`]
             rich_listTheory.FRONT_APPEND)]
QED

Theorem source_mem_front:
  !value (items : 'a list).
    MEM value (FRONT items) ==> MEM value items
Proof
  Cases_on `items` THENL
    [simp[], metis_tac[rich_listTheory.MEM_FRONT]]
QED

Theorem source_front_by_take:
  !items : 'a list.
    FRONT items = TAKE (LENGTH items - 1) items
Proof
  Cases_on `items`
  >> simp[rich_listTheory.FRONT_BY_TAKE]
QED

Theorem source_lt_length_take:
  !index limit (items : 'a list).
    index < LENGTH (TAKE limit items) <=>
    index < limit /\ index < LENGTH items
Proof
  rpt gen_tac
  >> Cases_on `limit <= LENGTH items`
  >> fs[listTheory.LENGTH_TAKE_EQ]
  >> Omega.OMEGA_TAC
QED

Theorem source_lt_length_drop:
  !index limit (items : 'a list).
    index < LENGTH (DROP limit items) <=>
    index + limit < LENGTH items
Proof
  rw[listTheory.LENGTH_DROP]
  >> Omega.OMEGA_TAC
QED

Theorem source_less_not_ge:
  !left right : num.
    left < right ==> ~(right <= left)
Proof
  Omega.OMEGA_TAC
QED

Theorem source_not_add_less_left:
  !left right : num.
    ~(left + right < left)
Proof
  Omega.OMEGA_TAC
QED

Theorem source_dropWhile_nonempty:
  !predicate (items : 'a list).
    EXISTS ($~ o predicate) items ==>
    dropWhile predicate items <> []
Proof
  REWRITE_TAC
    [listTheory.dropWhile_eq_nil, listTheory.EVERY_NOT_EXISTS,
     combinTheory.o_DEF]
QED

Theorem source_last_suffix:
  !whole suffix : 'a list.
    IS_SUFFIX whole suffix ==>
    suffix <> [] ==>
    LAST suffix = LAST whole
Proof
  rw[rich_listTheory.IS_SUFFIX_APPEND]
  >> ONCE_REWRITE_TAC[boolTheory.EQ_SYM_EQ]
  >> irule rich_listTheory.LAST_APPEND_NOT_NIL
  >> FIRST_ASSUM ACCEPT_TAC
QED

Theorem source_zip_map_fst_snd:
  !pairs : ('a # 'b) list.
    ZIP (MAP FST pairs, MAP SND pairs) = pairs
Proof
  REWRITE_TAC
    [GSYM listTheory.UNZIP_MAP, listTheory.ZIP_UNZIP]
QED

Theorem source_count_list_zero:
  !value (items : 'a list).
    LIST_ELEM_COUNT value items = 0 <=> ~MEM value items
Proof
  ONCE_REWRITE_TAC
    [GSYM arithmeticTheory.NOT_LT_ZERO_EQ_ZERO]
  >> REWRITE_TAC
       [REWRITE_RULE [arithmeticTheory.GREATER_DEF]
          rich_listTheory.LIST_ELEM_COUNT_MEM]
QED

Theorem source_length_nub_card:
  !items : 'a list.
    LENGTH (nub items) = CARD (LIST_TO_SET items)
Proof
  ONCE_REWRITE_TAC[boolTheory.EQ_SYM_EQ]
  >> MATCH_ACCEPT_TAC listTheory.CARD_LIST_TO_SET_EQN
QED

(* src/HOL/List.thy @ f7e02b7e states [takeWhile] as the primrec that
   keeps a head its predicate holds of and stops at the first it does
   not, which is HOL4's [takeWhile_def] clause for clause.  Naming
   that constant, rather than restating its clauses, is what lets the
   library's results about the walk meet a goal posed over the source
   one: a second copy of the equations would put every such result on
   the far side of a spelling difference. *)
Definition source_takeWhile_def[simp]:
  source_takeWhile = takeWhile
End

Theorem source_takeWhile_all:
  !predicate (items : 'a list).
    EVERY predicate items ==>
    takeWhile predicate items = items
Proof
  gen_tac
  >> Induct
  >> simp[listTheory.takeWhile_def]
QED

Theorem source_takeWhile_none:
  !predicate (items : 'a list).
    EVERY ($~ o predicate) items ==>
    takeWhile predicate items = []
Proof
  gen_tac
  >> Cases
  >> simp[listTheory.takeWhile_def, combinTheory.o_DEF]
QED

(* src/HOL/List.thy: set_takeWhileD.  HOL4 states the two conclusions
   apart, and neither half has the shape of the destruction rule the
   method names. *)
Theorem source_set_takeWhileD:
  !predicate xs item.
    MEM item (takeWhile predicate xs) ==> MEM item xs /\ predicate item
Proof
  metis_tac[listTheory.MEM_takeWhile_IMP, listTheory.EVERY_takeWhile,
            listTheory.EVERY_MEM]
QED

(* src/HOL/List.thy: dropWhile_eq_Cons_conv.  HOL4 states dropWhile_eq_nil
   for the empty result and dropWhile_eq_DROP for the index, and nothing
   that reads a nonempty result back as a decomposition of the list, which
   is the step the extract results are proved by. *)
Theorem source_dropWhile_eq_cons_conv:
  !predicate (xs : 'a list) head tail.
    dropWhile predicate xs = head::tail <=>
    xs = takeWhile predicate xs ++ head::tail /\ ~predicate head
Proof
  gen_tac
  >> Induct
  >> rw[listTheory.takeWhile_def]
  >> metis_tac[]
QED

(* Stated over HOL4's HD, as its [takeWhile] counterpart above is: the
   empty disjunct covers the list on which the two heads differ, so the
   source's [hd] reading is kept whole, and a library result about a
   head can meet the other disjunct. *)
Theorem source_dropWhile_eq_self_iff:
  !predicate (items : 'a list).
    dropWhile predicate items = items <=>
    items = [] \/ ~predicate (HD items)
Proof
  gen_tac
  >> Cases
  >> simp[listTheory.dropWhile_id]
QED

(* Isabelle/HOL src/HOL/List.thy:2529-2553. *)
Theorem source_takeWhile_dropWhile_id:
  !predicate (items : 'a list).
    takeWhile predicate items ++ dropWhile predicate items = items
Proof
  gen_tac
  >> Induct
  >> simp[listTheory.takeWhile_def]
  >> rw[]
QED

Theorem source_takeWhile_append1:
  !predicate (items : 'a list) suffix item.
    MEM item items ==>
    ~predicate item ==>
    takeWhile predicate (items ++ suffix) =
    takeWhile predicate items
Proof
  gen_tac
  >> Induct_on `items`
  >- simp[]
  >> rpt gen_tac
  >> Cases_on `predicate h`
  >> simp[listTheory.takeWhile_def]
  >> metis_tac[]
QED

Theorem source_takeWhile_append2:
  !predicate (items : 'a list) suffix.
    EVERY predicate items ==>
    takeWhile predicate (items ++ suffix) =
    items ++ takeWhile predicate suffix
Proof
  gen_tac
  >> Induct_on `items`
  >> simp[listTheory.takeWhile_def]
QED

Theorem source_takeWhile_eq_nil_iff:
  !predicate (items : 'a list).
    takeWhile predicate items = [] <=>
    items = [] \/ ~predicate (HD items)
Proof
  rpt gen_tac
  >> Cases_on `items`
  >> simp[listTheory.takeWhile_def]
  >> Cases_on `predicate h`
  >> simp[]
QED

(* Isabelle/HOL src/HOL/List.thy:2566-2574. *)
Theorem source_dropWhile_append1:
  !predicate (items : 'a list) suffix item.
    MEM item items ==>
    ~predicate item ==>
    dropWhile predicate (items ++ suffix) =
    dropWhile predicate items ++ suffix
Proof
  rpt strip_tac
  >> irule listTheory.dropWhile_APPEND_EXISTS
  >> simp[listTheory.EXISTS_MEM, combinTheory.o_DEF]
  >> metis_tac[]
QED

Theorem source_dropWhile_append2:
  !predicate (items : 'a list) suffix.
    EVERY predicate items ==>
    dropWhile predicate (items ++ suffix) =
    dropWhile predicate suffix
Proof
  metis_tac[listTheory.dropWhile_APPEND_EVERY]
QED

Theorem source_list_rel_all_mem_aux:
  (!left right.
     relation left right ==>
     (left_predicate left <=> right_predicate right)) ==>
  !left_items right_items.
    LIST_REL relation left_items right_items ==>
    ((!item. MEM item left_items ==> left_predicate item) <=>
     !item. MEM item right_items ==> right_predicate item)
Proof
  strip_tac
  >> Induct_on `LIST_REL`
  >> simp[]
  >> metis_tac[]
QED

Theorem source_list_rel_all_mem:
  !relation left_items right_items.
    LIST_REL relation left_items right_items ==>
    !left_predicate right_predicate.
    (!left right.
       relation left right ==>
       (left_predicate left <=> right_predicate right)) ==>
    ((!item. MEM item left_items ==> left_predicate item) <=>
     !item. MEM item right_items ==> right_predicate item)
Proof
  rpt gen_tac
  >> strip_tac
  >> rpt gen_tac
  >> strip_tac
  >> irule source_list_rel_all_mem_aux
  >> metis_tac[]
QED

(* Isabelle/HOL src/HOL/Fun.thy:831 [fun_upd], a plain definition, and
   the whole of a maplet: src/HOL/Map.thy:74 makes [m(a |-> b)] syntax
   for it.  It is a constant there -- a method reaches its body only by
   naming [fun_upd_def] -- and Map.thy states result after result of the
   unapplied constant simp: [map_add_upd] at :369, [restrict_fun_upd] at
   :441, [dom_fun_upd] at :581, [fun_upd_None_if_notin_dom] at :707.
   The corpus carried the body instead, against which none of them can
   be stated at all: the body is a conditional, and the weak conditional
   congruence Isabelle and this layer both keep leaves a branch alone,
   so no rewrite reaches the map the update is built on. *)
Definition source_fun_upd_def:
  source_fun_upd func key value =
    \query. if query = key then value else func query
End

(* src/HOL/Fun.thy:872 [fun_upd_apply], declared [simp] -- the equation
   that takes the constant apart again wherever a method reaches a
   point; :883 [fun_upd_upd], also [simp]; and :869 [fun_upd_triv],
   declared [iff].  Between them they are the whole of what Isabelle's
   simpset reads about an update whose definition it withholds. *)
Theorem source_fun_upd_apply:
  !func key value query.
    source_fun_upd func key value query =
    if query = key then value else func query
Proof
  rw[source_fun_upd_def]
QED

Theorem source_fun_upd_upd:
  !func key value replacement.
    source_fun_upd (source_fun_upd func key value) key replacement =
    source_fun_upd func key replacement
Proof
  rw[source_fun_upd_def, boolTheory.FUN_EQ_THM]
QED

Theorem source_fun_upd_triv:
  !func key. source_fun_upd func key (func key) = func
Proof
  rw[source_fun_upd_def, boolTheory.FUN_EQ_THM]
  >> COND_CASES_TAC
  >> simp[]
QED

(* Isabelle/HOL src/HOL/Map.thy:193-845. *)
Definition source_alookup_def[simp]:
  (source_alookup ([] : ('a # 'b) list) key = NONE) /\
  (source_alookup ((stored_key,value)::rest) key =
     if key = stored_key then SOME value
     else source_alookup rest key)
End

Overload ALOOKUP = “source_alookup”

Theorem source_alookup_append:
  !left right key.
    source_alookup (left ++ right) key =
    option_CASE (source_alookup left key)
      (source_alookup right key) SOME
Proof
  Induct
  >- simp[source_alookup_def]
  >> Cases_on `h`
  >> rpt gen_tac
  >> simp[source_alookup_def]
  >> Cases_on `key = q`
  >> simp[]
QED

Theorem source_option_overlay_assoc:
  !first second third.
    option_CASE (option_CASE first second SOME) third SOME =
    option_CASE first (option_CASE second third SOME) SOME
Proof
  Cases
  >> simp[]
QED

Theorem source_option_overlay_not_none:
  !left right.
    (option_CASE right left SOME <> NONE <=>
     right <> NONE \/ left <> NONE)
Proof
  Cases_on `right`
  >> Cases_on `left`
  >> simp[]
QED

Theorem source_map_upds_cons_pointwise:
  !function head_key tail_keys head_value tail_values key.
    option_CASE
      (source_alookup
        (REVERSE
          (ZIP
            (head_key::tail_keys, head_value::tail_values))) key)
      (function key) SOME =
    option_CASE
      (source_alookup
        (REVERSE (ZIP (tail_keys, tail_values))) key)
      (if key = head_key then SOME head_value else function key) SOME
Proof
  rpt gen_tac
  >> simp[listTheory.ZIP_def, listTheory.REVERSE_DEF,
          source_alookup_append, source_alookup_def]
  >> Cases_on
       `source_alookup
          (REVERSE (ZIP (tail_keys, tail_values))) key`
  >> Cases_on `key = head_key`
  >> simp[]
QED

Theorem source_alookup_some_mem:
  !pairs key value.
    source_alookup pairs key = SOME value ==>
    MEM (key,value) pairs
Proof
  rpt gen_tac
  >> Induct_on `pairs`
  >- simp[source_alookup_def]
  >> Cases_on `h`
  >> Cases_on `key = q`
  >> fs[source_alookup_def]
QED

Theorem source_mem_alookup_some:
  !pairs key value.
    MEM (key,value) pairs ==>
    ?result. source_alookup pairs key = SOME result
Proof
  rpt gen_tac
  >> Induct_on `pairs`
  >- simp[source_alookup_def]
  >> Cases_on `h`
  >> Cases_on `key = q`
  >> fs[source_alookup_def]
  >> metis_tac[]
QED

Theorem source_mem_fst:
  !pairs key value.
    MEM (key,value) pairs ==>
    MEM key (MAP FST pairs)
Proof
  rpt gen_tac
  >> Induct_on `pairs`
  >- simp[]
  >> gen_tac
  >> Cases_on `h`
  >> simp[]
  >> metis_tac[]
QED

Theorem source_distinct_keys_unique:
  !pairs key left right.
    ALL_DISTINCT (MAP FST pairs) /\
    MEM (key,left) pairs /\ MEM (key,right) pairs ==>
    left = right
Proof
  rpt gen_tac
  >> Induct_on `pairs`
  >- simp[]
  >> Cases_on `h`
  >> rw[]
  >> imp_res_tac source_mem_fst
  >> fs[]
QED

Theorem source_mem_map_fst_zip:
  !key keys values.
    MEM key (MAP FST (ZIP (keys,values))) ==>
    MEM key keys
Proof
  gen_tac
  >> Induct_on `keys`
  >- simp[listTheory.ZIP_def]
  >> Cases_on `values`
  >- simp[listTheory.ZIP_def]
  >> simp[listTheory.ZIP_def]
  >> metis_tac[]
QED

Theorem source_mem_fst_zip:
  !pair keys values.
    MEM pair (ZIP (keys,values)) ==>
    MEM (FST pair) keys
Proof
  rpt strip_tac
  >> `MEM (FST pair) (MAP FST (ZIP (keys,values)))`
       by metis_tac[listTheory.MEM_MAP]
  >> metis_tac[source_mem_map_fst_zip]
QED

Theorem source_map_fst_zip_take:
  !keys values.
    MAP FST (ZIP (keys,values)) =
    TAKE (LENGTH values) keys
Proof
  Induct_on `keys`
  >> Cases_on `values`
  >> simp[listTheory.ZIP_def]
QED

Theorem source_mem_fst_zip_take:
  !pair keys values.
    MEM pair (ZIP (keys,values)) ==>
    MEM (FST pair) (TAKE (LENGTH values) keys)
Proof
  rpt strip_tac
  >> `MEM (FST pair) (MAP FST (ZIP (keys,values)))`
       by metis_tac[listTheory.MEM_MAP]
  >> fs[source_map_fst_zip_take]
QED

Theorem source_alookup_reverse_zip_none:
  !key keys values.
    ~MEM key (TAKE (LENGTH values) keys) ==>
    ALOOKUP (REVERSE (ZIP (keys,values))) key = NONE
Proof
  rpt gen_tac
  >> strip_tac
  >> Cases_on `ALOOKUP (REVERSE (ZIP (keys,values))) key`
  >- simp[]
  >> pop_assum
       (fn th => assume_tac
          (MATCH_MP
             (Q.SPECL
                [`REVERSE (ZIP (keys,values))`, `key`, `x`]
                source_alookup_some_mem)
             th))
  >> fs[listTheory.MEM_REVERSE]
  >> pop_assum
       (fn th => assume_tac
          (MATCH_MP
             (Q.SPECL
                [`(key,x)`, `keys`, `values`]
                source_mem_fst_zip_take)
             th))
  >> fs[]
QED

Theorem source_alookup_reverse_zip_some:
  !key keys values.
    MEM key (TAKE (LENGTH values) keys) ==>
    ?result.
      ALOOKUP (REVERSE (ZIP (keys,values))) key = SOME result
Proof
  rpt strip_tac
  >> `MEM key (MAP FST (ZIP (keys,values)))`
       by fs[source_map_fst_zip_take]
  >> `?pair.
        key = FST pair /\ MEM pair (ZIP (keys,values))`
       by metis_tac[listTheory.MEM_MAP]
  >> pop_assum strip_assume_tac
  >> Cases_on `pair`
  >> fs[]
  >> `MEM (key,r) (REVERSE (ZIP (keys,values)))`
       by fs[listTheory.MEM_REVERSE]
  >> metis_tac[source_mem_alookup_some]
QED

Theorem source_alookup_reverse_zip_is_some:
  !key keys values.
    (?result.
       ALOOKUP (REVERSE (ZIP (keys,values))) key = SOME result) <=>
    MEM key (TAKE (LENGTH values) keys)
Proof
  rpt gen_tac
  >> eq_tac
  >- (strip_tac
      >> pop_assum
           (fn th => assume_tac
              (MATCH_MP
                 (Q.SPECL
                    [`REVERSE (ZIP (keys,values))`, `key`, `result`]
                    source_alookup_some_mem)
                 th))
      >> fs[listTheory.MEM_REVERSE]
      >> pop_assum
           (fn th => assume_tac
              (MATCH_MP
                 (Q.SPECL
                    [`(key,result)`, `keys`, `values`]
                    source_mem_fst_zip_take)
                 th))
      >> fs[])
  >> strip_tac
  >> pop_assum
       (fn th => ACCEPT_TAC
          (MATCH_MP
             (Q.SPECL [`key`, `keys`, `values`]
                source_alookup_reverse_zip_some)
             th))
QED

(* src/HOL/Map.thy: ran_distinct.  The translation inlines [ran] as the
   lambda below rather than naming a constant, and the map is HOL4's own
   [alist$ALOOKUP], not the [source_alookup] this section overloads. *)
Theorem source_ran_distinct:
  !al : ('a # 'b) list.
    ALL_DISTINCT (MAP FST al) ==>
    (\value. ?key. alist$ALOOKUP al key = SOME value) =
    IMAGE SND (LIST_TO_SET al)
Proof
  rw[pred_setTheory.EXTENSION, pred_setTheory.IN_ABS]
  >> eq_tac >> rw[]
  >- (drule alistTheory.ALOOKUP_MEM >> strip_tac
      >> qexists_tac `(key,x)` >> simp[])
  >> Cases_on `x'` >> fs[]
  >> metis_tac[alistTheory.ALOOKUP_ALL_DISTINCT_MEM]
QED

Theorem source_not_mem_take:
  !key keys count.
    ~MEM key keys ==>
    ~MEM key (TAKE count keys)
Proof
  metis_tac[rich_listTheory.MEM_TAKE]
QED

Theorem source_alookup_reverse_zip_none_full:
  !key keys values.
    ~MEM key keys ==>
    ALOOKUP (REVERSE (ZIP (keys,values))) key = NONE
Proof
  metis_tac[source_not_mem_take,
            source_alookup_reverse_zip_none]
QED

Theorem source_alookup_reverse_zip_some_mem:
  !key value keys values.
    ALOOKUP (REVERSE (ZIP (keys,values))) key = SOME value ==>
    MEM key keys
Proof
  rpt strip_tac
  >> CCONTR_TAC
  >> fs[source_alookup_reverse_zip_none_full]
QED

Theorem source_option_update_twist:
  !lookup function key value.
    lookup key = NONE ==>
    (\query.
       option_CASE (lookup query)
         (if query = key then SOME value else function query)
         SOME) =
    (\query.
       if query = key then SOME value
       else option_CASE (lookup query) (function query) SOME)
Proof
  rpt strip_tac
  >> simp[boolTheory.FUN_EQ_THM]
  >> gen_tac
  >> Cases_on `query = key`
  >> fs[]
QED

Theorem source_alookup_update_twist:
  !entries function key value.
    ALOOKUP entries key = NONE ==>
    (\query.
       option_CASE (ALOOKUP entries query)
         (if query = key then SOME value else function query)
         SOME) =
    (\query.
       if query = key then SOME value
       else option_CASE (ALOOKUP entries query) (function query) SOME)
Proof
  metis_tac[source_option_update_twist]
QED

Theorem source_map_upd_upds_conv_not_mem:
  !function key value keys values.
    ~MEM key (TAKE (LENGTH values) keys) ==>
    (\query.
       option_CASE
         (ALOOKUP (REVERSE (ZIP (keys,values))) query)
         (if query = key then SOME value else function query)
         SOME) =
    (\query.
       if query = key then SOME value
       else
         option_CASE
           (ALOOKUP (REVERSE (ZIP (keys,values))) query)
           (function query)
           SOME)
Proof
  rpt strip_tac
  >> irule source_alookup_update_twist
  >> metis_tac[source_alookup_reverse_zip_none]
QED

Theorem source_map_upd_upds_twist_full:
  !function key value keys values.
    ~MEM key keys ==>
    (\query.
       option_CASE
         (ALOOKUP (REVERSE (ZIP (keys,values))) query)
         (if query = key then SOME value else function query)
         SOME) =
    (\query.
       if query = key then SOME value
       else
         option_CASE
           (ALOOKUP (REVERSE (ZIP (keys,values))) query)
           (function query)
           SOME)
Proof
  metis_tac[source_not_mem_take, source_map_upd_upds_conv_not_mem]
QED

Theorem source_map_upd_upds_twist_full_iff:
  !function key value keys values.
    ((~MEM key keys ==>
      (\query.
         option_CASE
           (ALOOKUP (REVERSE (ZIP (keys,values))) query)
           (if query = key then SOME value else function query)
           SOME) =
      (\query.
         if query = key then SOME value
         else
           option_CASE
             (ALOOKUP (REVERSE (ZIP (keys,values))) query)
             (function query)
             SOME)) <=> T)
Proof
  simp[source_map_upd_upds_twist_full]
QED

Theorem source_finite_graph_alookup:
  !entries.
    FINITE
      (\pair.
         alist$ALOOKUP entries (FST pair) = SOME (SND pair))
Proof
  gen_tac
  >> irule pred_setTheory.SUBSET_FINITE
  >> qexists_tac `LIST_TO_SET entries`
  >> simp[pred_setTheory.SUBSET_DEF]
  >> metis_tac[alistTheory.ALOOKUP_MEM, pairTheory.PAIR]
QED

(* A reusable finite-graph constructor: the lookup implementation is
   arbitrary, and finiteness follows from any finite association-list
   support. *)
Theorem source_finite_functional_graph:
  !lookup entries.
    (!key value.
       lookup key = SOME value ==>
       MEM (key,value) entries) ==>
    FINITE
      (\pair.
         lookup (FST pair) = SOME (SND pair))
Proof
  rpt strip_tac
  >> irule pred_setTheory.SUBSET_FINITE
  >> qexists_tac `LIST_TO_SET entries`
  >> simp[pred_setTheory.SUBSET_DEF]
  >> metis_tac[pairTheory.PAIR]
QED

(* Keep the finite support visible in the graph constructor.  This lets
   proof search infer the association-list witness by ordinary first-order
   matching instead of guessing a hidden support for a partially applied
   lookup function. *)
Theorem source_finite_bounded_lookup_graph:
  !lookup_builder entries.
    (!key value.
       lookup_builder entries key = SOME value ==>
       MEM (key,value) entries) ==>
    FINITE
      (\pair.
         lookup_builder entries (FST pair) = SOME (SND pair))
Proof
  rpt strip_tac
  >> irule pred_setTheory.SUBSET_FINITE
  >> qexists_tac `LIST_TO_SET entries`
  >> simp[pred_setTheory.SUBSET_DEF]
  >> metis_tac[pairTheory.PAIR]
QED

(* General dependent-pair witness used by image/Sigma normalization. *)
Theorem source_pair_fibre_witness:
  !domain fibre value.
    domain value /\ fibre value <> {} ==>
    ?pair.
      FST pair = value /\
      domain (FST pair) /\
      SND pair IN fibre (FST pair)
Proof
  rpt strip_tac
  >> qexists_tac `(value, CHOICE (fibre value))`
  >> simp[]
  >> metis_tac[pred_setTheory.CHOICE_DEF]
QED

Theorem source_ran_update_old_witness:
  !function key old_value new_value value candidate.
    function key = SOME old_value ==>
    function candidate = SOME value ==>
    value <> old_value ==>
    ?witness.
      (witness = key ==> new_value = value) /\
      (witness <> key ==> function witness = SOME value)
Proof
  rpt strip_tac
  >> qexists_tac `candidate`
  >> Cases_on `candidate = key`
  >> fs[]
QED

Theorem source_ran_update_new_witness:
  !function key new_value value.
    value = new_value ==>
    ?witness.
      (witness = key ==> new_value = value) /\
      (witness <> key ==> function witness = SOME value)
Proof
  rpt strip_tac
  >> qexists_tac `key`
  >> simp[]
QED

Theorem source_ran_update_injective_pointwise:
  !function key old_value new_value.
    function key = SOME old_value ==>
    (!left right.
       (?value. function left = SOME value) /\
       (?value. function right = SOME value) ==>
       function left = function right ==>
       left = right) ==>
    (!candidate. function candidate <> SOME new_value) ==>
    !value.
      ((?candidate.
          (candidate = key ==> new_value = value) /\
          (candidate <> key ==> function candidate = SOME value)) <=>
       ((?candidate. function candidate = SOME value) /\
        value <> old_value) \/
       value = new_value)
Proof
  rpt gen_tac
  >> strip_tac
  >> strip_tac
  >> strip_tac
  >> gen_tac
  >> eq_tac
  >> metis_tac[source_ran_update_old_witness,
                source_ran_update_new_witness]
QED

Theorem source_ran_update_injective_pointwise_iff:
  !function key old_value new_value.
    ((function key = SOME old_value ==>
      (!left right.
         (?value. function left = SOME value) /\
         (?value. function right = SOME value) ==>
         function left = function right ==>
         left = right) ==>
      (!candidate. function candidate <> SOME new_value) ==>
      !value.
        ((?candidate.
            (candidate = key ==> new_value = value) /\
            (candidate <> key ==> function candidate = SOME value)) <=>
         ((?candidate. function candidate = SOME value) /\
          value <> old_value) \/
         value = new_value)) <=> T)
Proof
  rpt gen_tac
  >> rewrite_tac[boolTheory.EQ_CLAUSES]
  >> qspecl_then [`function`, `key`, `old_value`, `new_value`]
       MATCH_ACCEPT_TAC source_ran_update_injective_pointwise
QED

(* Isabelle/HOL src/HOL/Map.thy:26 [map_add] and :49 [map_le], both
   plain definitions.  They are constants there, and an Isabelle goal
   about them is headed by the constant; a method reaches their bodies
   only by naming [map_add_def] or [map_le_def].  [source_map_add] is
   stated at two arguments, as Isabelle states it, so its equation
   rewrites the partial application the goals carry.  [source_map_le]
   keeps the translated body -- Isabelle's bounded quantifier over
   [dom m1] says exactly this about a map the translation renders as a
   function into option. *)
Definition source_map_add_def:
  source_map_add left right =
    \key. option_CASE (right key) (left key) SOME
End

Definition source_map_le_def:
  source_map_le left right <=>
    !key value. left key = SOME value ==> right key = SOME value
End

(* src/HOL/Map.thy: map_le_antisym and map_add_le_mapI. *)
Theorem source_map_le_antisym:
  !left right.
    source_map_le left right ==>
    source_map_le right left ==>
    left = right
Proof
  rpt gen_tac
  >> rewrite_tac[source_map_le_def]
  >> strip_tac
  >> strip_tac
  >> simp[boolTheory.FUN_EQ_THM]
  >> gen_tac
  >> Cases_on `left x`
  >> Cases_on `right x`
  >> res_tac
  >> fs[]
QED

Theorem source_map_add_le_mapI:
  !left right upper.
    source_map_le left upper ==>
    source_map_le right upper ==>
    source_map_le (source_map_add left right) upper
Proof
  rpt gen_tac
  >> rewrite_tac[source_map_le_def, source_map_add_def]
  >> strip_tac
  >> strip_tac
  >> rpt gen_tac
  >> Cases_on `right key`
  >> fs[]
QED

(* Isabelle/HOL src/HOL/Map.thy:359 [map_add_SomeD], declared [dest!]
   -- a safe destruction rule in Isabelle's ambient claset, not in its
   simpset.  It is the reading of a map sum that the rewrites cannot
   give: they match the sum under [= NONE] or produce it from a value,
   and this takes one apart.  Map.thy:355 [map_add_Some_iff] is the
   equivalence it is derived from and carries no attribute; the corpus
   states that one as map_L355, so only the declared direction is
   ambient. *)
Theorem source_map_add_SomeD:
  !left right key value.
    source_map_add left right key = SOME value ==>
    right key = SOME value \/
    right key = NONE /\ left key = SOME value
Proof
  rw[source_map_add_def]
  >> Cases_on `right key`
  >> fs[]
QED

(* Isabelle/HOL src/HOL/Map.thy:363 [map_add_find_right], declared
   [simp].  Isabelle withholds [map_add]'s definition and declares this
   about it instead, so a method that never names [map_add_def] still
   reads a value out of the right-hand map. *)
Theorem source_map_add_find_right:
  !left right key value.
    right key = SOME value ==> source_map_add left right key = SOME value
Proof
  rw[source_map_add_def]
QED

(* Isabelle/HOL src/HOL/Map.thy:99 [map_upds], a plain definition
   stated through [map_add]: [m(xs [|->] ys) = m ++ map_of (rev (zip xs
   ys))].  Rendering it that way rather than writing the option case out
   is what lets the results Isabelle declares about [map_add] reach a
   goal about a list update, as they do in the source. *)
Definition source_map_upds_def:
  source_map_upds func keys values =
    source_map_add func (ALOOKUP (REVERSE (ZIP (keys,values))))
End

(* Isabelle/HOL src/HOL/Map.thy:91 [map_of.simps], a primrec clause and
   so ambient.  Isabelle states it as an equation between functions,
   onto [empty]; HOL4's recursion takes the key as well, so the
   translation's own clause is the pointwise reading and a rewrite that
   has to see the unapplied map -- [map_add_empty] below -- does not
   reach it. *)
Theorem source_map_of_Nil:
  source_alookup ([] : ('a # 'b) list) = (\key. NONE)
Proof
  simp[boolTheory.FUN_EQ_THM]
QED

(* Isabelle/HOL src/HOL/Map.thy:346 [map_add_empty], declared [simp]. *)
Theorem source_map_add_empty:
  !func : 'a -> 'b option. source_map_add func (\key. NONE) = func
Proof
  rw[source_map_add_def, boolTheory.FUN_EQ_THM]
QED

(* Isabelle/HOL src/HOL/Map.thy:92 [map_of.simps], the cons clause.
   Isabelle states it as an update of the tail's map and not as a
   conditional, which is what lets [map_add_upd] below reach the tail:
   written the other way the tail sits in a branch no rewrite descends
   into. *)
Theorem source_map_of_Cons:
  !stored_key value rest.
    source_alookup ((stored_key,value)::rest) =
    source_fun_upd (source_alookup rest) stored_key (SOME value)
Proof
  rw[source_fun_upd_def, boolTheory.FUN_EQ_THM]
QED

(* Isabelle/HOL src/HOL/Map.thy:378 [map_of_append], declared [simp]. *)
Theorem source_map_of_append:
  !left right.
    source_alookup (left ++ right) =
    source_map_add (source_alookup right) (source_alookup left)
Proof
  rw[boolTheory.FUN_EQ_THM, source_map_add_def, source_alookup_append]
QED

(* Isabelle/HOL src/HOL/Map.thy:369 [map_add_upd], declared [simp]. *)
Theorem source_map_add_upd:
  !left right key value.
    source_map_add left (source_fun_upd right key (SOME value)) =
    source_fun_upd (source_map_add left right) key (SOME value)
Proof
  rw[boolTheory.FUN_EQ_THM, source_map_add_def, source_fun_upd_def]
  >> BasicProvers.EVERY_CASE_TAC
  >> simp[]
QED

(* Isabelle/HOL src/HOL/Map.thy:352 [map_add_assoc], declared [simp]. *)
Theorem source_map_add_assoc:
  !left middle right.
    source_map_add left (source_map_add middle right) =
    source_map_add (source_map_add left middle) right
Proof
  rw[source_map_add_def, FUN_EQ_THM]
  >> Cases_on `right x`
  >> simp[]
QED

(* Isabelle/HOL src/HOL/Map.thy:501 [map_upd_upds_conv_if], not
   declared and named by map_L519's method.  Isabelle states it of the
   two constants, an update of a list update against a list update of
   an update; it was unstatable while the corpus carried the update as
   a beta-redex, and the option case had to be written out on both
   sides instead. *)
Theorem source_map_upd_upds_conv_if:
  !function key value keys values.
    source_map_upds (source_fun_upd function key (SOME value)) keys values =
    if MEM key (TAKE (LENGTH values) keys) then
      source_map_upds function keys values
    else
      source_fun_upd (source_map_upds function keys values) key (SOME value)
Proof
  rpt gen_tac
  >> rw[source_map_upds_def, source_map_add_def, source_fun_upd_def,
        boolTheory.FUN_EQ_THM]
  >> rpt (COND_CASES_TAC >> fs[])
  >> Cases_on `ALOOKUP (REVERSE (ZIP (keys,values))) key`
  >> fs[GSYM source_alookup_reverse_zip_is_some]
QED

(* Isabelle/HOL src/HOL/Map.thy:366 [map_add_None], declared [iff]. *)
Theorem source_map_add_None:
  !left right key.
    (source_map_add left right key = NONE) <=>
    right key = NONE /\ left key = NONE
Proof
  rw[source_map_add_def]
  >> Cases_on `right key`
  >> simp[]
QED

(* Isabelle/HOL src/HOL/Map.thy:610 [map_add_comm].  A map sum
   commutes where the two domains are disjoint.  The statement needs
   [map_add] as a term, so it was unstatable while the corpus carried
   the sum as a beta-redex; map_L810 names it, and Map.thy:610 is not
   itself a corpus goal.  [dom] stays inlined, as the corpus renders
   it -- the goal that cites this states its own hypothesis that way. *)
Theorem source_map_add_comm:
  !left right.
    (\candidate. left candidate <> NONE) INTER
    (\candidate. right candidate <> NONE) = {} ==>
    source_map_add left right = source_map_add right left
Proof
  rpt gen_tac
  >> rewrite_tac[pred_setTheory.EXTENSION, pred_setTheory.IN_INTER,
                 pred_setTheory.NOT_IN_EMPTY, boolTheory.IN_DEF]
  >> strip_tac
  >> simp[source_map_add_def, boolTheory.FUN_EQ_THM]
  >> gen_tac
  >> first_x_assum (qspec_then `x` mp_tac)
  >> Cases_on `left x`
  >> Cases_on `right x`
  >> simp[]
QED

(* Isabelle/HOL src/HOL/Map.thy:846 [map_le_refl], declared [simp]. *)
Theorem source_map_le_refl:
  !mapping. source_map_le mapping mapping
Proof
  rw[source_map_le_def]
QED

(* Isabelle/HOL src/HOL/Map.thy:856 [map_le_map_add], declared [simp].
   Isabelle proves it from [map_add_find_right], and the two say the
   same thing once [map_le] is unfolded; the corpus states it as
   map_L887, which is why the measurement withholds the ambient reading
   there. *)
Theorem source_map_le_map_add:
  !left right. source_map_le right (source_map_add left right)
Proof
  rw[source_map_le_def, source_map_add_def]
QED

Theorem source_map_add_subsumed_step:
  !left right.
    source_map_le left right ==>
    !key.
      (right key = NONE /\ left key = right key) \/
      (?value.
         right key = SOME value /\
         SOME value = right key)
Proof
  rpt gen_tac
  >> rewrite_tac[source_map_le_def]
  >> strip_tac
  >> gen_tac
  >> Cases_on `left key`
  >> Cases_on `right key`
  >> res_tac
  >> fs[]
QED

Theorem source_range_update_none:
  !mapping key value query.
    mapping key = NONE ==>
    ((?witness.
        (if witness = key then SOME value else mapping witness) =
        SOME query) <=>
     query = value \/
     ?witness. mapping witness = SOME query)
Proof
  rpt strip_tac >>
  eq_tac
  >- (strip_tac >>
      Cases_on `witness = key` >>
      fs[] >>
      metis_tac[]) >>
  strip_tac
  >- (qexists_tac `key` >> simp[]) >>
  qexists_tac `witness` >>
  Cases_on `witness = key` >>
  fs[]
QED

Theorem source_domI:
  !function key value.
    function key = SOME value ==>
    key IN (\candidate. function candidate <> NONE)
Proof
  simp[]
QED

(* Isabelle/HOL src/HOL/Map.thy:793.  [graph] and [dom] are both
   inlined, so the equation is stated between the two sets the
   translation writes out. *)
Theorem source_graph_eq_to_snd_dom:
  !mapping.
    (\pair. mapping (FST pair) = SOME (SND pair)) =
    IMAGE (\key. (key, THE (mapping key))) (\key. mapping key <> NONE)
Proof
  gen_tac
  >> simp[pred_setTheory.EXTENSION, pred_setTheory.IN_IMAGE,
          boolTheory.IN_DEF, pairTheory.FORALL_PROD]
  >> rpt gen_tac
  >> eq_tac
  >> rw[]
  >> metis_tac[optionTheory.THE_DEF, optionTheory.option_CLAUSES]
QED

(* Isabelle/HOL src/HOL/Map.thy:596.  [map_of] is [ALOOKUP] and [dom]
   is inlined, so the finiteness is stated of the key set the
   translation writes out. *)
Theorem source_finite_dom_map_of:
  !al. FINITE (\key. alist$ALOOKUP al key <> NONE)
Proof
  gen_tac
  >> irule pred_setTheory.SUBSET_FINITE
  >> qexists_tac `LIST_TO_SET (MAP FST al)`
  >> simp[pred_setTheory.SUBSET_DEF, boolTheory.IN_DEF,
          alistTheory.ALOOKUP_NONE]
QED

(* Isabelle/HOL src/HOL/List.thy:8687. *)
Theorem source_mem_product:
  !pair (xs : 'a list) (ys : 'b list).
    MEM pair
      (FLAT (MAP (\x. MAP (\y. (x,y)) ys) xs)) <=>
    MEM (FST pair) xs /\ MEM (SND pair) ys
Proof
  rpt gen_tac
  >> Cases_on `pair`
  >> Induct_on `xs`
  >> simp[listTheory.MEM_MAP]
  >> metis_tac[]
QED

(* Isabelle/HOL src/HOL/List.thy:8705. *)
Theorem source_mem_relcomp_row:
  !pair (xy : 'a # 'c) (yzs : ('c # 'b) list).
    MEM pair
      (FLAT
         (MAP
            (\yz.
               if SND xy = FST yz then
                 [(FST xy,SND yz)]
               else [])
            yzs)) <=>
    FST pair = FST xy /\
    MEM (SND xy,SND pair) yzs
Proof
  rpt gen_tac
  >> Cases_on `pair`
  >> Cases_on `xy`
  >> Induct_on `yzs`
  >- simp[]
  >> Cases_on `h`
  >> Cases_on `r' = q''`
  >> fs[boolTheory.LEFT_AND_OVER_OR]
QED

(* Isabelle/HOL src/HOL/List.thy:8705. *)
Theorem source_mem_relcomp:
  !pair (xys : ('a # 'c) list) (yzs : ('c # 'b) list).
    MEM pair
      (FLAT
         (MAP
            (\xy.
               FLAT
                 (MAP
                    (\yz.
                       if SND xy = FST yz then
                         [(FST xy,SND yz)]
                       else [])
                    yzs))
            xys)) <=>
    ?middle.
      MEM (FST pair,middle) xys /\
      MEM (middle,SND pair) yzs
Proof
  rpt gen_tac
  >> Cases_on `pair`
  >> Induct_on `xys`
  >- simp[]
  >> simp[source_mem_relcomp_row]
  >> gen_tac
  >> Cases_on `h`
  >> simp[boolTheory.LEFT_AND_OVER_OR]
  >> metis_tac[]
QED

Theorem source_tl_append:
  !xs ys : 'a list.
    TL (xs ++ ys) =
    list_CASE xs (TL ys) (\value tail. tail ++ ys)
Proof
  Cases
  >> simp[]
QED

Theorem source_num_offset_interval:
  !lower upper value : num.
    lower <= value /\ value < upper <=>
    ?offset. value = lower + offset /\ offset < upper - lower
Proof
  rpt gen_tac
  >> eq_tac
  >- (strip_tac
      >> qexists_tac `value - lower : num`
      >> (CONJ_TAC THENL
            [ONCE_REWRITE_TAC [arithmeticTheory.ADD_COMM]
             >> simp[arithmeticTheory.SUB_ADD],
             Omega.OMEGA_TAC]))
  >> strip_tac
  >> rw[]
  >> (CONJ_TAC THENL
        [MATCH_ACCEPT_TAC
           (Q.SPECL [`lower : num`, `offset : num`]
              arithmeticTheory.LESS_EQ_ADD),
         ONCE_REWRITE_TAC [arithmeticTheory.ADD_COMM]
         >> irule
              (iffLR
                (Q.SPECL
                   [`offset : num`, `upper : num`, `lower : num`]
                   arithmeticTheory.SUB_LEFT_LESS))
         >> FIRST_ASSUM ACCEPT_TAC])
QED

Theorem source_num_offset_open_interval:
  !lower upper value : num.
    lower < value /\ value < upper <=>
    ?offset. value = SUC lower + offset /\
             offset < upper - SUC lower
Proof
  metis_tac
    [source_num_offset_interval, arithmeticTheory.LESS_EQ]
QED

Theorem source_num_offset_open_closed:
  !lower upper value : num.
    lower < value /\ value <= upper <=>
    ?offset. value = SUC lower + offset /\
             offset < upper - lower
Proof
  metis_tac
    [source_num_offset_interval, arithmeticTheory.LESS_EQ,
     arithmeticTheory.LT_SUC_LE, arithmeticTheory.SUB_MONO_EQ]
QED

Theorem source_num_offset_closed:
  !lower upper value : num.
    lower <= value /\ value <= upper <=>
    ?offset. value = lower + offset /\
             offset < SUC upper - lower
Proof
  metis_tac
    [source_num_offset_interval, arithmeticTheory.LT_SUC_LE]
QED

(* Isabelle/HOL src/HOL/Transitive_Closure.thy:1452-1497 and
   src/HOL/List.thy:8701-8703.  A set of pairs is represented by its
   characteristic, curried relation.  This is the executable code
   equation for ntrancl: paths of between one and SUC bound steps. *)
Definition source_list_relation_def:
  source_list_relation pairs left right = MEM (left, right) pairs
End

Definition source_ntrancl_def:
  (source_ntrancl 0 relation left right = relation left right) /\
  (source_ntrancl (SUC bound) relation left right =
     (source_ntrancl bound relation left right \/
      ?middle.
        source_ntrancl bound relation left middle /\
        relation middle right))
End

Theorem source_ntrancl_nrc:
  !bound relation left right.
    source_ntrancl bound relation left right <=>
    ?extra. extra <= bound /\
            arithmetic$NRC relation (SUC extra) left right
Proof
  Induct
  >- simp[source_ntrancl_def, arithmeticTheory.NRC_1]
  >> rw[source_ntrancl_def]
  >> eq_tac
  >- (strip_tac
      >- (qexists_tac `extra`
          >> simp[])
      >> qexists_tac `SUC extra`
      >> conj_tac
      >- simp[]
      >> simp[Once arithmeticTheory.NRC_SUC_RECURSE_LEFT]
      >> qexists_tac `middle`
      >> simp[])
  >> strip_tac
  >> Cases_on `extra <= bound`
  >- (disj1_tac
          >> qexists_tac `extra`
      >> simp[])
  >> `extra = SUC bound` by Omega.OMEGA_TAC
  >> disj2_tac
  >> fs[]
  >> qpat_x_assum
       `arithmetic$NRC relation (SUC (SUC bound)) left right`
       mp_tac
  >> simp[Once arithmeticTheory.NRC_SUC_RECURSE_LEFT]
  >> strip_tac
  >> qexists_tac `z`
  >> conj_tac
  >- (qexists_tac `bound`
      >> simp[])
  >> metis_tac[]
QED

Theorem source_lrc_append:
  !relation prefix suffix left right.
    list$LRC relation (prefix ++ suffix) left right <=>
    ?middle.
      list$LRC relation prefix left middle /\
      list$LRC relation suffix middle right
Proof
  gen_tac
  >> Induct
  >- simp[listTheory.LRC_def]
  >> simp[listTheory.LRC_def]
  >> metis_tac[]
QED

Theorem source_lrc_simple:
  !relation path left right.
    list$LRC relation path left right ==>
    ?simple.
      list$LRC relation simple left right /\
      ALL_DISTINCT simple /\
      LIST_TO_SET simple SUBSET LIST_TO_SET path /\
      (path <> [] ==> simple <> [])
Proof
  gen_tac
  >> Induct
  >- (simp[listTheory.LRC_def]
      >> metis_tac[])
  >> rw[listTheory.LRC_def]
  >> first_x_assum drule
  >> strip_tac
  >> Cases_on `MEM h simple`
  >- (`?prefix suffix. simple = prefix ++ h::suffix`
        by metis_tac[listTheory.MEM_SPLIT]
      >> qexists_tac `h::suffix`
      >> fs[source_lrc_append, listTheory.LRC_def]
      >> conj_tac
      >- metis_tac[]
      >> conj_tac
      >- fs[listTheory.ALL_DISTINCT_APPEND]
      >> fs[pred_setTheory.SUBSET_DEF])
  >> qexists_tac `h::simple`
  >> simp[listTheory.LRC_def]
  >> metis_tac[]
QED

Theorem source_lrc_edges:
  !relation path left right.
    list$LRC relation path left right ==>
    ?edges.
      MAP FST edges = path /\
      EVERY (\edge. relation (FST edge) (SND edge)) edges
Proof
  gen_tac
  >> Induct
  >- (simp[listTheory.LRC_def]
      >> metis_tac[])
  >> rw[listTheory.LRC_def]
  >> first_x_assum drule
  >> strip_tac
  >> qexists_tac `(h,z)::edges`
  >> simp[]
QED

Theorem source_lrc_list_relation_bound:
  !pairs path left right.
    list$LRC (source_list_relation pairs) path left right /\
    ALL_DISTINCT path ==>
    LENGTH path <= CARD (LIST_TO_SET pairs)
Proof
  rpt gen_tac
  >> strip_tac
  >> drule source_lrc_edges
  >> strip_tac
  >> `ALL_DISTINCT edges`
       by metis_tac[listTheory.ALL_DISTINCT_MAP]
  >> `LIST_TO_SET edges SUBSET LIST_TO_SET pairs`
       by (fs[listTheory.EVERY_MEM, source_list_relation_def,
              pred_setTheory.SUBSET_DEF]
           >> metis_tac[])
  >> `CARD (LIST_TO_SET edges) <= CARD (LIST_TO_SET pairs)`
       by metis_tac[pred_setTheory.CARD_SUBSET,
                    listTheory.FINITE_LIST_TO_SET]
  >> `LENGTH edges = LENGTH path`
       by metis_tac[listTheory.LENGTH_MAP]
  >> `CARD (LIST_TO_SET edges) = LENGTH edges`
       by metis_tac[listTheory.ALL_DISTINCT_CARD_LIST_TO_SET]
  >> Omega.OMEGA_TAC
QED

Theorem source_list_relation_set:
  !pairs.
    source_list_relation pairs =
    set_relation$reln_to_rel (LIST_TO_SET pairs)
Proof
  simp[FUN_EQ_THM, source_list_relation_def,
       set_relationTheory.reln_to_rel_def]
QED

Theorem source_lrc_finite_relation_bound:
  !pairs path left right.
    FINITE pairs ==>
    list$LRC (set_relation$reln_to_rel pairs) path left right /\
    ALL_DISTINCT path ==>
    LENGTH path <= CARD pairs
Proof
  rpt gen_tac
  >> strip_tac
  >> strip_tac
  >> drule source_lrc_edges
  >> strip_tac
  >> `ALL_DISTINCT edges`
       by metis_tac[listTheory.ALL_DISTINCT_MAP]
  >> `LIST_TO_SET edges SUBSET pairs`
       by (fs[listTheory.EVERY_MEM,
              set_relationTheory.reln_to_rel_def,
              pred_setTheory.SUBSET_DEF]
           >> metis_tac[])
  >> `CARD (LIST_TO_SET edges) <= CARD pairs`
       by metis_tac[pred_setTheory.CARD_SUBSET,
                    listTheory.FINITE_LIST_TO_SET]
  >> `LENGTH edges = LENGTH path`
       by metis_tac[listTheory.LENGTH_MAP]
  >> `CARD (LIST_TO_SET edges) = LENGTH edges`
       by metis_tac[listTheory.ALL_DISTINCT_CARD_LIST_TO_SET]
  >> Omega.OMEGA_TAC
QED

Theorem source_finite_tc_ntrancl:
  !pairs.
    FINITE pairs ==>
    relation$TC (set_relation$reln_to_rel pairs) =
    source_ntrancl (CARD pairs - 1)
      (set_relation$reln_to_rel pairs)
Proof
  rpt strip_tac
  >> simp[FUN_EQ_THM, EQ_IMP_THM]
  >> rpt gen_tac
  >> conj_tac
  >- (rpt strip_tac
      >> fs[arithmeticTheory.TC_eq_NRC]
      >> drule (iffLR listTheory.NRC_LRC)
      >> strip_tac
      >> drule source_lrc_simple
      >> strip_tac
      >> `ls <> []` by (Cases_on `ls` >> fs[])
      >> `simple <> []` by metis_tac[]
      >> qspecl_then [`pairs`, `simple`, `x`, `x'`]
           mp_tac source_lrc_finite_relation_bound
      >> simp[]
      >> strip_tac
      >> Cases_on `simple`
      >- fs[]
      >> rw[source_ntrancl_nrc]
      >> qexists_tac `LENGTH t`
      >> conj_tac
      >- (fs[] >> Omega.OMEGA_TAC)
      >> simp[listTheory.NRC_LRC]
      >> qexists_tac `h::t`
      >> simp[])
  >> rpt strip_tac
  >> fs[source_ntrancl_nrc, arithmeticTheory.TC_eq_NRC]
  >> qexists_tac `extra`
  >> metis_tac[]
QED

Theorem source_trancl_set_ntrancl:
  !pairs.
    relation$TC (source_list_relation pairs) =
    source_ntrancl (CARD (LIST_TO_SET pairs) - 1)
      (source_list_relation pairs)
Proof
  gen_tac
  >> simp[FUN_EQ_THM, EQ_IMP_THM]
  >> rpt gen_tac
  >> conj_tac
  >- (rpt strip_tac
      >> fs[arithmeticTheory.TC_eq_NRC]
      >> drule (iffLR listTheory.NRC_LRC)
      >> strip_tac
      >> drule source_lrc_simple
      >> strip_tac
      >> `ls <> []` by (Cases_on `ls` >> fs[])
      >> `simple <> []` by metis_tac[]
      >> drule source_lrc_list_relation_bound
      >> impl_tac
      >- simp[]
      >> strip_tac
      >> Cases_on `simple`
      >- fs[]
      >> rw[source_ntrancl_nrc]
      >> qexists_tac `LENGTH t`
      >> conj_tac
      >- (fs[] >> Omega.OMEGA_TAC)
      >> simp[listTheory.NRC_LRC]
      >> qexists_tac `h::t`
      >> simp[])
  >> rpt strip_tac
  >> fs[source_ntrancl_nrc, arithmeticTheory.TC_eq_NRC]
  >> qexists_tac `extra`
  >> metis_tac[]
QED

Theorem source_abort_cong:
  !message message' function.
    message = message' ==>
    source_abort message function = source_abort message' function
Proof
  simp[source_abort_def]
QED

(* src/HOL/Option.thy uses option.split as a local simplifier split rule. *)
Theorem source_option_split:
  !predicate value none_case some_case.
    predicate (option_CASE value none_case some_case) <=>
    ((value = NONE ==> predicate none_case) /\
     !item. value = SOME item ==> predicate (some_case item))
Proof
  rpt gen_tac
  >> Cases_on `value`
  >> simp[]
QED

(* src/HOL/Option.thy: map_option_case. *)
Theorem source_map_option_case:
  !function value.
    OPTION_MAP function value =
    option_CASE value NONE (\item. SOME (function item))
Proof
  rpt gen_tac
  >> Cases_on `value`
  >> simp[]
QED

(* src/HOL/Option.thy: rel_option_iff. *)
Theorem source_rel_option_iff:
  !relation left right.
    OPTREL relation left right <=>
    UNCURRY
      (\left_option right_option.
         option_CASE left_option
           (option_CASE right_option T (\right_item. F))
           (\left_item.
              option_CASE right_option F
                (\right_item. relation left_item right_item)))
      (left,right)
Proof
  rpt gen_tac
  >> Cases_on `left`
  >> Cases_on `right`
  >> simp[optionTheory.OPTREL_def]
QED

(* src/HOL/Option.thy: rel_option_unfold. *)
Theorem source_rel_option_unfold:
  !relation left right.
    OPTREL relation left right <=>
    ((IS_NONE left <=> IS_NONE right) /\
     (~IS_NONE left ==>
      ~IS_NONE right ==>
      relation (THE left) (THE right)))
Proof
  rpt gen_tac
  >> Cases_on `left`
  >> Cases_on `right`
  >> simp[optionTheory.OPTREL_def]
QED

(* src/HOL/Option.thy: these_empty_eq. *)
Theorem source_these_empty_eq:
  !source : 'a option set.
    ((\item. SOME item IN source) = {}) <=>
    (source = {} \/ source = {NONE})
Proof
  gen_tac
  >> simp[pred_setTheory.EXTENSION, optionTheory.FORALL_OPTION]
  >> metis_tac[]
QED

Theorem source_no_some_member_none:
  !source value.
    value IN source ==>
    (!item. SOME item NOTIN source) ==>
    NONE IN source
Proof
  rpt gen_tac
  >> Cases_on `value`
  >> simp[]
  >> metis_tac[]
QED

(* src/HOL/String.thy: card_image on the character representation. *)
Theorem source_chr_inj_count:
  !limit left right.
    limit <= 256 ==>
    left IN count limit ==>
    right IN count limit ==>
    CHR left = CHR right ==>
    left = right
Proof
  rpt strip_tac
  >> fs[]
  >> `left < 256 /\ right < 256` by Omega.OMEGA_TAC
  >> metis_tac[stringTheory.CHR_11]
QED

Theorem source_card_image_chr_count:
  !limit.
    limit <= 256 ==>
    CARD (IMAGE CHR (count limit)) = limit
Proof
  rpt strip_tac
  >> `CARD (IMAGE CHR (count limit)) = CARD (count limit)` by
       (match_mp_tac pred_setTheory.CARD_IMAGE_INJ
        >> conj_tac
        >- metis_tac[source_chr_inj_count]
        >> simp[])
  >> simp[]
QED

(* src/HOL/List.thy uses list.split as a local simplifier split rule. *)
Theorem source_list_split:
  !predicate value nil_case cons_case.
    predicate (list_CASE value nil_case cons_case) <=>
    ((value = [] ==> predicate nil_case) /\
     !head tail. value = head::tail ==>
       predicate (cons_case head tail))
Proof
  rpt gen_tac
  >> Cases_on `value`
  >> simp[]
QED

(* src/HOL/List.thy: neq_Nil_conv. *)
Theorem source_neq_nil_conv:
  !items : 'a list.
    items <> [] <=> ?head tail. items = head::tail
Proof
  Cases
  >> simp[]
QED

(* src/HOL/Set.thy uses bool_induct as an introduction rule. *)
Theorem source_bool_induct:
  !predicate value.
    predicate T ==>
    predicate F ==>
    predicate value
Proof
  rpt gen_tac
  >> Cases_on `value`
  >> simp[]
QED

(* src/HOL/Set.thy: bool_contrapos. *)
Theorem source_bool_contrapos:
  !predicate value.
    predicate value ==>
    ~predicate F ==>
    predicate T
Proof
  rpt gen_tac
  >> Cases_on `value`
  >> simp[]
QED

(* Boolean datatype exhaustion in destructor form. *)
Theorem source_exists_bool_cases:
  !predicate.
    (?value : bool. predicate value) ==>
    predicate T \/ predicate F
Proof
  rpt strip_tac
  >> Cases_on `value`
  >> simp[]
QED

(* src/HOL/Option.thy: UNIV_option_conv. *)
Theorem source_UNIV_option_conv:
  (UNIV : 'a option set) =
  NONE INSERT IMAGE SOME (UNIV : 'a set)
Proof
  simp[pred_setTheory.EXTENSION, optionTheory.FORALL_OPTION]
QED

(* src/HOL/Set.thy uses conj_cong as a local simplifier congruence. *)
Theorem source_conj_cong:
  !left left' right right'.
    (left <=> left') ==>
    (left' ==> (right <=> right')) ==>
    (left /\ right <=> left' /\ right')
Proof
  metis_tac[]
QED

Theorem source_rev_conj_cong:
  !left left' right right'.
    (right <=> right') ==>
    (right' ==> (left <=> left')) ==>
    (left /\ right <=> left' /\ right')
Proof
  metis_tac[]
QED

(* src/HOL/Set.thy: Uniq_def. *)
Theorem source_unique_member_transfer:
  !family left right shared query.
    (!element first second.
       (family first /\ first element) /\
       family second /\ second element ==>
       !candidate. first candidate = second candidate) ==>
    family left ==>
    family right ==>
    left shared ==>
    right shared ==>
    left query ==>
    right query
Proof
  metis_tac[]
QED

Theorem source_set_zip:
  !xs ys.
    LIST_TO_SET (ZIP (xs, ys)) =
    (\pair.
       ?index.
         pair = (EL index xs, EL index ys) /\
         index < MIN (LENGTH xs) (LENGTH ys))
Proof
  simpLib.SIMP_TAC (clasimpLib.clasimp_ss ())
    [pred_setTheory.EXTENSION, pred_setTheory.IN_ABS,
     pairTheory.FORALL_PROD, source_set_conv_nth,
     listTheory.LENGTH_ZIP_MIN, source_el_zip_min,
     source_fst_el_zip_min, source_snd_el_zip_min,
     simpLib.Cong source_rev_conj_cong]
QED

(* Isabelle/HOL src/HOL/Product_Type.thy:1005 [Sigma], a plain
   definition.  It is a constant there and a method reaches its body
   only by naming [Sigma_def]; the corpus carried the body instead,
   which handed every Sigma goal an unfolding its source proof never
   saw.  Stated at two arguments, as Isabelle states it.  [Times] is an
   abbreviation for [Sigma A (\_. B)] and stays inlined, as Isabelle
   inlines it. *)
Definition source_Sigma_def:
  source_Sigma domain fibre =
    \pair. FST pair IN domain /\ SND pair IN fibre (FST pair)
End

(* src/HOL/Product_Type.thy:1027 [SigmaI], declared [intro!], and :1030
   [SigmaE], declared [elim!] -- the pair Isabelle's classical search
   reads about the constant without naming it.  Between them they are
   the whole of what a claset knows about a Sigma: one builds a member
   from its two components and the other takes a member apart into
   them, naming the equation that says the member is that pair. *)
Theorem source_SigmaI:
  !domain fibre first second.
    first IN domain ==>
    second IN fibre first ==>
    (first,second) IN source_Sigma domain fibre
Proof
  rw[source_Sigma_def, boolTheory.IN_DEF]
QED

Theorem source_SigmaE:
  !domain fibre member consequence.
    member IN source_Sigma domain fibre ==>
    (!first second.
       first IN domain ==>
       second IN fibre first ==>
       member = (first,second) ==>
       consequence) ==>
    consequence
Proof
  rw[source_Sigma_def, boolTheory.IN_DEF]
  >> first_x_assum (qspecl_then [`FST member`, `SND member`] mp_tac)
  >> simp[pairTheory.PAIR]
QED

(* src/HOL/Product_Type.thy:1069 [mem_Sigma_iff], declared [iff].  It is
   what Isabelle's simpset reads about a [Sigma] whose definition it
   withholds: the membership of a pair literal, and of nothing else. *)
Theorem source_mem_Sigma_iff:
  !first second domain fibre.
    (first,second) IN source_Sigma domain fibre <=>
    first IN domain /\ second IN fibre first
Proof
  rw[source_Sigma_def, boolTheory.IN_DEF]
QED

(* src/HOL/Product_Type.thy:1238 [Product_Type.product], a qualified
   definition standing for [A * B].  It is a constant there and
   [member_product] is proved by naming [product_def]; the corpus
   carried the body instead, and unfolded past [Sigma] at that, which
   left the lemma stating a Sigma against its own unfolding while every
   other [*] in the corpus kept the constant. *)
Definition source_product_def:
  source_product left right = source_Sigma left (\unused. right)
End

(* src/HOL/Product_Type.thy: unique pair selection used by The_split_eq. *)
Theorem source_choice_unique_pair:
  !predicate first second.
    (!left right.
       predicate left right <=> first = left /\ second = right) ==>
    CHOICE (UNCURRY predicate) = (first, second)
Proof
  rpt strip_tac >>
  `UNCURRY predicate = {(first, second)}` by
    (simp[pred_setTheory.EXTENSION, pairTheory.FORALL_PROD,
          pairTheory.PAIR_EQ] >>
     metis_tac[]) >>
  simp[]
QED

(* src/HOL/Product_Type.thy: pair-predicate monotonicity. *)
Theorem source_uncurry_subset_mono:
  !pairs predicate consequence.
    (!left.
       left IN IMAGE FST pairs ==>
       !right.
         right IN IMAGE SND pairs ==>
         predicate left right ==>
         consequence left right) ==>
    pairs SUBSET UNCURRY predicate ==>
    pairs SUBSET UNCURRY consequence
Proof
  simp[pred_setTheory.SUBSET_DEF, pred_setTheory.IN_IMAGE,
       pairTheory.FORALL_PROD] >>
  metis_tac[pairTheory.FST, pairTheory.SND]
QED

Theorem source_pair_map_inj:
  !left_map right_map left_domain right_domain left_range right_range.
    INJ left_map left_domain left_range ==>
    INJ right_map right_domain right_range ==>
    INJ
      (\pair. (left_map (FST pair), right_map (SND pair)))
      (\pair.
         FST pair IN left_domain /\ SND pair IN right_domain)
      (\pair.
         FST pair IN left_range /\ SND pair IN right_range)
Proof
  simp[pred_setTheory.INJ_DEF, pairTheory.FORALL_PROD,
       pairTheory.PAIR_EQ] >>
  metis_tac[]
QED

Theorem source_pair_map_surj:
  !left_map right_map left_domain right_domain left_range right_range.
    SURJ left_map left_domain left_range ==>
    SURJ right_map right_domain right_range ==>
    SURJ
      (\pair. (left_map (FST pair), right_map (SND pair)))
      (\pair.
         FST pair IN left_domain /\ SND pair IN right_domain)
      (\pair.
         FST pair IN left_range /\ SND pair IN right_range)
Proof
  simp[pred_setTheory.SURJ_DEF, pairTheory.FORALL_PROD,
       pairTheory.EXISTS_PROD] >>
  metis_tac[]
QED

Theorem source_bij_intro:
  !function domain range.
    INJ function domain range ==>
    SURJ function domain range ==>
    BIJ function domain range
Proof
  metis_tac[pred_setTheory.BIJ_DEF]
QED

Theorem source_bij_components:
  !function domain range.
    BIJ function domain range ==>
    INJ function domain range /\ SURJ function domain range
Proof
  metis_tac[pred_setTheory.BIJ_DEF]
QED

(* src/HOL/Set.thy: membership in a union of an indexed image. *)
Theorem source_mem_bigunion_image:
  !element family indices.
    (element IN BIGUNION (IMAGE family indices) <=>
     ?index. index IN indices /\ element IN family index)
Proof
  simp[pred_setTheory.IN_BIGUNION, pred_setTheory.IN_IMAGE] >>
  metis_tac[]
QED

Theorem source_exists_swapped_conj:
  !first second tail.
    ((?item. first item /\ second item) /\ tail <=>
     ?item. second item /\ first item /\ tail)
Proof
  metis_tac[]
QED

(* src/HOL/Set.thy: subset_imageE. *)
Theorem source_subset_imageE:
  !function source target conclusion.
    source SUBSET IMAGE function target ==>
    (!preimage.
       preimage SUBSET target ==>
       source = IMAGE function preimage ==>
       conclusion) ==>
    conclusion
Proof
  metis_tac[pred_setTheory.SUBSET_IMAGE]
QED

(* src/HOL/Set.thy: equalityE.  SET_EQ_SUBSET states the same content as
   an equivalence, which the claset cannot take as an elimination rule;
   the corpus goals that name this fact need its rule shape. *)
Theorem source_equalityE:
  !left right conclusion.
    left = right ==>
    (left SUBSET right ==> right SUBSET left ==> conclusion) ==>
    conclusion
Proof
  metis_tac[pred_setTheory.SUBSET_REFL]
QED

(* Isabelle's le_funE, named by the method of Product_Type.thy:1097.  The
   order on a function into sets is pointwise, so the rule reads an
   inclusion at one argument out of the pointwise hypothesis; SUBSET_DEF
   is about membership and cannot serve as that elimination. *)
Theorem source_le_funE:
  !smaller larger item conclusion.
    (!index. smaller index SUBSET larger index) ==>
    (smaller item SUBSET larger item ==> conclusion) ==>
    conclusion
Proof
  metis_tac[]
QED

(* Explicit, reusable preimage construction for subsets of an image. *)
Theorem source_subset_image_witness:
  !function source target.
    source SUBSET IMAGE function target ==>
    ?preimage.
      preimage SUBSET target /\
      source = IMAGE function preimage
Proof
  metis_tac[pred_setTheory.SUBSET_IMAGE]
QED

Theorem source_subset_image_witness_iff:
  !function source target.
    ((?preimage.
        preimage SUBSET target /\
        source = IMAGE function preimage) <=>
     source SUBSET IMAGE function target)
Proof
  metis_tac[pred_setTheory.SUBSET_IMAGE]
QED

(* The pointwise normal form of the same construction.  Keeping this as a
   predicate theorem lets extensional simplification use it after set and
   IMAGE notation have already been eliminated. *)
Theorem source_subset_image_pointwise_witness_iff:
  !function source target.
    ((?preimage.
        ((!element.
            source element ==>
            ?preimage_element.
              element = function preimage_element /\
              preimage preimage_element) /\
         (!preimage_element.
            preimage preimage_element ==>
            source (function preimage_element))) /\
        (!preimage_element.
           preimage preimage_element ==>
           target preimage_element)) <=>
     (!element.
        source element ==>
        ?preimage_element.
          element = function preimage_element /\
          target preimage_element))
Proof
  rpt gen_tac
  >> eq_tac
  >- metis_tac[]
  >> strip_tac
  >> qexists_tac
       `\preimage_element.
          target preimage_element /\
          source (function preimage_element)`
  >> simp[]
  >> metis_tac[]
QED

(* src/HOL/List.thy: rev_swap. *)
Theorem source_rev_swap:
  !xs ys.
    REVERSE xs = ys <=> xs = REVERSE ys
Proof
  metis_tac[listTheory.REVERSE_REVERSE]
QED

(* src/HOL/List.thy: split_list. *)
Theorem source_split_list:
  !item items.
    MEM item items ==>
    ?prefix suffix.
      items = prefix ++ item::suffix
Proof
  metis_tac[listTheory.MEM_SPLIT]
QED

(* src/HOL/List.thy: split_list_first and split_list_last. *)
Theorem source_split_list_first:
  !item items.
    MEM item items ==>
    ?prefix suffix.
      items = prefix ++ item::suffix /\
      ~MEM item prefix
Proof
  rpt gen_tac
  >> strip_tac
  >> drule_then strip_assume_tac
       (iffLR listTheory.MEM_SPLIT_APPEND_first)
  >> fs[]
  >> metis_tac[]
QED

Theorem source_split_list_last:
  !item items.
    MEM item items ==>
    ?prefix suffix.
      items = prefix ++ item::suffix /\
      ~MEM item suffix
Proof
  rpt gen_tac
  >> strip_tac
  >> drule_then strip_assume_tac
       (iffLR listTheory.MEM_SPLIT_APPEND_last)
  >> fs[]
  >> metis_tac[]
QED

(* src/HOL/List.thy: split_list_prop. *)
Theorem source_split_list_prop:
  !items predicate.
    (?item. MEM item items /\ predicate item) ==>
    ?prefix item suffix.
      items = prefix ++ item::suffix /\ predicate item
Proof
  metis_tac[listTheory.MEM_SPLIT]
QED

(* src/HOL/List.thy: split_list_first_prop. *)
Theorem source_split_list_first_prop:
  !items predicate.
    (?item. MEM item items /\ predicate item) ==>
    ?prefix item suffix.
      items = prefix ++ item::suffix /\
      predicate item /\
      (!earlier. MEM earlier prefix ==> ~predicate earlier)
Proof
  gen_tac
  >> Induct_on `items`
  >- simp[]
  >> rpt gen_tac
  >> Cases_on `predicate h`
  >- (strip_tac
      >> map_every qexists_tac [`[]`, `h`, `items`]
      >> simp[])
  >> strip_tac
  >> qpat_x_assum `!predicate. _`
       (qspec_then `predicate` mp_tac)
  >> impl_tac
  >- (qexists_tac `item`
      >> conj_tac
      >- (Cases_on `item = h` >> fs[])
      >> fs[])
  >> strip_tac
  >> rename [`items = prefix ++ chosen::suffix`]
  >> map_every qexists_tac [`h::prefix`, `chosen`, `suffix`]
  >> simp[]
  >> metis_tac[]
QED

(* src/HOL/List.thy: split_list_last_prop. *)
Theorem source_split_list_last_prop:
  !items predicate.
    (?item. MEM item items /\ predicate item) ==>
    ?prefix item suffix.
      items = prefix ++ item::suffix /\
      predicate item /\
      (!later. MEM later suffix ==> ~predicate later)
Proof
  gen_tac
  >> Induct_on `items`
  >- simp[]
  >> rpt gen_tac
  >> Cases_on `?item. MEM item items /\ predicate item`
  >- (strip_tac
      >> qpat_x_assum `!predicate. _`
           (qspec_then `predicate` mp_tac)
      >> impl_tac
      >- simp[]
      >> strip_tac
      >> rename [`items = prefix ++ chosen::suffix`]
      >> map_every qexists_tac [`h::prefix`, `chosen`, `suffix`]
      >> simp[])
  >> strip_tac
  >> map_every qexists_tac [`[]`, `h`, `items`]
  >> fs[]
  >> metis_tac[]
QED

(* src/HOL/List.thy: map_inj_on and map_injective. *)
Theorem source_map_inj_on:
  !function xs ys.
    MAP function xs = MAP function ys ==>
    INJ function (LIST_TO_SET xs UNION LIST_TO_SET ys) UNIV ==>
    xs = ys
Proof
  metis_tac[listTheory.INJ_MAP_EQ]
QED

Theorem source_map_injective:
  !function xs ys.
    MAP function xs = MAP function ys ==>
    INJ function UNIV UNIV ==>
    xs = ys
Proof
  metis_tac[listTheory.INJ_MAP_EQ,
            pred_setTheory.INJ_SUBSET_UNIV]
QED

(* src/HOL/List.thy: inj_mapI and inj_mapD. *)
Theorem source_inj_mapI:
  !function.
    INJ function UNIV UNIV ==>
    INJ (MAP function) UNIV UNIV
Proof
  rpt gen_tac
  >> strip_tac
  >> simp[pred_setTheory.INJ_DEF]
  >> rpt strip_tac
  >> match_mp_tac (Q.SPEC `function` listTheory.INJ_MAP_EQ)
  >> conj_tac
  >- (irule pred_setTheory.INJ_SUBSET_UNIV
      >> FIRST_ASSUM ACCEPT_TAC)
  >> FIRST_ASSUM ACCEPT_TAC
QED

Theorem source_inj_mapD:
  !function.
    INJ (MAP function) UNIV UNIV ==>
    INJ function UNIV UNIV
Proof
  simp[pred_setTheory.INJ_DEF]
  >> rpt strip_tac
  >> rename [`function left = function right`]
  >> qpat_x_assum
       `!xs ys. MAP function xs = MAP function ys ==> xs = ys`
       (qspecl_then [`[left]`, `[right]`] mp_tac)
  >> simp[]
QED

(* src/HOL/Set.thy: inj_onI and inj_onD. *)
Theorem source_inj_onI:
  !function source.
    (!left right.
       left IN source ==>
       right IN source ==>
       function left = function right ==>
       left = right) ==>
    INJ function source UNIV
Proof
  simp[pred_setTheory.INJ_DEF]
QED

Theorem source_inj_onD:
  !function source left right.
    INJ function source UNIV ==>
    left IN source ==>
    right IN source ==>
    function left = function right ==>
    left = right
Proof
  metis_tac[pred_setTheory.INJ_DEF]
QED

(* src/HOL/List.thy: Cons_eq_append_conv. *)
Theorem source_Cons_eq_append_conv:
  !head tail left right.
    (head::tail = left ++ right <=>
     left = [] /\ head::tail = right \/
     ?left_tail.
       head::left_tail = left /\ tail = left_tail ++ right)
Proof
  Cases_on `left`
  >> simp[]
QED

(* src/HOL/List.thy: concat_eq_concat_iff. *)
Theorem source_concat_eq_concat_iff:
  !xs ys.
    (!pair.
       pair IN LIST_TO_SET (ZIP (xs, ys)) ==>
       UNCURRY (\left right. LENGTH left = LENGTH right) pair) ==>
    LENGTH xs = LENGTH ys ==>
    (FLAT xs = FLAT ys <=> xs = ys)
Proof
  Induct
  >> Cases_on `ys`
  >> simp[boolTheory.DISJ_IMP_THM,
          boolTheory.FORALL_AND_THM,
          listTheory.APPEND_11_LENGTH]
QED

Theorem source_concat_eq_concat_iff_curried:
  !xs ys.
    (!left right.
       (left, right) IN LIST_TO_SET (ZIP (xs, ys)) ==>
       LENGTH left = LENGTH right) ==>
    LENGTH xs = LENGTH ys ==>
    (FLAT xs = FLAT ys <=> xs = ys)
Proof
  Induct
  >> Cases_on `ys`
  >> simp[boolTheory.DISJ_IMP_THM,
          boolTheory.FORALL_AND_THM,
          listTheory.APPEND_11_LENGTH]
QED

(* src/HOL/List.thy: concat_eq_appendD. *)
Theorem source_concat_eq_appendD:
  !xss ys zs.
    FLAT xss = ys ++ zs ==>
    xss <> [] ==>
    ?xss1 xs xs' xss2.
      xss = xss1 ++ (xs ++ xs')::xss2 /\
      ys = FLAT xss1 ++ xs /\
      zs = xs' ++ FLAT xss2
Proof
  rpt gen_tac
  >> strip_tac
  >> qpat_x_assum `FLAT xss = ys ++ zs` mp_tac
  >> simp[listTheory.FLAT_EQ_APPEND]
  >> strip_tac
  >> strip_tac
  >- (Cases_on `p` using listTheory.SNOC_CASES
      >- (fs[]
          >> Cases_on `s`
          >> fs[]
          >> map_every qexists_tac [`[]`, `h`, `t`]
          >> simp[])
      >> fs[listTheory.SNOC_APPEND]
      >> map_every qexists_tac [`l`, `x`, `[]`, `s`]
      >> simp[])
  >> map_every qexists_tac [`p`, `ip`, `is`, `s`]
  >> simp[]
QED

(* src/HOL/List.thy: filter_eq_ConsD. *)
Theorem source_filter_eq_ConsD:
  !predicate items head tail.
    FILTER predicate items = head::tail ==>
    ?prefix suffix.
      items = prefix ++ head::suffix /\
      (!item. MEM item prefix ==> ~predicate item) /\
      predicate head /\
      tail = FILTER predicate suffix
Proof
  rpt gen_tac
  >> strip_tac
  >> drule_then strip_assume_tac
       (iffLR listTheory.FILTER_EQ_CONS)
  >> rename [`items = prefix ++ [head] ++ suffix`]
  >> qexists_tac `prefix`
  >> qexists_tac `suffix`
  >> fs[listTheory.FILTER_EQ_NIL,
        listTheory.EVERY_MEM]
QED

Theorem source_filter_eq_ConsI:
  !predicate items head tail prefix suffix.
    items = prefix ++ head::suffix ==>
    (!item. MEM item prefix ==> ~predicate item) ==>
    predicate head ==>
    tail = FILTER predicate suffix ==>
    FILTER predicate items = head::tail
Proof
  rpt strip_tac >>
  fs[listTheory.FILTER_APPEND_DISTRIB, listTheory.FILTER_EQ_NIL,
     listTheory.EVERY_MEM]
QED

(* src/HOL/List.thy: Diff_eq [symmetric] and minus_set_fold. *)
Theorem source_Diff_eq_symmetric:
  !left right.
    left INTER COMPL right = left DIFF right
Proof
  simp[pred_setTheory.EXTENSION,
       pred_setTheory.DIFF_DEF]
QED

Theorem source_fold_delete_commute:
  !items source item.
    FOLDR (\removed result. result DELETE removed)
      (source DELETE item) items =
    FOLDR (\removed result. result DELETE removed)
      source items DELETE item
Proof
  Induct
  >> simp[pred_setTheory.DELETE_COMM]
QED

Theorem source_minus_set_fold:
  !items source.
    source DIFF LIST_TO_SET items =
    FOLDR (\item result. result DELETE item) source items
Proof
  Induct
  >> simp[pred_setTheory.DIFF_INSERT,
          source_fold_delete_commute]
QED

Theorem source_mem_fold_delete:
  !items source value.
    FOLDR (\item result. result DELETE item) source items value <=>
    value IN source /\ ~MEM value items
Proof
  Induct
  >> simp[pred_setTheory.SPECIFICATION,
          pred_setTheory.IN_DELETE]
  >> metis_tac[]
QED

(* src/HOL/List.thy: upt_rec and upt_conv_Cons.  Isabelle's half-open
   interval [start..<finish] is represented by the GENLIST expression
   below throughout the executable corpus. *)
(* src/HOL/List.thy: upt_Suc_append.  The interval is written
   [$+ start], the eta-contracted form the goals arrive in. *)
Theorem source_upt_suc_append:
  !start finish.
    start <= finish ==>
    GENLIST ($+ start) (SUC finish - start) =
    GENLIST ($+ start) (finish - start) ++ [finish]
Proof
  rpt strip_tac
  >> `SUC finish - start = SUC (finish - start)` by decide_tac
  >> simp[listTheory.GENLIST, listTheory.SNOC_APPEND]
QED

Theorem source_upt_rec:
  !start finish.
    GENLIST (\offset. start + offset) (finish - start) =
    if start < finish then
      start ::
        GENLIST (\offset. SUC start + offset) (finish - SUC start)
    else []
Proof
  rpt gen_tac
  >> Cases_on `start < finish`
  >- (`finish - start = SUC (finish - SUC start)` by decide_tac
      >> SRW_TAC[ARITH_ss]
           [listTheory.GENLIST_CONS, listTheory.GENLIST_FUN_EQ])
  >> `finish - start = 0` by decide_tac
  >> simp[]
QED

(* src/HOL/List.thy declares [distinct_upt] (:3788), [take_upt] (:3478)
   and [drop_upt] (:3485) simp, so a source proof that takes an interval
   apart or asks whether one repeats never names them.  HOL4's own
   [ALL_DISTINCT_GENLIST] is an injectivity condition rather than a
   fact, and its list library carries no law at all for a prefix or a
   suffix of an interval; each of the three is stated here in the
   eta-contracted [$+ start] form the goals arrive in. *)
Theorem source_distinct_upt:
  !start length. ALL_DISTINCT (GENLIST ($+ start) length)
Proof
  rw[listTheory.ALL_DISTINCT_GENLIST]
QED

Theorem source_take_upt:
  !start amount length.
    amount <= length ==>
    TAKE amount (GENLIST ($+ start) length) = GENLIST ($+ start) amount
Proof
  rpt strip_tac
  >> `MIN amount length = amount`
       by (rw[arithmeticTheory.MIN_DEF] >> decide_tac)
  >> simp[listTheory.TAKE_GENLIST]
QED

Theorem source_drop_upt:
  !start amount length.
    DROP amount (GENLIST ($+ start) length) =
    GENLIST ($+ (start + amount)) (length - amount)
Proof
  rw[listTheory.DROP_GENLIST, combinTheory.o_DEF,
     listTheory.GENLIST_FUN_EQ]
  >> decide_tac
QED

Theorem source_tl_num_genlist:
  !start length.
    TL (GENLIST (\offset. start + offset) length) =
    GENLIST (\offset. SUC start + offset) (PRE length)
Proof
  rpt gen_tac
  >> Cases_on `length`
  >- simp[]
  >> simp[listTheory.TL_GENLIST, listTheory.GENLIST_FUN_EQ,
          combinTheory.o_DEF]
QED

(* src/HOL/List.thy: le_Suc_eq and length_Suc_conv at the one-element
   boundary. *)
Theorem source_length_le_one:
  !items : 'a list.
    LENGTH items <= 1 <=>
    items = [] \/ ?item. items = [item]
Proof
  Cases_on `items`
  >> simp[]
  >> Cases_on `t`
  >> simp[]
QED

(* src/HOL/ex/Set_Theory.thy: singleton witnesses used by force. *)
Theorem source_predicate_set_witness:
  !predicate witness.
    predicate witness ==>
    ?aset.
      (!item. item IN aset ==> predicate item) /\
      witness IN aset
Proof
  rpt strip_tac
  >> qexists_tac `{witness}`
  >> simp[]
QED

Theorem source_nonempty_predicate_set:
  !predicate.
    ((?aset.
        (!item. item IN aset ==> predicate item) /\
        ?witness. witness IN aset) <=>
     ?witness. predicate witness)
Proof
  gen_tac
  >> eq_tac
  >- metis_tac[]
  >> strip_tac
  >> qexists_tac `{witness}`
  >> simp[]
QED

Theorem source_set_separates_image:
  !element forbidden.
    ((?aset.
        element IN aset /\
        !index. forbidden index NOTIN aset) <=>
     !index. element <> forbidden index)
Proof
  rpt gen_tac
  >> eq_tac
  >- metis_tac[]
  >> strip_tac
  >> qexists_tac `{element}`
  >> simp[]
QED

Theorem source_nonnegative_neq_negative:
  !nonnegative negative : int.
    0 <= nonnegative ==>
    negative < 0 ==>
    nonnegative <> negative
Proof
  intLib.ARITH_TAC
QED

Theorem source_set_separates_two:
  !left element right.
    ((?aset.
        left NOTIN aset /\
        element IN aset /\
        right NOTIN aset) <=>
     left <> element /\ right <> element)
Proof
  rpt gen_tac
  >> eq_tac
  >- metis_tac[]
  >> strip_tac
  >> qexists_tac `{element}`
  >> simp[]
QED

Theorem source_exists_not_member:
  !element. (?aset. element NOTIN aset) <=> T
Proof
  gen_tac
  >> eq_tac
  >- simp[]
  >> strip_tac
  >> qexists_tac `{}`
  >> simp[]
QED

Theorem source_exists_singleton_superset:
  !sets.
    ((?element. sets SUBSET {element}) <=>
     !left right.
       left IN sets /\ right IN sets ==>
       left = right)
Proof
  gen_tac
  >> eq_tac
  >- (simp[pred_setTheory.SUBSET_DEF] >> metis_tac[])
  >> strip_tac
  >> Cases_on `sets = {}`
  >- (qexists_tac `ARB` >> simp[])
  >> `?element. element IN sets` by
       metis_tac[pred_setTheory.MEMBER_NOT_EMPTY]
  >> qexists_tac `element`
  >> simp[pred_setTheory.SUBSET_DEF]
  >> metis_tac[]
QED

Theorem source_set_equality_elim:
  !left right.
    left = right ==>
    left SUBSET right /\ right SUBSET left
Proof
  simp[]
QED

Theorem source_unique_subset:
  !universe unique.
    (!candidate. candidate SUBSET universe ==> candidate = unique) <=>
    universe = {} /\ unique = {}
Proof
  rpt gen_tac
  >> eq_tac
  >- (strip_tac
      >> qpat_x_assum `!candidate. _`
           (fn theorem =>
              mp_tac (Q.SPEC `universe` theorem) >>
              mp_tac (Q.SPEC `{}` theorem))
      >> simp[])
  >> simp[]
QED

Theorem source_unique_subset_iff:
  !universe unique.
    (!candidate. candidate SUBSET universe <=> candidate = unique) <=>
    universe = {} /\ unique = {}
Proof
  rpt gen_tac
  >> eq_tac
  >- metis_tac[source_unique_subset]
  >> simp[]
QED

Theorem source_unique_predicate_subset_iff:
  !universe unique.
    (!candidate.
       (!element. candidate element ==> universe element) <=>
       candidate = unique) <=>
    universe = {} /\ unique = {}
Proof
  rpt gen_tac
  >> eq_tac
  >- (strip_tac
      >> qpat_x_assum `!candidate. _`
           (fn theorem =>
              mp_tac (Q.SPEC `universe` theorem) >>
              mp_tac (Q.SPEC `{}` theorem))
      >> simp[])
  >> simp[boolTheory.FUN_EQ_THM]
  >> metis_tac[]
QED

Theorem source_powerset_extensional:
  !universe collection.
    POW universe = collection <=>
    !candidate. candidate SUBSET universe <=> candidate IN collection
Proof
  simp[pred_setTheory.EXTENSION, pred_setTheory.IN_POW]
QED

Theorem source_forall_iffD1:
  !predicate other item.
    (!candidate. predicate candidate <=> other candidate) ==>
    predicate item ==>
    other item
Proof
  metis_tac[]
QED

Theorem source_forall_iffD2:
  !predicate other item.
    (!candidate. predicate candidate <=> other candidate) ==>
    other item ==>
    predicate item
Proof
  metis_tac[]
QED

Theorem source_complement_exI:
  !value predicate.
    predicate (COMPL value) ==>
    ?witness.
      value = COMPL witness /\ predicate witness
Proof
  rpt strip_tac
  >> qexists_tac `COMPL value`
  >> simp[]
QED

(* Difference retains its left operand exactly when the operands are
   disjoint.  This is a reusable normalization boundary between set
   constructors and the disjointness rules. *)
Theorem source_diff_eq_self_iff_disjoint:
  !left right.
    left DIFF right = left <=>
    DISJOINT left right
Proof
  simp[pred_setTheory.EXTENSION, pred_setTheory.DISJOINT_DEF]
  >> metis_tac[]
QED

Theorem source_complement_witness_iff:
  !value predicate.
    ((?witness.
        value = COMPL witness /\ predicate witness) <=>
     predicate (COMPL value))
Proof
  rpt gen_tac
  >> eq_tac
  >- (rpt strip_tac >> fs[])
  >> strip_tac
  >> qexists_tac `COMPL value`
  >> simp[]
QED

(* Complement reverses subset inclusion. *)
Theorem source_complement_subset_swap:
  !left right.
    left SUBSET COMPL right <=>
    right SUBSET COMPL left
Proof
  simp[pred_setTheory.SUBSET_DEF]
  >> metis_tac[]
QED

(* Choice from an arbitrary set with a proved unique member. *)
Theorem source_choice_unique_member:
  !source element.
    element IN source /\
    (!candidate. candidate IN source ==> candidate = element) ==>
    CHOICE source = element
Proof
  rpt strip_tac
  >> `CHOICE source IN source` by
       metis_tac[pred_setTheory.CHOICE_DEF,
                 pred_setTheory.MEMBER_NOT_EMPTY]
  >> metis_tac[]
QED

Theorem source_pow_insert_image_witness:
  !element set subset.
    subset IN POW (element INSERT set) ==>
    element IN subset ==>
    ?base.
      base IN POW set /\
      subset = element INSERT base
Proof
  rpt strip_tac
  >> qexists_tac `subset DELETE element`
  >> fs[pred_setTheory.IN_POW,
        pred_setTheory.SUBSET_DEF,
        pred_setTheory.EXTENSION]
  >> metis_tac[]
QED

Theorem source_pow_insert_image_case:
  !element source subset.
    element IN subset ==>
    subset DELETE element IN POW source ==>
    ?base.
      base IN POW source /\
      subset = element INSERT base
Proof
  rpt strip_tac
  >> qexists_tac `subset DELETE element`
  >> simp[pred_setTheory.INSERT_DELETE]
QED

Theorem source_pow_insert_image_case_iff:
  !element source subset.
    (element IN subset /\
     subset DELETE element IN POW source) <=>
    ?base.
      base IN POW source /\
      subset = element INSERT base
Proof
  rpt gen_tac
  >> eq_tac
  >- metis_tac[source_pow_insert_image_case]
  >> strip_tac
  >> fs[pred_setTheory.IN_POW,
        pred_setTheory.SUBSET_DEF]
  >> rpt strip_tac
  >> fs[]
QED

Theorem source_in_pow_insert:
  !element set subset.
    subset IN POW (element INSERT set) <=>
    subset IN POW set \/
    (element IN subset /\
     subset DELETE element IN POW set)
Proof
  simp[pred_setTheory.IN_POW, pred_setTheory.SUBSET_DEF]
  >> metis_tac[]
QED

Theorem source_doubleton_eq_iff:
  !first second third fourth.
    (first INSERT (second INSERT {}) =
       third INSERT (fourth INSERT {})) <=>
    (first = third /\ second = fourth) \/
    (first = fourth /\ second = third)
Proof
  simp[pred_setTheory.EXTENSION]
  >> metis_tac[]
QED

Theorem source_subset_image_iff:
  !target function source.
    target SUBSET IMAGE function source <=>
    ?preimage.
      preimage SUBSET source /\
      target = IMAGE function preimage
Proof
  simp[pred_setTheory.SUBSET_IMAGE]
QED

Theorem source_image_pow_surj:
  !function source target.
    IMAGE function source = target ==>
    IMAGE (IMAGE function) (POW source) = POW target
Proof
  rpt gen_tac
  >> strip_tac
  >> qpat_x_assum `IMAGE function source = target`
       (fn theorem => assume_tac (GSYM theorem))
  >> pop_assum SUBST_ALL_TAC
  >> simp[pred_setTheory.EXTENSION,
          pred_setTheory.IN_POW,
          source_subset_image_iff,
          boolTheory.CONJ_COMM]
QED

Theorem source_image_pow_surj_iff:
  !function source target.
    ((IMAGE function source = target ==>
      IMAGE (IMAGE function) (POW source) = POW target) <=>
     T)
Proof
  simp[source_image_pow_surj]
QED

Theorem source_pow_singleton_iff:
  !source target.
    (POW source = target INSERT {}) <=>
    source = {} /\ target = {}
Proof
  rpt gen_tac
  >> eq_tac
  >- (strip_tac
      >> `{} IN POW source` by
           simp[pred_setTheory.IN_POW]
      >> `source IN POW source` by
           simp[pred_setTheory.IN_POW]
      >> qpat_x_assum `POW source = target INSERT {}`
           (fn equality =>
             qpat_x_assum `{} IN POW source`
               (fn empty_member =>
                 qpat_x_assum `source IN POW source`
                   (fn source_member =>
                     map_every assume_tac
                       [REWRITE_RULE [equality] empty_member,
                        REWRITE_RULE [equality] source_member])))
      >> fs[])
  >> strip_tac
  >> fs[pred_setTheory.EXTENSION,
        pred_setTheory.IN_POW,
        pred_setTheory.SUBSET_DEF]
QED

Theorem source_pow_compl:
  !source.
    POW (COMPL source) =
    \subset.
      ?superset.
        subset = COMPL superset /\
        source IN POW superset
Proof
  simp[pred_setTheory.EXTENSION,
       pred_setTheory.IN_POW,
       pred_setTheory.SUBSET_DEF]
  >> rpt gen_tac
  >> eq_tac
  >- (strip_tac
      >> qexists_tac `COMPL x`
      >> simp[]
      >> rpt strip_tac
      >> qpat_x_assum `!item. _`
           (qspec_then `x'` mp_tac)
      >> simp[])
  >> strip_tac
  >> fs[]
  >> rpt strip_tac
  >> qpat_x_assum `!item. item IN source ==> _`
       (qspec_then `x'` mp_tac)
  >> simp[]
QED

Theorem source_pow_compl_iff:
  !source.
    ((POW (COMPL source) =
      \subset.
        ?superset.
          subset = COMPL superset /\
          source IN POW superset) <=>
     T)
Proof
  simp[source_pow_compl]
QED

Theorem source_pairwise_image:
  !relation function source.
    ((!left.
        left IN IMAGE function source ==>
        !right.
          right IN IMAGE function source ==>
          left <> right ==>
          relation left right) <=>
     (!left.
        left IN source ==>
        !right.
          right IN source ==>
          left <> right ==>
          function left <> function right ==>
          relation (function left) (function right)))
Proof
  simp[]
  >> metis_tac[]
QED

Theorem source_is_singleton_bridge:
  !source.
    ((?element. source = {element}) <=>
     pred_set$SING source)
Proof
  simp[pred_setTheory.SING_DEF]
QED

Theorem source_is_singleton_unique:
  !source.
    pred_set$SING source <=>
    ?!element. element IN source
Proof
  simp[pred_setTheory.SING_DEF,
       boolTheory.EXISTS_UNIQUE_THM]
  >> metis_tac[pred_setTheory.UNIQUE_MEMBER_SING]
QED

Theorem source_is_singleton_choice:
  !source.
    pred_set$SING source <=>
    source = {CHOICE source}
Proof
  gen_tac
  >> eq_tac
  >- (strip_tac
      >> fs[pred_setTheory.SING_DEF])
  >> strip_tac
  >> simp[pred_setTheory.SING_DEF]
  >> qexists_tac `CHOICE source`
  >> simp[]
QED

Theorem source_subset_sandwich:
  !lower middle upper.
    lower SUBSET middle ==>
    middle SUBSET upper ==>
    lower = upper ==>
    lower = middle
Proof
  metis_tac[pred_setTheory.SUBSET_ANTISYM]
QED

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/Set.thy, [image_constant].  It carries the membership
   premise; the unconditional [image_constant_conv], which is what
   pred_set$IMAGE_CONST states, is a different lemma. *)
Theorem source_image_constant:
  !value set (constant : 'b).
    value IN set ==> IMAGE (\x. constant) set = {constant}
Proof
  simp[pred_setTheory.EXTENSION]
  >> metis_tac[]
QED

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/List.thy, [set_replicate_conv_if].  The set, not the
   membership: the membership form is [in_set_replicate], which is the
   goal of [list_L5001_in_set_replicate]. *)
Theorem source_set_replicate_conv_if:
  !n (value : 'a).
    LIST_TO_SET (REPLICATE n value) = if n = 0 then {} else {value}
Proof
  Induct
  >> simp[rich_listTheory.REPLICATE]
  >> rw[]
  >> fs[]
QED

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/List.thy, [distinct_zipI1].  Isabelle's [zip] truncates and
   so does HOL4's, so no length condition is needed;
   list$ALL_DISTINCT_ZIP carries one. *)
Theorem source_mem_zip_left:
  !xs (ys : 'b list) left right.
    MEM (left, right) (ZIP (xs, ys)) ==> MEM left xs
Proof
  Induct
  >- simp[listTheory.ZIP_def]
  >> rpt gen_tac
  >> Cases_on `ys`
  >> simp[listTheory.ZIP_def]
  >> metis_tac[]
QED

Theorem source_distinct_zipI1:
  !xs (ys : 'b list).
    ALL_DISTINCT xs ==> ALL_DISTINCT (ZIP (xs, ys))
Proof
  Induct
  >- simp[listTheory.ZIP_def]
  >> gen_tac
  >> Cases_on `ys`
  >> simp[listTheory.ZIP_def]
  >> rpt strip_tac
  >> metis_tac[source_mem_zip_left]
QED

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/List.thy, [butlast_append].  Unconditional, with the case
   split on the right; rich_list$FRONT_APPEND_NOT_NIL is only the
   second branch. *)
Theorem source_butlast_append:
  !xs ys : 'a list.
    FRONT (xs ++ ys) = if ys = [] then FRONT xs else xs ++ FRONT ys
Proof
  rw[rich_listTheory.FRONT_APPEND_NOT_NIL]
QED

(* Isabelle/HOL src/HOL/Product_Type.thy:781, [curry_def].  Isabelle
   defines the constant unapplied -- [curry = (%c x y. c (x, y))] --
   where HOL4's [CURRY_DEF] states the applied equation, which is
   L785's goal.  Rendered as HOL4 defines it, the citation a method
   names is the goal it is cited for and is withheld; rendered as the
   source states it, unfolding the constant leaves a beta redex and the
   goal follows from it. *)
Theorem source_curry_def:
  pair$CURRY = \function first second. function (first, second)
Proof
  simp[FUN_EQ_THM, pairTheory.CURRY_DEF]
QED

(* Isabelle/HOL src/HOL/Nat.thy:714, [gr0_conv_Suc].  An equivalence
   between a positivity and the successor form of the same number.
   HOL4's [num_CASES] is the case split, which states neither side of
   it: a method that rewrites with the equivalence turns a positivity
   assumption into the successor form, where a case split offers two
   branches and leaves the positivity to refute the zero one. *)
Theorem source_gr0_conv_Suc:
  !number. 0 < number <=> ?predecessor. number = SUC predecessor
Proof
  Cases >> simp[]
QED
