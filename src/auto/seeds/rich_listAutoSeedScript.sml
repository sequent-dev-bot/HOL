Theory rich_listAutoSeed
Ancestors
  rich_list
Libs
  clasetLib clasimpLib

val sintro_spec =
  {kind = clasetRules.Intro, safe = true, prio = NONE}
val dest_spec =
  {kind = clasetRules.Dest, safe = false, prio = NONE}
val forward_spec =
  {kind = clasetRules.Forward, safe = false, prio = SOME 10}

(* List.thy analogues and documented HOL4-local structural judgments. *)
Theorem EVERY_REVERSE_AUTO[iff] = rich_listTheory.EVERY_REVERSE
Theorem MEM_REPLICATE_AUTO[iff] = rich_listTheory.MEM_REPLICATE
Theorem REPLICATE_NIL_AUTO[iff] = rich_listTheory.REPLICATE_NIL
Theorem LIST_REL_REVERSE_EQ_AUTO[iff] = rich_listTheory.LIST_REL_REVERSE_EQ
Theorem APPEND_EQ_APPEND_EQ_AUTO[iff] = rich_listTheory.APPEND_EQ_APPEND_EQ
Theorem LENGTH_FILTER_LEQ_AUTO[iff] = rich_listTheory.LENGTH_FILTER_LEQ
Theorem FILTER_ALL_DISTINCT_AUTO[iff] = listTheory.FILTER_ALL_DISTINCT

(* src/HOL/List.thy:2256 @ f7e02b7e.  [drop_drop] is simp there and
   declared to no simpset here; HOL4 states the unconditional equation
   as DROP_DROP_T.  Its [take_take] half is seeded in listAutoSeed. *)
Theorem DROP_DROP_T_AUTO[simp] = rich_listTheory.DROP_DROP_T

(* src/HOL/List.thy:3231 @ f7e02b7e.  [fold_append] is simp there and
   declared to no simpset here.  HOL4 reverses [rev (xs @ ys)]
   ambiently but leaves the fold over the result alone, so a goal that
   folds across an append stops one rewrite short. *)
Theorem FOLDL_APPEND_AUTO[simp] = rich_listTheory.FOLDL_APPEND

(* src/HOL/List.thy:1824 @ f7e02b7e.  [nth_append_length] is simp there:
   indexing an append at exactly the left length reaches the right
   list's head.  HOL4 states it on a non-empty right list and declares
   it nowhere.  Its [_plus] companion has no HOL4 counterpart, and the
   conditional halves [nth_append_left] and [_right] are simp in
   neither system; see the rest of the indexing family in
   listAutoSeed. *)
Theorem EL_LENGTH_APPEND_AUTO[simp] = rich_listTheory.EL_LENGTH_APPEND

(* src/HOL/List.thy:1807 @ f7e02b7e.  [nth_Cons_pos] is simp there and
   declared to no simpset here.  It is the constructor the indexing
   family in listAutoSeed leaves out -- a cons against an index known
   only to be non-zero, which is what a case split on the index leaves
   standing on the branch it does not settle.  HOL4 states it as
   EL_CONS, spelling the index below as [PRE n] where a translated goal
   spells it [n - 1]; the seeded step between the two spellings is what
   lets the rule meet such a goal at all. *)
Theorem EL_CONS_AUTO[simp] = rich_listTheory.EL_CONS

(* src/HOL/List.thy @ f7e02b7e.  [hd_replicate] is simp there and HOL4
   states it nowhere: the walk down a replicate reads its head off the
   count, and a source result about [takeWhile] or [dropWhile] of a
   replicate reaches its head through the [xs = [] \/ ~P (hd xs)] side
   of the walk's own characterisation.  The count is a variable, so no
   REPLICATE clause reduces and the head stays stuck. *)
Theorem HD_REPLICATE_AUTO[simp]:
  !count (item : 'a). count <> 0 ==> HD (REPLICATE count item) = item
Proof
  Cases >> simp[rich_listTheory.REPLICATE]
QED

(* src/HOL/List.thy @ f7e02b7e.  [hd_in_set] is simp there: the head
   of a non-empty list is one of its elements.  HOL4 states the same
   fact as [HEAD_MEM] and declares it to no simpset, so a premise
   quantified over the elements of a list stops short of its head --
   the simplifier's condition solver has no way to discharge
   [MEM (HD l) l], and every rule whose side condition asks for it
   fails to fire. *)
Theorem HEAD_MEM_AUTO[simp] = rich_listTheory.HEAD_MEM

(* src/HOL/List.thy @ f7e02b7e.  [take_append] is simp there and
   declared to no simpset here; its [drop_append] counterpart and the
   two length rules that finish the halves are seeded in
   listAutoSeed, which states them. *)
Theorem TAKE_APPEND_AUTO[simp] = rich_listTheory.TAKE_APPEND

val _ =
  List.app (clasetLib.export_rule sintro_spec)
    ["rich_list.IS_PREFIX_REFL", "rich_list.IS_SUFFIX_REFL"]

val _ =
  List.app (clasetLib.export_rule dest_spec)
    ["rich_list.EVERY_TAKE", "rich_list.EVERY_DROP",
     "rich_list.MEM_TAKE", "rich_list.MEM_DROP_IMP"]

val _ =
  List.app (clasetLib.export_rule forward_spec)
    ["rich_list.IS_PREFIX_ANTISYM", "rich_list.IS_PREFIX_TRANS",
     "rich_list.IS_SUFFIX_TRANS"]
