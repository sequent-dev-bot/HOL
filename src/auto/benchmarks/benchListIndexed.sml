structure benchListIndexed =
struct

open HolKernel

val commit = "f7e02b7e"

fun entry id line method goal : benchLib.source_goal =
  {id = id, goal = goal, source_method = method,
   provenance =
     {file = "src/HOL/List.thy", line = line, commit = commit},
   representative = false}

val goals =
  [entry "list_L5136_length_indexed_from" 5136
     "by (simp add: indexed_from_eq_zip)"
     ``!start xs.
         LENGTH (parityTranslation$source_indexed_from start xs) =
         LENGTH xs``,
   entry "list_L5140_map_fst_indexed_from" 5140
     "by (simp add: indexed_from_eq_zip)"
     ``!start xs.
         MAP FST (parityTranslation$source_indexed_from start xs) =
         GENLIST (\offset. start + offset) (LENGTH xs)``,
   entry "list_L5144_map_snd_indexed_from" 5144
     "by (simp add: indexed_from_eq_zip)"
     ``!start xs.
         MAP SND (parityTranslation$source_indexed_from start xs) = xs``,
   entry "list_L5163_nth_indexed_from_eq" 5163
     "by (simp add: indexed_from_eq_zip)"
     ``!start xs index.
         index < LENGTH xs ==>
         EL index
           (parityTranslation$source_indexed_from start xs) =
         (start + index, EL index xs)``,
   entry "list_L5176_distinct_indexed_from" 5176
     "by (simp add: indexed_from_eq_zip distinct_zipI1)"
     ``!start xs.
         ALL_DISTINCT
           (parityTranslation$source_indexed_from start xs)``,
   entry "list_L5180_indexed_from_append_eq" 5180
     "by (simp add: indexed_from_eq_zip add.assoc zip_append2)"
     ``!start xs ys.
         parityTranslation$source_indexed_from start (xs ++ ys) =
         parityTranslation$source_indexed_from start xs ++
         parityTranslation$source_indexed_from
           (start + LENGTH xs) ys``]

val shortfalls : benchLib.shortfall list = []

end
