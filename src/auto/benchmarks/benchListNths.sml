structure benchListNths =
struct

open HolKernel

val commit = "f7e02b7e"

fun entry id line method goal : benchLib.source_goal =
  {id = id, goal = goal, source_method = method,
   provenance =
     {file = "src/HOL/List.thy", line = line, commit = commit},
   representative = false}

val goals =
  [entry "list_L5334_nths_empty" 5334
     "by (auto simp add: nths_def)"
     ``!xs. parityTranslation$source_nths xs EMPTY = []``,
   entry "list_L5337_nths_nil" 5337
     "by (auto simp add: nths_def)"
     ``!indices. parityTranslation$source_nths [] indices = []``,
   entry "list_L5344_length_nths" 5344
     "by(simp add: nths_def length_filter_conv_card cong:conj_cong)"
     ``!xs indices.
         LENGTH (parityTranslation$source_nths xs indices) =
         CARD {index | index < LENGTH xs /\ index IN indices}``,
   entry "list_L5385_set_nths_subset" 5385
     "by(auto simp add:set_nths)"
     ``!xs indices.
         LIST_TO_SET (parityTranslation$source_nths xs indices)
           SUBSET LIST_TO_SET xs``,
   entry "list_L5388_notin_set_nthsI" 5388
     "by(auto simp add:set_nths)"
     ``!value xs indices.
         ~MEM value xs ==>
         ~MEM value (parityTranslation$source_nths xs indices)``,
   entry "list_L5391_in_set_nthsD" 5391
     "by(auto simp add:set_nths)"
     ``!value xs indices.
         MEM value (parityTranslation$source_nths xs indices) ==>
         MEM value xs``,
   entry "list_L5394_nths_singleton" 5394
     "by (simp add: nths_Cons)"
     ``!value indices.
         parityTranslation$source_nths [value] indices =
         if 0 IN indices then [value] else []``,
   entry "list_L5409_nths_drop" 5409
     ("by(force simp: drop_eq_nths nths_nths simp flip: atLeastLessThan_iff " ^
      "intro: arg_cong2[where f=nths, OF refl])")
     ``!count xs indices.
         parityTranslation$source_nths (DROP count xs) indices =
         parityTranslation$source_nths xs
           (IMAGE (\index. count + index) indices)``]

val shortfalls : benchLib.shortfall list = []

end
