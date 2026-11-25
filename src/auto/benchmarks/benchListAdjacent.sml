structure benchListAdjacent =
struct

open HolKernel

val commit = "f7e02b7e"

fun entry id line method goal : benchLib.source_goal =
  {id = id, goal = goal, source_method = method,
   provenance =
     {file = "src/HOL/List.thy", line = line, commit = commit},
   representative = false}

val goals =
  [entry "list_L4319_successively_nth" 4319 ("unfolding " ^
                                             "successively_conv_nth by blast")
     ``!relation xs i.
         parityTranslation$source_successively relation xs ==>
         i + 1 < LENGTH xs ==>
         relation (EL i xs) (EL (i + 1) xs)``,
   entry "list_L4322_distinct_adj_conv_nth" 4322
     "by (simp add: distinct_adj_def successively_conv_nth)"
     ``!xs.
         parityTranslation$source_distinct_adj xs <=>
         !i. i + 1 < LENGTH xs ==> EL i xs <> EL (i + 1) xs``,
   entry "list_L4326_distinct_adj_nth" 4326 ("unfolding " ^
                                             "distinct_adj_conv_nth by blast")
     ``!xs i.
         parityTranslation$source_distinct_adj xs ==>
         i + 1 < LENGTH xs ==> EL i xs <> EL (i + 1) xs``,
   entry "list_L4406_distinct_adj_Nil" 4406
     "by (auto simp: distinct_adj_def)"
     ``parityTranslation$source_distinct_adj ([] : 'a list)``,
   entry "list_L4406_distinct_adj_singleton" 4406
     "by (auto simp: distinct_adj_def)"
     ``!x. parityTranslation$source_distinct_adj [x]``,
   entry "list_L4406_distinct_adj_Cons_Cons" 4406
     "by (auto simp: distinct_adj_def)"
     ``!x y xs.
         parityTranslation$source_distinct_adj (x::y::xs) <=>
         x <> y /\
         parityTranslation$source_distinct_adj (y::xs)``,
   entry "list_L4431_distinct_adj_rev" 4431
     "by (simp add: distinct_adj_def eq_commute)"
     ``!xs.
         parityTranslation$source_distinct_adj (REVERSE xs) <=>
         parityTranslation$source_distinct_adj xs``,
   entry "list_L4434_distinct_adj_append_iff" 4434
     "by (auto simp: distinct_adj_def successively_append_iff)"
     ``!xs ys.
         parityTranslation$source_distinct_adj (xs ++ ys) <=>
         parityTranslation$source_distinct_adj xs /\
         parityTranslation$source_distinct_adj ys /\
         (xs = [] \/ ys = [] \/ LAST xs <> HD ys)``,
   entry "list_L4439_distinct_adj_appendD1" 4439
     "by (auto simp: distinct_adj_append_iff)"
     ``!xs ys.
         parityTranslation$source_distinct_adj (xs ++ ys) ==>
         parityTranslation$source_distinct_adj xs``,
   entry "list_L4439_distinct_adj_appendD2" 4439
     "by (auto simp: distinct_adj_append_iff)"
     ``!xs ys.
         parityTranslation$source_distinct_adj (xs ++ ys) ==>
         parityTranslation$source_distinct_adj ys``,
   entry "list_L4450_distinct_adj_map_iff" 4450 ("using distinct_adj_mapD " ^
                                                 "distinct_adj_mapI by blast")
     ``!function xs.
         parityTranslation$source_inj_on
           function (LIST_TO_SET xs) ==>
         (parityTranslation$source_distinct_adj
            (MAP function xs) <=>
          parityTranslation$source_distinct_adj xs)``]

val shortfalls : benchLib.shortfall list = []

end
