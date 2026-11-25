structure benchListCode =
struct

open HolKernel

fun entry id line method goal : benchLib.source_goal =
  {id = id, goal = goal, source_method = method,
   provenance =
     {file = "src/HOL/List.thy", line = line, commit = "f7e02b7e"},
   representative = false}

val goals =
  [entry "list_L8199_list_ex1_Nil_iff" 8199
     "by (auto simp add: list_ex1_iff)"
     ``!predicate.
         ~parityTranslation$source_list_ex1 predicate []``,
   entry "list_L8203_list_ex1_Cons_iff" 8203
     "by (auto simp add: list_ex1_iff list_all_iff)"
     ``!predicate value xs.
         (parityTranslation$source_list_ex1 predicate (value::xs) <=>
          if predicate value then
            parityTranslation$source_list_all
              (\other. ~predicate other \/ value = other) xs
          else
            parityTranslation$source_list_ex1 predicate xs)``,
   entry "list_L8673_these_set_code" 8673
     ("by (simp add: Option.these_eq Option.is_none_def set_eq_iff " ^
      "map_filter_def)")
     ``!xs.
         parityTranslation$source_these (LIST_TO_SET xs) =
         LIST_TO_SET (parityTranslation$source_map_filter I xs)``,
   entry "list_L8683_can_select_set_list_ex1" 8683
     "by (simp add: list_ex1_iff)"
     ``!predicate xs.
         (parityTranslation$source_can_select
            predicate (LIST_TO_SET xs) =
          parityTranslation$source_list_ex1 predicate xs)``,
   entry "list_L8691_Id_on_set" 8691
     "by (auto simp add: Id_on_def)"
     ``!xs.
         parityTranslation$source_Id_on (LIST_TO_SET xs) =
         LIST_TO_SET (MAP (\value. (value, value)) xs)``,
   entry "list_L8701_trancl_set_ntrancl" 8701
     "by (simp add: finite_trancl_ntranl)"
     ``!pairs.
         relation$TC
           (parityTranslation$source_list_relation pairs) =
         parityTranslation$source_ntrancl
           (CARD (LIST_TO_SET pairs) - 1)
           (parityTranslation$source_list_relation pairs)``,
   entry "list_L9009_null_transfer" 9009
     "unfolding rel_fun_def by auto"
     ``!relation xs ys.
         LIST_REL relation xs ys ==> (NULL xs = NULL ys)``]

val shortfalls : benchLib.shortfall list = []

end
