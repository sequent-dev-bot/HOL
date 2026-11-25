structure benchListRemoval =
struct

open HolKernel

val commit = "f7e02b7e"

fun entry id line method goal : benchLib.source_goal =
  {id = id, goal = goal, source_method = method,
   provenance =
     {file = "src/HOL/List.thy", line = line, commit = commit},
   representative = false}

val goals =
  [entry "list_L4628_extract_None_iff" 4628
     ("by(auto simp: extract_def dropWhile_eq_Cons_conv split: list.splits) " ^
      "(metis in_set_conv_decomp)")
     ``!predicate xs.
         (parityTranslation$source_extract predicate xs = NONE <=>
          ~(?value. MEM value xs /\ predicate value))``,
   entry "list_L4632_extract_SomeE" 4632
     "by(auto simp: extract_def dropWhile_eq_Cons_conv split: list.splits)"
     ``!predicate xs prefix value suffix.
         parityTranslation$source_extract predicate xs =
           SOME (prefix, value, suffix) ==>
         xs = prefix ++ value::suffix /\ predicate value /\
         ~(?item. MEM item prefix /\ predicate item)``,
   entry "list_L4637_extract_Some_iff" 4637
     ("by(auto simp: extract_def dropWhile_eq_Cons_conv dest: set_takeWhileD " ^
      "split: list.splits)")
     ``!predicate xs prefix value suffix.
         (parityTranslation$source_extract predicate xs =
            SOME (prefix, value, suffix) <=>
          xs = prefix ++ value::suffix /\ predicate value /\
          ~(?item. MEM item prefix /\ predicate item))``,
   entry "list_L4642_extract_Nil_code" 4642
     "by (simp add: extract_def)"
     ``!predicate.
         parityTranslation$source_extract predicate [] = NONE``,
   entry "list_L4645_extract_Cons_code" 4645
     ("by(auto simp add: extract_def comp_def split: list.splits) (metis " ^
      "dropWhile_eq_Nil_conv list.distinct(1))")
     ``!predicate head tail.
         parityTranslation$source_extract predicate (head::tail) =
         if predicate head then SOME ([], head, tail)
         else
           case parityTranslation$source_extract predicate tail of
             NONE => NONE
           | SOME (prefix, value, suffix) =>
               SOME (head::prefix, value, suffix)``,
   entry "list_L4707_foldr_fold_remove1" 4707 ("using foldr_fold[of _ " ^
                                               "remove1] remove1_commute by " ^
                                               "fastforce")
     ``parityTranslation$source_foldr
          parityTranslation$source_remove1 =
        parityTranslation$source_fold
          parityTranslation$source_remove1``,
   entry "list_L4742_distinct_removeAll" 4742
     "by (simp add: removeAll_filter_not_eq)"
     ``!xs value.
         ALL_DISTINCT xs ==>
         ALL_DISTINCT
           (parityTranslation$source_removeAll value xs)``,
   entry "list_L4758_length_removeAll_less_eq" 4758
     "by (simp add: removeAll_filter_not_eq)"
     ``!xs value.
         LENGTH (parityTranslation$source_removeAll value xs) <=
         LENGTH xs``,
   entry "list_L4762_length_removeAll_less" 4762
     "by (auto dest: length_filter_less simp add: removeAll_filter_not_eq)"
     ``!xs value.
         MEM value xs ==>
         LENGTH (parityTranslation$source_removeAll value xs) <
         LENGTH xs``,
   entry "list_L4781_foldr_fold_removeAll" 4781 ("using foldr_fold[of _ " ^
                                                 "removeAll] " ^
                                                 "removeAll_commute by " ^
                                                 "fastforce")
     ``parityTranslation$source_foldr
          parityTranslation$source_removeAll =
        parityTranslation$source_fold
          parityTranslation$source_removeAll``,
   entry "list_L4793_minus_list_mset_Nil2" 4793
     "by (simp add: minus_list_mset_def)"
     ``!xs.
         parityTranslation$source_minus_list_mset xs [] = xs``,
   entry "list_L4796_minus_list_mset_Cons2" 4796
     "by (simp add: minus_list_mset_def)"
     ``!xs value ys.
         parityTranslation$source_minus_list_mset
           xs (value::ys) =
         parityTranslation$source_remove1 value
           (parityTranslation$source_minus_list_mset xs ys)``,
   entry "list_L4857_minus_list_set_Cons2" 4857
     "by (simp add: minus_list_set_def)"
     ``!xs value ys.
         parityTranslation$source_minus_list_set
           xs (value::ys) =
         parityTranslation$source_removeAll value
           (parityTranslation$source_minus_list_set xs ys)``]

val shortfalls : benchLib.shortfall list = []

end
