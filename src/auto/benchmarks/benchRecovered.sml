structure benchRecovered =
struct

open HolKernel

fun entry id file line method goal : benchLib.source_goal =
  {id = id, goal = goal, source_method = method,
   provenance =
     {file = file, line = line, commit = "f7e02b7e"},
   representative = false}

val goals =
  [entry "list_L3349_anon_L3349" "src/HOL/List.thy" 3349
     "by simp"
     ``!function.
         function (LIST_TO_SET []) =
         parityTranslation$source_abort_empty_set function``,
   entry "list_L3566_map_nth_upt0" "src/HOL/List.thy" 3566
     "by(simp add: map_nth_upt)"
     ``!xs count.
         count <= LENGTH xs ==>
         MAP (\index. EL index xs)
           (rich_list$COUNT_LIST count) = TAKE count xs``,
   entry "list_L3381_anon_L3381" "src/HOL/List.thy" 3381
     "by (simp add: fold_map)"
     ``!aggregate operation top function xs.
         (!ys.
            aggregate (LIST_TO_SET ys) =
            parityTranslation$source_fold operation ys top) ==>
         parityTranslation$source_INF aggregate function
           (LIST_TO_SET xs) =
         parityTranslation$source_fold
           (\value current. operation (function value) current)
           xs top``,
   entry "list_L3385_anon_L3385" "src/HOL/List.thy" 3385
     "by (simp add: fold_map)"
     ``!aggregate operation bottom function xs.
         (!ys.
            aggregate (LIST_TO_SET ys) =
            parityTranslation$source_fold operation ys bottom) ==>
         parityTranslation$source_SUP aggregate function
           (LIST_TO_SET xs) =
         parityTranslation$source_fold
           (\value current. operation (function value) current)
           xs bottom``,
   entry "product_type_L1061_Sigma_insert"
     "src/HOL/Product_Type.thy" 1061 "by auto"
     ``!value domain fibres.
         parityTranslation$source_Sigma (value INSERT domain) fibres =
         IMAGE (\item. (value, item)) (fibres value) UNION
         parityTranslation$source_Sigma domain fibres``,
   entry "list_L8543_map_filter_map_filter" "src/HOL/List.thy" 8543
     "by (simp add: map_filter_def)"
     ``!function predicate xs.
         MAP function (FILTER predicate xs) =
         parityTranslation$source_map_filter
           (\value.
              if predicate value then SOME (function value) else NONE)
           xs``,
   entry "list_L8603_is_empty_set" "src/HOL/List.thy" 8603
     "by simp"
     ``!xs. (LIST_TO_SET xs = EMPTY <=> NULL xs)``,
   entry "list_L5527_Nil_in_shufflesI" "src/HOL/List.thy" 5527
     "by simp"
     ``!xs ys.
         xs = [] ==> ys = [] ==>
         [] IN parityTranslation$source_shuffles xs ys``,
   entry "list_L5470_subset_subseqs" "src/HOL/List.thy" 5470
     "unfolding subseqs_powset by simp"
     ``!xs subset.
         subset SUBSET LIST_TO_SET xs ==>
         subset IN
           IMAGE LIST_TO_SET
             (LIST_TO_SET
               (parityTranslation$source_subseqs xs))``,
   entry "list_L5441_distinct_set_subseqs" "src/HOL/List.thy" 5441
     "by (simp add: assms card_Pow card_distinct distinct_card length_subseqs subseqs_powset)"
     ``!xs.
         ALL_DISTINCT xs ==>
         ALL_DISTINCT
           (MAP LIST_TO_SET
             (parityTranslation$source_subseqs xs))``,
   entry "list_L6972_mono_lists" "src/HOL/List.thy" 6972
     "unfolding mono_def by auto"
     ``!left right.
         left SUBSET right ==>
         parityTranslation$source_lists left SUBSET
           parityTranslation$source_lists right``]

val shortfalls : benchLib.shortfall list = []

end
