structure benchListNumeric =
struct

open HolKernel

val commit = "f7e02b7e"

fun entry id line method goal : benchLib.source_goal =
  {id = id, goal = goal, source_method = method,
   provenance =
     {file = "src/HOL/List.thy", line = line, commit = commit},
   representative = false}

val goals =
  [entry "list_L3589_take_Cons_numeral" 3589
     "by (simp add: take_Cons')"
     ``!v x xs.
         TAKE (parityTranslation$source_numeral v) (x::xs) =
         x :: TAKE (parityTranslation$source_numeral v - 1) xs``,
   entry "list_L3593_drop_Cons_numeral" 3593
     "by (simp add: drop_Cons')"
     ``!v x xs.
         DROP (parityTranslation$source_numeral v) (x::xs) =
         DROP (parityTranslation$source_numeral v - 1) xs``,
   entry "list_L3597_nth_Cons_numeral" 3597
     "by (simp add: nth_Cons')"
     ``!v x xs.
         EL (parityTranslation$source_numeral v) (x::xs) =
         EL (parityTranslation$source_numeral v - 1) xs``,
   entry "list_L3635_upto_empty" 3635
     "by(simp add: upto.simps)"
     ``!i j : int. j < i ==>
         parityTranslation$source_upto i j = []``,
   entry "list_L3638_upto_single" 3638
     "by(simp add: upto.simps)"
     ``!i : int. parityTranslation$source_upto i i = [i]``,
   entry "list_L3641_upto_Nil" 3641
     "by (simp add: upto.simps)"
     ``!i j : int.
         (parityTranslation$source_upto i j = [] <=> j < i)``,
   entry "list_L3646_upto_rec1" 3646
     "by(simp add: upto.simps)"
     ``!i j : int. i <= j ==>
         parityTranslation$source_upto i j =
         i :: parityTranslation$source_upto (i + 1) j``,
   entry "list_L3683_upto_split2" 3683 ("using upto_rec1 upto_rec2 " ^
                                        "upto_split1 by auto")
     ``!i j k : int. i <= j ==> j <= k ==>
         parityTranslation$source_upto i k =
         parityTranslation$source_upto i j ++
         parityTranslation$source_upto (j + 1) k``,
   entry "list_L3687_upto_split3" 3687 "using upto_rec1 upto_split1 by auto"
     ``!i j k : int. i <= j ==> j <= k ==>
         parityTranslation$source_upto i k =
         parityTranslation$source_upto i (j - 1) ++
         j :: parityTranslation$source_upto (j + 1) k``,
   entry "list_L3695_upto_aux_rec" 3695
     "by (simp add: upto_aux_def upto_rec2)"
     ``!i j : int. !js.
         parityTranslation$source_upto_aux i j js =
         if j < i then js
         else parityTranslation$source_upto_aux
                i (j - 1) (j::js)``,
   entry "list_L3699_upto_code" 3699
     "by(simp add: upto_aux_def)"
     ``!i j : int.
         parityTranslation$source_upto i j =
         parityTranslation$source_upto_aux i j []``]

val shortfalls : benchLib.shortfall list = []

end
