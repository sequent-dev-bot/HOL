structure benchListRotate =
struct

open HolKernel

val commit = "f7e02b7e"

fun entry id line method goal : benchLib.source_goal =
  {id = id, goal = goal, source_method = method,
   provenance =
     {file = "src/HOL/List.thy", line = line, commit = commit},
   representative = false}

val goals =
  [entry "list_L5191_rotate0" 5191
     "by(simp add:rotate_def)"
     ``parityTranslation$source_rotate 0 = I``,
   entry "list_L5194_rotate_Suc" 5194
     "by(simp add:rotate_def)"
     ``!count xs.
         parityTranslation$source_rotate (SUC count) xs =
         parityTranslation$source_rotate1
           (parityTranslation$source_rotate count xs)``,
   entry "list_L5197_rotate_add" 5197
     "by(simp add:rotate_def funpow_add)"
     ``!left right.
         parityTranslation$source_rotate (left + right) =
         parityTranslation$source_rotate left o
         parityTranslation$source_rotate right``,
   entry "list_L5201_rotate_rotate" 5201
     "by(simp add:rotate_add)"
     ``!left right xs.
         parityTranslation$source_rotate left
           (parityTranslation$source_rotate right xs) =
         parityTranslation$source_rotate (left + right) xs``,
   entry "list_L5207_rotate1_rotate_swap" 5207
     "by(simp add:rotate_def funpow_swap1)"
     ``!count xs.
         parityTranslation$source_rotate1
           (parityTranslation$source_rotate count xs) =
         parityTranslation$source_rotate count
           (parityTranslation$source_rotate1 xs)``,
   entry "list_L5241_rotate_conv_mod" 5241
     "by (simp add: rotate_drop_take)"
     ``!count xs.
         parityTranslation$source_rotate count xs =
         parityTranslation$source_rotate
           (count MOD LENGTH xs) xs``,
   entry "list_L5244_rotate_id" 5244
     "by (simp add: rotate_drop_take)"
     ``!count xs.
         count MOD LENGTH xs = 0 ==>
         parityTranslation$source_rotate count xs = xs``,
   entry "list_L5259_rotate_map" 5259
     "by(simp add:rotate_drop_take take_map drop_map)"
     ``!count function xs.
         parityTranslation$source_rotate count (MAP function xs) =
         MAP function
           (parityTranslation$source_rotate count xs)``,
   entry "list_L5301_nth_rotate1" 5301
     "using that nth_rotate [of n xs 1] by simp"
     ``!xs index.
         index < LENGTH xs ==>
         EL index (parityTranslation$source_rotate1 xs) =
         EL (SUC index MOD LENGTH xs) xs``,
   entry "list_L5325_bij_rotate1" 5325
     "using bijI inj_rotate1 surj_rotate1 by blast"
     ``BIJ parityTranslation$source_rotate1 UNIV UNIV``]

val shortfalls : benchLib.shortfall list = []

end
