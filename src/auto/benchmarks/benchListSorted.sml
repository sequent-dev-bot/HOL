structure benchListSorted =
struct

open HolKernel

val commit = "f7e02b7e"

fun entry id line method goal : benchLib.source_goal =
  {id = id, goal = goal, source_method = method,
   provenance =
     {file = "src/HOL/List.thy", line = line, commit = commit},
   representative = false}

fun strict_entry id line method goal : benchLib.source_goal =
  {id = id, goal = goal, source_method = method,
   provenance =
     {file = "src/HOL/List.thy", line = line, commit = commit},
   representative = false}

val goals =
  [entry "list_L412_sorted_simps_1" 412 "by auto"
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         (parityTranslation$source_sorted le [] <=> T)``,
   entry "list_L412_sorted_simps_2" 412 "by auto"
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !x ys.
           (parityTranslation$source_sorted le (x::ys) <=>
            (!y. MEM y ys ==> le x y) /\
            parityTranslation$source_sorted le ys)``,
   entry "list_L415_strict_sorted_simps_1" 415 "by auto"
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         (parityTranslation$source_strict_sorted le [] <=> T)``,
   entry "list_L415_strict_sorted_simps_2" 415 "by auto"
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !x ys.
           (parityTranslation$source_strict_sorted le (x::ys) <=>
            (!y. MEM y ys ==> relation$STRORD le x y) /\
            parityTranslation$source_strict_sorted le ys)``,
   strict_entry "list_L441_strict_sorted_imp_sorted" 441
     "by (auto simp: strict_sorted_iff)"
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !xs. parityTranslation$source_strict_sorted le xs ==>
              parityTranslation$source_sorted le xs``]

val shortfalls : benchLib.shortfall list = []

end
