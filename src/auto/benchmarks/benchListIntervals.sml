structure benchListIntervals =
struct

open HolKernel

val commit = "f7e02b7e"

fun entry id line method goal : benchLib.source_goal =
  {id = id, goal = goal, source_method = method,
   provenance =
     {file = "src/HOL/List.thy", line = line, commit = commit},
   representative = false}

val goals =
  [entry "list_L8290_forall_less_eq_iff" 8290 "by auto"
     ``!le predicate bound.
         ((!value. le value bound ==> predicate value) <=>
          (!value. value IN parityTranslation$source_atMost le bound ==>
                   predicate value))``,
   entry "list_L8294_exists_less_eq_iff" 8294 "by auto"
     ``!le predicate bound.
         ((?value. le value bound /\ predicate value) <=>
          (?value. value IN parityTranslation$source_atMost le bound /\
                   predicate value))``,
   entry "list_L8298_forall_less_iff" 8298 "by auto"
     ``!lt predicate bound.
         ((!value. lt value bound ==> predicate value) <=>
          (!value. value IN parityTranslation$source_lessThan lt bound ==>
                   predicate value))``,
   entry "list_L8302_exists_less_iff" 8302 "by auto"
     ``!lt predicate bound.
         ((?value. lt value bound /\ predicate value) <=>
          (?value. value IN parityTranslation$source_lessThan lt bound /\
                   predicate value))``,
   entry "list_L8306_forall_greater_eq_iff" 8306 "by auto"
     ``!le predicate bound.
         ((!value. le bound value ==> predicate value) <=>
          (!value. value IN parityTranslation$source_atLeast le bound ==>
                   predicate value))``,
   entry "list_L8310_exists_greater_eq_iff" 8310 "by auto"
     ``!le predicate bound.
         ((?value. le bound value /\ predicate value) <=>
          (?value. value IN parityTranslation$source_atLeast le bound /\
                   predicate value))``,
   entry "list_L8314_forall_greater_iff" 8314 "by auto"
     ``!lt predicate bound.
         ((!value. lt bound value ==> predicate value) <=>
          (!value. value IN parityTranslation$source_greaterThan lt bound ==>
                   predicate value))``,
   entry "list_L8318_exists_greater_iff" 8318 "by auto"
     ``!lt predicate bound.
         ((?value. lt bound value /\ predicate value) <=>
          (?value.
             value IN parityTranslation$source_greaterThan lt bound /\
             predicate value))``,
   entry "list_L8454_atLeast_eq_atLeastAtMost_top" 8454 "by auto"
     ``!le top.
         (!value. le value top) ==>
         !lower.
           parityTranslation$source_atLeast le lower =
           parityTranslation$source_atLeastAtMost le lower top``,
   entry "list_L8458_greaterThan_eq_greaterThanAtMost_top" 8458
     "by auto"
     ``!le lt top.
         (!value. le value top) ==>
         !lower.
           parityTranslation$source_greaterThan lt lower =
           parityTranslation$source_greaterThanAtMost
             le lt lower top``,
   entry "list_L8467_atMost_eq_atLeastAtMost_bot" 8467 "by auto"
     ``!le bottom.
         (!value. le bottom value) ==>
         !upper.
           parityTranslation$source_atMost le upper =
           parityTranslation$source_atLeastAtMost le bottom upper``,
   entry "list_L8471_lessThan_eq_atLeastLessThan_bot" 8471 "by auto"
     ``!le lt bottom.
         (!value. le bottom value) ==>
         !upper.
           parityTranslation$source_lessThan lt upper =
           parityTranslation$source_atLeastLessThan
             le lt bottom upper``]

val shortfalls : benchLib.shortfall list = []

end
