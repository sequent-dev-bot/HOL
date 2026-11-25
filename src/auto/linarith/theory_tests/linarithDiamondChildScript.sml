Theory linarithDiamondChild
Ancestors
  linarithDiamondAdd linarithDiamondRemove

fun fail message =
  raise Fail ("linarith diamond test: " ^ message)

fun count theorem theorems =
  List.length
    (List.filter
      (fn candidate => aconv (concl candidate) (concl theorem)) theorems)

val add_fact = linarithDiamondAddTheory.arith_diamond_add_fact
val add_split = linarithDiamondAddTheory.arith_split_diamond_add_rule
val contested_fact =
  linarithDiamondAddTheory.arith_diamond_contested_fact
val contested_split =
  linarithDiamondAddTheory.arith_split_diamond_contested_rule
val root_fact =
  DB.fetch "linarithDiamondRoot" "arith_diamond_root_fact"
val root_split =
  DB.fetch "linarithDiamondRoot" "arith_split_diamond_root_rule"

val facts = linarithData.arith_facts ()
val splits = linarithData.arith_split_thms ()

val _ =
  if count add_fact facts = 1 andalso count add_split splits = 1
  then ()
  else fail "a sibling declaration was not ancestry-merged"

val _ =
  if count root_fact facts = 0 andalso count root_split splits = 0
  then ()
  else fail "a sibling retraction did not beat the root declaration"

val _ =
  if count contested_fact facts = 0 andalso
     count contested_split splits = 0
  then ()
  else fail "a retraction did not reach the sibling branch's declaration"
