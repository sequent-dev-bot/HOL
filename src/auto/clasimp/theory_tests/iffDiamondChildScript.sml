Theory iffDiamondChild
Ancestors
  iffDiamondAdd iffDiamondRemove
Libs
  iffTestSupport

fun fail message = failer "iff diamond test" message

val root_name = "iffDiamondRoot$iff_diamond_root_rule"
val add_name = "iffDiamondAdd$iff_diamond_add_rule"

val _ =
  if not (has_iff_rules add_name)
  then fail "the sibling addition was not ancestry-merged into the claset"
  else if not (has_iff_rewrite add_name)
  then fail "the sibling addition was not ancestry-merged into the simpsets"
  else if has_any_iff_rules root_name
  then fail "the sibling removal did not beat the root claset addition"
  else if has_iff_rewrite root_name
  then fail "the sibling removal did not beat the root simpset addition"
  else ()
