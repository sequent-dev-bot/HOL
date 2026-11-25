Theory diamondChild
Ancestors
  diamondAdd diamondRemove
Libs
  clasetLib

fun fail message = raise Fail ("diamond claset test: " ^ message)

fun find_rule name =
  List.find (fn (_, (name', _)) => name = name') (rules_of (the_claset ()))

val _ =
  case find_rule "diamondAdd$diamond_add_rule" of
      SOME ({kind = clasetRules.Elim, safe = true, ...}, _) =>
        if not
          (Option.isSome (find_rule "diamondRoot$diamond_root_rule"))
        then ()
        else fail "a sibling removal did not beat the ancestor addition"
    | _ => fail "the sibling addition was not ancestry-merged"
