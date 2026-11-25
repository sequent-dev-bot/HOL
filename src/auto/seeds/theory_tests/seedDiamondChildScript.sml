Theory seedDiamondChild
Ancestors
  seedDiamondLeft seedDiamondRight
Libs
  clasimpLib

fun fail message = raise Fail ("seed diamond merge: " ^ message)

val matching =
  List.filter
    (fn ({name, ...} : clasetLib.aesop_rule) =>
      String.isSubstring "pairAutoSeed$CURRY_AUTO_IFF" name)
    (clasetLib.all_rules (clasetLib.the_claset ()))

fun duplicate [] = false
  | duplicate ((rule : clasetLib.aesop_rule) :: rest) =
      List.exists
        (fn (other : clasetLib.aesop_rule) =>
          #kind (#spec rule) = #kind (#spec other) andalso
          aconv (concl (#thm rule)) (concl (#thm other)))
        rest orelse duplicate rest

val _ =
  if null matching then fail "merged ancestry lost the pair iff rules"
  else if duplicate matching then fail "diamond ancestry duplicated a rule"
  else ()
