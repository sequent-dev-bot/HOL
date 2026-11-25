Theory seedChild
Ancestors
  pairAutoSeed
Libs
  clasimpLib

fun fail message = raise Fail ("seed child visibility: " ^ message)

val _ =
  if List.exists
       (fn ({name, ...} : clasetLib.aesop_rule) =>
         String.isSubstring "pairAutoSeed$CURRY_AUTO_IFF" name)
       (clasetLib.all_rules (clasetLib.the_claset ()))
  then ()
  else fail "pair iff declaration is not visible"
