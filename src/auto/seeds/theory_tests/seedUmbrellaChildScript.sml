Theory seedUmbrellaChild
Ancestors
  autoSeed

fun fail message = raise Fail ("seed umbrella child: " ^ message)

val required =
  ["pairAutoSeed", "sumAutoSeed", "optionAutoSeed", "listAutoSeed",
   "pred_setAutoSeed", "arithmeticAutoSeed", "finite_mapAutoSeed",
   "integerAutoSeed", "realAutoSeed", "stringAutoSeed",
   "rich_listAutoSeed", "sortingAutoSeed"]

val ancestry = Theory.ancestry (Theory.current_theory ())

val _ =
  if List.all (fn name => List.exists (equal name) ancestry) required
  then ()
  else fail "a per-theory seed is absent below the umbrella"
