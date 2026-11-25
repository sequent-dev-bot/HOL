Theory iffBatchChild
Ancestors
  iffBatch
Libs
  iffTestSupport

fun fail message = failer "iff batch child test" message

val names =
  ["iffBatch$iff_batch_one_rule",
   "iffBatch$iff_batch_two_rule",
   "iffBatch$iff_batch_three_rule"]

val _ =
  if List.all has_iff_rewrite names andalso List.all has_iff_rules names
  then ()
  else fail "the reloaded child lost an inherited iff declaration"

(* The finaliser replays a theory's whole iff stream at once, so the three
   declarations arrive as one named fragment rather than one each. *)
val _ =
  case iff_fragment_count names (BasicProvers.srw_ss ()) of
      1 => ()
    | count =>
        fail
          ("three iff declarations produced " ^ Int.toString count ^
           " simpset fragments, not one")
