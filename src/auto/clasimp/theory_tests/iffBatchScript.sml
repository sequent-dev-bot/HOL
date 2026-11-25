Theory iffBatch
Ancestors
  clasetSeed
Libs
  clasimpLib iffTestSupport

Definition iff_batch_one_def:
  iff_batch_one (p : bool) = p
End

Definition iff_batch_two_def:
  iff_batch_two (p : bool) = p
End

Definition iff_batch_three_def:
  iff_batch_three (p : bool) = p
End

Theorem iff_batch_one_rule[iff]:
  !p. iff_batch_one p <=> p
Proof
  simp[iff_batch_one_def]
QED

Theorem iff_batch_two_rule[iff]:
  !p. iff_batch_two p <=> p
Proof
  simp[iff_batch_two_def]
QED

Theorem iff_batch_three_rule[iff]:
  !p. iff_batch_three p <=> p
Proof
  simp[iff_batch_three_def]
QED

(* Batching is the finaliser's job, so the count that matters is the one a
   descendant theory sees; iffBatchChild asserts it.  Here the declarations
   only have to be individually live. *)
val _ =
  if List.all has_iff_rewrite
       ["iffBatch$iff_batch_one_rule",
        "iffBatch$iff_batch_two_rule",
        "iffBatch$iff_batch_three_rule"]
  then ()
  else fail "an iff declaration was not immediately live in its own theory"
