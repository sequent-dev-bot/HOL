Theory iffRoundTripBase
Ancestors
  clasetSeed
Libs
  clasimpLib iffTestSupport

fun fail message = failer "iff round-trip base test" message

Definition iff_round_trip_live_def:
  iff_round_trip_live (p : bool) = p
End

Theorem iff_round_trip_live_rule[iff]:
  !p. iff_round_trip_live p <=> p
Proof
  simp[iff_round_trip_live_def]
QED

val live_name = "iffRoundTripBase$iff_round_trip_live_rule"

val _ =
  if not (has_iff_rules live_name)
  then fail "the attribute did not immediately update the claset"
  else if not (has_iff_rewrite live_name)
  then fail "the attribute did not immediately update the simpsets"
  else ()

(* An ordinary [simp] declaration, so a descendant can check that the two
   declaration streams answer to different fragment names. *)
Definition iff_round_trip_simp_def:
  iff_round_trip_simp (p : bool) = ~p
End

Theorem iff_round_trip_simp_rule[simp]:
  !p. iff_round_trip_simp p <=> ~p
Proof
  simp[iff_round_trip_simp_def]
QED

Definition iff_round_trip_removed_def:
  iff_round_trip_removed (p : bool) = p
End

Theorem iff_round_trip_removed_rule[iff]:
  !p. iff_round_trip_removed p <=> p
Proof
  simp[iff_round_trip_removed_def]
QED

val removed_name = "iffRoundTripBase$iff_round_trip_removed_rule"
val _ = remove_iff "iffRoundTripBase.iff_round_trip_removed_rule"

val _ =
  if has_any_iff_rules removed_name
  then fail "remove_iff did not immediately retract the claset rules"
  else if has_iff_rewrite removed_name
  then fail "remove_iff did not immediately retract the simpset fragment"
  else ()

(* A negated declaration derives an elimination rule and nothing else, and a
   plain one an introduction rule.  Both shapes have to survive a reload and
   a retraction as the equality shape does. *)
Definition iff_round_trip_neg_def:
  iff_round_trip_neg (p : bool) = F
End

Theorem iff_round_trip_neg_rule[iff]:
  !p. ~iff_round_trip_neg p
Proof
  simp[iff_round_trip_neg_def]
QED

val neg_name = "iffRoundTripBase$iff_round_trip_neg_rule"

Definition iff_round_trip_plain_def:
  iff_round_trip_plain (p : bool) = T
End

Theorem iff_round_trip_plain_rule[iff]:
  !p. iff_round_trip_plain p
Proof
  simp[iff_round_trip_plain_def]
QED

val plain_name = "iffRoundTripBase$iff_round_trip_plain_rule"

val _ =
  if not (has_iff_rules_of NegShape neg_name)
  then fail "a negated declaration did not derive exactly an elim rule"
  else if not (has_iff_rewrite neg_name)
  then fail "a negated declaration did not update the simpsets"
  else if not (has_iff_rules_of PlainShape plain_name)
  then fail "a plain declaration did not derive exactly an intro rule"
  else if not (has_iff_rewrite plain_name)
  then fail "a plain declaration did not update the simpsets"
  else ()

Definition iff_round_trip_neg_removed_def:
  iff_round_trip_neg_removed (p : bool) = F
End

Theorem iff_round_trip_neg_removed_rule[iff]:
  !p. ~iff_round_trip_neg_removed p
Proof
  simp[iff_round_trip_neg_removed_def]
QED

val neg_removed_name =
  "iffRoundTripBase$iff_round_trip_neg_removed_rule"
val _ = remove_iff "iffRoundTripBase.iff_round_trip_neg_removed_rule"

val _ =
  if has_any_iff_rules neg_removed_name
  then fail "remove_iff left the derived elim rule behind"
  else if has_iff_rewrite neg_removed_name
  then fail "remove_iff left the negated declaration's rewrite behind"
  else ()

Definition iff_round_trip_delsimp_def:
  iff_round_trip_delsimp (p : bool) = p
End

Theorem iff_round_trip_delsimp_rule[iff]:
  !p. iff_round_trip_delsimp p <=> p
Proof
  simp[iff_round_trip_delsimp_def]
QED

(* Only a delsimps naming the iff view's own key persists into a reload; a
   theory cannot spell its own theorems in the [Thy.Name] form simp accepts
   from descendants. *)
val delsimp_name = "iffRoundTripBase$iff_round_trip_delsimp_rule"
val _ =
  BasicProvers.delsimps
    ["iffRoundTripBase.iff_round_trip_delsimp_rule.__clasimp_iff"]

val _ =
  if has_iff_rewrite delsimp_name
  then fail "a qualified delsimps did not retract the iff simpset view"
  else if not (has_iff_rules delsimp_name)
  then fail "delsimps unexpectedly retracted the iff claset view"
  else ()

(* The finaliser weighs a theory's delsimps declarations against its whole
   iff stream, so a delsimps recorded first has to suppress the iff rewrite
   in the session too.  Otherwise the session and a reload disagree. *)
val _ =
  BasicProvers.delsimps
    ["iffRoundTripBase.iff_round_trip_predelsimp_rule.__clasimp_iff"]

Definition iff_round_trip_predelsimp_def:
  iff_round_trip_predelsimp (p : bool) = p
End

Theorem iff_round_trip_predelsimp_rule[iff]:
  !p. iff_round_trip_predelsimp p <=> p
Proof
  simp[iff_round_trip_predelsimp_def]
QED

val predelsimp_name = "iffRoundTripBase$iff_round_trip_predelsimp_rule"

val _ =
  if has_iff_rewrite predelsimp_name
  then fail "a delsimps recorded before the declaration was ignored"
  else if not (has_iff_rules predelsimp_name)
  then fail "the early delsimps also retracted the iff claset view"
  else ()

(* A bare delsimps names whatever rewrite carries that name, an ancestor's
   as readily as this theory's, so it must not be read as a removal of a
   local [iff] declaration that happens to share the theorem's name. *)
val _ = BasicProvers.delsimps ["iff_round_trip_bare_rule"]

Definition iff_round_trip_bare_def:
  iff_round_trip_bare (p : bool) = p
End

Theorem iff_round_trip_bare_rule[iff]:
  !p. iff_round_trip_bare p <=> p
Proof
  simp[iff_round_trip_bare_def]
QED

val bare_name = "iffRoundTripBase$iff_round_trip_bare_rule"

val _ =
  if not (has_iff_rewrite bare_name)
  then fail "a bare delsimps suppressed an unrelated local declaration"
  else if not (has_iff_rules bare_name)
  then fail "a bare delsimps retracted the iff claset view"
  else ()
