Theory linarithRoundTripBase
Ancestors
  bool
Libs
  linarithData

fun fail message =
  raise Fail ("linarith round-trip base test: " ^ message)

fun contains theorem theorems =
  List.exists (fn candidate => aconv (concl candidate) (concl theorem))
    theorems

Definition arith_round_trip_def:
  arith_round_trip (p : bool) = p
End

Theorem arith_round_trip_fact[arith]:
  !p. arith_round_trip p <=> p
Proof
  simp[arith_round_trip_def]
QED

Definition arith_split_round_trip_def:
  arith_split_round_trip (p : bool) = p
End

Theorem arith_split_round_trip_rule[arith_split]:
  !P p. P (arith_split_round_trip p) <=> P p
Proof
  simp[arith_split_round_trip_def]
QED

Definition arith_split_removed_def:
  arith_split_removed (p : bool) = p
End

Theorem arith_split_round_trip_removed[arith_split]:
  !P p. P (arith_split_removed p) <=> P p
Proof
  simp[arith_split_removed_def]
QED

val _ =
  if contains arith_round_trip_fact (linarithData.arith_facts ()) andalso
     contains arith_split_round_trip_rule
       (linarithData.arith_split_thms ())
  then ()
  else fail "attributes did not immediately update their theorem sets"

Theorem arith_round_trip_removed[arith]:
  arith_round_trip T
Proof
  simp[arith_round_trip_def]
QED

val removed_name =
  "linarithRoundTripBase.arith_round_trip_removed"
val removed_key =
  "linarithRoundTripBase$arith_round_trip_removed"
val _ = linarithData.remove_arith removed_name

(* The delta carries the table's own key rather than the spelling the
   retraction was written in: a descendant replays it as it stands. *)
val has_remove_delta =
  List.exists
    (fn ThmSetData.REMOVE name => name = removed_key | _ => false)
    (ThmSetData.current_data {settype = "arith"})

val _ =
  if has_remove_delta andalso
     not (contains arith_round_trip_removed (linarithData.arith_facts ()))
  then ()
  else fail "remove_arith did not write and apply its REMOVE delta"

val split_removed_name =
  "linarithRoundTripBase.arith_split_round_trip_removed"
val split_removed_key =
  "linarithRoundTripBase$arith_split_round_trip_removed"
val _ = linarithData.remove_arith_split split_removed_name

val has_split_remove_delta =
  List.exists
    (fn ThmSetData.REMOVE name => name = split_removed_key | _ => false)
    (ThmSetData.current_data {settype = "arith_split"})

val _ =
  if has_split_remove_delta andalso
     not (contains arith_split_round_trip_removed
       (linarithData.arith_split_thms ()))
  then ()
  else fail "remove_arith_split did not write and apply its REMOVE delta"

(* An unqualified retraction is the spelling that has no meaning of its
   own in a descendant theory: what it denotes is fixed here, in the
   theory that wrote it, and the delta below carries that key. *)
Theorem arith_round_trip_bare_removed[arith]:
  !p. arith_round_trip (arith_round_trip p) <=> p
Proof
  simp[arith_round_trip_def]
QED

Definition arith_split_bare_removed_def:
  arith_split_bare_removed (p : bool) = p
End

Theorem arith_split_round_trip_bare_removed[arith_split]:
  !P p. P (arith_split_bare_removed p) <=> P p
Proof
  simp[arith_split_bare_removed_def]
QED

val _ = linarithData.remove_arith "arith_round_trip_bare_removed"
val _ =
  linarithData.remove_arith_split "arith_split_round_trip_bare_removed"

fun retracted_here key settype =
  List.exists
    (fn ThmSetData.REMOVE name => name = key | _ => false)
    (ThmSetData.current_data {settype = settype})

val _ =
  if retracted_here
       "linarithRoundTripBase$arith_round_trip_bare_removed" "arith" andalso
     retracted_here
       "linarithRoundTripBase$arith_split_round_trip_bare_removed"
       "arith_split" andalso
     not (contains arith_round_trip_bare_removed
       (linarithData.arith_facts ())) andalso
     not (contains arith_split_round_trip_bare_removed
       (linarithData.arith_split_thms ()))
  then ()
  else fail "an unqualified retraction did not record the entry's key"
