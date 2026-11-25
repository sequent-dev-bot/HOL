Theory linarithRoundTripChild
Ancestors
  linarithRoundTripBase

fun fail message =
  raise Fail ("linarith round-trip child test: " ^ message)

fun count theorem theorems =
  List.length
    (List.filter
      (fn candidate => aconv (concl candidate) (concl theorem)) theorems)

val fact_count =
  count linarithRoundTripBaseTheory.arith_round_trip_fact
    (linarithData.arith_facts ())
val split_count =
  count linarithRoundTripBaseTheory.arith_split_round_trip_rule
    (linarithData.arith_split_thms ())
val removed_count =
  count linarithRoundTripBaseTheory.arith_round_trip_removed
    (linarithData.arith_facts ())
val split_removed_count =
  count linarithRoundTripBaseTheory.arith_split_round_trip_removed
    (linarithData.arith_split_thms ())

(* The two an unqualified retraction named.  Resolving that name here,
   where the delta is replayed, would look for a declaration of this
   theory and leave the base theory's live. *)
val bare_removed_count =
  count linarithRoundTripBaseTheory.arith_round_trip_bare_removed
    (linarithData.arith_facts ())
val split_bare_removed_count =
  count linarithRoundTripBaseTheory.arith_split_round_trip_bare_removed
    (linarithData.arith_split_thms ())

val _ =
  if fact_count = 1 andalso split_count = 1 andalso
     removed_count = 0 andalso split_removed_count = 0 andalso
     bare_removed_count = 0 andalso split_bare_removed_count = 0
  then ()
  else fail "reload lost, duplicated, or resurrected an inherited theorem"
