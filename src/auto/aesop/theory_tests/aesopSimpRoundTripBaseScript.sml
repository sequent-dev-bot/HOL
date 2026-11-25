Theory aesopSimpRoundTripBase
Ancestors
  bool
Libs
  aesopData

fun fail message =
  raise Fail ("aesop_simp round-trip base test: " ^ message)

Definition aesop_simp_round_trip_def:
  aesop_simp_round_trip (p : bool) = p
End

Theorem aesop_simp_round_trip_rule[aesop_simp]:
  !p. aesop_simp_round_trip p <=> p
Proof
  simp[aesop_simp_round_trip_def]
QED

val source = ``aesop_simp_round_trip T``
val result =
  snd
    (boolSyntax.dest_eq
      (concl
        (Conv.QCONV
          (simpLib.SIMP_CONV (aesopData.aesop_ss ()) [])
          source)))

val _ =
  if aconv result boolSyntax.T andalso
     not (null (ThmSetData.current_data {settype = "aesop_simp"}))
  then ()
  else fail "the attribute did not immediately update aesop_ss"
