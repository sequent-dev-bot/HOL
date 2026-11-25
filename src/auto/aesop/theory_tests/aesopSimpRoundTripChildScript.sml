Theory aesopSimpRoundTripChild
Ancestors
  aesopSimpRoundTripBase

fun fail message =
  raise Fail ("aesop_simp round-trip child test: " ^ message)

val source =
  ``aesopSimpRoundTripBase$aesop_simp_round_trip T``
val result =
  snd
    (boolSyntax.dest_eq
      (concl
        (Conv.QCONV
          (simpLib.SIMP_CONV (aesopData.aesop_ss ()) [])
          source)))

val _ =
  if aconv result boolSyntax.T
  then ()
  else fail "the reloaded child lost its inherited aesop_simp rewrite"
