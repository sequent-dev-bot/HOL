Theory iffRoundTripChild
Ancestors
  iffRoundTripBase
Libs
  clasimpLib iffTestSupport

fun fail message = failer "iff round-trip child test" message

val live_name = "iffRoundTripBase$iff_round_trip_live_rule"
val removed_name = "iffRoundTripBase$iff_round_trip_removed_rule"
val neg_name = "iffRoundTripBase$iff_round_trip_neg_rule"
val plain_name = "iffRoundTripBase$iff_round_trip_plain_rule"
val neg_removed_name =
  "iffRoundTripBase$iff_round_trip_neg_removed_rule"
val delsimp_name = "iffRoundTripBase$iff_round_trip_delsimp_rule"
val predelsimp_name = "iffRoundTripBase$iff_round_trip_predelsimp_rule"
val bare_name = "iffRoundTripBase$iff_round_trip_bare_rule"

val _ =
  let
    val source = ``iffRoundTripBase$iff_round_trip_live T``
    val ordinary =
      Conv.QCONV (simpLib.SIMP_CONV (BasicProvers.srw_ss ()) []) source
    val excluded =
      Conv.QCONV
        (simpLib.SIMP_CONV (BasicProvers.srw_ss ())
          [markerLib.Excl
             "iffRoundTripBase.iff_round_trip_live_rule"])
        source
  in
    if aconv (snd (boolSyntax.dest_eq (concl ordinary))) boolSyntax.T andalso
       aconv (snd (boolSyntax.dest_eq (concl excluded))) source andalso
       has_iff_rules live_name
    then ()
    else fail "Excl did not disable only the named iff rewrite"
  end

val _ =
  if not (has_iff_rules live_name)
  then fail "the reloaded child claset lost its inherited declaration"
  else if not (has_iff_rewrite live_name)
  then fail "the reloaded child simpsets lost the inherited declaration"
  else if has_any_iff_rules removed_name
  then fail "the removed declaration reappeared in the child claset"
  else if has_iff_rewrite removed_name
  then fail "the removed declaration reappeared in the child simpsets"
  else if not (has_iff_rules_of NegShape neg_name)
  then fail "the reloaded child lost the negated declaration's elim rule"
  else if not (has_iff_rewrite neg_name)
  then fail "the reloaded child lost the negated declaration's rewrite"
  else if not (has_iff_rules_of PlainShape plain_name)
  then fail "the reloaded child lost the plain declaration's intro rule"
  else if not (has_iff_rewrite plain_name)
  then fail "the reloaded child lost the plain declaration's rewrite"
  else if has_any_iff_rules neg_removed_name
  then fail "a retracted elim rule reappeared in the child claset"
  else if has_iff_rewrite neg_removed_name
  then fail "a retracted negated declaration reappeared in the child"
  else if has_iff_rewrite delsimp_name
  then fail "the persistent delsimps removal was lost in the child"
  else if not (has_iff_rules delsimp_name)
  then fail "delsimps removed the child claset view"
  else if has_iff_rewrite predelsimp_name
  then fail "the delsimps recorded before the declaration was lost"
  else if not (has_iff_rules predelsimp_name)
  then fail "the early delsimps removed the child claset view"
  else if not (has_iff_rewrite bare_name)
  then fail "a bare delsimps suppressed an unrelated inherited declaration"
  else if not (has_iff_rules bare_name)
  then fail "a bare delsimps removed the child claset view"
  else ()

(* The iff batch is a fragment of its own, so a theory's [simp] and [iff]
   streams can be switched off independently. *)
val _ =
  let
    val iff_source = ``iffRoundTripBase$iff_round_trip_live T``
    val simp_source = ``iffRoundTripBase$iff_round_trip_simp T``
    fun simplify controls source =
      snd
        (boolSyntax.dest_eq
          (concl
            (Conv.QCONV
              (simpLib.SIMP_CONV (BasicProvers.srw_ss ()) controls)
              source)))
    val without_simp = [markerLib.ExclSF "iffRoundTripBase"]
    val without_iff = [markerLib.ExclSF "iffRoundTripBase-iff"]
  in
    if not (aconv (simplify without_simp iff_source) boolSyntax.T)
    then fail "excluding the simp fragment also lost the iff rewrites"
    else if aconv (simplify without_simp simp_source) boolSyntax.F
    then fail "excluding the simp fragment left its rewrites in place"
    else if not (aconv (simplify without_iff simp_source) boolSyntax.F)
    then fail "excluding the iff fragment also lost the simp rewrites"
    else if not (aconv (simplify without_iff iff_source) iff_source)
    then fail "excluding the iff fragment left its rewrites in place"
    else ()
  end

(* A bare name names the declaration wherever it was made; defaulting the
   theory part to this one would retract nothing, silently. *)
val _ = clasimpLib.remove_iff "iff_round_trip_plain_rule"

val _ =
  if has_any_iff_rules plain_name
  then fail "a bare remove_iff did not reach the ancestor's declaration"
  else if has_iff_rewrite plain_name
  then fail "a bare remove_iff left the ancestor's rewrite installed"
  else ()
