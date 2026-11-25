Theory stringAutoSeed
Ancestors
  string
Libs
  clasetLib clasimpLib

val sintro_spec =
  {kind = clasetRules.Intro, safe = true, prio = NONE}

(* src/HOL/String.thy:87-145,429-519 @ f7e02b7e. *)
Theorem ORD_11_AUTO[iff] = stringTheory.ORD_11
Theorem CHR_11_AUTO[iff] = stringTheory.CHR_11
Theorem EXPLODE_11_AUTO[iff] = stringTheory.EXPLODE_11
Theorem IMPLODE_11_AUTO[iff] = stringTheory.IMPLODE_11

Theorem IMPLODE_EQ_EMPTYSTRING_1_AUTO[iff] =
  GEN_ALL (CONJUNCT1 (SPEC_ALL stringTheory.IMPLODE_EQ_EMPTYSTRING))

Theorem IMPLODE_EQ_EMPTYSTRING_2_AUTO[iff] =
  GEN_ALL (CONJUNCT2 (SPEC_ALL stringTheory.IMPLODE_EQ_EMPTYSTRING))

Theorem EXPLODE_EQ_NIL_1_AUTO[iff] =
  GEN_ALL (CONJUNCT1 (SPEC_ALL stringTheory.EXPLODE_EQ_NIL))

Theorem EXPLODE_EQ_NIL_2_AUTO[iff] =
  GEN_ALL (CONJUNCT2 (SPEC_ALL stringTheory.EXPLODE_EQ_NIL))

Theorem STRLEN_EQ_0_AUTO[iff] = stringTheory.STRLEN_EQ_0
Theorem STRCAT_EQ_EMPTY_AUTO[iff] = stringTheory.STRCAT_EQ_EMPTY

val _ =
  List.app (clasetLib.export_rule sintro_spec)
    ["string.FINITE_UNIV_char", "string.WF_char_lt"]
