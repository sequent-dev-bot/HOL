structure benchStringCorpus =
struct

open HolKernel autoSeedTheory

val goals : benchLib.source_goal list =
[{id = "string_L34_of_char_Char",
 goal = ``∀b0 b1 b2 b3 b4 b5 b6 b7.
  source_of_char (source_Char b0 b1 b2 b3 b4 b5 b6 b7) =
  source_horner8 b0 b1 b2 b3 b4 b5 b6 b7``,
 source_method = "by (simp add: of_char_def)",
 provenance = {file = "src/HOL/String.thy", line = 34, commit = "f7e02b7e"},
 representative = false},
{id = "string_L60_char_of_take_bit_eq",
 goal = ``∀width number.
  8 ≤ width ⇒
  source_char_of (source_take_bit width number) = source_char_of number``,
 source_method = "using that by (simp add: char_of_def bit_take_bit_iff)",
 provenance = {file = "src/HOL/String.thy", line = 60, commit = "f7e02b7e"},
 representative = false},
{id = "string_L68_char_of_comp_of_char",
 goal = ``source_char_of ∘ source_of_char = I``,
 source_method = "by (simp add: fun_eq_iff)",
 provenance = {file = "src/HOL/String.thy", line = 68, commit = "f7e02b7e"},
 representative = false},
{id = "string_L83_of_char_eqI",
 goal = ``∀left right. source_of_char left = source_of_char right ⇒ left = right``,
 source_method = "using that inj_of_char by (simp add: inj_eq)",
 provenance = {file = "src/HOL/String.thy", line = 83, commit = "f7e02b7e"},
 representative = false},
{id = "string_L87_of_char_eq_iff",
 goal = ``∀left right. source_of_char left = source_of_char right ⇔ left = right``,
 source_method = "by (auto intro: of_char_eqI)",
 provenance = {file = "src/HOL/String.thy", line = 87, commit = "f7e02b7e"},
 representative = false},
{id = "string_L131_char_of_eq_iff",
 goal = ``∀number character.
  source_char_of number = character ⇔
  source_take_bit 8 number = source_of_char character``,
 source_method = "by (auto intro: of_char_eqI simp add: take_bit_eq_mod)",
 provenance = {file = "src/HOL/String.thy", line = 131, commit = "f7e02b7e"},
 representative = false},
{id = "string_L135_char_of_nat",
 goal = ``∀number. source_char_of (source_of_nat number) = source_char_of number``,
 source_method = "by (simp add: char_of_def String.char_of_def drop_bit_of_nat bit_simps possible_bit_def)",
 provenance = {file = "src/HOL/String.thy", line = 135, commit = "f7e02b7e"},
 representative = false},
{id = "string_L344_char_of_integer_code",
 goal = ``∀number.
  source_char_of_integer number =
  (let
     (q0,b0) = source_bit_cut_integer number;
     (q1,b1) = source_bit_cut_integer q0;
     (q2,b2) = source_bit_cut_integer q1;
     (q3,b3) = source_bit_cut_integer q2;
     (q4,b4) = source_bit_cut_integer q3;
     (q5,b5) = source_bit_cut_integer q4;
     (q6,b6) = source_bit_cut_integer q5;
     (q7,b7) = source_bit_cut_integer q6
   in
     source_Char b0 b1 b2 b3 b4 b5 b6 b7)``,
 source_method = "by (simp add: bit_cut_integer_def char_of_integer_def char_of_def div_mult2_numeral_eq bit_iff_odd_drop_bit drop_bit_eq_div)",
 provenance = {file = "src/HOL/String.thy", line = 344, commit = "f7e02b7e"},
 representative = false},
{id = "string_L357_integer_of_char_code",
 goal = ``∀b0 b1 b2 b3 b4 b5 b6 b7.
  source_integer_of_char (source_Char b0 b1 b2 b3 b4 b5 b6 b7) =
  &source_horner8 b0 b1 b2 b3 b4 b5 b6 b7``,
 source_method = "by (simp add: integer_of_char_def of_char_def)",
 provenance = {file = "src/HOL/String.thy", line = 357, commit = "f7e02b7e"},
 representative = false},
{id = "string_L728_anon_L728",
 goal = ``source_Literal = source_Literal_prime``,
 source_method = "by simp",
 provenance = {file = "src/HOL/String.thy", line = 728, commit = "f7e02b7e"},
 representative = false},
{id = "string_L919_abort_cong",
 goal = ``∀message message' function.
  message = message' ⇒
  source_abort message function = source_abort message' function``,
 source_method = "by simp",
 provenance = {file = "src/HOL/String.thy", line = 919, commit = "f7e02b7e"},
 representative = false},
{id = "string_L178_card_UNIV_char",
 goal = ``CARD 𝕌(:char) = 256``,
 source_method = "by (auto simp add: UNIV_char_of_nat card_image)",
 provenance = {file = "src/HOL/String.thy", line = 178, commit = "f7e02b7e"},
 representative = true}]

end
