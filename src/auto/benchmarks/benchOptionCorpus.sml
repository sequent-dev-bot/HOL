structure benchOptionCorpus =
struct

open HolKernel autoSeedTheory

val goals : benchLib.source_goal list =
[{id = "option_L39_comp_the_Some",
 goal = ``THE ∘ SOME = I``,
 source_method = "by auto",
 provenance = {file = "src/HOL/Option.thy", line = 39, commit = "f7e02b7e"},
 representative = false},
{id = "option_L56_split_option_all",
 goal = ``(∀b_x. v_P0 b_x) ⇔ v_P0 NONE ∧ ∀b_x. v_P0 (SOME b_x)``,
 source_method = "by (auto intro: option.induct)",
 provenance = {file = "src/HOL/Option.thy", line = 56, commit = "f7e02b7e"},
 representative = false},
{id = "option_L59_split_option_ex",
 goal = ``(∃b_x. v_P0 b_x) ⇔ v_P0 NONE ∨ ∃b_x. v_P0 (SOME b_x)``,
 source_method = "using split_option_all[of \"\\<lambda>x. \\<not> P x\"] by blast",
 provenance = {file = "src/HOL/Option.thy", line = 59, commit = "f7e02b7e"},
 representative = false},
{id = "option_L62_UNIV_option_conv",
 goal = ``𝕌(:α option) = NONE INSERT IMAGE SOME 𝕌(:α)``,
 source_method = "by (auto intro: classical)",
 provenance = {file = "src/HOL/Option.thy", line = 62, commit = "f7e02b7e"},
 representative = false},
{id = "option_L91_ospec",
 goal = ``(∀b_x.
   b_x ∈ (λb_set_option b_set_item. b_set_option = SOME b_set_item) v_A0 ⇒
   v_P0 b_x) ⇒
v_A0 = SOME v_x0 ⇒
v_P0 v_x0``,
 source_method = "by simp",
 provenance = {file = "src/HOL/Option.thy", line = 91, commit = "f7e02b7e"},
 representative = false},
{id = "option_L102_map_option_case",
 goal = ``OPTION_MAP v_f0 v_y0 =
(λb_option_none b_option_some b_option_value.
     option_CASE b_option_value b_option_none b_option_some) NONE
  (λb_x. SOME (v_f0 b_x)) v_y0``,
 source_method = "by (auto split: option.split)",
 provenance = {file = "src/HOL/Option.thy", line = 102, commit = "f7e02b7e"},
 representative = false},
{id = "option_L105_map_option_is_None",
 goal = ``OPTION_MAP v_f0 v_opt0 = NONE ⇔ v_opt0 = NONE``,
 source_method = "by (simp add: map_option_case split: option.split)",
 provenance = {file = "src/HOL/Option.thy", line = 105, commit = "f7e02b7e"},
 representative = true},
{id = "option_L111_map_option_eq_Some",
 goal = ``OPTION_MAP v_f0 v_xo0 = SOME v_y0 ⇔ ∃b_z. v_xo0 = SOME b_z ∧ v_f0 b_z = v_y0``,
 source_method = "by (simp add: map_option_case split: option.split)",
 provenance = {file = "src/HOL/Option.thy", line = 111, commit = "f7e02b7e"},
 representative = false},
{id = "option_L130_None_notin_image_Some",
 goal = ``NONE ∉ IMAGE SOME v_A0``,
 source_method = "by auto",
 provenance = {file = "src/HOL/Option.thy", line = 130, commit = "f7e02b7e"},
 representative = false},
{id = "option_L136_rel_option_iff",
 goal = ``OPTREL v_R0 v_x0 v_y0 ⇔
(λ(b_a,b_b).
     (λb_option_none b_option_some b_option_value.
          option_CASE b_option_value b_option_none b_option_some)
       ((λb_option_none b_option_some b_option_value.
             option_CASE b_option_value b_option_none b_option_some) T
          (λb_a. F) b_b)
       (λb_x.
            (λb_option_none b_option_some b_option_value.
                 option_CASE b_option_value b_option_none b_option_some) F
              (λb_y. v_R0 b_x b_y) b_b) b_a) (v_x0,v_y0)``,
 source_method = "by (auto split: prod.split option.split)",
 provenance = {file = "src/HOL/Option.thy", line = 136, commit = "f7e02b7e"},
 representative = false},
{id = "option_L163_combine_options_assoc",
 goal = ``(∀b_x b_y b_z. v_f0 (v_f0 b_x b_y) b_z = v_f0 b_x (v_f0 b_y b_z)) ⇒
(λb_combine b_option_left b_option_right.
     case b_option_left of
       NONE => b_option_right
     | SOME b_combine_left =>
       case b_option_right of
         NONE => SOME b_combine_left
       | SOME b_combine_right =>
         SOME (b_combine b_combine_left b_combine_right)) v_f0
  ((λb_combine b_option_left b_option_right.
        case b_option_left of
          NONE => b_option_right
        | SOME b_combine_left =>
          case b_option_right of
            NONE => SOME b_combine_left
          | SOME b_combine_right =>
            SOME (b_combine b_combine_left b_combine_right)) v_f0 v_x0 v_y0)
  v_z0 =
(λb_combine b_option_left b_option_right.
     case b_option_left of
       NONE => b_option_right
     | SOME b_combine_left =>
       case b_option_right of
         NONE => SOME b_combine_left
       | SOME b_combine_right =>
         SOME (b_combine b_combine_left b_combine_right)) v_f0 v_x0
  ((λb_combine b_option_left b_option_right.
        case b_option_left of
          NONE => b_option_right
        | SOME b_combine_left =>
          case b_option_right of
            NONE => SOME b_combine_left
          | SOME b_combine_right =>
            SOME (b_combine b_combine_left b_combine_right)) v_f0 v_y0 v_z0)``,
 source_method = "by (auto simp: combine_options_def split: option.splits)",
 provenance = {file = "src/HOL/Option.thy", line = 163, commit = "f7e02b7e"},
 representative = false},
{id = "option_L169_combine_options_left_commute",
 goal = ``(∀b_x b_y. v_f0 b_x b_y = v_f0 b_y b_x) ⇒
(∀b_x b_y b_z. v_f0 (v_f0 b_x b_y) b_z = v_f0 b_x (v_f0 b_y b_z)) ⇒
(λb_combine b_option_left b_option_right.
     case b_option_left of
       NONE => b_option_right
     | SOME b_combine_left =>
       case b_option_right of
         NONE => SOME b_combine_left
       | SOME b_combine_right =>
         SOME (b_combine b_combine_left b_combine_right)) v_f0 v_y0
  ((λb_combine b_option_left b_option_right.
        case b_option_left of
          NONE => b_option_right
        | SOME b_combine_left =>
          case b_option_right of
            NONE => SOME b_combine_left
          | SOME b_combine_right =>
            SOME (b_combine b_combine_left b_combine_right)) v_f0 v_x0 v_z0) =
(λb_combine b_option_left b_option_right.
     case b_option_left of
       NONE => b_option_right
     | SOME b_combine_left =>
       case b_option_right of
         NONE => SOME b_combine_left
       | SOME b_combine_right =>
         SOME (b_combine b_combine_left b_combine_right)) v_f0 v_x0
  ((λb_combine b_option_left b_option_right.
        case b_option_left of
          NONE => b_option_right
        | SOME b_combine_left =>
          case b_option_right of
            NONE => SOME b_combine_left
          | SOME b_combine_right =>
            SOME (b_combine b_combine_left b_combine_right)) v_f0 v_y0 v_z0)``,
 source_method = "by (auto simp: combine_options_def split: option.splits)",
 provenance = {file = "src/HOL/Option.thy", line = 169, commit = "f7e02b7e"},
 representative = false},
{id = "option_L195_rel_option_unfold",
 goal = ``OPTREL v_R0 v_x0 v_y0 ⇔
(IS_NONE v_x0 ⇔ IS_NONE v_y0) ∧
(¬IS_NONE v_x0 ⇒ ¬IS_NONE v_y0 ⇒ v_R0 (THE v_x0) (THE v_y0))``,
 source_method = "by (simp add: rel_option_iff split: option.split)",
 provenance = {file = "src/HOL/Option.thy", line = 195, commit = "f7e02b7e"},
 representative = false},
{id = "option_L200_rel_optionI",
 goal = ``(IS_NONE v_x0 ⇔ IS_NONE v_y0) ⇒
(¬IS_NONE v_x0 ⇒ ¬IS_NONE v_y0 ⇒ v_P0 (THE v_x0) (THE v_y0)) ⇒
OPTREL v_P0 v_x0 v_y0``,
 source_method = "by (simp add: rel_option_unfold)",
 provenance = {file = "src/HOL/Option.thy", line = 200, commit = "f7e02b7e"},
 representative = false},
{id = "option_L205_is_none_map_option",
 goal = ``IS_NONE (OPTION_MAP v_f0 v_x0) ⇔ IS_NONE v_x0``,
 source_method = "by (simp add: is_none_def)",
 provenance = {file = "src/HOL/Option.thy", line = 205, commit = "f7e02b7e"},
 representative = false},
{id = "option_L208_the_map_option",
 goal = ``¬IS_NONE v_x0 ⇒ THE (OPTION_MAP v_f0 v_x0) = v_f0 (THE v_x0)``,
 source_method = "by (auto simp add: is_none_def)",
 provenance = {file = "src/HOL/Option.thy", line = 208, commit = "f7e02b7e"},
 representative = false},
{id = "option_L257_bind_option_cong_code",
 goal = ``v_x0 = v_y0 ⇒ OPTION_BIND v_x0 v_f0 = OPTION_BIND v_y0 v_f0``,
 source_method = "by simp",
 provenance = {file = "src/HOL/Option.thy", line = 257, commit = "f7e02b7e"},
 representative = false},
{id = "option_L288_these_empty",
 goal = ``(λb_these_source b_these_item. SOME b_these_item ∈ b_these_source) ∅ = ∅``,
 source_method = "by (simp add: these_def)",
 provenance = {file = "src/HOL/Option.thy", line = 288, commit = "f7e02b7e"},
 representative = false},
{id = "option_L291_these_insert_None",
 goal = ``(λb_these_source b_these_item. SOME b_these_item ∈ b_these_source)
  (NONE INSERT v_A0) =
(λb_these_source b_these_item. SOME b_these_item ∈ b_these_source) v_A0``,
 source_method = "by (auto simp add: these_def)",
 provenance = {file = "src/HOL/Option.thy", line = 291, commit = "f7e02b7e"},
 representative = false},
{id = "option_L311_these_image_Some_eq",
 goal = ``(λb_these_source b_these_item. SOME b_these_item ∈ b_these_source)
  (IMAGE SOME v_A0) = v_A0``,
 source_method = "by (auto simp add: these_def intro!: image_eqI)",
 provenance = {file = "src/HOL/Option.thy", line = 311, commit = "f7e02b7e"},
 representative = false},
{id = "option_L314_Some_image_these_eq",
 goal = ``IMAGE SOME
  ((λb_these_source b_these_item. SOME b_these_item ∈ b_these_source) v_A0) =
(λb_x. b_x ∈ v_A0 ∧ b_x ≠ NONE)``,
 source_method = "by (auto simp add: these_def image_image intro!: image_eqI)",
 provenance = {file = "src/HOL/Option.thy", line = 314, commit = "f7e02b7e"},
 representative = false},
{id = "option_L317_these_empty_eq",
 goal = ``(λb_these_source b_these_item. SOME b_these_item ∈ b_these_source) v_B0 = ∅ ⇔
v_B0 = ∅ ∨ v_B0 = {NONE}``,
 source_method = "by (auto simp add: these_def)",
 provenance = {file = "src/HOL/Option.thy", line = 317, commit = "f7e02b7e"},
 representative = false},
{id = "option_L320_these_not_empty_eq",
 goal = ``(λb_these_source b_these_item. SOME b_these_item ∈ b_these_source) v_B0 ≠ ∅ ⇔
v_B0 ≠ ∅ ∧ v_B0 ≠ {NONE}``,
 source_method = "by (auto simp add: these_empty_eq)",
 provenance = {file = "src/HOL/Option.thy", line = 320, commit = "f7e02b7e"},
 representative = false},
{id = "option_L328_finite_range_Some",
 goal = ``FINITE (IMAGE SOME 𝕌(:α)) ⇔ FINITE 𝕌(:α)``,
 source_method = "by (auto dest: finite_imageD intro: inj_Some)",
 provenance = {file = "src/HOL/Option.thy", line = 328, commit = "f7e02b7e"},
 representative = false},
{id = "option_L337_option_bind_transfer",
 goal = ``(λb_rel_left b_rel_right b_rel_left_function b_rel_right_function.
     ∀b_rel_x b_rel_y.
       b_rel_left b_rel_x b_rel_y ⇒
       b_rel_right (b_rel_left_function b_rel_x)
         (b_rel_right_function b_rel_y)) (OPTREL v_A0)
  ((λb_rel_left b_rel_right b_rel_left_function b_rel_right_function.
        ∀b_rel_x b_rel_y.
          b_rel_left b_rel_x b_rel_y ⇒
          b_rel_right (b_rel_left_function b_rel_x)
            (b_rel_right_function b_rel_y))
     ((λb_rel_left b_rel_right b_rel_left_function b_rel_right_function.
           ∀b_rel_x b_rel_y.
             b_rel_left b_rel_x b_rel_y ⇒
             b_rel_right (b_rel_left_function b_rel_x)
               (b_rel_right_function b_rel_y)) v_A0 (OPTREL v_B0))
     (OPTREL v_B0)) OPTION_BIND OPTION_BIND``,
 source_method = "unfolding rel_fun_def split_option_all by simp",
 provenance = {file = "src/HOL/Option.thy", line = 337, commit = "f7e02b7e"},
 representative = false},
{id = "option_L351_finite_option_UNIV",
 goal = ``FINITE 𝕌(:α option) ⇔ FINITE 𝕌(:α)``,
 source_method = "by (auto simp add: UNIV_option_conv elim: finite_imageD intro: inj_Some)",
 provenance = {file = "src/HOL/Option.thy", line = 351, commit = "f7e02b7e"},
 representative = false},
{id = "option_L361_equal_None_code_unfold_1",
 goal = ``(λb_equal_left b_equal_right. b_equal_left = b_equal_right) v_x0 NONE ⇔
IS_NONE v_x0``,
 source_method = "by (auto simp add: equal Option.is_none_def)",
 provenance = {file = "src/HOL/Option.thy", line = 361, commit = "f7e02b7e"},
 representative = false},
{id = "option_L361_equal_None_code_unfold_2",
 goal = ``(λb_equal_left b_equal_right. b_equal_left = b_equal_right) NONE = IS_NONE``,
 source_method = "by (auto simp add: equal Option.is_none_def)",
 provenance = {file = "src/HOL/Option.thy", line = 361, commit = "f7e02b7e"},
 representative = false}]

end
