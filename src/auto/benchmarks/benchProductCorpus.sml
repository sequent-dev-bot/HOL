structure benchProductCorpus =
struct

open HolKernel autoSeedTheory

val goals : benchLib.source_goal list =
[{id = "product_type_L140_less_eq_unit",
 goal = ``∀u v. source_unit_le u v``,
 source_method = "by (simp add: less_eq_unit_def)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 140, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L107_unit_all_eq1",
 goal = ``(∀b_x. v_P0 b_x) ⇔ v_P0 ()``,
 source_method = "by simp",
 provenance = {file = "src/HOL/Product_Type.thy", line = 107, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L122_UNIV_unit",
 goal = ``𝕌(:unit) = {()}``,
 source_method = "by auto",
 provenance = {file = "src/HOL/Product_Type.thy", line = 122, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L419_Pair_inject",
 goal = ``(v_a0,v_b0) = (v_a_0,v_b_0) ⇒ (v_a0 = v_a_0 ⇒ v_b0 = v_b_0 ⇒ v_R0) ⇒ v_R0``,
 source_method = "by simp",
 provenance = {file = "src/HOL/Product_Type.thy", line = 419, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L425_fst_eqD",
 goal = ``FST (v_x0,v_y0) = v_a0 ⇒ v_x0 = v_a0``,
 source_method = "by simp",
 provenance = {file = "src/HOL/Product_Type.thy", line = 425, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L428_snd_eqD",
 goal = ``SND (v_x0,v_y0) = v_a0 ⇒ v_y0 = v_a0``,
 source_method = "by simp",
 provenance = {file = "src/HOL/Product_Type.thy", line = 428, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L431_case_prod_unfold",
 goal = ``UNCURRY = (λb_c b_p. b_c (FST b_p) (SND b_p))``,
 source_method = "by (simp add: fun_eq_iff split: prod.split)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 431, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L442_prod_eqI",
 goal = ``FST v_p0 = FST v_q0 ⇒ SND v_p0 = SND v_q0 ⇒ v_p0 = v_q0``,
 source_method = "by (simp add: prod_eq_iff)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 442, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L451_case_prod_Pair",
 goal = ``(λ(b_pair_left,b_pair_right). (b_pair_left,b_pair_right)) = I``,
 source_method = "by (simp add: fun_eq_iff split: prod.split)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 451, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L454_case_prod_eta",
 goal = ``(λ(b_x,b_y). v_f0 (b_x,b_y)) = v_f0``,
 source_method = "by (simp add: fun_eq_iff split: prod.split)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 454, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L466_The_case_prod",
 goal = ``CHOICE (UNCURRY v_P0) = CHOICE (λb_xy. v_P0 (FST b_xy) (SND b_xy))``,
 source_method = "by (simp add: case_prod_unfold)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 466, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L469_cond_case_prod_eta",
 goal = ``(∀b_x b_y. v_f0 b_x b_y = v_g0 (b_x,b_y)) ⇒ (λ(b_x,b_y). v_f0 b_x b_y) = v_g0``,
 source_method = "by (simp add: case_prod_eta)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 469, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L527_split_paired_The",
 goal = ``CHOICE (λb_x. v_P0 b_x) = CHOICE (λ(b_a,b_b). v_P0 (b_a,b_b))``,
 source_method = "by (simp add: case_prod_eta)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 527, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L587_case_prod_beta_",
 goal = ``(λ(b_x,b_y). v_f0 b_x b_y) = (λb_x. v_f0 (FST b_x) (SND b_x))``,
 source_method = "by (auto simp: fun_eq_iff)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 587, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L596_case_prodI2",
 goal = ``(∀b_a b_b. v_p0 = (b_a,b_b) ⇒ v_c0 b_a b_b) ⇒ (λ(b_a,b_b). v_c0 b_a b_b) v_p0``,
 source_method = "by (simp add: split_tupled_all)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 596, commit = "f7e02b7e"},
 representative = true},
{id = "product_type_L600_case_prodI2_",
 goal = ``(∀b_a b_b. (b_a,b_b) = v_p0 ⇒ v_c0 b_a b_b v_x0) ⇒
(λ(b_a,b_b). v_c0 b_a b_b) v_p0 v_x0``,
 source_method = "by (simp add: split_tupled_all)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 600, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L622_case_prodD_",
 goal = ``(λ(b_c,b_d). v_R0 b_c b_d) (v_a0,v_b0) v_c0 ⇒ v_R0 v_a0 v_b0 v_c0``,
 source_method = "by simp",
 provenance = {file = "src/HOL/Product_Type.thy", line = 622, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L625_mem_case_prodI",
 goal = ``v_z0 ∈ v_c0 v_a0 v_b0 ⇒ v_z0 ∈ (λ(b_d,b_e). v_c0 b_d b_e) (v_a0,v_b0)``,
 source_method = "by simp",
 provenance = {file = "src/HOL/Product_Type.thy", line = 625, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L685_Collect_const_case_prod",
 goal = ``(λ(b_a,b_b). v_P0) = if v_P0 then 𝕌(:α # β) else ∅``,
 source_method = "by auto",
 provenance = {file = "src/HOL/Product_Type.thy", line = 685, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L688_The_split_eq",
 goal = ``CHOICE (λ(b_x_,b_y_). v_x0 = b_x_ ∧ v_y0 = b_y_) = (v_x0,v_y0)``,
 source_method = "by blast",
 provenance = {file = "src/HOL/Product_Type.thy", line = 688, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L785_curry_conv",
 goal = ``CURRY v_f0 v_a0 v_b0 = v_f0 (v_a0,v_b0)``,
 source_method = "by (simp add: curry_def)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 785, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L788_curryI",
 goal = ``v_f0 (v_a0,v_b0) ⇒ CURRY v_f0 v_a0 v_b0``,
 source_method = "by (simp add: curry_def)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 788, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L791_curryD",
 goal = ``CURRY v_f0 v_a0 v_b0 ⇒ v_f0 (v_a0,v_b0)``,
 source_method = "by (simp add: curry_def)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 791, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L794_curryE",
 goal = ``CURRY v_f0 v_a0 v_b0 ⇒ (v_f0 (v_a0,v_b0) ⇒ v_Q0) ⇒ v_Q0``,
 source_method = "by (simp add: curry_def)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 794, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L797_curry_case_prod",
 goal = ``CURRY (UNCURRY v_f0) = v_f0``,
 source_method = "by (simp add: curry_def case_prod_unfold)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 797, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L800_case_prod_curry",
 goal = ``UNCURRY (CURRY v_f0) = v_f0``,
 source_method = "by (simp add: curry_def case_prod_unfold)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 800, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L803_curry_K",
 goal = ``CURRY (λb_x. v_c0) = (λb_x b_y. v_c0)``,
 source_method = "by (simp add: fun_eq_iff)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 803, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L823_scomp_unfold",
 goal = ``(λb_scomp_source b_scomp_combine b_scomp_input.
     b_scomp_combine (FST (b_scomp_source b_scomp_input))
       (SND (b_scomp_source b_scomp_input))) =
(λb_f b_g b_x. b_g (FST (b_f b_x)) (SND (b_f b_x)))``,
 source_method = "by (simp add: fun_eq_iff scomp_def case_prod_unfold)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 823, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L826_scomp_apply",
 goal = ``(λb_scomp_source b_scomp_combine b_scomp_input.
     b_scomp_combine (FST (b_scomp_source b_scomp_input))
       (SND (b_scomp_source b_scomp_input))) v_f0 v_g0 v_x0 =
UNCURRY v_g0 (v_f0 v_x0)``,
 source_method = "by (simp add: scomp_unfold case_prod_unfold)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 826, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L829_Pair_scomp",
 goal = ``(λb_scomp_source b_scomp_combine b_scomp_input.
     b_scomp_combine (FST (b_scomp_source b_scomp_input))
       (SND (b_scomp_source b_scomp_input)))
  ((λb_pair_left b_pair_right. (b_pair_left,b_pair_right)) v_x0) v_f0 =
v_f0 v_x0``,
 source_method = "by (simp add: fun_eq_iff)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 829, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L832_scomp_Pair",
 goal = ``(λb_scomp_source b_scomp_combine b_scomp_input.
     b_scomp_combine (FST (b_scomp_source b_scomp_input))
       (SND (b_scomp_source b_scomp_input))) v_x0
  (λb_pair_left b_pair_right. (b_pair_left,b_pair_right)) = v_x0``,
 source_method = "by (simp add: fun_eq_iff)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 832, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L835_scomp_scomp",
 goal = ``(λb_scomp_source b_scomp_combine b_scomp_input.
     b_scomp_combine (FST (b_scomp_source b_scomp_input))
       (SND (b_scomp_source b_scomp_input)))
  ((λb_scomp_source b_scomp_combine b_scomp_input.
        b_scomp_combine (FST (b_scomp_source b_scomp_input))
          (SND (b_scomp_source b_scomp_input))) v_f0 v_g0) v_h0 =
(λb_scomp_source b_scomp_combine b_scomp_input.
     b_scomp_combine (FST (b_scomp_source b_scomp_input))
       (SND (b_scomp_source b_scomp_input))) v_f0
  (λb_x.
       (λb_scomp_source b_scomp_combine b_scomp_input.
            b_scomp_combine (FST (b_scomp_source b_scomp_input))
              (SND (b_scomp_source b_scomp_input))) (v_g0 b_x) v_h0)``,
 source_method = "by (simp add: fun_eq_iff scomp_unfold)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 835, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L838_scomp_fcomp",
 goal = ``(λb_fcomp_first b_fcomp_second b_fcomp_input.
     b_fcomp_second (b_fcomp_first b_fcomp_input))
  ((λb_scomp_source b_scomp_combine b_scomp_input.
        b_scomp_combine (FST (b_scomp_source b_scomp_input))
          (SND (b_scomp_source b_scomp_input))) v_f0 v_g0) v_h0 =
(λb_scomp_source b_scomp_combine b_scomp_input.
     b_scomp_combine (FST (b_scomp_source b_scomp_input))
       (SND (b_scomp_source b_scomp_input))) v_f0
  (λb_x.
       (λb_fcomp_first b_fcomp_second b_fcomp_input.
            b_fcomp_second (b_fcomp_first b_fcomp_input)) (v_g0 b_x) v_h0)``,
 source_method = "by (simp add: fun_eq_iff scomp_unfold fcomp_def)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 838, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L841_fcomp_scomp",
 goal = ``(λb_scomp_source b_scomp_combine b_scomp_input.
     b_scomp_combine (FST (b_scomp_source b_scomp_input))
       (SND (b_scomp_source b_scomp_input)))
  ((λb_fcomp_first b_fcomp_second b_fcomp_input.
        b_fcomp_second (b_fcomp_first b_fcomp_input)) v_f0 v_g0) v_h0 =
(λb_fcomp_first b_fcomp_second b_fcomp_input.
     b_fcomp_second (b_fcomp_first b_fcomp_input)) v_f0
  ((λb_scomp_source b_scomp_combine b_scomp_input.
        b_scomp_combine (FST (b_scomp_source b_scomp_input))
          (SND (b_scomp_source b_scomp_input))) v_g0 v_h0)``,
 source_method = "by (simp add: fun_eq_iff scomp_unfold)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 841, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L856_map_prod_simp",
 goal = ``(λb_map_left b_map_right b_map_pair.
     (b_map_left (FST b_map_pair),b_map_right (SND b_map_pair))) v_f0 v_g0
  (v_a0,v_b0) = (v_f0 v_a0,v_g0 v_b0)``,
 source_method = "by (simp add: map_prod_def)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 856, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L900_apfst_conv",
 goal = ``(λb_apfst_func b_apfst_pair.
     (b_apfst_func (FST b_apfst_pair),SND b_apfst_pair)) v_f0 (v_x0,v_y0) =
(v_f0 v_x0,v_y0)``,
 source_method = "by (simp add: apfst_def)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 900, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L903_apsnd_conv",
 goal = ``(λb_apsnd_func b_apsnd_pair.
     (FST b_apsnd_pair,b_apsnd_func (SND b_apsnd_pair))) v_f0 (v_x0,v_y0) =
(v_x0,v_f0 v_y0)``,
 source_method = "by (simp add: apsnd_def)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 903, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L909_fst_comp_apfst",
 goal = ``FST ∘
(λb_apfst_func b_apfst_pair.
     (b_apfst_func (FST b_apfst_pair),SND b_apfst_pair)) v_f0 = v_f0 ∘ FST``,
 source_method = "by (simp add: fun_eq_iff)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 909, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L915_fst_comp_apsnd",
 goal = ``FST ∘
(λb_apsnd_func b_apsnd_pair.
     (FST b_apsnd_pair,b_apsnd_func (SND b_apsnd_pair))) v_f0 = FST``,
 source_method = "by (simp add: fun_eq_iff)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 915, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L921_snd_comp_apfst",
 goal = ``SND ∘
(λb_apfst_func b_apfst_pair.
     (b_apfst_func (FST b_apfst_pair),SND b_apfst_pair)) v_f0 = SND``,
 source_method = "by (simp add: fun_eq_iff)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 921, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L927_snd_comp_apsnd",
 goal = ``SND ∘
(λb_apsnd_func b_apsnd_pair.
     (FST b_apsnd_pair,b_apsnd_func (SND b_apsnd_pair))) v_f0 = v_f0 ∘ SND``,
 source_method = "by (simp add: fun_eq_iff)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 927, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L942_apfst_id",
 goal = ``(λb_apfst_func b_apfst_pair.
     (b_apfst_func (FST b_apfst_pair),SND b_apfst_pair)) I = I``,
 source_method = "by (simp add: fun_eq_iff)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 942, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L945_apsnd_id",
 goal = ``(λb_apsnd_func b_apsnd_pair.
     (FST b_apsnd_pair,b_apsnd_func (SND b_apsnd_pair))) I = I``,
 source_method = "by (simp add: fun_eq_iff)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 945, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L954_apsnd_apfst_commute",
 goal = ``(λb_apsnd_func b_apsnd_pair.
     (FST b_apsnd_pair,b_apsnd_func (SND b_apsnd_pair))) v_f0
  ((λb_apfst_func b_apfst_pair.
        (b_apfst_func (FST b_apfst_pair),SND b_apfst_pair)) v_g0 v_p0) =
(λb_apfst_func b_apfst_pair.
     (b_apfst_func (FST b_apfst_pair),SND b_apfst_pair)) v_g0
  ((λb_apsnd_func b_apsnd_pair.
        (FST b_apsnd_pair,b_apsnd_func (SND b_apsnd_pair))) v_f0 v_p0)``,
 source_method = "by simp",
 provenance = {file = "src/HOL/Product_Type.thy", line = 954, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L967_swap_simp",
 goal = ``(λb_swap_pair. (SND b_swap_pair,FST b_swap_pair)) (v_x0,v_y0) = (v_y0,v_x0)``,
 source_method = "by (simp add: prod.swap_def)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 967, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L973_swap_comp_swap",
 goal = ``(λb_swap_pair. (SND b_swap_pair,FST b_swap_pair)) ∘
(λb_swap_pair. (SND b_swap_pair,FST b_swap_pair)) = I``,
 source_method = "by (simp add: fun_eq_iff)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 973, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L976_pair_in_swap_image",
 goal = ``(v_y0,v_x0) ∈ IMAGE (λb_swap_pair. (SND b_swap_pair,FST b_swap_pair)) v_A0 ⇔
(v_x0,v_y0) ∈ v_A0``,
 source_method = "by (auto intro!: image_eqI)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 976, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L988_bij_swap",
 goal = ``BIJ (λb_swap_pair. (SND b_swap_pair,FST b_swap_pair)) 𝕌(:α # β) 𝕌(:β # α)``,
 source_method = "by (simp add: bij_def)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 988, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1000_split_pairs",
 goal = ``(v_A0,v_B0) = v_X0 ⇔ FST v_X0 = v_A0 ∧ SND v_X0 = v_B0``,
 source_method = "by auto",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1000, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1000_split_pairs2",
 goal = ``v_X0 = (v_A0,v_B0) ⇔ FST v_X0 = v_A0 ∧ SND v_X0 = v_B0``,
 source_method = "by auto",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1000, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1028_SigmaI",
 goal = ``v_a0 ∈ v_A0 ⇒
v_b0 ∈ v_B0 v_a0 ⇒
(v_a0,v_b0) ∈
(source_Sigma v_A0 v_B0)``,
 source_method = "unfolding Sigma_def by blast",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1028, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1031_SigmaE",
 goal = ``v_c0 ∈
(source_Sigma v_A0 v_B0) ⇒
(∀b_x b_y. b_x ∈ v_A0 ⇒ b_y ∈ v_B0 b_x ⇒ v_c0 = (b_x,b_y) ⇒ v_P0) ⇒
v_P0``,
 source_method = "unfolding Sigma_def by blast",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1031, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1040_SigmaD1",
 goal = ``(v_a0,v_b0) ∈
(source_Sigma v_A0 v_B0) ⇒
v_a0 ∈ v_A0``,
 source_method = "by blast",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1040, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1043_SigmaD2",
 goal = ``(v_a0,v_b0) ∈
(source_Sigma v_A0 v_B0) ⇒
v_b0 ∈ v_B0 v_a0``,
 source_method = "by blast",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1043, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1046_SigmaE2",
 goal = ``(v_a0,v_b0) ∈
(source_Sigma v_A0 v_B0) ⇒
(v_a0 ∈ v_A0 ⇒ v_b0 ∈ v_B0 v_a0 ⇒ v_P0) ⇒
v_P0``,
 source_method = "by blast",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1046, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1049_Sigma_cong",
 goal = ``v_A0 = v_B0 ⇒
(∀b_x. b_x ∈ v_B0 ⇒ v_C0 b_x = v_D0 b_x) ⇒
(source_Sigma v_A0 (λb_x. v_C0 b_x)) =
(source_Sigma v_B0 (λb_x. v_D0 b_x))``,
 source_method = "by auto",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1049, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1052_Sigma_mono",
 goal = ``v_A0 ⊆ v_C0 ⇒
(∀b_x. b_x ∈ v_A0 ⇒ v_B0 b_x ⊆ v_D0 b_x) ⇒
(source_Sigma v_A0 v_B0) ⊆
(source_Sigma v_C0 v_D0)``,
 source_method = "by blast",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1052, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1055_Sigma_empty1",
 goal = ``(source_Sigma ∅ v_B0) = ∅``,
 source_method = "by blast",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1055, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1058_Sigma_empty2",
 goal = ``(source_Sigma v_A0 (λb_uu_. ∅)) = ∅``,
 source_method = "by blast",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1058, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1064_UNIV_Times_UNIV",
 goal = ``(source_Sigma 𝕌(:α) (λb_uu_. 𝕌(:β))) = 𝕌(:α # β)``,
 source_method = "by auto",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1064, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1067_Compl_Times_UNIV1",
 goal = ``COMPL
  (source_Sigma 𝕌(:α) (λb_uu_. v_A0)) =
(source_Sigma 𝕌(:α) (λb_uu_. COMPL v_A0))``,
 source_method = "by auto",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1067, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1070_Compl_Times_UNIV2",
 goal = ``COMPL
  (source_Sigma v_A0 (λb_uu_. 𝕌(:β))) =
(source_Sigma (COMPL v_A0) (λb_uu_. 𝕌(:β)))``,
 source_method = "by auto",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1070, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1073_mem_Sigma_iff",
 goal = ``(v_a0,v_b0) ∈
(source_Sigma v_A0 v_B0) ⇔
v_a0 ∈ v_A0 ∧ v_b0 ∈ v_B0 v_a0``,
 source_method = "by blast",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1073, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1079_Sigma_empty_iff",
 goal = ``(source_Sigma v_I0 (λb_i. v_X0 b_i)) = ∅ ⇔
∀b_i. b_i ∈ v_I0 ⇒ v_X0 b_i = ∅``,
 source_method = "by auto",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1079, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1082_Times_subset_cancel2",
 goal = ``v_x0 ∈ v_C0 ⇒
((source_Sigma v_A0 (λb_uu_. v_C0)) ⊆
 (source_Sigma v_B0 (λb_uu_. v_C0)) ⇔ v_A0 ⊆ v_B0)``,
 source_method = "by blast",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1082, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1085_Times_eq_cancel2",
 goal = ``v_x0 ∈ v_C0 ⇒
((source_Sigma v_A0 (λb_uu_. v_C0)) =
 (source_Sigma v_B0 (λb_uu_. v_C0)) ⇔ v_A0 = v_B0)``,
 source_method = "by (blast elim: equalityE)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1085, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1088_Collect_case_prod_Sigma",
 goal = ``(λ(b_x,b_y). v_P0 b_x ∧ v_Q0 b_x b_y) =
(source_Sigma v_P0 (λb_x. v_Q0 b_x))``,
 source_method = "by blast",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1088, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1094_Collect_case_prodD",
 goal = ``v_x0 ∈ UNCURRY v_A0 ⇒ v_A0 (FST v_x0) (SND v_x0)``,
 source_method = "by auto",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1094, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1097_Collect_case_prod_mono",
 goal = ``(∀b_order0. v_A0 b_order0 ⊆ v_B0 b_order0) ⇒ UNCURRY v_A0 ⊆ UNCURRY v_B0``,
 source_method = "by auto (auto elim!: le_funE)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1097, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1100_Collect_split_mono_strong",
 goal = ``v_X0 = IMAGE FST v_A0 ⇒
v_Y0 = IMAGE SND v_A0 ⇒
(∀b_a. b_a ∈ v_X0 ⇒ ∀b_b. b_b ∈ v_Y0 ⇒ v_P0 b_a b_b ⇒ v_Q0 b_a b_b) ⇒
v_A0 ⊆ UNCURRY v_P0 ⇒
v_A0 ⊆ UNCURRY v_Q0``,
 source_method = "by fastforce",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1100, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1109_split_paired_Ball_Sigma",
 goal = ``(∀b_z.
   b_z ∈
   (source_Sigma v_A0 v_B0) ⇒
   v_P0 b_z) ⇔ ∀b_x. b_x ∈ v_A0 ⇒ ∀b_y. b_y ∈ v_B0 b_x ⇒ v_P0 (b_x,b_y)``,
 source_method = "by blast",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1109, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1112_split_paired_Bex_Sigma",
 goal = ``(∃b_z.
   b_z ∈
   (source_Sigma v_A0 v_B0) ∧
   v_P0 b_z) ⇔ ∃b_x. b_x ∈ v_A0 ∧ ∃b_y. b_y ∈ v_B0 b_x ∧ v_P0 (b_x,b_y)``,
 source_method = "by blast",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1112, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1115_Sigma_Un_distrib1",
 goal = ``(source_Sigma (v_I0 ∪ v_J0) v_C0) =
(source_Sigma v_I0 v_C0) ∪
(source_Sigma v_J0 v_C0)``,
 source_method = "by blast",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1115, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1118_Sigma_Un_distrib2",
 goal = ``(source_Sigma v_I0 (λb_i. v_A0 b_i ∪ v_B0 b_i)) =
(source_Sigma v_I0 v_A0) ∪
(source_Sigma v_I0 v_B0)``,
 source_method = "by blast",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1118, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1121_Sigma_Int_distrib1",
 goal = ``(source_Sigma (v_I0 ∩ v_J0) v_C0) =
(source_Sigma v_I0 v_C0) ∩
(source_Sigma v_J0 v_C0)``,
 source_method = "by blast",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1121, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1124_Sigma_Int_distrib2",
 goal = ``(source_Sigma v_I0 (λb_i. v_A0 b_i ∩ v_B0 b_i)) =
(source_Sigma v_I0 v_A0) ∩
(source_Sigma v_I0 v_B0)``,
 source_method = "by blast",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1124, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1127_Sigma_Diff_distrib1",
 goal = ``(source_Sigma (v_I0 DIFF v_J0) v_C0) =
(source_Sigma v_I0 v_C0) DIFF
(source_Sigma v_J0 v_C0)``,
 source_method = "by blast",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1127, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1130_Sigma_Diff_distrib2",
 goal = ``(source_Sigma v_I0 (λb_i. v_A0 b_i DIFF v_B0 b_i)) =
(source_Sigma v_I0 v_A0) DIFF
(source_Sigma v_I0 v_B0)``,
 source_method = "by blast",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1130, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1133_Sigma_Union",
 goal = ``(source_Sigma (BIGUNION v_X0) v_B0) =
BIGUNION
  (IMAGE
     (λb_A. source_Sigma b_A v_B0)
     v_X0)``,
 source_method = "by blast",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1133, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1136_Pair_vimage_Sigma",
 goal = ``PREIMAGE ((λb_pair_left b_pair_right. (b_pair_left,b_pair_right)) v_x0)
  (source_Sigma v_A0 v_f0) =
if v_x0 ∈ v_A0 then v_f0 v_x0 else ∅``,
 source_method = "by auto",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1136, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1153_Times_empty",
 goal = ``(source_Sigma v_A0 (λb_uu_. v_B0)) = ∅ ⇔
v_A0 = ∅ ∨ v_B0 = ∅``,
 source_method = "by auto",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1153, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1156_times_subset_iff",
 goal = ``(source_Sigma v_A0 (λb_uu_. v_C0)) ⊆
(source_Sigma v_B0 (λb_uu_. v_D0)) ⇔
v_A0 = ∅ ∨ v_C0 = ∅ ∨ v_A0 ⊆ v_B0 ∧ v_C0 ⊆ v_D0``,
 source_method = "by blast",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1156, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1159_times_eq_iff",
 goal = ``(source_Sigma v_A0 (λb_uu_. v_B0)) =
(source_Sigma v_C0 (λb_uu_. v_D0)) ⇔
v_A0 = v_C0 ∧ v_B0 = v_D0 ∨ (v_A0 = ∅ ∨ v_B0 = ∅) ∧ (v_C0 = ∅ ∨ v_D0 = ∅)``,
 source_method = "by auto",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1159, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1162_fst_image_times",
 goal = ``IMAGE FST
  (source_Sigma v_A0 (λb_uu_. v_B0)) =
if v_B0 = ∅ then ∅ else v_A0``,
 source_method = "by force",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1162, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1165_snd_image_times",
 goal = ``IMAGE SND
  (source_Sigma v_A0 (λb_uu_. v_B0)) =
if v_A0 = ∅ then ∅ else v_B0``,
 source_method = "by force",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1165, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1168_fst_image_Sigma",
 goal = ``IMAGE FST
  (source_Sigma v_A0 v_B0) =
(λb_x. b_x ∈ v_A0 ∧ v_B0 b_x ≠ ∅)``,
 source_method = "by force",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1168, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1171_snd_image_Sigma",
 goal = ``IMAGE SND
  (source_Sigma v_A0 v_B0) =
BIGUNION (IMAGE (λb_x. v_B0 b_x) v_A0)``,
 source_method = "by force",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1171, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1174_vimage_fst",
 goal = ``PREIMAGE FST v_A0 =
(source_Sigma v_A0 (λb_uu_. 𝕌(:β)))``,
 source_method = "by auto",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1174, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1177_vimage_snd",
 goal = ``PREIMAGE SND v_A0 =
(source_Sigma 𝕌(:α) (λb_uu_. v_A0))``,
 source_method = "by auto",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1177, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1180_insert_Times_insert",
 goal = ``(source_Sigma (v_a0 INSERT v_A0) (λb_uu_. v_b0 INSERT v_B0)) =
(v_a0,v_b0) INSERT
(source_Sigma v_A0 (λb_uu_. v_b0 INSERT v_B0)) ∪
(source_Sigma {v_a0} (λb_uu_. v_B0))``,
 source_method = "by blast",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1180, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1184_sing_Times_sing",
 goal = ``(source_Sigma {v_x0} (λb_uu_. {v_y0})) = {(v_x0,v_y0)}``,
 source_method = "by simp",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1184, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1193_Times_Int_Times",
 goal = ``(source_Sigma v_A0 (λb_uu_. v_B0)) ∩
(source_Sigma v_C0 (λb_uu_. v_D0)) =
(source_Sigma (v_A0 ∩ v_C0) (λb_uu_. v_B0 ∩ v_D0))``,
 source_method = "by auto",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1193, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1196_image_paired_Times",
 goal = ``IMAGE (λ(b_x,b_y). (v_f0 b_x,v_g0 b_y))
  (source_Sigma v_A0 (λb_uu_. v_B0)) =
(source_Sigma (IMAGE v_f0 v_A0) (λb_uu_. IMAGE v_g0 v_B0))``,
 source_method = "by auto",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1196, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1200_Times_insert_right",
 goal = ``(source_Sigma v_A0 (λb_uu_. v_y0 INSERT v_B0)) =
IMAGE (λb_x. (b_x,v_y0)) v_A0 ∪
(source_Sigma v_A0 (λb_uu_. v_B0))``,
 source_method = "by auto",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1200, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1203_Times_insert_left",
 goal = ``(source_Sigma (v_x0 INSERT v_A0) (λb_uu_. v_B0)) =
IMAGE (λb_y. (v_x0,b_y)) v_B0 ∪
(source_Sigma v_A0 (λb_uu_. v_B0))``,
 source_method = "by auto",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1203, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1206_product_swap",
 goal = ``IMAGE (λb_swap_pair. (SND b_swap_pair,FST b_swap_pair))
  (source_Sigma v_A0 (λb_uu_. v_B0)) =
(source_Sigma v_B0 (λb_uu_. v_A0))``,
 source_method = "by (auto simp add: set_eq_iff)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1206, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1209_swap_product",
 goal = ``IMAGE (λ(b_i,b_j). (b_j,b_i))
  (source_Sigma v_A0 (λb_uu_. v_B0)) =
(source_Sigma v_B0 (λb_uu_. v_A0))``,
 source_method = "by (auto simp add: set_eq_iff)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1209, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1220_subset_fst_snd",
 goal = ``v_A0 ⊆
(source_Sigma (IMAGE FST v_A0) (λb_uu_. IMAGE SND v_A0))``,
 source_method = "by force",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1220, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1223_inj_on_apfst",
 goal = ``(λb_inj_func b_inj_set. INJ b_inj_func b_inj_set 𝕌(:γ # β))
  ((λb_apfst_func b_apfst_pair.
        (b_apfst_func (FST b_apfst_pair),SND b_apfst_pair)) v_f0)
  (source_Sigma v_A0 (λb_uu_. 𝕌(:β))) ⇔
(λb_inj_func b_inj_set. INJ b_inj_func b_inj_set 𝕌(:γ)) v_f0 v_A0``,
 source_method = "by (auto simp add: inj_on_def)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1223, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1226_inj_apfst",
 goal = ``(λb_inj_func b_inj_set. INJ b_inj_func b_inj_set 𝕌(:γ # β))
  ((λb_apfst_func b_apfst_pair.
        (b_apfst_func (FST b_apfst_pair),SND b_apfst_pair)) v_f0) 𝕌(:α # β) ⇔
(λb_inj_func b_inj_set. INJ b_inj_func b_inj_set 𝕌(:γ)) v_f0 𝕌(:α)``,
 source_method = "using inj_on_apfst[of f UNIV] by simp",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1226, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1229_inj_on_apsnd",
 goal = ``(λb_inj_func b_inj_set. INJ b_inj_func b_inj_set 𝕌(:α # γ))
  ((λb_apsnd_func b_apsnd_pair.
        (FST b_apsnd_pair,b_apsnd_func (SND b_apsnd_pair))) v_f0)
  (source_Sigma 𝕌(:α) (λb_uu_. v_A0)) ⇔
(λb_inj_func b_inj_set. INJ b_inj_func b_inj_set 𝕌(:γ)) v_f0 v_A0``,
 source_method = "by (auto simp add: inj_on_def)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1229, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1232_inj_apsnd",
 goal = ``(λb_inj_func b_inj_set. INJ b_inj_func b_inj_set 𝕌(:α # γ))
  ((λb_apsnd_func b_apsnd_pair.
        (FST b_apsnd_pair,b_apsnd_func (SND b_apsnd_pair))) v_f0) 𝕌(:α # β) ⇔
(λb_inj_func b_inj_set. INJ b_inj_func b_inj_set 𝕌(:γ)) v_f0 𝕌(:β)``,
 source_method = "using inj_on_apsnd[of f UNIV] by simp",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1232, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1241_member_product",
 goal = ``v_x0 ∈ (source_product v_A0 v_B0) ⇔
v_x0 ∈
(source_Sigma v_A0 (λb_uu_. v_B0))``,
 source_method = "by (simp add: product_def)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1241, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1329_bij_betw_map_prod",
 goal = ``BIJ v_f0 v_A0 v_C0 ⇒
BIJ v_g0 v_B0 v_D0 ⇒
BIJ
  ((λb_map_left b_map_right b_map_pair.
        (b_map_left (FST b_map_pair),b_map_right (SND b_map_pair))) v_f0 v_g0)
  (source_Sigma v_A0 (λb_uu_. v_B0))
  (source_Sigma v_C0 (λb_uu_. v_D0))``,
 source_method = "using assms unfolding bij_betw_def inj_on_def by auto",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1329, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1364_disjnt_Times1_iff",
 goal = ``DISJOINT
  (source_Sigma v_C0 (λb_uu_. v_A0))
  (source_Sigma v_C0 (λb_uu_. v_B0)) ⇔
v_C0 = ∅ ∨ DISJOINT v_A0 v_B0``,
 source_method = "by (auto simp: disjnt_def)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1364, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1367_disjnt_Times2_iff",
 goal = ``DISJOINT
  (source_Sigma v_A0 (λb_uu_. v_C0))
  (source_Sigma v_B0 (λb_uu_. v_C0)) ⇔
v_C0 = ∅ ∨ DISJOINT v_A0 v_B0``,
 source_method = "by (auto simp: disjnt_def)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1367, commit = "f7e02b7e"},
 representative = false},
{id = "product_type_L1370_disjnt_Sigma_iff",
 goal = ``DISJOINT
  (source_Sigma v_A0 v_C0)
  (source_Sigma v_B0 v_C0) ⇔
(∀b_i. b_i ∈ v_A0 ∩ v_B0 ⇒ v_C0 b_i = ∅) ∨ DISJOINT v_A0 v_B0``,
 source_method = "by (auto simp: disjnt_def)",
 provenance = {file = "src/HOL/Product_Type.thy", line = 1370, commit = "f7e02b7e"},
 representative = false}]

end
