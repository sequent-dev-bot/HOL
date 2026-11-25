structure benchListCorpus =
struct

open HolKernel autoSeedTheory

val goals : benchLib.source_goal list =
[{id = "list_L849_inj_split_Cons",
 goal = ``(λb_inj_func b_inj_set. INJ b_inj_func b_inj_set 𝕌(:α list))
  (λ(b_xs,b_n). b_n::b_xs) v_X0``,
 source_method = "by (auto intro!: inj_onI)",
 provenance = {file = "src/HOL/List.thy", line = 849, commit = "f7e02b7e"},
 representative = false},
{id = "list_L852_inj_on_Cons1",
 goal = ``(λb_inj_func b_inj_set. INJ b_inj_func b_inj_set 𝕌(:α list)) (CONS v_x0) v_A0``,
 source_method = "by(simp add: inj_on_def)",
 provenance = {file = "src/HOL/List.thy", line = 852, commit = "f7e02b7e"},
 representative = false},
{id = "list_L880_length_pos_if_in_set",
 goal = ``MEM v_x0 v_xs0 ⇒ 0 < LENGTH v_xs0``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 880, commit = "f7e02b7e"},
 representative = false},
{id = "list_L981_same_append_eq",
 goal = ``v_xs0 ++ v_ys0 = v_xs0 ++ v_zs0 ⇔ v_ys0 = v_zs0``,
 source_method = "by simp",
 provenance = {file = "src/HOL/List.thy", line = 981, commit = "f7e02b7e"},
 representative = false},
{id = "list_L984_append1_eq_conv",
 goal = ``v_xs0 ++ [v_x0] = v_ys0 ++ [v_y0] ⇔ v_xs0 = v_ys0 ∧ v_x0 = v_y0``,
 source_method = "by simp",
 provenance = {file = "src/HOL/List.thy", line = 984, commit = "f7e02b7e"},
 representative = false},
{id = "list_L987_append_same_eq",
 goal = ``v_ys0 ++ v_xs0 = v_zs0 ++ v_xs0 ⇔ v_ys0 = v_zs0``,
 source_method = "by simp",
 provenance = {file = "src/HOL/List.thy", line = 987, commit = "f7e02b7e"},
 representative = false},
{id = "list_L990_append_self_conv2",
 goal = ``v_xs0 ++ v_ys0 = v_ys0 ⇔ v_xs0 = []``,
 source_method = "using append_same_eq [of _ _ \"[]\"] by auto",
 provenance = {file = "src/HOL/List.thy", line = 990, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1001_hd_append2",
 goal = ``v_xs0 ≠ [] ⇒ HD (v_xs0 ++ v_ys0) = HD v_xs0``,
 source_method = "by (simp add: hd_append split: list.split)",
 provenance = {file = "src/HOL/List.thy", line = 1001, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1004_tl_append",
 goal = ``TL (v_xs0 ++ v_ys0) =
(λb_list_nil b_list_cons b_list_value.
     list_CASE b_list_value b_list_nil b_list_cons) (TL v_ys0)
  (λb_z b_zs. b_zs ++ v_ys0) v_xs0``,
 source_method = "by (simp split: list.split)",
 provenance = {file = "src/HOL/List.thy", line = 1004, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1007_tl_append2",
 goal = ``v_xs0 ≠ [] ⇒ TL (v_xs0 ++ v_ys0) = TL v_xs0 ++ v_ys0``,
 source_method = "by (simp add: tl_append split: list.split)",
 provenance = {file = "src/HOL/List.thy", line = 1007, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1010_tl_append_if",
 goal = ``TL (v_xs0 ++ v_ys0) = if v_xs0 = [] then TL v_ys0 else TL v_xs0 ++ v_ys0``,
 source_method = "by (simp)",
 provenance = {file = "src/HOL/List.thy", line = 1010, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1030_eq_Nil_appendI",
 goal = ``v_xs0 = v_ys0 ⇒ v_xs0 = [] ++ v_ys0``,
 source_method = "by simp",
 provenance = {file = "src/HOL/List.thy", line = 1030, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1033_Cons_eq_appendI",
 goal = ``v_x0::v_xs10 = v_ys0 ⇒ v_xs0 = v_xs10 ++ v_zs0 ⇒ v_x0::v_xs0 = v_ys0 ++ v_zs0``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 1033, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1036_append_eq_appendI",
 goal = ``v_xs0 ++ v_xs10 = v_zs0 ⇒
v_ys0 = v_xs10 ++ v_us0 ⇒
v_xs0 ++ v_ys0 = v_zs0 ++ v_us0``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 1036, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1119_map_cong",
 goal = ``v_xs0 = v_ys0 ⇒
(∀b_x. MEM b_x v_ys0 ⇒ v_f0 b_x = v_g0 b_x) ⇒
MAP v_f0 v_xs0 = MAP v_g0 v_ys0``,
 source_method = "by simp",
 provenance = {file = "src/HOL/List.thy", line = 1119, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1193_inj_on_map_eq_map",
 goal = ``(λb_inj_func b_inj_set. INJ b_inj_func b_inj_set 𝕌(:β)) v_f0
  (set v_xs0 ∪ set v_ys0) ⇒
(MAP v_f0 v_xs0 = MAP v_f0 v_ys0 ⇔ v_xs0 = v_ys0)``,
 source_method = "by(blast dest:map_inj_on)",
 provenance = {file = "src/HOL/List.thy", line = 1193, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1201_inj_map_eq_map",
 goal = ``(λb_inj_func b_inj_set. INJ b_inj_func b_inj_set 𝕌(:β)) v_f0 𝕌(:α) ⇒
(MAP v_f0 v_xs0 = MAP v_f0 v_ys0 ⇔ v_xs0 = v_ys0)``,
 source_method = "by(blast dest:map_injective)",
 provenance = {file = "src/HOL/List.thy", line = 1201, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1210_inj_map",
 goal = ``(λb_inj_func b_inj_set. INJ b_inj_func b_inj_set 𝕌(:β list)) (MAP v_f0)
  𝕌(:α list) ⇔
(λb_inj_func b_inj_set. INJ b_inj_func b_inj_set 𝕌(:β)) v_f0 𝕌(:α)``,
 source_method = "by (blast dest: inj_mapD intro: inj_mapI)",
 provenance = {file = "src/HOL/List.thy", line = 1210, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1213_inj_on_mapI",
 goal = ``(λb_inj_func b_inj_set. INJ b_inj_func b_inj_set 𝕌(:β)) v_f0
  (BIGUNION (IMAGE set v_A0)) ⇒
(λb_inj_func b_inj_set. INJ b_inj_func b_inj_set 𝕌(:β list)) (MAP v_f0) v_A0``,
 source_method = "by (blast intro:inj_onI dest:inj_onD map_inj_on)",
 provenance = {file = "src/HOL/List.thy", line = 1213, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1255_rev_involution",
 goal = ``REVERSE ∘ REVERSE = I``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 1255, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1258_rev_swap",
 goal = ``REVERSE v_xs0 = v_ys0 ⇔ v_xs0 = REVERSE v_ys0``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 1258, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1287_rev_eq_Cons_iff",
 goal = ``REVERSE v_xs0 = v_y0::v_ys0 ⇔ v_xs0 = REVERSE v_ys0 ++ [v_y0]``,
 source_method = "by (simp add: rev_swap)",
 provenance = {file = "src/HOL/List.thy", line = 1287, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1292_inj_on_rev",
 goal = ``(λb_inj_func b_inj_set. INJ b_inj_func b_inj_set 𝕌(:α list)) REVERSE v_A0``,
 source_method = "by(simp add:inj_on_def)",
 provenance = {file = "src/HOL/List.thy", line = 1292, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1356_set_subset_Cons",
 goal = ``set v_xs0 ⊆ set (v_x0::v_xs0)``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 1356, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1359_set_ConsD",
 goal = ``MEM v_y0 (v_x0::v_xs0) ⇒ v_y0 = v_x0 ∨ MEM v_y0 v_xs0``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 1359, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1367_append_eq_append_conv_if_disj",
 goal = ``(set v_xs0 ∪ set v_xs_0) ∩ (set v_ys0 ∪ set v_ys_0) = ∅ ⇒
(v_xs0 ++ v_ys0 = v_xs_0 ++ v_ys_0 ⇔ v_xs0 = v_xs_0 ∧ v_ys0 = v_ys_0)``,
 source_method = "by (auto simp: all_conj_distrib disjoint_iff append_eq_append_conv2)",
 provenance = {file = "src/HOL/List.thy", line = 1367, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1384_atMost_upto",
 goal = ``(λb_at_most b_at_most_item. b_at_most_item ≤ b_at_most) v_n0 =
set
  ((λb_upt_start b_upt_end.
        GENLIST (λb_upt_offset. b_upt_start + b_upt_offset)
          (b_upt_end − b_upt_start)) 0 (SUC v_n0))``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 1384, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1388_atLeast_upt",
 goal = ``(λb_less_than b_less_item. b_less_item < b_less_than) v_n0 =
set
  ((λb_upt_start b_upt_end.
        GENLIST (λb_upt_offset. b_upt_start + b_upt_offset)
          (b_upt_end − b_upt_start)) 0 v_n0)``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 1388, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1392_greaterThanLessThan_upt",
 goal = ``(λb_open_left b_open_right b_open_item.
     b_open_left < b_open_item ∧ b_open_item < b_open_right) v_n0 v_m0 =
set
  ((λb_upt_start b_upt_end.
        GENLIST (λb_upt_offset. b_upt_start + b_upt_offset)
          (b_upt_end − b_upt_start)) (SUC v_n0) v_m0)``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 1392, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1396_atLeastLessThan_upt",
 goal = ``(λb_interval_left b_interval_right b_interval_item.
     b_interval_left ≤ b_interval_item ∧ b_interval_item < b_interval_right)
  v_i0 v_j0 =
set
  ((λb_upt_start b_upt_end.
        GENLIST (λb_upt_offset. b_upt_start + b_upt_offset)
          (b_upt_end − b_upt_start)) v_i0 v_j0)``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 1396, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1400_greaterThanAtMost_upt",
 goal = ``(λb_interval_left b_interval_right b_interval_item.
     b_interval_left < b_interval_item ∧ b_interval_item ≤ b_interval_right)
  v_n0 v_m0 =
set
  ((λb_upt_start b_upt_end.
        GENLIST (λb_upt_offset. b_upt_start + b_upt_offset)
          (b_upt_end − b_upt_start)) (SUC v_n0) (SUC v_m0))``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 1400, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1404_atLeastAtMost_upt",
 goal = ``(λb_closed_left b_closed_right b_closed_item.
     b_closed_left ≤ b_closed_item ∧ b_closed_item ≤ b_closed_right) v_n0
  v_m0 =
set
  ((λb_upt_start b_upt_end.
        GENLIST (λb_upt_offset. b_upt_start + b_upt_offset)
          (b_upt_end − b_upt_start)) v_n0 (SUC v_m0))``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 1404, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1415_in_set_conv_decomp",
 goal = ``MEM v_x0 v_xs0 ⇔ ∃b_ys b_zs. v_xs0 = b_ys ++ v_x0::b_zs``,
 source_method = "by (auto elim: split_list)",
 provenance = {file = "src/HOL/List.thy", line = 1415, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1431_in_set_conv_decomp_first",
 goal = ``MEM v_x0 v_xs0 ⇔ ∃b_ys b_zs. v_xs0 = b_ys ++ v_x0::b_zs ∧ ¬MEM v_x0 b_ys``,
 source_method = "by (auto dest!: split_list_first)",
 provenance = {file = "src/HOL/List.thy", line = 1431, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1448_in_set_conv_decomp_last",
 goal = ``MEM v_x0 v_xs0 ⇔ ∃b_ys b_zs. v_xs0 = b_ys ++ v_x0::b_zs ∧ ¬MEM v_x0 b_zs``,
 source_method = "by (auto dest!: split_list_last)",
 provenance = {file = "src/HOL/List.thy", line = 1448, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1460_split_list_propE",
 goal = ``(∃b_x. MEM b_x v_xs0 ∧ v_P0 b_x) ⇒
(∀b_ys b_x b_zs. v_xs0 = b_ys ++ b_x::b_zs ⇒ v_P0 b_x ⇒ v_thesis0) ⇒
v_thesis0``,
 source_method = "using split_list_prop [OF assms] by blast",
 provenance = {file = "src/HOL/List.thy", line = 1460, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1484_split_list_first_propE",
 goal = ``(∃b_x. MEM b_x v_xs0 ∧ v_P0 b_x) ⇒
(∀b_ys b_x b_zs.
   v_xs0 = b_ys ++ b_x::b_zs ⇒
   v_P0 b_x ⇒
   (∀b_y. MEM b_y b_ys ⇒ ¬v_P0 b_y) ⇒
   v_thesis0) ⇒
v_thesis0``,
 source_method = "using split_list_first_prop [OF assms] by blast",
 provenance = {file = "src/HOL/List.thy", line = 1484, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1511_split_list_last_propE",
 goal = ``(∃b_x. MEM b_x v_xs0 ∧ v_P0 b_x) ⇒
(∀b_ys b_x b_zs.
   v_xs0 = b_ys ++ b_x::b_zs ⇒
   v_P0 b_x ⇒
   (∀b_z. MEM b_z b_zs ⇒ ¬v_P0 b_z) ⇒
   v_thesis0) ⇒
v_thesis0``,
 source_method = "using split_list_last_prop [OF assms] by blast",
 provenance = {file = "src/HOL/List.thy", line = 1511, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1532_append_Cons_eq_iff",
 goal = ``¬MEM v_x0 v_xs0 ⇒
¬MEM v_x0 v_ys0 ⇒
(v_xs0 ++ v_x0::v_ys0 = v_xs_0 ++ v_x0::v_ys_0 ⇔
 v_xs0 = v_xs_0 ∧ v_ys0 = v_ys_0)``,
 source_method = "by(auto simp: append_eq_Cons_conv Cons_eq_append_conv append_eq_append_conv2)",
 provenance = {file = "src/HOL/List.thy", line = 1532, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1569_concat_injective",
 goal = ``FLAT v_xs0 = FLAT v_ys0 ⇒
LENGTH v_xs0 = LENGTH v_ys0 ⇒
(∀b_set.
   MEM b_set (ZIP (v_xs0,v_ys0)) ⇒
   (λ(b_x,b_y). LENGTH b_x = LENGTH b_y) b_set) ⇒
v_xs0 = v_ys0``,
 source_method = "by (simp add: concat_eq_concat_iff)",
 provenance = {file = "src/HOL/List.thy", line = 1569, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1590_concat_eq_append_conv",
 goal = ``FLAT v_xss0 = v_ys0 ++ v_zs0 ⇔
if v_xss0 = [] then v_ys0 = [] ∧ v_zs0 = []
else
  ∃b_xss1 b_xs b_xs_ b_xss2.
    v_xss0 = b_xss1 ++ (b_xs ++ b_xs_)::b_xss2 ∧
    v_ys0 = FLAT b_xss1 ++ b_xs ∧ v_zs0 = b_xs_ ++ FLAT b_xss2``,
 source_method = "by(auto dest: concat_eq_appendD)",
 provenance = {file = "src/HOL/List.thy", line = 1590, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1706_length_filter_map",
 goal = ``LENGTH (FILTER v_P0 (MAP v_f0 v_xs0)) = LENGTH (FILTER (v_P0 ∘ v_f0) v_xs0)``,
 source_method = "by (simp add:filter_map)",
 provenance = {file = "src/HOL/List.thy", line = 1706, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1710_filter_is_subset",
 goal = ``set (FILTER v_P0 v_xs0) ⊆ set v_xs0``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 1710, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1789_filter_eq_Cons_iff",
 goal = ``FILTER v_P0 v_ys0 = v_x0::v_xs0 ⇔
∃b_us b_vs.
  v_ys0 = b_us ++ v_x0::b_vs ∧ (∀b_u. MEM b_u b_us ⇒ ¬v_P0 b_u) ∧ v_P0 v_x0 ∧
  v_xs0 = FILTER v_P0 b_vs``,
 source_method = "by(auto dest:filter_eq_ConsD)",
 provenance = {file = "src/HOL/List.thy", line = 1789, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1838_partition_filter_conv",
 goal = ``(λb_partition_predicate b_partition_list.
     (FILTER b_partition_predicate b_partition_list,
      FILTER (λb_partition_item. ¬b_partition_predicate b_partition_item)
        b_partition_list)) v_f0 v_xs0 =
(FILTER v_f0 v_xs0,FILTER ((λb_not. ¬b_not) ∘ v_f0) v_xs0)``,
 source_method = "unfolding partition_filter2[symmetric] unfolding partition_filter1[symmetric] by simp",
 provenance = {file = "src/HOL/List.thy", line = 1838, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1848_nth_Cons_0",
 goal = ``(λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) (v_x0::v_xs0) 0 = v_x0``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 1848, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1851_nth_Cons_Suc",
 goal = ``(λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) (v_x0::v_xs0) (SUC v_n0) =
(λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_xs0 v_n0``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 1851, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1856_nth_Cons_pos",
 goal = ``0 < v_n0 ⇒
(λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) (v_x0::v_xs0) v_n0 =
(λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_xs0 (v_n0 − 1)``,
 source_method = "by(auto simp: Nat.gr0_conv_Suc)",
 provenance = {file = "src/HOL/List.thy", line = 1856, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1867_nth_append_left",
 goal = ``v_i0 < LENGTH v_xs0 ⇒
(λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) (v_xs0 ++ v_ys0) v_i0 =
(λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_xs0 v_i0``,
 source_method = "by (auto simp: nth_append)",
 provenance = {file = "src/HOL/List.thy", line = 1867, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1870_nth_append_right",
 goal = ``LENGTH v_xs0 ≤ v_i0 ⇒
(λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) (v_xs0 ++ v_ys0) v_i0 =
(λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_ys0
  (v_i0 − LENGTH v_xs0)``,
 source_method = "by (auto simp: nth_append)",
 provenance = {file = "src/HOL/List.thy", line = 1870, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1903_map_equality_iff",
 goal = ``MAP v_f0 v_xs0 = MAP v_g0 v_ys0 ⇔
LENGTH v_xs0 = LENGTH v_ys0 ∧
∀b_i.
  b_i < LENGTH v_ys0 ⇒
  v_f0 ((λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_xs0 b_i) =
  v_g0 ((λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_ys0 b_i)``,
 source_method = "by (fastforce simp: list_eq_iff_nth_eq)",
 provenance = {file = "src/HOL/List.thy", line = 1903, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1921_in_set_conv_nth",
 goal = ``MEM v_x0 v_xs0 ⇔
∃b_i.
  b_i < LENGTH v_xs0 ∧
  (λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_xs0 b_i = v_x0``,
 source_method = "by(auto simp:set_conv_nth)",
 provenance = {file = "src/HOL/List.thy", line = 1921, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1953_list_ball_nth",
 goal = ``v_n0 < LENGTH v_xs0 ⇒
(∀b_x. MEM b_x v_xs0 ⇒ v_P0 b_x) ⇒
v_P0 ((λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_xs0 v_n0)``,
 source_method = "by (auto simp add: set_conv_nth)",
 provenance = {file = "src/HOL/List.thy", line = 1953, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1956_nth_mem",
 goal = ``v_n0 < LENGTH v_xs0 ⇒
MEM ((λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_xs0 v_n0) v_xs0``,
 source_method = "by (auto simp add: set_conv_nth)",
 provenance = {file = "src/HOL/List.thy", line = 1956, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1959_all_nth_imp_all_set",
 goal = ``(∀b_i.
   b_i < LENGTH v_xs0 ⇒
   v_P0 ((λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_xs0 b_i)) ⇒
MEM v_x0 v_xs0 ⇒
v_P0 v_x0``,
 source_method = "by (auto simp add: set_conv_nth)",
 provenance = {file = "src/HOL/List.thy", line = 1959, commit = "f7e02b7e"},
 representative = false},
{id = "list_L1963_all_set_conv_all_nth",
 goal = ``(∀b_x. MEM b_x v_xs0 ⇒ v_P0 b_x) ⇔
∀b_i.
  b_i < LENGTH v_xs0 ⇒
  v_P0 ((λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_xs0 b_i)``,
 source_method = "by (auto simp add: set_conv_nth)",
 provenance = {file = "src/HOL/List.thy", line = 1963, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2015_nth_list_update_eq",
 goal = ``v_i0 < LENGTH v_xs0 ⇒
(λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳)
  ((λb_update_list b_update_index b_update_item.
        b_update_list❲b_update_index ↦ b_update_item❳) v_xs0 v_i0 v_x0) v_i0 =
v_x0``,
 source_method = "by (simp add: nth_list_update)",
 provenance = {file = "src/HOL/List.thy", line = 2015, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2065_set_update_subsetI",
 goal = ``set v_xs0 ⊆ v_A0 ⇒
v_x0 ∈ v_A0 ⇒
set
  ((λb_update_list b_update_index b_update_item.
        b_update_list❲b_update_index ↦ b_update_item❳) v_xs0 v_i0 v_x0) ⊆
v_A0``,
 source_method = "by (blast dest!: set_update_subset_insert [THEN subsetD])",
 provenance = {file = "src/HOL/List.thy", line = 2065, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2088_hd_Nil_eq_last",
 goal = ``source_hd [] = source_last []``,
 source_method = "unfolding hd_def last_def by simp",
 provenance = {file = "src/HOL/List.thy", line = 2088, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2097_last_ConsL",
 goal = ``v_xs0 = [] ⇒ LAST (v_x0::v_xs0) = v_x0``,
 source_method = "by simp",
 provenance = {file = "src/HOL/List.thy", line = 2097, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2100_last_ConsR",
 goal = ``v_xs0 ≠ [] ⇒ LAST (v_x0::v_xs0) = LAST v_xs0``,
 source_method = "by simp",
 provenance = {file = "src/HOL/List.thy", line = 2100, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2106_last_appendL",
 goal = ``v_ys0 = [] ⇒ LAST (v_xs0 ++ v_ys0) = LAST v_xs0``,
 source_method = "by(simp add:last_append)",
 provenance = {file = "src/HOL/List.thy", line = 2106, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2109_last_appendR",
 goal = ``v_ys0 ≠ [] ⇒ LAST (v_xs0 ++ v_ys0) = LAST v_ys0``,
 source_method = "by(simp add:last_append)",
 provenance = {file = "src/HOL/List.thy", line = 2109, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2141_in_set_butlast_appendI",
 goal = ``MEM v_x0 (FRONT v_xs0) ∨ MEM v_x0 (FRONT v_ys0) ⇒
MEM v_x0 (FRONT (v_xs0 ++ v_ys0))``,
 source_method = "by (auto dest: in_set_butlastD simp add: butlast_append)",
 provenance = {file = "src/HOL/List.thy", line = 2141, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2163_last_list_update",
 goal = ``v_xs0 ≠ [] ⇒
LAST
  ((λb_update_list b_update_index b_update_item.
        b_update_list❲b_update_index ↦ b_update_item❳) v_xs0 v_k0 v_x0) =
if v_k0 = LENGTH v_xs0 − 1 then v_x0 else LAST v_xs0``,
 source_method = "by (auto simp: last_conv_nth)",
 provenance = {file = "src/HOL/List.thy", line = 2163, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2178_snoc_eq_iff_butlast",
 goal = ``v_xs0 ++ [v_x0] = v_ys0 ⇔
v_ys0 ≠ [] ∧ FRONT v_ys0 = v_xs0 ∧ LAST v_ys0 = v_x0``,
 source_method = "by fastforce",
 provenance = {file = "src/HOL/List.thy", line = 2178, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2206_take_Suc_Cons",
 goal = ``TAKE (SUC v_n0) (v_x0::v_xs0) = v_x0::TAKE v_n0 v_xs0``,
 source_method = "by simp",
 provenance = {file = "src/HOL/List.thy", line = 2206, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2209_drop_Suc_Cons",
 goal = ``DROP (SUC v_n0) (v_x0::v_xs0) = DROP v_n0 v_xs0``,
 source_method = "by simp",
 provenance = {file = "src/HOL/List.thy", line = 2209, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2214_take_Suc",
 goal = ``v_xs0 ≠ [] ⇒ TAKE (SUC v_n0) v_xs0 = HD v_xs0::TAKE v_n0 (TL v_xs0)``,
 source_method = "by(clarsimp simp add:neq_Nil_conv)",
 provenance = {file = "src/HOL/List.thy", line = 2214, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2396_butlast_take",
 goal = ``v_n0 ≤ LENGTH v_xs0 ⇒ FRONT (TAKE v_n0 v_xs0) = TAKE (v_n0 − 1) v_xs0``,
 source_method = "by (simp add: butlast_conv_take)",
 provenance = {file = "src/HOL/List.thy", line = 2396, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2400_butlast_drop",
 goal = ``FRONT (DROP v_n0 v_xs0) = DROP v_n0 (FRONT v_xs0)``,
 source_method = "by (simp add: butlast_conv_take drop_take ac_simps)",
 provenance = {file = "src/HOL/List.thy", line = 2400, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2403_take_butlast",
 goal = ``v_n0 < LENGTH v_xs0 ⇒ TAKE v_n0 (FRONT v_xs0) = TAKE v_n0 v_xs0``,
 source_method = "by (simp add: butlast_conv_take)",
 provenance = {file = "src/HOL/List.thy", line = 2403, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2406_drop_butlast",
 goal = ``DROP v_n0 (FRONT v_xs0) = FRONT (DROP v_n0 v_xs0)``,
 source_method = "by (simp add: butlast_conv_take drop_take ac_simps)",
 provenance = {file = "src/HOL/List.thy", line = 2406, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2412_hd_drop_conv_nth",
 goal = ``v_n0 < LENGTH v_xs0 ⇒
HD (DROP v_n0 v_xs0) =
(λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_xs0 v_n0``,
 source_method = "by(simp add: hd_conv_nth)",
 provenance = {file = "src/HOL/List.thy", line = 2412, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2480_take_update_cancel",
 goal = ``v_n0 ≤ v_m0 ⇒
TAKE v_n0
  ((λb_update_list b_update_index b_update_item.
        b_update_list❲b_update_index ↦ b_update_item❳) v_xs0 v_m0 v_y0) =
TAKE v_n0 v_xs0``,
 source_method = "by(simp add: list_eq_iff_nth_eq)",
 provenance = {file = "src/HOL/List.thy", line = 2480, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2483_drop_update_cancel",
 goal = ``v_n0 < v_m0 ⇒
DROP v_m0
  ((λb_update_list b_update_index b_update_item.
        b_update_list❲b_update_index ↦ b_update_item❳) v_xs0 v_n0 v_x0) =
DROP v_m0 v_xs0``,
 source_method = "by(simp add: list_eq_iff_nth_eq)",
 provenance = {file = "src/HOL/List.thy", line = 2483, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2545_takeWhile_append",
 goal = ``source_takeWhile v_P0 (v_xs0 ++ v_ys0) =
if ∀b_x. MEM b_x v_xs0 ⇒ v_P0 b_x then v_xs0 ++ source_takeWhile v_P0 v_ys0
else source_takeWhile v_P0 v_xs0``,
 source_method = "using takeWhile_append1[of _ xs P ys] takeWhile_append2[of xs P ys] by auto",
 provenance = {file = "src/HOL/List.thy", line = 2545, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2576_dropWhile_id",
 goal = ``(∀b_x. MEM b_x v_xs0 ⇒ ¬v_P0 b_x) ⇒ dropWhile v_P0 v_xs0 = v_xs0``,
 source_method = "using takeWhile_dropWhile_id[of P xs] takeWhile_eq_Nil_iff[of P xs] by fastforce",
 provenance = {file = "src/HOL/List.thy", line = 2576, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2585_dropWhile_append",
 goal = ``dropWhile v_P0 (v_xs0 ++ v_ys0) =
if ∀b_x. MEM b_x v_xs0 ⇒ v_P0 b_x then dropWhile v_P0 v_ys0
else dropWhile v_P0 v_xs0 ++ v_ys0``,
 source_method = "using dropWhile_append1[of _ xs P ys] dropWhile_append2[of xs P ys] by auto",
 provenance = {file = "src/HOL/List.thy", line = 2585, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2589_dropWhile_last",
 goal = ``MEM v_x0 v_xs0 ⇒ ¬v_P0 v_x0 ⇒ LAST (dropWhile v_P0 v_xs0) = LAST v_xs0``,
 source_method = "by (auto simp add: dropWhile_append3 in_set_conv_decomp)",
 provenance = {file = "src/HOL/List.thy", line = 2589, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2740_zip_Cons_Cons",
 goal = ``ZIP (v_x0::v_xs0,v_y0::v_ys0) = (v_x0,v_y0)::ZIP (v_xs0,v_ys0)``,
 source_method = "by simp",
 provenance = {file = "src/HOL/List.thy", line = 2740, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2751_zip_Cons1",
 goal = ``ZIP (v_x0::v_xs0,v_ys0) =
(λb_list_nil b_list_cons b_list_value.
     list_CASE b_list_value b_list_nil b_list_cons) []
  (λb_y b_ys. (v_x0,b_y)::ZIP (v_xs0,b_ys)) v_ys0``,
 source_method = "by(auto split:list.split)",
 provenance = {file = "src/HOL/List.thy", line = 2751, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2786_zip_append",
 goal = ``LENGTH v_xs0 = LENGTH v_us0 ⇒
ZIP (v_xs0 ++ v_ys0,v_us0 ++ v_vs0) = ZIP (v_xs0,v_us0) ++ ZIP (v_ys0,v_vs0)``,
 source_method = "by (simp add: zip_append1)",
 provenance = {file = "src/HOL/List.thy", line = 2786, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2806_zip_map1",
 goal = ``ZIP (MAP v_f0 v_xs0,v_ys0) =
MAP (λ(b_x,b_y). (v_f0 b_x,b_y)) (ZIP (v_xs0,v_ys0))``,
 source_method = "using zip_map_map[of f xs \"\\<lambda>x. x\" ys] by simp",
 provenance = {file = "src/HOL/List.thy", line = 2806, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2810_zip_map2",
 goal = ``ZIP (v_xs0,MAP v_f0 v_ys0) =
MAP (λ(b_x,b_y). (b_x,v_f0 b_y)) (ZIP (v_xs0,v_ys0))``,
 source_method = "using zip_map_map[of \"\\<lambda>x. x\" xs f ys] by simp",
 provenance = {file = "src/HOL/List.thy", line = 2810, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2814_map_zip_map",
 goal = ``MAP v_f0 (ZIP (MAP v_g0 v_xs0,v_ys0)) =
MAP (λ(b_x,b_y). v_f0 (v_g0 b_x,b_y)) (ZIP (v_xs0,v_ys0))``,
 source_method = "by (auto simp: zip_map1)",
 provenance = {file = "src/HOL/List.thy", line = 2814, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2818_map_zip_map2",
 goal = ``MAP v_f0 (ZIP (v_xs0,MAP v_g0 v_ys0)) =
MAP (λ(b_x,b_y). v_f0 (b_x,v_g0 b_y)) (ZIP (v_xs0,v_ys0))``,
 source_method = "by (auto simp: zip_map2)",
 provenance = {file = "src/HOL/List.thy", line = 2818, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2834_set_zip",
 goal = ``set (ZIP (v_xs0,v_ys0)) =
(λb_uu_.
     ∃b_i.
       b_uu_ =
       ((λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_xs0 b_i,
        (λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_ys0 b_i) ∧
       b_i < MIN (LENGTH v_xs0) (LENGTH v_ys0))``,
 source_method = "by(simp add: set_conv_nth cong: rev_conj_cong)",
 provenance = {file = "src/HOL/List.thy", line = 2834, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2841_zip_update",
 goal = ``ZIP
  ((λb_update_list b_update_index b_update_item.
        b_update_list❲b_update_index ↦ b_update_item❳) v_xs0 v_i0 v_x0,
   (λb_update_list b_update_index b_update_item.
        b_update_list❲b_update_index ↦ b_update_item❳) v_ys0 v_i0 v_y0) =
(λb_update_list b_update_index b_update_item.
     b_update_list❲b_update_index ↦ b_update_item❳) (ZIP (v_xs0,v_ys0)) v_i0
  (v_x0,v_y0)``,
 source_method = "by (simp add: update_zip)",
 provenance = {file = "src/HOL/List.thy", line = 2841, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2897_in_set_zipE",
 goal = ``MEM (v_x0,v_y0) (ZIP (v_xs0,v_ys0)) ⇒
(MEM v_x0 v_xs0 ⇒ MEM v_y0 v_ys0 ⇒ v_R0) ⇒
v_R0``,
 source_method = "by(blast dest: set_zip_leftD set_zip_rightD)",
 provenance = {file = "src/HOL/List.thy", line = 2897, commit = "f7e02b7e"},
 representative = false},
{id = "list_L2904_zip_eq_conv",
 goal = ``LENGTH v_xs0 = LENGTH v_ys0 ⇒
(ZIP (v_xs0,v_ys0) = v_zs0 ⇔ MAP FST v_zs0 = v_xs0 ∧ MAP SND v_zs0 = v_ys0)``,
 source_method = "by (auto simp add: zip_map_fst_snd)",
 provenance = {file = "src/HOL/List.thy", line = 2904, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3010_list_all2_lengthD",
 goal = ``LIST_REL v_P0 v_xs0 v_ys0 ⇒ LENGTH v_xs0 = LENGTH v_ys0``,
 source_method = "by (simp add: list_all2_iff)",
 provenance = {file = "src/HOL/List.thy", line = 3010, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3014_list_all2_Nil",
 goal = ``LIST_REL v_P0 [] v_ys0 ⇔ v_ys0 = []``,
 source_method = "by (simp add: list_all2_iff)",
 provenance = {file = "src/HOL/List.thy", line = 3014, commit = "f7e02b7e"},
 representative = true},
{id = "list_L3017_list_all2_Nil2",
 goal = ``LIST_REL v_P0 v_xs0 [] ⇔ v_xs0 = []``,
 source_method = "by (simp add: list_all2_iff)",
 provenance = {file = "src/HOL/List.thy", line = 3017, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3020_list_all2_Cons",
 goal = ``LIST_REL v_P0 (v_x0::v_xs0) (v_y0::v_ys0) ⇔
v_P0 v_x0 v_y0 ∧ LIST_REL v_P0 v_xs0 v_ys0``,
 source_method = "by (auto simp add: list_all2_iff)",
 provenance = {file = "src/HOL/List.thy", line = 3020, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3042_list_all2_rev",
 goal = ``LIST_REL v_P0 (REVERSE v_xs0) (REVERSE v_ys0) ⇔ LIST_REL v_P0 v_xs0 v_ys0``,
 source_method = "by (simp add: list_all2_iff zip_rev cong: conj_cong)",
 provenance = {file = "src/HOL/List.thy", line = 3042, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3089_list_all2_appendI",
 goal = ``LIST_REL v_P0 v_a0 v_b0 ⇒
LIST_REL v_P0 v_c0 v_d0 ⇒
LIST_REL v_P0 (v_a0 ++ v_c0) (v_b0 ++ v_d0)``,
 source_method = "by (simp add: list_all2_append list_all2_lengthD)",
 provenance = {file = "src/HOL/List.thy", line = 3089, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3093_list_all2_conv_all_nth",
 goal = ``LIST_REL v_P0 v_xs0 v_ys0 ⇔
LENGTH v_xs0 = LENGTH v_ys0 ∧
∀b_i.
  b_i < LENGTH v_xs0 ⇒
  v_P0 ((λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_xs0 b_i)
    ((λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_ys0 b_i)``,
 source_method = "by (force simp add: list_all2_iff set_zip)",
 provenance = {file = "src/HOL/List.thy", line = 3093, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3112_list_all2_all_nthI",
 goal = ``LENGTH v_a0 = LENGTH v_b0 ⇒
(∀b_n.
   b_n < LENGTH v_a0 ⇒
   v_P0 ((λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_a0 b_n)
     ((λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_b0 b_n)) ⇒
LIST_REL v_P0 v_a0 v_b0``,
 source_method = "by (simp add: list_all2_conv_all_nth)",
 provenance = {file = "src/HOL/List.thy", line = 3112, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3116_list_all2I",
 goal = ``(∀b_x. MEM b_x (ZIP (v_a0,v_b0)) ⇒ UNCURRY v_P0 b_x) ⇒
LENGTH v_a0 = LENGTH v_b0 ⇒
LIST_REL v_P0 v_a0 v_b0``,
 source_method = "by (simp add: list_all2_iff)",
 provenance = {file = "src/HOL/List.thy", line = 3116, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3120_list_all2_nthD",
 goal = ``LIST_REL v_P0 v_xs0 v_ys0 ⇒
v_p0 < LENGTH v_xs0 ⇒
v_P0 ((λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_xs0 v_p0)
  ((λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_ys0 v_p0)``,
 source_method = "by (simp add: list_all2_conv_all_nth)",
 provenance = {file = "src/HOL/List.thy", line = 3120, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3128_list_all2_map1",
 goal = ``LIST_REL v_P0 (MAP v_f0 v_as0) v_bs0 ⇔
LIST_REL (λb_x b_y. v_P0 (v_f0 b_x) b_y) v_as0 v_bs0``,
 source_method = "by (simp add: list_all2_conv_all_nth)",
 provenance = {file = "src/HOL/List.thy", line = 3128, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3132_list_all2_map2",
 goal = ``LIST_REL v_P0 v_as0 (MAP v_f0 v_bs0) ⇔
LIST_REL (λb_x b_y. v_P0 b_x (v_f0 b_y)) v_as0 v_bs0``,
 source_method = "by (auto simp add: list_all2_conv_all_nth)",
 provenance = {file = "src/HOL/List.thy", line = 3132, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3136_list_all2_refl",
 goal = ``(∀b_x. v_P0 b_x b_x) ⇒ LIST_REL v_P0 v_xs0 v_xs0``,
 source_method = "by (simp add: list_all2_conv_all_nth)",
 provenance = {file = "src/HOL/List.thy", line = 3136, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3168_list_eq_iff_zip_eq",
 goal = ``v_xs0 = v_ys0 ⇔
LENGTH v_xs0 = LENGTH v_ys0 ∧
∀b_set. MEM b_set (ZIP (v_xs0,v_ys0)) ⇒ (λ(b_x,b_y). b_x = b_y) b_set``,
 source_method = "by(auto simp add: set_zip list_all2_eq list_all2_conv_all_nth cong: conj_cong)",
 provenance = {file = "src/HOL/List.thy", line = 3168, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3172_list_all2_same",
 goal = ``LIST_REL v_P0 v_xs0 v_xs0 ⇔ ∀b_x. MEM b_x v_xs0 ⇒ v_P0 b_x b_x``,
 source_method = "by(auto simp add: list_all2_conv_all_nth set_conv_nth)",
 provenance = {file = "src/HOL/List.thy", line = 3172, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3286_rev_conv_fold",
 goal = ``REVERSE v_xs0 = source_fold CONS v_xs0 []``,
 source_method = "by (simp add: fold_Cons_rev)",
 provenance = {file = "src/HOL/List.thy", line = 3286, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3320_union_coset_filter",
 goal = ``(λb_coset_list. COMPL (set b_coset_list)) v_xs0 ∪ v_A0 =
(λb_coset_list. COMPL (set b_coset_list)) (FILTER (λb_x. b_x ∉ v_A0) v_xs0)``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 3320, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3332_minus_coset_filter",
 goal = ``v_A0 DIFF (λb_coset_list. COMPL (set b_coset_list)) v_xs0 =
set (FILTER (λb_x. b_x ∈ v_A0) v_xs0)``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 3332, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3336_inter_set_filter",
 goal = ``v_A0 ∩ set v_xs0 = set (FILTER (λb_x. b_x ∈ v_A0) v_xs0)``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 3336, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3340_inter_coset_fold",
 goal = ``v_A0 ∩ (λb_coset_list. COMPL (set b_coset_list)) v_xs0 =
(λb_fold_function b_fold_list b_fold_initial.
     FOLDR b_fold_function b_fold_initial b_fold_list)
  (λb_remove_item b_remove_set. b_remove_set DELETE b_remove_item) v_xs0 v_A0``,
 source_method = "by (simp add: Diff_eq [symmetric] minus_set_fold)",
 provenance = {file = "src/HOL/List.thy", line = 3340, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3400_foldr_conv_foldl",
 goal = ``(λb_fold_function b_fold_list b_fold_initial.
     FOLDR b_fold_function b_fold_initial b_fold_list) v_f0 v_xs0 v_a0 =
FOLDL (λb_x b_y. v_f0 b_y b_x) v_a0 (REVERSE v_xs0)``,
 source_method = "by (simp add: foldr_conv_fold foldl_conv_fold)",
 provenance = {file = "src/HOL/List.thy", line = 3400, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3404_foldl_conv_foldr",
 goal = ``FOLDL v_f0 v_a0 v_xs0 =
(λb_fold_function b_fold_list b_fold_initial.
     FOLDR b_fold_function b_fold_initial b_fold_list)
  (λb_x b_y. v_f0 b_y b_x) (REVERSE v_xs0) v_a0``,
 source_method = "by (simp add: foldr_conv_fold foldl_conv_fold)",
 provenance = {file = "src/HOL/List.thy", line = 3404, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3413_foldr_cong",
 goal = ``v_a0 = v_b0 ⇒
v_l0 = v_k0 ⇒
(∀b_a b_x. MEM b_x v_l0 ⇒ v_f0 b_x b_a = v_g0 b_x b_a) ⇒
(λb_fold_function b_fold_list b_fold_initial.
     FOLDR b_fold_function b_fold_initial b_fold_list) v_f0 v_l0 v_a0 =
(λb_fold_function b_fold_list b_fold_initial.
     FOLDR b_fold_function b_fold_initial b_fold_list) v_g0 v_k0 v_b0``,
 source_method = "by (auto simp add: foldr_conv_fold intro!: fold_cong)",
 provenance = {file = "src/HOL/List.thy", line = 3413, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3417_foldl_cong",
 goal = ``v_a0 = v_b0 ⇒
v_l0 = v_k0 ⇒
(∀b_a b_x. MEM b_x v_l0 ⇒ v_f0 b_a b_x = v_g0 b_a b_x) ⇒
FOLDL v_f0 v_a0 v_l0 = FOLDL v_g0 v_b0 v_k0``,
 source_method = "by (auto simp add: foldl_conv_fold intro!: fold_cong)",
 provenance = {file = "src/HOL/List.thy", line = 3417, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3421_foldr_append",
 goal = ``(λb_fold_function b_fold_list b_fold_initial.
     FOLDR b_fold_function b_fold_initial b_fold_list) v_f0 (v_xs0 ++ v_ys0)
  v_a0 =
(λb_fold_function b_fold_list b_fold_initial.
     FOLDR b_fold_function b_fold_initial b_fold_list) v_f0 v_xs0
  ((λb_fold_function b_fold_list b_fold_initial.
        FOLDR b_fold_function b_fold_initial b_fold_list) v_f0 v_ys0 v_a0)``,
 source_method = "by (simp add: foldr_conv_fold)",
 provenance = {file = "src/HOL/List.thy", line = 3421, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3424_foldl_append",
 goal = ``FOLDL v_f0 v_a0 (v_xs0 ++ v_ys0) = FOLDL v_f0 (FOLDL v_f0 v_a0 v_xs0) v_ys0``,
 source_method = "by (simp add: foldl_conv_fold)",
 provenance = {file = "src/HOL/List.thy", line = 3424, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3427_foldr_map",
 goal = ``(λb_fold_function b_fold_list b_fold_initial.
     FOLDR b_fold_function b_fold_initial b_fold_list) v_g0 (MAP v_f0 v_xs0)
  v_a0 =
(λb_fold_function b_fold_list b_fold_initial.
     FOLDR b_fold_function b_fold_initial b_fold_list) (v_g0 ∘ v_f0) v_xs0
  v_a0``,
 source_method = "by (simp add: foldr_conv_fold fold_map rev_map)",
 provenance = {file = "src/HOL/List.thy", line = 3427, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3430_foldr_filter",
 goal = ``(λb_fold_function b_fold_list b_fold_initial.
     FOLDR b_fold_function b_fold_initial b_fold_list) v_f0
  (FILTER v_P0 v_xs0) =
(λb_fold_function b_fold_list b_fold_initial.
     FOLDR b_fold_function b_fold_initial b_fold_list)
  (λb_x. if v_P0 b_x then v_f0 b_x else I) v_xs0``,
 source_method = "by (simp add: foldr_conv_fold rev_filter fold_filter)",
 provenance = {file = "src/HOL/List.thy", line = 3430, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3434_foldl_map",
 goal = ``FOLDL v_g0 v_a0 (MAP v_f0 v_xs0) =
FOLDL (λb_a b_x. v_g0 b_a (v_f0 b_x)) v_a0 v_xs0``,
 source_method = "by (simp add: foldl_conv_fold fold_map comp_def)",
 provenance = {file = "src/HOL/List.thy", line = 3434, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3438_concat_conv_foldr",
 goal = ``FLAT v_xss0 =
(λb_fold_function b_fold_list b_fold_initial.
     FOLDR b_fold_function b_fold_initial b_fold_list) $++ v_xss0 []``,
 source_method = "by (simp add: fold_append_concat_rev foldr_conv_fold)",
 provenance = {file = "src/HOL/List.thy", line = 3438, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3481_upt_Suc_append",
 goal = ``v_i0 ≤ v_j0 ⇒
(λb_upt_start b_upt_end.
     GENLIST (λb_upt_offset. b_upt_start + b_upt_offset)
       (b_upt_end − b_upt_start)) v_i0 (SUC v_j0) =
(λb_upt_start b_upt_end.
     GENLIST (λb_upt_offset. b_upt_start + b_upt_offset)
       (b_upt_end − b_upt_start)) v_i0 v_j0 ++ [v_j0]``,
 source_method = "by simp",
 provenance = {file = "src/HOL/List.thy", line = 3481, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3485_upt_conv_Cons",
 goal = ``v_i0 < v_j0 ⇒
(λb_upt_start b_upt_end.
     GENLIST (λb_upt_offset. b_upt_start + b_upt_offset)
       (b_upt_end − b_upt_start)) v_i0 v_j0 =
v_i0::
  (λb_upt_start b_upt_end.
       GENLIST (λb_upt_offset. b_upt_start + b_upt_offset)
         (b_upt_end − b_upt_start)) (SUC v_i0) v_j0``,
 source_method = "by (simp add: upt_rec)",
 provenance = {file = "src/HOL/List.thy", line = 3485, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3506_hd_upt",
 goal = ``v_i0 < v_j0 ⇒
HD
  ((λb_upt_start b_upt_end.
        GENLIST (λb_upt_offset. b_upt_start + b_upt_offset)
          (b_upt_end − b_upt_start)) v_i0 v_j0) = v_i0``,
 source_method = "by(simp add:upt_conv_Cons)",
 provenance = {file = "src/HOL/List.thy", line = 3506, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3509_tl_upt",
 goal = ``TL
  ((λb_upt_start b_upt_end.
        GENLIST (λb_upt_offset. b_upt_start + b_upt_offset)
          (b_upt_end − b_upt_start)) v_m0 v_n0) =
(λb_upt_start b_upt_end.
     GENLIST (λb_upt_offset. b_upt_start + b_upt_offset)
       (b_upt_end − b_upt_start)) (SUC v_m0) v_n0``,
 source_method = "by (simp add: upt_rec)",
 provenance = {file = "src/HOL/List.thy", line = 3509, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3569_list_all2_antisym",
 goal = ``(∀b_x b_y. v_P0 b_x b_y ⇒ v_Q0 b_y b_x ⇒ b_x = b_y) ⇒
LIST_REL v_P0 v_xs0 v_ys0 ⇒
LIST_REL v_Q0 v_ys0 v_xs0 ⇒
v_xs0 = v_ys0``,
 source_method = "by (simp add: list_all2_conv_all_nth nth_equalityI)",
 provenance = {file = "src/HOL/List.thy", line = 3569, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3908_nth_eq_iff_index_eq",
 goal = ``ALL_DISTINCT v_xs0 ⇒
v_i0 < LENGTH v_xs0 ⇒
v_j0 < LENGTH v_xs0 ⇒
((λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_xs0 v_i0 =
 (λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_xs0 v_j0 ⇔ v_i0 = v_j0)``,
 source_method = "by(auto simp: distinct_conv_nth)",
 provenance = {file = "src/HOL/List.thy", line = 3908, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3912_distinct_Ex1",
 goal = ``ALL_DISTINCT v_xs0 ⇒
MEM v_x0 v_xs0 ⇒
∃!b_i.
  b_i < LENGTH v_xs0 ∧
  (λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_xs0 b_i = v_x0``,
 source_method = "by (auto simp: in_set_conv_nth nth_eq_iff_index_eq)",
 provenance = {file = "src/HOL/List.thy", line = 3912, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3919_bij_betw_nth",
 goal = ``ALL_DISTINCT v_xs0 ⇒
v_A0 = (λb_less_than b_less_item. b_less_item < b_less_than) (LENGTH v_xs0) ⇒
v_B0 = set v_xs0 ⇒
BIJ ((λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_xs0) v_A0 v_B0``,
 source_method = "using assms unfolding bij_betw_def by (auto intro!: inj_on_nth simp: set_conv_nth)",
 provenance = {file = "src/HOL/List.thy", line = 3919, commit = "f7e02b7e"},
 representative = false},
{id = "list_L3925_set_update_distinct",
 goal = ``ALL_DISTINCT v_xs0 ⇒
v_n0 < LENGTH v_xs0 ⇒
set
  ((λb_update_list b_update_index b_update_item.
        b_update_list❲b_update_index ↦ b_update_item❳) v_xs0 v_n0 v_x0) =
v_x0 INSERT
set v_xs0 DIFF
{(λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_xs0 v_n0}``,
 source_method = "by(auto simp: set_eq_iff in_set_conv_nth nth_list_update nth_eq_iff_index_eq)",
 provenance = {file = "src/HOL/List.thy", line = 3925, commit = "f7e02b7e"},
 representative = false},
{id = "list_L4011_length_remdups_concat",
 goal = ``LENGTH (nub (FLAT v_xss0)) =
CARD (BIGUNION (IMAGE (λb_xs. set b_xs) (set v_xss0)))``,
 source_method = "by (simp add: distinct_card [symmetric])",
 provenance = {file = "src/HOL/List.thy", line = 4011, commit = "f7e02b7e"},
 representative = false},
{id = "list_L4065_set_take_disj_set_drop_if_distinct",
 goal = ``ALL_DISTINCT v_vs0 ⇒
v_i0 ≤ v_j0 ⇒
set (TAKE v_i0 v_vs0) ∩ set (DROP v_j0 v_vs0) = ∅``,
 source_method = "by (auto simp: in_set_conv_nth distinct_conv_nth)",
 provenance = {file = "src/HOL/List.thy", line = 4065, commit = "f7e02b7e"},
 representative = false},
{id = "list_L4071_distinct_singleton",
 goal = ``ALL_DISTINCT [v_x0]``,
 source_method = "by simp",
 provenance = {file = "src/HOL/List.thy", line = 4071, commit = "f7e02b7e"},
 representative = false},
{id = "list_L4073_distinct_length_2_or_more",
 goal = ``ALL_DISTINCT (v_a0::v_b0::v_xs0) ⇔
v_a0 ≠ v_b0 ∧ ALL_DISTINCT (v_a0::v_xs0) ∧ ALL_DISTINCT (v_b0::v_xs0)``,
 source_method = "by force",
 provenance = {file = "src/HOL/List.thy", line = 4073, commit = "f7e02b7e"},
 representative = false},
{id = "list_L4464_in_set_insert",
 goal = ``MEM v_x0 v_xs0 ⇒ (if MEM v_x0 v_xs0 then v_xs0 else v_x0::v_xs0) = v_xs0``,
 source_method = "by (simp add: List.insert_def)",
 provenance = {file = "src/HOL/List.thy", line = 4464, commit = "f7e02b7e"},
 representative = false},
{id = "list_L4468_not_in_set_insert",
 goal = ``¬MEM v_x0 v_xs0 ⇒
(if MEM v_x0 v_xs0 then v_xs0 else v_x0::v_xs0) = v_x0::v_xs0``,
 source_method = "by (simp add: List.insert_def)",
 provenance = {file = "src/HOL/List.thy", line = 4468, commit = "f7e02b7e"},
 representative = false},
{id = "list_L4472_insert_Nil",
 goal = ``(if MEM v_x0 [] then [] else [v_x0]) = [v_x0]``,
 source_method = "by simp",
 provenance = {file = "src/HOL/List.thy", line = 4472, commit = "f7e02b7e"},
 representative = false},
{id = "list_L4475_set_insert",
 goal = ``set (if MEM v_x0 v_xs0 then v_xs0 else v_x0::v_xs0) = v_x0 INSERT set v_xs0``,
 source_method = "by (auto simp add: List.insert_def)",
 provenance = {file = "src/HOL/List.thy", line = 4475, commit = "f7e02b7e"},
 representative = false},
{id = "list_L4478_distinct_insert",
 goal = ``ALL_DISTINCT (if MEM v_x0 v_xs0 then v_xs0 else v_x0::v_xs0) ⇔
ALL_DISTINCT v_xs0``,
 source_method = "by (simp add: List.insert_def)",
 provenance = {file = "src/HOL/List.thy", line = 4478, commit = "f7e02b7e"},
 representative = false},
{id = "list_L4481_insert_remdups",
 goal = ``(if MEM v_x0 (nub v_xs0) then nub v_xs0 else v_x0::nub v_xs0) =
nub (if MEM v_x0 v_xs0 then v_xs0 else v_x0::v_xs0)``,
 source_method = "by (simp add: List.insert_def)",
 provenance = {file = "src/HOL/List.thy", line = 4481, commit = "f7e02b7e"},
 representative = false},
{id = "list_L4553_count_notin",
 goal = ``¬MEM v_x0 v_xs0 ⇒
(λb_count_list b_count_item. LIST_ELEM_COUNT b_count_item b_count_list) v_xs0
  v_x0 = 0``,
 source_method = "by(simp add: count_list_0_iff)",
 provenance = {file = "src/HOL/List.thy", line = 4553, commit = "f7e02b7e"},
 representative = false},
{id = "list_L4854_minus_list_set_Nil2",
 goal = ``(λb_minus_left b_minus_right.
     FILTER (λb_minus_item. ¬MEM b_minus_item b_minus_right) b_minus_left)
  v_xs0 [] = v_xs0``,
 source_method = "by(simp add: minus_list_set_def)",
 provenance = {file = "src/HOL/List.thy", line = 4854, commit = "f7e02b7e"},
 representative = false},
{id = "list_L4867_minus_list_set_Nil1",
 goal = ``(λb_minus_left b_minus_right.
     FILTER (λb_minus_item. ¬MEM b_minus_item b_minus_right) b_minus_left) []
  v_xs0 = []``,
 source_method = "by (simp add: minus_list_set_eq_filter)",
 provenance = {file = "src/HOL/List.thy", line = 4867, commit = "f7e02b7e"},
 representative = false},
{id = "list_L4870_minus_list_set_Cons1",
 goal = ``(λb_minus_left b_minus_right.
     FILTER (λb_minus_item. ¬MEM b_minus_item b_minus_right) b_minus_left)
  (v_x0::v_xs0) v_ys0 =
if MEM v_x0 v_ys0 then
  (λb_minus_left b_minus_right.
       FILTER (λb_minus_item. ¬MEM b_minus_item b_minus_right) b_minus_left)
    v_xs0 v_ys0
else
  v_x0::
    (λb_minus_left b_minus_right.
         FILTER (λb_minus_item. ¬MEM b_minus_item b_minus_right) b_minus_left)
      v_xs0 v_ys0``,
 source_method = "by(simp add:minus_list_set_eq_filter)",
 provenance = {file = "src/HOL/List.thy", line = 4870, commit = "f7e02b7e"},
 representative = false},
{id = "list_L4878_length_minus_list_set",
 goal = ``LENGTH
  ((λb_minus_left b_minus_right.
        FILTER (λb_minus_item. ¬MEM b_minus_item b_minus_right) b_minus_left)
     v_xs0 v_ys0) ≤ LENGTH v_xs0``,
 source_method = "by (simp add: minus_list_set_eq_filter)",
 provenance = {file = "src/HOL/List.thy", line = 4878, commit = "f7e02b7e"},
 representative = false},
{id = "list_L4881_distinct_minus_list_set",
 goal = ``ALL_DISTINCT v_xs0 ⇒
ALL_DISTINCT
  ((λb_minus_left b_minus_right.
        FILTER (λb_minus_item. ¬MEM b_minus_item b_minus_right) b_minus_left)
     v_xs0 v_ys0)``,
 source_method = "by (simp add: minus_list_set_eq_filter)",
 provenance = {file = "src/HOL/List.thy", line = 4881, commit = "f7e02b7e"},
 representative = false},
{id = "list_L4890_set_inter_list_set",
 goal = ``set
  ((λb_inter_left b_inter_right.
        FILTER (λb_inter_item. MEM b_inter_item b_inter_right) b_inter_left)
     v_xs0 v_ys0) = set v_xs0 ∩ set v_ys0``,
 source_method = "by(auto simp add: inter_list_set_def)",
 provenance = {file = "src/HOL/List.thy", line = 4890, commit = "f7e02b7e"},
 representative = false},
{id = "list_L4893_inter_list_set_Nil",
 goal = ``(λb_inter_left b_inter_right.
     FILTER (λb_inter_item. MEM b_inter_item b_inter_right) b_inter_left) []
  v_xs0 = []``,
 source_method = "by (simp add: inter_list_set_def)",
 provenance = {file = "src/HOL/List.thy", line = 4893, commit = "f7e02b7e"},
 representative = false},
{id = "list_L4896_inter_list_set_Cons",
 goal = ``(λb_inter_left b_inter_right.
     FILTER (λb_inter_item. MEM b_inter_item b_inter_right) b_inter_left)
  (v_x0::v_xs0) v_ys0 =
if MEM v_x0 v_ys0 then
  v_x0::
    (λb_inter_left b_inter_right.
         FILTER (λb_inter_item. MEM b_inter_item b_inter_right) b_inter_left)
      v_xs0 v_ys0
else
  (λb_inter_left b_inter_right.
       FILTER (λb_inter_item. MEM b_inter_item b_inter_right) b_inter_left)
    v_xs0 v_ys0``,
 source_method = "by(simp add:inter_list_set_def)",
 provenance = {file = "src/HOL/List.thy", line = 4896, commit = "f7e02b7e"},
 representative = false},
{id = "list_L4900_inter_list_set_Nil2",
 goal = ``(λb_inter_left b_inter_right.
     FILTER (λb_inter_item. MEM b_inter_item b_inter_right) b_inter_left)
  v_xs0 [] = []``,
 source_method = "by(simp add: inter_list_set_def)",
 provenance = {file = "src/HOL/List.thy", line = 4900, commit = "f7e02b7e"},
 representative = false},
{id = "list_L4903_distinct_inter_list_set",
 goal = ``ALL_DISTINCT v_xs0 ⇒
ALL_DISTINCT
  ((λb_inter_left b_inter_right.
        FILTER (λb_inter_item. MEM b_inter_item b_inter_right) b_inter_left)
     v_xs0 v_ys0)``,
 source_method = "by (simp add: inter_list_set_def)",
 provenance = {file = "src/HOL/List.thy", line = 4903, commit = "f7e02b7e"},
 representative = false},
{id = "list_L4906_inter_list_set_append",
 goal = ``(λb_inter_left b_inter_right.
     FILTER (λb_inter_item. MEM b_inter_item b_inter_right) b_inter_left)
  (v_xs0 ++ v_ys0) v_zs0 =
(λb_inter_left b_inter_right.
     FILTER (λb_inter_item. MEM b_inter_item b_inter_right) b_inter_left)
  v_xs0 v_zs0 ++
(λb_inter_left b_inter_right.
     FILTER (λb_inter_item. MEM b_inter_item b_inter_right) b_inter_left)
  v_ys0 v_zs0``,
 source_method = "by (simp add: inter_list_set_def)",
 provenance = {file = "src/HOL/List.thy", line = 4906, commit = "f7e02b7e"},
 representative = false},
{id = "list_L4910_length_inter_list_set",
 goal = ``LENGTH
  ((λb_inter_left b_inter_right.
        FILTER (λb_inter_item. MEM b_inter_item b_inter_right) b_inter_left)
     v_xs0 v_ys0) ≤ LENGTH v_xs0``,
 source_method = "by (simp add: inter_list_set_def)",
 provenance = {file = "src/HOL/List.thy", line = 4910, commit = "f7e02b7e"},
 representative = false},
{id = "list_L4998_set_replicate_conv_if",
 goal = ``set (REPLICATE v_n0 v_x0) = if v_n0 = 0 then ∅ else {v_x0}``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 4998, commit = "f7e02b7e"},
 representative = false},
{id = "list_L5001_in_set_replicate",
 goal = ``MEM v_x0 (REPLICATE v_n0 v_y0) ⇔ v_x0 = v_y0 ∧ v_n0 ≠ 0``,
 source_method = "by (simp add: set_replicate_conv_if)",
 provenance = {file = "src/HOL/List.thy", line = 5001, commit = "f7e02b7e"},
 representative = false},
{id = "list_L5008_Ball_set_replicate",
 goal = ``(∀b_x. MEM b_x (REPLICATE v_n0 v_a0) ⇒ v_P0 b_x) ⇔ v_P0 v_a0 ∨ v_n0 = 0``,
 source_method = "by(simp add: set_replicate_conv_if)",
 provenance = {file = "src/HOL/List.thy", line = 5008, commit = "f7e02b7e"},
 representative = false},
{id = "list_L5012_Bex_set_replicate",
 goal = ``(∃b_x. MEM b_x (REPLICATE v_n0 v_a0) ∧ v_P0 b_x) ⇔ v_P0 v_a0 ∧ v_n0 ≠ 0``,
 source_method = "by(simp add: set_replicate_conv_if)",
 provenance = {file = "src/HOL/List.thy", line = 5012, commit = "f7e02b7e"},
 representative = false},
{id = "list_L5044_takeWhile_replicate",
 goal = ``source_takeWhile v_P0 (REPLICATE v_n0 v_x0) =
if v_P0 v_x0 then REPLICATE v_n0 v_x0 else []``,
 source_method = "using takeWhile_eq_Nil_iff by fastforce",
 provenance = {file = "src/HOL/List.thy", line = 5044, commit = "f7e02b7e"},
 representative = false},
{id = "list_L5048_dropWhile_replicate",
 goal = ``dropWhile v_P0 (REPLICATE v_n0 v_x0) =
if v_P0 v_x0 then [] else REPLICATE v_n0 v_x0``,
 source_method = "using dropWhile_eq_self_iff by fastforce",
 provenance = {file = "src/HOL/List.thy", line = 5048, commit = "f7e02b7e"},
 representative = false},
{id = "list_L5788_lists_length_Suc_eq",
 goal = ``(λb_xs. set b_xs ⊆ v_A0 ∧ LENGTH b_xs = SUC v_n0) =
IMAGE (λ(b_xs,b_n). b_n::b_xs)
  (source_Sigma (λb_xs. set b_xs ⊆ v_A0 ∧ LENGTH b_xs = v_n0) (λb_uu_. v_A0))``,
 source_method = "by (auto simp: length_Suc_conv)",
 provenance = {file = "src/HOL/List.thy", line = 5788, commit = "f7e02b7e"},
 representative = false},
{id = "list_L5911_sorted_wrt1",
 goal = ``source_sorted_wrt v_P0 [v_x0] ⇔ T``,
 source_method = "by(simp)",
 provenance = {file = "src/HOL/List.thy", line = 5911, commit = "f7e02b7e"},
 representative = false},
{id = "list_L5946_sorted_wrt_dropWhile",
 goal = ``source_sorted_wrt v_R0 v_xs0 ⇒ source_sorted_wrt v_R0 (dropWhile v_P0 v_xs0)``,
 source_method = "by (auto dest: sorted_wrt_drop simp: dropWhile_eq_drop)",
 provenance = {file = "src/HOL/List.thy", line = 5946, commit = "f7e02b7e"},
 representative = false},
{id = "list_L5964_sorted_wrt01",
 goal = ``LENGTH v_xs0 ≤ 1 ⇒ source_sorted_wrt v_P0 v_xs0``,
 source_method = "by(auto simp: le_Suc_eq length_Suc_conv)",
 provenance = {file = "src/HOL/List.thy", line = 5964, commit = "f7e02b7e"},
 representative = false},
{id = "list_L5971_sorted_wrt_nth_less",
 goal = ``source_sorted_wrt v_P0 v_xs0 ⇒
v_i0 < v_j0 ⇒
v_j0 < LENGTH v_xs0 ⇒
v_P0 v_xs0❲v_i0❳ v_xs0❲v_j0❳``,
 source_method = "by(auto simp: sorted_wrt_iff_nth_less)",
 provenance = {file = "src/HOL/List.thy", line = 5971, commit = "f7e02b7e"},
 representative = false},
{id = "list_L6208_sorted_upt",
 goal = ``source_sorted_wrt (λb_order_left b_order_right. b_order_left ≤ b_order_right)
  (GENLIST (λb_upt_offset. v_m0 + b_upt_offset) (v_n0 − v_m0))``,
 source_method = "by(simp add: sorted_wrt_mono_rel[OF _ sorted_wrt_upt])",
 provenance = {file = "src/HOL/List.thy", line = 6208, commit = "f7e02b7e"},
 representative = false},
{id = "list_L6948_Cons_in_lists_iff",
 goal = ``v_x0::v_xs0 ∈
(λb_lists_set b_lists_list. set b_lists_list ⊆ b_lists_set) v_A0 ⇔
v_x0 ∈ v_A0 ∧
v_xs0 ∈ (λb_lists_set b_lists_list. set b_lists_list ⊆ b_lists_set) v_A0``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 6948, commit = "f7e02b7e"},
 representative = false},
{id = "list_L6975_lists_eq_set",
 goal = ``(λb_lists_set b_lists_list. set b_lists_list ⊆ b_lists_set) v_A0 =
(λb_xs. set b_xs ⊆ v_A0)``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 6975, commit = "f7e02b7e"},
 representative = false},
{id = "list_L6978_lists_empty",
 goal = ``(λb_lists_set b_lists_list. set b_lists_list ⊆ b_lists_set) ∅ = {[]}``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 6978, commit = "f7e02b7e"},
 representative = false},
{id = "list_L6981_lists_UNIV",
 goal = ``(λb_lists_set b_lists_list. set b_lists_list ⊆ b_lists_set) 𝕌(:α) =
𝕌(:α list)``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 6981, commit = "f7e02b7e"},
 representative = false},
{id = "list_L7035_set_Cons_sing_Nil",
 goal = ``(λb_cons_heads b_cons_tails b_cons_list.
     ∃b_cons_head b_cons_tail.
       b_cons_head ∈ b_cons_heads ∧ b_cons_tail ∈ b_cons_tails ∧
       b_cons_list = b_cons_head::b_cons_tail) v_A0 {[]} =
IMAGE (λb_x. [b_x]) v_A0``,
 source_method = "by (auto simp add: set_Cons_def)",
 provenance = {file = "src/HOL/List.thy", line = 7035, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8167_list_all_iff",
 goal = ``EVERY v_P0 v_xs0 ⇔ ∀b_set. MEM b_set v_xs0 ⇒ v_P0 b_set``,
 source_method = "by (simp add: list.pred_set)",
 provenance = {file = "src/HOL/List.thy", line = 8167, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8183_list_all_Nil_iff",
 goal = ``EVERY v_P0 [] ⇔ T``,
 source_method = "by (simp add: list_all_iff)",
 provenance = {file = "src/HOL/List.thy", line = 8183, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8187_list_all_Cons_iff",
 goal = ``EVERY v_P0 (v_x0::v_xs0) ⇔ v_P0 v_x0 ∧ EVERY v_P0 v_xs0``,
 source_method = "by (simp add: list_all_iff)",
 provenance = {file = "src/HOL/List.thy", line = 8187, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8191_list_ex_Nil_iff",
 goal = ``EXISTS v_P0 [] ⇔ F``,
 source_method = "by (simp add: list_ex_iff)",
 provenance = {file = "src/HOL/List.thy", line = 8191, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8195_list_ex_Cons_iff",
 goal = ``EXISTS v_P0 (v_x0::v_xs0) ⇔ v_P0 v_x0 ∨ EXISTS v_P0 v_xs0``,
 source_method = "by (simp add: list_ex_iff)",
 provenance = {file = "src/HOL/List.thy", line = 8195, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8207_list_all_append",
 goal = ``EVERY v_P0 (v_xs0 ++ v_ys0) ⇔ EVERY v_P0 v_xs0 ∧ EVERY v_P0 v_ys0``,
 source_method = "by (auto simp add: list_all_iff)",
 provenance = {file = "src/HOL/List.thy", line = 8207, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8211_list_ex_append",
 goal = ``EXISTS v_P0 (v_xs0 ++ v_ys0) ⇔ EXISTS v_P0 v_xs0 ∨ EXISTS v_P0 v_ys0``,
 source_method = "by (auto simp add: list_ex_iff)",
 provenance = {file = "src/HOL/List.thy", line = 8211, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8215_list_all_rev",
 goal = ``EVERY v_P0 (REVERSE v_xs0) ⇔ EVERY v_P0 v_xs0``,
 source_method = "by (simp add: list_all_iff)",
 provenance = {file = "src/HOL/List.thy", line = 8215, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8219_list_ex_rev",
 goal = ``EXISTS v_P0 (REVERSE v_xs0) ⇔ EXISTS v_P0 v_xs0``,
 source_method = "by (simp add: list_ex_iff)",
 provenance = {file = "src/HOL/List.thy", line = 8219, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8223_list_all_length",
 goal = ``EVERY v_P0 v_xs0 ⇔
∀b_n.
  b_n < LENGTH v_xs0 ⇒
  v_P0 ((λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_xs0 b_n)``,
 source_method = "by (auto simp add: list_all_iff set_conv_nth)",
 provenance = {file = "src/HOL/List.thy", line = 8223, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8227_list_ex_length",
 goal = ``EXISTS v_P0 v_xs0 ⇔
∃b_n.
  b_n < LENGTH v_xs0 ∧
  v_P0 ((λb_nth_list b_nth_index. b_nth_list❲b_nth_index❳) v_xs0 b_n)``,
 source_method = "by (auto simp add: list_ex_iff set_conv_nth)",
 provenance = {file = "src/HOL/List.thy", line = 8227, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8236_list_ex_cong",
 goal = ``v_xs0 = v_ys0 ⇒
(∀b_x. MEM b_x v_ys0 ⇒ (v_f0 b_x ⇔ v_g0 b_x)) ⇒
(EXISTS v_f0 v_xs0 ⇔ EXISTS v_g0 v_ys0)``,
 source_method = "using that by (simp add: list_ex_iff)",
 provenance = {file = "src/HOL/List.thy", line = 8236, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8607_empty_set",
 goal = ``∅ = set []``,
 source_method = "by simp",
 provenance = {file = "src/HOL/List.thy", line = 8607, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8611_UNIV_coset",
 goal = ``𝕌(:α) = (λb_coset_list. COMPL (set b_coset_list)) []``,
 source_method = "by simp",
 provenance = {file = "src/HOL/List.thy", line = 8611, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8615_compl_set",
 goal = ``COMPL (set v_xs0) = (λb_coset_list. COMPL (set b_coset_list)) v_xs0``,
 source_method = "by simp",
 provenance = {file = "src/HOL/List.thy", line = 8615, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8619_compl_coset",
 goal = ``COMPL ((λb_coset_list. COMPL (set b_coset_list)) v_xs0) = set v_xs0``,
 source_method = "by simp",
 provenance = {file = "src/HOL/List.thy", line = 8619, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8638_filter_set",
 goal = ``(λb_filter_predicate b_filter_set b_filter_item.
     b_filter_item ∈ b_filter_set ∧ b_filter_predicate b_filter_item) v_P0
  (set v_xs0) = set (FILTER v_P0 v_xs0)``,
 source_method = "by simp",
 provenance = {file = "src/HOL/List.thy", line = 8638, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8642_image_set",
 goal = ``IMAGE v_f0 (set v_xs0) = set (MAP v_f0 v_xs0)``,
 source_method = "by simp",
 provenance = {file = "src/HOL/List.thy", line = 8642, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8646_subset_code_1",
 goal = ``set v_xs0 ⊆ v_B0 ⇔ ∀b_x. MEM b_x v_xs0 ⇒ b_x ∈ v_B0``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 8646, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8646_subset_code_2",
 goal = ``v_A0 ⊆ (λb_coset_list. COMPL (set b_coset_list)) v_ys0 ⇔
∀b_y. MEM b_y v_ys0 ⇒ b_y ∉ v_A0``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 8646, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8646_subset_code_3",
 goal = ``(λb_coset_list. COMPL (set b_coset_list)) [] ⊆ set [] ⇔ F``,
 source_method = "by auto",
 provenance = {file = "src/HOL/List.thy", line = 8646, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8652_Ball_set",
 goal = ``(∀b_set. MEM b_set v_xs0 ⇒ v_P0 b_set) ⇔ EVERY v_P0 v_xs0``,
 source_method = "by (simp add: list_all_iff)",
 provenance = {file = "src/HOL/List.thy", line = 8652, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8656_Bex_set",
 goal = ``(∃b_set. MEM b_set v_xs0 ∧ v_P0 b_set) ⇔ EXISTS v_P0 v_xs0``,
 source_method = "by (simp add: list_ex_iff)",
 provenance = {file = "src/HOL/List.thy", line = 8656, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8660_card_set",
 goal = ``CARD (set v_xs0) = LENGTH (nub v_xs0)``,
 source_method = "by (simp add: length_remdups_card_conv)",
 provenance = {file = "src/HOL/List.thy", line = 8660, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8664_the_elem_set",
 goal = ``CHOICE (set [v_x0]) = v_x0``,
 source_method = "by simp",
 provenance = {file = "src/HOL/List.thy", line = 8664, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8687_product_code",
 goal = ``source_product (set v_xs0) (set v_ys0) =
set (FLAT (MAP (λb_x. MAP (λb_y. (b_x,b_y)) v_ys0) v_xs0))``,
 source_method = "by (auto simp add: Product_Type.product_def)",
 provenance = {file = "src/HOL/List.thy", line = 8687, commit = "f7e02b7e"},
 representative = false},
{id = "list_L8705_set_relcomp",
 goal = ``(λb_relcomp_left b_relcomp_right b_relcomp_pair.
     ∃b_relcomp_middle.
       (FST b_relcomp_pair,b_relcomp_middle) ∈ b_relcomp_left ∧
       (b_relcomp_middle,SND b_relcomp_pair) ∈ b_relcomp_right) (set v_xys0)
  (set v_yzs0) =
set
  (FLAT
     (MAP
        (λb_xy.
             FLAT
               (MAP
                  (λb_yz.
                       if SND b_xy = FST b_yz then [(FST b_xy,SND b_yz)]
                       else []) v_yzs0)) v_xys0))``,
 source_method = "by simp (auto simp add: Bex_def image_def)",
 provenance = {file = "src/HOL/List.thy", line = 8705, commit = "f7e02b7e"},
 representative = false},
{id = "list_L9013_list_all_transfer",
 goal = ``(λb_rel_left b_rel_right b_rel_left_function b_rel_right_function.
     ∀b_rel_x b_rel_y.
       b_rel_left b_rel_x b_rel_y ⇒
       b_rel_right (b_rel_left_function b_rel_x)
         (b_rel_right_function b_rel_y))
  ((λb_rel_left b_rel_right b_rel_left_function b_rel_right_function.
        ∀b_rel_x b_rel_y.
          b_rel_left b_rel_x b_rel_y ⇒
          b_rel_right (b_rel_left_function b_rel_x)
            (b_rel_right_function b_rel_y)) v_A0
     (λb_equal_left b_equal_right. b_equal_left ⇔ b_equal_right))
  ((λb_rel_left b_rel_right b_rel_left_function b_rel_right_function.
        ∀b_rel_x b_rel_y.
          b_rel_left b_rel_x b_rel_y ⇒
          b_rel_right (b_rel_left_function b_rel_x)
            (b_rel_right_function b_rel_y)) (LIST_REL v_A0)
     (λb_equal_left b_equal_right. b_equal_left ⇔ b_equal_right)) EVERY EVERY``,
 source_method = "using list.pred_transfer by blast",
 provenance = {file = "src/HOL/List.thy", line = 9013, commit = "f7e02b7e"},
 representative = false}]

end
