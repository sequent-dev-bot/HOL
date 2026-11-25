structure benchLibraryShortfalls =
struct

(* Records for the list, map, option, string and product-type goals
   that the assigned tactic did not close in the 2026-08-28
   measurement.  The classification names the root cause and the note
   says what stands in the way.  A goal listed in [over_budget] was
   cut off by the budget rather than reporting no proof, so its
   classification is the family it belongs to rather than an observed
   residual; a goal whose own note already says it ran out the budget
   is not listed again there.  That list is measured, not inherited:
   the engine work since has brought twelve of its goals back inside
   the budget, and each now carries the class its residual says it
   belongs to (re-measured 2026-09-15). *)

(* Isabelle's [code_unfold] lemmas at List.thy:8259 and 8273 state that
   a set-encoded relation and its predicate encoding agree:
   [(xs, ys) : lexord r <-> lexordp (%x y. (x, y) : r) xs ys], and the
   same for [listrel1].  HOL4 encodes a relation one way only, so both
   sides of each translate to the same term and the source result has
   no HOL4 statement.  They carry no goal, and the corpus accounts for
   them here instead. *)
fun encoding_gap id line : benchLib.shortfall =
  {id = id, cause = benchLib.TranslationGap, date = "2026-08-28",
   note =
     "predicate and set encodings: the source result at List.thy:" ^
     Int.toString line ^ " relates Isabelle's set encoding of a " ^
     "relation to its predicate encoding, a distinction HOL4 does " ^
     "not make, so the translated statement is not the source result"}

val translation : benchLib.shortfall list =
  [encoding_gap "list_L8259_anon_L8259" 8259,
   encoding_gap "list_L8273_anon_L8273" 8273]

val over_budget =
  ["list_L6138_map_sorted_distinct_set_unique",
   "list_L8999_set_Cons_transfer",
   "list_L9013_list_all_transfer"]

fun record note id : benchLib.shortfall =
  {id = id, cause = benchLib.EngineLimitation, date = "2026-08-28",
   note =
     if List.exists (fn other => other = id) over_budget then
       note ^ " (the search did not return within the budget rather " ^
       "than reporting no proof)"
     else
       note}

fun classified classification note ids =
  map (record (classification ^ ": " ^ note)) ids

val prefix_from_its_indices =
  classified "prefix from its indices"
    ("the cited [map_nth_upt] has no HOL4 counterpart: the name table "
     ^ "answers it with [rich_listTheory.MAP_COUNT_LIST], which fuses "
     ^ "the MAP into a GENLIST and says nothing about a prefix, so "
     ^ "what is left is [GENLIST (\\index. EL index xs) count = TAKE "
     ^ "count xs] -- an equation between a list built from the indices "
     ^ "it is read at and a prefix, which neither simpset carries")
    ["list_L3566_map_nth_upt0"]

val transpose_column_lengths =
  classified "transpose column lengths"
    ("the residual is that the column lengths of a transpose "
     ^ "decrease; it holds because the number of rows reaching an "
     ^ "index falls as the index grows, which is an induction "
     ^ "rather than a rewrite")
    ["list_L6453_sorted_transpose"]

val emptiness_from_disjoint_membership =
  classified "emptiness from disjoint membership"
    ("the residual is [x = []] under hypotheses saying no element "
     ^ "of x occurs in either of two other lists; concluding it "
     ^ "needs induction on x, which the search does not perform")
    ["list_L1367_append_eq_append_conv_if_disj"]

val list_decomposition_witnesses =
  classified "list decomposition witnesses"
    ("the residual needs an existential witness splitting a list "
     ^ "at a member")
    ["list_L8673_these_set_code"]

(* src/HOL/List.thy:6138 @ f7e02b7e.  Four causes were found here and
   three are fixed: a fact frozen at a type the goal never states it
   at, an order premise the search could not ask for, and a cited
   implication that reached the search only as an assumption.  What is
   left is measured rather than inherited -- the recipe runs a live
   search with both of the method's citations in front of it,
   expansions=256 and no residual, and spends the budget.  The fourth
   cause read earlier, that Isabelle's one [inj_on] is spelled
   [source_inj_on] at this goal and [INJ _ _ UNIV] at the cited
   [source_map_inj_on], is refuted in both directions: restating the
   goal leaves it exactly where it was, and restating the fact costs
   [list_L1193_inj_on_map_eq_map] and [list_L1213_inj_on_mapI], whose
   own hypotheses are written the transparent way the ambient INJ
   unfolding reads. *)
val over_budget_with_no_residual =
  classified "over budget with no residual"
    ("the recipe runs a live search with both of the method's "
     ^ "citations in front of it -- expansions=256, no residual -- "
     ^ "and spends the budget; three separate causes of this goal's "
     ^ "failure have been fixed and the fourth is not the two "
     ^ "spellings of the cited injectivity premise, which is measured "
     ^ "and refuted in both directions")
    ["list_L6138_map_sorted_distinct_set_unique"]

(* src/HOL/List.thy:9013,6761 @ f7e02b7e.  [list_all_transfer] is
   proved [using list.pred_transfer by blast], and [list.pred_transfer]
   is the [list] BNF's own predicator transfer rule: the two statements
   are the same one, so the source proof is the citation and nothing
   else.  [list_L6761] reaches the same place by the other road -- its
   citation is represented, as [source_strict_sorted_equal_unique], and
   is the goal word for word, so rule A1 withholds it and the recipe is
   authored without it.  [Uniq_def], the method's other citation, is
   inlined and carries no fact. *)
val the_only_citation_states_the_goal =
  classified "the only citation states the goal"
    ("the source method's only fact-bearing citation is the goal's "
     ^ "own statement -- recorded unrepresented by the name table, or "
     ^ "represented and withheld by rule A1 -- so the recipe reaches "
     ^ "the goal with the ambient context and nothing else.  What is "
     ^ "left is an induction and not a step any classical or simp "
     ^ "method takes: for [list_L9013] EVERY at two predicates across "
     ^ "a LIST_REL, and for [list_L6761] that two strictly sorted "
     ^ "listings of one set are equal")
    ["list_L9013_list_all_transfer", "list_L6761_anon_L6761"]

(* src/HOL/List.thy:6669,6770,6847 @ f7e02b7e.  The residual is stated
   on the translated [sorted_key_list_of_set], which is a sort of the
   set's elements in an arbitrary listing.  The source's facts about it
   are the locale lemmas of the fold that builds it -- its head is the
   least element, and it is empty exactly when the set is -- and HOL4
   has no constant of its own to state them on, so a sort at a set
   known only to be finite reduces nowhere.  L6770 was filed under a
   cardinality reading and is here on its residual: both halves of its
   iff are left, and what each turns on is
   [source_sorted_key_list_of_set le function domain = target], the
   same sort at the same kind of set. *)
val sorted_list_of_a_set =
  classified "sorted list of a set"
    ("the residual is a sort over a set's elements, which the source "
     ^ "reads through the locale lemmas of the fold that builds it "
     ^ "and HOL4 states on no constant of its own")
    ["list_L6669_sorted_key_list_of_set_eq_Nil_iff",
     "list_L6770_sorted_key_list_of_set_unique",
     "list_L6847_sorted_list_of_set_nonempty"]

(* src/HOL/List.thy:1838 @ f7e02b7e.  The source proof folds both
   filters back into [partition] through partition_filter1 and
   partition_filter2 and closes by reflexivity.  HOL4 has no constant
   the translation could name there, so the goal arrives with
   [partition] inlined as a lambda and the two citations resolve to
   nothing.  What is left equates FILTER at [\item. ~f item] with
   FILTER at [$~ o f]: the same function pointwise, in an argument
   position where neither is applied, so identifying them is an
   extensionality step.  Isabelle's own simp does not take it either --
   [filter (%x. ~ f x) xs = filter (Not o f) xs] fails under plain simp
   in Isabelle2025-2, measured 2026-09-18. *)
val a_composed_predicate_at_a_function_argument =
  classified "a composed predicate at a function argument"
    ("the residual equates FILTER at a negated lambda with FILTER at "
     ^ "the composition [$~ o f].  The two agree pointwise and stand "
     ^ "in an argument position where neither is applied, so they are "
     ^ "identified only by extensionality.  The source method never "
     ^ "meets the residual: its citations fold both filters back into "
     ^ "the [partition] the translation had to inline")
    ["list_L1838_partition_filter_conv"]

val indexing_through_list_constructors =
  classified "indexing through list constructors"
    ("the goal characterises a list operation by index.  The "
     ^ "simpset pushes EL through MAP, ZIP, LUPDATE, TAKE, DROP and "
     ^ "a cons, so what is left is a side condition on one of those "
     ^ "rules that the goal does not supply, or the index "
     ^ "characterisation itself, which neither simplification nor "
     ^ "search reduces")
    ["list_L3168_list_eq_iff_zip_eq",
     "list_L6487_nth_nth_transpose_sorted",
     "list_L6873_nth_sorted_list_of_set_greaterThanAtMost"]

(* src/HOL/Fun.thy:140-141,196-201 @ f7e02b7e.  Owner decision D-D13
   keeps the ambient unfolding, so this goal keeps a record. *)
val the_codomain_the_source_predicate_has_not =
  classified "the codomain the source predicate has not"
    ("Isabelle's [inj_on f A] carries no codomain and HOL4's "
     ^ "[INJ f s t] does, so the translation of the method's own "
     ^ "cited [inj_on_nth] concludes [INJ f s UNIV] and does not "
     ^ "unify with a goal whose codomain is a real set.  The road "
     ^ "that would join them -- discharging the codomain obligation "
     ^ "separately and leaving the codomain-free injectivity "
     ^ "standing -- is closed by this layer's own ambient unfolding "
     ^ "of INJ, which dissolves the literal before any rule "
     ^ "concluding one is offered a redex.  Measured: the citation "
     ^ "never fires either way, and with the unfolding withheld and "
     ^ "the codomain discharged by an unsafe introduction the goal "
     ^ "closes in 0.046s.  The unfolding stays because Isabelle keeps "
     ^ "[inj_on] opaque while declaring specific facts about it "
     ^ "simp, and this layer put one blanket rewrite where that set "
     ^ "of facts stands")
    ["list_L3919_bij_betw_nth"]

(* What used to be one class saying only that the method reported no
   proof.  Each goal's residual was read and each names a different
   cause; [list_L7998_listrel_rtrancl_refl] left the class altogether,
   its citation now resolved as the source method instantiates it. *)

val the_cited_characterisation_has_no_counterpart =
  classified "the cited characterisation has no counterpart"
    ("every fact the source method names is one the name table "
     ^ "records as unrepresented, so the recipe reaches the goal with "
     ^ "the ambient context and nothing else: [nths_drop] cites "
     ^ "[drop_eq_nths], [nths_nths] and [atLeastLessThan_iff], and "
     ^ "the two lex goals cite [lexn_conv], which characterises "
     ^ "Isabelle's length-indexed [lexn] by a common prefix and a "
     ^ "related pair after it -- a constant HOL4 does not have, and "
     ^ "a reading of [LLEX] that [LLEX_EL_THM] states at an index "
     ^ "instead")
    ["list_L5409_nths_drop", "list_L7247_lex_conv",
     "list_L7321_lex_append_rightI"]

val a_set_relation_stated_by_its_graph =
  classified "a set relation stated by its graph"
    ("the method unfolds [rel_set_def], and HOL4's [SET_REL] is "
     ^ "stated the other way round -- as a set of pairs whose two "
     ^ "projections are the two sides -- so unfolding it leaves that "
     ^ "set to be built where Isabelle's unfolding leaves two bounded "
     ^ "quantifiers to be read off the cons rules")
    ["list_L8999_set_Cons_transfer"]

val an_injectivity_premise_no_ambient_fact_reaches =
  classified "an injectivity premise no ambient fact reaches"
    ("Isabelle discharges the cited [card_image]'s premise from its "
     ^ "ambient [inj_on_char_of_nat], String.thy:141, an atom its "
     ^ "simpset rewrites to T.  Both HOL4 counterparts state that "
     ^ "premise in a shape no ambient fact reaches: [CARD_IMAGE_INJ] "
     ^ "writes it out as a quantified implication, which the "
     ^ "condition solver discharges from an assumption but not from "
     ^ "a rewrite, and [INJ_CARD_IMAGE] states it as [INJ f s t] "
     ^ "whose [t] the left-hand side does not determine, so the "
     ^ "condition arrives existentially closed.  The shape is what "
     ^ "is missing and not the solver's strength: measured in "
     ^ "Isabelle 2026-09-20, its own simplifier leaves a conditional "
     ^ "rule unfired where the conditions stand as earlier conjuncts "
     ^ "of the antecedent -- in the membership spelling and in the "
     ^ "bound one alike -- and fires it once they stand as "
     ^ "assumptions, which is what HOL4's solver does here too")
    ["string_L178_card_UNIV_char"]

(* The earlier reading -- that the translation renders foldr as FOLDL
   over REVERSE -- was wrong: [source_foldr] is FOLDR.  The FOLDL over
   a REVERSE arrives from the cited [foldr_conv_fold], which is what
   Isabelle's own proofs rewrite with.  The reading after that -- that
   the append law was the goal and rule A1 withheld it -- was wrong
   too: the law the source route needs is [source_fold_append], which
   is ambient and stands in the recipe.  What stood between the two
   was the reversal the citation leaves around the append, which the
   seeded [rev_append] now moves, and [list_L3421_foldr_append] left
   the class with it.  What is left is a second cause the other two
   share. *)
val a_point_free_law_stated_applied =
  classified "a point-free law stated applied"
    ("Isabelle states [fold_map] and [fold_filter] at the function "
     ^ "level -- [fold (g o f)] and [fold (%x. if P x then f x else "
     ^ "id)] -- which is the spelling the goal's own right-hand side "
     ^ "carries, so the citation lands on it.  The translation states "
     ^ "both applied to the accumulator, so what the citation leaves "
     ^ "is that right-hand side against a lambda that agrees with it "
     ^ "pointwise: [\\value. g (f value)] against [g o f], and the "
     ^ "guarded step against [\\x. if P x then f x else I].  The "
     ^ "layer's extensionality step has already taken the equation "
     ^ "pointwise in the accumulator, and the pair that is left "
     ^ "stands in an argument position of the fold, where no "
     ^ "extensionality reaches it.  Unfolding the composition would "
     ^ "close the first, and neither system declares that unfolding: "
     ^ "Isabelle's own proofs cite [comp_def] by hand where they need "
     ^ "it, and this method does not, there being nothing left to "
     ^ "unfold once [fold_map] is stated point-free")
    ["list_L3427_foldr_map", "list_L3430_foldr_filter"]

val fold_against_a_set_aggregate =
  classified "fold against a set aggregate"
    ("the goal relates a set-valued aggregate to a fold over any list "
     ^ "with that set, and the residual still carries the aggregate: "
     ^ "nothing turns the hypothesis about every list into the "
     ^ "instance the goal needs")
    ["list_L3381_anon_L3381", "list_L3385_anon_L3385"]

(* [source_sorted] is now [source_sorted_wrt], and the ambient bridge
   has crossed: the residual below is stated on HOL4's own adjacent
   SORTED, with nothing of the all-pairs reading left in it.  So the
   class is no longer about the two readings at all -- it is what the
   engine cannot do with SORTED once it has it.  Two goals have left
   it: [list_L6761] is withholding its only citation and not a fact
   about SORTED at all, and [list_L6053] needs no induction, which the
   note used to claim of all three. *)
val sortedness_beyond_the_bridge =
  classified "sortedness beyond the bridge"
    ("the residual is stated on HOL4's adjacent SORTED, so the "
     ^ "ambient bridge has crossed; what is left is SORTED's closure "
     ^ "under a list operation, which needs an induction the search "
     ^ "does not perform")
    ["list_L6384_sorted_insort_insert_key"]

(* src/HOL/List.thy:6053 @ f7e02b7e.  Measured, not read off the
   residual's shape: the residual
   [right < LENGTH xs, left <= right, !l r. l < r ==> r < LENGTH xs ==>
    le xs[l] xs[r], WeakLinearOrder le |- le xs[left] xs[right]]
   is left open by the assigned tactic, and closes in 0.102s once
   [left < right \/ left = right] is handed over as an assumption.
   Reflexivity is already reachable from the order premise (closed in
   0.006s), and the split is provable where it is the goal (0.010s), so
   neither half is the obstruction -- what is missing is the step that
   takes a [<=] standing in the assumptions to the disjunction.  The
   source method gets it from the cited [nat_less_le], which rewrites
   the quantified premise's [<] into [<= /\ <>]; the name table pins
   that citation engine-native, and the ambient simpset leaves [a < b]
   unchanged. *)
val the_order_split_the_citation_supplies =
  classified "the order split the citation supplies"
    ("the residual needs a [<=] assumption split into its strict and "
     ^ "equal cases; handed that disjunction the assigned tactic "
     ^ "closes the goal in 0.102s, and both halves are reachable on "
     ^ "their own.  Isabelle gets the split from the cited "
     ^ "[nat_less_le], which the name table records as engine-native, "
     ^ "and nothing in the ambient layer performs it")
    ["list_L6053_sorted_iff_nth_mono"]

val numeral_against_Suc =
  classified "numeral against Suc"
    ("two mismatches block this residual and each was measured to "
     ^ "block on its own.  The successor is in both spellings -- "
     ^ "[index + 1] in the cited fact and [SUC index] in the goal -- "
     ^ "and neither is HOL4's normal form for the other, where "
     ^ "Isabelle's arithmetic simp takes [1 + n] to [Suc n] and the "
     ^ "two meet; and the fact is stated of [rotate 1] where the goal "
     ^ "states [rotate1], which Isabelle bridges from its own "
     ^ "[rotate_Suc] and [rotate0], both simp at List.thy:5135,5138, "
     ^ "while the translation defines [source_rotate] through FUNPOW "
     ^ "and declares neither clause.  Supplying both -- the "
     ^ "definition and [ADD1] -- closes the residual in 0.014s, and "
     ^ "supplying either alone leaves the other standing.  The second "
     ^ "is a declaration on a translation constant, so it is corpus "
     ^ "work rather than engine work")
    ["list_L5301_nth_rotate1"]

(* Two of this class's goals were not in it: their citation is a
   definition Isabelle states unapplied -- [curry_def] at
   Product_Type.thy:781, [gr0_conv_Suc] at Nat.thy:714 -- which the
   name table answered with HOL4's applied equation, and the applied
   equation is the goal.  Both are stated in the translation as the
   source states them and both close.  The rest are the real thing:
   the fact the source method names is, in Isabelle too, the goal's own
   statement.  [list_L1921_in_set_conv_nth] is the one that is neither.
   Isabelle's [set_conv_nth] is a set equation, and its own
   [in_set_conv_nth] follows by rewriting [set xs] inside [x : set xs].
   The translation renders list membership as MEM, which is HOL4's
   normal form and what every other goal is stated in, so a goal that
   says MEM carries no [set xs] for that equation to rewrite; the
   citation is therefore carried in the MEM spelling, where it is the
   goal.  Recovering the source's route means spelling the corpus's
   list membership through [IN set] instead, which is every list goal's
   statement and not one goal's fix. *)
val characterisation_is_the_goal =
  classified "characterisation is the goal"
    ("the HOL4 theorem that is this goal -- the one the Isabelle "
     ^ "method cites, or one the simpset carries, or one a seed file "
     ^ "declares -- is withheld as the goal's own statement, by A1 or "
     ^ "by the recipe's self-citation filter, up to the orientation "
     ^ "of an equation or an equivalence or the unfolding of a "
     ^ "constant the translation introduces, and the assigned tactic "
     ^ "has no second route")
    ["list_L1921_in_set_conv_nth",
     "list_L6444_stable_sort_key_sort_key",
     "list_L8167_list_all_iff",
     "list_L8642_image_set", "list_L8660_card_set",
     "list_L8683_can_select_set_list_ex1",
     "option_L361_equal_None_code_unfold_1", "string_L728_anon_L728"]

val integer_interval_emptiness =
  classified "integer interval emptiness"
    ("the residual is [j < i ==> source_upto i j = []], which the "
     ^ "source method does not name and no simpset carries")
    ["list_L3695_upto_aux_rec"]

(* The successor clause has been seeded -- arithmetic states it as
   FUNPOW_SUC and declared it to no simpset, where the source's is a
   primrec equation and simp -- and [list_L5194_rotate_Suc] left the
   class with it.  What remains is the other half, and it is not a
   declaration but a statement: HOL4 has no single-step swap under any
   name, and the name table's [FUNPOW_COMM] is the commuting law
   between two iterations, which the goal's shape does not meet. *)
val rotation_by_iteration =
  classified "rotation by iteration"
    ("the iteration unfolds and the residual is a FUNPOW law HOL4 "
     ^ "does not have where the source does: the swap, which HOL4 "
     ^ "states only as the commuting law between two iterations and "
     ^ "never as the single step the goal carries")
    ["list_L5207_rotate1_rotate_swap"]

val decision_procedure_scope =
  classified "decision procedure scope"
    ("the goal is outside what the HOL4 counterpart of the cited "
     ^ "decision procedure decides: the cited facts are supplied and "
     ^ "the procedure rejects what is left of the goal")
    ["list_L6315_sort_replicate",
     "list_L6835_sorted_list_of_set_lessThan_Suc"]

val definitional_unfolding_stops_short =
  classified "definitional unfolding stops short"
    ("the cited definition unfolds one constant and nothing "
     ^ "reduces what it exposes")
    ["list_L5441_distinct_set_subseqs", "list_L8701_trancl_set_ntrancl"]

(* What used to be one class saying the residual was an INJ, SURJ or
   BIJ claim the tactic does not decompose.  Two of the three are not
   that, and the third is a constant the translation has to inline;
   each residual was read on 2026-09-20 and each names its own cause. *)

val the_mapped_distinctness_equivalence =
  classified "the mapped distinctness equivalence"
    ("Isabelle's [distinct_map] is the equivalence whose left side is "
     ^ "this goal's antecedent, so rewriting the antecedent closes "
     ^ "it.  The name table answers the citation with HOL4's two "
     ^ "readings: [ALL_DISTINCT_MAP], which is this goal and A1 "
     ^ "withholds, and [ALL_DISTINCT_MAP_INJ], whose premise is "
     ^ "injectivity everywhere where Isabelle's is injectivity on the "
     ^ "list's own elements.  Nothing decomposes the antecedent, and "
     ^ "the tactic returns it beside the goal in 0.156s without "
     ^ "searching")
    ["list_L6690_distinct_if_distinct_map"]

(* Two classes left the accounting when the surjectivity bridge
   landed: "the surjective half is an atom"
   ([product_type_L1329_bij_betw_map_prod]) and "the inlined swap"
   ([product_type_L988_bij_swap]).  Both named the same atom -- HOL4
   states SURJ where the source states an image equation -- and the
   second is now closed where Isabelle's own [auto] on the inlined
   form is not. *)

(* src/HOL/Map.thy:363 @ f7e02b7e.  Isabelle closes this one from its
   simpset, by [map_add_find_right], and that declaration's translated
   statement is this goal once [map_le] is unfolded -- two source facts
   onto one HOL4 theorem.  The measurement withholds a rule that states
   the goal it is offered on, so the goal runs without the fact the
   source proof read. *)
val the_ambient_rule_is_the_goal =
  classified "the ambient rule is the goal"
    ("Isabelle reads this from its simpset as map_add_find_right, "
     ^ "whose translated statement is the goal, so the measurement "
     ^ "withholds it here")
    ["map_L887_map_le_map_add"]

(* src/HOL/Map.thy:810 @ f7e02b7e.  [map_add_comm] reaches the goal as a
   rewrite now.  It goes in as a fact, so it stands as a universal
   assumption with a domain-disjointness condition, and the simplifier
   the search runs before each unsafe step instantiates it at the redex
   that condition pins and commutes there.  That step is the one the
   source proof needs: the membership branch it serves -- a value held
   by one map read out of the sum -- closes outright once the commuted
   sum is in reach of the ambient [map_add_find_right].  What is left is
   the set equality the goal is stated as, on which the recipe still
   runs out a budget ten times the measurement's. *)
val map_sum_commuted_under_a_fact =
  classified "map sum commuted under a fact"
    ("the commuting fact now reaches its redex and the membership "
     ^ "branch it serves closes, and the set equality around it still "
     ^ "runs out a budget ten times the measurement's")
    ["map_L810_graph_map_add"]

(* src/HOL/Option.thy:317,320 @ f7e02b7e.  Both goals are set
   equalities about [these], and taken apart into memberships they
   leave a residual whose missing step is the goal's own negation:
   [x' = NONE] is atomic, and what the claset derived about an option
   is an introduction on [!y. x <> SOME y] and a destruction from it,
   neither of which meets the goal until it is negated.  Isabelle's
   [auto] fails on that same subgoal (measured 2026-09-19) and never
   reaches it, closing the source lemma from [these_def] instead: the
   divergence is upstream of the residual, in how the set equality is
   taken apart, and not a rule the claset lacks. *)
val these_set_equality_route =
  classified "these set equality route"
    ("the set equality is taken apart into memberships and the "
     ^ "residual needs the goal's own negation, which the rules the "
     ^ "claset derived about an option meet only once it is negated; "
     ^ "Isabelle closes the lemma from these_def without reaching it")
    ["option_L317_these_empty_eq", "option_L320_these_not_empty_eq"]

val character_arithmetic =
  classified "character arithmetic"
    ("the residual is modular arithmetic on character codes; "
     ^ "HOL4's char is a numeral typedef and the source proof "
     ^ "reasons about bits")
    ["string_L344_char_of_integer_code",
     "string_L60_char_of_take_bit_eq"]

val sigma_and_times_rule_forms =
  classified "Sigma and Times rule forms"
    ("the goal equates a set written as a paired abstraction with one "
     ^ "written another way -- a Sigma on one side, a choice over the "
     ^ "abstraction on the other -- and nothing relates the two "
     ^ "spellings")
    ["product_type_L1088_Collect_case_prod_Sigma",
     "product_type_L688_The_split_eq"]

(* Five goals the corrected circularity guard newly withholds a rule
   from, all in the [characterisation is the goal] class above and
   dated to the measurement that found them.  Four are one conjunct of
   a conjunctive rule -- [listTheory.ZIP], [EVERY_DEF], [EXISTS_DEF]
   and the ambient [in_measures] -- and the simpset splits each into a
   rewrite that is the goal.  The fifth is [listTheory.SHORTLEX_NIL2],
   which is the goal once the translation of [lenlex] is unfolded; the
   guard used to compare a rule's conclusion against the goal with the
   goal's quantifier prefix still on, so neither reading matched.

   Five have left the class since, none of them because the guard
   released the rule: a withheld rule leaves the goal to the rest of
   the layer, and each of the five is reached by a second route.
   [list_L1851_nth_Cons_Suc] withholds one conjunct of [listTheory.EL]
   and is reached by the seeded EL_CONS, which takes a cons at an index
   known only to be non-zero, as the successor in the goal is.  The two
   [LIST_REL_NIL] readings, [list_L3014_list_all2_Nil] and
   [list_L3017_list_all2_Nil2], are reached once the seeded one-sided
   nil equations for ZIP empty the [set (zip xs ys)] the cited
   [list_all2_iff] expands to.  [list_L7775_in_measures_2] withholds
   one conjunct of the ambient [in_measures] and is reached by the
   citation it names: [measures] is now defined as the source defines
   it, and unfolding it leaves a pair of conses in the equal-length
   lexicographic order the ambient [Cons_in_lex] takes apart.
   [list_L7300_Nil_lenlex_iff2] no longer meets [SHORTLEX_NIL2] at
   all: [lenlex] is now the source's composite too, and unfolding it
   leaves the nil in the equal-length order the ambient
   [Nil2_notin_lex] rejects.

   Two more have left it, and these two because the second route now
   exists.  [list_L8187_list_all_Cons_iff] and
   [list_L8195_list_ex_Cons_iff] withhold one conjunct of [EVERY_DEF]
   and of [EXISTS_DEF], and what the cited [list_all_iff] /
   [list_ex_iff] leave is a bounded quantifier over a cons.  Isabelle
   reads [set (x # xs)] as an insert, so the insert clauses of
   [ball_simps] and [bex_simps], both simp there, split the head off
   above the membership; HOL4 spells the membership as MEM, whose own
   cons equation is simp too, and outermost-first the quantifier
   descends into that instead.  The seeded list reading of those
   clauses is stated on the quantifier, so it is reached first. *)
val a_reading_of_the_characterisation_is_the_goal =
  map
    (fn id =>
      {id = id, cause = benchLib.EngineLimitation, date = "2026-09-03",
       note =
         "a reading of the characterisation is the goal: the HOL4 " ^
         "rule that reaches this goal states it as one conjunct of a " ^
         "conjunction, and A1 withholds the conjunction; the " ^
         "assigned tactic has no second route"} : benchLib.shortfall)
    ["list_L2740_zip_Cons_Cons"]

val execution : benchLib.shortfall list =
  prefix_from_its_indices @
  transpose_column_lengths @
  emptiness_from_disjoint_membership @
  list_decomposition_witnesses @
  over_budget_with_no_residual @
  the_only_citation_states_the_goal @
  sorted_list_of_a_set @
  a_composed_predicate_at_a_function_argument @
  indexing_through_list_constructors @
  the_codomain_the_source_predicate_has_not @
  the_cited_characterisation_has_no_counterpart @
  a_set_relation_stated_by_its_graph @
  an_injectivity_premise_no_ambient_fact_reaches @
  a_point_free_law_stated_applied @
  fold_against_a_set_aggregate @
  sortedness_beyond_the_bridge @
  the_order_split_the_citation_supplies @
  numeral_against_Suc @
  characterisation_is_the_goal @
  integer_interval_emptiness @
  rotation_by_iteration @
  decision_procedure_scope @
  definitional_unfolding_stops_short @
  the_mapped_distinctness_equivalence @
  the_ambient_rule_is_the_goal @
  map_sum_commuted_under_a_fact @
  these_set_equality_route @
  character_arithmetic @
  sigma_and_times_rule_forms @
  a_reading_of_the_characterisation_is_the_goal

end
