# Automation benchmark results

## What this report measures

Each benchmark entry contains a HOL4 theorem statement, the Isabelle method used for the corresponding source result, and the HOL4 tactic chosen as that method's closest counterpart. This report calls that HOL4 tactic the **assigned tactic**.

The assigned tactic and its arguments are derived from the recorded Isabelle method string rather than authored per goal, so a goal cannot be handed a fact its source proof did not name. One context is added on top of that: the definitions the translation introduces whose equations Isabelle's own simpset would carry, as rewrites, and only to the methods that consult a simpset. This stands in for the ambient simpset an Isabelle method reads without naming it. Which definitions those are is recorded per constant against the Isabelle source line that introduces it: a `fun`, a `primrec`, a datatype's selectors and predicator, and a `definition` whose characterisation Isabelle separately declares simp are in; a plain `definition` is out. A few results Isabelle declares `simp` or `iff` about a constant whose definition it withholds are carried alongside, each citing the declaration it transplants. Two Isabelle facts can translate onto one HOL4 theorem, so one of them can be a corpus goal's statement; the measurement then withholds it on that goal, as it withholds a citation that states its goal, and the selftest checks that it does. A second, smaller half stands in for the ambient claset: the rules Isabelle declares `intro`, `elim` or `dest` about a constant whose definition it withholds, carried with the safety Isabelle gives them and only to the methods that consult a claset, which is a different set -- `simp` reads none.

Both halves are cut by Isabelle's theory order. Isabelle reads a theory in order and sees only the theories it imports, so a result declared below a proof, or in a theory that imports the proof's rather than the other way round, was not in that proof's simpset or claset: `Pow_Compl` is proved at `Set.thy:1610` and knows nothing of `Sigma`, which `Product_Type.thy` introduces. The cut reads the goal's mined source line and nothing about its statement, so the context is one set for the whole corpus rather than a per-goal choice. It is a formality on neither side: an out-of-scope rewrite is a fact the source proof did not have, and an out-of-scope classical rule is search the source proof was not paying for -- given the two `Sigma` rules, `Pow_Compl`'s tableau goes from 88 branches to 1181 and the proof is lost.

The comparison data was mined from Isabelle/HOL commit `f7e02b7e`. Each in-repository benchmark entry records its source file, line, method, and commit. The report was generated on 2026-10-03 with a 30-second limit for each tactic attempt. The limit is an asynchronous interrupt, so a goal can overrun it by the time its search takes to reach an interruptible point; the times below are wall-clock and record the overrun where it happened.

## Scope

The corpus covers six Isabelle theories at one commit -- `Set.thy`, `List.thy`, `Product_Type.thy`, `Map.thy`, `Option.thy` and `String.thy` -- plus a handful of `ex/` files. That is Isabelle's base library, not Isabelle/HOL. What follows says what these HOL4 tactics do on those goals at that budget. It is not a claim about Isabelle automation in general, and it is not a claim about goals outside the six theories.

## Facts the measurement withheld

Two distinct Isabelle facts can translate onto one HOL4 theorem, and a proof citing one of them then reads as if it assumed what it proves. The citation is dropped rather than the goal, so HOL4 is asked to close the goal without a fact the Isabelle proof had. That can only under-credit HOL4, and it is named here rather than left for the reader to discover.

- `set_L105_set_eq_iff (pred_set$EXTENSION)`
- `set_L563_empty_def (pred_set$EMPTY_DEF)`
- `set_L595_UNIV_def (pred_set$UNIV_DEF)`
- `list_L1921_in_set_conv_nth (parityTranslation$source_set_conv_nth)`
- `list_L8167_list_all_iff (list$EVERY_MEM)`
- `list_L8660_card_set (list$CARD_LIST_TO_SET_EQN[symmetric])`
- `list_L6444_stable_sort_key_sort_key (parityTranslation$source_sort_key_stable)`
- `list_L6690_distinct_if_distinct_map (list$ALL_DISTINCT_MAP)`
- `list_L6761_anon_L6761 (parityTranslation$source_strict_sorted_equal_unique)`
- `list_L8683_can_select_set_list_ex1 (parityTranslation$source_list_ex1_def)`
- `list_L7806_not_Nil_listrel1 (parityTranslation$source_not_Nil_listrel1)`
- `list_L7809_not_listrel1_Nil (parityTranslation$source_not_listrel1_Nil)`
- `list_L7775_in_measures_1 (parityTranslation$source_in_measures)`
- `list_L7775_in_measures_2 (parityTranslation$source_in_measures)`
- `list_L7283_Nil_notin_lex (parityTranslation$source_Nil_notin_lex)`
- `list_L7286_Nil2_notin_lex (parityTranslation$source_Nil2_notin_lex)`
- `list_L7300_Nil_lenlex_iff1 (parityTranslation$source_Nil_lenlex_iff1)`
- `list_L7300_Nil_lenlex_iff2 (parityTranslation$source_Nil_lenlex_iff2)`
- `map_L877_map_le_refl (parityTranslation$source_map_le_refl)`
- `map_L887_map_le_map_add (parityTranslation$source_map_add_find_right, parityTranslation$source_map_le_map_add)`
- `string_L728_anon_L728 (source_Literal_prime_def)`
- `product_type_L1028_SigmaI (parityTranslation$source_SigmaI)`
- `product_type_L1031_SigmaE (parityTranslation$source_SigmaE)`
- `product_type_L1073_mem_Sigma_iff (parityTranslation$source_mem_Sigma_iff)`

## Facts the translation does not render

An Isabelle proof can name a fact HOL4 states nowhere -- neither in a library nor in the translation theory.  The recipe has nothing to supply for such a citation, so the goal below is measured without it. As above, that can only under-credit HOL4, and the goals are named rather than left implicit in a shortfall count.

- `set_L651_Pow_not_empty (Pow_top)`
- `list_L1838_partition_filter_conv (partition_filter2[symmetric], partition_filter1[symmetric])`
- `list_L9013_list_all_transfer (list.pred_transfer)`
- `list_L5409_nths_drop (drop_eq_nths, nths_nths, atLeastLessThan_iff[symmetric])`
- `list_L6487_nth_nth_transpose_sorted (filter_equals_takeWhile_sorted_rev[OF sorted, of i])`
- `list_L6669_sorted_key_list_of_set_eq_Nil_iff (fold_insort_key.remove)`
- `list_L6770_sorted_key_list_of_set_unique (idem_if_sorted_distinct)`
- `list_L6873_nth_sorted_list_of_set_greaterThanAtMost (nth_sorted_list_of_set_greaterThanLessThan[of n "Suc j" i], greaterThanLessThan_eq)`
- `list_L7247_lex_conv (lexn_conv)`
- `list_L7321_lex_append_rightI (lexn_conv)`
- `map_L308_dom_map_option_comp (dom_map_option[of "\<lambda>_. g" m])`
- `string_L60_char_of_take_bit_eq (bit_take_bit_iff)`
- `string_L135_char_of_nat (drop_bit_of_nat, bit_simps, possible_bit_def)`
- `string_L344_char_of_integer_code (bit_iff_odd_drop_bit, drop_bit_eq_div)`
- `product_type_L1226_inj_apfst (inj_on_apfst[of f UNIV])`
- `product_type_L1232_inj_apsnd (inj_on_apsnd[of f UNIV])`

## Source accounting

Source mining identified 1,036 relevant Isabelle results. Seven pairs translated to the same HOL4 statement except for bound variable names, so they are tested once. This leaves 1,029 distinct source-derived results:

- 1027 are executable HOL4 benchmark goals.
- 2 could not be translated faithfully and are listed by identifier and reason in the benchmark files.
- 0 source results are missing from both groups.

The selftest checks this accounting in both directions. An unexpected failure is an error, but so is an expected failure that starts succeeding without its record being updated.

## Results from the assigned tactics

**Executable goals** is the number of runnable HOL4 statements. **Solved by assigned tactic** counts statements proved by the HOL4 counterpart selected for their Isabelle method, with the ambient context described above. **Routine selftest goals** is a fixed, explicitly marked subset run when `HOLSELFTESTLEVEL=1`; it is not a random sample. At level 2 or higher, all executable goals run.

A **family** is a subject-area group:

- **Classical** contains propositional and first-order logic.
- **Sets** contains set and relation reasoning.
- **List/map** contains lists, finite maps, options, strings, and product types.
- **Linarith** contains linear arithmetic over natural numbers, integers, real numbers, and rational numbers.

| Family | Executable goals | Solved by assigned tactic | Routine selftest goals |
|---|---:|---:|---:|
| Classical | 25 | 25 | 4 |
| Sets | 353 | 345 | 4 |
| List/map | 602 | 551 | 5 |
| Linarith | 47 | 47 | 4 |
| **Total** | **1027** | **968** | **17** |

## Cost of the solutions

A solve at 28 seconds is not the same result as a solve in milliseconds, and the count above cannot tell them apart. The columns below split the solved goals by elapsed time and report the search work the engines metered while solving them: node expansions, tableau branches, inferences and rule applications, summed. Zero search work means the goal was closed by rewriting rather than by search. The time is the tactic's alone: deriving the goal's invocation-local simpset is the harness reading its own declarations, and it happens before the clock starts. Goals that overran the budget are counted as limitations, not here, so this distribution is bounded by the budget by construction.

| Family | Solved | < 0.1 s | 0.1-1 s | 1-10 s | > 10 s | Slowest | Median search work | Largest search work |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Classical | 25 | 22 | 2 | 1 | 0 | 1.0 | 33 | 516 |
| Sets | 345 | 305 | 29 | 11 | 0 | 5.6 | 0 | 1813 |
| List/map | 551 | 407 | 128 | 15 | 1 | 13.6 | 0 | 454 |
| Linarith | 47 | 44 | 2 | 1 | 0 | 1.4 | 0 | 0 |
| **Total** | **968** | **778** | **161** | **28** | **1** | **13.6** | **0** | **1813** |

## Documented results not solved by the assigned tactic

- **Accepted scope exclusions** are executable goals deliberately outside the supported tactic scope, with a recorded reason.
- **Assigned-tactic limitations** are executable goals for which the assigned tactic failed or exceeded 30 seconds. Each one has a dated record naming its root cause, in `benchmarks/benchSetShortfalls.sml` or `benchmarks/benchLibraryShortfalls.sml`.
- **Unavailable translations** are source results that could not be represented faithfully as HOL4 goals. They are not included in the executable-goal count.
- **Unaccounted source results** would be source results that are neither executable nor documented as unavailable. This number must remain zero.

| Family | Accepted scope exclusions | Assigned-tactic limitations | Unavailable translations | Unaccounted source results |
|---|---:|---:|---:|---:|
| Classical | 0 | 0 | 0 | 0 |
| Sets | 0 | 8 | 0 | 0 |
| List/map | 0 | 51 | 2 | 0 |
| Linarith | 0 | 0 | 0 | 0 |
| **Total** | **0** | **59** | **2** | **0** |

For every family, executable goals equal assigned-tactic solutions plus accepted scope exclusions plus assigned-tactic limitations.

## Goals another tactic would have closed

The exhaustive run also tries three general-purpose HOL4 tactics on every goal whose recipe does not already use them. A goal is counted below when that tactic closed it and the assigned tactic did not, so each column measures what the method-to-tactic mapping cost rather than what HOL4 cannot do. The columns overlap one another and are disjoint from the solved count. They are not strength scores: a tactic is never counted on a goal it was assigned. They do not affect whether the benchmark selftest passes.

| Family | `AUTO_TAC` | `BLAST_TAC` | `AESOP_TAC` |
|---|---:|---:|---:|
| Classical | 0 | 0 | 0 |
| Sets | 0 | 0 | 1 |
| List/map | 2 | 0 | 2 |
| Linarith | 0 | 0 | 0 |
| **Total** | **2** | **0** | **3** |

## Seed-rule safety check

A rule is classified as **safe** when applying it cannot discard a possible proof of the goal. The automated seed-rule check proves the required reverse direction for every such rule. It currently passes with no exceptions.

## Reproducing the report

From `src/auto/benchmarks/`:

```sh
Holmake
./selftest.exe
HOLSELFTESTLEVEL=2 ./selftest.exe
./genparity.exe
```

The first selftest command runs the fixed routine subset. The second runs every executable goal and the other-tactic observations. The final command regenerates `../PARITY.md`.
