# Automation generalization evidence

The local selftests exercise the public tactic paths as well as the
underlying engine cursors. This table names representative independent
checks; it is not a solved-goal score.

| Scenario | Regression observation |
| --- | --- |
| Bound-name and carrier changes | `rules/selftest.sml` checks a rename/carrier matrix, fixed support, and two schematic citations. |
| Redundant forward candidates | `aesop/selftest.sml` puts a useful consequence after more than 200 redundant candidates, then compares small resumed scans with one funded run. |
| New applications and contexts | `classical/selftest.sml` checks membership/application crossings, interleaved explicit contexts, and interrupted replay. |
| Normalization bridges | `clasimp/selftest.sml` uses independently defined predicates for a tagged rule whose premise changes normal form, and reports a typed limit for cyclic rewrites. |
| Child-first migration | `clasimp/selftest.sml` runs the same subject rewrite with plain `[iff]` and `[iff_bottom_up]` declarations under the opt-in policy; both close after the child rewrite. The ordinary simplifier test still distinguishes their priorities. |
| Head preservation and seeds | `seeds/selftest.sml` uses eta-expanded interval terms and an independently defined `INJ` client predicate; a separate client datatype and relation exercise temporary declarations. |
| Bounded FORCE turns | `clasimp/selftest.sml` compares the admitted first-best expansions under one-unit and large slices on the same partial-map proof. `classical/selftest.sml` resumes depth search and pending kernel replay under one budget. |
| FORCE scheduling | `clasimp/selftest.sml` drives the production round-robin loop with scripted yielding, proving and exhausting engines; each engine is the sole finisher in one case, and a shared three-application limit reaches all three before propagation. |
| Resumed tableau turns | `blast/selftest.sml` compares small application slices with one funded fixed-depth run, interleaves another search while a live owned trail is suspended, rejects the first proof to force backtracking, and validates a resumed theorem in an explicit context. |
| Renamed arithmetic declarations | `linarith/instances/selftest.sml` registers fresh names for integer addition and order, derives their laws from the existing theorem kit, and closes an additive inequality the ordinary instance declines. |
| Nested simplifier budgets | `clasimp/selftest.sml` proves arithmetic and order chains through public `CLARSIMP_TAC_BUDGETED`, then checks that a zero candidate allowance reports a typed limit. The direct reducer tests in `linarith/selftest.sml` and `order/selftest.sml` check the same behavior inside their own fragments. |
| Independent arithmetic carrier | `linarith/instances/selftest.sml` defines a fresh `client_integer` datatype, proves its addition and order kit from integer laws, and closes an additive inequality only after registering that instance. Its AC fallback also checks certified cancellation replay. |
| Safe tagged rule transport | `clasimp/selftest.sml` derives a safe introduction rule whose conclusion reaches the goal only after an invocation rewrite changes its normal form. |
| Persistent claset transport | `clasimp/selftest.sml` uses an explicit base-claset destruction rule through `CS_AUTO_TAC` and scoped public `AUTO_TAC`, and a safe introduction rule through `CS_CLARSIMP_TAC`. Each needs a supplied rewrite before the rule view reaches the goal; a polymorphic rule is checked at both `num` and `bool`. |
| Reloaded persistent transport | `clasimp/theory_tests/transportPersistentBaseScript.sml` declares a safe destruction rule; its child theory closes the differently spelled goal with public `AUTO_TAC` and a supplied bridge rewrite. |
| Contextual FORCE transport | `clasimp/selftest.sml` keeps only FORCE's best-first leg and closes a rule/goal spelling mismatch after the ordinary search exhausts. |
| Atomic FORCE normalization | Fresh opaque rules make a simplification wrapper exceed a small resumable slice. The wrapper runs once and reconstructs the exact theorem; a separate invocation-limit check still reports `LimitReached`. |
| Compatible partial type matches | Three fresh polymorphic predicates exercise disjoint matches, competing carriers and renamed binders. Existing ordered partial instances remain, followed only by distinct maximal compatible joins; a zero candidate allowance propagates. |
| Rule-derived abstraction positions | Fresh consumer constants exercise generic abstraction arguments at different positions. Their rule-derived policy preserves those arguments, while ordinary eta contraction and unrelated positions retain their previous behavior. |
| Supplied rewrite precedence | Fresh rules exercise immediate ambient converses, sibling conjuncts, conditional supplied rules, Once/Ntimes consumption, excluded sources and longer cycles. Only unconditional immediate ambient converses are suspended; longer cycles retain typed limits. |

The following temporary source ablations were run, then removed:

| Removed mechanism | Designated public failure |
| --- | --- |
| Fresh specialization before fixed-variable classification | `bound-variable spelling preserves fact type instances` failed in rules when specialization reused binder names and the resulting variables were classified as fixed. The rename/carrier matrix passed after restoration. |
| Safe consumers retain a literal implication | `the conditional citation does not add unsafe CLARSIMP search` failed when `SafeFacts` compiled the implication as a search rule and withheld its assumption. |
| Unbounded raw forward enumeration | `forward search reaches useful candidates through known results` failed when the shared forward cursor stopped after 200 raw candidates. A cap after duplicate filtering left that public proof green but broke `budgeted Aesop resumes a safe forward candidate scan`; it was not counted as evidence for E3. |
| Certified transport of unsafe tagged rules | `certified tagged rule view crosses an invocation normal form` failed in clasimp. |
| Currying a normalized conjunctive premise | `an INJ client rule survives the seed's definition normal form` failed in seeds. |
| Retaining FORCE's first-best session after a turn | `FORCE preserves first-best expansions across small turns` failed in clasimp. |
| Advancing after a yielded FORCE turn | `FORCE scheduler gives yielding engines one turn per round` failed when a yield immediately retried the same engine. |
| Transporting safe tagged rules | `safe tagged introduction retains its role after transport` failed in clasimp when safe transport was disabled. |
| Retaining the tableau continuation | `resumed tableau retains its fixed-depth work and proof` failed when yielded turns restarted the fixed-depth run. |
| Selecting persistent claset rules for transport | `persistent destruction rule crosses a supplied normal form` failed through public `AUTO_TAC` when only invocation markers were selected; the invocation tagged-rule control still passed. |
| Contextual FORCE's view fallback | `contextual FORCE uses a persistent rule's certified view` failed when that entry point passed no persistent candidates to the shared fallback. |
| Certified AC fallback reflexivity | `a new arithmetic carrier uses its registered theorem kit` failed with `EQT_ELIM` when the shared fallback left equal canonical forms as an unevaluated equality. |
| Budgeted arithmetic reducer | `CLARSIMP charges nested arithmetic to its invocation` failed when the reducer called the legacy cached, unbudgeted procedure. |
| Budgeted order reducer | `CLARSIMP charges nested order to its invocation` failed when its reducer selected the unbudgeted graph search. |

The restored rules, classical, clasimp, linarith instances and seeds local
selftests pass. The ordered `upto-auto` gate and `bin/build -F -t` passed
after the nested arithmetic and order budget integration, including the
benchmark harness, theory tests, full distribution and generated
documentation.

Tableau now retains its mutable search frontier at bounded turns. A cutoff
during initial translation restarts that preparation, and a cutoff within
one search step can replay charged work inside that step. Invocation safe
rule transport retains its declared role only when its safe class is
unchanged and no new theorem hypothesis is introduced. Persistent claset
rules now use the same certified view checks when a tactic leaves work open.
The independent arithmetic carrier uses its own type and operations; its
laws are proved from integer arithmetic, then consumed through the public
instance registry and tactic without generic dispatch on its names.

When arithmetic reduction joined the invocation budget, the former
100,000-unit default stopped the seed suite's finite negative INJ check.
The legacy and budgeted reducers gave the same success/failure answers on
its arithmetic atoms; the difference was counting nested proof work.
The default is now 1,000,000 normalization units, and explicit budgeted
entry points can still request smaller limits. The budgeted reducer uses
an invocation-local RCACHE so arithmetic context components, negative
answers and dynamic `[arith]` facts follow the legacy proof path while
cache misses charge the invocation.

The deferred public continuation additionally passes a fresh
public-rule argument fixture and a compound-goal quota fixture. The raw
pass closes one conjunct with a supplied Once/Ntimes rewrite; a remaining
conjunct needs an ambient rewrite view. Resuming the residual goals retains
the raw subproof and its spent quota. Retrying the original goal instead
fails the two positive cases, while a second occurrence cannot consume a
new Once allowance. The six mechanism ablations below use isolated module
copies with the same executable definitions as this integration, original
selftest dependencies and unchanged fresh regression fixtures. Each
variant covers all four benchmark families and 1027 goals.

| Removed mechanism | Independent semantic failure |
| --- | --- |
| F1 rewrite LHS views | The fresh proper-argument rule no longer fires; the compound Once/Ntimes fixture reports `false false true`, restored to `true true true` with the continuation. |
| F2 rule-derived abstraction policy | The fresh generic-abstraction fixture fails overall. Its seven scope controls still pass; the installed consumer loses its abstraction. |
| F3 atomic invocation charging | The fresh wrapper's invocation-limit test still passes, but the once-across-a-slice test fails. |
| F4 applicability before charging | The fresh non-arithmetic atom changes candidate usage instead of declining without charges. |
| F5 compatible maximal joins | The fresh partial-type fixture loses its maximal joined instance. |
| F6 immediate converse suspension | The indexed fresh-rule vector loses four positive converse cases; the restored vector is all true. |

These tests establish mechanisms independently of corpus names. Corpus
dependencies overlap: F1 compensates for F2 on CollectI/D, while F2 is
needed for several F1 views. F3 and F4 both support ran_map_upd_Some.
The ablated variants expose those interactions; the complete engine
retains all previously solved goals and recovers the 15 targets.
