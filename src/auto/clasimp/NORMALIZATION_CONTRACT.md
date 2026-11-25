# Automation normalization: G4 inventory and proposed contract

This records the G4 passes and their migration status. The owner approved
D2's opt-in child-first traversal and D5's abstraction policy.
Ordinary HOL4 simplification retains its existing traversal.
Extensional reading helpers inspect the effective compiled rewrites,
including installed aliases. Removed or excluded sources and declarations
discarded by the rewrite compiler do not advertise a reading. The root
extensional step stands down for a matching original or view, preserving
the equation for the invocation's simplifier.

## Current passes

| Pass | Input and output | Traversal, context and progress | Consumers |
| --- | --- | --- | --- |
| Opt-in child-first traversal (`Traverse`, `simpLib`) | A goal, invocation simpset and rewrite arguments become a goal simplified with local assumptions and selected invocation rules. | Congruences control descent and context. A certified eta contraction preserves function-argument heads before permitted children are visited; logical binders and positions consumed by generic abstraction rewrites are excluded. The rule-derived predicate also protects partial applications from the standard ETA fragment. Parent rewrites follow child descent, and the simplifier's assumption/conclusion fixpoint remains in use. This replaces the former `context_first` and `refining` outer pass in clasimp. One invocation policy carries its normalization charge and abstraction predicate through mutual simplification, rule transport, retries and search wrappers. Constant kernel identities and argument positions come from the actual compiled and supplied rewrites; exclusions and filters remove their positions. Ambient positions are cached, and supplied positions extend their persistent source tails. | `asm_full_simp`, `safe_asm_full_simp`, then AUTO, FORCE, CLARSIMP and their search wrappers. |
| Conditional witness subgoaler | A residual side condition and simplifier context theorems become a proved equality to `T`, or the traversal's unchanged reduction. | It recursively simplifies the condition, reverses existential miniscoping, then matches each condition against context assumptions while holding the condition's other variables and types fixed. It constructs the proof from those context theorems without taking an ambient context snapshot. Public tactics charge each candidate match and proof work to their invocation budget. It runs only in conditional rewriting. | The derived clasimp simpset, including tactics built on it. |
| Conditional congruence | A conditional's condition and branches become a simplified conditional. | The weak congruence simplifies the condition but leaves both branches alone to avoid recursive unfolding inside an inactive branch. The split fragment handles branch reasoning later. | Every tactic using the derived clasimp simpset. |
| `permutation_instances` | A supplied permutative theorem and current goal assumptions become bounded contextual rewrite instances. | Before the main simplification pass, it matches a redex in the current goal, discharges every condition from exact assumptions, checks support rigidity and term order, then bounds each rewrite by its redex occurrences. | Unsafe `asm_full_simp` and its AUTO/FORCE/search wrappers. |
| `iff_bottom_up`, `simp_bottom_up` and invocation subject reducer | Named declarations or invocation rewrites become higher-order root reductions. | A reducer is reached after higher-priority ordinary rewrites at a node. The persistent reducer closes over the declarations it was installed with and is replaced in `srw_ss` when they change; the invocation reducer closes over its own rules. Neither is a general child-first traversal. | The derived simpset; `[iff_bottom_up]` also seeds claset rules. |
| `membership_heads`, `pointwise` and `extensional_normalize` | A function equality becomes an applied or membership equivalence with a kernel conversion. | `membership_heads` scans rewrite heads once per tactic construction. The conversion acts at the goal boundary under leading universal quantifiers and implications; it stands down when a supplied rewrite states the reading. It does not recurse through arbitrary nested equalities. Each pointwise step removes one function arrow. | AUTO, FORCE, FASTFORCE and terminal `with_extensionality`; safe-only methods do not add the unsafe extensional step. |
| `GEN_GLOBAL_SIMP_TAC` mutual fixpoint | Goal assumptions and conclusion become simplified goals plus kernel validation. | It scans assumptions in configured order, simplifies the conclusion, and repeats after actual changes or structural decomposition. Root implication rewriting and rebuild are separate flags. `cascade_safe_simp` disables implication rebuild to avoid a safe-step cycle. | Context, ambient and cascade simplification in clasimp; Aesop's normalization rule also calls safe simplification. |
| Fact and rule views | The invocation's original theorems become literal assumptions, schematic simplifier views, and compiled search rules. | `clasetFacts` owns original theorem, support, fixed parameters and source ID. Safe consumers insert literal facts without compiling an unsafe rule. Search consumers compile eligible implications from lazy schematic views and insert the others, avoiding duplicate assumption expansion. Search canonicalization instantiates the rule view at use sites. Clasimp derives certified child-first normalized views of supplied search facts against the invocation simpset; it then curries conjunctive antecedents so separately simplified assumptions remain usable. Rewrite LHS views use the separate pass below. If the ordinary tactic leaves work open, clasimp derives rule views of persistent and invocation declarations and retries on the original goal. The originals remain installed, and transported rules retain their declared role. Safe consumers transport only safe declarations; every derived rule must preserve its safe classification and theorem support. BLAST offers a safe introduction view for plain facts with loose type variables. Aesop selects equational normalization views, including equational conjuncts, before freshening; derived views retain their source and support while propositional facts remain available to forward rules. Order tactics match theorem views at relation sites, and the order reducer matches directly supplied schematic citations at an atom while keeping assumptions fixed. Literal insertion still specializes against the current goal as a compatibility route, retaining the original ordered partial type instances and appending distinct maximal unions of compatible site matches under the invocation budget. | Classical, BLAST, clasimp, Aesop and order; linarith still inserts literal facts. |
| Rewrite LHS views | An ambient or supplied rewrite conjunct gains a kernel-certified view with its proper arguments in child-first normal form. The original remains installed. | Only the invocation's surviving ambient rules reduce a view; supplied rules contribute abstraction positions but never become ambient reducers. Conditional premises are assumed and reattached. Unchanged, joinable, renaming-unstable and limited derivations yield no view. Tables update incrementally from complete dependency inventories. Public tactics first use the raw simpset. An open pass requests cached views and continues its residual goals, composing validations with the retained raw subproofs. Both passes share the supplied originals, actual Once/Ntimes counters, context and invocation budget. | Direct safe and unsafe simplification; public and explicit-simpset AUTO, FORCE, FASTFORCE, SLOWSIMP, BESTSIMP and CLARSIMP. |

The ordinary `Traverse.TRAVERSE_IN_CONTEXT` still tries high-priority
rewriters at a node before descending through congruences. The opt-in
child-first path contracts an eta function argument first when possible,
unless a generic abstraction rewrite consumes that argument position.
Positions use the constant's kernel identity, so restoring a context
and reusing a constant's name cannot retain an unrelated abstraction.
It then descends and offers rewrites and reducers at that node. Its policy
charges head preservation, traversal and reducer attempts; the existing
`limit` counts successful reducer calls. Public clasimp tactics share an
invocation normalization budget across their mutual fixpoint, search
wrappers, initial FORCE simplification, extensional conversions and target
transport.
For each public invocation, clasimp replaces the order and linarith
decision fragments in its working simpset with budgeted copies. Their
context derivation, theorem-view matching, candidate search and proof
reconstruction charge the same invocation budget. The standalone
`ORDER_ss` and `LINARITH_ss` fragments retain their existing behavior;
the budgeted fragment constructors are available to callers that own a
budget explicitly.

The explicit supplied-view binding API compiles supplied originals once,
then finds ambient converses by one parallel application of each eligible
unconditional conjunct to a supplied right-hand side. Supplied conditions
are retained. Only the offending ambient occurrences are suspended;
siblings keep their names, allowances and views. Suspension persists in
the working simpset's replay history, and the original ambient simpset
stays available for a later invocation. Cached dependency metadata
re-derives affected ambient views after suspension; supplied views use
that remaining ambient set without using other supplied rules as reducers.
Supplied abstraction positions extend the surviving ambient positions for
both derivations. A changed policy rebuilds the ambient entries even when
no converse is suspended. The bounded adjusted-table cache keys the input
generation, exact suspension set and supplied positions; equal policies
before suspension need not remain equal afterward. Empty or redundant
policy extensions with no suspension retain the original table identity.
Each completed table also owns a lazy viewed simpset and decision bases.
Materializing a supplied binding uses that adjusted table directly, without
deriving a raw-policy table or carrying earlier-policy ambient views forward.
Default and bound working states share the completed table's viewed values.
Decision-fragment removal uses opt-in history replay that shares compatible
surviving native controls with the input and its existing views, including
consumed Once/Ntimes allowances. Ordinary fragment removal keeps its existing
behavior. Supplied originals are still installed separately by their binding.
A native LHS term net retains every possible first-order match, including
variable and abstraction patterns. Compatible root types further narrow
candidates. Per-binding RHS inventories share repeated subtrees and prune
only branches where the source cannot match; the kernel conversion still
checks the exact one-parallel-rewrite predicate. Memo hits replay the
caller's normalization charges, including
typed cutoffs, without consuming the original rewrite allowances.
The staged API detects against a bounded native inventory before a first
pass, without constructing ambient views or querying ambient reducers.
Its policy comes from compiled supplied occurrences and surviving ambient
rewrites. A later view binding accepts a table for the original or masked
ambient set, retains the same compiled originals and callback, and never
repeats converse detection. An unrelated ambient table is rejected.
Cold and warm stages have identical usage and typed cutoffs; a completed
theorem group survives an interruption while an incomplete group is retried.
An opt-in bound global simplifier accepts an already installed bundle apart
from additional arguments. Cached untagged originals remain solver context
through assumption/conclusion passes, root rewrites, rebuilds and final
solving, without reinstalling their rewrites. Compatible controls survive
local marker replay, including an exhausted allowance shared by a view.
The ordinary global simplifier retains its existing argument handling.
Prepared supplied bundles retain their compiled rules through history
replay, source suspension and citation filtering. Replay does not invoke
their rewrite maker again. Ordinary replay resets declared quotas while
preserving conjunction sharing; replay with control preservation retains
the actual remaining original/view counters, including zero.
An explicit bound invocation state prepares its runtime simpset, then
installs those originals once, retaining a lazy ambient-table provider.
New runtime decision procedures receive the untagged originals as context.
Raw, viewed, safe and cascade passes share its policy, original solver context
and remaining allowances. Attaching ambient views preserves supplied-rule
precedence with aliases of the installed compiled occurrences; it adds no
new native occurrences or rewrite quotas. A failed table request can be
retried, and a completed viewed state is retained. Public consumers first
run the raw pass, then request views only for work that remains open.
Its argument preparation uses the ordinary simp directive parser before
binding, preserving compatible surviving native counters after marker edits.
Tactic-only directives survive that parser separately from compiled rules.
Bound global passes apply `NoAsms` and `IgnAsm` to each current reducer
context, including assumption normalization, conclusion simplification,
root rewrites and implication rebuilds. Unsafe permutation instances use
the same selection. Assumptions remain in the proof goal and can still
justify structural closure; these controls select rewrite context rather
than remove hypotheses. Public standalone tactics expand abbreviations
and resolve labelled citations before binding, so those citations retain
their supplied origins, converse suspension and abstraction policy.
The marker-free path retains physical identity without a control scan or
history replay. Bound unsafe and safe search wrappers carry the same installed
bundle into FAST, bounded depth, SAFE and CLARIFY consumers; they do not pass
the original citations again as new rewrite arguments. Supplied conjunctions
therefore retain their shared remaining quota across those consumers.
The opt-in public argument processor reuses classical declaration routing
and the invocation fact environment. Simp/Iff payloads become supplied
originals, never ambient reducers for view derivation. Labels are resolved
before compilation; original fact IDs, support and cached schematic views
remain attached to that environment. Requirement-tagged payloads are bound
once and share original/view quotas. Req0/ReqD checks wrap each simplifier
step without recompiling their payloads as fresh rewrite occurrences.
AUTO, FORCE, FASTFORCE, SLOWSIMP, BESTSIMP and CLARSIMP driver bodies now
share one set of simplifier and wrapper operations. Their bound variants
retain the same invocation state in direct simplification, extensional
passes, unsafe search, final safe saturation and safe clarification.
FORCE's resumable first-best and depth sessions use that same wrapper;
atomic simplification retains the invocation's policy and budget rather
than a slice budget. Ordinary driver variants retain their existing
argument handling. The opt-in bound argument processor transports facts
and declarations only after the first attempt leaves work open. Fact
rewrite views are aliases of actual compiled fact sources, retaining
source IDs, support and their original remaining quotas. Filtering a
source out cannot introduce its alias. Conditional search facts retain
their destruction-rule role; safe consumers add no unsafe fact rules.
Transport suspends fact sources while normalizing their views, and
filters each declaration's own rewrite direction before normalizing it.
These copies preserve surviving counters and cached supplied compilation.
Prepared normalization uses declared allowances privately and restores
the actual remaining counters even when the invocation budget interrupts
it. Original and transported retries share one policy, fact environment,
runtime context and supplied bundle. Public AUTO, FORCE, FASTFORCE,
SLOWSIMP, BESTSIMP and CLARSIMP now use that processor and the bound
driver operations, including their budgeted entry points. Direct unsafe
and safe simplification bind once per invocation; explicit-simpset
drivers use the same binding through their classical wrappers and retries.
Runtime decisions are prepared after converse suspension and before the
supplied originals are installed. Labels, Simp/Iff declarations and
requirements keep their established routing. Completed raw proofs do not
force ambient views. An open pass continues its residual goals with the
viewed state under the same budget, callback and remaining rewrite quotas.
A failing continuation retains the raw proof and residual goals; typed
work limits and interrupts propagate. Longer cycles keep the typed
normalization-limit outcome.

The generic `process_clasimp_args` callback preserves supplied provenance
when its body passes the processed simpset to a CS tactic. It retains the
compiled declaration bundle and original fact environment for that
callback application. Generic controls remain unchanged for arbitrary
callbacks; the first CS consumer resolves and binds their payloads,
combining compiled bundles without refreshing source identities or
remaining counters. It selects the invocation budget and runtime context;
subsequent CS calls within that callback reuse them. Nested callbacks
restore the enclosing binding on normal return and exceptions, and no
binding survives beyond its callback. This scope is keyed by the exact
processed simpset, rather than a persistent cache of callback inputs.

Cached working states retain the original simpset, a lazy ambient view
table, one named view fragment, and separate lazy decision bases with and
without those views. The stateful clasimp derivation owns its default
working state; explicit simpsets use a bounded identity cache backed by
the incremental table cache. Equal native inventories can have different
conversion/decision contexts, so predecessor ties prefer the context with
fewer actual invalidations. Exclusions still remove original occurrences
and their views. Repeated reads preserve the same compiled view controls
and stripped decision base, including an already consumed allowance.
Plain decision requests do not force views or an unused default derivation.
The public explicit-simpset path caches its plain decision base and shares
one supplied binding per invocation. The first open raw pass requests its
ambient table; later invocations reuse it until a relevant context change.

## Proposed automation contract

1. Congruence controls which children may be visited and which local
   assumptions they receive. Weak conditional congruence leaves branches
   untouched until the split stage licenses them.
2. For an automation traversal, visit permitted children before ordinary
   parent rewrites, then revisit a changed parent under the invocation's
   normalization budget. At a redex, local and ambient rules have one
   deterministic precedence independent of registration name. A rewrite
   is also offered in the form its left-hand side takes under child-first
   normalization. An immediate ambient converse of a supplied rule is
   suspended as described in item 7. A congruence's explicit behavior
   takes priority over this default order.
3. Conditional rewriting may match a witness against the invocation fact
   environment and local context. Fixed parameters and theorem hypotheses
   remain support; no unsupported witness is guessed. Replay uses the
   tactic's explicit context and discharges that support.
4. Permutative rewrites follow the configured term order. A grounded
   contextual instance may use a justified orientation only when its
   premises have been discharged and its support fixes the matched terms.
5. Assumption and conclusion normalization form one mutual fixpoint.
   Before simplifying a context fact, dependents can read its original
   view; a fact cannot justify rewriting itself away. Context generations
   invalidate derived views when the available assumptions change.
6. Extensionality remains a certified inference at a documented goal
   boundary. It does not expand nested equations by default or enter a
   safe-only tactic as an unsafe step. Membership and application views
   must reconstruct the caller's exact target.
7. An unconditional ambient conjunct that reverses one supplied rewrite
   in one parallel step is suspended for that invocation. Sibling
   conjuncts and supplied conditions remain. Longer user-rule cycles
   terminate with a typed normalization-limit outcome. Built-in rules
   receive either a decreasing measure or an explicit repeat guard.
   An exhausted budget never reports saturation.

The approved D2 API is an opt-in traversal policy in `simp`. It preserves
eta function-argument heads with a certified conversion, then selects
child-first order under congruence. Its record carries a normalization
charge and a predicate keeping abstraction arguments at applications.
Clasimp derives this predicate syntactically from rewrites in force,
without naming a library theorem or client constant. simpLib also guards
its standard ETA conversion at protected partial applications; raw Traverse
leaves caller-supplied reducers under the caller's control.
Traverse.charge_only supplies the former contraction policy.
The default traversal stays as it is. `context_first` and
overlap-specific deferral were removed after local overlap and
recursive-equation tests. The seed and benchmark gates now pass, including
the `GENLIST` interval case that initially exposed the abstraction-head
problem. A paired subject-rewrite test shows that ordinary `[iff]` and
`[iff_bottom_up]` rules reach the same result under child-first traversal.
The persistent bottom-up reducer remains for ordinary HOL4 simplification,
whose default still visits the parent rewrite first in this case. The
exported invocation reducer remains a compatibility operation; automation
does not depend on it for traversal. The existing context fixpoint and
conditional subgoaler remain reusable. Certified rule-view transport now
covers persistent claset rules in AUTO and the direct contextual AUTO,
FORCE, FASTFORCE, SLOWSIMP,
BESTSIMP and CLARSIMP entry points. The ordinary tactic runs first, and a
certified derived view is tried when it leaves work open. Candidates share
a nonlogical head with the goal, a residual goal from the first attempt,
or a head reachable through chains of the supplied simpset's direct
rewrite-head bridges; this bounds conversion work without
assuming that the rule and goal use identical heads. The original
declaration and role are retained. A synthetic pair of cyclic rules
exercises the typed
normalization-limit outcome through `CLARSIMP_TAC_BUDGETED`.
