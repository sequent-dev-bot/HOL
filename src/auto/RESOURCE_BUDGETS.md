# Automation work budgets

`searchBudget` belongs to one invocation. A caller passes the same budget to
nested consumers; no backend resets its counters. Each dimension has an
optional nonnegative limit. `SOME 0` rejects the first charge, `NONE` is
unbounded, and negative limits or extensions are errors. Charges happen
before the admitted work. A yield retains usage, and extending that budget
does not reset it. Semantic depth bounds remain separate from these counts.
Bounded child turns charge their own counters and the enclosing invocation
atomically for resumable work. Atomic simplification within a FORCE turn
charges the invocation alone. Extending a child's local limit preserves
both sets of counts.

The implemented checkpoints are:

- Literal fact insertion: candidate charges on subterm scans, head and
  type matches, and duplicate/support comparisons; normalization charges
  on theorem specialization and type instances; application charges on
  admitted assumptions. The budgeted fact environment also charges
  classification, first construction of a lazy schematic view, and
  admitted search-rule declarations. Literal insertion retains its
  ordered partial type instances and appends distinct maximal compatible
  joins. Compatibility checks, cached graph queries and emitted joins
  charge candidates; theorem instantiation and duplicate/support checks
  charge as for the original instances. Zero or one partial match adds
  no join work. Clasimp's fact-view tactics pass
  their invocation budget through these paths. The ordinary insertion
  entry point is unchanged.
- Clasimp's opt-in child-first traversal: normalization charges before
  congruence descent, weakening, and reducer attempts. AUTO, FORCE,
  FASTFORCE, SLOWSIMP, BESTSIMP, and CLARSIMP share one callback across
  their mutual simplification and search wrappers per tactic invocation.
  Their conditional witness subgoaler charges each context match as a
  candidate, plus normalization and proof application work. A typed cutoff
  propagates through a failed witness attempt.
  A fallback search for certified rule views charges rewrite-head scans,
  declaration relevance scans, and selected rule conversions as candidate
  work. It charges child-first conversion as normalization and each
  installed derived rule as an application. It keeps the original
  declaration and shares the ordinary tactic's budget.
  `CLARSIMP_TAC_BUDGETED` accepts a caller-owned budget and propagates
  `LimitReached` without translating it into tactic failure. FORCE's
  initial simplification, extensional conversions, and target transport
  charge the same normalization budget.
- Clasimp's explicit supplied-view binding charges normalization before
  each RHS subtree inventory lookup, candidate type check, conversion
  preparation and parallel converse-rewrite attempt. A native pattern net
  and shared subtree inventories avoid impossible root matches and whole
  branches; the actual predicate stays one parallel rewrite. The binding
  then charges certified view derivation against the remaining
  ambient rules. Its bounded memo replays those exact units, so cold and
  warm bindings have the same usage and typed cutoff. Converse detection
  uses the input table generation; views use the post-suspension table
  generation and effective abstraction policy. A completed stage can be
  reused after a later cutoff; an incomplete theorem group is not cached.
  The staged binding first detects from an eight-entry native inventory
  cache without constructing ambient views or querying ambient reducers.
  Detection keys that inventory's generation; its 256-entry theorem memo
  replays the same units. A late binding retains the original callback,
  suspensions and compiled originals, continuing view derivation without
  recharging detection. Its reported normalization total covers both
  binding stages, excluding intervening goal-simplification charges.
  Ambient table construction and incremental invalidation are simpset
  derivation, outside an invocation's counters. Empty or control-only
  supplied arguments do no detection or supplied-view work. Public
  consumers request the ambient table only after an open raw pass; a
  completed raw proof pays no ambient derivation cost.
  Supplied abstraction positions also adjust the ambient table's policy;
  this cached simpset derivation stays outside the invocation's counters.
  Both sets of views use surviving ambient positions plus supplied
  positions, while only ambient rewrites reduce either set of views.
  The stateful/default and explicit working caches retain lazy view tables
  and viewed decision bases. Their ordinary decision-base reads do not
  construct views. Construction is outside the invocation's counters;
  subsequent identity reads repeat no derivation. A failed table force can
  be retried without retaining incomplete entries. Cached decision bases
  also retain consumed rewrite allowances across repeated reads, rather
  than reviving them through history replay.
  Completed adjusted tables own the same lazy viewed values used by bound
  working states. Opt-in decision-fragment replay preserves actual native
  counters across plain, full and stripped copies, including earlier
  consumption; it does not grant a new allowance when a view is attached.
  The opt-in bound global simplifier takes an already installed bundle
  separately from additional arguments. Its cached untagged originals
  remain solver context in mutual passes, root rewrites, implication
  rebuilds and final solving. It never reinstalls the bundle as arguments.
  Marker-adjusted copies rebind compatible bundle counters, including
  exhausted counters shared by views. The marker-free path uses the input
  directly; building the control index visits only supplied bundle sources.
  An explicit bound invocation state prepares its runtime simpset once.
  Its raw and viewed consumers share the binding's normalization callback,
  original solver context and actual remaining counters. Ambient views are
  attached lazily; aliases of supplied occurrences retain their precedence
  without creating native occurrences or granting more rewrite uses.
  Successful view attachment is retained; an interrupted provider is retried.
  Preparing arguments applies existing simp directives before binding and
  retains compatible surviving native counters, including earlier consumption.
  Marker-free inputs incur no control-index scan or history replay. Bound
  search wrappers reuse the installed bundle and shared callback at unsafe,
  depth, safe and clarify steps; they never compile the original citations
  as additional arguments, which would grant sibling conjuncts fresh uses.
  Opt-in bound fact and declaration transport starts only after an open
  initial attempt. All retries use the same fact environment and bundle.
  Fact aliases share their compiled source counters; removed sources
  contribute no aliases. Derivation has a private 20000-unit cap per fact
  source or schematic fact view and also charges the invocation callback.
  Private cap exhaustion rejects that view; a typed invocation limit
  propagates. Prepared normalization restores actual counters on both
  success and exceptions. Filtering declarations preserves surviving
  counters and cached supplied compilation, rather than resetting quotas.
  Public default, budgeted and explicit-simpset tactic drivers now enter
  that binding once; direct safe and unsafe simplification do likewise.
  Runtime decisions are prepared after converse suspension and before
  original installation, with one callback and context for nested search.
  The raw pass does not force its lazy ambient-table provider. If it
  leaves work open, the viewed pass continues the residual goals and
  composes their validations with the raw subproofs. It retains the same
  callback, invocation budget and spent allowances; neither a view nor
  a continuation grants fresh rewrite uses. Once declarations retain
  their quota across fixpoint passes, search wrappers, safe saturation
  and transport retries.
  A CS consumer reached through the generic argument callback retains its
  already compiled declarations and fact environment. Its first CS call
  selects the invocation budget and runtime context; later CS calls in
  that callback share them. Deferred generic control payloads compile
  once and join the declaration bundle with their existing source IDs and
  counters. Callback nesting and exceptions restore the enclosing scope.
- Classical best-first: candidate charges on heap selections, lazy child
  pulls, and forward-rule premise scans; application charges on node
  expansion; normalization charges before kernel replay. A budgeted depth
  stage charges each safe fixed-point attempt and accepted transition,
  then each depth expansion and pulled child. Both charge a candidate
  before deriving each constructor-distinctness pair a lookup needs and
  the claset has not yet derived. Derived pairs stay cached in the claset,
  so later lookups, in this search or another, reuse them free. A lookup
  at a type variable of the goal derives no pair; one at a type
  metavariable covers every datatype.
- Aesop: candidate charges on forward-rule premise scans, ordinary
  introduction/elimination-major attempts, and rendered-tactic or
  multi-step alternative pulls; application charges on committed safe
  rules and installed unsafe alternatives; normalization charges on each
  normalization-rule scan.
- BLAST fixed-depth: candidate charges at cooperative scan and unification
  checkpoints; application charges on committed tableau transitions;
  normalization charges at term normalization and equality substitution.
- Order: candidate charges during source-theorem and conjunct
  classification, relation grouping, axiom lookup, graph scans, and
  reachability; application charges on derived rules, chained edges, and
  closures; normalization charges on context and fact reduction, conjunct
  splitting, and goal reduction.
- Linarith full proof search, certificate search, and replay: candidate
  charges on coefficient, atom, row, disjunction, and case scans;
  application charges on row-pair elimination, disequality branches,
  and search nodes; normalization charges on decomposition, row
  construction, preprocessing, augmentation, and justification replay.
  The budgeted reducer checks arithmetic applicability before charging
  its question and input-context candidates; a declined atom costs none.

Classical and Aesop candidate yields retain their search sessions. Classical
also retains a candidate awaiting kernel replay when the normalization limit
is reached. A cutoff inside a constructor-pair lookup keeps the pairs
derived so far; the resumed lookup charges only those still underived, so
each further candidate derives one more pair. A nested expansion cutoff
retains the selected frontier state, and the retry does not charge again
for the alternative it was forcing; other work charged inside a partially
forced lazy alternative can repeat.
BLAST's one-shot fixed-depth adapter restores its trail on a limit. Its
resumable fixed-depth path retains the owned trail, branch/script state,
rule cache and backtracking handlers across turns. A cutoff within one
partially scanned step may replay charged work at that step; a cutoff
during initial goal translation restarts translation before the first
tableau frontier exists. Order returns a one-shot proved, exhausted, or
limit result. Existing tactic, depth, and order entry points keep their
compatibility behavior.

FORCE uses a configurable schedule of positive candidate, application, and
normalization slices. Its first-best session keeps its heap and pending
alternatives across turns. Classical depth keeps its lazy cursor and a
candidate awaiting replay at each stage up to the configured bound. Their
yielded slices double for the next turn. Tableau runs at one configured
depth and retains its owned frontier and pending reconstruction across
turns on the same child budget. Every round offers one turn to each active
engine, and a parent limit reports a typed cutoff.
First-best and depth simplification wrappers are atomic: their normalization
charges use the invocation budget, so a small turn slice cannot restart a
partially completed simplification. Resumable selections, expansions and
replay still charge the child slice; the invocation limit bounds each
atomic step and propagates a typed cutoff.
`FORCE_TAC_BUDGETED` accepts a caller-owned budget; the ordinary FORCE
entry points allocate finite default candidate, application, and
normalization limits.

Aesop's ordinary claset rule and forward-rule cursors retain their partial
scan across a candidate yield, including the uniqueness check for
deterministic safe rules. A rendered tactic is charged before its callback
starts; work inside an arbitrary callback remains the callback's own
responsibility. Forward duplicate filtering compares existing assumptions
in the candidate's arriving substitution. It compares alternative
results in their common parent substitution only when bindings of
pre-existing metavariables agree.

Aesop keys saved scans by the tactic registry generation. Replacing a
registered rule during a yielded budget session restarts its tree search
from the original goal under the same budget, so repeated work is charged.
An unchanged registry resumes its pending alternatives in place.

Aesop's budgeted session retains the explicit proof context for rendered
tactic rules across yields, including interleaved sessions. Contextual
engine rules, including Aesop's built-in disch, gen, and hypothesis
substitution, retain that context when lazy alternatives are forced.
Convenience search entry points snapshot the ambient context once at
invocation. Classical safe, clarify, fast, best, A*, first-best, and
depth searches pass the tactic context to their wrappers and built-in
safe tactic calls. Internal hypothesis substitution uses that context.
Exact BLAST reconstruction and recursive kernel replay use the supplied
context and propagate interrupts and typed work cutoffs to their callers.

Linarith's budgeted proof entry point includes splitting and carries an
explicit tactic context through nested forward side proofs without a
nested ambient pin. `LINARITH_TAC_BUDGETED` and
`CFG_LINARITH_TAC_BUDGETED` also charge the caller's budget through the
full tactic search. `SIMPLE_LINARITH_TAC_BUDGETED` charges its direct
refutation path. All three propagate a typed work-limit exception. They are
one-shot tactics: extending the budget permits a retry but does not
resume a suspended split tree. The existing tactic and simplifier
adapters retain their unbudgeted behavior. These are G5 integration
tasks, not exhaustive-search outcomes.
