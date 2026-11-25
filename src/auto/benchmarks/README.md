# Automation parity benchmarks

This directory contains a data-driven comparison of Isabelle automation
methods and their closest HOL4 tactic counterparts.  The complete results
and definitions of every reported category are in
[`../PARITY.md`](../PARITY.md).

Each benchmark goal records:

- a HOL4 theorem statement;
- the Isabelle source file, line, commit, and method;
- the structured HOL4 method recipe assigned as that invocation's closest
counterpart, including local rewrites, splits, classical rules, facts,
  and method composition;
- whether the goal belongs to the fixed routine selftest subset; and
- any HOL4 theorem that must be excluded to avoid solving the goal by
  reusing its direct analogue.

The SML interfaces call the complete collection a `corpus`.  A `shortfall`
is a dated record saying that a goal is outside the accepted scope, exposes
a current tactic limitation, or could not be translated faithfully.  The
selftest compares actual results with those records in both directions.
`benchSetShortfalls` and `benchLibraryShortfalls` hold the current
ledgers; each record names a root cause, not just an identifier.

Recipes are not authored.  `benchRecipe` parses the entry's Isabelle method
string and `benchTactics` maps each method name to the `src/auto` tactic
it stands for, so a goal cannot be given an argument its source proof did
not name.  Only methods the layer has a counterpart for are in the table:
Isabelle's `algebra` is not, and `arith` and `presburger` stand for
`LINARITH_TAC`, the layer's one arithmetic tactic.  A method string the
parser does not understand is a hard error, never a silent fallback to a
bare tactic.  `benchNames` is a single global table from
Isabelle theorem name to HOL4 theorem; it is keyed by name only and knows
nothing about which goal is asking.  Where a citation's attribute
resolves it against the enclosing lemma's assumptions --
`split_list_prop [OF assms]` -- the recipe supplies that entry at the
instance the goal's own leading antecedents determine, which is what
the resolution fixes; the premises stay, where the goal's antecedent
discharges them, and a citation whose first premise matches no
antecedent is an error naming it.  `benchAmbient` supplies the
translation's definitions as rewrites, and only
to the methods that consult a simpset -- Isabelle's `blast`, `safe`,
`clarify`, `metis` and its decision procedures do not.  It stands in for the
ambient simpset an Isabelle method reads without naming it, and is cut to
what that simpset carries: `benchIsabelleAmbient` records, per constant,
how Isabelle introduces it and the source line that says so.  A `fun`, a
`primrec`, a datatype's selectors and predicator, and a `definition` whose
characterisation Isabelle separately declares simp are in; a plain
`definition` is out.  Alongside them the set carries a few results
Isabelle declares `simp` or `iff` about a constant whose definition it
withholds, each citing the declaration it transplants.  Two Isabelle
facts can translate onto one HOL4 theorem, so one of them can be a
corpus goal's statement; the measurement then withholds it on that
goal, as it withholds a citation that states its goal, and the
selftest checks that it does.

The ambient context has a second half, for Isabelle's claset: the
rules it declares `intro`, `elim` or `dest` about a constant whose
definition it withholds.  No rewrite stands in for one -- a classical
rule takes a term apart in a direction the simplifier will not run --
and each carries the safety Isabelle gives it, `!` being safe.  The
two halves go to their own methods: `benchLib.consults_claset` is not
`benchLib.consults_simpset`, and Isabelle's `simp` reads no claset
while its `blast`, `safe` and `clarify` read nothing else.

Both halves are cut by Isabelle's theory order.  Isabelle reads a
theory in order and sees only the theories it imports, so a result
declared below a proof, or in a theory that imports the proof's rather
than the other way round, was not in that proof's context: `Pow_Compl`
is proved at `Set.thy:1610` and knows nothing of `Sigma`, which
`Product_Type.thy` introduces.  `benchIsabelleAmbient.in_scope` is the
cut and `benchAmbient.arguments_at` applies it; the import order is
mined alongside the introductions.  The cut reads the goal's mined
source line and nothing about its statement, so the context is one set
for the whole corpus rather than a per-goal choice.  It is a formality
on neither side: an out-of-scope rewrite is a fact the source proof did
not have, and an out-of-scope classical rule is search the source proof
was not paying for.

`HOLSELFTESTLEVEL=1` runs the explicitly marked representative goals.  This
is a fixed subset, not random sampling.  Level 2 or higher runs every
executable goal and also tries selected alternative tactics -- counting a
goal only where the alternative closed it and the assigned tactic did not.
Alternative-tactic results never decide whether the test passes.

Source mining produced 1,029 distinct Isabelle results after deduplicating
translated statements up to bound-variable renaming; 1,027 are executable
goals and two could not be translated faithfully.  They come from six
Isabelle theories plus a handful of `ex/` files: this is Isabelle's base
library, not Isabelle/HOL.

Each goal is run under a wall-clock budget, enforced by `Timeout.apply`
under thread attributes that admit asynchronous interrupts: a runaway
computation is cut off, and the selftest checks that directly.  The
interrupt still has to reach the tactic, and a handler that treats every
exception alike swallows it.  The budget then bounds nothing: the
elapsed time is compared against it when the payload finally returns, so
such an overrun is reported rather than prevented, and it has been seen
to run for many minutes on a goal whose budget is thirty seconds.  A run
that goes quiet with one goal named is that goal still running, not a
lost harness.

To build and run both test levels from this directory:

```sh
Holmake
./selftest.exe
HOLSELFTESTLEVEL=2 ./selftest.exe
```

`./genparity.exe` performs the exhaustive measurement and rewrites
`../PARITY.md` deterministically.

## Corpus integrity detectors

`benchGuards` answers the questions a corpus entry cannot be trusted to
answer about itself.  Each detector reports findings; the caller decides
whether a finding is fatal.

- **A1 recognition** — whether a supplied theorem alone closes the goal,
  by `MATCH_ACCEPT_TAC`, `REWRITE_TAC`, its `GSYM`, a pure boolean
  simplification, `MATCH_MP_TAC` followed by safe steps, or a
  minimum-budget `METIS_TAC`.  A route counts only when the same route
  without the theorem fails, so an ambient tautology is not mistaken for
  recognition.  `benchLib.theorem_is_goal` is the cheap accepting
  pre-filter, and it is also what decides at measurement time whether a
  citation is dropped.  It compares the two statements up to reordering of
  conjunctions and disjunctions, orientation of equations and
  equivalences, and renaming of free variables, so a lemma that is the
  goal spelled differently is still the goal.
- **A2 provenance** — every `parityTranslation$source_X` argument must be
  named by the entry's Isabelle method, modulo a closed suffix list, or be
  a registered definition of a constant occurring in the goal.
- **A3 search work** — a goal whose Isabelle method is a search method
  must do search work.  The engines report node expansions, tableau depth,
  branches, inferences and rule applications to the shared `searchWork`
  meter, which brackets the run.
- **A4 single-use rules** — a translation lemma used by exactly one corpus
  goal must be named by that goal's method.
- **A5 alias audit** — every hand-mapped display name in
  `benchExplicit.special`, reported unless it renders a real lemma under a
  documented Isabelle attribute.
- **A6 goal-term pin** — a structural hash of every goal statement, de
  Bruijn for bound variables and theory-qualified for constants, pinned per
  family in `selftest.sml`.  A changed hash means a goal statement moved.

Detector logic, thresholds and pins are owner-signed.  Widening one to make
a run green is the defect they exist to catch.

`./guards.exe` sweeps the whole corpus and writes the findings list to
`guards-findings.md`.  `HOLGUARDSOUT` names another output file,
`HOLGUARDSSKIP` leaves detectors out,
`HOLGUARDSFAMILY` restricts the sweep to one family, `HOLGUARDSLIMIT` caps
the goals per family, and `HOLGUARDSPROGRESS=1` names each goal as it is
swept.  Each restriction is recorded in the generated header.

Set `HOLBENCHDIAGNOSTICS=1` to emit a diagnostic block for every selected
goal.  Set it to a path instead to append those blocks to a manifest file.
Set `HOLBENCHSHORTFALLSONLY=1` to select only executable registered
shortfalls in the requested family.  A run restricted this way measures
part of the corpus, so the suite's corpus accounting -- the exact
per-family slice sizes -- does not hold and the run reports a failure
saying so.  Read the manifest it wrote, not its exit status.  The
restriction reaches the corpus families only: the hand-built families
the suite measures the harness itself with go through
`benchLib.run_family`, which restricts nothing.
Diagnostics report the source method, legally translated recipe, excluded
ambient analogues, residual outcome, elapsed time, exposed search statistics,
and the working root-cause classification.  This mode observes the ordinary
tactic run and does not change its recipe or timeout.

For focused debugging, `HOLBENCHBLASTRESIDUAL=1` prints residual tableau
goals and `HOLBENCHPATTERNTRACE=1` traces restricted predicate abstraction.
The HOL trace family `clasimp` reports the selected search engine and stage;
level 2 also reports available search statistics.  The exhaustive alternative
tactic battery is informational and never contributes to the assigned count.
