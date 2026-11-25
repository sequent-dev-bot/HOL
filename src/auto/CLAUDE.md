This file provides guidance to AI agents when working with code in
the automation project of the HOL4 repository.

Scope: `src/auto/` — the opt-in automation project: Isabelle/HOL-parity automation layer.

## Project ground rules

- The goal is HOL4 analogues of Isabelle/HOL's automation (`auto`,
  `blast`, `force`, `safe`, `clarify`, `arith`, …) that are **at least
  as strong** as the originals.  The target is parity in **automation
  strength**, not Isabelle-style surface syntax — judge every design by
  resulting tactic strength, not resemblance to Isabelle.
- Naming is HOL4 uppercase convention only: `AUTO_TAC`, `BLAST_TAC`,
  `SAFE_TAC`, `CLARIFY_TAC`, `ARITH_TAC`, …  No lowercase Isabelle-alias
  layer.
- Solutions must be general, principled and extensible — no pragmatic
  fixes.
- Architectural decisions are the owner's: present them one-by-one with
  options and a recommendation; never decide silently.  Settled
  decisions are not re-litigated.
- NO CHEATS ALLOWED.

## Building and testing

From the repo root:

    bin/build -t --seq=tools/sequences/upto-auto

is the routine development gate building kernel + core theories + this layer,
with selftests.  Its real scope is wider than the entries suggest: Holmake
recurses from `linarith/instances/` into src/integer, src/real, src/rational
and their closure, and a failure in any of those is reported against the
`src/auto/linarith/instances` entry.  The sequence then builds the
post-`boss` `seeds/`, `benchmarks/` and `examples/` entries in that
order.
`bin/build -F -t` checks the full distribution except `benchmarks/` and
`examples/`.

Numeric attribute values (`[elim=75]`, `[norm=~3]`) need a quote filter
built from the current `tools/parsing/HOLSourceParser.sml`.  Configure,
not any Holmakefile rule, compiles it into `bin/` and the heaps, so
after pulling run `poly < tools/smart-configure.sml` — a stale filter
reports `expected close delimiter` at the attribute.

Theory scripts live in `rules/`, `linarith/`, `linarith/instances/`,
`linarith/theory_tests/` and `aesop/theory_tests/`; in `classical/`,
`blast/`, `clasimp/` and `aesop/` plain `Holmake` compiles nothing and
exits 0 even on type errors.  Build `selftest.exe` there.

Per-directory: plain `Holmake` inside `src/auto/rules/` and
`src/auto/linarith/` works — their Holmakefiles pin
`HOLHEAP = $(HOLDIR)/bin/hol.state0` themselves.
`src/auto/linarith/instances/` is post-boss and must *not* be given
that heap; plain `Holmake` is right there too.  Every directory builds
`selftest.exe`; run it directly, or set `HOLSELFTESTLEVEL` to tee into
the directory's log — `ntactical-selftest.log` in `rules/`,
`linarith-selftest.log` in `linarith/`,
`linarith-instances-selftest.log` in `linarith/instances/`,
`<dir>-selftest.log` elsewhere.
Cross-theory persistence scenarios live in `rules/theory_tests/` with
their own Holmakefile (diamond merges, reload idempotence, batched
delta replay); `linarith/theory_tests/` holds the round-trip scenarios
for the `[arith]`/`[arith_split]` tables.

The library directories are registered in `SRCRELNAMES` in
`src/parallel_builds/core/Holmakefile`, so `bin/build -F` exercises them;
`benchmarks/` and `examples/` are built only by `upto-auto`.

## Architecture

Subtree layout:

    rules/       rule DB, attributes, netpairs, seeds
    classical/   SAFE/CLARIFY step tactics, FAST/BEST/DEEPEN
    blast/       tableau prover (Paulson's blast)
    clasimp/     AUTO/FORCE/FASTFORCE/CLARSIMP, [iff],
                 [iff_bottom_up]
    aesop/       best-first engine (aesop-style)
    linarith/    generic linear arith, `LINARITH_TAC`; carrier
                 instances, no dispatching `ARITH_TAC`
    seeds/       per-theory opt-in seeds, inversion audit, and named
                 algebra/field simp collections
    benchmarks/  translated parity corpora and exact shortfall accounting

`linarith/` contains the pre-boss core and num instance.  Its
`instances/` subdirectory contains the int, real and rat instances and
belongs to the parallel build band.

### Constraints that are easy to violate

- **Dependency stratification**: code here may depend only on
  libraries built before `src/boss` (`portableML`, `src/1`,
  `src/parse`, `src/marker`, `src/basicProof`); `rules/` must not
  depend on `src/simp`.  This keeps eventual promotion into the core
  build a sequence edit only.  The post-boss exceptions under `src/auto`
  are `linarith/instances/`, `seeds/`, and `benchmarks/`; their `INCLUDES`
  provide the source theories and tactic backends needed by the opt-in
  corpus and parity suite.
- **Portability**: the build entry is not `[poly]`-tagged — code must
  be Moscow-ML-compatible SML (no Poly/ML-isms).
- **No goal metavariables in HOL4**: safe steps run as genuine tactics
  on the goal state; unsafe search (rules needing undetermined
  witnesses) runs on an engine-internal proof-state representation
  with metavariables, followed by kernel replay of the found proof
  (the blast/MESON pattern). Don't design search that instantiates
  goal unknowns directly.
- **Wrappers and tactic-valued rules are never persisted** — they are
  closures; libraries re-establish them at load via `augment_claset`.
- Constructor distinctness is a runtime TypeBase entry per datatype,
  named `__claset_tyinfo_<thy>_<ty>_distinct`. Retrieval derives and caches
  ordinary safe elimination theorems from the case definition for the
  requested constructor pairs. These entries and cached theorems are absent
  from `rules_of`; `distinct_rule_names` lists their `Del` handles. Engine
  queries must supply genuine metavariables so rigid datatype variables do
  not trigger pair enumeration. Injectivity remains ordinary declarations.
- The global claset always carries the TypeBase-derived rules (injectivity
  and distinctness, `__claset_tyinfo_` names): `delrule`/`temp_delrule` on
  such a name warn and do nothing, and record no delta.  Drop one with
  `Del` or `remove_rule` + `with_claset`; never through `augment_claset`,
  whose removal the next TypeBase catch-up undoes.
- Preserve observable claset behaviour when refactoring: `rules_of`
  contents and order (except the constructor-distinctness entries above),
  wrapper lists, exact candidate-query sequences,
  `process_claset_tags` leftovers, and the existing warnings for
  stale/ill-formed/duplicate/cross-kind declarations.

## Testing Guidelines

- Write tests in the changed directory's `selftest.sml` (`testutils`);
  persistence/attribute changes also get `theory_tests/` scenarios
  (child-theory visibility, diamond merge, reload idempotence).
- Tactic tests: run successes through `Tactical.VALID`; assert exact
  residual goals for non-closing (`SAFE_TAC`-style) tactics; add
  negative cases (safe tactics must refuse unsafe steps); no theory or
  claset/simpset state left behind on success or failure.
- Strength benchmarks (Pelletier, translated Isabelle goals, arith
  corpora) are selftest assertions: solved-goal counts + time
  budgets.  Exhaustive corpora sit behind a higher `HOLSELFTESTLEVEL`;
  never prune goals to make a gate pass.
- The benchmark harness asserts the exact assigned-tactic solved set and the
  exact dated expected-non-solution records in both directions.  A newly
  solved registered goal is a failing test until its record is removed.  An
  `UnderIteration` record means a source result is not yet represented or
  otherwise accounted for; any such record blocks a parity claim.
- Corpus recipes are derived from the Isabelle method string; a goal is
  never given a fact its method does not name.
- Every safe seed declaration is covered by `seedAudit`; an exception is a
  dated, reasoned waiver consumed by the selftest, and stale waivers fail.
  Seed rules must not duplicate TypeBase contributions.
- Benchmark goals are closed by search, never recognition: no tactic,
  preprocessor, rewrite set or seed may name a problem, its statement,
  or a lemma that only discharges one.  Seeds carry general rule
  schemas with claset attributes and nothing else.
- Preprocessing normalizes forms, not instances; a justification that
  needs a problem's name is recognition.
- Checked-to-fail is only for method boundaries: a goal the procedure
  is documented not to decide, asserted to fail fast, with its error,
  citing the procedure that would close it.  A goal that is merely too
  hard or too slow is never asserted to fail — assert that the tactic
  terminates and reports no proof, and leave closing it a pass.
- Test specified behavior (solved goals, residues, warnings), not
  internals — nets and `claset` internals may change.
- Bug fixes get a failing-first regression test.
- Run: `Holmake` + `./selftest.exe` in the directory while editing;
  use the `upto-auto` gate before a change is done and `bin/build -F -t`
  before PR handoff or after any change outside `src/auto/` (simp,
  seeding).  New library subdirectories go into
  `tools/sequences/upto-auto` and `SRCRELNAMES`; new corpus or example
  subdirectories into `upto-auto` only.
