# Examples for the `src/auto` automation layer

The theories in this directory are a user-level tour of the tactics
provided by `src/auto` — HOL4 analogues of Isabelle/HOL's automation
(`auto`, `blast`, `force`, `safe`, `clarify`, `arith`, …).  Every
theorem here is proved by the tactic it demonstrates; the files build
as ordinary theory scripts and double as documentation.

Suggested reading order:

| Theory              | Shows                                             |
|---------------------|---------------------------------------------------|
| `clasetExamples`    | declaring rules: `[intro]`/`[elim]`/`[dest]`/…    |
|                     | attributes, priorities, markers, persistence      |
| `classicalExamples` | `FAST_TAC`, `BEST_TAC`, `SLOW_TAC`, `ASTAR_TAC`,  |
|                     | `DEEPEN_TAC`, `SAFE_TAC`, `CLARIFY_TAC`           |
| `blastExamples`     | `BLAST_TAC`, `BLAST_DEPTH_TAC` (tableau prover)   |
| `clasimpExamples`   | `AUTO_TAC`, `FORCE_TAC`, `FASTFORCE_TAC`,         |
|                     | `SLOWSIMP_TAC`, `BESTSIMP_TAC`, `CLARSIMP_TAC`,   |
|                     | `[iff]`, `Simp`/`Iff` markers                     |
| `aesopExamples`     | `AESOP_TAC`, `AESOP_SAFE_TAC` (best-first engine) |
| `linarithExamples`  | `LINARITH_TAC` over num/int/real/rat, mixed       |
|                     | goals, `[arith]`, `[arith_split]`, `LINARITH_ss`  |

To experiment interactively, start `bin/hol` and load the library for
the tactic family you want, e.g.:

    > load "clasimpLib"; open clasetLib clasimpLib;

The int, real and rat instances of `LINARITH_TAC` register themselves
when their modules are loaded:

    > load "intLinarith"; load "realLinarith"; load "ratLinarith";
    > load "linarithLib"; open linarithLib;

The implementation lives one directory up: `rules/` (rule database and
attributes), `classical/`, `blast/`, `clasimp/`, `aesop/`, `linarith/`
(with `linarith/instances/`).  Each has a `selftest.sml` whose
regression corpora are a further source of worked goals.
