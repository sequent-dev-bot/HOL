(* Test support shared by the suites that exercise linear arithmetic,
   and not part of linarithLib's surface.  Two of them are the
   Arith_Examples strength corpora: selftest.sml here runs the 34
   num/bool goals; instances/selftest.sml runs all 54 translations.
   Those 34 goals are stated here, along with the driver and the
   canonical numbering both suites are checked against, so that the one
   proposition each stands for is written once.  What cannot be shared
   is the other 20: this directory is pre-boss and cannot parse int,
   real or rat syntax, so the instances suite states those itself and
   merges them into the numbering.  The assertion helpers below are
   shared more widely still: clasimp's and aesop's suites reach linear
   arithmetic through their solvers and check the same [arith] table. *)

signature linarithCorpus =
sig
  include Abbrev

  (* A corpus goal is either one the tactics are expected to close, or
     one they are expected to refuse.  Refusal is asserted only where
     refusing is the specified behaviour: a method boundary, a goal
     linear arithmetic is documented not to decide.  A goal that is
     merely hard, or slow, does not belong in the second category --
     failing it is not desired behaviour, and a suite that asserts the
     failure obstructs the work of removing it, and cannot tell a
     reported "no proof" from a tactic that never came back.

     Both fields of a boundary are checked.  error is the message the
     tactic must fail with, so that a goal recorded as beyond the method
     cannot be silently satisfied by an unrelated crash; the boundary
     budget is much tighter than the goal budget, so that a boundary is
     one the tactics report rather than one they run into.  remedy names
     the decision procedure that would close the goal, and is what the
     suite prints when the boundary moves. *)
  datatype strength_outcome =
      StrengthSuccess
    | StrengthExpectedFailure of {error : string, remedy : string}

  type strength_goal = int * strength_outcome * term

  (* The goal numbers of Isabelle's Arith_Examples.thy: full_numbering
     is all 54, core_numbering the 34 that survive translation to num.
     Stated here once so that the two suites, which run in different
     processes, cannot drift apart. *)
  val full_numbering : int list
  val core_numbering : int list

  (* The core_numbering goals, in source order.  The suite here runs
     them as they stand; the instances suite merges its own 20 into
     them, which merge_by_number does because source order is goal
     number order. *)
  val core_arith_examples : strength_goal list
  val merge_by_number :
    strength_goal list * strength_goal list -> strength_goal list

  val selftest_level : unit -> int

  (* check (name, predicate) is the testutils tprint/OK/die triple the
     suites state a boolean assertion with. *)
  val check : string * (unit -> bool) -> unit

  (* Every tactic assertion runs the tactic under Tactical.VALID, so
     that a bad justification is caught rather than scored as a
     success.  residual is what the tactic leaves behind; the two
     answers a tactic is asserted to give are closing the goal outright
     and refusing it outright.  A suite that wants a third answer --
     reading a refusal as simply not closing the goal, say -- states
     that variant itself, over residual. *)
  val residual : tactic -> goal -> goal list
  val valid_closes : tactic -> goal -> bool
  val tactic_fails : tactic -> goal -> bool

  (* The right-hand side of what an instance's norm_conv proves.
     canonical_form additionally accepts UNCHANGED, which norm_conv may
     raise instead of proving a reflexive equation, so that a test
     comparing two terms' normal forms can name a term already in
     normal form. *)
  val normalized_rhs : linarithData.linarith_instance -> term -> term
  val canonical_form : linarithData.linarith_instance -> term -> term

  (* Runs operation with one arithmetic fact temporarily in the [arith]
     table, removing it again however operation ends, and answers false
     if the table is not registered at all.  Suites that reach linear
     arithmetic through a solver use it to check that the solver reads
     the table on each call rather than snapshotting it, and that
     nothing is left behind afterwards. *)
  val with_arith_fact : (unit -> bool) -> bool

  (* A snapshot that has the probe fact and one that lacks it, in that
     order, both taken from the ambient state when called. *)
  val contexts_with_and_without_fact : unit -> Context.t * Context.t

  (* Whether tactic closes goal in the given context, never raising. *)
  val closes_in : Context.t -> tactic -> goal -> bool

  (* Whether a tactic built from a context reads that context's [arith]. *)
  val follows_arith_context : (Context.t -> tactic) -> goal -> bool

  (* check_numbering {suite, numbering} goals checks that goals uses
     exactly the numbers in numbering, once each, and that the two
     numberings above still stand in their documented relation. *)
  val check_numbering :
    {suite : string, numbering : int list} -> strength_goal list -> unit

  (* run_suite runs every goal under tactic against a per-goal budget,
     labelling each attempt suite ^ " goal " ^ number, then checks the
     outcome counts and the elapsed time against suite_budget.  tactic
     is a thunk built afresh per goal, so a tactic that snapshots the
     [arith] table sees the table each goal actually runs against. *)
  val run_suite :
    {suite : string,
     tactic : unit -> tactic,
     suite_budget : Time.time,
     expected_successes : int,
     expected_boundaries : int} -> strength_goal list -> unit
end
