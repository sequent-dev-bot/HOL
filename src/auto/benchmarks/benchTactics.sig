signature benchTactics =
sig
  (* The src/auto tactic an Isabelle method name stands for.  The table
     is keyed by the method name alone and reads nothing of the goal, so
     this dispatch cannot become a per-goal hint however the corpus
     grows.

     An Isabelle method the table does not cover raises, naming it.
     There is no fallback tactic: a method silently mapped to something
     plausible would let the measurement claim a result the source proof
     never asked for. *)
  val tactic : string -> benchLib.tactic_id
  val methods : string list
end
