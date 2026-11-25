signature blastReconstruct =
sig
  include Abbrev

  type claset = clasetLib.claset
  type proof = blastSearch.proof

  (* Reconstruction executes the recorded tableau script left-to-right on a
     typed classical-engine node, then grounds and kernel-replays once. *)
  val reconstruct :
    Context.t -> goal -> proof -> (goal list * validation) option
  val reconstructWith :
    Context.t -> claset -> goal -> proof ->
    (goal list * validation) option

  (* Search continuations reject failed reconstruction with
     blastSearch.PROOF_FAILED, so the tableau resumes at its choice stack. *)
  val searchGoal :
    Context.t -> claset -> int -> goal ->
    (proof * (goal list * validation)) option
end
