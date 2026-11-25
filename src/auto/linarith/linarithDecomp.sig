signature linarithDecomp =
sig
  (* An application of a binary operator, as (operator, left, right).
     Raises on anything else. *)
  val binary_parts : Term.term -> Term.term * Term.term * Term.term

  val demult :
    Term.term * Arbrat.rat -> Term.term option * Arbrat.rat
  val decomp : Term.term -> linarithSolve.decomp option
  val is_nonnegative : Term.term -> bool
  val is_relevant : Term.term -> bool
end
