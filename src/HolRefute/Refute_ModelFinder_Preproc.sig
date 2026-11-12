signature Refute_ModelFinder_Preproc = sig
  type term = Term.term

  type context = Refute_ModelFinder_HOL.mf_context

  (* How many axioms a problem may collect. *)
  val axioms_max_count : int ref

  val preprocess_formulas :
    context -> term list -> term ->
    term list * term list * term list * bool * bool * bool
end
