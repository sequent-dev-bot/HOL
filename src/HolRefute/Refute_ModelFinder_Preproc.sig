signature Refute_ModelFinder_Preproc = sig
  type term = Term.term

  type context = Refute_ModelFinder_HOL.mf_context

  (* The boxing pass and a hook that sees each
     input and output of it. *)
  val box_fun_and_pair_in_term : context -> bool -> term -> term
  val box_check : (context -> bool -> term -> term -> unit) ref
  (* The pass that reduces what boxing leaves (selectors of constructors,
     redexes); two boxed terms mean the same when they are alpha-equivalent
     after it. *)
  val after_boxing : context -> term -> term

  val is_generated_const : term -> bool

  (* [deviation from upstream] A test sees each preprocessed problem. *)
  val preprocess_check :
    ((unit -> context) -> context -> term ->
     term list * term list * term list * bool * bool * bool -> unit) ref

  val preprocess_formulas :
    context -> term list -> term ->
    term list * term list * term list * bool * bool * bool

  (* The same, reporting each pass, and each
     axiom of a pass over the axioms, to the function before it starts;
     the observer of a test sees the text after it. *)
  val pass_observer : (string -> unit) ref
  val preprocess_formulas_noting :
    (string -> unit) -> context -> term list -> term ->
    term list * term list * term list * bool * bool * bool
end
