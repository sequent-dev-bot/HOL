signature linarithSolve =
sig
  datatype relation = REL_LE | REL_LT | REL_EQ | REL_NEQ

  (* negated says the relation appeared under a negation, and only the
     order relations ever carry it: linarithDecomp.decomp turns a
     negated equality into REL_NEQ with negated = false, and REL_NEQ has
     no negated form because ~(x <> y) is not a relation this layer
     recognises.  So a producer of a decomp -- decomp, less_decomp,
     swap_less, or a caller building one directly -- must present an
     equation as REL_EQ and a disequation as REL_NEQ, both unnegated.
     Row building reads the invariant rather than restating both
     encodings. *)
  datatype decomp = Decomp of {
    lhs : (Term.term * Arbrat.rat) list,
    lhs_const : Arbrat.rat,
    rel : relation,
    rhs : (Term.term * Arbrat.rat) list,
    rhs_const : Arbrat.rat,
    discrete : bool,
    negated : bool
  }

  (* Asm indexes the assumption list replay is given; Nonneg carries
     the atom itself, whose own instance supplies its theorem. *)
  datatype injust =
      Asm of int
    | Nonneg of Term.term
    | LessD of injust
    | NotLessD of injust
    | NotLeD of injust
    | NotLeDD of injust
    | Multiplied of Arbint.int * injust
    | Added of injust * injust

  type linarith_config = linarithData.linarith_config

  (* The atom ordering that coefficient rows follow. *)
  val atoms_of_decomps : decomp list -> Term.term list

  val negate : Term.term -> Term.term

  (* The first argument of each is the linarith.trace level the search
     reports at.  The flag reports whether disequalities were split:
     when it is true there is one justification per case, in the order
     the cases are generated, and the caller must reproduce that case
     split. *)
  val prove :
    traceUtil.level -> linarith_config -> (Term.term -> decomp option) ->
    (Term.term -> bool) -> Term.term list -> Term.term ->
    bool * injust list option

  (* prove is this applied to its decomposed hypotheses.  A caller that
     asks the same question repeatedly about one fixed hypothesis set
     decomposes that set once and calls this directly; the negated
     conclusion is still decomposed per call, since it varies. *)
  val prove_decomposed :
    traceUtil.level -> linarith_config -> (Term.term -> decomp option) ->
    (Term.term -> bool) -> (Term.term * decomp option) list ->
    Term.term -> bool * injust list option

  datatype budget_outcome =
      CertificateFound of
        {split_neq : bool, justifications : injust list}
    | CertificateExhausted
    | CertificateLimitReached of
        {kind : searchBudget.kind, usage : searchBudget.usage}

  (* Candidate work covers coefficient, row, atom, and case scans;
     applications admit row-pair elimination and disequality branches;
     normalization admits decomposition and row construction.  These
     are certificate-search outcomes, not yet kernel proof outcomes. *)
  val prove_budgeted :
    traceUtil.level -> searchBudget.budget -> linarith_config ->
    (Term.term -> decomp option) -> (Term.term -> bool) ->
    Term.term list -> Term.term -> budget_outcome
  val prove_decomposed_budgeted :
    traceUtil.level -> searchBudget.budget -> linarith_config ->
    (Term.term -> decomp option) -> (Term.term -> bool) ->
    (Term.term * decomp option) list -> Term.term -> budget_outcome
end
