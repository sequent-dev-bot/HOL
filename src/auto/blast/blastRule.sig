signature blastRule =
sig
  type hol_term = Term.term
  type thm = Thm.thm
  type goal = Abbrev.goal
  type pterm = blastTerm.term
  type var = blastTerm.var

  datatype origin =
      Stored of {is_elim : bool, theorem : thm}
    | ImpIntro
    | AllIntro

  type tableau_rule =
    {origin : origin,
     pattern : pterm,
     premises : pterm list list,
     (* Parallel to premises.  SOME n records the typed elimination
        antecedent ~F which tableau conversion hides after n visible
        antecedents; exact replay still retains that assumption. *)
     hidden_assumptions : int option list}

  (* blast.trace.  A search is given its level, which the tactics read
     from their context with traceUtil.level_of. *)
  val tracer : traceUtil.tracer

  (* A cache belongs to one tableau search.  Cached rule templates are
     instantiated freshly on retrieval because their variables are mutable.
     It is made with the search's blast.trace level, at which conversion
     reports the elimination rules it drops. *)
  type cache
  val newCache : traceUtil.level -> cache
  val conversionCount : cache -> int
  val hitCount : cache -> int

  (* HOL4 goals have no schematic term variables.  Thus the four TRANS
     failures in Isabelle's fromSubgoal are vacuous here: free term
     variables become nullary Skolems and free type variables stay rigid. *)
  val fromGoalTerm : hol_term -> pterm
  val initialBranch : goal -> pterm list
  val initialBranchMeasured :
    (unit -> unit) -> goal -> pterm list

  (* Conversion hooks are public for focused tests and diagnostics.  Normal
     clients acquire clauses through safeRules and unsafeRules. *)
  val convertIntro : cache -> var list -> thm -> tableau_rule
  val convertElim : cache -> var list -> thm -> tableau_rule option

  val safeRules :
    cache -> clasetLib.claset -> var list -> pterm -> tableau_rule list
  val unsafeRules :
    cache -> clasetLib.claset -> var list -> pterm -> tableau_rule list

  (* Search monitoring is deliberately confined to these measured rule
     acquisition entry points.  candidate records a tagged rule presented
     for conversion, conversion records the start of that conversion, and
     checkpoint may cooperatively interrupt net edges and result appends,
     ordering/partitioning, canonical theorem and HOL/type translation,
     quantified/bound-variable conversion, or cache-template copying.
     Individual kernel and persistent map/set operations remain indivisible.
     Acquisition polls before invoking either counter hook. *)
  type monitor =
    {candidate : unit -> unit,
     conversion : unit -> unit,
     checkpoint : unit -> unit}
  val safeRulesMeasured :
    monitor -> cache -> clasetLib.claset -> var list -> pterm ->
    tableau_rule list
  val unsafeRulesMeasured :
    monitor -> cache -> clasetLib.claset -> var list -> pterm ->
    tableau_rule list

  (* Premises that share an unbound variable are not independent for a
     search that attempts their branches in order: the branch attempted
     first decides the shared variable and its sibling inherits that
     decision.  [rotatePremises k rule] restates the rule with premise [k]
     leading, relative order otherwise kept, so a search may attempt the
     split the other way round.  The stored theorem is permuted with the
     premises, which keeps a recorded application replayable subgoal by
     subgoal.  NONE when the rule has no stored theorem to permute. *)
  val rotatePremises : int -> tableau_rule -> tableau_rule option

  (* Introduction-rule duplication is deliberately absent: with delayed
     unsafe rules that arm is dead (Isabelle blast.ML:537-539). *)
  val replayTheorem : tableau_rule -> bool -> thm option
end
