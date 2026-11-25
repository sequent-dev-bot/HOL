(*
  Corpus integrity detectors.

  Each detector answers one question about a benchmark entry that the
  entry itself cannot be trusted to answer.  They are reporting
  functions: a detector returns findings, and the caller decides whether
  a finding is fatal.  Detector logic and thresholds are owner-signed --
  widening one to make a run green is the defect they exist to catch.
*)
signature benchGuards =
sig
  include Abbrev

  type finding = {id : string, detector : string, detail : string}

  val finding_text : finding -> string

  (* A1.  [recognition_route goal theorem] names the route by which
     [theorem] alone closes [goal], if there is one.  A route counts only
     when the same route without the theorem fails, so an ambient
     tautology is not mistaken for recognition.  The syntactic test of
     benchLib.theorem_is_goal is a cheap accepting pre-filter. *)
  val recognition_budget : Time.time ref
  val recognition_route : term -> thm -> string option
  val recognises : term -> thm -> bool

  (* The sweep runs over the entry's own arguments and over the ambient
     context alike: a seed declared for every goal is not a recipe
     argument, but a seed that states a goal closes it by recognition
     just as a cited fact would.  An ambient candidate is judged against
     a control that already has the translation's definitions, so what
     is reported is the rule that turns the goal into a triviality, not
     the unfolding that lets it apply. *)
  val relevant_definitions : term -> thm list
  val ambient_candidates : benchLib.corpus_goal -> benchLib.named_thm list
  val recognition_findings : benchLib.corpus_goal list -> finding list

  (* A2.  Every parityTranslation$source_X argument must be named by the
     entry's Isabelle method, or be a registered definition of a constant
     of the goal. *)
  val translation_prefix : string
  val documented_suffixes : string list
  val method_names : string -> string list
  val method_names_argument : string -> string -> bool
  val provenance_violations : benchLib.corpus_goal -> string list
  val provenance_findings : benchLib.corpus_goal list -> finding list

  (* A3.  A search method must do search work.  [work_floor] is the
     smallest total the invariant admits. *)
  val search_methods : string list
  val is_search_method : string -> bool
  val work_floor : int
  val measured_run :
    Time.time -> benchLib.corpus_goal ->
    benchLib.outcome * searchWork.work
  val search_work_findings :
    Time.time -> benchLib.corpus_goal list -> finding list

  (* A4.  A translation lemma used by exactly one corpus goal must be
     named by that goal's method. *)
  val translation_uses :
    benchLib.corpus_goal list -> (string * string list) list
  val single_use_findings : benchLib.corpus_goal list -> finding list

  (* A5.  Hand-mapped display names in benchExplicit.  A special case is
     admissible only when it renders a real lemma under a documented
     Isabelle attribute; a fabricated name, a fabricated attribute marker,
     a goal-shaped alias, and a name that resolves to a theorem other than
     the one it maps to are all reported. *)
  val documented_attributes : string list
  val alias_findings : unit -> finding list

  (* A6.  Structural goal-statement pin.  The signature is de Bruijn for
     bound variables and carries theory-qualified constants and full
     types, so it is invariant under printer changes and under bound
     variable renaming, and nothing else. *)
  val goal_signature : term -> string
  val family_hash : benchLib.corpus_goal list -> string
end
