(* A supplied theorem and its application views belong to one tactic
   invocation.  Consumers retain the source when deriving further views. *)
signature clasetFacts =
sig
  type term = Term.term
  type hol_type = Type.hol_type
  type thm = Thm.thm

  type fact
  type environment
  type view =
    {source_id : int, source : thm, theorem : thm,
     support : term list}

  (* Fixed variables are genuine free variables shared with the initial
     goal, plus variables in theorem support.  Other genuine free
     variables and loose type variables are freshened separately for each
     citation.  Quantified variables remain quantified until a consumer
     applies the theorem. *)
  val create : Abbrev.goal -> thm list -> environment
  (* Charge fact classification as Candidate and first construction of
     each cached schematic view as Normalization. *)
  val create_with_charge :
    (searchBudget.kind -> unit) ->
    Abbrev.goal -> thm list -> environment
  val facts : environment -> fact list
  val source_id : fact -> int
  val source : fact -> thm
  val support : fact -> term list
  val fixed_terms : fact -> term list
  val fixed_types : fact -> hol_type list
  (* A consumer that fixes assumption types needs another theorem view
     to use this fact at a carrier exposed after the initial goal. *)
  val has_schematic_types : fact -> bool
  (* Literal compatibility keeps the source theorem and its support.
     Schematic views are fresh within this invocation. *)
  val literal_view : fact -> view
  val literal_views : environment -> view list
  val schematic_view : fact -> view
  val schematic_views : environment -> view list
  (* A conversion transports only the derived theorem. Its source ID and
     original theorem remain attached; support follows all hypotheses of
     the certified result, including new rewrite obligations. *)
  val transport_view : Abbrev.conv -> view -> view
  (* Match a consumer-selected subterm against a current application
     site.  Fixed parameters and support types cannot be instantiated. *)
  val match_view : fact -> term -> term -> view option
  (* Search compiles conditional facts as rules only when their original
     conclusion has a top-level implication after specialization.  The
     schematic view is constructed only for eligible facts. *)
  val implication_rule_view : fact -> view option
  (* Aesop's assumption normalizer may use equations, including
     conditional equations and equational conjuncts, without erasing
     propositional facts needed by forward inference.  Filter before
     constructing schematic views; derived conjuncts keep source ID and
     hypothesis support. *)
  val equational_views : environment -> view list
end
