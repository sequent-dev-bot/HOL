signature orderData =
sig
  include Abbrev

  (* The order axioms a goal supplies for one relation, each as a
     theorem about that relation.  They are held one at a time because
     a goal may carry [transitive] without [antisymmetric], and a step
     that needs only transitivity should not be refused for that. *)
  type axioms =
    {reflexive : thm option,
     transitive : thm option,
     antisymmetric : thm option,
     total : thm option}

  (* A relation with the axioms in hand.  [reduction] is applied to
     every candidate fact and every goal before it is read: it is the
     identity for a relation that arrived weak, and rewrites a strict
     primitive into the strict part of its own reflexive closure
     otherwise, so the procedure works with one shape of context.  It
     is a conversion rather than a rule because a goal has to be
     carried back to the spelling it was posed in. *)
  type context =
    {relation : term,
     axioms : axioms,
     reduction : conv}

  (* [tm = tm'], the reading the procedure works in. *)
  val reduce : context -> term -> thm
  val normalise : context -> thm -> thm

  datatype literal =
      Weak of term * term
    | Strict of term * term
    | Equal of term * term
    | Distinct of term * term

  (* A literal with the theorem that states it in the normalised
     spelling: [R x y] for Weak, [STRORD R x y] for Strict, and the
     equation or its negation for the other two. *)
  type fact = {literal : literal, theorem : thm}

  (* The meter charges each source theorem and conjunct normalization,
     candidate scan and derived rule application. *)
  type meter = searchBudget.charger

  (* Every relation the theorems supply order axioms for.  A relation
     with no transitivity yields no context: nothing can be chained
     for it, so a search that kept it would only cost time. *)
  val contexts : meter -> thm list -> context list
  val contexts_unmetered : thm list -> context list

  (* Whether the theorems name an order predicate at all.  A decision
     procedure consulted on every atom of every goal has to answer this
     before it does anything, and answering it costs one walk over the
     conclusions rather than a rewrite of each. *)
  val has_order_axiom : thm list -> bool

  (* The literal a term states, read positively.  A negated relational
     atom has no positive reading and yields NONE: turning one round is
     what totality is for, and that happens to a fact and not to a
     target.  [is_literal] is the companion guard, on the other side
     from [has_order_axiom]: it keeps the procedure off the atoms that
     are not about its relation. *)
  val literal_of_term : context -> term -> literal option
  val is_literal : context -> term -> bool

  (* A reader shares derived rules across the theorems it reads. *)
  val facts_of : meter -> context -> thm -> fact list
  val facts_of_all : meter -> context -> thm list -> fact list
end
