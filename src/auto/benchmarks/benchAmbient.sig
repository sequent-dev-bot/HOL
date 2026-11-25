signature benchAmbient =
sig
  (* The translation's definitional equations, ambient for every goal.

     A translated goal mentions constants that Isabelle introduced with
     [fun] or [definition]; the source proof never names their
     equations because an Isabelle method reads its simpset without
     naming it.  Supplying them here restores that much of the source
     context and no more.  Isabelle puts a [fun] definition in the
     default simpset and a plain [definition] not, and
     [ambient_definitions] is the subset that distinction leaves.

     The set is one theorem per mined constant, and the selftest holds
     it against what the translation theory records, so it grows only
     when a definition is added.  What reaches a goal is this same set
     cut by where the goal sits in Isabelle's theory order and by
     nothing else, so it cannot be tuned against one goal.

     [arguments] adds the lemmas below to it -- the declared results
     and one correspondence.  That correspondence is
     [source_sorted_wrt_bridge].  Isabelle's [sorted] is
     [sorted_wrt (<=)], so its simpset's facts about sorted lists reach
     the [sorted_wrt] reading with nobody naming them; HOL4 states the
     same facts about its adjacent SORTED, and the correspondence
     between the two is what the translation has to supply for the
     ambient context to mean the same thing on both sides.  It is
     conditional on transitivity, and the bridge reads left to right,
     so it fires wherever that condition can be discharged: by the
     assigned method itself, or from the source linorder premise the
     goals carry, which the order-premise seeds put within reach of the
     simplifier's own condition solver.  That is sound, the two
     predicates agreeing under transitivity, and it costs a goal only
     where a cited rule is left on the far side; the crossing below is
     what keeps those rules usable. *)
  val definitions : benchLib.named_thm list

  (* True of a theorem that states equations, which is what a definition
     contributes to a simpset.  A translated type's [TY_DEF] predicate
     is not one.  The selftest reads the translation theory through it
     to check nothing the theory defines is missing above. *)
  val equational : Term.term -> bool

  (* The subset of [definitions] whose equations Isabelle's own simpset
     carries.  [benchIsabelleAmbient] records how Isabelle introduces
     each translated constant, one constant at a time, with the source
     line that says so, and this is the set the corpus is measured
     under. *)
  val ambient_definitions : benchLib.named_thm list

  (* The whole ambient context as recipe arguments --
     [ambient_definitions] and the lemmas below, then [declared_rules]
     -- in the order a recipe takes.  It has two halves, and each
     reaches only the methods that consult it: the rewrites go to the
     methods that read a simpset, the classical rules to those that
     read a claset. *)
  val arguments : benchLib.method_arg list

  (* [arguments] cut to what was in scope where the goal was proved,
     which is what the measurement hands a goal.  The argument is the
     goal's own Isabelle line, "src/HOL/<theory>.thy:<line>".  Isabelle
     reads a theory in order and sees only what it imports, so a result
     declared below a proof, or in a theory that imports the proof's
     rather than the other way round, was not in that proof's simpset
     or claset: [Pow_Compl] at Set.thy:1610 had nothing about [Sigma],
     which Product_Type introduces.  Neither half is free of the other
     -- a rule that cannot fire still costs a classical search the
     nodes it is tried at -- so the cut runs over both.

     The cut reads mined provenance and never the goal's statement, so
     the context still cannot be tuned against a goal.  It raises on a
     theory [benchIsabelleAmbient] has no order for. *)
  val arguments_at : string -> benchLib.method_arg list

  (* The Isabelle line each of the results and rules below is declared
     at.  Definitions answer from [benchIsabelleAmbient]; this raises on
     an argument neither table covers. *)
  val declaration_site : string -> string

  (* The results Isabelle declares simp about a translated constant,
     which its simp step has and a context of definitions alone does
     not.  Each is part of [arguments].  One that states a corpus goal
     -- two Isabelle facts can translate onto one HOL4 theorem -- is
     withheld on that goal, as a citation stating its goal is.
     [arguments] carries them read through the ambient alias
     definitions, which have already rewritten the goal by the time one
     of them is tried. *)
  val declared_results : benchLib.named_thm list

  (* The results Isabelle declares [intro]/[elim]/[dest] about a
     translated constant whose definition it withholds.  Its claset has
     them and a context of rewrites does not, and no rewrite stands in
     for one: a classical rule takes a term apart in a direction the
     simplifier will not run.  Each cites the declaration it
     transplants and carries the safety Isabelle gives it, [!] being
     safe.  The [map_add_SomeD] entry is the exception, and says in
     [benchAmbient] why its own measurement puts it the other way. *)
  val declared_rules : benchLib.method_arg list

  (* The entries of [definitions] that define one constant: every
     clause heads on the same one.  A [define_new_type_bijections]
     theorem is not one of them -- its clauses relate two constants,
     and it is a characterisation rather than an unfolding. *)
  val wrapper_definitions : benchLib.named_thm list

  (* Loading this structure installs [wrapper_definitions] as benchLib's
     definitional context, so that a rule stating a goal under the
     translation's constants is recognised as stating it.  The
     characterisations stay out: being one ambient rewrite away from a
     goal is not stating it. *)

  (* Loading it also installs [source_sorted_wrt_bridge] as benchLib's
     ambient correspondence, so a recipe's own rules are offered on both
     sides of it.  The bridge rewrites goals left to right; without the
     crossing a rule cited in the translation's spelling stops meeting
     the goal as soon as the bridge's transitivity condition becomes
     dischargeable. *)
end
