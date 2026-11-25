signature benchDerive =
sig
  (* The recipe an entry's Isabelle method calls for.

     The inputs are the method string the source proof used, the
     Isabelle line the proof sits on, and the goal -- read only to
     instantiate a citation the method resolves against the goal's
     assumptions and to withhold a citation that states the goal.
     Nothing is read that an author could tune per goal: citations
     resolve through the global [benchNames] table and method heads
     through [benchTactics], both keyed by name alone, and the ambient
     context is one set for the whole corpus cut by that mined line.  A
     goal therefore cannot be handed an argument its source proof never
     named, nor one that was not yet declared where it was proved. *)
  val recipe : benchLib.source_goal -> benchLib.method_recipe

  (* [recipe] on the three fields it actually reads, for a caller
     holding a goal that has already been prepared.  The first is the
     goal's Isabelle line, "src/HOL/<theory>.thy:<line>". *)
  val recipe_of : string -> Term.term -> string -> benchLib.method_recipe

  (* The citations dropped from an entry's recipe because their HOL4
     theorem is the goal.  Empty for all but a handful of goals whose
     translation collapses two Isabelle facts onto one HOL4 theorem;
     those goals are still measured, but without a fact the Isabelle
     proof had.  A theorem the recipe carries twice is named once. *)
  val self_supplied : benchLib.source_goal -> string list

  (* [self_supplied] on the three fields it reads, for a goal that has
     already been prepared. *)
  val self_supplied_of : string -> Term.term -> string -> string list

  (* Every authored goal of one family, with its derived recipe and
     exclusions attached and checked.  This is the only route from what
     a corpus file writes to what the harness runs; [family] appears in
     the error a rejected entry raises. *)
  val prepare :
    string -> benchLib.source_goal list -> benchLib.corpus_goal list
end
