structure benchSetShortfalls =
struct

(* Every record here is an executable Set.thy or Set_Theory.thy goal
   that the assigned tactic did not close in the 2026-08-28
   measurement.  The classification names the root cause and the note
   says what stands in the way.  A goal listed in [over_budget] was
   still searching when the budget expired, so its classification is
   the family it belongs to rather than an observed residual. *)

val over_budget =
  ["set_L1607_Pow_insert",
   "set_L1847_is_singleton_the_elem",
   "set_L1610_Pow_Compl"]

fun record note id : benchLib.shortfall =
  {id = id, cause = benchLib.EngineLimitation, date = "2026-08-28",
   note =
     if List.exists (fn other => other = id) over_budget then
       note ^ " (the search exceeded the budget rather than " ^
       "reporting no proof)"
     else
       note}

fun classified classification note ids =
  map (record (classification ^ ": " ^ note)) ids

(* The class this goal was in was named for a rule form, and none of
   the three goals in it had that cause.  [set_theory_L168] was the
   goal that did, and a singleton introduction closed it;
   [set_L1125_image_Pow_surj] was the corpus's own set-equality pass
   dissolving a hypothesis the search would have substituted, and
   leaving the pass that equation closes it; [set_L1607_Pow_insert] is
   the witness its method supplies, which is where it now stands.
   What is left is one goal and a cause of its own. *)
val translated_fact_unfolded =
  classified "translated fact unfolded"
    ("the goal withholds no ambient analogue at all, so the earlier "
     ^ "reading -- that excluding the goal's own characterisation "
     ^ "left no second route -- was wrong for it.  What comes back "
     ^ "in 0.331s is a residual in which the translation's own "
     ^ "[source_add_image] stands folded, with nothing stated on "
     ^ "it for the search to meet -- the recipe its [by auto] method "
     ^ "compiles to carries [source_image_def] and no equation for "
     ^ "[source_add_image] at all: the obstruction is the shape of "
     ^ "the translated fact and not the strength of the method")
    ["set_L994_image_add_0"]

val disjnt =
  classified "disjnt"
    ("pred_set declares the goal itself, DISJOINT_INSERT, [simp], so "
     ^ "rule A1 withholds it, and the assigned method is simp alone.  "
     ^ "What the remaining rewrites leave is the same equivalence in "
     ^ "membership form, which a rewriter cannot close -- though it is "
     ^ "not out of first-order reach: AUTO_TAC and BLAST_TAC each "
     ^ "close that residual.  The membership form is the obstacle: the "
     ^ "ambient normalisation of an equation with the empty set "
     ^ "dissolves the intersection before any rule stated on it can "
     ^ "apply.  Withholding that normalisation while supplying "
     ^ "pred_set's INSERT_INTER lets simp alone close the first of "
     ^ "these; the second inserts on the right, and pred_set states "
     ^ "no mirror of INSERT_INTER.  That route is not worth its cost: "
     ^ "restricting the normalisation to a set former, as Isabelle "
     ^ "states it, costs five goals whose left-hand side is not a "
     ^ "former, and supplying INSERT_INTER alongside the unrestricted "
     ^ "normalisation gains nothing, since the normalisation reaches "
     ^ "the term first")
    ["set_L1988_disjnt_insert1", "set_L1991_disjnt_insert2"]

val definite_description_specified =
  classified "definite description"
    ("the source method cites [the_elem_def], an equation -- "
     ^ "[the_elem A = (THE a. A = {a})] -- and its simp closes the "
     ^ "goal by unfolding it.  HOL4 introduces CHOICE by "
     ^ "new_specification, and the fact of that name, [CHOICE_DEF], "
     ^ "is the conditional membership [s <> {} ==> CHOICE s IN s]: "
     ^ "the cited fact translates by name and not by content, and "
     ^ "nothing in it reaches the goal's left-hand side.  The "
     ^ "equation that would is the goal itself, [CHOICE_SING], which "
     ^ "rule A1 withholds.  The method returns the goal unchanged in "
     ^ "0.1s rather than searching, and Isabelle's own simp fails the "
     ^ "same way where the constant is specified rather than defined "
     ^ "(checked there on an axiomatized choice constant), so what is "
     ^ "missing is the shape of the cited fact and not the strength "
     ^ "of the method")
    ["set_L1844_the_elem_eq"]

val definite_description_reading =
  classified "definite description"
    ("the assigned tactic and its rewrites close this goal as stated "
     ^ "in 0.012s.  What does not close is the reading the corpus's "
     ^ "own set-equality pass imposes before the engine sees it: each "
     ^ "of the goal's two equations has a singleton on one side, a "
     ^ "constant the simpset states a membership fact about, so the "
     ^ "pass takes both to their membership form, and the search does "
     ^ "not return on [(?b. !x. x IN A <=> x IN {b}) <=> "
     ^ "(!x. x IN A <=> x IN {CHOICE A})] -- nor does Isabelle's auto "
     ^ "on that same reading, which it has no pass to reach and which "
     ^ "was killed at 54s unfinished.  The membership reading is what "
     ^ "brings HOL4's set facts within reach of a goal stated as an "
     ^ "equation, and on this goal it is the loss; standing the pass "
     ^ "down for the shape is a corpus decision to be measured across "
     ^ "the families, not an engine gap")
    ["set_L1847_is_singleton_the_elem"]

val instantiated_fact_citation =
  classified "instantiated fact citation"
    ("the source method instantiates its cited facts with [OF "
     ^ "...] and [of ...]; the recipe compiler represents a "
     ^ "citation but not its instantiation")
    ["set_theory_L79"]

(* src/HOL/Set.thy:1610 @ f7e02b7e.  The source method supplies the
   existential witness ([blast intro: exI [where ?x = "- u" for u]]) and
   the recipe compiler represents a citation but not its instantiation,
   so the search has to guess it.  The guess is what the union
   membership rules meet: a branch guessing a witness leaves a
   membership whose set it has not decided, and [BIGUNION_E_AUTO]'s
   major premise unifies with such a literal by deciding it.  Measured:
   89 tableau branches and 0.038s with the two eliminations out of the
   claset, 1370 branches and past the budget with them.  They stay --
   Isabelle declares both [elim!] and they are what closes
   [set_L928_subset_image_iff] and [set_theory_L48] -- so what is left
   here is the witness the method was given and the recipe was not. *)
(* src/HOL/Set.thy:1607 @ f7e02b7e.  [Pow_insert]'s method supplies a
   witness the same way ([blast intro: image_eqI [where ?x = "u - {a}"
   for u]]), and the supply is load-bearing rather than decoration:
   measured against Isabelle itself, its own [blast] closes the goal
   in under a second with the instantiation and does not return in
   300s with the method reduced to bare [blast].  What the recipe
   compiler cannot represent is therefore the whole of the gap. *)
val witness_the_method_supplies : benchLib.shortfall list =
  map
    (fn (id, date) =>
      {id = id, cause = benchLib.EngineLimitation, date = date,
       note =
         "witness the method supplies: the source method instantiates " ^
         "the introduction with the witness; the recipe compiler " ^
         "represents a citation but not its instantiation, so the " ^
         "search guesses it, and the membership rules Isabelle " ^
         "declares [elim!] meet the undetermined membership the guess " ^
         "leaves behind (the search exceeded the budget rather than " ^
         "reporting no proof)"})
    [("set_L1610_Pow_Compl", "2026-09-12"),
     ("set_L1607_Pow_insert", "2026-09-21")]

val entries : benchLib.shortfall list =
  translated_fact_unfolded @
  disjnt @
  definite_description_specified @
  definite_description_reading @
  instantiated_fact_citation @
  witness_the_method_supplies

end
