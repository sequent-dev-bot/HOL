signature benchLib =
sig
  include Abbrev

  type provenance = {file : string, line : int, commit : string}

  datatype tactic_id =
      Simp
    | Auto
    | Blast
    | Force
    | Fastforce
    | Safe
    | Clarify
    | Clarsimp
    | Aesop
    | Metis
    | Linarith

  type named_thm = {name : string, theorem : thm}

  datatype rule_strength = SafeRule | UnsafeRule

  datatype method_arg =
      RewriteAdd of named_thm
      (* The same rewrite, installed so that the traversal offers it a
         subject the other rules have finished with.  HOL4 rewrites the
         outermost redex first, so a rule whose left side reads an
         arbitrary term of its subject's type -- [set_zip], which reads
         any zip pointwise -- fires above every rule about the subject's
         own head and re-embeds the subject where none of them match.
         Isabelle rewrites the innermost redex first and so offers such
         a rule nothing but a normal subject.  Which citations take this
         is recorded in [benchNames], once per rule and never per goal;
         the argument is the same theorem under the same name. *)
    | RewriteAddBottomUp of named_thm
    | RewriteDelete of string
    | SplitAdd of named_thm
    | IntroAdd of rule_strength * named_thm
    | ElimAdd of rule_strength * named_thm
    | DestAdd of rule_strength * named_thm
    | CongruenceAdd of named_thm
    | FactAdd of named_thm
    | DefinitionAdd of named_thm
      (* Isabelle's [iff]: one attribute that puts the equivalence in
         the simpset and the rules derived from it in the claset, so
         the argument reaches a method reading either half. *)
    | IffAdd of named_thm

  (* [Repeat] is Isabelle's method combinator [+]: the recipe runs once
     and then as often as it keeps applying. *)
  datatype method_recipe =
      Invoke of tactic_id * method_arg list
    | Then of method_recipe * method_recipe
    | AllGoals of method_recipe * method_recipe
    | Repeat of method_recipe

  type exclusion = {name : string, theorem : thm}

  (* What a corpus file authors.  There is no recipe field and no
     exclusion field, so neither can be written against a particular
     goal: both are derived, by [benchDerive.prepare], from the
     Isabelle method string and the goal alone. *)
  type source_goal = {
    id : string,
    goal : term,
    source_method : string,
    provenance : provenance,
    representative : bool
  }

  (* A source goal with its derived recipe and exclusions attached.
     Only [benchDerive.prepare] builds one. *)
  type corpus_goal = {
    id : string,
    goal : term,
    source_method : string,
    recipe : method_recipe,
    excl : exclusion list,
    provenance : provenance,
    representative : bool
  }

  datatype outcome = SOLVED of Time.time | TIMEOUT | FAILED of string

  datatype cause =
      AcceptedGap
    | EngineLimitation
    | TranslationGap
    | UnderIteration

  type shortfall = {
    id : string,
    cause : cause,
    date : string,
    note : string
  }

  type family_result = {
    gated : (string * outcome) list,
    (* Search work per gated goal, in the same order as [gated].  A
       solve at 28 seconds is not parity with a method that returns in
       milliseconds, and the outcome alone cannot tell them apart. *)
    work : (string * searchWork.work) list,
    battery : (string * tactic_id * outcome) list
  }

  val default_budget : Time.time
  val selftest_level : unit -> int
  val tactic_name : tactic_id -> string
  val recipe_name : method_recipe -> string
  val cause_name : cause -> string
  val outcome_solved : outcome -> bool

  (* A term with its conjunctions and disjunctions reordered, its
     equations and equivalences turned round, and its free variables
     numbered by first occurrence.  Two terms with the same normal
     form state the same thing. *)
  val statement_normal_form : term -> term

  (* The translation's definitional equations.  [benchAmbient] installs
     them, because the theory that holds them is built above this
     module, and [theorem_is_goal] compares under them: a corpus goal
     wears the translation's constants where an ambient rule wears
     HOL4's, and without the unfolding the two never look alike.  With
     nothing installed the comparison is the plain syntactic one. *)
  val set_definitional_context : thm list -> unit
  val definitional_theorems : unit -> thm list

  (* The ambient correspondences: conditional equivalences between a
     translated predicate and the HOL4 predicate the ambient set
     rewrites goals into.  [benchAmbient] installs them, for the reason
     it installs the definitional context.  A recipe's own rules are
     offered on both sides of each one, in the same role: the goal is
     rewritten across the correspondence and a rule stated on the
     translated side would otherwise no longer meet it.  With nothing
     installed a recipe carries exactly the rules it cites. *)
  val set_correspondences : thm list -> unit
  val across_correspondence :
    corpus_goal -> method_arg list -> method_arg list

  (* [term] with the installed definitions unfolded, to a fixed depth. *)
  val unfolded : term -> term

  (* True when the theorem states the goal -- as written, or under the
     installed definitions. *)
  val theorem_is_goal : term -> thm -> bool

  val method_arg_name : method_arg -> string
  val named_theorem : method_arg -> named_thm option
  val recipe_arguments : method_recipe -> method_arg list

  (* True of the methods that consult the source theory's default
     simpset.  Isabelle's [blast], [safe], [clarify] and [metis], and
     its arithmetic decision procedures, do not: they take
     the claset, the facts they are handed, or nothing but the goal.
     The distinction is not cosmetic here -- a benchmark tactic given a
     non-empty argument list runs a simplification pass that a source
     proof using one of those methods never had. *)
  val consults_simpset : tactic_id -> bool

  (* True of the methods that consult the source theory's default
     claset.  It is a different set: Isabelle's [simp] does not read
     one, and [blast], [safe] and [clarify] read nothing else.  The two
     halves of the ambient context go to their own methods. *)
  val consults_claset : tactic_id -> bool

  (* True of an argument that goes to a claset rather than a simpset,
     which is what decides which half of the ambient context it is. *)
  val claset_argument : method_arg -> bool

  (* True of an [iff] argument, which goes to both halves. *)
  val iff_argument : method_arg -> bool

  (* Whether an argument reaches a method at all: a claset argument
     only where the method reads a claset, a simpset one only where it
     reads a simpset, and an [iff] wherever either holds.  This is the
     filter the ambient context passes through. *)
  val argument_reaches : tactic_id -> method_arg -> bool

  (* False of an argument whose theorem is the goal being measured --
     the check [validate_raw_goal] raises on.  Exported so that a
     caller deriving a recipe can drop such an argument rather than
     build one that will be rejected. *)
  val permitted_for : term -> method_arg -> bool
  (* Reuse citation readings for the corpus's recurring ambient arguments. *)
  val set_ambient_citations : method_arg list -> unit
  val argument_name : method_arg -> string

  val validate_raw_goal : corpus_goal -> unit
  val validate_raw_goals : string -> corpus_goal list -> unit
  (* Attaches a derived recipe to an authored goal and works out the
     exclusions it needs.  The recipe is a parameter rather than
     something this computes, because the derivation sits above this
     module; [benchDerive.prepare] is the only intended caller. *)
  val prepare_goal : method_recipe -> source_goal -> corpus_goal

  val exclusions_effective :
    clasetLib.claset -> corpus_goal -> bool

  (* Runs the thunk under a budget that preempts it, NONE on expiry. *)
  val within_budget : Time.time -> (unit -> 'a) -> 'a option
  val run_goal : Time.time -> method_recipe -> corpus_goal -> outcome
  (* Uses the same execution and timeout path as run_goal with a
     supplied clock and wrapper around simpset preparation. *)
  val run_goal_with_timing :
    {now : unit -> Time.time,
     prepare : (unit -> simpLib.simpset) -> simpLib.simpset} ->
    Time.time -> method_recipe -> corpus_goal -> outcome

  val assert_accounting : {
    family : string,
    goals : corpus_goal list,
    shortfalls : shortfall list,
    gated : (string * outcome) list
  } -> unit

  (* [run_family] measures the family it is given.  [run_corpus_family]
     first drops the goals the run's environment restricts it to --
     HOLBENCHSHORTFALLSONLY and HOLBENCHFAMILY with HOLBENCHGOAL -- so
     a debugging restriction reaches the corpus and not the families
     the selftest builds by hand to measure the harness with. *)
  type restriction = {
    shortfalls_only : bool,
    goals_wanted : (string * string list) option
  }

  val restrict : restriction -> {
    family : string,
    goals : corpus_goal list,
    shortfalls : shortfall list
  } -> corpus_goal list

  val run_family : {
    family : string,
    goals : corpus_goal list,
    shortfalls : shortfall list,
    budget : Time.time,
    battery : tactic_id list,
    level : int
  } -> family_result

  val run_corpus_family : {
    family : string,
    goals : corpus_goal list,
    shortfalls : shortfall list,
    budget : Time.time,
    battery : tactic_id list,
    level : int
  } -> family_result
end
