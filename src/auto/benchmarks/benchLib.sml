structure benchLib :> benchLib =
struct

open Abbrev HolKernel

(* All simplifier flows in this harness use clasimp's extension simpsets.
   This local spelling deliberately denotes the extension API, including
   fragment registration and SF transport, before any rule installation. *)

val ERR = mk_HOL_ERR "benchLib"

(* Force the post-boss carrier registrations into every benchmark image. *)
val _ =
  (intLinarith.instance, realLinarith.instance, ratLinarith.instance)

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
  | RewriteAddBottomUp of named_thm
  | RewriteDelete of string
  | SplitAdd of named_thm
  | IntroAdd of rule_strength * named_thm
  | ElimAdd of rule_strength * named_thm
  | DestAdd of rule_strength * named_thm
  | CongruenceAdd of named_thm
  | FactAdd of named_thm
  | DefinitionAdd of named_thm
  | IffAdd of named_thm

datatype method_recipe =
    Invoke of tactic_id * method_arg list
  | Then of method_recipe * method_recipe
  | AllGoals of method_recipe * method_recipe
  | Repeat of method_recipe

type exclusion = {name : string, theorem : thm}

type source_goal = {
  id : string,
  goal : term,
  source_method : string,
  provenance : provenance,
  representative : bool
}

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
  work : (string * searchWork.work) list,
  battery : (string * tactic_id * outcome) list
}

val default_budget =
  case Option.mapPartial Int.fromString
         (OS.Process.getEnv "HOLBENCHBUDGET") of
      SOME seconds =>
        if seconds > 0 then Time.fromSeconds (LargeInt.fromInt seconds)
        else Time.fromSeconds 30
    | NONE => Time.fromSeconds 30

fun selftest_level () =
  case OS.Process.getEnv "HOLSELFTESTLEVEL" of
      NONE => 1
    | SOME text =>
        (case Int.fromString text of SOME level => level | NONE => 1)

fun tactic_name Simp = "simp"
  | tactic_name Auto = "AUTO_TAC"
  | tactic_name Blast = "BLAST_TAC"
  | tactic_name Force = "FORCE_TAC"
  | tactic_name Fastforce = "FASTFORCE_TAC"
  | tactic_name Safe = "SAFE_TAC"
  | tactic_name Clarify = "CLARIFY_TAC"
  | tactic_name Clarsimp = "CLARSIMP_TAC"
  | tactic_name Aesop = "AESOP_TAC"
  | tactic_name Metis = "AMBIENT_METIS_TAC"
  | tactic_name Linarith = "LINARITH_TAC"

fun strength_name SafeRule = "safe"
  | strength_name UnsafeRule = "unsafe"

fun named_arg constructor ({name, ...} : named_thm) =
  constructor ^ "(" ^ name ^ ")"

fun strength_arg constructor strength ({name, ...} : named_thm) =
  constructor ^ "-" ^ strength_name strength ^ "(" ^ name ^ ")"

fun method_arg_name (RewriteAdd theorem) = named_arg "rewrite" theorem
  | method_arg_name (RewriteAddBottomUp theorem) =
      named_arg "rewrite-bottom-up" theorem
  | method_arg_name (RewriteDelete name) = "rewrite-delete(" ^ name ^ ")"
  | method_arg_name (SplitAdd theorem) = named_arg "split" theorem
  | method_arg_name (IntroAdd (strength, theorem)) =
      strength_arg "intro" strength theorem
  | method_arg_name (ElimAdd (strength, theorem)) =
      strength_arg "elim" strength theorem
  | method_arg_name (DestAdd (strength, theorem)) =
      strength_arg "dest" strength theorem
  | method_arg_name (CongruenceAdd theorem) = named_arg "cong" theorem
  | method_arg_name (FactAdd theorem) = named_arg "fact" theorem
  | method_arg_name (DefinitionAdd theorem) = named_arg "definition" theorem
  | method_arg_name (IffAdd theorem) = named_arg "iff" theorem

fun recipe_name recipe =
  let
    fun render (Invoke (tactic_id, args)) =
          tactic_name tactic_id ^
          (if null args then ""
           else "[" ^ String.concatWith ", " (map method_arg_name args) ^
                "]")
      | render (Then (left, right)) =
          "then(" ^ render left ^ ", " ^ render right ^ ")"
      | render (AllGoals (left, right)) =
          "all-goals(" ^ render left ^ ", " ^ render right ^ ")"
      | render (Repeat inner) = "repeat(" ^ render inner ^ ")"
  in
    render recipe
  end

fun recipe_uses predicate (Invoke (tactic_id, _)) = predicate tactic_id
  | recipe_uses predicate (Then (left, right)) =
      recipe_uses predicate left orelse recipe_uses predicate right
  | recipe_uses predicate (AllGoals (left, right)) =
      recipe_uses predicate left orelse recipe_uses predicate right
  | recipe_uses predicate (Repeat inner) = recipe_uses predicate inner

fun recipe_has_tactic wanted = recipe_uses (equal wanted)

fun linarith_stats_text () =
  let
    val {nodes, refutations, disjunction_splits,
         operator_splits, augmentations} =
      linarithLib.last_search_stats ()
  in
    String.concat
      ["linarith stats: nodes=", Int.toString nodes,
       ", refutations=", Int.toString refutations,
       ", disjunction-splits=", Int.toString disjunction_splits,
       ", operator-splits=", Int.toString operator_splits,
       ", augmentations=", Int.toString augmentations]
  end

fun cause_name AcceptedGap = "accepted-gap"
  | cause_name EngineLimitation = "engine-limitation"
  | cause_name TranslationGap = "translation-gap"
  | cause_name UnderIteration = "under-iteration"

fun outcome_solved (SOLVED _) = true
  | outcome_solved _ = false

fun outcome_text (SOLVED elapsed) = "solved:" ^ Time.toString elapsed
  | outcome_text TIMEOUT = "timeout"
  | outcome_text (FAILED message) = "failed:" ^ message

fun diagnostic_output text =
  case OS.Process.getEnv "HOLBENCHDIAGNOSTICS" of
      NONE => ()
    | SOME "1" => TextIO.print text
    | SOME path =>
        let
          val stream = TextIO.openAppend path
          val _ = TextIO.output (stream, text)
        in
          TextIO.closeOut stream
        end

fun diagnostics_enabled () =
  Option.isSome (OS.Process.getEnv "HOLBENCHDIAGNOSTICS")

fun claset_names name =
  [name,
   name ^ ".__clasimp_iff_intro",
   name ^ ".__clasimp_iff_dest",
   name ^ ".__clasimp_iff_elim"]

(* The view of the product type the translation needs: [prod.case],
   [prod.collapse], [split_paired_All] and [split_paired_Ex] are [simp]
   in Isabelle, and [prod_eq_iff] is the equation it states a pair
   equality by.  This is translation support, not a corpus theorem or a
   persistent simpset change. *)
val translation_frag =
  simpLib.name_ss "bench-translation-base"
    (simpLib.rewrites
       [pairTheory.UNCURRY_DEF, pairTheory.PAIR, pairTheory.FORALL_PROD,
       pairTheory.EXISTS_PROD, pairTheory.PAIR_FST_SND_EQ])
val translation_frag = simpLib.register_frag translation_frag
val translation_base = simpLib.SF translation_frag

(* Each primitive set operation with the membership rewrite Isabelle
   states it by.  Isabelle carries the rewrites -- [Un_iff], [Int_iff]
   and [Diff_iff] are [simp] in Set.thy -- and not the defining
   equations, and the difference is not cosmetic: unfolding a definition
   replaces the operator by a set comprehension, and every rule that
   takes a union apart, in the claset and in the simpset alike, keys on
   the operator.  Where the union sits under a constant no membership
   rewrite reaches into -- [Sigma (I UNION J) C] -- the comprehension is
   simply lost work, and [blast] is left with a goal it has no rule for.
   So the definition is supplied exactly where the goal being measured
   is the membership rewrite itself, which withholds it and leaves the
   definition the only thing to reason from. *)
val primitive_definitions =
  [(pred_setTheory.UNION_DEF, pred_setTheory.IN_UNION),
   (pred_setTheory.INTER_DEF, pred_setTheory.IN_INTER),
   (pred_setTheory.DIFF_DEF, pred_setTheory.IN_DIFF)]

(* Legacy Excl uses Thy.Name, not the kernel's Thy$Name spelling used
   by the corpus and claset. Keep it literal (and silent for a claset-only
   rule); ExclX would instead require a matching simplifier target. *)
fun rewrite_exclusion name =
  markerLib.Excl
    (case String.fields (equal #"$") name of
         [thy, rule] => thy ^ "." ^ rule
       | _ => name)

fun controls exclusions =
  List.concat
    (map
      (fn ({name, ...} : exclusion) =>
        map clasetLib.Del (claset_names name) @ [rewrite_exclusion name])
      exclusions)

local
  (* An eta-shaped binder can still fail the conversion's freshness
     check. Keep the original proof conversion for any candidate. *)
  fun has_beta_eta_candidate term =
    case Term.dest_term term of
        COMB (operator, operand) =>
          Term.is_abs operator orelse has_beta_eta_candidate operator
          orelse has_beta_eta_candidate operand
      | LAMB (binder, body) =>
          (Term.is_comb body andalso Term.aconv binder (Term.rand body))
          orelse has_beta_eta_candidate body
      | _ => false
in
  fun beta_eta_normalise term =
    if has_beta_eta_candidate term then
      boolSyntax.rhs
        (Thm.concl
          (Conv.QCONV
            (Conv.REDEPTH_CONV
              (Conv.ORELSEC (Thm.BETA_CONV, Drule.ETA_CONV))) term))
    else term
end

fun strip_normal_truth_equivalence term =
  if boolSyntax.is_eq term then
    let
      val (left, right) = boolSyntax.dest_eq term
    in
      if Term.aconv right boolSyntax.T then left
      else if Term.aconv left boolSyntax.T then right
      else term
    end
  else term

fun strip_truth_equivalence term =
  strip_normal_truth_equivalence (beta_eta_normalise term)

(* A statement is unchanged when a conjunction or a disjunction is
   reordered, when an equation or an equivalence is turned round, and
   when its free variables are renamed.  A supplied theorem that is
   the goal under those three symmetries is the goal, and comparing
   the two terms as written misses it: a translation lemma whose
   conjuncts happen to stand in the other order would close its own
   goal with nothing to report.

   The quotient is by symmetries only, so two terms with the same
   normal form do state the same thing.  It is incomplete in the other
   direction: the renaming is read off the term before the reordering,
   so two statements whose free variables first occur in different
   orders are not identified.  That direction is the safe one -- a
   missed identification leaves the pre-existing comparison in charge,
   and an identification that fires drops a citation, which can only
   ask HOL4 for more. *)
fun rename_free term =
  let
    fun numbered (variable, (index, substitution)) =
      (index + 1,
       (variable |->
          Term.mk_var
            ("%bench" ^ Int.toString index, Term.type_of variable)) ::
       substitution)
    val (_, substitution) =
      List.foldl numbered (0, []) (Term.free_vars_lr term)
  in
    Term.subst substitution term
  end

fun symmetry_normalise term =
  case Term.dest_term term of
      COMB (operator, operand) =>
        let
          fun ordinary () =
            let
              val operator' = symmetry_normalise operator
              val operand' = symmetry_normalise operand
            in
              if Portable.pointer_eq (operator, operator') andalso
                 Portable.pointer_eq (operand, operand')
              then term
              else Term.mk_comb (operator', operand')
            end
          fun sorted strip rebuild =
            rebuild (Listsort.sort Term.compare
              (map symmetry_normalise (strip term)))
        in
          if Term.is_comb operator then
            let val (head, left) = Term.dest_comb operator
            in
              if Term.same_const head boolSyntax.conjunction then
                sorted boolSyntax.strip_conj boolSyntax.list_mk_conj
              else if Term.same_const head boolSyntax.disjunction then
                sorted boolSyntax.strip_disj boolSyntax.list_mk_disj
              else if Term.same_const head boolSyntax.equality then
                let
                  val left' = symmetry_normalise left
                  val right' = symmetry_normalise operand
                in
                  case Term.compare (left', right') of
                      GREATER => boolSyntax.mk_eq (right', left')
                    | _ => boolSyntax.mk_eq (left', right')
                end
              else ordinary ()
            end
          else ordinary ()
        end
    | LAMB (variable, body) =>
        (* dest_term may choose a fresh binder to avoid capture. *)
        Term.mk_abs (variable, symmetry_normalise body)
    | _ => term

(* Isabelle has no predecessor constant -- src/HOL/Nat.thy writes the
   predecessor as [n - 1] throughout -- so a translated goal spells an
   index one below another that way where a HOL4 rule spells it
   [PRE n].  The layer's simpset carries the step between the two, so
   they are one term to every tactic that reads a rule, and a
   comparison that counted them as two statements would let a rule be
   the goal in one spelling and not in the other. *)
val predecessor = prim_mk_const {Thy = "prim_rec", Name = "PRE"}

fun predecessor_normalise term =
  case Term.dest_term term of
      COMB (rator, rand) =>
        let
          val rand = predecessor_normalise rand
        in
          if Term.is_const rator andalso Term.same_const rator predecessor
          then numSyntax.mk_minus (rand, numSyntax.term_of_int 1)
          else Term.mk_comb (predecessor_normalise rator, rand)
        end
    | LAMB (variable, body) =>
        Term.mk_abs (variable, predecessor_normalise body)
    | _ => term

fun statement_symmetry_normal_form term =
  let
    val term =
      if Term.free_in predecessor term then predecessor_normalise term
      else term
  in
    symmetry_normalise (rename_free term)
  end

fun statement_normal_form term =
  statement_symmetry_normal_form (beta_eta_normalise term)

(* A rule and the goal can state the same thing and still not look
   alike.  A corpus goal wears the translation's constants and a library
   rule wears HOL4's: [source_lexord] is [LLEX] by definition, so a
   rule about LLEX is the goal of a source_lexord statement, and a
   comparison that reads only the two terms cannot see it.  The
   translation's definitions are ambient for every goal already, so
   comparing under them grants the measurement nothing new; what it
   catches is a rule that closes a goal by recognition through the
   wrapper.

   The context is installed rather than read here, because the
   translation theory is built above this module.  Nothing installed
   means the plain syntactic comparison, which is what this was. *)
val definitional_context : thm list ref = ref []

fun memoized_unfolding definitions =
  memoUtil.keyed_memo
    (fn previous => fn implicit => Portable.pointer_eq (previous, implicit))
    (fn implicit =>
      Conv.QCONV (Rewrite.GEN_REWRITE_CONV Conv.ONCE_DEPTH_CONV
        implicit definitions))

val definitional_conversion = ref (memoized_unfolding [])

(* The names the context defines.  A term mentioning none of them
   unfolds to itself, and the comparison below is called once per
   ambient rule per goal, so recognising that case by a constant scan is
   what keeps the sweep affordable. *)
val definitional_heads : string HOLset.set ref =
  ref (HOLset.empty String.compare)

fun forall_body term =
  if boolSyntax.is_forall term then snd (boolSyntax.strip_forall term)
  else term

fun defined_head theorem =
  let
    val body = forall_body (Thm.concl theorem)
    val (_, equation) = boolSyntax.strip_imp_only body
    val (left, _) = boolSyntax.dest_eq equation
    val (head, _) = boolSyntax.strip_comb left
  in
    SOME (#1 (Term.dest_const head))
  end
  handle HOL_ERR _ => NONE

type 'a susp = 'a Portable.HOLSusp.susp
type symmetry_term = term * term susp
type stripped_reading =
  term option * (int * bool susp) susp * symmetry_term
type premise_groups = symmetry_term list susp list

datatype citation_reading =
    WholeCitation
  | CitationPart of term option * stripped_reading susp

type prepared_citation =
  {statement : term, head : term option,
   contentless : bool susp, whole : stripped_reading susp,
   readings : (premise_groups * citation_reading) seq.seq}
type comparison_statement = prepared_citation * (unit -> prepared_citation)

(* Each ambient sweep compares the same goal against many theorems. *)
val goal_comparison :
    (term * Rewrite.rewrites * (comparison_statement -> bool)) option ref =
    ref NONE

fun set_definitional_context theorems =
  (goal_comparison := NONE;
   definitional_conversion := memoized_unfolding theorems;
   definitional_context := theorems;
   definitional_heads :=
     HOLset.addList
       (HOLset.empty String.compare, List.mapPartial defined_head theorems))

fun mentions_constant_names heads term =
  let
    fun mentions current =
      case Term.dest_term current of
          CONST {Name, ...} => HOLset.member (heads, Name)
        | COMB (rator, rand) => mentions rator orelse mentions rand
        | LAMB (_, body) => mentions body
        | _ => false
  in
    mentions term
  end

(* Bounded rather than exhaustive: one pass strips one wrapper, and a
   wrapper over a wrapper needs as many passes as it has layers.  A
   fixed fuel cannot diverge on a recursive equation, which an
   unbounded rewrite could. *)
val unfolding_passes = 5

fun unfold_with make_conversion rewrites term =
  let
    val conversion = make_conversion rewrites
    fun pass current 0 = current
      | pass current fuel =
          let
            val next = boolSyntax.rhs (Thm.concl (conversion current))
          in
            if Term.aconv next current then current
            else pass next (fuel - 1)
          end
  in
    pass term unfolding_passes
  end
  handle HOL_ERR _ => term

fun unfold term =
  unfold_with (!definitional_conversion) (Rewrite.implicit_rewrites ()) term

fun unfolded term =
  if List.null (!definitional_context) orelse
     not (mentions_constant_names (!definitional_heads) term)
  then term
  else unfold term

fun definitional_theorems () = !definitional_context

(* Unfolding a definition against itself leaves [t = t], and every
   vacuous statement matches every other.  A comparison of two of them
   says nothing, so the unfolded reading is only consulted when it still
   has content. *)
fun contentless term =
  let
    val body = forall_body term
    val (_, conclusion) = boolSyntax.strip_imp_only body
  in
    Term.aconv conclusion boolSyntax.T orelse
    (case total boolSyntax.dest_eq conclusion of
         SOME (left, right) => Term.aconv left right
       | NONE => false)
  end

(* A citation and a goal can be one statement written two ways: the
   quantifier prefix differs, the premises stand in a different order,
   or the citation states the goal alongside other conjuncts.
   Stripping only the citation and comparing what is left against the
   whole goal therefore sees a citation that is a premise-free goal and
   misses one that is a goal carrying premises.

   So the citation is read every way a rule is read from it -- prefix
   off, premises accumulated, conjunction split, since a conjunctive
   rule enters the simpset as one rewrite per conjunct -- and it is the
   goal when one of those readings has the goal's conclusion and every
   premise it carries is one the goal carries too.  Coverage runs that
   way only: a reading with fewer premises is stronger than the goal and
   supplies it outright, while one with a premise the goal does not have
   leaves work and is not the goal.

   A prefix is not always one prefix.  A rule can quantify what its
   premise speaks about, discharge it, and quantify again over what is
   left -- [!x s. x NOTIN s ==> !t. s SUBSET x INSERT t <=> s SUBSET t]
   -- and taking the prefix off once leaves the inner one standing in
   the conclusion, where it is nothing the goal says.  Such a rule was
   read as no reading of the goal at all, and two goals that are one of
   these rules were measured with their own statement left in the
   simpset.  So a reading with premises is read on beyond them, for as
   often as a prefix reappears.  The readings that stop there are kept
   beside the ones that go on, because a conclusion that is the whole
   goal is a reading of it in its own right and reading past its prefix
   loses it.  Moving a prefix out past a premise is an equivalence, so
   this adds readings without admitting any statement the rule does not
   make. *)
fun prepare_symmetry normal_form term =
  (term, Portable.HOLSusp.delay (fn () => normal_form term))

(* PRE cannot be used as a rigid head because its symmetry normal form
   changes its head. *)
fun rigid_head term =
  if Term.is_comb term then rigid_head (Term.rator term)
  else if Term.is_const term andalso not (Term.same_const term predecessor)
  then SOME term
  else NONE

(* Stripping a truth equivalence can expose a different head. *)
fun citation_head term =
  case rigid_head term of
      SOME head =>
        if Term.same_const head boolSyntax.equality then NONE else SOME head
    | NONE => NONE

fun prepare_stripped term =
  let
    open Portable.HOLSusp
    val size = delay (fn () =>
      (Term.term_size term, delay (fn () => Term.free_in predecessor term)))
  in
    (rigid_head term, size, prepare_symmetry statement_symmetry_normal_form term)
  end

fun prepare_normal term =
  prepare_stripped (strip_normal_truth_equivalence term)

fun statement_parts term =
  boolSyntax.strip_imp_only (forall_body term)

fun prepare_citation statement : prepared_citation =
  let
    open Portable.HOLSusp
    fun normal_reading term =
      delay (fn () => prepare_normal (beta_eta_normalise term))

    (* The lazy traversal preserves conjunct and nested-prefix order and
       stops at the first matching reading. Premises are shared across
       conjuncts and prepared only once a conclusion matches. *)
    fun read inherited term rest =
      let
        val (premises, conclusion) = statement_parts term
        val inherited =
          if null premises then inherited
          else delay (fn () =>
            map (prepare_symmetry statement_normal_form) premises) ::
            inherited
        val rest =
          if not (null premises) andalso boolSyntax.is_forall conclusion
          then seq.delay (fn () => read inherited conclusion rest)
          else rest
      in
        case total boolSyntax.dest_conj conclusion of
            SOME (left, right) =>
              read inherited left
                (seq.delay (fn () => read inherited right rest))
          | NONE =>
              let
                val reading =
                  if Portable.pointer_eq (conclusion, statement)
                  then WholeCitation
                  else CitationPart
                    (citation_head conclusion, normal_reading conclusion)
              in
                seq.cons (inherited, reading) rest
              end
      end
  in
    {statement = statement, head = citation_head statement,
     contentless = delay (fn () => contentless statement),
     whole = normal_reading statement,
     readings = seq.delay (fn () => read [] statement seq.empty)}
  end

fun expanded_citation (citation : prepared_citation) term =
  if Portable.pointer_eq (term, #statement citation) then citation
  else prepare_citation term

(* Corpus goals repeatedly inspect the same ambient citations. Reuse
   their unfolded readings while the definition and rewrite sources
   which produced them are current. *)
fun memoized_citation statement : comparison_statement =
  let
    val citation = prepare_citation statement
    val mentions = memoUtil.keyed_memo (curry Portable.pointer_eq)
      (fn heads => mentions_constant_names heads statement)
    fun same (previous, old_rewrites) (current, new_rewrites) =
      Portable.pointer_eq (previous, current) andalso
      Portable.pointer_eq (old_rewrites, new_rewrites)
    val expand = memoUtil.keyed_memo same
      (fn (conversion, rewrites) =>
        expanded_citation citation (unfold_with conversion rewrites statement))
  in
    (citation, fn () =>
      if mentions (!definitional_heads) then
        expand (!definitional_conversion, Rewrite.implicit_rewrites ())
      else citation)
  end

fun prepare_statement_comparison goal =
  let
    open Portable.HOLSusp
    val goal = strip_truth_equivalence goal
    fun variants left right =
      can (match_term left) right andalso can (match_term right) left
    fun symmetric (_, left_normal) (_, right_normal) =
      Term.aconv (force left_normal) (force right_normal)
    fun same (left as (a, _)) (right as (b, _)) =
      Term.aconv a b orelse variants a b orelse symmetric left right
    (* Mutual matching and the symmetry normal form preserve rigid heads
       here, after beta and eta reduction and with PRE excluded. *)
    fun same_stripped (left_head, left_size, left as (left_term, _))
                      (right_head, right_size, right as (right_term, _)) =
      (case (left_head, right_head) of
           (SOME a, SOME b) => Term.same_const a b
         | _ => true) andalso
      (Portable.pointer_eq (left_term, right_term) orelse
       let
         val (a, left_pre) = force left_size
         val (b, right_pre) = force right_size
       in
         (* First-order matching can only increase term size. These
            readings already went through beta and eta reduction, so
            only PRE can change size in the symmetry pass. *)
         if a = b then same left right
         else
           (force left_pre orelse force right_pre) andalso symmetric left right
       end)
    val (goal_premises, goal_body) = statement_parts goal
    val whole = prepare_stripped goal
    (* Stripping the prefix and premises preserves the beta-eta normal
       form obtained for the whole goal. *)
    val stripped_body = strip_normal_truth_equivalence goal_body
    val distinct_readings = not (Portable.pointer_eq (stripped_body, goal))
    val conclusion =
      if distinct_readings then prepare_stripped stripped_body else whole
    val premises = map (prepare_symmetry statement_normal_form) goal_premises
    fun covered premise = List.exists (same premise) premises
    (* Beta and eta preserve the heads recorded for raw citations. *)
    fun possible (SOME a) (SOME b, _, _) = Term.same_const a b
      | possible _ _ = true
  in
    fn ({head, whole = citation, readings, ...} : prepared_citation) =>
      let
        val whole_possible = possible head whole
        fun all_covered [] = true
          | all_covered (premises :: earlier) =
              all_covered earlier andalso List.all covered (force premises)
        fun matches (premises, WholeCitation) =
              distinct_readings andalso
              possible head conclusion andalso
              same_stripped (force citation) conclusion andalso
              all_covered premises
          | matches (premises, CitationPart (head, prepared)) =
              (possible head whole andalso
               same_stripped (force prepared) whole) orelse
              (distinct_readings andalso possible head conclusion andalso
               same_stripped (force prepared) conclusion andalso
               all_covered premises)
        fun matches_reading readings =
          case seq.cases readings of
              NONE => false
            | SOME (reading, rest) =>
                matches reading orelse matches_reading rest
      in
        (whole_possible andalso same_stripped (force citation) whole) orelse
        matches_reading readings
      end
  end

fun prepare_goal_comparison goal =
  let
    open Portable.HOLSusp
    val ordinary = prepare_statement_comparison goal
    val expanded =
      delay (fn () =>
        let val term = unfolded goal
        in
          if Portable.pointer_eq (term, goal) then (true, ordinary)
          else (Term.aconv term goal, prepare_statement_comparison term)
        end)
  in
    fn (citation, expand_citation) =>
      ordinary citation orelse
      (not (List.null (!definitional_context)) andalso
       let
         val unfolded_citation = expand_citation ()
         val unfolded_statement = #statement unfolded_citation
         val statement = #statement citation
         val (same_goal, compare) = force expanded
         val original = Portable.pointer_eq (unfolded_statement, statement)
       in
         not (same_goal andalso
              (original orelse Term.aconv unfolded_statement statement))
         andalso
         not (force (#contentless unfolded_citation)) andalso
         compare unfolded_citation
       end)
  end

fun compare_with_goal goal =
  let
    val implicit = Rewrite.implicit_rewrites ()
    fun fresh () =
      let val compare = prepare_goal_comparison goal
      in goal_comparison := SOME (goal, implicit, compare); compare
      end
  in
    case !goal_comparison of
        SOME (previous, rewrites, compare) =>
          (* The stripped reading retains the binder's variable name. *)
          if Portable.pointer_eq (goal, previous) andalso
             Portable.pointer_eq (implicit, rewrites)
          then compare else fresh ()
      | NONE => fresh ()
  end

fun theorem_statement theorem : comparison_statement =
  let val citation = prepare_citation (Thm.concl theorem)
  in
    (citation,
     fn () => expanded_citation citation (unfolded (#statement citation)))
  end

fun theorem_is_goal goal theorem =
  compare_with_goal goal (theorem_statement theorem)

val primitive_citations =
  map (fn (definition, rewrite) =>
         (definition, memoized_citation (Thm.concl rewrite)))
    primitive_definitions

fun withheld_primitives goal =
  let val compare = compare_with_goal goal
  in
    List.mapPartial
      (fn (definition, citation) =>
        if compare citation then SOME definition else NONE)
      primitive_citations
  end

fun simp_controls goal exclusions =
  translation_base :: withheld_primitives goal @ controls exclusions

fun named_theorem (RewriteAdd theorem) = SOME theorem
  | named_theorem (RewriteAddBottomUp theorem) = SOME theorem
  | named_theorem (SplitAdd theorem) = SOME theorem
  | named_theorem (IntroAdd (_, theorem)) = SOME theorem
  | named_theorem (ElimAdd (_, theorem)) = SOME theorem
  | named_theorem (DestAdd (_, theorem)) = SOME theorem
  | named_theorem (CongruenceAdd theorem) = SOME theorem
  | named_theorem (FactAdd theorem) = SOME theorem
  | named_theorem (DefinitionAdd theorem) = SOME theorem
  | named_theorem (IffAdd theorem) = SOME theorem
  | named_theorem (RewriteDelete _) = NONE

(* Ambient method arguments recur across the corpus. Cache their
   syntactic readings, while unfolding still uses the current rewrites. *)
val ambient_citations :
    (term * comparison_statement) Symtab.table ref = ref Symtab.empty

fun set_ambient_citations arguments =
  let
    fun insert ({name, theorem} : named_thm, table) =
      let val statement = Thm.concl theorem
      in Symtab.update (name, (statement, memoized_citation statement)) table
      end
  in
    ambient_citations :=
      List.foldl insert Symtab.empty (List.mapPartial named_theorem arguments)
  end

fun argument_is_goal goal ({name, theorem} : named_thm) =
  case Symtab.lookup (!ambient_citations) name of
      SOME (statement, citation) =>
        if Portable.pointer_eq (Thm.concl theorem, statement)
        then compare_with_goal goal citation
        else theorem_is_goal goal theorem
    | NONE => theorem_is_goal goal theorem

(* A direct analogue is excluded by theorem shape as well as by its
   persistent name.  This check happens before controls are appended, so a
   recipe cannot put the measured theorem back under an invocation-private
   name. *)
fun location_name (DB.Local name) = name
  | location_name (DB.Stored name) = KernelSig.name_toString name

fun registered_definition theorem =
  List.exists
    (fn location =>
      let val name = location_name location
      in String.isSuffix "_def" name orelse String.isSuffix "_DEF" name
      end)
    (DB.revlookup theorem)

fun permitted_for goal (DefinitionAdd (named as {theorem, ...})) =
      not (argument_is_goal goal named) orelse
      registered_definition theorem
  | permitted_for goal arg =
      case named_theorem arg of
          NONE => true
        | SOME named => not (argument_is_goal goal named)

fun permitted_arg ({goal, ...} : corpus_goal) = permitted_for goal

fun consults_simpset Simp = true
  | consults_simpset Auto = true
  | consults_simpset Force = true
  | consults_simpset Fastforce = true
  | consults_simpset Clarsimp = true
  | consults_simpset Aesop = true
  | consults_simpset _ = false

fun consults_claset Auto = true
  | consults_claset Blast = true
  | consults_claset Force = true
  | consults_claset Fastforce = true
  | consults_claset Safe = true
  | consults_claset Clarify = true
  | consults_claset Clarsimp = true
  | consults_claset Aesop = true
  | consults_claset _ = false

fun claset_argument (IntroAdd _) = true
  | claset_argument (ElimAdd _) = true
  | claset_argument (DestAdd _) = true
  | claset_argument _ = false

fun iff_argument (IffAdd _) = true
  | iff_argument _ = false

(* Isabelle's [iff] is one attribute with two effects: the equivalence
   goes to the simpset and the rules derived from it to the claset.  An
   entry declared that way therefore reaches a method that reads either
   half, and carrying it as a rewrite alone leaves [blast], [safe] and
   [clarify] -- which read no simpset -- without a declaration Isabelle
   gave them. *)
fun argument_reaches identifier argument =
  if claset_argument argument then consults_claset identifier
  else if iff_argument argument then
    consults_claset identifier orelse consults_simpset identifier
  else consults_simpset identifier

fun recipe_arguments (Invoke (_, arguments)) = arguments
  | recipe_arguments (Then (left, right)) =
      recipe_arguments left @ recipe_arguments right
  | recipe_arguments (AllGoals (left, right)) =
      recipe_arguments left @ recipe_arguments right
  | recipe_arguments (Repeat inner) = recipe_arguments inner

fun direct_recipe_arguments ({goal, recipe, ...} : corpus_goal) =
  List.filter (not o permitted_for goal) (recipe_arguments recipe)

fun direct_argument_name argument =
  case named_theorem argument of
      SOME {name, ...} => name
    | NONE => method_arg_name argument

val argument_name = direct_argument_name

fun raw_goal_diagnostic ({id, ...} : corpus_goal) arguments =
  id ^ "=[" ^
  String.concatWith ", " (map direct_argument_name arguments) ^ "]"

fun validate_raw_goal (goal : corpus_goal) =
  case direct_recipe_arguments goal of
      [] => ()
    | arguments =>
        raise ERR "validate_raw_goal"
          ("forbidden method arguments: " ^
           raw_goal_diagnostic goal arguments)

fun validate_raw_goals family goals =
  let
    val circular =
      List.mapPartial
        (fn goal =>
          case direct_recipe_arguments goal of
              [] => NONE
            | arguments => SOME (raw_goal_diagnostic goal arguments))
        goals
  in
    if null circular then ()
    else
      raise ERR "validate_raw_goals"
        (family ^ ": forbidden method arguments: " ^
         String.concatWith "; " circular)
  end

fun ambient_statement theorem = memoized_citation (Thm.concl theorem)

val ambient_claset_cache :
    (clasetLib.claset * (exclusion * comparison_statement) list) option ref =
  ref NONE

fun cached_ambient_claset claset =
  case !ambient_claset_cache of
      SOME (previous, statements) =>
        if Portable.pointer_eq (previous, claset) then SOME statements
        else NONE
    | NONE => NONE

fun ambient_claset_statements claset =
  case cached_ambient_claset claset of
      SOME statements => statements
    | NONE =>
        let
          val statements =
            map (fn (_, (name, theorem)) =>
              ({name = name, theorem = theorem},
               ambient_statement theorem))
              (clasetLib.rules_of claset)
        in
          ambient_claset_cache := SOME (claset, statements);
          statements
        end

val ambient_simpset_statements =
  memoUtil.keyed_memo (curry Portable.pointer_eq)
    (fn simpset =>
      List.concat
        (map
          (map (fn theorem => (theorem, ambient_statement theorem)) o
           simpLib.frag_rewrites)
          (simpLib.ssfrags_of simpset)))

fun select_analogues goal statements =
  let val compare = compare_with_goal goal
  in
    List.mapPartial
      (fn (entry, statement) =>
        if compare statement then SOME entry else NONE)
      statements
  end

fun current_simpset_statements () =
  ambient_simpset_statements (clasimpLib.clasimp_ss ())

fun simpset_analogues goal =
  select_analogues goal (current_simpset_statements ())

fun named_rewrite theorem =
  map
    (fn location =>
      {name = location_name location, theorem = theorem})
    (DB.revlookup theorem)

val benchmark_safe_solver =
  simpLib.mk_tactic_solver
    ("benchmark clasimp safe",
     Tactical.FIRST
       [Tactical.FIRST_ASSUM Tactic.ACCEPT_TAC,
        Tactic.REFL_TAC,
        Tactic.ACCEPT_TAC boolTheory.TRUTH,
        Tactical.FIRST_ASSUM Tactic.CONTR_TAC])

(* Rule A1 on the context's simpset: a rewrite that states the goal is not
   what closes it.  The filter goes through simpLib, which replays the
   simpset's own history, rather than rebuilding it from its fragments:
   the fragments are not the simpset.  Rebuilt from them, what the layer
   had removed by name comes back -- [APPEND_ASSOC], which
   [clasimpLib] drops because it and the equation normalisation that
   respells a trailing cons are each other's reverse, and the pair
   loops. *)
fun clean_simpset ctxt goal =
  let
    val simpset = clasimpLib.clasimp_ss_of ctxt
    val statements = ref (ambient_simpset_statements simpset)
    val compare = compare_with_goal goal
    (* The cache and the filter walk the same fragment history. Confirm
       each theorem's identity before reusing its prepared statement. *)
    fun keep (_, theorem) =
      case !statements of
          (expected, statement) :: rest =>
            if Portable.pointer_eq (theorem, expected) then
              (statements := rest; not (compare statement))
            else
              (statements := []; not (theorem_is_goal goal theorem))
        | [] => not (theorem_is_goal goal theorem)
  in
    simpLib.filter_rewrites keep simpset
    |> simpLib.set_cond_depth clasimpLib.cond_depth
    |> simpLib.set_safe_solvers [benchmark_safe_solver]
    |> simpLib.add_unsafe_solver
         (linarithLib.linarith_solver_with_facts
            (linarithData.arith_facts_of ctxt))
    |> simpLib.set_subgoaler clasimpLib.witness_subgoaler
  end

fun preserve_target tactic (original as (_, target)) ctxt =
  let
    val (goals, validation) = tactic original ctxt
    fun restore theorems =
      let
        val theorem = validation theorems
      in
        if aconv (concl theorem) target then theorem
        else
          let
            val normalization =
              Conv.QCONV
                (Conv.REDEPTH_CONV
                   (Conv.ORELSEC (Thm.BETA_CONV, Drule.ETA_CONV))) target
            val normalized = boolSyntax.rhs (concl normalization)
          in
            if aconv (concl theorem) normalized then
              EQ_MP (SYM normalization) theorem
            else theorem
          end
      end
  in
    (goals, restore)
  end

fun processed_clasimp simpset body arguments =
  clasimpLib.process_clasimp_args
    (fn claset => fn processed_simpset => fn _ =>
      preserve_target (body claset processed_simpset))
    (clasetLib.the_claset ()) simpset arguments

(* Preparation derives only the clean invocation-local context.  Raw recipe
   validation happens before any ambient declarations are inspected, so a
   forbidden argument is an error rather than something preparation hides. *)
fun prepare_goal recipe
      ({id, goal, source_method, provenance,
        representative} : source_goal) : corpus_goal =
  let
    val _ = validate_raw_goal
      {id = id, goal = goal, source_method = source_method,
       recipe = recipe, excl = [], provenance = provenance,
       representative = representative}
    val ambient =
      select_analogues goal
        (ambient_claset_statements (clasetLib.the_claset ()))
    val candidates =
      ambient @ List.concat (map named_rewrite (simpset_analogues goal))
    val exclusions = listUtil.distinct_by String.compare #name candidates
  in
    {id = id, goal = goal, source_method = source_method,
     recipe = recipe, excl = exclusions,
     provenance = provenance, representative = representative}
  end

(* Isabelle's [iff] is a theory declaration, not a method modifier: its
   [blast], [safe] and [clarify] take intro:, elim: and dest: and nothing
   else, and what they see of an [iff] is the rules it derived into the
   claset.  A claset-only front end is therefore handed those rules, one
   marker apiece, where a front end holding a simpset is handed the
   declaration itself and derives them for both halves.  Dropping the
   declaration instead would leave the claset without rules Isabelle's
   had; passing it on would be rejected, a claset alone having nowhere
   to put the equivalence. *)
fun iff_markers ({name, theorem} : named_thm) =
  map
    (fn ({kind, safe, ...} : clasetLib.rulespec, (_, rule)) =>
      case kind of
          clasetRules.Intro =>
            if safe then clasetLib.SIntro rule else clasetLib.Intro rule
        | clasetRules.Elim =>
            if safe then clasetLib.SElim rule else clasetLib.Elim rule
        | clasetRules.Dest =>
            if safe then clasetLib.SDest rule else clasetLib.Dest rule
        | _ =>
            raise mk_HOL_ERR "benchLib" "iff_markers"
              ("[iff] derived a rule no classical marker names: " ^ name))
    (clasetLib.iff_rules name theorem)

fun class_args (RewriteAdd {theorem, ...}) = [clasetLib.Simp theorem]
  (* Installed in the simpset the invocation runs with, by
     [with_normalised_subjects] below, and so named in no marker: the
     low priority is the fragment's, and an invocation rewrite has
     none. *)
  | class_args (RewriteAddBottomUp _) = []
  | class_args (RewriteDelete name) =
      map clasetLib.Del (claset_names name) @ [rewrite_exclusion name]
  | class_args (SplitAdd {theorem, ...}) = [simpLib.Split theorem]
  | class_args (IntroAdd (SafeRule, {theorem, ...})) =
      [clasetLib.SIntro theorem]
  | class_args (IntroAdd (UnsafeRule, {theorem, ...})) =
      [clasetLib.Intro theorem]
  | class_args (ElimAdd (SafeRule, {theorem, ...})) =
      [clasetLib.SElim theorem]
  | class_args (ElimAdd (UnsafeRule, {theorem, ...})) =
      [clasetLib.Elim theorem]
  | class_args (DestAdd (SafeRule, {theorem, ...})) =
      [clasetLib.SDest theorem]
  | class_args (DestAdd (UnsafeRule, {theorem, ...})) =
      [clasetLib.Dest theorem]
  | class_args (CongruenceAdd {theorem, ...}) = [simpLib.Cong theorem]
  | class_args (FactAdd _) = []
  | class_args (DefinitionAdd {theorem, ...}) =
      [clasetLib.Simp theorem]
  | class_args (IffAdd {theorem, ...}) = [clasetLib.Iff theorem]

fun all_class_args args = List.concat (map class_args args)

fun classical_arg (RewriteDelete name) =
      map clasetLib.Del (claset_names name)
  | classical_arg (IntroAdd (SafeRule, {theorem, ...})) =
      [clasetLib.SIntro theorem]
  | classical_arg (IntroAdd (UnsafeRule, {theorem, ...})) =
      [clasetLib.Intro theorem]
  | classical_arg (ElimAdd (SafeRule, {theorem, ...})) =
      [clasetLib.SElim theorem]
  | classical_arg (ElimAdd (UnsafeRule, {theorem, ...})) =
      [clasetLib.Elim theorem]
  | classical_arg (DestAdd (SafeRule, {theorem, ...})) =
      [clasetLib.SDest theorem]
  | classical_arg (DestAdd (UnsafeRule, {theorem, ...})) =
      [clasetLib.Dest theorem]
  | classical_arg (IffAdd named) = iff_markers named
  | classical_arg _ = []

fun all_classical_args args = List.concat (map classical_arg args)

fun classical_controls exclusions =
  List.concat
    (map
      (fn ({name, ...} : exclusion) =>
        map clasetLib.Del (claset_names name))
      exclusions)

fun blast_arg (IntroAdd (SafeRule, {theorem, ...})) =
      [clasetLib.SIntro theorem]
  | blast_arg (IntroAdd (UnsafeRule, {theorem, ...})) =
      [clasetLib.Intro theorem]
  | blast_arg (ElimAdd (SafeRule, {theorem, ...})) =
      [clasetLib.SElim theorem]
  | blast_arg (ElimAdd (UnsafeRule, {theorem, ...})) =
      [clasetLib.Elim theorem]
  | blast_arg (DestAdd (SafeRule, {theorem, ...})) =
      [clasetLib.SDest theorem]
  | blast_arg (DestAdd (UnsafeRule, {theorem, ...})) =
      [clasetLib.Dest theorem]
  | blast_arg (IffAdd named) = iff_markers named
  | blast_arg (FactAdd _) = []
  | blast_arg _ = []

fun all_blast_args args = List.concat (map blast_arg args)

(* The translation writes a set of pairs as a predicate over a pair
   variable, so a goal can need [PAIR] where the Isabelle source it came
   from never wrote a pair down.  It is support for that spelling and not
   a fact the source method names, so a goal with no pair in it is given
   it neither faithfully nor usefully: it arrives as an assumption, which
   is a universal the search instantiates afresh on every branch it
   opens.  [DISJOINT A B ==> DISJOINT B A] closes in milliseconds without
   it and does not return inside the budget with it. *)
fun type_mentions_pair ty =
  case Lib.total Type.dest_thy_type ty of
      SOME {Thy = "pair", Tyop = "prod", ...} => true
    | SOME {Args, ...} => List.exists type_mentions_pair Args
    | NONE => false

fun mentions_pair term =
  type_mentions_pair (Term.type_of term) orelse
  (case Term.dest_term term of
       COMB (rator, rand) => mentions_pair rator orelse mentions_pair rand
     | LAMB (bound, body) => mentions_pair bound orelse mentions_pair body
     | _ => false)

fun blast_translation_args goal =
  (if mentions_pair goal then [pairTheory.PAIR] else []) @
  [clasetLib.Intro boolTheory.SELECT_UNIQUE]

(* A [simp add:] argument the simplifier can make no firing rewrite of is
   not passed to one.  The invocations below reach their simpsets twice --
   once through a front end that routes such an argument to its claset, and
   once through a [FULL_SIMP_TAC] of their own that would install the
   rewrite the front end refused -- and that rewrite is what the front end
   refuses it for: it matches every equation and calls the solver on an
   existential at each. *)
fun simp_arg (RewriteAdd {theorem, ...}) =
      if clasimpLib.simp_argument_can_fire theorem then SOME theorem
      else NONE
  (* Not a rewrite of the invocation: see [class_args] above. *)
  | simp_arg (RewriteAddBottomUp _) = NONE
  | simp_arg (RewriteDelete name) = SOME (rewrite_exclusion name)
  | simp_arg (SplitAdd {theorem, ...}) = SOME (simpLib.Split theorem)
  | simp_arg (CongruenceAdd {theorem, ...}) = SOME (simpLib.Cong theorem)
  | simp_arg (DefinitionAdd {theorem, ...}) = SOME theorem
  (* The other half of the same declaration: Isabelle's [iff] is a simp
     rule as well as a source of classical rules, so a front end reading
     its arguments as rewrites sees the equivalence. *)
  | simp_arg (IffAdd {theorem, ...}) = SOME theorem
  | simp_arg _ = NONE

fun fact_arg (FactAdd {theorem, ...}) = SOME theorem
  | fact_arg _ = NONE

fun bottom_up_arg (RewriteAddBottomUp {theorem, ...}) = SOME theorem
  | bottom_up_arg _ = NONE

(* Where a low-priority argument is installed: in the simpset the
   invocation runs with, so that every engine reading a simpset --
   the simplifier's own pass and the classical search's alike -- offers
   the rule the same subject. *)
fun with_normalised_subjects simpset args =
  case List.mapPartial bottom_up_arg args of
      [] => simpset
    | rewrites =>
        simpLib.++ (simpset, clasimpLib.normalised_subject_fragment rewrites)

fun supplied_rule (IntroAdd (_, {theorem, ...})) = SOME theorem
  | supplied_rule (ElimAdd (_, {theorem, ...})) = SOME theorem
  | supplied_rule (DestAdd (_, {theorem, ...})) = SOME theorem
  | supplied_rule _ = NONE

(* The engines' own insertion: a [using] fact reaches the goal through
   [clasetLib.INSERT_FACTS_TAC], instances and order included, so the
   corpus measures what a caller gets. *)
val insert_facts = clasetLib.INSERT_FACTS_TAC

fun with_facts args tactic =
  let
    val facts = List.mapPartial fact_arg args
  in
    Tactical.ORELSE
      (Tactical.FIRST (map Tactic.MATCH_ACCEPT_TAC facts),
       Tactical.THEN (insert_facts facts, tactic))
  end

(* Restricted higher-order pattern instantiation.  If the target is
   [predicate argument], try a universally quantified assumption at the set
   (predicate) [predicate].  The quantified variable is instantiated only
   by a well-typed term already present at the target head; SPEC performs the
   kernel type/scope checks and no non-pattern term is guessed. *)
fun predicate_abstraction_core
      (goal as (_, target)) =
  let
    val tracing = OS.Process.getEnv "HOLBENCHPATTERNTRACE" = SOME "1"
    fun trace prefix term =
      if tracing then
        TextIO.print (prefix ^ Parse.term_to_string term ^ "\n")
      else
        ()
    val _ = trace "pattern target: " target
    val (predicate, _) = dest_comb target
    val (_, predicate_range) = dom_rng (type_of predicate)
    val _ =
      if predicate_range = Type.bool then ()
      else
        raise ERR "predicate_abstraction_tac" "target head is not a predicate"
    fun use assumption =
      let
        val _ = boolSyntax.dest_forall (concl assumption)
        val instantiated =
          Rewrite.REWRITE_RULE [pred_setTheory.SPECIFICATION]
            (SPEC predicate assumption)
        val (_, result) = boolSyntax.strip_imp_only (concl instantiated)
        val _ = trace "pattern candidate: " result
      in
        if aconv result target then
          Tactical.THEN
            (Tactic.MATCH_MP_TAC instantiated,
             Tactical.THEN
               (Tactic.BETA_TAC,
                Tactical.THEN
                  (Tactical.REPEAT Tactic.CONJ_TAC,
                   Tactical.FIRST_ASSUM Tactic.MATCH_ACCEPT_TAC)))
        else
          Tactical.NO_TAC
      end
  in
    Tactical.FIRST_ASSUM use goal
  end
  handle HOL_ERR _ => Tactical.NO_TAC goal

fun predicate_abstraction_tac goal =
  Tactical.THEN
    (Tactical.REPEAT
       (Tactical.FIRST
          [Tactic.GEN_TAC,
           Thm_cont.DISCH_THEN Tactic.STRIP_ASSUME_TAC]),
     predicate_abstraction_core) goal

(* Construct the least-fixed-point witness for any set-valued equation.
   The tactic only recognizes the logical pattern [?x. x = body x]; all
   reasoning about [body] is left as the ordinary monotonicity subgoal. *)
fun lfp_witness_tac (goal as (_, target)) =
  let
    val (fixed, equation) = boolSyntax.dest_exists target
    val (left, right) = dest_eq equation
    val _ =
      if aconv left fixed then ()
      else raise ERR "lfp_witness_tac" "left side is not the witness"
    val operator = mk_abs (fixed, right)
    val fixedpoint =
      SPEC operator fixedPointTheory.lfp_fixedpoint
    val (monotone, fixedpoint_conclusion) =
      boolSyntax.dest_imp (concl fixedpoint)
    val (fixedpoint_equation, _) =
      boolSyntax.dest_conj fixedpoint_conclusion
    val (_, witness) = dest_eq fixedpoint_equation
    val assumed = ASSUME monotone
    val equation = SYM (Drule.cj 1 (MP fixedpoint assumed))
    val rule =
      Conv.CONV_RULE (Conv.DEPTH_CONV Thm.BETA_CONV)
        (DISCH monotone equation)
  in
    Tactical.THEN
      (Tactic.EXISTS_TAC witness,
       Tactical.THEN
         (Tactical.TRY Tactic.BETA_TAC,
          Tactic.MATCH_MP_TAC rule)) goal
  end
  handle HOL_ERR _ => Tactical.NO_TAC goal

fun recipe_args entry args =
  if List.all (permitted_arg entry) args then args
  else
    raise ERR "compile_recipe"
      (#id entry ^ ": recipe supplies the measured theorem")

(* An ambient correspondence rewrites a goal out of the translation's
   predicate and into HOL4's -- [source_sorted_wrt] into SORTED -- and a
   rule the recipe supplies in the translation's spelling then stops
   meeting the goal it was cited for.  Each supplied rule is offered on
   the far side of the correspondence as well, in the same role.  The
   crossing is an equivalence, so the offered rule states the same fact,
   and the condition the equivalence rests on is kept as the rule's last
   premise -- after the rule's own, so a destruction rule's major
   premise stays first -- for the search to discharge rather than
   assumed here.

   Installed rather than read, for the reason the definitional context
   is: the translation theory is built above this module. *)
val correspondences : thm list ref = ref []

val correspondence_heads : string HOLset.set ref =
  ref (HOLset.empty String.compare)

fun correspondence_head theorem =
  let
    val body = forall_body (Thm.concl theorem)
    val (_, equation) = boolSyntax.strip_imp_only body
    val (left, _) = boolSyntax.dest_eq equation
    val (head, _) = boolSyntax.strip_comb left
  in
    SOME (#1 (Term.dest_const head))
  end
  handle HOL_ERR _ => NONE

fun set_correspondences theorems =
  (correspondences := map (Drule.UNDISCH_ALL o Drule.SPEC_ALL) theorems;
   correspondence_heads :=
     HOLset.addList
       (HOLset.empty String.compare,
        List.mapPartial correspondence_head theorems))

fun crossed ({name, theorem} : named_thm) =
  if List.null (!correspondences) orelse
     not (mentions_constant_names (!correspondence_heads) (Thm.concl theorem))
  then
    NONE
  else
    let
      val specialised = Drule.SPEC_ALL theorem
      val rewritten = Rewrite.REWRITE_RULE (!correspondences) specialised
      val crossed_conclusion = Thm.concl rewritten
    in
      if aconv crossed_conclusion (Thm.concl specialised) orelse
         aconv crossed_conclusion boolSyntax.T
      then
        NONE
      else
        let
          val premises = fst (boolSyntax.strip_imp_only crossed_conclusion)
          val conditions = HOLset.listItems (Thm.hypset rewritten)
          val core = Drule.UNDISCH_ALL rewritten
          val ordered =
            List.foldr (fn (term, current) => Thm.DISCH term current)
              core (premises @ conditions)
        in
          SOME {name = name ^ "[bridged]", theorem = Drule.GEN_ALL ordered}
        end
    end
  handle HOL_ERR _ => NONE

fun crossed_arg arg =
  case arg of
      RewriteAdd entry => Option.map RewriteAdd (crossed entry)
    | RewriteAddBottomUp entry =>
        Option.map RewriteAddBottomUp (crossed entry)
    | IffAdd entry => Option.map IffAdd (crossed entry)
    | IntroAdd (strength, entry) =>
        Option.map (fn crossing => IntroAdd (strength, crossing))
          (crossed entry)
    | ElimAdd (strength, entry) =>
        Option.map (fn crossing => ElimAdd (strength, crossing))
          (crossed entry)
    | DestAdd (strength, entry) =>
        Option.map (fn crossing => DestAdd (strength, crossing))
          (crossed entry)
    | FactAdd entry => Option.map FactAdd (crossed entry)
    | _ => NONE

(* A crossing that states the goal is dropped rather than reported: it
   is derived here, not cited, so it is not a recipe supplying its own
   answer. *)
fun crossing_arguments entry args =
  List.filter (permitted_arg entry) (List.mapPartial crossed_arg args)

fun across_correspondence entry args = args @ crossing_arguments entry args

(* The layer's own [asm_full_simp] is the analogue of the method being
   measured -- asm_full_simp_tac, premises simplified mutually -- where
   HOL4's [FULL_SIMP_TAC] offers a premise only the premises before it.
   A source result states its premises as the antecedents of its
   conclusion, which is where the difference is felt. *)
(* The set-equality pass below reads an equation as a membership,
   which is the reading HOL4's set and list facts are stated on.  It
   stands down in two cases, both of them the engines' own -- the pass
   runs before [FULL_SIMP_TAC] and so before the engine ever sees the
   equation, and run first it puts the equation out of the other
   reading's reach for good.

   The first is the method's own rewrite: where it named one that states
   a reading of the equation, that is the one meant, and [fun_eq_iff]
   names the applied reading outright.  Only a rewrite of equations
   between functions states one, which is what keeps the ambient
   rewrites -- supplied to every goal, and between them matching almost
   any statement -- out of the decision.

   The second is the equation's own shape: the membership reading is the
   right one only where a side is headed by a constant the simpset
   states a membership fact about, which is what
   [clasimpLib.reads_as_membership] decides.  A constant-headed side
   that is a predicate short of an argument, and no set, meets none of
   the facts the predicate's own are stated on.  This one is asked of
   each equation the pass reaches rather than of the goal: the pass
   descends, and a source lemma stating when two sets are equal -- an
   iff between set equations -- has no equation at its conclusion at
   all.

   Both are the decisions [clasimpLib.extensional_normalize] takes
   inside the engines.  The test reads the goal's own shape against the
   rewrites the method named, as [preprocess_fires] below decides its
   pass. *)
fun reading_is_supplied goal rewrites =
  clasimpLib.reads_as_supplied rewrites (forall_body goal)

fun set_equality_pass simpset goal rewrites =
  if reading_is_supplied goal rewrites then Tactical.ALL_TAC
  else
    let
      (* What the invocation states on membership comes from both its
         simpset and its supplied rewrites. Isabelle's [iff] declarations
         such as [mem_Sigma_iff] reach this pass as arguments. *)
      val stated =
        if null rewrites then simpset
        else simpLib.++ (simpset, simpLib.rewrites rewrites)
      val reads_as_membership = clasimpLib.reads_as_membership stated
      fun take_to_membership term =
        if reads_as_membership term then hurdUtils.SET_EQ_CONV term
        else raise ERR "set_equality_pass" "the equation is read applied"
    in
      Tactical.TRY
        (Tactic.CONV_TAC
           (Conv.CHANGED_CONV (Conv.ONCE_DEPTH_CONV take_to_membership)))
    end

fun tactic_for simpset goal Simp args exclusions =
      let
        val facts = List.mapPartial fact_arg args
        val simps = List.mapPartial simp_arg args
        val simplify =
          clasimpLib.with_extensionality simpset
            (clasimpLib.asm_full_simp simpset
               (simps @ simp_controls goal exclusions))
      in
        Tactical.THEN
          (insert_facts facts, simplify)
      end
  | tactic_for simpset goal Auto args exclusions =
      let
        val controls_for_simp = simp_controls goal exclusions
        val automatic =
          processed_clasimp simpset
            (clasimpLib.CS_AUTO_TAC {blast = 4, depth = 2})
            (all_class_args args @ controls_for_simp)
        val simps = List.mapPartial simp_arg args
        val set_equality = set_equality_pass simpset goal simps
      in
        with_facts args
          (Tactical.ORELSE
            (predicate_abstraction_tac,
             if null args then
               Tactical.THEN (set_equality, automatic)
             else
               Tactical.THEN
                 (Tactical.THEN
                    (set_equality,
                     simpLib.FULL_SIMP_TAC simpset
                       (simps @ controls_for_simp)),
                  Tactical.ORELSE (predicate_abstraction_tac, automatic))))
      end
  | tactic_for simpset goal Blast args exclusions =
      let
        (* Isabelle's [blast] has no [iff:] modifier, so an [iff]
           argument here is ambient and reaches the search as the
           rules the declaration derived, never as an equivalence.
           Letting it into the pass below would turn that pass on for
           every blast goal an [iff] is in scope of, which is what it
           was gated away from. *)
        val simps =
          List.mapPartial simp_arg (List.filter (not o iff_argument) args)
        (* Isabelle's [blast] never unfolds an equation.  One with a
           variable on a side it eliminates by substituting it, and so
           does this search: [blastSearch]'s [HypSubst], oriented on
           exactly that side.  Taking such an equation to membership
           spends the step instead.  [set_L1125_image_Pow_surj] arrives
           as [IMAGE f A = B ==> ...], and dissolving the hypothesis
           loses two things at once -- the equation the search would
           have substituted, and the last [IMAGE] standing under a
           [SUBSET], which is the major premise of [subset_imageE], the
           rule the method itself supplies.  With nothing for that rule
           to match the search is blind: measured, 3055 branches and
           past the budget dissolved, 0.016s left standing.  What the
           pass is for is the equation no substitution reaches, which
           is the one with the same variable on both sides. *)
        fun substitutable term =
          case Lib.total boolSyntax.dest_eq term of
              NONE => false
            | SOME (left, right) =>
                (Term.is_var left andalso not (Term.free_in left right))
                orelse
                (Term.is_var right andalso not (Term.free_in right left))
        fun set_eq_conv term =
          if substitutable term then
            raise ERR "tactic_for" "the search substitutes the equation"
          else hurdUtils.SET_EQ_CONV term
        val set_equality_step =
          Tactic.CONV_TAC
            (Conv.CHANGED_CONV (Conv.ONCE_DEPTH_CONV set_eq_conv))
        val supplied_rules = List.mapPartial supplied_rule args
        val accept_supplied =
          Tactical.FIRST
            (map Tactic.MATCH_ACCEPT_TAC supplied_rules)
        val direct_supplied =
          Tactical.THEN
            (Tactical.TRY Tactic.BETA_TAC,
             Tactical.ORELSE
               (accept_supplied,
                Tactical.THEN (Tactic.EQ_TAC, accept_supplied)))
        val controls_for_simp = simp_controls goal exclusions
        val simplify = simpLib.SIMP_TAC simpset (simps @ controls_for_simp)
        (* Isabelle's [blast] never simplifies, so the pass below is
           the [unfolding] the method asked for and nothing else: it
           runs unconditionally exactly where there is a rewrite to run
           it with, and otherwise wherever the goal has a set equality
           the step above will take -- which is not only a goal whose
           own conclusion is one, an equality under a quantifier or a
           connective being reached just the same.  Gating it on the
           argument list instead would make it depend on arguments
           that are not rewrites -- a [dest:] the method named, or the
           ambient claset, which by construction the method did not
           name.  It did, until the ambient claset arrived: it turned
           the pass on for every blast goal at once, and
           [classical_L803], a Hilbert-system goal with no rewrite in
           sight, went from 0.029s to past fifteen minutes. *)
        val preprocess =
          if null simps then
            Tactical.TRY
              (Tactical.THEN
                (set_equality_step, simplify))
          else
            Tactical.THEN
              (Tactical.TRY set_equality_step,
               simplify)
        (* A rule the method supplied is stated in the vocabulary the
           method's own goal had.  The pass above rewrites the goal out
           of that vocabulary, and a rule left behind in it matches
           nothing: a goal handed [subset_imageE], whose major premise
           is [source SUBSET IMAGE function target], is left by the
           pass with no [SUBSET] in it at all, and the search has to
           guess the set the rule would have named.  The selftest's
           [stranded_rule_goal] is that shape.  The rules go
           through the same pass as the goal, and only where that pass
           runs -- which is what the test below decides, on the goal,
           exactly as the tactic does.  Both forms reach the search:
           the pass is [ONCE_DEPTH_CONV], so it rewrites the outermost
           set equality on a path and leaves what is under it, and a
           rule the method stated still has the equalities under that
           one to meet. *)
        val preprocess_fires =
          not (null simps) orelse
          Lib.can
            (Conv.CHANGED_CONV (Conv.ONCE_DEPTH_CONV set_eq_conv))
            goal
        fun normalise_with rewrites =
          Conv.QCONV
            (Conv.THENC
              (Conv.TRY_CONV
                 (Conv.ONCE_DEPTH_CONV set_eq_conv),
               simpLib.SIMP_CONV simpset (rewrites @ controls_for_simp)))
        fun normalised_by conversion theorem =
          case Lib.total (Conv.CONV_RULE conversion) theorem of
              SOME normalised => normalised
            | NONE => theorem
        val normalised_theorem = normalised_by (normalise_with simps)
        fun rule_kind (IntroAdd (strength, _)) =
              SOME (clasetRules.Intro, strength)
          | rule_kind (ElimAdd (strength, _)) =
              SOME (clasetRules.Elim, strength)
          | rule_kind (DestAdd (strength, _)) =
              SOME (clasetRules.Dest, strength)
          | rule_kind _ = NONE
        fun rebuilt (IntroAdd (strength, {name, ...})) theorem =
              IntroAdd (strength, {name = name, theorem = theorem})
          | rebuilt (ElimAdd (strength, {name, ...})) theorem =
              ElimAdd (strength, {name = name, theorem = theorem})
          | rebuilt (DestAdd (strength, {name, ...})) theorem =
              DestAdd (strength, {name = name, theorem = theorem})
          | rebuilt argument _ = argument
        (* The pass can simplify a rule out of rule shape: [equalityE]
           is [left = right ==> (left SUBSET right ==> right SUBSET
           left ==> conclusion) ==> conclusion], whose minor premise
           follows from its major, so simplifying the two together
           leaves [T] and the claset refuses the result as an
           ill-formed elimination rule.  A carried rule is offered only
           where it is still a rule of the kind the method declared,
           which is the claset's own test. *)
        fun carried argument =
          case (rule_kind argument, named_theorem argument) of
              (SOME (kind, strength), SOME {theorem = stated, ...}) =>
                let
                  val rewritten = normalised_theorem stated
                  val spec =
                    {kind = kind, safe = strength = SafeRule, prio = NONE}
                in
                  if aconv (Thm.concl stated) (Thm.concl rewritten) orelse
                     not (Lib.can (clasetRules.ext_info spec) rewritten)
                  then []
                  else [rebuilt argument rewritten]
                end
            | _ => []
        val search_args =
          all_blast_args
            (args @
             (if preprocess_fires then List.concat (map carried args)
              else []))
        (* A supplied fact is stated in the same vocabulary as a
           supplied rule, and the pass rewrites the goal out of it just
           as surely: [finite_dom_map_of] states the finiteness of a
           domain the pass turns into an existential, leaving the
           search two spellings of one set and no way to see they are
           the same.  Isabelle's [unfolding] rewrites the chained facts
           with the goal; the facts go through the pass here for the
           same reason the rules do, and both forms reach the search. *)
        fun carried_fact (FactAdd {name, theorem}) =
              let
                (* The pass a fact goes through is the goal's, and the
                   goal is not the fact: a fact left among the rewrites
                   normalises itself to [T], which states nothing. *)
                val others =
                  List.filter
                    (fn rewrite =>
                      not (aconv (Thm.concl rewrite) (Thm.concl theorem)))
                    simps
                val rewritten = normalised_by (normalise_with others) theorem
              in
                if aconv (Thm.concl theorem) (Thm.concl rewritten) then []
                else [FactAdd {name = name, theorem = rewritten}]
              end
          | carried_fact _ = []
        val fact_args =
          args @
          (if preprocess_fires then List.concat (map carried_fact args)
           else [])
        fun trace_residual (goal as (_, target)) =
          (if OS.Process.getEnv "HOLBENCHBLASTRESIDUAL" = SOME "1" then
             TextIO.print
               ("blast residual: " ^ Parse.term_to_string target ^ "\n")
           else
             ();
           Tactical.ALL_TAC goal)
      in
        with_facts fact_args
          (Tactical.ORELSE
            (direct_supplied,
             Tactical.THEN
               (Tactical.TRY lfp_witness_tac,
                Tactical.THEN
                  (Tactical.TRY
                     (Tactic.MATCH_MP_TAC boolTheory.SELECT_UNIQUE),
                   Tactical.THEN
                     (preprocess,
                      Tactical.THEN
                        (trace_residual,
                         Tactical.THEN
                           (Tactical.TRY Tactic.EQ_TAC,
                            Tactical.THEN
                             (Tactical.TRY Tactic.BETA_TAC,
                              Tactical.ORELSE
                                (accept_supplied,
                                 tableauLib.BLAST_TAC
                                   (search_args @
                                    blast_translation_args goal @
                                    controls exclusions))))))))))
      end
  | tactic_for simpset goal Force args exclusions =
      let
        val simps = List.mapPartial simp_arg args
        val controls_for_simp = simp_controls goal exclusions
        val prepare =
          Tactical.THEN
            (set_equality_pass simpset goal simps,
             simpLib.FULL_SIMP_TAC simpset
               (simps @ controls_for_simp))
      in
        with_facts args
          (Tactical.THEN
            (prepare,
             processed_clasimp simpset clasimpLib.CS_FORCE_TAC
               (all_class_args args @ controls_for_simp)))
      end
  | tactic_for simpset goal Fastforce args exclusions =
      with_facts args
        (Tactical.THEN
          (set_equality_pass simpset goal (List.mapPartial simp_arg args),
           processed_clasimp simpset clasimpLib.CS_FASTFORCE_TAC
             (all_class_args args @ simp_controls goal exclusions)))
  | tactic_for _ _ Safe args exclusions =
      with_facts args
        (classicalLib.SAFE_TAC
          (all_classical_args args @ classical_controls exclusions))
  | tactic_for _ _ Clarify args exclusions =
      with_facts args
        (classicalLib.CLARIFY_TAC
          (all_classical_args args @ classical_controls exclusions))
  | tactic_for simpset goal Clarsimp args exclusions =
      with_facts args
        (processed_clasimp simpset clasimpLib.CS_CLARSIMP_TAC
          (all_class_args args @ simp_controls goal exclusions))
  | tactic_for simpset goal Aesop args exclusions =
      with_facts args
        (processed_clasimp simpset
          (aesopLib.CS_AESOP_TAC aesopLib.default_config)
          (all_class_args args @ simp_controls goal exclusions))
  (* Isabelle's metis reads its facts in the normal form its simp leaves
     goals in; the ambient simpset here imposes normal forms the library
     does not state its lemmas in, so the facts enter in both. *)
  | tactic_for _ _ Metis args _ =
      clasimpLib.AMBIENT_METIS_TAC (List.mapPartial fact_arg args)
  | tactic_for _ _ Linarith args _ =
      with_facts args
        (linarithLib.LINARITH_TAC
          (all_class_args args))

(* The simpset is prepared once for the goal and handed to every
   tactic the recipe composes, which each built their own before.  A
   recipe cannot change what it would contain: it is derived from the
   goal and the ambient declarations, and compiling a recipe reads
   both without touching either. *)
fun compile_recipe simpset entry recipe =
  case recipe of
      Invoke (tactic_id, args) =>
        let
          val crossings = crossing_arguments entry args
          val arguments = recipe_args entry args @ crossings
        in
          tactic_for (with_normalised_subjects simpset arguments)
            (#goal entry) tactic_id arguments (#excl entry)
        end
    | Then (left, right) =>
        Tactical.THEN1
          (compile_recipe simpset entry left,
           compile_recipe simpset entry right)
    | AllGoals (left, right) =>
        Tactical.THEN
          (compile_recipe simpset entry left,
           compile_recipe simpset entry right)
    (* Isabelle's [+] applies its method once and then repeats it, so a
       recipe that never applies fails rather than passing the goal on. *)
    | Repeat inner =>
        let val step = compile_recipe simpset entry inner
        in Tactical.THEN (step, Tactical.REPEAT step)
        end

(* Compare the declarations that would survive deletion. This check
   needs their names and statements, so the rule indexes can stay shared. *)
fun remaining_claset_comparison goal (excl : exclusion list) =
  let
    val names =
      HOLset.fromList String.compare
        (List.concat (map (claset_names o #name) excl))
  in
    (fn name => not (HOLset.member (names, name)), compare_with_goal goal)
  end

fun has_remaining_claset_analogue claset goal excl =
  let
    val (retained, compare) = remaining_claset_comparison goal excl
  in
    case cached_ambient_claset claset of
        SOME statements =>
          List.exists (fn ({name, ...}, statement) =>
            retained name andalso compare statement) statements
      | NONE =>
          (* One-off clasets can validate without replacing the snapshot
             that corpus preparation will reuse. *)
          List.exists (fn (_, (name, theorem)) =>
            retained name andalso compare (theorem_statement theorem))
            (clasetLib.rules_of claset)
  end

fun exclusions_effective claset ({goal, excl, ...} : corpus_goal) =
  let
    val base_names = map #name excl
    fun supplied_is_analogue ({theorem, ...} : exclusion) =
      theorem_is_goal goal theorem
    fun has_remaining_rewrite () =
      let
        val statements = current_simpset_statements ()
        val compare = compare_with_goal goal
        fun unexcluded (theorem, statement) =
          compare statement andalso
          List.exists
            (fn location =>
              not (List.exists (equal (location_name location)) base_names))
            (DB.revlookup theorem)
      in
        List.exists unexcluded statements
      end
  in
    List.all supplied_is_analogue excl andalso
    not (has_remaining_claset_analogue claset goal excl)
    andalso
    not (has_remaining_rewrite ())
  end

fun exclusion_diagnostic claset ({goal, excl, ...} : corpus_goal) =
  let
    val bad_supplied =
      map
        (fn ({name, theorem} : exclusion) =>
          name ^ ": " ^ Parse.term_to_string (Thm.concl theorem))
        (List.filter
          (fn ({theorem, ...} : exclusion) =>
            not (theorem_is_goal goal theorem)) excl)
    val (retained, compare) = remaining_claset_comparison goal excl
    val remaining =
      List.mapPartial
        (fn ({name, ...}, statement) =>
          if retained name andalso compare statement then SOME name else NONE)
        (ambient_claset_statements claset)
    fun rewrite_names theorem =
      case DB.revlookup theorem of
          [] => ["<unnamed>"]
        | locations => map location_name locations
    val remaining_rewrites =
      List.concat
        (map rewrite_names
          (List.filter
            (fn theorem =>
              case DB.revlookup theorem of
                  [] => false
                | locations =>
                    List.exists
                      (fn location =>
                        not
                          (List.exists (equal (location_name location))
                            (map #name excl)))
                      locations)
            (simpset_analogues goal)))
  in
    "non-analogues = [" ^ String.concatWith ", " bad_supplied ^
    "], goal = " ^ Parse.term_to_string goal ^
    ", remaining rules = [" ^
    String.concatWith ", " remaining ^
    "], remaining rewrites = [" ^
    String.concatWith ", " remaining_rewrites ^ "]"
  end

(* Runs [work] under [budget], NONE if the budget expired.

   [Timeout.apply] runs its payload under the caller's thread
   attributes, which here admit asynchronous interrupts: a runaway
   computation really is cut off, as the selftest checks directly.  A
   tactic can still overrun its budget by a wide margin, but not for
   want of an interrupt -- see the note on swallowed interrupts in the
   benchmark harness documentation. *)
fun within_budget budget work =
  SOME (Timeout.apply budget work ())
  handle Timeout.TIMEOUT _ => NONE

(* A source result's variables are fixed in the proof state the method
   runs on: Isabelle's premises are that subgoal's, and the lemma's
   variables are its parameters.  A corpus goal states the result
   closed, so the same premises arrive as the antecedents of a
   conclusion under a binder -- where the implication congruence offers
   a premise only the premises before it, and no premise reaches the
   assumptions the method reads.  Fixing the parameters first is what
   the generated corpus files write out by hand, stating a source
   result with free variables; this is the same goal for the entries
   that state it closed. *)
val fix_parameters = Tactical.REPEAT Tactic.GEN_TAC

(* What is timed, and what the budget is spent on, is the tactic.
   Preparing the goal's simpset is neither: it asks the circularity
   guard about every ambient rewrite. It depends on the goal and the
   ambient declarations and is done before the clock starts. *)
fun run_goal_with_timing {now, prepare} budget recipe
      (entry : corpus_goal) =
  let
    val ctxt = Context.snapshot ()
    val simpset = prepare (fn () => clean_simpset ctxt (#goal entry))
    val started = now ()
    val residual = ref "tactic returned residual goals or failed"
    fun goal_text (assumptions, conclusion) =
      (if null assumptions then ""
       else String.concatWith ", " (map Parse.term_to_string assumptions) ^
            " |- ") ^
      Parse.term_to_string conclusion
    fun run () =
      case Tactical.VALID
             (Tactical.THEN
                (fix_parameters,
                 preserve_target (compile_recipe simpset entry recipe)))
             ([], #goal entry) ctxt of
          ([], validation) => (ignore (validation []); true)
        | (goals, _) =>
            (residual :=
               "residual goals: [" ^
               String.concatWith "; " (map goal_text goals) ^ "]";
             false)
    val timed_out = ref false
    val solved =
      (case within_budget budget run of
           SOME outcome => outcome
         | NONE =>
             (if recipe_has_tactic Linarith recipe andalso
                 OS.Process.getEnv "HOLBENCHPROGRESS" = SOME "1"
              then TextIO.print (linarith_stats_text () ^ "\n")
              else ();
              timed_out := true;
              false))
      handle Portable.Interrupt => raise Portable.Interrupt
           | exn =>
               raise ERR "run_goal"
                 (recipe_name recipe ^ " on " ^ #id entry ^ ": " ^
                  Feedback.exn_to_string exn)
    val elapsed = Time.- (now (), started)
  in
    if !timed_out orelse not (Time.< (elapsed, budget)) then TIMEOUT
    else if solved then SOLVED elapsed
    else FAILED (!residual)
  end
  handle Portable.Interrupt => raise Portable.Interrupt
       | exn => FAILED (Feedback.exn_to_string exn)

fun uses_simpset Safe = false
  | uses_simpset Clarify = false
  | uses_simpset Metis = false
  | uses_simpset Linarith = false
  | uses_simpset _ = true

fun run_goal budget recipe =
  let
    val prepare =
      if recipe_uses uses_simpset recipe then fn build => build ()
      else fn _ => simpLib.empty_ss
  in
    run_goal_with_timing {now = Time.now, prepare = prepare} budget recipe
  end

fun id_set ids = HOLset.fromList String.compare ids

fun duplicate_goal_pairs (goals : corpus_goal list) =
  let
    (* Index goals to the right, keeping both sides of each pair in the
       same order as in the corpus for diagnostics. *)
    fun add ({id,goal,...} : corpus_goal, (index,pairs)) =
      let
        val later = Option.getOpt (Redblackmap.peek (index,goal), [])
        val pairs = List.foldr (fn (other,rest) => (id,other) :: rest)
                      pairs later
      in
        (Redblackmap.insert (index,goal,id :: later),pairs)
      end
  in
    #2 (List.foldr add (Redblackmap.mkDict Term.compare,[]) goals)
  end

fun is_translation ({cause = TranslationGap, ...} : shortfall) = true
  | is_translation _ = false

fun validate_corpus {family, goals, shortfalls} =
  let
    val goal_ids = map #id goals
    val shortfall_ids = map #id shortfalls
    val goal_set = id_set goal_ids
    val duplicate_pairs = duplicate_goal_pairs goals
    val circular =
      List.filter
        (not o null o direct_recipe_arguments) goals
    fun is_goal id = HOLset.member (goal_set,id)
    val unknown =
      List.filter
        (fn (item as {id, ...} : shortfall) =>
          not (is_goal id) andalso not (is_translation item)) shortfalls
    val misplaced_translation =
      List.filter
        (fn ({id, ...} : shortfall) => is_goal id)
        (List.filter is_translation shortfalls)
    val valid_entries =
      List.all
        (fn ({id, date, note, ...} : shortfall) =>
          id <> "" andalso date <> "" andalso note <> "") shortfalls
  in
    if HOLset.numItems goal_set <> length goal_ids then
      raise ERR "validate_corpus" (family ^ ": duplicate corpus goal id")
    else if not (null duplicate_pairs) then
      raise ERR "validate_corpus"
        (family ^ ": aconv corpus goals: " ^
         String.concatWith ", "
           (map (fn (left, right) => left ^ "=" ^ right)
             duplicate_pairs))
    else if not (null circular) then
      raise ERR "validate_corpus"
        (family ^ ": recipes supply their measured theorem: " ^
         String.concatWith ", " (map #id circular))
    else if HOLset.numItems (id_set shortfall_ids) <> length shortfall_ids then
      raise ERR "validate_corpus" (family ^ ": duplicate shortfall id")
    else if not valid_entries then
      raise ERR "validate_corpus"
        (family ^ ": shortfalls need non-empty id, date, and note")
    else if not (null unknown) then
      raise ERR "validate_corpus"
        (family ^ ": unknown shortfalls: " ^
         String.concatWith ", " (map #id unknown))
    else if not (null misplaced_translation) then
      raise ERR "validate_corpus"
        (family ^ ": translation gaps unexpectedly have HOL goals: " ^
         String.concatWith ", " (map #id misplaced_translation))
    else
      ()
  end

fun assert_validated_accounting {family, goals, shortfalls, gated} =
  let
    val goal_ids = map #id goals
    val gated_ids = map #1 gated
    val goal_set = id_set goal_ids
    val gated_set = id_set gated_ids
    val missing_runs =
      List.filter
        (fn id => not (HOLset.member (gated_set,id))) goal_ids
    val extra_runs =
      List.filter
        (fn id => not (HOLset.member (goal_set,id))) gated_ids
    val solved =
      map #1 (List.filter (outcome_solved o #2) gated)
    val shortfall_set =
      id_set (map #id (List.filter (not o is_translation) shortfalls))
    val expected =
      List.filter
        (fn id => not (HOLset.member (shortfall_set,id))) goal_ids
    val expected_set = id_set expected
  in
    if not (null missing_runs) orelse not (null extra_runs) then
      raise ERR "assert_accounting" (family ^ ": gated result id drift")
    else if length solved <> length expected orelse
            not (List.all (fn id => HOLset.member (expected_set,id)) solved)
    then
      raise ERR "assert_accounting"
        (family ^ ": solved/shortfall drift; solved = [" ^
         String.concatWith ", " solved ^ "], expected = [" ^
         String.concatWith ", " expected ^ "], outcomes = [" ^
         String.concatWith ", "
           (map (fn (id, result) => id ^ "=" ^ outcome_text result)
             gated) ^ "]")
    else
      ()
  end

fun assert_accounting (args as {family, goals, shortfalls, ...}) =
  (validate_corpus {family = family, goals = goals, shortfalls = shortfalls};
   assert_validated_accounting args)

fun selected level ({representative, ...} : corpus_goal) =
  level >= 2 orelse representative

(* Which goals of a corpus family a debugging run wants to see.  This
   restricts the corpus and nothing else: it was read inside
   [run_family], where it also reached the hand-built families the
   selftest measures the harness itself with, and emptying one of those
   made it fail an exact-set check that has nothing to do with the
   corpus.  [restrict] takes the restriction rather than reading it, so
   what it does is checkable without an environment. *)
type restriction = {
  shortfalls_only : bool,
  goals_wanted : (string * string list) option
}

fun restrict ({shortfalls_only, goals_wanted} : restriction)
      {family, goals, shortfalls} =
  List.filter
    (fn (goal : corpus_goal) =>
      (not shortfalls_only orelse
       List.exists
         (fn ({id, cause, ...} : shortfall) =>
           id = #id goal andalso cause <> TranslationGap)
         shortfalls) andalso
      (case goals_wanted of
           SOME (selected_family, ids) =>
             selected_family <> family orelse
             List.exists (equal (#id goal)) ids
         | NONE => true)) goals

fun environment_restriction () =
  {shortfalls_only =
     OS.Process.getEnv "HOLBENCHSHORTFALLSONLY" = SOME "1",
   goals_wanted =
     case (OS.Process.getEnv "HOLBENCHFAMILY",
           OS.Process.getEnv "HOLBENCHGOAL") of
         (SOME family, SOME ids) =>
           SOME (family, String.tokens (equal #",") ids)
       | _ => NONE}

fun run_family {family, goals, shortfalls, budget, battery, level} =
  let
    val selected_goals = List.filter (selected level) goals
    val selected_ids = id_set (map #id selected_goals)
    val selected_shortfalls =
      List.filter
        (fn ({id, cause, ...} : shortfall) =>
          HOLset.member (selected_ids,id) orelse
          (level >= 2 andalso cause = TranslationGap)) shortfalls
    val _ = validate_corpus
      {family = family, goals = selected_goals,
       shortfalls = selected_shortfalls}
    val _ =
      if diagnostics_enabled () then
        diagnostic_output ("## " ^ family ^ "\n\n")
      else
        ()
    val _ =
      List.app
        (fn goal =>
          if exclusions_effective (clasetLib.the_claset ()) goal
          then ()
          else
            raise ERR "run_family"
              (family ^ ": ineffective self-analogue exclusion for " ^
               #id goal ^ "; " ^
               exclusion_diagnostic (clasetLib.the_claset ()) goal))
        selected_goals
    fun run_gated goal =
      let
        val _ =
          if OS.Process.getEnv "HOLBENCHPROGRESS" = SOME "1" then
            (TextIO.print (family ^ ": " ^ #id goal ^ " ... ");
             TextIO.flushOut TextIO.stdOut)
          else
            ()
        val diagnostic_timer =
          if diagnostics_enabled () then SOME (Timer.startRealTimer ())
          else NONE
        val (result, work) =
          searchWork.measure
            (fn () => run_goal budget (#recipe goal) goal)
        val _ =
          case diagnostic_timer of
              NONE => ()
            | SOME timer =>
              let
                val elapsed = Timer.checkRealTimer timer
                val exclusion_names = map #name (#excl goal)
                fun is_excluded name =
                  List.exists (equal name) exclusion_names
                val excluded_claset =
                  map #name
                    (List.filter
                      (fn ({name, thm, ...} : clasetLib.aesop_rule) =>
                        is_excluded name andalso
                        theorem_is_goal (#goal goal) thm)
                      (clasetLib.all_rules (clasetLib.the_claset ())))
                val excluded_simpset =
                  map #name
                    (List.filter (is_excluded o #name)
                      (List.concat
                        (map named_rewrite (simpset_analogues (#goal goal)))))
                val classification =
                  case List.find
                         (fn ({id, ...} : shortfall) => id = #id goal)
                         selected_shortfalls of
                      NONE => "None"
                    | SOME {note, ...} =>
                        (case String.tokens (equal #":") note of
                             [] => "Unclassified"
                           | first :: _ => first)
                val search_statistics =
                  if recipe_has_tactic Linarith (#recipe goal) then
                    linarith_stats_text ()
                  else
                    searchWork.render work
              in
                diagnostic_output
                  (String.concat
                    ["### ", #id goal, "\n\n",
                     "- Source method: `", #source_method goal, "`\n",
                     "- Assigned recipe: `", recipe_name (#recipe goal),
                     "`\n",
                     "- Excluded ambient simp analogues: ",
                     "[", String.concatWith ", " excluded_simpset, "]\n",
                     "- Excluded ambient claset analogues: ",
                     "[", String.concatWith ", " excluded_claset, "]\n",
                     "- Outcome: `", outcome_text result, "`\n",
                     "- Elapsed: `", Time.toString elapsed, "`\n",
                     "- Search statistics: ", search_statistics, "\n",
                     "- Working classification: `", classification,
                     "`\n\n"])
              end
        val _ =
          if OS.Process.getEnv "HOLBENCHPROGRESS" = SOME "1" then
            TextIO.print
              (outcome_text result ^
               (if recipe_has_tactic Linarith (#recipe goal) then
                  " " ^ linarith_stats_text ()
                else
                  "") ^ "\n")
          else
            ()
      in
        (#id goal, result, work)
      end
    val measured = map run_gated selected_goals
    val gated = map (fn (id, result, _) => (id, result)) measured
    val work_done = map (fn (id, _, work) => (id, work)) measured
    val _ =
      assert_validated_accounting
        {family = family, goals = selected_goals,
         shortfalls = selected_shortfalls, gated = gated}
    fun run_battery goal tactic_id =
      let
        val progress =
          OS.Process.getEnv "HOLBENCHPROGRESS" = SOME "1"
        val _ =
          if progress then
            (TextIO.print
               (family ^ " battery: " ^ #id goal ^ " " ^
                tactic_name tactic_id ^ " ... ");
             TextIO.flushOut TextIO.stdOut)
          else
            ()
        val detailed_result =
          run_goal budget (Invoke (tactic_id, [])) goal
        val result =
          case detailed_result of
              FAILED _ => FAILED "additional observation failed"
            | outcome => outcome
        val _ =
          if progress then
            TextIO.print (outcome_text result ^ "\n")
          else
            ()
      in
        (#id goal, tactic_id, result)
      end
    val battery_results =
      if level < 2 orelse
         OS.Process.getEnv "HOLBENCHNOBATTERY" = SOME "1"
      then []
      else
        List.concat
          (map
            (fn goal =>
              map
                (run_battery goal)
                (List.filter
                   (fn tactic_id =>
                     not (recipe_has_tactic tactic_id (#recipe goal)))
                   battery))
            selected_goals)
  in
    {gated = gated, work = work_done, battery = battery_results}
  end

(* A corpus family is measured under whatever restriction the run asked
   for; a family built by hand is measured as it is given. *)
fun run_corpus_family {family, goals, shortfalls, budget, battery, level} =
  run_family
    {family = family,
     goals =
       restrict (environment_restriction ())
         {family = family, goals = goals, shortfalls = shortfalls},
     shortfalls = shortfalls, budget = budget, battery = battery,
     level = level}

end
