structure clasimpLib :> clasimpLib =
struct

open Abbrev HolKernel

(* Select the tracked engine before constructing any clasimp fragments or
   binding sources. Ordinary persistence is deliberately a separate path. *)

val ERR = mk_HOL_ERR "clasimpLib"

(* Load-time congruence proofs run before a theory is selected.  VALID checks
   the tactic result without requiring TAC_PROOF's ambient-theory guard. *)
fun prove (term, tactic) =
  case Tactical.VALID tactic ([], term) (Context.snapshot()) of
      ([], validation) => validation []
    | _ => raise ERR "prove" "load-time proof left goals"

val tracer =
  traceUtil.create
    {group = "clasimp", max = 3,
     emit = fn m => Feedback.HOL_MESG ("Clasimp: " ^ m)}

val safe_solver =
  simpLib.mk_tactic_solver
    ("clasimp safe",
     Tactical.FIRST
       [Tactical.FIRST_ASSUM Tactic.ACCEPT_TAC,
        Tactic.REFL_TAC,
        Tactic.ACCEPT_TAC boolTheory.TRUTH,
        Tactical.FIRST_ASSUM Tactic.CONTR_TAC])

(* A rewrite whose condition carries a variable its left-hand side does
   not determine reaches the traversal with that variable existentially
   closed: [QUANTIFY_CONDITIONS] is what HOL4 has where Isabelle leaves
   a schematic in the condition.  [EVERY2_LENGTH] is the shape --
   [LIST_REL P l1 l2 ==> LENGTH l1 = LENGTH l2] prepares to
   [(?P. LIST_REL P l1 l2) ==> (LENGTH l1 = LENGTH l2 <=> T)] -- and
   Isabelle discharges the condition of its own [list_all2_lengthD] by
   assumption, the unifier reading the relation off the assumption the
   schematic meets.  The existential is what is left of that unification
   here, and nothing above answers it: the assumption is in the context,
   and the condition asks for the witness the assumption names.

   So this pass names it: the condition is matched against the context
   assumptions with the goal's own variables held fixed, and the
   witnesses the match reads off discharge the existential.  A rewrite
   with more than one premise arrives as one existential over their
   conjunction, so the conjuncts are matched in turn under what the
   earlier ones have named.  A match against an assumption already in
   the context is Isabelle's [assume_tac] step, not a search.

   It is the subgoaler, not a solver, because the subgoaler is the one
   slot only a side condition reaches: the traversal simplifies a
   condition through it and offers what survives to the solvers, while
   the solvers are also what a simplification tactic tries on the goal
   itself.  An existential goal is not a condition a rewrite left open,
   and simplification does not prove one in Isabelle either.  The
   subgoaler runs the traversal's own recursion first and looks only at
   what that leaves. *)

(* Conditions arrive as an existential closure of the rule premises.
   A simpset can move that closure into the conjunction. Pull it back
   out before matching so the same assumptions still name the witnesses. *)
val pull_existentials =
  Conv.QCONV (Conv.TOP_DEPTH_CONV (Conv.FIRST_CONV
    (map (Conv.HO_REWR_CONV o Drule.SPEC_ALL o Conv.GSYM)
      [boolTheory.LEFT_EXISTS_AND_THM, boolTheory.RIGHT_EXISTS_AND_THM])))

fun has_witness_quantifier root =
  let
    fun next [] eta_short =
          (* The conversion may recognize an eta-short predicate
             application. Preserve the original whole-term guard once. *)
          eta_short andalso
          Lib.can (HolKernel.find_term boolSyntax.is_exists) root
      | next (term :: rest) eta_short = reachable term rest eta_short
    and reachable term rest eta_short =
      if not (Term.is_comb term) then next rest eta_short
      else
        let val (operator, operand) = Term.dest_comb term
        in
          if Term.same_const operator boolSyntax.existential then
            Term.is_abs operand orelse next rest true
          else if Term.is_comb operator andalso
                  Term.same_const (Term.rator operator)
                    boolSyntax.conjunction then
            reachable (Term.rand operator) (operand :: rest) eta_short
          else
            next rest eta_short
        end
  in
    reachable root [] false
  end

fun witness_subgoaler_with_charge charge : Traverse.subgoaler =
  let
    (* The conditions are matched one at a time against the context, each
       under what the earlier matches have already named: the rewrite's
       premises share the variables the traversal left open, which is how
       they determine one another in Isabelle's unifier too. *)
    fun witnesses assumptions fixed fixed_types conditions =
      let
        fun search [] instance = SOME instance
          | search (condition :: rest) instance =
              let
                val _ = charge searchBudget.Normalization
                val pattern = Term.subst instance condition
                fun attempt [] = NONE
                  | attempt (assumption :: others) =
                      (charge searchBudget.Candidate;
                       case Lib.total
                             (Term.match_terml fixed_types fixed pattern)
                             assumption of
                          NONE => attempt others
                        | SOME (extra, _) =>
                            (case search rest (extra @ instance) of
                                 NONE => attempt others
                               | found => found))
              in
                attempt assumptions
              end
      in
        search conditions []
      end
    fun prove_witness context_thms term =
      let
        val pulled_thm = pull_existentials term
        val pulled = boolSyntax.rhs (Thm.concl pulled_thm)
        val (vars, body) = boolSyntax.strip_exists pulled
        val _ =
          if null vars then
            raise ERR "witness_proof" "no contextual witness"
          else ()
        val fixed =
          HOLset.difference
            (Term.FVL [pulled] Term.empty_tmset,
             HOLset.fromList Term.compare vars)
        val fixed_types = Term.type_vars_in_term pulled
        val assumptions = map Thm.concl context_thms
        fun attempt conditions =
          witnesses assumptions fixed fixed_types conditions
        (* Prefer one context theorem for the whole condition.
           Otherwise reconstruct its conjuncts from their own
           supporting theorems. *)
        val matched =
          case attempt [body] of
              NONE => attempt (boolSyntax.strip_conj body)
            | found => found
        val instance =
          case matched of
              SOME instance => instance
            | NONE => raise ERR "witness_proof" "no contextual witness"
        fun find_context proposition =
          let
            fun scan [] = NONE
              | scan (theorem :: rest) =
                  (charge searchBudget.Candidate;
                   if Term.aconv (Thm.concl theorem) proposition then
                     SOME theorem
                   else scan rest)
          in scan context_thms end
        fun contextual proposition =
          case find_context proposition of
              SOME theorem => theorem
            | NONE =>
                raise ERR "witness_proof"
                  "matched condition has no context theorem"
        val _ = charge searchBudget.Normalization
        val body' = Term.subst instance body
        val body_thm =
          case find_context body' of
              SOME theorem => theorem
            | NONE =>
                (case map (contextual o Term.subst instance)
                        (boolSyntax.strip_conj body) of
                     [] =>
                       raise ERR "witness_proof"
                         "empty contextual condition"
                   | theorem :: rest =>
                       List.foldl
                         (fn (next, combined) =>
                           Thm.CONJ combined next)
                         theorem rest)
        fun introduce quantified [] theorem = theorem
          | introduce quantified (witness :: rest) theorem =
              let
                val (variable, inner) =
                  boolSyntax.dest_exists quantified
                val inner' =
                  Term.subst
                    [{redex = variable, residue = witness}] inner
              in
                Thm.EXISTS (quantified, witness)
                  (introduce inner' rest theorem)
              end
        val _ = charge searchBudget.Application
        val witnesses = map (Term.subst instance) vars
        val introduced = introduce pulled witnesses body_thm
      in
        Thm.EQ_MP (Thm.SYM pulled_thm) introduced
      end
    fun witness_proof context_thms term =
      (charge searchBudget.Normalization;
       if has_witness_quantifier term then
         SOME (prove_witness context_thms term)
       else NONE)
      handle Portable.Interrupt => raise Portable.Interrupt
           | e as searchBudget.LimitReached _ => raise e
           | _ => NONE
  in
    fn ({recurse, context_thms, ...} : Traverse.simp_prover_ctxt) =>
      fn term =>
        let
          val reduction = recurse term
          val reduced = boolSyntax.rhs (Thm.concl reduction)
        in
          if Term.aconv reduced boolSyntax.T then reduction
          else
            case witness_proof context_thms reduced of
                NONE => reduction
              | SOME theorem =>
                  Thm.TRANS reduction (Drule.EQT_INTRO theorem)
        end
  end

val witness_subgoaler : Traverse.subgoaler =
  witness_subgoaler_with_charge (fn _ => ())

fun witness_subgoaler_budgeted budget =
  witness_subgoaler_with_charge (searchBudget.charge budget)

(* HOL4's COND_CONG simplifies both branches of a conditional as well as
   its condition.  A recursive equation whose right-hand side is a
   conditional -- how an interval or an iteration is ordinarily stated --
   then rewrites its own unfolding without end: the branch holds an
   instance of the rule's own left-hand side, and rewriting it produces
   another.  Isabelle states such equations and rewrites with them, which
   its weak conditional congruence -- the condition simplified, the
   branches left alone -- is what allows.  Nothing short of that helps:
   the unfolding is licensed by the rule alone, so a congruence that
   descends into the branches at all diverges, whether or not it carries
   the condition down with it.  This layer follows Isabelle; the branch
   reasoning comes back from the case split, split_ss below.

   A congruence belongs to a fragment and a fragment is replaced whole,
   so the three other congruences of CONG_ss are restated here. *)
local
  infix THEN
  val op THEN = Tactical.THEN
in
val cond_weak_cong =
  prove
    (``!condition simplified left right.
         (condition = simplified) ==>
         ((if condition then left else right) =
          (if simplified then left else right))``,
     Tactical.REPEAT Tactic.GEN_TAC THEN
     Tactic.DISCH_TAC THEN
     Rewrite.ASM_REWRITE_TAC [])
end

(* src/HOL/Set.thy:461,471 @ f7e02b7e.  [ball_cong_simp] and
   [bex_cong_simp] are default congruences there, so the body of a
   bounded quantifier is simplified with its bound in context.  HOL4
   spells a bounded quantifier unfolded -- [EXISTS_MEM] states
   [EXISTS P l] as [?e. MEM e l /\ P e], [IN_IMAGE] leaves the
   membership on the other side of the conjunction -- so the rule has to
   be stated of the conjunction the quantifier binds, once per
   membership and once per side.  Neither side subsumes the other: with
   the membership on the left the body is what its bound simplifies, and
   with the membership on the right the body is the context the
   membership simplifies in, which is where an assumption constraining
   the elements that answer an equation gets to fire.

   What it must not be stated of is every conjunction, which is
   Isabelle's [conj_cong]: Isabelle declines to make that a default
   congruence and a measurement agrees, the four-square identity of the
   algebra corpus going from 0.9s to 483s against a 30s budget as the
   conjunctive side conditions of the ring rewrites each acquire a
   context.  Keeping the bound rigid is not a weakening towards that
   measurement but the source's own shape: a bounded quantifier is what
   Isabelle carries a congruence for.  It also keeps the rule away from
   an existential a *rewrite* is conditional on -- [submonoid_element]
   in src/algebra states [x IN H] under [?h. h << g /\ ...], whose
   conjuncts are not a bound on the variable -- where opening the body
   re-enables the rewrite that raised the condition and the search
   recurses to the conditional depth.

   The last premise is what keeps the rule from taking the conjunction
   away from everything else.  A congruence decides the descent at the
   node it matches, so without it the conjunction under the quantifier
   would never again be a term the rewrites and the caller's own
   congruences see -- a [Cong] argument stated of a conjunction stops
   working under an existential, and the bound itself stops being
   rewritten.  Handing the rebuilt conjunction back to the traversal
   restores both, at one further pass over a body that is already in
   normal form.

   The bounded universal needs nothing: it unfolds to an implication,
   which [IMP_CONG] below already opens. *)
local
  infix THEN
  val op THEN = Tactical.THEN

  val element = Term.mk_var ("element", Type.alpha)
  val boolean = Type.alpha --> Type.bool

  fun membership_bounds element =
    [listSyntax.mk_mem
       (element, Term.mk_var ("elements", listSyntax.mk_list_type Type.alpha)),
     Term.mk_comb
       (boolSyntax.mk_icomb
          (Term.prim_mk_const {Thy = "bool", Name = "IN"}, element),
        Term.mk_var ("elements", boolean))]

  (* One schema, instantiated with the bound on either side of the
     conjunction: the left conjunct is simplified on its own, the right
     one with the simplified left in context, and the conjunction they
     rebuild is handed back to the traversal. *)
  fun bounded_cong bound bound_first =
    let
      val simplified_bound = Term.mk_var ("simplified_bound", boolean)
      val body = Term.mk_var ("body", boolean)
      val simplified_body = Term.mk_var ("simplified_body", boolean)
      val rebuilt = Term.mk_var ("rebuilt", boolean)
      fun apply f = Term.mk_comb (f, element)
      val (left, simplified_left, right, simplified_right) =
        if bound_first then
          (bound, apply simplified_bound, apply body, apply simplified_body)
        else
          (apply body, apply simplified_body, bound, apply simplified_bound)
      fun quantify statement = boolSyntax.mk_forall (element, statement)
      val left_alone = quantify (boolSyntax.mk_eq (left, simplified_left))
      val right_in_context =
        quantify
          (boolSyntax.mk_imp
             (simplified_left, boolSyntax.mk_eq (right, simplified_right)))
      val handed_back =
        quantify
          (boolSyntax.mk_eq
             (boolSyntax.mk_conj (simplified_left, simplified_right),
              apply rebuilt))
      val statement =
        boolSyntax.list_mk_imp
          ([left_alone, right_in_context, handed_back],
           boolSyntax.mk_eq
             (boolSyntax.mk_exists
                (element, boolSyntax.mk_conj (left, right)),
              boolSyntax.mk_exists (element, apply rebuilt)))
    in
      prove
        (statement,
         Tactic.DISCH_TAC THEN
         Tactic.DISCH_TAC THEN
         Thm_cont.DISCH_THEN
           (fn equation => Rewrite.REWRITE_TAC [Conv.GSYM equation]) THEN
         Tactic.AP_TERM_TAC THEN
         Tactic.ABS_TAC THEN
         Rewrite.ASM_REWRITE_TAC [] THEN
         Tactic.ASM_CASES_TAC simplified_left THEN
         Tactic.RES_TAC THEN
         Rewrite.ASM_REWRITE_TAC [])
    end
in
val bounded_exists_congs =
  List.concat
    (map (fn bound => [bounded_cong bound true, bounded_cong bound false])
       (membership_bounds element))
end

val weak_cong_ss = simpLib.named_merge_ss "CONGWEAK"
  [simpLib.SSFRAG
     {name = NONE,
      congs =
        [Rewrite.REWRITE_RULE [Conv.GSYM boolTheory.AND_IMP_INTRO]
           boolTheory.IMP_CONG,
         cond_weak_cong,
         boolTheory.RES_FORALL_CONG,
         boolTheory.RES_EXISTS_CONG],
      convs = [], rewrs = [], filter = NONE, ac = [], dprocs = []},
   (* Later premises use the functions computed by earlier premises.
      The ordinary congruence opener cannot thread these instantiations. *)
   simpLib.threaded_cong_ss bounded_exists_congs]

(* HOL4's list-equation procedure is the analogue of the one src/HOL/
   List.thy installs over [append1_eq_conv], [append_same_eq] and
   [same_append_eq]: cancelling a common prefix or suffix of an
   equation is a step no rewrite set takes by itself, and both sides
   want it.  HOL4's reaches it through a normal form the layer does not
   share -- it left-nests an append and turns a trailing cons into a
   singleton append -- and it leaves the term renested even when
   nothing cancelled, which is how a goal arrives at a source rule in a
   spelling the rule cannot read.  Running it and then putting the
   result back into the source's spelling keeps the cancellation and
   drops the normal form; a run that only renested becomes no step at
   all, and the fragment says so rather than reporting progress it did
   not make. *)
val source_spelling_conv =
  Rewrite.PURE_REWRITE_CONV
    [Conv.GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]

fun list_equation_conv term =
  let
    val cancelled = listSimps.LIST_EQ_SIMP_CONV term
    val respelled =
      Thm.TRANS cancelled
        (source_spelling_conv (boolSyntax.rhs (Thm.concl cancelled)))
      handle Conv.UNCHANGED => cancelled
  in
    if aconv (boolSyntax.rhs (Thm.concl respelled)) term then
      raise Conv.UNCHANGED
    else respelled
  end

val list_equation_ss =
  simpLib.name_ss "AUTO list EQ"
    (simpLib.conv_ss
       {name = "SOURCE_LIST_EQ_CONV",
        trace = 2,
        key =
          SOME ([],
                let
                  val left =
                    mk_var ("l1", listSyntax.mk_list_type Type.alpha)
                in
                  boolSyntax.mk_eq (left, mk_var ("l2", type_of left))
                end),
        conv = K (K list_equation_conv)})

(* Two spellings of one statement reach a rewrite as two terms.
   Isabelle never meets the difference -- its rule and its goal are
   stated in the same theory and already agree on the order of a
   conjunction and the side an equation is written on, so its
   simplifier needs no ordering step and carries none: [conj_ac],
   [disj_ac] and [eq_ac] are all stated in HOL.thy and none of them is
   [simp] there.  A translated goal does meet it, because the HOL4
   result answering the source's states the same fact in its own order,
   and what is left is an equivalence between a term and a permutation
   of itself.

   Ordering the goal instead is not open to this layer.  A conjunction
   carries its left conjuncts into the right one's context -- that is
   what [rev_conj_cong] is, and the corpus names it -- so reordering a
   conjunction takes away the context a conditional rewrite is
   discharged in; measured, an ambient AC fragment costs the
   translation theory's own proof of [source_set_zip].  So the
   permutation is *decided* rather than imposed: the two sides are
   ordered privately, and if they agree the equivalence is closed.  The
   goal is either proved or untouched, and no term anywhere is
   reordered. *)
local
  val permutation_frag =
    simpLib.SSFRAG
      {name = SOME "AUTOPERMNF",
       convs = [], congs = [], filter = NONE, dprocs = [],
       ac = [(boolTheory.CONJ_ASSOC, boolTheory.CONJ_COMM),
             (boolTheory.DISJ_ASSOC, boolTheory.DISJ_COMM)],
       rewrs = [(NONE, boolTheory.EQ_SYM_EQ)]}
  val permutation_ss = simpLib.mk_simpset [permutation_frag]
in
  fun ordered term =
    simpLib.SIMP_CONV permutation_ss [] term
    handle Conv.UNCHANGED => Thm.REFL term
end

(* The two cheap conditions a permutation satisfies, tested before
   anything is ordered: the equation is an equivalence -- the net keys
   on [=], which is polymorphic, so most of what reaches here is an
   equation between terms of some other type -- and reordering and
   turning round both preserve the size of a term. *)
fun could_be_permuted (left, right) =
  Type.compare (type_of left, Type.bool) = EQUAL andalso
  Term.term_size left = Term.term_size right andalso
  not (aconv left right)

fun permuted_equivalence_conv term =
  let
    val (left, right) = boolSyntax.dest_eq term
    val _ =
      if could_be_permuted (left, right) then ()
      else raise ERR "permuted_equivalence_conv" "not a permutation"
    val ordered_left = ordered left
    val ordered_right = ordered right
  in
    if aconv (boolSyntax.rhs (Thm.concl ordered_left))
             (boolSyntax.rhs (Thm.concl ordered_right))
    then
      Drule.EQT_INTRO (Thm.TRANS ordered_left (Thm.SYM ordered_right))
    else raise ERR "permuted_equivalence_conv" "not one statement"
  end

val permuted_equivalence_ss =
  simpLib.name_ss "AUTO permuted equivalence"
    (simpLib.conv_ss
       {name = "PERMUTED_EQUIVALENCE_CONV",
        trace = 2,
        key =
          SOME ([],
                boolSyntax.mk_eq
                  (mk_var ("permuted_left", Type.bool),
                   mk_var ("permuted_right", Type.bool))),
        conv = K (K permuted_equivalence_conv)})

(* [remove_ssfrags] signals an absent fragment by raising UNCHANGED.
   Reporting that is what keeps the replacement honest: a caught
   exception here would leave the strong congruence in place under a
   name that says otherwise. *)
fun weaken_cond_congruence ss =
  simpLib.++
    (simpLib.remove_ssfrags ["CONG"] ss
       handle Conv.UNCHANGED =>
         raise ERR "weaken_cond_congruence"
           "the simpset carries no CONG fragment to replace",
     weak_cong_ss)

val cond_depth = 40

(* The clasimp simpset in two layers.  [clasimp_core] is everything that
   does not depend on the [arith] facts of a context, and is derived once
   for an srw_ss.  [clasimp_with_facts] adds the linear-arithmetic layer,
   which is all the facts change, so a new fact list costs a fragment and
   a solver rather than a derivation, and the LHS views, which are derived
   from the core, are shared between fact lists (see [view_base]).  The
   linear-arithmetic fragment is added last: the one fragment after it in
   the original order, [ARITH_AC_ss], has no decision procedure, so the
   decision procedures are in the same order either way. *)
fun clasimp_core ss =
  ss
  |> weaken_cond_congruence
  |> simpLib.set_cond_depth cond_depth
  |> (fn ss' => simpLib.++ (ss', simpLib.split_ss))
  (* ETA_ss is where Isabelle's matcher is and HOL4's is not.  Isabelle
     rewrites under higher-order patterns, which are matched modulo eta,
     so a rule about [$+ start] fires on a goal spelled
     [\offset. start + offset] as well.  HOL4's rewriter matches up to
     alpha and beta only, so without this the two silently fail to meet;
     a translated term arrives in both spellings, since the translation
     writes the abstraction and the simplifier contracts it only
     sometimes.  The classical search does close some such goals on its
     own -- it is the rewriting that stops at the mismatch. *)
  |> (fn ss' => simpLib.++ (ss', boolSimps.ETA_ss))
  (* The same mismatch one spelling further on.  Isabelle normalises the
     natural number 1 to [Suc 0] -- One_nat_def is a simp rule there --
     so a fact stated on SUC fires against a goal that bounds by a
     numeral.  HOL4 normalises the other way, numerals being the normal
     form, and a cited SUC rule then never meets the goal.  SUC_FILTER
     closes the gap from HOL4's side, deriving the numeral-matching
     variant of each SUC rule as it enters, which leaves HOL4's normal
     form alone. *)
  |> (fn ss' => simpLib.++ (ss', numSimps.SUC_FILTER_ss))
  (* The same mismatch again, and this one HOL4's normal form cannot be
     left alone through.  Isabelle's [append_assoc] is a simp rule that
     reads into the right-nested form and its [append_Cons] keeps a cons
     at the front, so every source result about a walk down [xs @ ys] is
     stated of a right-nested append.  HOL4 exports [APPEND_ASSOC] as a
     rewrite in the other direction and [listSimps]' equation
     normalisation turns a trailing cons into a singleton append, so the
     same term arrives as [(xs ++ [y]) ++ zs]; a rule about the prefix
     every element satisfies then has to read [xs ++ [y]] as that
     prefix, which is false of [y], and it never fires.  The two
     directions cannot both be ambient -- each is the other's reverse
     and the pair loops -- and the layer needs neither: dropping HOL4's
     leaves an append with the nesting it was written with, which for a
     translated goal is the source's.  The cons clause of APPEND is simp
     on both sides and keeps a leading cons at the front.  The equation
     procedure the exclusion drops comes back respelled: cancelling is
     wanted, its normal form is not. *)
  |> simpLib.remove_simps ["APPEND_ASSOC"]
  |> simpLib.exclude_ssfrags ["list EQ"]
  |> (fn ss' => simpLib.++ (ss', list_equation_ss))
  (* The same mismatch in the premises.  src/HOL/HOL.thy declares
     [disj_not1] -- [~P \/ Q <=> (P ==> Q)] -- simp, so a negated
     conjunction or existential reaches a source rule as an implication;
     HOL4 stops at the disjunction its own de Morgan rules leave.  The
     difference is not cosmetic: the simplifier's condition solver
     discharges a conditional rewrite's side condition from
     [!item. MEM item prefix ==> ~predicate item] and not from
     [!item. ~MEM item prefix \/ ~predicate item], so a rule whose
     condition constrains the elements of a list stops firing at exactly
     the goals that state the constraint negatively.  Isabelle declares
     this direction only -- [disj_not2] is left out there for changing
     the orientation -- and HOL4 carries no rewrite the other way, so
     the pair cannot loop. *)
  |> (fn ss' =>
        simpLib.++ (ss',
          simpLib.rewrites [Conv.GSYM boolTheory.IMP_DISJ_THM]))
  (* The permutation decision, for the reason given at
     [permuted_equivalence_conv]. *)
  |> (fn ss' => simpLib.++ (ss', permuted_equivalence_ss))
  (* HOL4 carries no order reasoning ambiently: a goal that supplies its
     own order -- as a [WeakLinearOrder] premise, say -- has the axioms
     and the steps in the assumptions and nothing chains them.  Isabelle
     reads such a chain off the linorder class without naming it
     (Provers/order_tac.ML, installed by Orderings.thy).  The decision
     procedure covers both places a chain is wanted, since it is asked
     about an atom wherever the traversal meets one: the atom the
     rewriting has left standing, and the side condition of a conditional
     rewrite, which is simplified with this same simpset. *)
  |> (fn ss' => simpLib.++ (ss', orderLib.ORDER_ext_ss))
  (* The other half of the arithmetic layer.  HOL4's own arithmetic
     simproc fragment normalises a linear term as well as deciding an
     atom -- [std_ss ++ numSimps.ARITH_DP_ss] answers [LENGTH l - 1 - n]
     with [LENGTH l - (n + 1)] -- and the reducer of the facts layer only
     decides.  So two spellings of one term never met here: this simpset
     folds the repeated subtraction to [LENGTH l - (1 + n)] and leaves it
     beside [LENGTH l - (n + 1)].  [ARITH_AC_ss] is that normalisation on
     its own, and it is num only; the int and real instances have no AC
     fragment to point at, which is a limit of this line and not of the
     argument for it. *)
  |> (fn ss' => simpLib.++ (ss', numSimps.ARITH_AC_ss))
  |> simpLib.set_safe_solvers [safe_solver]
  |> simpLib.set_subgoaler witness_subgoaler

(* The unsafe side-condition solver added here reaches this simpset only:
   the simplifier offers unsafe solvers to every traversal regardless of
   the safe solvers, so a simpset with a normalisation phase to protect
   (aesop) names the decision procedures it wants rather than inheriting
   from here. *)
fun clasimp_with_facts core facts =
  (* Isabelle decides an arithmetic atom wherever the traversal meets
     one.  [Fields.thy]'s [fast_arith_nat] and [Int.thy]'s [fast_arith]
     are simprocs on [m < n], [m <= n] and [m = n], and the comment on
     the first says what the solver below is left with once they are
     there: the arithmetic solver "is really only useful to detect
     inconsistencies among the premises for subgoals which are not
     themselves (in)equalities, because the latter activate
     fast_nat_arith_simproc anyway".  The layer carried only that half,
     so an unfolded interval left a linear fact about num -- an atom in
     the goal rather than the condition of a rewrite -- standing. *)
  simpLib.++ (core, linarithLib.LINARITH_ext_ss_with facts)
  |> simpLib.add_unsafe_solver
       (linarithLib.linarith_solver_with_facts facts)

(* Generic abstraction arguments are keyed by constant identity and arity. *)
type abstraction_position = KernelSig.kernelid * int
val position_compare =
  Lib.pair_compare (KernelSig.id_compare, Int.compare)
val no_positions = HOLset.empty position_compare

fun rule_abstraction_positions theorem positions =
  let
    val fixed = free_varsl (hyp theorem)
    fun collect bound tm found =
      if is_abs tm then
        let val (v, body) = dest_abs tm
        in collect (v :: bound) body found end
      else if is_comb tm then
        let
          val (head, args) = strip_comb tm
          val constant = is_const head
          fun selected argument =
            if is_abs argument then
              let
                val (v, body) = dest_abs argument
                val pattern = if is_comb body then rator body else body
              in
                is_comb body andalso aconv (rand body) v andalso
                is_var pattern andalso not (aconv pattern v) andalso
                not (boolSyntax.tmem pattern bound) andalso
                not (boolSyntax.tmem pattern fixed)
              end
            else false
          (* Visit the outermost argument first, as in the walk down
             successive rators. Each is at a different partial arity. *)
          fun walk [] _ found = collect bound head found
            | walk (argument :: rest) arity found =
                let
                  val next =
                    if constant andalso selected argument then
                      let val {Name, ...} = Term.dest_thy_constid head
                      in HOLset.add (found, (Name, arity)) end
                    else found
                in
                  walk rest (arity - 1) (collect bound argument next)
                end
        in
          walk (List.rev args) (length args) found
        end
      else found
    fun statement tm found =
      let
        val body = #2 (boolSyntax.strip_forall tm)
        val result = #2 (boolSyntax.strip_imp_only body)
      in
        if boolSyntax.is_conj result then
          let val (left, right) = boolSyntax.dest_conj result
          in statement right (statement left found) end
        else
          collect [] (boolSyntax.lhs result handle HOL_ERR _ => result) found
      end
  in
    statement (concl theorem) positions
  end

(* Supplied rule sources share tails with cached ambient metadata. *)
val position_cache =
  ref ([] : ((simpLib.thname option * thm) list *
              abstraction_position HOLset.set) list)

fun positions_of_sources sources =
  let
    fun cached rules =
      List.find
        (fn (previous, _) => Portable.pointer_eq (previous, rules))
        (!position_cache)
    fun suffix rules pending =
      case cached rules of
          SOME entry => (entry, pending)
        | NONE =>
            case rules of
                [] => (([], no_positions), pending)
              | (_, theorem) :: rest => suffix rest (theorem :: pending)
    val (entry as (_, initial), added) = suffix sources []
    val result = List.foldl
      (fn (theorem, found) => rule_abstraction_positions theorem found)
      initial added
    val previous =
      List.filter
        (fn (key, _) => not (Portable.pointer_eq (key, sources)) andalso
                       not (Portable.pointer_eq (key, #1 entry)))
        (!position_cache)
    val anchor =
      if Portable.pointer_eq (sources, #1 entry) then [] else [entry]
    val count = 31 - length anchor
    val retained = List.take (previous, Int.min (count, length previous))
  in
    position_cache := (sources, result) :: (anchor @ retained);
    result
  end

fun position_policy charge positions : Traverse.child_first_policy =
  let
    fun keep tm =
      let
        val (head, args) = strip_comb tm
        val {Name, ...} = Term.dest_thy_constid head
      in
        HOLset.member (positions, (Name, length args))
      end
      handle HOL_ERR _ => false
  in
    {charge=charge, keep_abstraction=keep}
  end

fun abstraction_policy charge ss arguments =
  let
    val (sources,supplied) = simpLib.rewrite_sources ss arguments
    val positions = List.foldl
      (fn (theorem,found) => rule_abstraction_positions theorem found)
      (positions_of_sources sources) supplied
  in position_policy charge positions end

(* A simpset with its static ORDER and LINARITH decision procedures and
   its context-free arithmetic solver removed, and which of the three it
   carried.  The solver is looked for on its own: a simpset can carry it
   without the fragment, as aesop's does. *)
type decision_base =
  {stripped : simpLib.simpset, order : bool, linarith : bool,
   solver : bool}

(* Prepare once for the whole source inventory. No rule is selected by
   goal relevance or size. Opaque reducers conservatively defeat the
   indexed pre-test. Original rewrite controls are restored by simpLib. *)
datatype lhs_view_rejection =
    NoReducibleArguments | UnchangedLHS | JoinableLHS
  | RenamingUnstable | DerivationLimited | UnsupportedLHS

type lhs_view_entry =
  {origin : simpLib.rewrite_source,
   source : simpLib.thname option * thm, view : thm option,
   rejection : lhs_view_rejection option, footprint : term list,
   abstraction_positions : abstraction_position list, normalization : int}

fun rename_view_variables theorem =
  let
    val variables = Listsort.sort Term.compare
      (free_varsl (concl theorem :: hyp theorem))
    val width = size (Int.toString (length variables))
    val reversed = rev variables
    val fresh = List.tabulate (length variables,
      fn n => variant variables
        (mk_var ("lhs_view_" ^
                 StringCvt.padLeft #"0" width (Int.toString n),
                 type_of (List.nth (reversed,n)))))
    val replacements = ListPair.mapEq
      (fn (v,w) => {redex=v,residue=w}) (variables,rev fresh)
    val inverse = map
      (fn {redex,residue} => {redex=residue,residue=redex}) replacements
  in (Thm.INST replacements theorem,Term.subst inverse) end

fun frag_present ss =
  let val names = simpLib.ssfrag_names_of ss
  in fn name => Lib.mem name names end

fun remove_present_frags names ss =
  simpLib.remove_ssfrags_preserving_controls
    (List.filter (frag_present ss) names) ss
  handle Conv.UNCHANGED => ss

(* LHS views are derived once for a simpset and kept with it: they are a
   function of the simpset, which carries the bottom-up declarations of its
   context ([iff_bottom_up] below).  The linear-arithmetic procedures are
   stripped because views must not depend on arithmetic: they carry the
   [arith] facts of the context the simpset was derived for, and a view
   table is reused as the predecessor of another simpset's, which may
   carry other facts.  An invocation runs them on its goal with its own
   context.  Stripping them rebuilds the
   simpset, so it is done once for each simpset derived from.

   A derivation is given the simpset it derives from, the view base, and
   a table records it: whether a table is stale for a simpset is a
   question about their bases, not about the simpsets themselves, which
   differ in the linear-arithmetic layer alone when they carry other
   [arith] facts.  A clasimp-derived value supplies its core, which is
   that simpset without the layer; any other simpset's base is the strip.
   The base is delayed, so that a cache hit forces neither the core nor
   the strip.  A clasimp-derived value's base is the strip of its core
   with the bottom-up layer: the core keeps whatever linear-arithmetic
   procedures srw_ss itself carries.  The strip returns its argument where
   it has none. *)
type view_base = simpLib.simpset Susp.susp

fun strip_view_procedures ss =
  remove_present_frags [linarithLib.linarith_fragment_name] ss
  |> simpLib.remove_solver linarithLib.linarith_solver_name

val view_derivation_simpset =
  memoUtil.keyed_memo (Lib.curry Portable.pointer_eq) strip_view_procedures

fun stripped_view_base ss : view_base =
  Susp.delay (fn () => view_derivation_simpset ss)

fun prepare_lhs_view_derivation_with_positions caller_charge base positions =
  let
    exception DerivationLimit
    datatype candidate_result =
        Rejected of lhs_view_rejection
      | Candidate of term * term * thm
    val remaining = ref 20000
    val callback_failure = ref (NONE : exn option)
    val footprint = ref (HOLset.empty Term.compare)
    fun remember tm = footprint := HOLset.add (!footprint, tm)
    fun inventory tm =
      (remember tm;
       if is_comb tm then (inventory (rator tm); inventory (rand tm))
       else if is_abs tm then inventory (#2 (dest_abs tm))
       else ())
    fun charge () =
      if !remaining = 0 then raise DerivationLimit
      else
        (remaining := !remaining - 1;
         caller_charge ()
           handle e => (callback_failure := SOME e; raise e))
    val policy = position_policy charge positions
    val prepared =
      simpLib.prepare_child_first_observed remember policy base
    fun candidate theorem =
      let
        val specialised = Drule.SPEC_ALL theorem
        val _ = List.app inventory (concl specialised :: hyp specialised)
        val (premises, equation) =
          boolSyntax.strip_imp_only (concl specialised)
        val (left, right) = boolSyntax.dest_eq equation
      in
        if null premises andalso
           not (#may_reduce_arguments prepared left) then
          Rejected NoReducibleArguments
        else
          let
            val assumptions = map Thm.ASSUME premises
            val normal = #arguments prepared assumptions left
            val left' = boolSyntax.rhs (concl normal)
            val _ = inventory left'
          in
            if aconv left left' then Rejected UnchangedLHS
            else if aconv left' right then Rejected JoinableLHS
            else
              let
                val right_normal = #normalize prepared assumptions right
                val right' = boolSyntax.rhs (concl right_normal)
                val _ = inventory right'
                val body = List.foldl
                  (fn (p, th) => Thm.MP th (Thm.ASSUME p))
                  specialised premises
                val derived = Thm.TRANS (Thm.SYM normal) body
                val discharged = List.foldr
                  (fn (p, th) => Thm.DISCH p th) derived premises
              in
                if aconv left' right' then Rejected JoinableLHS
                else if not (null (hyp discharged)) then
                  Rejected UnsupportedLHS
                else Candidate (left', right', Drule.GEN_ALL discharged)
              end
          end
      end
    fun derive theorem =
      case candidate theorem of
          Rejected reason => (NONE, SOME reason)
        | Candidate (left, right, view) =>
            let val (other, undo) =
                  rename_view_variables (Drule.SPEC_ALL theorem)
            in
              case candidate other of
                  Candidate (left', right', _) =>
                    if aconv left (undo left') andalso
                       aconv right (undo right')
                    then (SOME view, NONE)
                    else (NONE, SOME RenamingUnstable)
                | Rejected _ => (NONE, SOME RenamingUnstable)
            end
    fun one origin : lhs_view_entry =
      let
        val source as (_, theorem) = simpLib.source_rewrite origin
        val _ = remaining := 20000
        val _ = callback_failure := NONE
        val _ = footprint := HOLset.empty Term.compare
        val (view, rejection) =
          derive theorem
          handle DerivationLimit => (NONE, SOME DerivationLimited)
               | HOL_ERR _ =>
                   (case !callback_failure of
                        SOME e => raise e
                      | NONE => (NONE, SOME UnsupportedLHS))
      in
        {origin=origin, source=source, view=view, rejection=rejection,
         footprint=HOLset.listItems (!footprint),
         abstraction_positions=HOLset.listItems
           (rule_abstraction_positions theorem no_positions),
         normalization=20000 - !remaining}
      end
  in one end

fun prepare_lhs_view_derivation caller_charge ss =
  prepare_lhs_view_derivation_with_positions caller_charge
    (view_derivation_simpset ss)
    (positions_of_sources (#1 (simpLib.rewrite_sources ss [])))

fun derive_lhs_view_entries caller_charge ss =
  map (prepare_lhs_view_derivation caller_charge ss)
      (simpLib.rewrite_source_handles ss)

fun derive_lhs_view_entries_with_positions caller_charge ss positions =
  map (prepare_lhs_view_derivation_with_positions caller_charge
        (view_derivation_simpset ss)
        (HOLset.addList (no_positions,positions)))
      (simpLib.rewrite_source_handles ss)

fun derive_lhs_views charge ss =
  List.mapPartial
    (fn ({source=(name, theorem), view,...} : lhs_view_entry) =>
      Option.map (fn derived => (name, theorem, derived)) view)
    (derive_lhs_view_entries charge ss)

(* Decision-fragment replay must retain consumed native rewrite controls. *)
fun strip_decisions ss =
  let
    val present = frag_present ss
    val removed =
      remove_present_frags ["ORDER", linarithLib.linarith_fragment_name] ss
    (* remove_solver gives back the simpset it was given when that has no
       solver of the name, so a change means the solver was there *)
    val stripped =
      simpLib.remove_solver linarithLib.linarith_solver_name removed
  in
    {stripped = stripped,
     order = present "ORDER",
     linarith = present linarithLib.linarith_fragment_name,
     solver = not (Portable.pointer_eq (stripped, removed))}
  end

fun supplied_view_associations entries = List.mapPartial
  (fn ({origin,view,...} : lhs_view_entry) =>
    Option.map (fn theorem => (origin,theorem)) view) entries

type source_set = simpLib.rewrite_source HOLset.set
type source_index = (simpLib.rewrite_source,lhs_view_entry) Binarymap.dict
type dependency_index = (KernelSig.kernelid,source_set) Binarymap.dict
type converse_rewriter = simpLib.rewrite_source * conv Susp.susp option
type rewrite_pattern_index = (converse_rewriter * hol_type) Net.net
datatype lhs_view_table = LHSViewTable of
  {simpset : simpLib.simpset, base : view_base,
   sources : simpLib.rewrite_source list, entries : lhs_view_entry list,
   index : source_index,
   heads : dependency_index,
   rewrite_patterns : rewrite_pattern_index Susp.susp,
   positions : abstraction_position HOLset.set,
   generation : int, derived : int, reused : int, rebuild : bool,
   normalization : int, full : simpLib.simpset Susp.susp,
   decisions : decision_base Susp.susp,plain : decision_base Susp.susp}

fun lhs_view_table_entries (LHSViewTable data) = #entries data
fun lhs_view_table_generation (LHSViewTable data) = #generation data
fun lhs_view_table_stats (LHSViewTable data) =
  {derived= #derived data,reused= #reused data,rebuild= #rebuild data,
   normalization= #normalization data}

val view_generation = ref 0
val source_compare = simpLib.rewrite_source_compare
val no_sources = HOLset.empty source_compare
val no_converse_rewriters : converse_rewriter HOLset.set =
  HOLset.empty (fn ((left, _), (right, _)) => source_compare (left, right))

(* Net.match conservatively indexes the same first-order patterns as
   REWR_CONV. Keep the type for the converse walk's compatibility check
   and share the matcher for each origin. Force it only after charging. *)
fun rewrite_pattern_index sources = List.foldl
  (fn (source,index) =>
    let
      val theorem = Drule.SPEC_ALL (#2 (simpLib.source_rewrite source))
      val left = boolSyntax.lhs
        (#2 (boolSyntax.strip_imp_only (concl theorem)))
      val rewrite =
        if HOLset.isEmpty (hypset theorem) andalso
           boolSyntax.is_eq (concl theorem) then
          SOME (Susp.delay (fn () => Conv.REWR_CONV theorem))
        else NONE
    in Net.insert (left,((source,rewrite),type_of left)) index end)
  Net.empty sources

fun table_indices entries =
  let
    fun entry (entry : lhs_view_entry,(sources,heads)) =
      let
        val origin = #origin entry
        fun add tm found =
          case Lib.total Term.dest_thy_constid (fst (strip_comb tm)) of
              NONE => found
            | SOME {Name,...} =>
                let
                  val previous = Option.getOpt
                    (Binarymap.peek (found,Name),no_sources)
                in Binarymap.insert (found,Name,HOLset.add (previous,origin))
                end
      in
        (Binarymap.insert (sources,origin,entry),
         List.foldl (fn (tm,index) => add tm index) heads (#footprint entry))
      end
  in
    List.foldl entry
      (Binarymap.mkDict source_compare,Binarymap.mkDict KernelSig.id_compare)
      entries
  end

(* Opaque reducers can change answers when their primed context changes. *)
fun update_lhs_view_table_with_positions caller_charge previous base ss
      positions =
  let
    val sources = simpLib.rewrite_source_handles ss
    val charged = ref 0
    fun charge () = (charged := !charged + 1; caller_charge ())
    fun key source =
      let
        val (_,theorem) = simpLib.source_rewrite source
      in
        (free_varsl (hyp theorem),
         boolSyntax.lhs (#2 (boolSyntax.strip_imp_only (concl theorem))))
      end
    fun retained index source =
      case Binarymap.peek (index,source) of
          NONE => NONE
        | SOME entry =>
            if simpLib.same_rewrite_source (source,#origin entry)
            then SOME entry else NONE
    fun affected heads keys =
      let
        fun add ((_,pattern),found) =
          case Lib.total Term.dest_thy_constid (fst (strip_comb pattern)) of
              NONE => NONE
            | SOME {Name,...} =>
                Option.map
                  (fn selected => HOLset.union
                    (selected,Option.getOpt (Binarymap.peek (heads,Name),
                                             no_sources))) found
        fun fold [] found = found
          | fold _ NONE = NONE
          | fold (pattern::rest) found = fold rest (add (pattern,found))
      in fold keys (SOME no_sources) end
    val (old_index,dirty,rebuild) =
      case previous of
          NONE => (Binarymap.mkDict source_compare,NONE,true)
        | SOME (LHSViewTable old) =>
            let
              val context = simpLib.rewrite_context_changes
                (Susp.force (#base old),Susp.force base)
              (* Append-mostly inventories share their unchanged suffix. *)
              fun additions remaining added =
                if Portable.pointer_eq (remaining,#sources old) then
                  SOME (rev added)
                else case remaining of
                         [] => NONE
                       | source::rest => additions rest (source::added)
              val (added,removed) =
                case additions sources [] of
                    SOME added =>
                      (* A shared suffix still has the last entry at
                         each old origin, including repeated origins. *)
                      (added, if Binarymap.numItems (#index old) =
                                 #derived old + #reused old
                              then []
                              else List.filter
                                (not o Option.isSome o retained (#index old))
                                (#sources old))
                  | NONE =>
                      let
                        val new_index = List.foldl
                          (fn (source,index) =>
                            Binarymap.insert (index,source,source))
                          (Binarymap.mkDict source_compare) sources
                        val added = List.filter
                          (not o Option.isSome o retained (#index old)) sources
                        val removed = List.filter
                          (fn source =>
                            case Binarymap.peek (new_index,source) of
                                NONE => true
                              | SOME current =>
                                  not (simpLib.same_rewrite_source
                                    (source,current)))
                          (#sources old)
                      in (added,removed) end
              val keys = map key (added @ removed) @ #keys context
              val full = #rebuild context orelse
                not (HOLset.equal (#positions old,positions)) orelse
                (#context_sensitive context andalso
                 not (null added andalso null removed andalso null keys))
              val selected = if full then NONE else affected (#heads old) keys
            in
              (#index old,selected,full orelse not (Option.isSome selected))
            end
    fun reusable source =
      case dirty of
          NONE => NONE
        | SOME found =>
            if HOLset.member (found,source) then NONE
            else retained old_index source
    val derived = ref 0
    val derive = Susp.delay (fn () =>
      prepare_lhs_view_derivation_with_positions charge (Susp.force base)
        positions)
    fun obtain source =
      case reusable source of
          NONE =>
            (derived := !derived + 1; Susp.force derive source)
        | SOME old =>
          {origin=source,source=simpLib.source_rewrite source,
           view= #view old,rejection= #rejection old,
           footprint= #footprint old,
           abstraction_positions= #abstraction_positions old,
           normalization= #normalization old}
    val entries = map obtain sources
    val (index,heads) = table_indices entries
    (* Only converse detection needs this index. Most table consumers use
       the views directly, and a prior converse binding can be reused. *)
    val rewrite_patterns = Susp.delay (fn () => rewrite_pattern_index sources)
    val full = Susp.delay (fn () =>
      case supplied_view_associations entries of
          [] => ss
        | views => simpLib.++ (ss,simpLib.name_ss "CLASIMP_REWRITE_VIEWS"
                                   (simpLib.rewrite_views views)))
    val _ = view_generation := !view_generation + 1
  in
    LHSViewTable
      {simpset=ss,base=base,sources=sources,entries=entries,index=index,
       heads=heads,
       rewrite_patterns=rewrite_patterns,
       positions=positions,generation= !view_generation,
       derived= !derived,reused=length sources - !derived,
       rebuild=rebuild,normalization= !charged,full=full,
       decisions=Susp.delay (fn () => strip_decisions (Susp.force full)),
       plain=Susp.delay (fn () => strip_decisions ss)}
  end

fun update_lhs_view_table caller_charge previous base ss =
  update_lhs_view_table_with_positions caller_charge previous base ss
    (positions_of_sources (#1 (simpLib.rewrite_sources ss [])))

(* Bounded memoization is independent of when callers request a table. *)
fun make_lhs_view_cache_of_base caller_charge =
  let
    val tables = ref ([] : lhs_view_table list)
    fun base_of (LHSViewTable data) = Susp.force (#base data)
    fun previous base ss sources =
      let
        (* Several tables can share the same native inventory while their
           conversions or decision procedures differ. Break that tie by
           actual context changes before choosing a predecessor. *)
        fun context_rank table =
          let val changes = simpLib.rewrite_context_changes
                (base_of table,Susp.force base)
          in
            (if #rebuild changes then 1 else 0,
             (if #context_sensitive changes then 1 else 0,
              length (#keys changes)))
          end
        val rank_compare = Lib.pair_compare
          (Int.compare,Lib.pair_compare (Int.compare,Int.compare))
        fun prefer (table,old) =
          if rank_compare (context_rank table,context_rank old) = LESS
          then table else old
        fun matching remaining = List.filter
          (fn LHSViewTable data =>
            Portable.pointer_eq (remaining,#sources data)) (!tables)
        fun suffix remaining =
          case matching remaining of
              first::rest => SOME (List.foldl prefer first rest)
            | [] => case remaining of [] => NONE | _::rest => suffix rest
        fun score (table as LHSViewTable data,(best,count)) =
          let
            val reused = List.foldl
              (fn (source,n) =>
                case Binarymap.peek (#index data,source) of
                    NONE => n
                  | SOME entry =>
                      if simpLib.same_rewrite_source (source,#origin entry)
                      then n+1 else n) 0 sources
          in
            if reused > count then (SOME table,reused)
            else if reused = count then
              (SOME (case best of NONE => table
                                 | SOME old => prefer (table,old)),count)
            else (best,count)
          end
      in
        case suffix sources of SOME table => SOME table
          | NONE => #1 (List.foldl score (NONE,~1) (!tables))
      end
    fun get base ss =
      case List.find
        (fn LHSViewTable data => Portable.pointer_eq (#simpset data,ss))
        (!tables) of
          SOME table => table
        | NONE =>
            let
              val table = update_lhs_view_table caller_charge
                (previous base ss (simpLib.rewrite_source_handles ss)) base ss
              val kept = List.take (!tables,Int.min (7,length (!tables)))
            in tables := table::kept; table end
  in get end

fun make_lhs_view_cache caller_charge =
  let val get = make_lhs_view_cache_of_base caller_charge
  in fn ss => get (stripped_view_base ss) ss end

fun marker_skip theorem =
  Option.isSome (clasetLib.marker_of theorem) orelse
  (case markerLib.dest_directive theorem of
       NONE => false
     | SOME (markerLib.DBounded (body,_)) =>
         marker_skip body
     | SOME _ => true)

datatype supplied_rule_binding = SuppliedRuleBinding of
  {bundle : simpLib.rewrite_bundle,controls : thm list,originals : thm list,
   positions : abstraction_position HOLset.set}

(* Bind before any first pass; deferred views must retain these origins. *)
fun prepare_supplied_rules ss arguments =
  let
    val (controls,originals) = List.partition marker_skip arguments
    val bundle = simpLib.prepare_rewrite_bundle ss originals
    val positions = List.foldl
      (fn ((_,sources),found) => List.foldl
        (fn (source,found) => rule_abstraction_positions
          (#2 (simpLib.source_rewrite source)) found) found sources)
      no_positions (simpLib.rewrite_bundle_rules bundle)
  in SuppliedRuleBinding
       {bundle=bundle,controls=controls,originals=originals,positions=positions}
  end

fun supplied_rule_controls (SuppliedRuleBinding data) = #controls data
fun supplied_rule_originals (SuppliedRuleBinding data) = #originals data
fun supplied_rule_policy charge ss (SuppliedRuleBinding data) =
  position_policy charge (HOLset.union (#positions data,
    positions_of_sources (#1 (simpLib.rewrite_sources ss []))))
fun install_supplied_rules (SuppliedRuleBinding {bundle,...}) =
  simpLib.install_rewrite_bundle bundle []

datatype supplied_view_binding = SuppliedViewBinding of
  {rules : supplied_rule_binding,entries : lhs_view_entry list,
   positions : abstraction_position HOLset.set,
   table : lhs_view_table,suspended : simpLib.rewrite_source list,
   normalization : int,derived : int,memoized : int}

fun supplied_view_entries (SuppliedViewBinding data) = #entries data
fun supplied_view_controls (SuppliedViewBinding data) =
  supplied_rule_controls (#rules data)
fun supplied_view_table (SuppliedViewBinding data) = #table data
fun supplied_view_suspended (SuppliedViewBinding data) = #suspended data
fun supplied_view_stats (SuppliedViewBinding data) =
  {normalization= #normalization data,derived= #derived data,
   memoized= #memoized data}
fun supplied_view_policy charge (SuppliedViewBinding data) =
  position_policy charge (#positions data)
fun install_supplied_views
      (SuppliedViewBinding {rules=SuppliedRuleBinding {bundle,...},
                            entries,suspended,...}) ss =
  simpLib.install_rewrite_bundle bundle (supplied_view_associations entries)
    (simpLib.suspend_rewrite_sources suspended ss)

(* Attach to surviving originals, including an already exhausted quota. *)
fun add_supplied_views (SuppliedViewBinding {entries,suspended,...}) ss =
  let val working = simpLib.suspend_rewrite_sources suspended ss
  in
    case supplied_view_associations entries of
        [] => working
      | views => simpLib.++ (working,simpLib.name_ss "SUPPLIED_REWRITE_VIEWS"
                                (simpLib.rewrite_views views))
  end

fun trace_suspended_converses level sources = List.app
  (fn source => traceUtil.trace level 1 (fn () =>
    "suspending ambient converse " ^
    (case simpLib.source_rewrite source of
         (SOME {Thy,Name},_) => Thy ^ "." ^ Name
       | (NONE,theorem) => Parse.thm_to_string theorem))) sources

type supplied_view_memo =
  {generation : int,theorem : thm,
   positions : abstraction_position HOLset.set,
   sources : (simpLib.thname option * thm) list,
   entries : lhs_view_entry list option,
   converses : (simpLib.rewrite_source list * int) option}

(* Replay each unit before returning a cached theorem, including cutoffs. *)
fun replay_normalization charge units =
  let fun loop 0 = () | loop n = (charge (); loop (n-1))
  in loop units end

fun converse_sources caller_charge patterns sources =
  let
    val callback_failure = ref (NONE : exn option)
    fun charge () = caller_charge ()
      handle e => (callback_failure := SOME e; raise e)
    fun check_callback () =
      case !callback_failure of NONE => () | SOME e => raise e
    (* Cache both root matches and their union over the RHS subtree.
       Descend only where the origin can match; attempt a rewrite only
       at a possible root. The actual conversion still establishes the
       one parallel rewrite predicate, without normalizing either side. *)
    val subtrees = ref (Binarymap.mkDict Term.compare)
    fun candidates tm =
      (charge ();
       case Binarymap.peek (!subtrees,tm) of
           SOME found => found
         | NONE =>
             let
               fun add ((rewriter,pattern_type),found) =
                 let
                   val _ = charge ()
                 in
                   if Lib.can (Type.match_type pattern_type)
                        (type_of tm) then HOLset.add (found,rewriter)
                   else found
                 end
               val own =
                 List.foldl add no_converse_rewriters (Net.match tm patterns)
               val found = if is_comb tm then
                   HOLset.union (own,HOLset.union
                     (#2 (candidates (rator tm)),#2 (candidates (rand tm))))
                 else if is_abs tm then
                   HOLset.union (own,#2 (candidates (#2 (dest_abs tm))))
                 else own
               val result = (own,found)
               val _ = subtrees := Binarymap.insert (!subtrees,tm,result)
             in result end)
    fun once rewriter rewrite tm =
      let val (own,below) = candidates tm
      in
        if not (HOLset.member (below,rewriter)) then raise Conv.UNCHANGED
        else if HOLset.member (own,rewriter) then Conv.TRY_CONV
          (Conv.ORELSEC
            (fn target => (charge (); rewrite target),
             Conv.SUB_CONV (once rewriter rewrite))) tm
        else Conv.SUB_CONV (once rewriter rewrite) tm
      end
    fun converse source found =
      let
        val supplied = Drule.SPEC_ALL (#2 (simpLib.source_rewrite source))
        val (left,right) = boolSyntax.dest_eq
          (#2 (boolSyntax.strip_imp_only (concl supplied)))
        fun consider (rewriter as (origin,prepared),found) =
          case prepared of
              NONE => found
            | SOME matcher =>
                let
                  val _ = charge ()
                  val rewrite = Susp.force matcher
                  val result = Conv.QCONV (once rewriter rewrite) right
                  val _ = check_callback ()
                in
                  if aconv (boolSyntax.rhs (concl result)) left then
                    HOLset.add (found,origin) else found
                end
      in
        List.foldl consider found (HOLset.listItems (#2 (candidates right)))
      end
      handle HOL_ERR _ => (check_callback (); found)
  in
    List.foldl (fn (source,found) => converse source found) no_sources sources
  end

fun compatible_supplied_source (source,(old_name,old_theorem)) =
  let val (name,theorem) = simpLib.source_rewrite source
  in
    name = old_name andalso
    (Portable.pointer_eq (theorem,old_theorem) orelse
     (aconv (concl theorem) (concl old_theorem) andalso
      HOLset.equal (hypset theorem,hypset old_theorem)))
  end

(* Derivation can invoke callers, which may themselves use the cache. *)
fun store_supplied_memo memo scanned previous matches entry =
  let
    val current = !memo
    val others =
      if Option.isSome previous orelse
         not (Portable.pointer_eq (current,scanned)) then
        List.filter (not o matches) current
      else current
    val kept = List.take (others,Int.min (255,length others))
  in
    memo := entry::kept
  end

datatype supplied_converse_binding = SuppliedConverseBinding of
  {rules : supplied_rule_binding,ambient : simpLib.simpset,
   working : simpLib.simpset,positions : abstraction_position HOLset.set,
   suspended : simpLib.rewrite_source list,charge : unit -> unit,
   normalization : int,derived : int,memoized : int}

type converse_inventory =
  {simpset : simpLib.simpset,generation : int,
   positions : abstraction_position HOLset.set,
   patterns : rewrite_pattern_index}

fun make_supplied_converse_cache () =
  let
    val inventories = ref ([] : converse_inventory list)
    val generation = ref 0
    val memo = ref ([] : supplied_view_memo list)
    val masked = ref ([] : (int * source_set * simpLib.simpset) list)
    fun inventory ss =
      case List.find (fn (data : converse_inventory) =>
        Portable.pointer_eq (#simpset data,ss)) (!inventories) of
          SOME data => data
        | NONE =>
            let
              val patterns = rewrite_pattern_index
                (simpLib.rewrite_source_handles ss)
              val positions = positions_of_sources
                (#1 (simpLib.rewrite_sources ss []))
              val _ = generation := !generation + 1
              val data = {simpset=ss,generation= !generation,
                          patterns=patterns,positions=positions}
              val kept = List.take
                (!inventories,Int.min (7,length (!inventories)))
            in inventories := data::kept; data end
    fun working (data : converse_inventory) suspended =
      if HOLset.isEmpty suspended then #simpset data
      else case List.find
        (fn (generation,previous,_) => generation = #generation data andalso
          HOLset.equal (previous,suspended)) (!masked) of
          SOME (_,_,ss) => ss
        | NONE =>
            let
              val ss = simpLib.suspend_rewrite_sources
                (HOLset.listItems suspended) (#simpset data)
              val kept = List.take (!masked,Int.min (7,length (!masked)))
            in masked := (#generation data,suspended,ss)::kept; ss end
    fun bind caller_charge ambient
          (binding as SuppliedRuleBinding {bundle,positions,...}) =
      let
        val rules = simpLib.rewrite_bundle_rules bundle
        val has_sources = List.exists (not o null o #2) rules
        val input = if has_sources then SOME (inventory ambient) else NONE
        val initial_positions = HOLset.union (positions,
          case input of SOME data => #positions data
            | NONE => positions_of_sources
                (#1 (simpLib.rewrite_sources ambient [])))
        val charged = ref 0
        val derived = ref 0
        val memoized = ref 0
        fun charge () = (caller_charge (); charged := !charged + 1)
        fun detect (data : converse_inventory) (theorem,sources) =
          let
            fun matches (entry : supplied_view_memo) =
              #generation entry = #generation data andalso
              Portable.pointer_eq (#theorem entry,theorem) andalso
              HOLset.equal (#positions entry,initial_positions) andalso
              ListPair.allEq compatible_supplied_source
                (sources,#sources entry)
            val scanned = !memo
            val previous = List.find matches scanned
          in
            case Option.mapPartial #converses previous of
                SOME (suspended,units) =>
                  (replay_normalization charge units;
                   memoized := !memoized + 1; suspended)
              | NONE =>
                  let
                    val start = !charged
                    val suspended = HOLset.listItems (converse_sources charge
                      (#patterns data) sources)
                    val entry =
                      {generation= #generation data,theorem=theorem,
                       positions=initial_positions,
                       sources=map simpLib.source_rewrite sources,entries=NONE,
                       converses=SOME (suspended,!charged-start)}
                    val _ =
                      store_supplied_memo memo scanned previous matches entry
                    val _ = derived := !derived + 1
                  in suspended end
          end
        val suspended = case input of NONE => no_sources
          | SOME data => HOLset.addList
              (no_sources,List.concat (map (detect data) rules))
        val working = case input of NONE => ambient
          | SOME data => working data suspended
        val effective_positions =
          if HOLset.isEmpty suspended then initial_positions
          else HOLset.union (positions,positions_of_sources
            (#1 (simpLib.rewrite_sources working [])))
      in SuppliedConverseBinding
           {rules=binding,ambient=ambient,working=working,
            positions=effective_positions,charge=caller_charge,
            suspended=HOLset.listItems suspended,normalization= !charged,
            derived= !derived,memoized= !memoized}
      end
  in bind end

fun supplied_converse_rules (SuppliedConverseBinding data) = #rules data
fun supplied_converse_working (SuppliedConverseBinding data) = #working data
fun supplied_converse_policy (SuppliedConverseBinding data) =
  position_policy (#charge data) (#positions data)
fun supplied_converse_suspended (SuppliedConverseBinding data) = #suspended data
fun supplied_converse_stats (SuppliedConverseBinding data) =
  {normalization= #normalization data,derived= #derived data,
   memoized= #memoized data}

fun make_supplied_view_cache_core () =
  let
    val memo = ref ([] : supplied_view_memo list)
    val adjusted = ref
      ([] : (int * source_set * abstraction_position HOLset.set *
             lhs_view_table) list)
    (* Supplied rules affect policy, never the ambient reducer inventory. *)
    fun working_table (ambient as LHSViewTable table) suspended supplied
          prepared =
      let
        val already_masked = case prepared of
            SOME ss => Portable.pointer_eq (ss,#simpset table)
          | NONE => false
        val effective_suspension = if already_masked then no_sources
          else suspended
      in
      if HOLset.isEmpty effective_suspension andalso
         HOLset.isSubset (supplied,#positions table) then ambient
      else
        case List.find
          (fn (generation,previous,positions,_) =>
            generation = #generation table andalso
            HOLset.equal (previous,suspended) andalso
            HOLset.equal (positions,supplied)) (!adjusted) of
            SOME (_,_,_,table) => table
          | NONE =>
              let
                val ss = case prepared of SOME ss => ss
                  | NONE => if HOLset.isEmpty suspended then #simpset table
                    else simpLib.suspend_rewrite_sources
                      (HOLset.listItems suspended) (#simpset table)
                val positions = if HOLset.isEmpty effective_suspension then
                    #positions table
                  else positions_of_sources
                    (#1 (simpLib.rewrite_sources ss []))
                (* ss is the table's simpset or its suspension by
                   `suspended` (a prepared simpset is the latter, by the
                   check in bind), so the base is the table's base,
                   suspended the same way. *)
                val base =
                  if Portable.pointer_eq (ss,#simpset table) then #base table
                  else Susp.delay (fn () =>
                    simpLib.suspend_rewrite_sources
                      (HOLset.listItems suspended) (Susp.force (#base table)))
                val next = update_lhs_view_table_with_positions
                  (fn () => ()) (SOME ambient) base ss
                  (HOLset.union (positions,supplied))
                val kept = List.take
                  (!adjusted,Int.min (7,length (!adjusted)))
              in
                adjusted := (#generation table,suspended,supplied,next)::kept;
                next
              end
      end
    fun matching generation positions theorem sources
          (entry : supplied_view_memo) =
      #generation entry = generation andalso
      Portable.pointer_eq (#theorem entry,theorem) andalso
      HOLset.equal (#positions entry,positions) andalso
      ListPair.allEq compatible_supplied_source
        (sources,#sources entry)
    fun rebind (source,old : lhs_view_entry) : lhs_view_entry =
      {origin=source,source=simpLib.source_rewrite source,
       view= #view old,rejection= #rejection old,footprint= #footprint old,
       abstraction_positions= #abstraction_positions old,
       normalization= #normalization old}
    fun bind prior caller_charge (ambient as LHSViewTable table)
          (binding as SuppliedRuleBinding
            {bundle,positions=supplied_positions,...}) =
      let
        val rules = simpLib.rewrite_bundle_rules bundle
        val initial_positions = HOLset.union
          (#positions table,supplied_positions)
        val _ = case prior of NONE => ()
          | SOME (SuppliedConverseBinding data) =>
              if Portable.pointer_eq (#simpset table,#ambient data) orelse
                 Portable.pointer_eq (#simpset table,#working data) then ()
              else raise ERR "make_supplied_view_cache_after"
                "ambient table belongs to another binding"
        val charged = ref (case prior of NONE => 0
          | SOME (SuppliedConverseBinding data) => #normalization data)
        fun charge () = (caller_charge (); charged := !charged + 1)
        fun detect (theorem,sources) =
          let
            val matches = matching (#generation table) initial_positions
              theorem sources
            val scanned = !memo
            val previous = List.find matches scanned
          in
            case Option.mapPartial #converses previous of
                SOME (suspended,units) =>
                  (replay_normalization charge units; suspended)
              | NONE =>
                  let
                    val start = !charged
                    val suspended =
                      if null sources then []
                      else HOLset.listItems
                        (converse_sources charge
                          (Susp.force (#rewrite_patterns table))
                          sources)
                    val entry =
                      {generation= #generation table,theorem=theorem,
                       positions=initial_positions,
                       sources=map simpLib.source_rewrite sources,
                       entries=Option.mapPartial #entries previous,
                       converses=SOME (suspended,!charged-start)}
                    val _ =
                      store_supplied_memo memo scanned previous matches entry
                  in suspended end
          end
        val suspended = HOLset.addList (no_sources,case prior of
            NONE => List.concat (map detect rules)
          | SOME (SuppliedConverseBinding data) => #suspended data)
        val prepared = case prior of NONE => NONE
          | SOME (SuppliedConverseBinding data) => SOME (#working data)
        val effective as LHSViewTable working =
          working_table ambient suspended supplied_positions prepared
        val positions = #positions working
        val _ = case prior of NONE => ()
          | SOME (SuppliedConverseBinding data) =>
              if HOLset.equal (positions,#positions data) then ()
              else raise ERR "make_supplied_view_cache_after"
                "ambient table has another abstraction policy"
        val derive = Susp.delay (fn () =>
          prepare_lhs_view_derivation_with_positions charge
            (Susp.force (#base working)) positions)
        val derived = ref 0
        val memoized = ref 0
        fun one (theorem,sources) =
          let
            val matches = matching (#generation working) positions
              theorem sources
            val scanned = !memo
            val previous = List.find matches scanned
          in
            case Option.mapPartial #entries previous of
                SOME old_entries =>
                  let
                    val entries = ListPair.mapEq rebind (sources,old_entries)
                    val _ = List.app
                      (fn (entry : lhs_view_entry) =>
                        replay_normalization charge (#normalization entry))
                      entries
                    val _ = memoized := !memoized + 1
                  in entries end
              | NONE =>
                  let
                    val entries = map (Susp.force derive) sources
                    val entry =
                      {generation= #generation working,theorem=theorem,
                       positions=positions,
                       sources=map simpLib.source_rewrite sources,
                       entries=SOME entries,
                       converses=Option.mapPartial #converses previous}
                    val _ =
                      store_supplied_memo memo scanned previous matches entry
                    val _ = derived := !derived + 1
                  in entries end
          end
        val entries = List.concat (map one rules)
      in
        SuppliedViewBinding
          {rules=binding,entries=entries,positions=positions,
           table=effective,suspended=HOLset.listItems suspended,
           normalization= !charged,derived= !derived,memoized= !memoized}
      end
  in
    {bind=bind NONE,
     after=fn table => fn early as SuppliedConverseBinding data =>
       bind (SOME early) (#charge data) table (#rules data)}
  end

fun make_supplied_view_cache () = #bind (make_supplied_view_cache_core ())
fun make_supplied_view_cache_after () =
  #after (make_supplied_view_cache_core ())

datatype bound_simplification = BoundSimplification of
  {rules : supplied_rule_binding,policy : Traverse.child_first_policy,
   initial : simpLib.simpset,viewed : simpLib.simpset Susp.susp}

val bound_supplied_views = make_supplied_view_cache_after ()

fun make_bound_simplification prepare_runtime provide_table early =
  let
    val rules as SuppliedRuleBinding {bundle,...} =
      supplied_converse_rules early
    val raw = supplied_converse_working early
    val prepared = prepare_runtime raw
    val initial = if null (supplied_rule_originals rules) then prepared
      else install_supplied_rules rules prepared
    fun viewed () =
      let
        val binding = bound_supplied_views (provide_table ()) early
        val ambient = supplied_view_associations
          (lhs_view_table_entries (supplied_view_table binding))
        val with_ambient = case ambient of [] => initial
          | _ => simpLib.++ (initial,simpLib.name_ss "CLASIMP_REWRITE_VIEWS"
              (simpLib.rewrite_views ambient))
        (* Ambient aliases cannot outrank the caller's installed rules. *)
        val originals = if null ambient then [] else List.concat
          (map (fn (_,sources) => map
            (fn source => (source,#2 (simpLib.source_rewrite source))) sources)
            (simpLib.rewrite_bundle_rules bundle))
        val ordered = case originals of [] => with_ambient
          | _ => simpLib.++
              (with_ambient,simpLib.name_ss "SUPPLIED_REWRITE_PRECEDENCE"
                (simpLib.rewrite_views originals))
      in add_supplied_views binding ordered end
  in BoundSimplification
       {rules=rules,policy=supplied_converse_policy early,initial=initial,
        viewed=Susp.delay viewed}
  end

fun bound_simplification_simpset viewed (BoundSimplification data) =
  if viewed then Susp.force (#viewed data) else #initial data

fun bound_simplification_policy (BoundSimplification data) = #policy data

(* Residual goals continue with views under the same bound occurrences,
   normalization callback and invocation budget; completed proofs remain. *)
fun deferred_view_tactic make goal ctxt =
  let
    val initial = (SOME (make false goal ctxt),NONE)
      handle error as HOL_ERR _ => (NONE,SOME error)
    fun continue answer =
      Tactical.THEN
        ((fn _ => fn _ => answer),
         (fn current => fn context => make true current context)) goal ctxt
      handle HOL_ERR _ => answer
  in
    case initial of
        (SOME ([],validate),_) => ([],validate)
      | (SOME answer,_) => continue answer
      | (_,SOME error) => (make true goal ctxt handle HOL_ERR _ => raise error)
      | _ => raise ERR "deferred_view_tactic" "missing first result"
  end

datatype working_simpset = WorkingSimpset of
  {original : simpLib.simpset,table : lhs_view_table Susp.susp,
   full : simpLib.simpset Susp.susp,
   decisions : decision_base Susp.susp,plain : decision_base Susp.susp}

fun working_original (WorkingSimpset data) = #original data
fun working_view_table (WorkingSimpset data) = Susp.force (#table data)
fun working_full_simpset (WorkingSimpset data) = Susp.force (#full data)
fun working_decision_base (WorkingSimpset data) =
  Susp.force (#decisions data)
fun working_plain_decision_base (WorkingSimpset data) =
  Susp.force (#plain data)

(* Retain lazy working states as well as completed predecessor tables.
   Forcing plain decisions cannot trigger ambient view construction. *)
fun make_working_simpset_cache_of_base caller_charge =
  let
    val tables = make_lhs_view_cache_of_base caller_charge
    val states = ref ([] : working_simpset list)
    fun get base ss =
      case List.find
        (fn state => Portable.pointer_eq (working_original state,ss))
        (!states) of
          SOME state => state
        | NONE =>
            let
              val table = Susp.delay (fn () => tables base ss)
              val full = Susp.delay (fn () =>
                let val LHSViewTable data = Susp.force table
                in Susp.force (#full data) end)
              val state = WorkingSimpset
                {original=ss,table=table,full=full,
                 decisions=Susp.delay (fn () =>
                   let val LHSViewTable data = Susp.force table
                   in Susp.force (#decisions data) end),
                 plain=Susp.delay (fn () => strip_decisions ss)}
              val kept = List.take (!states,Int.min (7,length (!states)))
            in states := state::kept; state end
  in get end

fun make_working_simpset_cache caller_charge =
  let val get = make_working_simpset_cache_of_base caller_charge
  in fn ss => get (stripped_view_base ss) ss end

val cached_working_simpset = make_working_simpset_cache_of_base (fn () => ())

(* Materialize the adjusted table, never its earlier raw-simpset policy. *)
fun working_simpset_for (SuppliedViewBinding {table,...}) =
  let val LHSViewTable data = table
  in WorkingSimpset
       {original= #simpset data,table=Susp.delay (fn () => table),
        full= #full data,decisions= #decisions data,plain= #plain data}
  end

(* BasicProvers supplies the initialization seed, not the predecessor,
   lifted into the extension engine.  The bounded identity/source memo
   above retains completed tables across changes; the derived value owns
   its lazy working state, for the simpset ss whose LHS views derive from
   base. *)
fun owned_working_simpset base ss = cached_working_simpset base ss

(* The bottom-up declarations are one srw_ss fragment ([bottom_up_fragment]
   below).  The simpsets this layer derives from srw_ss take it as a layer
   of their own, added after what they derive from the rest of srw_ss.
   [layered_srw_derivation {base, layered}] memoises [base] of srw_ss
   without the fragment on that srw_ss (by identity), and [layered] of
   that and of the fragment on the fragment's identity: [layered derived
   add] receives the delayed [base] and [add], which adds the layer to a
   simpset (or leaves it, when srw_ss carries no declaration).  Going back
   to a recent srw_ss answers what it had. *)
val bottom_up_fragment_name = "clasimp-bottom-up"

fun same_layer (NONE, NONE) = true
  | same_layer (SOME f, SOME g) = Portable.pointer_eq (f, g)
  | same_layer _ = false

fun layered_srw_derivation {base, layered} =
  let
    fun add_layer NONE ss = ss
      | add_layer (SOME layer) ss = simpLib.++ (ss, layer)
    val by_srw =
      memoUtil.bounded_memo 4 (fn a => fn b => Portable.pointer_eq (a, b))
        (fn srw =>
           let
             val derived = Susp.delay (fn () =>
               base (simpLib.remove_ssfrags [bottom_up_fragment_name] srw
                     handle Conv.UNCHANGED => srw))
           in
             memoUtil.bounded_memo 4 (fn a => fn b => same_layer (a, b))
               (fn layer => layered derived (add_layer layer))
           end)
  in
    fn srw =>
      let
        val layer =
          List.find
            (fn f => simpLib.frag_name f = SOME bottom_up_fragment_name)
            (simpLib.ssfrags_of srw)
      in
        by_srw srw layer
      end
  end

(* The derived value is a function of the srw_ss and of the context's
   [arith] facts.  The core is derived once for srw_ss without its
   bottom-up layer, when first needed; the layer goes on top of it, and
   each fact list builds only the facts layer on that.  The lists,
   compared element-wise by identity, key a memo of the four most recent,
   so going back to an earlier fact list answers the value it had,
   working state and LHS views included.  The bound is 4 because each
   entry keeps a full simpset with its working state and view tables
   alive, and the observed alternation uses two fact lists.  The views
   derive from the strip of the core with the bottom-up layer, so they
   follow the declarations and do not depend on arithmetic. *)
fun derive_clasimp_value core base facts =
  let val full = clasimp_with_facts (Susp.force core) facts
  in {full = full,
      positions = positions_of_sources
        (#1 (simpLib.rewrite_sources full [])),
      working = owned_working_simpset base full}
  end

val clasimp_value_of_srw =
  layered_srw_derivation
    {base = fn lifted =>
       let val core = clasimp_core lifted
       in (core, Susp.delay (fn () => strip_view_procedures core)) end,
     layered = fn derived => fn add =>
       let
         val core = Susp.delay (fn () => add (#1 (Susp.force derived)))
         val base = Susp.delay (fn () =>
           add (Susp.force (#2 (Susp.force derived))))
       in
         memoUtil.bounded_memo 4 (Lib.list_eq (Lib.curry Portable.pointer_eq))
           (derive_clasimp_value core base)
       end}

val {get = _, get_of = clasimp_derived_of} =
  BasicProvers.make_simpset_derived_value "clasimpLib.clasimp_ss"
    (fn ss => fn _ => clasimp_value_of_srw ss)
    (fn _ => {full = simpLib.empty_ss, positions = no_positions,
              working = owned_working_simpset
                          (Susp.delay (fn () => simpLib.empty_ss))
                          simpLib.empty_ss})

val selected_default = ref (NONE : working_simpset option)

fun clasimp_value_of ctxt =
  let val value =
        clasimp_derived_of ctxt (linarithData.arith_facts_of ctxt)
  in selected_default := SOME (#working value); value end

fun clasimp_value () = clasimp_value_of (Context.snapshot ())

fun clasimp_ss_of ctxt = #full (clasimp_value_of ctxt)
fun clasimp_ss () = clasimp_ss_of (Context.snapshot ())

fun clasimp_working_simpset_of ctxt = #working (clasimp_value_of ctxt)
fun clasimp_working_simpset () =
  clasimp_working_simpset_of (Context.snapshot ())

fun working_simpset_of ss =
  case !selected_default of
      SOME state =>
        if Portable.pointer_eq (ss,working_original state) then state
        else cached_working_simpset (stripped_view_base ss) ss
    | NONE => cached_working_simpset (stripped_view_base ss) ss

fun clasimp_decision_base () =
  working_plain_decision_base (clasimp_working_simpset ())

(* Isabelle's asm_full_simp_tac simplifies premises mutually and turns the
   mksimps_pairs decomposition of premises into usable rewrites.

   strip=true       decomposes simplified conjunction, existential and
                    implication assumptions, covering that premise view;
   elimvars=false   avoids HOL4's stronger, Isabelle-incompatible
                    substitution and deletion of variable equations;
   droptrues=true   removes premises simplified to T, as implication
                    simplification does;
   oldestfirst=true visits assumptions in their original implication order.

   The extended flags supply mut_impc parity: the conclusion participates
   in the fixpoint and implication-shaped rewrites can rebuild the goal.
   The premises mut_impc is mutual over are the subgoal's, which a
   translated source result states as the antecedents of its conclusion,
   so imp_premises discharges those before the fixpoint; without it a
   goal stating its premises that way reaches the simplifier through the
   implication congruence alone, which offers a premise only the ones
   before it. *)
val asm_full_simp_base : simpLib.simptac_config =
  {strip = true, elimvars = false, droptrues = true, oldestfirst = true}

val asm_full_simp_config : simpLib.xsimptac_config =
  {base = asm_full_simp_base,
   concl_in_fixpoint = true,
   imp_rebuild = true,
   imp_premises = true}

(* Each public tactic application owns this allocation. Nested simplifier
   passes receive the same callback, including passes installed as search
   wrappers. The million-unit default includes nested arithmetic and
   order proofs; a lower cap clipped finite seed simplification. The
   explicit budgeted entry point can choose other limits. *)
fun normalization_budget () =
  searchBudget.create
    {candidates = NONE, applications = NONE,
     normalization = SOME 1000000}

fun charge_normalization budget () =
  searchBudget.charge budget searchBudget.Normalization

(* Replace the static decision procedures only for this tactic invocation.
   Their legacy fragments remain available to standalone simpsets, while
   this copy shares the caller's budget and explicit proof context. *)
fun budgeted_decisions_of ctxt budget
      ({stripped, order, linarith, solver} : decision_base) =
  let
    val with_order =
      if order then
        simpLib.++ (stripped, orderLib.ORDER_ext_ss_budgeted budget)
      else stripped
    val with_linarith =
      if linarith then
        simpLib.++
          (with_order, linarithLib.LINARITH_ext_ss_budgeted ctxt budget)
      else with_order
  in
    if linarith orelse solver then
      simpLib.add_unsafe_solver
        (linarithLib.linarith_solver_budgeted ctxt budget)
        with_linarith
    else with_linarith
  end

fun budgeted_decisions ctxt budget ss =
  budgeted_decisions_of ctxt budget
    (working_plain_decision_base (working_simpset_of ss))

val bound_converses = make_supplied_converse_cache ()

fun strip_requirements theorem =
  let
    val theorem = Option.getOpt (markerLib.dest_Req0 theorem,theorem)
  in Option.getOpt (markerLib.dest_ReqD theorem,theorem) end

fun is_requirement theorem =
  Option.isSome (markerLib.dest_Req0 theorem) orelse
  Option.isSome (markerLib.dest_ReqD theorem)

fun is_tactic_control theorem =
  case markerLib.dest_directive theorem of
      SOME markerLib.DNoAsms => true
    | SOME (markerLib.DIgnAsm _) => true
    | SOME (markerLib.DAbbr _) => true
    | SOME (markerLib.DLabel _) => true
    | _ => false

fun is_assumption_control theorem =
  case markerLib.dest_directive theorem of
      SOME markerLib.DNoAsms => true
    | SOME (markerLib.DIgnAsm _) => true
    | _ => false

fun prepare_invocation_rules ss arguments =
  let
    val controls = List.filter
      (fn theorem => is_requirement theorem orelse is_tactic_control theorem)
      arguments
    val (ambient,originals) = simpLib.prepare_rewrite_arguments ss
      (map strip_requirements arguments)
    val SuppliedRuleBinding data = prepare_supplied_rules ambient originals
    val rules = SuppliedRuleBinding
      {bundle= #bundle data,controls=controls @ #controls data,
       originals= #originals data,positions= #positions data}
  in (ambient,rules) end

fun prepare_bound_rules level runtime charge ambient rules =
  let
    val early = bound_converses charge ambient rules
    val _ =
      trace_suspended_converses level (supplied_converse_suspended early)
    val working = working_simpset_of ambient
  in make_bound_simplification runtime
       (fn () => working_view_table working) early end

fun prepare_bound_simplification level runtime charge ss arguments =
  let val (ambient,rules) = prepare_invocation_rules ss arguments
  in prepare_bound_rules level runtime charge ambient rules end

(* A generic callback can pass its simpset to a CS tactic and discard its
   theorem list. Keep compiled supplied origins and facts scoped to that
   callback application, rather than reclassifying them as ambient rules. *)
type callback_binding =
  {simpset : simpLib.simpset,ambient : simpLib.simpset,
   rules : supplied_rule_binding,environment : clasetFacts.environment,
   base_cs : clasetLib.claset,controls : thm list,
   active : (searchBudget.budget * bound_simplification) option ref}

val callback_bindings = ref ([] : callback_binding list)

fun callback_binding_for ss = List.find
  (fn binding => Portable.pointer_eq (ss,#simpset binding))
  (!callback_bindings)

fun with_callback_binding binding action =
  let val saved = !callback_bindings
  in
    callback_bindings := binding::saved;
    Portable.finally (fn () => callback_bindings := saved) action ()
  end

fun ambient_simp policy safe ss =
  simpLib.GEN_GLOBAL_SIMP_TAC_CHILD_FIRST
    policy {safe = safe} asm_full_simp_config ss

(* Where the two sides are sets -- functions into bool -- the pointwise
   reading is membership and not application.  Every set and list fact
   HOL4 states is headed by [IN]: [MEM x l] is [x IN set l] itself, and
   [x IN s] is an application of [IN] rather than the application [s x]
   that FUN_EQ_THM produces.  Left applied, a set equation meets only
   what unfolds on its own -- an intersection is a comprehension
   underneath and reaches the membership reading anyway, while [set l]
   is opaque and stays as it is.  Isabelle needs no such step: its
   [set_eq_iff] is the membership reading outright. *)
val membership_extensionality =
      prove
    (``!(left : 'a -> bool) right.
         (left = right) <=>
         !element. element IN left <=> element IN right``,
     Tactical.EVERY
       [Rewrite.REWRITE_TAC [boolTheory.IN_DEF, boolTheory.FUN_EQ_THM],
        Tactic.BETA_TAC,
        Rewrite.REWRITE_TAC []])

(* A rewrite states a fact about a head on the membership when its own
   left-hand side is a membership at that head: [MEM x l] is
   [x IN set l], [IN_IMAGE] and [IN_INTER] are the same shape, and
   [NOT_IN_EMPTY] is that shape negated.  The heads so collected are what
   the invocation states on the membership and nothing else is. *)
(* Fragment declarations omit aliases and may include rules the compiler
   discarded. Read the same active inventory the simplifier was given. *)
fun effective_rewrites ss = map #2 (#1 (simpLib.rewrite_sources ss []))

fun membership_heads_of rewrites =
  let
    (* Opening a binder can rename its variables but cannot change
       whether the inspected head is a constant. *)
    fun body term =
      if boolSyntax.is_forall term then #2 (boolSyntax.strip_forall term)
      else term
    fun subject term =
      let
        val (_, statement) = boolSyntax.strip_imp_only (body term)
      in
        case Lib.total boolSyntax.dest_eq statement of
            SOME (left, _) => left
          | NONE =>
              Option.getOpt (Lib.total boolSyntax.dest_neg statement,
                             statement)
      end
    fun head_of term =
      let
        val (_, set) = pred_setSyntax.dest_in term
        val (head, _) = boolSyntax.strip_comb set
      in
        if Term.is_const head then SOME (Term.dest_thy_const head) else NONE
      end
      handle HOL_ERR _ => NONE
    fun record (term, heads) =
      case head_of term of
          SOME {Thy, Name, ...} => Binaryset.add (heads, (Thy, Name))
        | NONE => heads
    fun record_reading (term, heads) =
      record (subject term, heads) handle HOL_ERR _ => heads
    fun readings term =
      boolSyntax.strip_conj (body term) handle HOL_ERR _ => [term]
    fun scan (theorem, heads) =
      let val term = Thm.concl theorem
      in
        case Lib.total boolSyntax.dest_eq term of
            SOME (left, _) => record (left, heads)
          | NONE => List.foldl record_reading heads (readings term)
      end
  in
    List.foldl scan
      (Binaryset.empty (Lib.pair_compare (String.compare, String.compare)))
      rewrites
  end

fun extensional_inventory ss =
  let
    val rewrites = Susp.delay (fn () => effective_rewrites ss)
    val heads = Susp.delay (fn () => membership_heads_of (Susp.force rewrites))
  in
    {rewrites=rewrites,heads=heads}
  end

(* Which of the two readings an equation is given is decided by its
   sides.  A side headed by a constant HOL4 states facts about on the
   membership -- [set l], an image, an intersection -- is read there;
   where neither side is, there is no such fact to meet, and the applied
   reading is the one the goal's own context is in.  The source's
   [Collect_cong] is that case: it arrives with an applied premise about
   a predicate variable, and reading its conclusion as a membership puts
   the two out of each other's reach.  So is a constant-headed side that
   is a predicate short of an argument and no set -- [IS_NONE], a
   translated [source_superset] -- whose every fact is stated applied:
   read as a membership it meets none of them, and no rewrite brings the
   two readings back together. *)
fun membership_reading heads term =
  let
    fun head_constant side =
      Lib.total (Term.dest_thy_const o fst o boolSyntax.strip_comb) side
    fun stated_on_membership side =
      case head_constant side of
          SOME {Thy, Name, ...} =>
            Binaryset.member (Susp.force heads, (Thy, Name))
        | NONE => false
    fun both_sides (left, right) =
      snd (Type.dom_rng (Term.type_of left)) = Type.bool andalso
      (stated_on_membership left orelse stated_on_membership right)
  in
    Lib.can (Lib.assert both_sides o boolSyntax.dest_eq) term
  end

fun extensional_rule heads term =
  if membership_reading heads term then membership_extensionality
  else boolTheory.FUN_EQ_THM

(* Whether the engine's default takes an equation as a membership, for a
   method built from HOL4's simplifier directly -- the parity corpus
   builds its recipes that way -- to make the same decision about its own
   set-equality pass.  The closure collects the heads once, when an
   equation first needs them. *)
fun reads_as_membership ss =
  membership_reading (#heads (extensional_inventory ss))

(* An equation between two functions is decided pointwise.  The source
   states its laws at the function level -- [f ^^ 0 = id],
   [set (filter P xs) = {x : set xs. P x}] -- where HOL4 states the same
   facts applied to an argument, so a goal that has reached the function
   level cannot meet the rule that settles it: the rewrite and the goal
   are the same fact at different arities.  Isabelle needs no step for
   this, its statements being already where its goals are; where a goal
   does reach it, [ext] is an introduction rule there.

   The equation is looked for under the goal's leading quantifiers and
   implications, which is where simplification leaves it, and taking it
   pointwise strips one arrow, so the step applies finitely often. *)
fun pointwise_conv heads term =
  if boolSyntax.is_forall term then
    Conv.QUANT_CONV (pointwise_conv heads) term
  else if boolSyntax.is_imp_only term then
    Conv.RAND_CONV (pointwise_conv heads) term
  else Conv.REWR_CONV (extensional_rule heads term) term

fun pointwise heads = Tactic.CONV_TAC (pointwise_conv heads)

fun pointwise_with charge heads goal =
  (charge (); pointwise heads goal)

(* The step is terminal: it runs on what simplification could not close,
   so no goal that already closes takes a different route.  Where
   simplification reports nothing to do the step still applies if the
   conclusion is a function equation -- that is the case it exists for
   -- and where neither applies the composite fails as it did.

   It belongs to a method, not to a step of one.  [extensional_normalize]
   below already puts a goal that arrives as a function equation into
   pointwise form before the search tactics start; what is left to this
   one is the equation that only appears once simplification has run,
   and asking for it again at every node of the classical cascade would
   pay for a whole simplification at each.  The safe cascade does not
   take it at all: Isabelle's [ext] is an introduction rule and not a
   safe one, and a safe step that rewrote every function equation would
   change what SAFE_TAC leaves. *)
fun with_extensionality_with charge heads simplify =
  let
    val pointwise_then =
      Tactical.THEN
        (pointwise_with charge heads,
         Tactical.TRY simplify)
  in
    Tactical.THEN
      (Tactical.ORELSE (simplify, pointwise_then),
       Tactical.REPEAT pointwise_then)
  end

fun with_extensionality ss simplify =
  with_extensionality_with (fn () => ())
    (#heads (extensional_inventory ss)) simplify

(* Isabelle reads an ordered rewrite by its schematic variables.  Stated
   with them a rule is permutative, and the simplifier applies it only in
   the direction its term order takes downwards; the same rule
   instantiated at the goal's own fixed terms has no schematic variable
   left, is not permutative, and rewrites left to right.  That is how
   [force] closes a goal whose supplied fact commutes an operation: its
   search instantiates the fact at the goal's terms, and the simplifier
   it runs before each unsafe step reads the instance as an ordinary
   rewrite.

   HOL4 has no Free/Var distinction in a term, but it has one in a
   theorem: a variable free in a theorem's hypotheses is a local constant
   to matching, which is what [HO_PART_MATCH] computes its [lconsts]
   from.  So an instance is made rigid the way Isabelle's search makes
   one: the rule's conditions are discharged from the goal's own
   assumptions, and the terms those assumptions speak of can no longer be
   matched away.  A rule with nothing to discharge yields nothing here,
   which is right -- Isabelle refuses an uninstantiated permutative rule
   just as HOL4 does, and the parity gap is only about the instance a
   condition pins down.

   What the ordering guard sees is still a permutation, so the instance
   goes in *bounded*, which is that guard's own escape: bounded once per
   occurrence of the redex, since the rewrite removes the left-hand side
   it fires on and nothing else can reach it.  Every hypothesis of an
   instance is one of the goal's assumptions, so a proof that uses it
   still answers the goal it was read from. *)
local
  fun permutative_equation theorem =
    let
      val specialised = Drule.SPEC_ALL theorem
      val (_, equation) = boolSyntax.strip_imp (Thm.concl specialised)
      val (left, right) = boolSyntax.dest_eq equation
      val (head, _) = boolSyntax.strip_comb left
    in
      if Cond_rewr.is_var_perm (left, right) then SOME (specialised, head)
      else NONE
    end
    handle HOL_ERR _ => NONE

  fun redexes head terms =
    let
      val matches_head =
        if is_const head then
          fn candidate => is_const candidate andalso same_const head candidate
        else aconv head

      (* Reuse the operator's head for every application on its spine.
         Visiting the argument first and prepending each match gives the
         reverse of find_terms' result for one term. *)
      fun visit term found =
        case dest_term term of
            COMB (operator, operand) =>
              let
                val (_, found) = visit operand found
                val (candidate, found) = visit operator found
              in
                (candidate, if matches_head candidate then term :: found
                            else found)
              end
          | LAMB (_, body) => (term, #2 (visit body found))
          | _ => (term, found)

      fun count (term, (counts, entries)) =
        case Redblackmap.peek (counts, term) of
            SOME n => (n := !n + 1; (counts, entries))
          | NONE =>
              let val n = ref 1
              in (Redblackmap.insert (counts, term, n), (term, n) :: entries)
              end
      val (_, entries) =
        (* Count in the same order as a right fold over find_terms'
           concatenated results, retaining the same representatives. *)
        List.foldr (fn (term, state) =>
          List.foldl count state (#2 (visit term [])))
          (Redblackmap.mkDict Term.compare, []) terms
    in
      map (fn (term, n) => (term, !n)) entries
    end

  fun discharge find_condition matched =
    let
      val (conditions, _) = boolSyntax.strip_imp (Thm.concl matched)
      fun step (condition, theorem) =
        case find_condition condition of
            SOME fact => Thm.MP theorem fact
          | NONE => raise ERR "permutation_instances" "condition not assumed"
    in
      List.foldl step matched conditions
    end

  fun instance find_condition specialised match_redex (redex, occurrences) =
    let
      val matched = match_redex redex
      val rewrite = discharge find_condition matched
      val (left, right) = boolSyntax.dest_eq (Thm.concl rewrite)
    in
      if HOLset.equal (Thm.hypset matched, Thm.hypset specialised) andalso
         not (aconv left right) andalso
         Cond_rewr.ac_term_ord (left, right) <> GREATER andalso
         HOLset.isSubset (FVL [left] empty_tmset, Thm.hyp_frees rewrite)
      then SOME (BoundedRewrites.Ntimes rewrite occurrences)
      else NONE
    end
    handle HOL_ERR _ => NONE
in
  fun permutation_instances theorems (assumptions, conclusion) =
    let
      (* Goals with few distinct conditions need only the lookup results.
         After repeated misses, index the available proofs once. *)
      val recent_conditions = ref (Redblackmap.mkDict Term.compare)
      val condition_index = ref NONE
      fun find_condition condition =
        case !condition_index of
            SOME index => Redblackmap.peek (index, condition)
          | NONE =>
              case Redblackmap.peek (!recent_conditions, condition) of
                  SOME result => result
                | NONE =>
                    if Redblackmap.numItems (!recent_conditions) < 16 then
                      let
                        val result =
                          List.find
                            (fn fact => aconv (Thm.concl fact) condition)
                            theorems
                      in
                        recent_conditions :=
                          Redblackmap.insert
                            (!recent_conditions, condition, result);
                        result
                      end
                    else
                      let
                        (* The first proof wins when conclusions coincide. *)
                        val index =
                          List.foldr
                            (fn (fact, table) =>
                              Redblackmap.insert (table, Thm.concl fact, fact))
                            (Redblackmap.mkDict Term.compare) theorems
                      in
                        condition_index := SOME index;
                        Redblackmap.peek (index, condition)
                      end
      val redex_cache = ref (Redblackmap.mkDict Term.compare)
      fun goal_redexes head =
        case Redblackmap.peek (!redex_cache, head) of
            SOME found => found
          | NONE =>
              let
                val found = redexes head (conclusion :: assumptions)
              in
                redex_cache := Redblackmap.insert (!redex_cache, head, found);
                found
              end
      fun instances theorem =
        case permutative_equation theorem of
            NONE => []
          | SOME (specialised, head) =>
              (case goal_redexes head of
                   [] => []
                 | redexes =>
                     (let
                        val match_redex = Drule.PART_MATCH
                          (boolSyntax.lhs o snd o boolSyntax.strip_imp)
                          specialised
                      in
                        List.mapPartial
                          (instance find_condition specialised match_redex)
                          redexes
                      end
                      handle HOL_ERR _ => []))
    in
      List.concat (map instances theorems)
    end
end

(* The instances are read off the goal the step is handed, before
   ambient simplification has simplified it: an assumption that states a
   permutation is its own decreasing rewrite, so the pass that reads the
   goal's own equations turns it into T and drops it. *)
fun with_permutation_instances_controlled controls step simp_args =
  (if null controls then Tactical.ASSUM_LIST
   else markerLib.process_taclist_then {arg=controls})
    (fn theorems =>
       fn goal => fn ctxt =>
         let
           val instances = permutation_instances theorems goal
           val _ =
             if null instances then ()
             else
               traceUtil.trace (traceUtil.level_of tracer ctxt) 2
                 (fn () =>
                    "permutation instances: " ^
                    String.concatWith ", "
                      (map (Parse.term_to_string o Thm.concl) instances))
         in
           step (simp_args @ instances) goal ctxt
         end)

fun asm_full_simp_with policy ss simp_args =
  with_permutation_instances_controlled []
    (fn args => ambient_simp policy false ss args)
    simp_args

fun safe_asm_full_simp_with policy ss simp_args =
  ambient_simp policy true ss simp_args

fun bound_global_simp config safe viewed
      (state as BoundSimplification {rules=SuppliedRuleBinding data,
                                    policy,...}) extras =
  let
    val (required,controls) = List.partition is_requirement (#controls data)
    val step = simpLib.GEN_GLOBAL_SIMP_TAC_CHILD_FIRST_BOUND
      policy {safe=safe} config (bound_simplification_simpset viewed state)
      (#bundle data) (controls @ extras)
    (* Their payloads already belong to the bundle. Only the requirement
       checks recur here; recompiling the payload would grant fresh quotas. *)
  in markerLib.mk_require_tac (fn _ => step) required end

fun asm_full_simp_bound viewed
      (state as BoundSimplification {rules=SuppliedRuleBinding data,...})
      extras =
  with_permutation_instances_controlled
    (List.filter is_assumption_control (#controls data @ extras))
    (bound_global_simp asm_full_simp_config false viewed state) extras

fun safe_asm_full_simp_bound viewed state =
  bound_global_simp asm_full_simp_config true viewed state

fun standalone_simp safe ss arguments goal =
  let val budget = normalization_budget ()
  in
    markerLib.ABBRS_THEN (markerLib.LLABEL_RES_THEN
      (fn resolved => fn current => fn ctxt =>
        let val state = prepare_bound_simplification
              (traceUtil.level_of tracer ctxt)
              (budgeted_decisions ctxt budget) (charge_normalization budget)
              ss resolved
        in
          deferred_view_tactic
            (fn viewed =>
              (if safe then safe_asm_full_simp_bound else asm_full_simp_bound)
                viewed state []) current ctxt
        end)) arguments goal
  end

val asm_full_simp = standalone_simp false
val safe_asm_full_simp = standalone_simp true

(* Inside the classical cascade the split between assumptions and
   conclusion is the cascade's own: its negation introduction strips a
   goal [~p] to [p |- F], and an implication rebuild re-forms [p ==> F]
   as [~p].  Safe saturation repeats while any step applies, so a
   wrapper that inverts one of its steps gives the two a cycle it never
   leaves; simplification participating in the cascade therefore
   normalises in place.  Discharging the conclusion's antecedents is
   left out for the same reason and costs nothing: the cascade's own
   implication introduction moves them into the assumptions, where the
   fixpoint reads them. *)
val cascade_simp_config : simpLib.xsimptac_config =
  {base = asm_full_simp_base,
   concl_in_fixpoint = true,
   imp_rebuild = false,
   imp_premises = false}

fun cascade_safe_simp_bound viewed state =
  bound_global_simp cascade_simp_config true viewed state

fun cascade_safe_simp policy ss =
  simpLib.GEN_GLOBAL_SIMP_TAC_CHILD_FIRST
    policy {safe = true} cascade_simp_config ss

fun add_simp_wrapper_tactic simplify =
  let
    fun wrapper step =
      NTactical.NAPPEND
        (NTactical.NCHANGED
           (NTactical.LIFT simplify),
         step)
  in
    clasetLib.add_unsafe_wrapper ("asm_full_simp_tac", wrapper)
  end

fun add_safe_simp_wrapper_tactic simplify =
  let
    fun wrapper step =
      NTactical.NORELSE
        (step,
         NTactical.NCHANGED
           (NTactical.LIFT simplify))
  in
    clasetLib.add_safe_wrapper
      ("safe_asm_full_simp_tac", wrapper)
  end

fun add_simp_wrapper_with policy ss simp_args =
  add_simp_wrapper_tactic (asm_full_simp_with policy ss simp_args)

fun add_safe_simp_wrapper_with policy ss simp_args =
  add_safe_simp_wrapper_tactic (cascade_safe_simp policy ss simp_args)

fun add_simp_wrapper_bound viewed state extras =
  add_simp_wrapper_tactic (asm_full_simp_bound viewed state extras)

fun add_safe_simp_wrapper_bound viewed state extras =
  add_safe_simp_wrapper_tactic (cascade_safe_simp_bound viewed state extras)

(* Standalone wrapper constructors retain their existing interface. Each
   embedded simplification owns a budget when a caller invokes it. *)
fun add_simp_wrapper ss simp_args =
  let
    fun wrapper step =
      NTactical.NAPPEND
        (NTactical.NCHANGED
           (NTactical.LIFT (asm_full_simp ss simp_args)), step)
  in
    clasetLib.add_unsafe_wrapper ("asm_full_simp_tac", wrapper)
  end

fun add_safe_simp_wrapper ss simp_args =
  let
    fun wrapper step =
      NTactical.NORELSE
        (step,
         NTactical.NCHANGED
           (NTactical.LIFT
              (fn goal =>
                 let val budget = normalization_budget ()
                 in cascade_safe_simp
                      (abstraction_policy
                         (charge_normalization budget) ss simp_args)
                      ss simp_args goal
                 end)))
  in
    clasetLib.add_safe_wrapper
      ("safe_asm_full_simp_tac", wrapper)
  end

fun iff_declaration name theorem =
  let
    val th = Drule.SPEC_ALL theorem
  in
    {rules = clasetLib.iff_rules name theorem, rewrite = th}
  end

(* The derived rules are internal to the [iff] declaration, so a clash among
   them is not a declaration the user can correct.  add_derived_rule keeps
   the diagnostics quiet, and gives each declaration its own copy of a rule
   two declarations happen to derive alike, so retracting one declaration
   cannot silently disarm another. *)
fun add_iff_rules rules cs =
  List.foldl
    (fn ((rule_spec, named_rule), current) =>
      clasetLib.add_derived_rule rule_spec named_rule current)
    cs rules

fun persistent_iff_name name = KernelSig.name_toString name

val normalise_iff_name = clasetLib.normalise_rule_name

(* Persistent iff views live below the source theorem's public name.  Simp's
   prefix deletion means that Excl/delsimps on [Thy.Name] still affect the iff
   rewrite, while the dotted private key lets remove_iff retract only its own
   contribution.  The private claset stem likewise cannot collide with the
   ordinary rule generated by a theorem called [Name_intro]. *)
fun iff_view_name name = name ^ ".__clasimp_iff"

fun iff_rule_name kname =
  iff_view_name (persistent_iff_name kname)

fun iff_simp_kname ({Thy, Name} : KernelSig.kernelname) =
  {Thy = Thy, Name = iff_view_name Name}

(* Simp deletion keys use the public "Thy.Name" spelling.  Claset and iff-db
   keys deliberately retain the kernel's "Thy$Name" spelling. *)
fun simp_delete_key ({Thy, Name} : KernelSig.kernelname) =
  Thy ^ "." ^ Name

(* The private name contains a dot, so this is a three-field simp key.  Such
   keys retain their explicit theory qualifier even for the current scratch
   theory, which is intentionally absent from [ancestry "-"]. *)
fun iff_simp_delete_key kname =
  simp_delete_key (iff_simp_kname kname)

(* The one spelling of an iff rule name, shared by the declaration path and
   by the theory finaliser: the kernel "Thy$Name" form, the public "Thy.Name"
   form, or a bare name resolved against [default_thy].  remove_iff records
   only the kernel form, so the [default_thy] fallback serves the finaliser's
   reading of a name it did not itself record. *)
fun iff_kname {default_thy} name =
  case String.fields (equal #"$") name of
      [thy, theorem] => {Thy = thy, Name = theorem}
    | _ =>
        (case String.fields (equal #".") name of
             [thy, theorem] => {Thy = thy, Name = theorem}
           | [theorem] => {Thy = default_thy, Name = theorem}
           | _ =>
               raise ERR "iff_kname" ("malformed iff name: " ^ name))

fun persistent_iff_kname name =
  iff_kname {default_thy = current_theory ()} name

fun remove_iff_rules name =
  clasetLib.remove_rule (name ^ "_intro") o
  clasetLib.remove_rule (name ^ "_dest") o
  clasetLib.remove_rule (name ^ "_elim")

(* The simp stream is loaded before this later-registered iff stream, so a
   delsimps in the declaring theory would otherwise find the iff view
   resurrecting the named rewrite behind it.  The predicate makes such a
   removal persist, and both the declaration path and the finaliser apply
   it, so what a session ends with is what a descendant theory reloads.

   Only a theory-qualified removal counts.  A bare name is theory-agnostic
   in simp and matches by prefix, so honouring one here would let a
   delsimps aimed at an ancestor's rewrite silently suppress an unrelated
   local [iff] declaration that happens to share the theorem's name -- and
   the two delta streams carry no common ordering with which to tell the
   two apart.  remove_iff is the supported way to drop one's own
   declaration; a bare delsimps of it reaches the current session only. *)
fun theory_delsimped thyname =
  let
    val names =
      List.foldl
        (fn (ThmSetData.REMOVE name, names) => Symtab.update (name, ()) names
          | (_, names) => names)
        Symtab.empty
        (ThmSetData.theory_data {settype = "simp", thy = thyname})
  in
    fn (kname : KernelSig.kernelname) =>
      Symtab.defined names (simp_delete_key kname) orelse
      Symtab.defined names (iff_simp_delete_key kname)
  end

(* Installing and retracting a single declaration and installing a theory's
   whole batch are the same operation; the batched form is the only
   implementation.  [declarations] is in claset declaration order. *)
fun retract_persistent_iffs [] = ()
  | retract_persistent_iffs knames =
      let
        fun remove_rules cs =
          List.foldl
            (fn (kname, current) =>
              remove_iff_rules (iff_rule_name kname) current)
            cs knames
      in
        BasicProvers.temp_delsimps (map iff_simp_delete_key knames);
        clasetLib.augment_claset remove_rules
      end

(* The iff batch is a fragment of its own rather than one more contribution
   to the fragment BasicProvers names after the theory.  Sharing that name
   would leave Excl/ExclSF, diminish_srw_ss and exclude_ssfrags unable to
   address the [simp] and [iff] streams separately, and would let an
   exclusion already in force drop the whole batch unannounced. *)
fun iff_fragment_name thyname = thyname ^ "-iff"

fun install_persistent_iffs thyname declarations =
  let
    val delsimped = theory_delsimped thyname
    (* Reversed so that the most recent declaration takes precedence in the
       fragment, as successive single-declaration fragments do. *)
    val rewrites =
      List.rev
        (List.filter (fn (kname, _) => not (delsimped kname)) declarations)
    fun add_rules ((kname, theorem), cs) =
      add_iff_rules
        (#rules (iff_declaration (iff_rule_name kname) theorem)) cs
    val _ =
      if null rewrites then ()
      else
        BasicProvers.augment_srw_ss
          [simpLib.named_rewrites_with_names (iff_fragment_name thyname)
             (map
                (fn (kname, theorem) =>
                  (iff_simp_kname kname, Drule.SPEC_ALL theorem))
                rewrites)]
  in
    if null declarations then ()
    else
      clasetLib.augment_claset
        (fn cs => List.foldl add_rules cs declarations)
  end

fun retract_iff_declaration kname = retract_persistent_iffs [kname]

fun install_persistent_iff kname theorem =
  install_persistent_iffs (#Thy kname) [(kname, theorem)]

(* The value of every persistent declaration stream here ([iff],
   [iff_bottom_up], [simp_bottom_up]): the source theorems whose views are
   currently installed, keyed by their kernel names.  Only the source
   theorem is persistent. *)
fun apply_named_delta delta table =
  case delta of
      ThmSetData.ADD (kname, theorem) =>
        Symtab.update (persistent_iff_name kname, theorem) table
    | ThmSetData.REMOVE name =>
        Symtab.delete_safe (normalise_iff_name name) table

(* Resolve against the declarations currently installed rather than against
   the current theory.  Removing an ancestor's declaration by its plain name
   is the ordinary case, and defaulting the theory part to the current
   theory would name nothing and retract nothing, silently.  Resolving here
   also settles the name before it reaches the delta stream: a descendant
   theory replays the recorded name, so an unknown or ambiguous one would
   otherwise be replayed as a no-op by every descendant in turn. *)
fun resolve_installed
      {data : thmTable.table thmTable.data, label, caller} name =
  let
    val installed = Symtab.keys (#get_global_value data ())
    fun denotes candidate =
      candidate = name orelse
      (case String.fields (equal #"$") candidate of
           [thy, theorem] => theorem = name orelse thy ^ "." ^ theorem = name
         | _ => false)
  in
    case List.filter denotes installed of
        [resolved] => resolved
      | [] =>
          raise ERR caller
            ("no [" ^ label ^ "] declaration named " ^ name ^
             " is installed")
      | candidates =>
          raise ERR caller
            ("ambiguous [" ^ label ^ "] name " ^ name ^ ": " ^
             String.concatWith ", " candidates)
  end

fun remove_declaration {data, label, caller, apply_to_global} name =
  let
    val delta =
      ThmSetData.REMOVE
        (resolve_installed {data = data, label = label, caller = caller} name)
  in
    #record_delta data delta;
    #update_global_value data (apply_to_global delta)
  end

(* Retraction only ever applies to a name the db records as installed.
   Skipping it otherwise avoids a whole-history rebuild of the global
   simpset for every declaration replayed at theory load. *)
fun apply_iff_to_global delta db =
  let
    fun retract_if_present kname =
      if Symtab.defined db (persistent_iff_name kname)
      then retract_iff_declaration kname
      else ()
    val _ =
      case delta of
          ThmSetData.ADD (name, theorem) =>
            (retract_if_present name;
             install_persistent_iff name theorem)
        | ThmSetData.REMOVE name =>
            retract_if_present
              (persistent_iff_kname (normalise_iff_name name))
  in
    apply_named_delta delta db
  end

(* Loading a theory resolves repeated declarations by their final event.
   Final-touch order preserves the recency tie-break of sequential replay. *)
fun iff_finaliser {thyname} deltas db =
  let
    fun delta_info (ThmSetData.ADD (kname, theorem)) =
          (kname, SOME (kname, theorem))
      | delta_info (ThmSetData.REMOVE name) =
          (iff_kname {default_thy = thyname} name, NONE)

    (* Scanning from the right keeps each name's final event, in the order
       those final events occur.  That is the recency order sequential
       replay would leave behind, at one pass over the deltas. *)
    fun remember (delta, (seen, touched)) =
      let
        val (kname, state) = delta_info delta
        val key = persistent_iff_name kname
      in
        if Symtab.defined seen key then (seen, touched)
        else (Symtab.update (key, ()) seen, (kname, state) :: touched)
      end

    val (_, touched) = List.foldr remember (Symtab.empty, []) deltas
    val stale =
      List.mapPartial
        (fn (kname, _) =>
          if Symtab.defined db (persistent_iff_name kname) then SOME kname
          else NONE)
        touched
    val live = List.mapPartial #2 touched
  in
    retract_persistent_iffs stale;
    install_persistent_iffs thyname live;
    List.foldl
      (fn (delta, current) => apply_named_delta delta current)
      db deltas
  end

(* ------------------------------------------------------------------
   An [iff] whose rewrite may only run once its subject is normalized
   ------------------------------------------------------------------ *)

(* [not_None_eq] reads an arbitrary option through a constructor: the
   subject of its left side [x <> NONE] is a pattern variable, so the rule
   is about every term of the type.  Isabelle declares it [iff] and its
   simplifier rewrites the innermost redex first, so the rule is only ever
   offered a subject already in normal form.  HOL4's rewrites the outermost
   redex first, so a rule of that shape fires above every rule about the
   subject's own head, and its right side re-embeds the subject where none
   of them match: [(m ++ n) x <> NONE] becomes the stuck
   [?y. (m ++ n) x = SOME y], where Isabelle rewrites the inner [= NONE] by
   [map_add_None] and reaches the disjunction that discharges it.

   A low-priority reducer is what the traversal reaches only once the
   rewrites and the descent have both left a node alone, which is the order
   Isabelle applies such a rule in: on the term above it now yields
   [n x = NONE ==> ?y. m x = SOME y], and on a subject that is a variable
   it yields what the rewrite did.  So the declaration differs from [iff]
   in where its simpset half goes and nowhere else -- the claset halves are
   the same derived rules, under the same names.

   The rewrite is not a named simpset entry, so [delsimps] does not address
   it; [remove_iff_bottom_up] retracts a declaration, as [remove_iff] does
   for [iff]. *)

exception bottom_up_context

(* A reducer rewriting with [rewrites] as the simplifier matches its own
   rewrites.  Isabelle's laws of this kind are higher-order patterns --
   [all_simps] reads a body as [P x] -- and a first-order matcher offers
   them only a body that is literally a variable applied to the bound one,
   so the rule would be silently inert on every other goal. *)
fun ho_rewrite_reducer name rewrites =
  let
    (* Prepare the matchers once, at the first reduction attempt. *)
    val conversion = Susp.delay (fn () =>
      Conv.FIRST_CONV (map (Conv.HO_REWR_CONV o Drule.SPEC_ALL) rewrites))
  in
    Traverse.REDUCER
      {name = SOME name,
       initial = bottom_up_context,
       addcontext = fn (context, _) => context,
       apply = fn _ => fn term => Susp.force conversion term}
  end

fun ho_rewrite_fragment name rewrites =
  simpLib.name_ss name
    (simpLib.dproc_ss ((ho_rewrite_reducer name rewrites)))

(* The same reducer for a rule installed for one invocation rather than
   declared. *)
val normalised_subject_fragment_name = "clasimp-normalised-subject"

fun normalised_subject_fragment rewrites =
  ho_rewrite_fragment normalised_subject_fragment_name rewrites

fun normalised_subject_fragment_ordinary rewrites =
  simpLib.name_ss normalised_subject_fragment_name
    (simpLib.dproc_ss
      (ho_rewrite_reducer normalised_subject_fragment_name rewrites))

(* The declarations, as the bottom-up tables below list them.  One
   fragment carries both: [simp_bottom_up] is [iff_bottom_up] without the
   claset halves -- Isabelle states a law whose subject must be normal as
   [simp] as well as as [iff], and a rule the source declares [simp] may
   not seed the claset. *)
val bottom_up_rewrites : thm list Context.Data.slot = Context.Data.new
  {name = "clasimp.iff_bottom_up", empty = [],
   pp = fn _ => "<iff bottom-up declarations>"}

val simp_bottom_up_rewrites : thm list Context.Data.slot = Context.Data.new
  {name = "clasimp.simp_bottom_up", empty = [],
   pp = fn _ => "<simp bottom-up declarations>"}

(* The declarations live in srw_ss.  The fragment closes over the rules
   declared when it is built, and a declaration or retraction that changes
   them replaces it there, so a context's srw_ss carries that context's
   declarations: a proof reads them from the context it runs in, the
   reducer reads nothing ambient, and every cache keyed on the simpset
   follows them.  The simpsets derived here take the fragment as a layer
   of their own ([layered_srw_derivation]); other simpsets built from
   srw_ss carry it as any other fragment.

   Replacing removes the fragment from the srw_ss history, which
   diminish_srw_ss does, and adds its successor.  Deleting it with -*
   instead would leave a deletion event in the history, and every
   simpset rebuilt from that history (filter_rewrites, once per rule a
   proof transports) would replay it over the whole net.  Removal forces
   an uninitialised srw_ss state, so it is done only when the state holds
   the fragment, applied or queued.  Neither update records a simp delta:
   the bottom-up tables record the declarations, and their replay
   installs the fragment again. *)
fun bottom_up_fragment rewrites =
  simpLib.name_ss bottom_up_fragment_name
    (simpLib.dproc_ss
       (ho_rewrite_reducer bottom_up_fragment_name rewrites))

fun bottom_up_fragment_present () =
  let
    val (sset, _, updates) = BasicProvers.simpset_state ()
    fun queued (BasicProvers.ADD_SSFRAG fragment) =
          simpLib.frag_name fragment = SOME bottom_up_fragment_name
      | queued (BasicProvers.REMOVE_RWT _) = false
  in
    Lib.mem bottom_up_fragment_name (simpLib.ssfrag_names_of sset) orelse
    List.exists queued updates
  end

fun replace_bottom_up_fragment () =
  let
    val ctxt = Context.snapshot ()
    val rewrites =
      Context.Data.get bottom_up_rewrites ctxt @
      Context.Data.get simp_bottom_up_rewrites ctxt
  in
    if bottom_up_fragment_present () then
      BasicProvers.diminish_srw_ss [bottom_up_fragment_name]
    else ();
    if null rewrites then ()
    else BasicProvers.augment_srw_ss [bottom_up_fragment rewrites]
  end

(* Whether a delta changes the declarations, found without comparing them:
   retracting what is not declared, and declaring again the same theorem,
   leave the table as it was. *)
fun delta_changes delta table =
  case delta of
      ThmSetData.ADD (kname, theorem) =>
        (case Symtab.lookup table (persistent_iff_name kname) of
             SOME declared => not (Portable.pointer_eq (declared, theorem))
           | NONE => true)
    | ThmSetData.REMOVE name => Symtab.defined table (normalise_iff_name name)

(* The fragment is replaced only when the declarations changed. *)
fun install_bottom_up_declarations slot changed table =
  if changed then
    (Context.update (Context.Data.put slot (map #2 (Symtab.dest table)));
     replace_bottom_up_fragment ())
  else ()

(* A declaration applies at once.  A theory's deltas replayed at load go
   through the finaliser instead, which installs the fragment once for the
   theory rather than once for each of its deltas.  [step] applies one
   delta to the table and reports whether it changed the declarations. *)
fun bottom_up_ops slot step =
  {apply_to_global = fn delta => fn table =>
     let val (changed, table) = step delta table
     in install_bottom_up_declarations slot changed table; table end,
   thy_finaliser = fn {thyname = _} => fn deltas => fn table =>
     let
       val (changed, table) =
         List.foldl
           (fn (delta, (changed, table)) =>
              let val (changed', table) = step delta table
              in (changed orelse changed', table) end)
           (false, table) deltas
     in install_bottom_up_declarations slot changed table; table end}

fun bottom_up_rules kname theorem =
  #rules (iff_declaration (iff_rule_name kname) theorem)

(* Retraction is addressed to what the table records as installed, and by
   the key it is recorded under: naming a declaration takes a theory to
   resolve a bare name against, and the replay of an ancestor's deltas at
   load time has no current theory.  Retracting before a repeated
   declaration keeps one name to one copy of the derived rules. *)
fun bottom_up_step delta table =
  let
    fun retract_if_present key =
      if Symtab.defined table key
      then clasetLib.augment_claset (remove_iff_rules (iff_view_name key))
      else ()
    val _ =
      case delta of
          ThmSetData.ADD (kname, theorem) =>
            (retract_if_present (persistent_iff_name kname);
             clasetLib.augment_claset
               (add_iff_rules (bottom_up_rules kname theorem)))
        | ThmSetData.REMOVE name =>
            retract_if_present (normalise_iff_name name)
  in
    (delta_changes delta table, apply_named_delta delta table)
  end

val {apply_to_global = apply_bottom_up_to_global,
     thy_finaliser = finalise_bottom_up} =
  bottom_up_ops bottom_up_rewrites bottom_up_step

val bottom_up_data =
  thmTable.register_finalised
    {settype = "iff_bottom_up", initial_value = Symtab.empty,
     apply_delta = apply_named_delta,
     apply_to_global = apply_bottom_up_to_global,
     thy_finaliser = finalise_bottom_up}

val remove_iff_bottom_up =
  remove_declaration
    {data = bottom_up_data, label = "iff_bottom_up",
     caller = "remove_iff_bottom_up",
     apply_to_global = apply_bottom_up_to_global}

(* ------------------------------------------------------------------
   A [simp] whose rewrite may only run once its subject is normalized
   ------------------------------------------------------------------ *)

(* [iff_bottom_up] without the claset halves.  Isabelle's miniscoping laws
   -- [ex_simps] and [all_simps], src/HOL/HOL.thy:1396-1414,1442-1443 --
   are the family this is for: they are declared [simp] there and nothing
   else, and their subject is a quantifier whose body the traversal must
   have normalised first.  Fired above the body, as HOL4's outermost-first
   order would fire an ordinary rewrite, the law pushes the quantifier past
   a side whose own antecedent had not yet been used, and the reading that
   antecedent would have settled is lost. *)

val {apply_to_global = apply_simp_bottom_up_to_global,
     thy_finaliser = finalise_simp_bottom_up} =
  bottom_up_ops simp_bottom_up_rewrites
    (fn delta => fn table =>
       (delta_changes delta table, apply_named_delta delta table))

val simp_bottom_up_data =
  thmTable.register_finalised
    {settype = "simp_bottom_up", initial_value = Symtab.empty,
     apply_delta = apply_named_delta,
     apply_to_global = apply_simp_bottom_up_to_global,
     thy_finaliser = finalise_simp_bottom_up}

val remove_simp_bottom_up =
  remove_declaration
    {data = simp_bottom_up_data, label = "simp_bottom_up",
     caller = "remove_simp_bottom_up",
     apply_to_global = apply_simp_bottom_up_to_global}

(* The source theorem is the only persistent declaration.  Its claset and
   simpset views are recomputed by this hook whenever the iff stream is
   replayed.  The views deliberately use the public augmentation APIs, so
   neither the claset cdelta schema nor the simp declaration stream changes.

   Claset candidate order uses declaration recency as a tie-break.  Since
   [intro] and [iff] inhabit different delta streams, their relative recency
   in one theory may be permuted on reload.  This affects ties only; a shared
   declaration counter can be introduced if later benchmarks need one. *)
val iff_data =
  thmTable.register_finalised
    {settype = "iff", initial_value = Symtab.empty,
     apply_delta = apply_named_delta,
     apply_to_global = apply_iff_to_global,
     thy_finaliser = iff_finaliser}

val remove_iff =
  remove_declaration
    {data = iff_data, label = "iff", caller = "remove_iff",
     apply_to_global = apply_iff_to_global}

(* A conditional rule whose conclusion is an equation between variables --
   [inj_onD] is the standard one -- is a rewrite in Isabelle:
   [Simplifier.mksimps] keeps the schematic left-hand side, and the
   subgoaler instantiates the schematics its conditions carry by unifying
   them against the assumptions.  HOL4 matches the left-hand side first and
   only then proves the conditions, so a left-hand side that is a bare
   variable is refused and the rule is turned into an [<=> T] rewrite of
   its own conclusion, with the condition variables the conclusion does not
   carry existentially closed
   (IMP_EQ_CANON and QUANTIFY_CONDITIONS, src/simp/src/Cond_rewr.sml).
   [inj_onD] prepares to
   [(?f s t. INJ f s t /\ x IN s /\ y IN s /\ f x = f y) ==> (x = y <=> T)]:
   a rewrite whose pattern is an equation between two variables, so it
   matches every equation in the goal, and whose condition the match
   determines nothing of.  It cannot fire, and it is not merely inert: the
   simplifier reaches it at every equation and calls its solver on the
   existential, so a four-assumption goal does not come back in a minute
   where the same call without the argument returns at once.

   The rule reaches those goals as an unsafe destruction rule instead: its
   premises say where the condition variables come from, so the reasoner
   fires it on an assumption matching the first and resolves the rest --
   what Isabelle's subgoaler does when it instantiates the schematics a
   condition carries, and the declaration Isabelle's own libraries give
   this rule family ([dest: inj_onD]).  Conclusion-directed instead, as an
   introduction rule, it is offered on every equality goal with the
   witnesses its premises name left to the search to guess: measured on the
   corpus goal that names [inj_onD], the destruction rule closes it and the
   introduction rule does not close it in twelve times the time.

   The test is on that exact shape, and reads the argument's form rather
   than its name.  A conditional equation between variables whose conditions
   the two sides do determine -- [LIST_EQ] is one -- carries no existential
   and keeps its rewrite, and so does an argument that prepares to several
   rewrites of which any is usable. *)
val undetermined_dest_spec : clasetLib.rulespec =
  {kind = clasetRules.Dest, safe = false, prio = NONE}

fun rewrites_every_equation rule =
  let
    val conclusion = concl rule
  in
    boolSyntax.is_imp_only conclusion andalso
    boolSyntax.is_exists (fst (boolSyntax.dest_imp conclusion)) andalso
    (case Lib.total boolSyntax.dest_eq
            (snd (boolSyntax.dest_imp conclusion)) of
         SOME (pattern, value) =>
           aconv value boolSyntax.T andalso
           (case Lib.total boolSyntax.dest_eq pattern of
                SOME (left, right) => is_var left andalso is_var right
              | NONE => false)
       | NONE => false)
  end

fun simp_argument_can_fire theorem =
  case Lib.total Cond_rewr.mk_cond_rewrs
         (BoundedRewrites.dest_tagged_rewrite theorem) of
      NONE => true
    | SOME prepared =>
        List.exists (not o rewrites_every_equation o #1) prepared

(* The declaration takes the rule the bound was attached to: a bound counts
   rewrite applications, and there are none to count here. *)
fun declare_undetermined theorem cs from =
  let
    val rule = #1 (BoundedRewrites.dest_tagged_rewrite theorem)
    val (name, index) = clasetLib.fresh_rule_name_indexed
      {prefix = "__clasimp_undetermined_arg_", from = from} cs
  in
    (clasetLib.add_derived_rule undetermined_dest_spec (name, rule) cs, index)
  end

(* A fact the classical reasoner declines too stays a rewrite: it is then
   no worse off than it was, and the argument is not silently dropped. *)
fun route_simp_argument level (theorem, (cs, rewrites, from)) =
  if simp_argument_can_fire theorem then (cs, theorem :: rewrites, from)
  else
    case Lib.total (declare_undetermined theorem cs) from of
        SOME (extended, index) =>
          (traceUtil.trace level 1
             (fn () =>
               "no rewrite of " ^ Parse.thm_to_string theorem ^
               " can fire; declaring it as an unsafe destruction rule");
           (extended, rewrites, index))
      | NONE => (cs, theorem :: rewrites, from)

fun invocation_declarations level iff_prefix simp_rules iff_rules claset =
  let
    val (routed_claset, rewritable, _) =
      List.foldr (route_simp_argument level) (claset, [], 0) simp_rules
    val declarations =
      map
        (fn (index, rule) =>
          iff_declaration (iff_prefix ^ Int.toString index) rule)
        (Lib.enumerate 0 iff_rules)
    val invocation_cs =
      List.foldl
        (fn ({rules,...}, cs) => add_iff_rules rules cs)
        routed_claset declarations
  in (invocation_cs,rewritable,List.rev (map #rewrite declarations)) end

fun extend_invocation
      {iff_prefix,simp_rules,iff_rules,claset,simpset,context} =
  let
    val (invocation_cs,rewritable,iff_rewrites) =
      invocation_declarations (traceUtil.level_of tracer context) iff_prefix
        simp_rules iff_rules claset
    val simp_ss =
      if null rewritable then simpset
      else simpLib.++ (simpset, simpLib.rewrites rewritable)
    (* A single fragment rebuilds the rewrite net once.  Its head has the
       highest precedence, so reverse the declarations to match successive
       fragment insertion. *)
    val invocation_ss =
      if null iff_rewrites then simp_ss
      else
        simpLib.++
          (simp_ss,
           simpLib.rewrites iff_rewrites)
  in
    (invocation_cs, invocation_ss)
  end

datatype invocation_rewrites = InvocationRewrites of
  {ambient : simpLib.simpset,supplied : thm list}

fun extend_bound_invocation
      {iff_prefix,simp_rules,iff_rules,claset,
       simpset=InvocationRewrites {ambient,supplied},context} =
  let
    val (cs,rewritable,iff_rewrites) =
      invocation_declarations (traceUtil.level_of tracer context) iff_prefix
        simp_rules iff_rules claset
  in
    (cs,InvocationRewrites
      {ambient=ambient,supplied=iff_rewrites @ rewritable @ supplied})
  end

val curry_premises =
  Conv.REDEPTH_CONV (Conv.REWR_CONV (Conv.GSYM boolTheory.AND_IMP_INTRO))

(* The simpset's normal form of a rule, with conjoined premises curried. *)
fun finish_rule_normal_form (policy : Traverse.child_first_policy) conversion =
  Conv.THENC
    (conversion,
     fn term =>
       (#charge policy ();
        Conv.QCONV curry_premises term))

fun rule_normal_form_conv policy ss = finish_rule_normal_form policy
  (simpLib.SIMP_CONV_CHILD_FIRST policy ss [])

fun bound_rule_normal_form_conv policy ss =
  let val prepared = simpLib.prepare_child_first policy ss
  in finish_rule_normal_form policy (#normalize prepared []) end

fun transport_name cs from =
  clasetLib.fresh_rule_name_indexed
    {prefix = "__clasimp_transport_", from = from} cs

(* Keep the original declaration and add a certified view for the
   simpset's representation. Exclude a rule's own rewrite statement or
   an equivalence of which the rule is one direction. *)
fun transport_claset_rules_with filter normal_form budget policy ss rules cs =
  let
    fun rule_body theorem =
      boolSyntax.strip_imp_only (concl (Drule.SPEC_ALL theorem))
    fun equation theorem = boolSyntax.dest_eq (#2 (rule_body theorem))
    fun index_rewrite (rewrite, (statements, directions)) =
      let
        val statements = HOLset.add (statements, concl rewrite)
        val directions =
          let val (left, right) = equation rewrite
          in HOLset.add (HOLset.add (directions, (left, right)), (right, left))
          end
          handle HOL_ERR _ => directions
      in
        (statements, directions)
      end
    (* Index the same raw fragment entries the history filter reads.
       Most candidates have no source to exclude. *)
    val inventory = Susp.delay (fn () =>
      List.foldl
        (fn (fragment, index) =>
          List.foldl index_rewrite index (simpLib.frag_rewrites fragment))
        (Term.empty_tmset,
         HOLset.empty (Lib.pair_compare (Term.compare, Term.compare)))
        (simpLib.ssfrags_of ss))
    fun may_exclude statement result premises =
      case rules of
          _ :: _ :: _ =>
            let val (statements, directions) = Susp.force inventory
            in
              HOLset.member (statements, statement) orelse
              List.exists (fn premise =>
                HOLset.member (directions, (result, premise))) premises
            end
        | _ => true
    val ambient = Susp.delay (fn () => normal_form policy ss)
    fun conversion theorem =
      let
        val statement = concl theorem
        val (premises, result) = rule_body theorem
        fun own_direction rewrite =
          let
            val (left, right) = equation rewrite
          in
            (aconv result left andalso boolSyntax.tmem right premises)
            orelse
            (aconv result right andalso boolSyntax.tmem left premises)
          end
          handle HOL_ERR _ => false
      in
        if may_exclude statement result premises then
          normal_form policy
            (filter
              (fn (_, rewrite) =>
                not (aconv (concl rewrite) statement) andalso
                (null premises orelse not (own_direction rewrite))) ss)
        else Susp.force ambient
      end
    fun add ((spec, (_, theorem)), state as (added, from)) =
      let
        val _ = searchBudget.charge budget searchBudget.Candidate
        val derived = Conv.CONV_RULE (conversion theorem) theorem
        fun role_preserved () =
          clasetRules.safe_class_of spec (clasetRules.ext_info spec theorem) =
          clasetRules.safe_class_of spec (clasetRules.ext_info spec derived)
        fun support_preserved () =
          List.all
            (fn assumption => boolSyntax.tmem assumption (hyp theorem))
            (hyp derived)
      in
        if aconv (concl derived) (concl theorem) orelse
           aconv (concl derived) boolSyntax.T orelse
           not (role_preserved ()) orelse
           not (support_preserved ()) then state
        else
          let
            val current = Option.getOpt (added, cs)
            val (name, index) = transport_name current from
          in
            searchBudget.charge budget searchBudget.Application;
            (* The fresh name makes admission independent of whether an
               earlier declaration has the same conclusion. *)
            (SOME (clasetLib.add_derived_rule spec (name, derived) current),
             index)
          end
      end
      handle HOL_ERR _ => state
           | Conv.UNCHANGED => state
  in
    #1 (List.foldl add (NONE, 0) rules)
  end

val transport_claset_rules = transport_claset_rules_with
  simpLib.filter_rewrites rule_normal_form_conv
val transport_bound_claset_rules = transport_claset_rules_with
  simpLib.filter_rewrites_preserving_controls bound_rule_normal_form_conv

fun safe_named_rule ((spec : clasetLib.rulespec), _) = #safe spec

(* Only declarations connected to the goal's vocabulary need a new
   normal-form view. Follow direct rewrite-head bridges as well: a rule
   about P must remain eligible when the simpset presents the goal as Q. *)
fun transport_candidates budget ss goals candidates =
  let
    (* A constant is keyed by name alone, as [same_const] compares. *)
    fun key head =
      let val {Thy, Name, ...} = dest_thy_const head in (Thy, Name) end
    val head_compare = Lib.pair_compare (String.compare, String.compare)
    val no_heads = HOLset.empty head_compare
    fun fold_heads add term state =
      if boolSyntax.is_forall term then
        fold_heads add (snd (boolSyntax.dest_forall term)) state
      else if boolSyntax.is_exists term then
        fold_heads add (snd (boolSyntax.dest_exists term)) state
      else if is_abs term then
        fold_heads add (snd (dest_abs term)) state
      else if boolSyntax.is_imp term then
        let val (left, right) = boolSyntax.dest_imp term
        in fold_heads add right (fold_heads add left state) end
      else if boolSyntax.is_conj term then
        let val (left, right) = boolSyntax.dest_conj term
        in fold_heads add right (fold_heads add left state) end
      else if boolSyntax.is_disj term then
        let val (left, right) = boolSyntax.dest_disj term
        in fold_heads add right (fold_heads add left state) end
      else if boolSyntax.is_neg term then
        fold_heads add (boolSyntax.dest_neg term) state
      else if boolSyntax.is_eq term then
        let val (left, right) = boolSyntax.dest_eq term
        in fold_heads add right (fold_heads add left state) end
      else
        let
          val (head, arguments) = strip_comb term
          val state =
            if is_const head andalso
               not (aconv head boolSyntax.T) andalso
               not (aconv head boolSyntax.F) then
              add (state, key head)
            else state
        in
          List.foldl (fn (argument, state) =>
            fold_heads add argument state) state arguments
        end
    fun root_head term =
      let val (head, _) = strip_comb term
      in if is_const head then SOME head else NONE end
    fun bridge theorem =
      let
        val _ = searchBudget.charge budget searchBudget.Candidate
        (* Opening the quantifiers is enough to inspect constant heads. *)
        val (_, body) =
          boolSyntax.strip_imp_only
            (snd (boolSyntax.strip_forall (concl theorem)))
        val (left, right) = dest_eq body
      in
        case (root_head left, root_head right) of
            (SOME first, SOME second) => SOME (key first, key second)
          | _ => NONE
      end
      handle HOL_ERR _ => NONE
    val rewrites =
      List.concat
        (map simpLib.frag_rewrites (simpLib.ssfrags_of ss))
    val bridges = List.mapPartial bridge rewrites
    fun collect term heads = fold_heads HOLset.add term heads
    fun collect_goal ((assumptions, target), heads) =
      List.foldl (fn (term, found) => collect term found)
        (collect target heads) assumptions
    val goal_heads = List.foldl collect_goal no_heads goals
    fun sweep heads =
      let
        fun add ((left, right), (found, changed)) =
          let
            fun join head =
              if HOLset.member (found, head) then (found, changed)
              else (HOLset.add (found, head), true)
          in
            if HOLset.member (found, left) then join right
            else if HOLset.member (found, right) then join left
            else (found, changed)
          end
      in
        List.foldl add (heads, false) bridges
      end
    fun indexed_growth heads =
      let
        fun link from target adjacency =
          let val neighbors = getOpt (Redblackmap.peek (adjacency, from), [])
          in Redblackmap.insert (adjacency, from, target :: neighbors) end
        fun connect ((left, right), adjacency) =
          if left = right orelse
             (HOLset.member (heads, left) andalso HOLset.member (heads, right))
          then adjacency
          else link left right (link right left adjacency)
        val adjacency =
          List.foldl connect (Redblackmap.mkDict head_compare) bridges
        fun discover (head, result as (seen, pending)) =
          if HOLset.member (seen, head) then result
          else (HOLset.add (seen, head), head :: pending)
        fun visit [] seen = seen
          | visit (head :: rest) seen =
              case Redblackmap.peek (adjacency, head) of
                  NONE => visit rest seen
                | SOME neighbors =>
                    let
                      val (seen', pending) =
                        List.foldl discover (seen, rest) neighbors
                    in visit pending seen' end
      in
        visit (HOLset.listItems heads) heads
      end
    (* Sweep small closures without building an index of unrelated heads. *)
    fun grow passes heads =
      case sweep heads of
          (heads, false) => heads
        | (heads, true) =>
            if passes = 1 then indexed_growth heads
            else grow (passes - 1) heads
    val relevant = grow 8 goal_heads
    (* One relevant head suffices, regardless of its position. *)
    exception RelevantHead
    fun check_head ((), head) =
      if HOLset.member (relevant, head) then raise RelevantHead else ()
    fun related (_, (_, theorem)) =
      (searchBudget.charge budget searchBudget.Candidate;
       fold_heads check_head (concl theorem) ();
       false)
      handle RelevantHead => true
  in
    List.filter related candidates
  end

fun with_claset_transport_from transport budget policy ss candidates cs build
      initial goal ctxt =
  let
    fun initial_result () =
      case initial of
          (SOME result, _) => result
        | (NONE, SOME exn) => raise exn
        | _ => raise ERR "with_claset_transport" "missing result"
    fun improve () =
      if null candidates then initial_result ()
      else let
        val sites =
          case initial of
              (SOME (goals, _), _) => goal :: goals
            | _ => [goal]
        val relevant =
          transport_candidates budget ss sites candidates
      in
        case transport budget policy ss relevant cs of
          NONE => initial_result ()
        | SOME extended =>
          let
            val result =
              SOME (build extended goal ctxt)
              handle HOL_ERR _ => NONE
          in
            case (initial, result) of
                ((SOME (goals, _), _), SOME (next_goals, validation)) =>
                  if length next_goals < length goals then
                    (next_goals, validation)
                  else initial_result ()
              | ((NONE, _), SOME next) => next
              | _ => initial_result ()
          end
      end
  in
    case initial of
        (SOME ([], validation), _) => ([], validation)
      | _ => improve ()
  end

fun with_claset_transport budget policy ss candidates cs build goal ctxt =
  let
    val initial = (SOME (build cs goal ctxt),NONE)
      handle exn as HOL_ERR _ => (NONE,SOME exn)
  in with_claset_transport_from transport_claset_rules budget policy ss
       candidates cs build initial goal ctxt end

fun process_clasimp_args body base_cs base_ss =
  clasetLib.with_invocation_fact_env
    {iff_prefix="__clasimp_iff_arg_",extra_markers=clasetLib.no_extra_markers,
     consumer=clasetLib.SearchFacts}
    (fn cs => fn simpset => fn controls => fn environment =>
      case simpset of
          SOME (InvocationRewrites {ambient,supplied}) =>
            markerLib.LLABEL_RES_THEN
              (fn arguments => fn goal => fn ctxt =>
                let
                  val (ambient,rules) =
                    prepare_invocation_rules ambient arguments
                  val ss = install_supplied_rules rules ambient
                  val binding =
                    {simpset=ss,ambient=ambient,rules=rules,
                     environment=environment,base_cs=base_cs,
                     controls=controls,active=ref NONE}
                in with_callback_binding binding
                     (fn () => body cs ss controls goal ctxt) end)
              (map #theorem
                (clasetFacts.schematic_views environment) @ supplied)
        | NONE => raise ERR "process_clasimp_args"
            "simpset was not installed")
    base_cs (SOME
      {base=InvocationRewrites {ambient=base_ss,supplied=[]},
       extend=extend_bound_invocation})

fun process_clasimp_args_with_policy budget body =
  process_clasimp_args
    (fn cs => fn ss => fn arguments =>
      body (abstraction_policy (charge_normalization budget) ss arguments)
        cs ss arguments)

fun process_clasimp_bound_args consumer budget runtime body base_cs base_ss =
  clasetLib.with_invocation_fact_env_budgeted budget
    {iff_prefix="__clasimp_iff_arg_",extra_markers=clasetLib.no_extra_markers,
     consumer=consumer}
    (fn cs => fn simpset => fn controls => fn environment =>
      case simpset of
          SOME (InvocationRewrites {ambient,supplied}) =>
            markerLib.LLABEL_RES_THEN
              (fn arguments => fn goal => fn ctxt =>
                let
                  val bound =
                    prepare_bound_simplification
                      (traceUtil.level_of tracer ctxt) runtime
                      (charge_normalization budget) ambient arguments
                in body bound cs environment goal ctxt end)
              (controls @ map #theorem
                (clasetFacts.schematic_views environment) @ supplied)
        | NONE => raise ERR "process_clasimp_bound_args"
            "simpset was not installed")
    base_cs (SOME
      {base=InvocationRewrites {ambient=base_ss,supplied=[]},
       extend=extend_bound_invocation})

fun add_bound_fact_aliases [] state = state
  | add_bound_fact_aliases aliases (BoundSimplification data) =
      let
        fun install ss = simpLib.++ (ss,simpLib.name_ss "CLASIMP_FACT_VIEWS"
          (simpLib.rewrite_views aliases))
      in BoundSimplification
           {rules= #rules data,policy= #policy data,
            initial=install (#initial data),
            viewed=Susp.delay (fn () => install (Susp.force (#viewed data)))}
      end

(* Fact aliases retain compiled origins; normalization cannot spend them. *)
fun transport_bound_facts viewed
      (state as BoundSimplification {rules=SuppliedRuleBinding data,
                                    policy,...}) environment =
  case clasetFacts.schematic_views environment of
      [] => (state,[])
    | views =>
  let
    fun is_fact (theorem,_) = List.exists
      (fn (view : clasetFacts.view) =>
        Portable.pointer_eq (theorem,#theorem view)) views
    val sources = List.concat (map #2 (List.filter is_fact
      (simpLib.rewrite_bundle_rules (#bundle data))))
    val basis = simpLib.suspend_rewrite_sources sources
      (bound_simplification_simpset viewed state)
    exception FactViewLimit
    val remaining = ref 20000
    fun charge () = if !remaining = 0 then raise FactViewLimit
      else (remaining := !remaining - 1; #charge policy ())
    val local_policy =
      {charge=charge,keep_abstraction= #keep_abstraction policy}
    val prepared = simpLib.prepare_child_first local_policy basis
    fun supported original derived = List.all
      (fn assumption => boolSyntax.tmem assumption (hyp original))
      (hyp derived)
    fun candidate theorem =
      let
        val specialised = Drule.SPEC_ALL theorem
        val (premises,equation) =
          boolSyntax.strip_imp_only (concl specialised)
        val (left,right) = boolSyntax.dest_eq equation
        val assumptions = map Thm.ASSUME premises
        val normal = #normalize prepared assumptions left
        val left' = boolSyntax.rhs (concl normal)
      in
        if aconv left left' orelse aconv left' right then NONE
        else
          let
            val right' = boolSyntax.rhs
              (concl (#normalize prepared assumptions right))
            val body = List.foldl
              (fn (premise,th) => Thm.MP th (Thm.ASSUME premise))
              specialised premises
            val derived = Thm.TRANS (Thm.SYM normal) body
            val discharged = List.foldr
              (fn (premise,th) => Thm.DISCH premise th) derived premises
          in
            if aconv left' right' orelse
               not (supported specialised discharged) then NONE
            else SOME (List.foldl
              (fn (assumption,th) => Drule.ADD_ASSUM assumption th)
              discharged (hyp specialised))
          end
      end
    fun alias source =
      let
        val theorem = #2 (simpLib.source_rewrite source)
        val _ = remaining := 20000
      in
        case candidate theorem of
            NONE => NONE
          | SOME derived =>
              let val (other,undo) = rename_view_variables theorem
              in case candidate other of
                  SOME renamed => if aconv (concl derived)
                      (undo (concl renamed))
                    then SOME (source,Drule.GEN_ALL derived) else NONE
                | NONE => NONE end
      end
      handle FactViewLimit => NONE | HOL_ERR _ => NONE
           | Conv.UNCHANGED => NONE
    fun transport (view : clasetFacts.view) =
      let
        val _ = remaining := 20000
        val conversion = finish_rule_normal_form local_policy
          (#normalize prepared [])
        val derived = clasetFacts.transport_view conversion view
        val theorem = #theorem derived
      in
        if aconv (concl theorem) (concl (#theorem view)) orelse
           aconv (concl theorem) boolSyntax.T orelse
           not (supported (#theorem view) theorem) then NONE
        else SOME derived
      end
      handle FactViewLimit => NONE | HOL_ERR _ => NONE
           | Conv.UNCHANGED => NONE
  in
    (add_bound_fact_aliases (List.mapPartial alias sources) state,
     List.mapPartial transport views)
  end

fun add_transported_facts consumer budget transported cs =
  let
    fun implication theorem =
      boolSyntax.is_imp_only (concl (Drule.SPEC_ALL theorem))
    fun add (view : clasetFacts.view, state as (current, from)) =
      if implication (#source view) andalso implication (#theorem view) then
        let
          val (name, index) = transport_name current from
          val _ = searchBudget.charge budget searchBudget.Application
        in
          (clasetLib.add_derived_rule
             {kind=clasetRules.Dest,safe=false,prio=NONE}
             (name,#theorem view) current, index)
        end
        handle HOL_ERR _ => state
      else state
  in if consumer <> clasetLib.SearchFacts then cs
     else #1 (List.foldl add (cs, 0) transported) end

fun bound_fact_views viewed consumer budget body base_cs
      bound cs environment goal ctxt =
      let
        fun attempt state current =
          (SOME (body state current environment goal ctxt),NONE)
          handle exn as HOL_ERR _ => (NONE,SOME exn)
        val initial = attempt bound cs
        fun result (SOME answer,_) = answer
          | result (_,SOME error) = raise error
          | result _ = raise ERR "process_clasimp_bound_fact_views"
              "missing result"
        fun improve () =
          let
            val (next,transported) =
              transport_bound_facts viewed bound environment
            val fact_cs = add_transported_facts consumer budget transported cs
            val candidates = clasetLib.rules_of base_cs @
              clasetLib.invocation_marker_rules cs
            val eligible = if consumer = clasetLib.SafeFacts
              then List.filter safe_named_rule candidates else candidates
            val policy = bound_simplification_policy next
            val ss = bound_simplification_simpset viewed next
            val same = Portable.pointer_eq (bound,next) andalso
              Portable.pointer_eq (cs,fact_cs)
            val start = if same then initial else attempt next fact_cs
            val completed =
              SOME (with_claset_transport_from transport_bound_claset_rules
                budget policy ss eligible fact_cs
                (fn current => body next current environment)
                start goal ctxt)
              handle HOL_ERR _ => NONE
          in
            case (initial,completed) of
                ((SOME (goals,_),_),SOME (new_goals,validate)) =>
                  if length new_goals < length goals then (new_goals,validate)
                  else result initial
              | ((NONE,_),SOME answer) => answer
              | _ => result initial
          end
      in case initial of (SOME ([],validate),_) => ([],validate)
           | _ => improve () end

fun process_clasimp_bound_fact_views viewed consumer budget runtime body
      base_cs base_ss =
  process_clasimp_bound_args consumer budget runtime
    (bound_fact_views viewed consumer budget body base_cs)
    base_cs base_ss

fun process_clasimp_args_fact_views consumer budget
    body base_cs base_ss =
  clasetLib.with_invocation_fact_env_budgeted budget
    {iff_prefix="__clasimp_iff_arg_", extra_markers=clasetLib.no_extra_markers,
     consumer=consumer}
    (fn cs => fn simpset => fn controls => fn environment =>
      case simpset of
          SOME ss =>
            let
              val views =
                clasetFacts.schematic_views environment
              val policy =
                abstraction_policy (charge_normalization budget) ss
                  (controls @ map #theorem views)
              val conversion = rule_normal_form_conv policy ss
              fun transport (view : clasetFacts.view) =
                let
                  val derived =
                    clasetFacts.transport_view conversion view
                  val theorem = #theorem derived
                in
                  if aconv (concl theorem) (concl (#theorem view)) orelse
                     aconv (concl theorem) boolSyntax.T then NONE
                  else SOME derived
                end
                handle HOL_ERR _ => NONE
                     | Conv.UNCHANGED => NONE
              val transported = List.mapPartial transport views
              fun implication theorem =
                boolSyntax.is_imp_only
                  (concl (Drule.SPEC_ALL theorem))
              val fact_cs =
                if consumer <> clasetLib.SearchFacts then cs
                else
                  #1 (List.foldl
                    (fn (view, state as (current, from)) =>
                      if implication (#source view) andalso
                         implication (#theorem view) then
                        let
                          val (name, index) = transport_name current from
                        in
                          searchBudget.charge budget
                            searchBudget.Application;
                          (clasetLib.add_derived_rule
                             {kind = clasetRules.Dest,
                              safe = false, prio = NONE}
                             (name, #theorem view) current, index)
                          handle HOL_ERR _ => state
                        end
                      else state)
                    (cs, 0) transported)
              val candidates =
                clasetLib.rules_of base_cs @
                clasetLib.invocation_marker_rules cs
              val eligible =
                if consumer = clasetLib.SafeFacts then
                  List.filter safe_named_rule candidates
                else candidates
              val arguments =
                controls @ map #theorem (views @ transported)
            in
              with_claset_transport budget policy ss eligible fact_cs
                (fn current => body policy current ss arguments)
            end
        | NONE =>
            raise ERR "process_clasimp_args_fact_views"
              "simpset was not installed")
    base_cs (SOME {base=base_ss, extend=extend_invocation})

fun must_close name =
  Tactical.check_delta
    (ERR name "tactic did not close the goal")
    (fn (_, goals) => null goals)

(* Search tactics benefit from putting extensional equalities into their
   pointwise form before simplification and rule search, in the same two
   readings the terminal step takes.  The conversion is deliberately
   root-only: expanding a nested test such as [f = EMPTY] would lose a
   useful case split, and a pointwise goal must not be extensionalized
   again.

   Which of the two readings an equation is given is this layer's
   default and not the invocation's, and the invocation has the better
   claim where one of its own rewrites states a reading: Isabelle's
   [fun_eq_iff] names the applied one outright.  Only a rewrite of
   equations between functions states one -- [states_a_reading] is
   that test, and it is what keeps every other rewrite that happens to
   match the goal's statement out of the decision -- and the step
   stands down for one that takes this equation where it stands.
   Taken first, the default puts the equation out of that rewrite's
   reach for good -- a membership at a constant-headed side that is a
   predicate short of an argument, and no set, meets none of the facts
   the predicate's own are stated on, and no rewrite brings the two
   readings back together. *)
fun equation_reading term =
  let
    val (equation, _) = boolSyntax.dest_eq term
    val (equated, _) = boolSyntax.dest_eq equation
  in
    Lib.can Type.dom_rng (Term.type_of equated)
  end
  handle HOL_ERR _ => false

fun states_a_reading theorem =
  equation_reading (Thm.concl (Drule.SPEC_ALL theorem))
  handle HOL_ERR _ => false

fun may_state_a_reading theorem =
  let
    fun strip term =
      if boolSyntax.is_forall term then snd (boolSyntax.strip_forall term)
      else term
    fun inspect term =
      if boolSyntax.is_conj term then
        let val (left, right) = boolSyntax.dest_conj term
        in inspect left orelse inspect right end
      else equation_reading (strip term)
  in
    (* Mirror SPEC_ALL followed by CONJUNCTS. A quantifier at a leaf
       can expose an equation, but does not expose more conjuncts. *)
    inspect (strip (Thm.concl theorem))
  end

(* [Conv.REWR_CONV] rejects a theorem it cannot read as a rewrite when
   it is given the theorem, not when the conversion is run, so the
   rejection escapes a [can] that is handed the conversion already
   built.  Applying it inside the [can] is what keeps one unusable
   rewrite in the simpset from raising out of the test and standing
   the step down everywhere. *)
fun read_by_a_rewrite rewrites term =
  let
    fun readings theorem =
      Drule.CONJUNCTS (Drule.SPEC_ALL theorem) handle HOL_ERR _ => [theorem]
    fun applies theorem =
      states_a_reading theorem andalso
      Lib.can (fn subject => Conv.REWR_CONV theorem subject) term
  in
    List.exists
      (fn theorem =>
        may_state_a_reading theorem andalso
        List.exists applies (readings theorem))
      rewrites
  end

val function_equation =
  Lib.can (Type.dom_rng o Term.type_of o boolSyntax.lhs)

fun supplied_reading get_rewrites term =
  function_equation term andalso read_by_a_rewrite (get_rewrites ()) term

fun reads_as_supplied rewrites term =
  not (null rewrites) andalso supplied_reading (fn () => rewrites) term

fun extensional_normalize {rewrites,heads} =
  let val reads = supplied_reading (fn () => Susp.force rewrites)
  in
    Tactical.CONV_TAC
      (Conv.CHANGED_CONV
         (fn term =>
            if reads term then
              raise ERR "extensional_normalize"
                "a rewrite of the invocation's takes the equation"
            else
              Conv.REWR_CONV (extensional_rule heads term) term))
  end

fun extensional_normalize_with charge inventory =
  let val normalize = extensional_normalize inventory
  in fn goal => (charge (); normalize goal) end

fun search_stages limit =
  let
    fun loop bound stages =
      if bound >= limit then List.rev (limit :: stages)
      else loop (bound * 2) (bound :: stages)
  in
    if limit <= 0 then [] else loop 1 []
  end

(* Try the witness-producing tableau at its invocation bound, then deepen
   the classical engine geometrically.  Re-running tableau from depth one
   repeats its whole frontier and caused previously cheap depth-four goals
   to spend their budget before reaching that bound.  Both legs remain
   bounded, and tableau witnesses are not hidden behind a complete
   classical traversal. *)
fun staged_auto_search {blast, depth} tableau_cs classical_cs =
  let
    fun report engine bound tactic goal ctxt =
      let
        val result = tactic goal ctxt
        val suffix =
          if engine = "classical" then
            ", expansions=" ^ Int.toString (clasetSearch.node_count ())
          else
            ", enable 'blast' trace level 2 for expansion statistics"
        val _ =
          traceUtil.trace (traceUtil.level_of tracer ctxt) 1
            (fn () =>
              engine ^ " search solved at stage " ^ Int.toString bound ^
              suffix)
      in
        result
      end
    val tableau =
      if blast <= 0 then []
      else
        [report "tableau" blast
           (tableauLib.CS_BLAST_DEPTH_TAC tableau_cs blast)]
    val classical =
      map
        (fn bound =>
          report "classical" bound
            (NTactical.DETERM
               (classicalLib.CS_DEPTH_SOLVE_TAC
                  {dup = false} bound classical_cs)))
        (search_stages depth)
  in
    Tactical.FIRST (tableau @ classical)
  end

type simplification_driver =
  {policy : Traverse.child_first_policy,ss : simpLib.simpset,
   simplify : tactic,safe_simplify : tactic,
   add_simp : clasetLib.claset -> clasetLib.claset,
   add_safe_simp : clasetLib.claset -> clasetLib.claset}

fun ordinary_simplification_driver policy ss arguments :
      simplification_driver =
  {policy=policy,ss=ss,
   simplify=asm_full_simp_with policy ss arguments,
   safe_simplify=safe_asm_full_simp_with policy ss arguments,
   add_simp=add_simp_wrapper_with policy ss arguments,
   add_safe_simp=add_safe_simp_wrapper_with policy ss arguments}

fun bound_simplification_driver viewed state : simplification_driver =
  {policy=bound_simplification_policy state,
   ss=bound_simplification_simpset viewed state,
   simplify=asm_full_simp_bound viewed state [],
   safe_simplify=safe_asm_full_simp_bound viewed state [],
   add_simp=add_simp_wrapper_bound viewed state [],
   add_safe_simp=add_safe_simp_wrapper_bound viewed state []}

fun auto_driver {blast, depth}
      ({policy,ss,simplify,add_simp,add_safe_simp,...} :
        simplification_driver) cs =
  let
    val search_cs = add_simp cs
    val final_cs = add_safe_simp cs
    val initial_safe =
      NTactical.DETERM (classicalLib.CS_SAFE_TAC cs)
    val search =
      staged_auto_search {blast = blast, depth = depth} cs search_cs
    val final_safe =
      NTactical.DETERM (classicalLib.CS_SAFE_TAC final_cs)
    val inventory = extensional_inventory ss

    (* Isabelle repeatedly selects the first goal on which search succeeds.
       Both search legs solve their selected goal, and the repetition only
       revisits a residue when solving another goal instantiates shared
       schematic variables.  HOL4 kernel subgoals cannot share
       metavariables, so one TRY per subgoal (from THEN) is equivalent. *)
    val script =
      Tactical.EVERY
        [Tactical.TRY (extensional_normalize_with (#charge policy) inventory),
         with_extensionality_with (#charge policy) (#heads inventory) simplify,
         Tactical.TRY initial_safe,
         Tactical.TRY search,
         Tactical.TRY final_safe]
  in
    Tactical.CHANGED_TAC script
  end

fun auto_with bounds policy cs ss arguments =
  auto_driver bounds (ordinary_simplification_driver policy ss arguments) cs

fun callback_bound_rules ambient rules [] goal ctxt = (ambient,rules)
  | callback_bound_rules ambient (SuppliedRuleBinding supplied)
      controls goal ctxt =
      let
        val resolved = ref []
        val _ = markerLib.LLABEL_RES_THEN
          (fn arguments => (resolved := arguments; Tactical.ALL_TAC))
          controls goal ctxt
        val (ambient,SuppliedRuleBinding additional) =
          prepare_invocation_rules ambient (!resolved)
        val rules = SuppliedRuleBinding
          {bundle=simpLib.combine_rewrite_bundles
             [#bundle additional,#bundle supplied],
           controls= #controls additional @ #controls supplied,
           originals= #originals additional @ #originals supplied,
           positions=HOLset.union
             (#positions additional,#positions supplied)}
      in (ambient,rules) end

fun CS_of_with allocate safe_only body cs ss goal ctxt =
  let
    val consumer = if safe_only then clasetLib.SafeFacts
      else clasetLib.SearchFacts
    fun run budget state current _ =
      deferred_view_tactic (fn viewed =>
        body budget (bound_simplification_driver viewed state) current)
  in
    case callback_binding_for ss of
        NONE =>
          let val budget = allocate ()
          in process_clasimp_bound_fact_views true consumer budget
               (budgeted_decisions ctxt budget) (run budget)
               cs ss [] goal ctxt end
      | SOME {ambient,rules,environment,base_cs,controls,active,...} =>
          let
            val (budget,state) = case !active of SOME bound => bound
              | NONE =>
                  let
                    val budget = allocate ()
                    val (ambient,rules) = callback_bound_rules ambient rules
                      controls goal ctxt
                    val state = prepare_bound_rules
                      (traceUtil.level_of tracer ctxt)
                      (budgeted_decisions ctxt budget)
                      (charge_normalization budget) ambient rules
                  in active := SOME (budget,state); (budget,state) end
          in bound_fact_views true consumer budget (run budget)
               base_cs
               state cs environment goal ctxt end
  end

fun CS_of safe_only body =
  CS_of_with normalization_budget safe_only (fn _ => body)

fun CS_AUTO_TAC bounds = CS_of false (auto_driver bounds)

type force_slice =
  {candidates : int, applications : int, normalization : int}

type force_schedule =
  {best : force_slice, tableau : force_slice, depth : force_slice,
   blast_depth : int, classical_depth : int}

val force_schedule : force_schedule ref =
  ref
    {best =
       {candidates = 5000, applications = 500,
        normalization = 500},
     tableau =
       {candidates = 5000, applications = 500,
        normalization = 500},
     depth =
       {candidates = 5000, applications = 500,
        normalization = 500},
     blast_depth = 8, classical_depth = 4}

fun force_budget () =
  searchBudget.create
    {candidates = SOME 100000, applications = SOME 10000,
     normalization = SOME 100000}

fun slice_limits
      ({candidates, applications, normalization} : force_slice) =
  {candidates = SOME candidates, applications = SOME applications,
   normalization = SOME normalization}

fun grow_slice
      ({candidates, applications, normalization} : force_slice) =
  {candidates = candidates * 2,
   applications = applications * 2,
   normalization = normalization * 2}

fun valid_slice
      ({candidates, applications, normalization} : force_slice) =
  candidates > 0 andalso applications > 0 andalso normalization > 0

fun force_search schedule budget cs search_cs goal ctxt =
  let
    val {best, tableau, depth, blast_depth, classical_depth} =
      schedule
    val level = traceUtil.level_of tracer ctxt
    val best_budget = searchBudget.child budget (slice_limits best)
    (* Atomic simplification retains its invocation policy and budget;
       yielding engines alone receive the resumable slice budgets. *)
    val best_session =
      classicalLib.CS_FIRST_BEST_SESSION best_budget
        search_cs goal ctxt
    val best_slice = ref best
    val tableau_slice = ref tableau
    val tableau_current =
      ref
        (NONE :
          (searchBudget.budget *
           (unit ->
             (goal list * validation) blastSearch.budget_outcome))
          option)
    val depth_stages = ref (search_stages classical_depth)
    val depth_slice = ref depth
    val depth_current =
      ref (NONE :
        (searchBudget.budget * classicalLib.depth_session) option)

    fun limit kind =
      if searchBudget.available budget kind then ()
      else raise searchBudget.LimitReached
                   (kind, searchBudget.usage budget)

    (* Extend a yielded turn by its slice, and double the slice. *)
    fun refill turn (slice : force_slice ref) =
      (searchBudget.extend turn searchBudget.Candidate
         (#candidates (!slice));
       searchBudget.extend turn searchBudget.Application
         (#applications (!slice));
       searchBudget.extend turn searchBudget.Normalization
         (#normalization (!slice));
       slice := grow_slice (!slice))

    fun best_turn () =
      case classicalLib.RESUME_FIRST_BEST_SESSION best_session of
            classicalLib.BudgetProved {result, ...} =>
              forceScheduler.Proved result
          | classicalLib.BudgetExhausted => forceScheduler.Exhausted
          | classicalLib.BudgetYielded {kind, ...} =>
              (limit kind;
               traceUtil.trace level 1
                 (fn () =>
                   "FORCE first-best resumes after a " ^
                   (case kind of
                        searchBudget.Candidate => "candidate"
                      | searchBudget.Application => "application"
                      | searchBudget.Normalization => "normalization") ^
                   " turn");
               refill best_budget best_slice;
               forceScheduler.Yielded)
          | classicalLib.BudgetLimitReached {kind, ...} =>
              raise searchBudget.LimitReached
                (kind, searchBudget.usage budget)

    fun tableau_turn () =
      if blast_depth = 0 then forceScheduler.Exhausted
      else
        let
          val (turn, resume) =
            case !tableau_current of
                SOME current => current
              | NONE =>
                  let
                    val turn =
                      searchBudget.child budget
                        (slice_limits (!tableau_slice))
                    val current =
                      (turn,
                       fn () =>
                         tableauLib.CS_BLAST_DEPTH_RESUMABLE turn
                           cs blast_depth goal ctxt)
                  in
                    tableau_current := SOME current;
                    current
                  end
        in
          case resume () of
              blastSearch.BudgetFinished {result = SOME result, ...} =>
                forceScheduler.Proved result
            | blastSearch.BudgetFinished {result = NONE, ...} =>
                (tableau_current := NONE;
                 forceScheduler.Exhausted)
            | blastSearch.BudgetYielded {kind, resume, ...} =>
                (limit kind;
                 traceUtil.trace level 1
                   (fn () =>
                     "FORCE tableau depth " ^
                     Int.toString blast_depth ^
                     " resumes after a bounded turn");
                 refill turn tableau_slice;
                 tableau_current := SOME (turn, resume);
                 forceScheduler.Yielded)
            | blastSearch.BudgetLimitReached {kind, ...} =>
                raise searchBudget.LimitReached
                  (kind, searchBudget.usage budget)
        end

    fun depth_turn () =
      case !depth_stages of
          [] => forceScheduler.Exhausted
        | bound :: rest =>
            let
              val (turn, session) =
                case !depth_current of
                    SOME current => current
                  | NONE =>
                      let
                        val turn =
                          searchBudget.child budget
                            (slice_limits (!depth_slice))
                        val session =
                          classicalLib.CS_DEPTH_SESSION turn
                            {dup = false} bound search_cs goal ctxt
                        val current = (turn, session)
                      in
                        depth_current := SOME current;
                        current
                      end
            in
              case classicalLib.RESUME_DEPTH_SESSION session of
                  classicalLib.DepthProved {result, ...} =>
                    forceScheduler.Proved result
                | classicalLib.DepthExhausted =>
                    (depth_stages := rest;
                     depth_current := NONE;
                     depth_slice := depth;
                     if null rest then forceScheduler.Exhausted
                     else forceScheduler.Yielded)
                | classicalLib.DepthYielded {kind, ...} =>
                    (limit kind;
                     traceUtil.trace level 1
                       (fn () =>
                         "FORCE classical depth " ^
                         Int.toString bound ^
                         " resumes after a bounded turn");
                     refill turn depth_slice;
                     forceScheduler.Yielded)
            end
  in
    case forceScheduler.run
           [best_turn, tableau_turn, depth_turn] of
        SOME result => result
      | NONE => raise ERR "force_search"
                  "all FORCE search engines exhausted"
  end

fun force_driver name budget
      ({policy,ss,simplify,add_simp,...} : simplification_driver) cs =
  let
    val schedule as
      {best, tableau, depth, blast_depth, classical_depth} =
      !force_schedule
    val _ =
      if valid_slice best andalso valid_slice tableau andalso
         valid_slice depth andalso blast_depth >= 0 andalso
         classical_depth >= 0 then ()
      else raise ERR "force_with" "invalid FORCE schedule"
    val search_cs = add_simp cs
    val clarify =
      NTactical.DETERM (classicalLib.CS_CLARIFY_TAC cs)

    (* Simplify before safe saturation.  In particular, this preserves an
       extensional IMAGE obligation until membership rewrites expose the
       constructor constraints from which tableau search builds a witness. *)
    val safe =
      NTactical.DETERM (classicalLib.CS_SAFE_TAC search_cs)
    val search = force_search schedule budget cs search_cs
    val inventory = extensional_inventory ss
    val script =
      Tactical.EVERY
        [Tactical.TRY clarify,
         Tactical.TRY (extensional_normalize_with (#charge policy) inventory),
         simplify,
         with_extensionality_with (#charge policy) (#heads inventory) simplify,
         Tactical.TRY safe,
         search]
  in
    must_close name script
  end

fun force_with name budget policy cs ss arguments =
  force_driver name budget
    (ordinary_simplification_driver policy ss arguments) cs

val CS_FORCE_TAC = CS_of_with force_budget false
  (force_driver "CS_FORCE_TAC")

(* The classical search drivers already succeed only with a closed engine
   state.  must_close is the public contract guard in case that invariant
   changes; it does not add another search step. *)
fun search_driver name engine
      ({policy,ss,add_simp,...} : simplification_driver) cs =
  let
    val clarify =
      NTactical.DETERM (classicalLib.CS_CLARIFY_TAC cs)
    val inventory = extensional_inventory ss
  in
    must_close name
      (Tactical.EVERY
         [Tactical.TRY clarify,
          Tactical.TRY (extensional_normalize_with (#charge policy) inventory),
          NTactical.DETERM
            (engine (add_simp cs))])
  end

fun search_with_simp name engine policy cs ss arguments =
  search_driver name engine
    (ordinary_simplification_driver policy ss arguments) cs

val simp_search =
  (classicalLib.CS_FAST_TAC, classicalLib.CS_SLOW_TAC,
   classicalLib.CS_BEST_TAC)
val (fast_search, slow_search, best_search) = simp_search

val CS_FASTFORCE_TAC =
  CS_of false (search_driver "CS_FASTFORCE_TAC" fast_search)
val CS_SLOWSIMP_TAC =
  CS_of false (search_driver "CS_SLOWSIMP_TAC" slow_search)
val CS_BESTSIMP_TAC =
  CS_of false (search_driver "CS_BESTSIMP_TAC" best_search)

fun clarsimp_driver
      ({safe_simplify,add_safe_simp,...} : simplification_driver) cs =
  let
    val clarify =
      NTactical.DETERM
        (classicalLib.CS_CLARIFY_TAC (add_safe_simp cs))
    val script =
      Tactical.THEN
        (safe_simplify,
         (* Isabelle's clarify tactic succeeds unchanged.  The HOL4
            CS_CLARIFY_TAC deliberately fails on a no-op, so TRY restores
            the sequencing behavior; CHANGED_TAC below guards the complete
            script. *)
         Tactical.TRY clarify)
  in
    Tactical.CHANGED_TAC script
  end

fun clarsimp_with policy cs ss arguments =
  clarsimp_driver (ordinary_simplification_driver policy ss arguments) cs

val CS_CLARSIMP_TAC = CS_of true clarsimp_driver

fun auto_bound bounds viewed state =
  auto_driver bounds (bound_simplification_driver viewed state)

fun force_bound budget viewed state =
  force_driver "FORCE_TAC" budget (bound_simplification_driver viewed state)

fun search_bound name engine viewed state =
  search_driver name engine (bound_simplification_driver viewed state)

val fastforce_bound = search_bound "FASTFORCE_TAC" fast_search
val slowsimp_bound = search_bound "SLOWSIMP_TAC" slow_search
val bestsimp_bound = search_bound "BESTSIMP_TAC" best_search

fun clarsimp_bound viewed state =
  clarsimp_driver (bound_simplification_driver viewed state)

fun restore_normalized_target budget target validation theorems =
  let
    val theorem = validation theorems
  in
    if aconv (concl theorem) target then theorem
    else
      let
        val _ = searchBudget.charge budget searchBudget.Normalization
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

(* Public entry points request certified views only for an open raw pass. *)
fun deferred_bound_driver make state cs =
  deferred_view_tactic (fn viewed => make viewed state cs)

fun public_bound_using_budgeted budget consumer body theorems
      (goal as (_,target)) ctxt =
  let
    fun runtime ss = simpLib.set_subgoaler
      (witness_subgoaler_budgeted budget) (budgeted_decisions ctxt budget ss)
    val (goals,validation) =
      process_clasimp_bound_fact_views true consumer budget runtime
        (fn state => fn cs => fn _ => body state cs)
        (clasetLib.the_claset_of ctxt)
        (clasimp_ss_of ctxt)
        theorems goal ctxt
  in (goals,restore_normalized_target budget target validation) end

fun public_bound_using_with allocate consumer make_body arguments goal ctxt =
  let val budget = allocate ()
  in public_bound_using_budgeted budget consumer (make_body budget)
       arguments goal ctxt end

fun public_bound_using consumer body =
  public_bound_using_with normalization_budget consumer (fn _ => body)

fun AUTO_DEPTH_TAC bounds =
  public_bound_using clasetLib.SearchFacts
    (deferred_bound_driver (auto_bound bounds))

fun AUTO_TAC theorems =
  AUTO_DEPTH_TAC {blast=4,depth=2} theorems

val FORCE_TAC = public_bound_using_with force_budget clasetLib.SearchFacts
  (fn budget => deferred_bound_driver (force_bound budget))

fun FORCE_TAC_BUDGETED budget =
  public_bound_using_budgeted budget clasetLib.SearchFacts
    (deferred_bound_driver (force_bound budget))

val FASTFORCE_TAC =
  public_bound_using clasetLib.SearchFacts
    (deferred_bound_driver fastforce_bound)
val SLOWSIMP_TAC =
  public_bound_using clasetLib.SearchFacts
    (deferred_bound_driver slowsimp_bound)
val BESTSIMP_TAC =
  public_bound_using clasetLib.SearchFacts
    (deferred_bound_driver bestsimp_bound)
val CLARSIMP_TAC =
  public_bound_using clasetLib.SafeFacts (deferred_bound_driver clarsimp_bound)

fun CLARSIMP_TAC_BUDGETED budget =
  public_bound_using_budgeted budget clasetLib.SafeFacts
    (deferred_bound_driver clarsimp_bound)

(* A first-order step meets a goal the simplification before it left in
   the ambient normal form, and HOL4's normal forms are not the ones its
   library states lemmas in: a list equation normalises [x::l] to
   [[x] ++ l], and the ambient EVERY_MEM iff reads EVERY as membership.
   A fact stated the library's way then never meets such a goal, where
   Isabelle's metis reads its facts in the one normal form its simp
   leaves goals in.  Each fact enters in every spelling -- the same
   closing of a normal-form gap from HOL4's side that SUC_FILTER
   performs for the simpset -- so nothing METIS_TAC would have found is
   lost. *)
local
  (* A rule the ambient set already carries normalizes to nothing when
     the whole of it is rewritten -- it rewrites itself away -- so the
     consequent is normalized on its own as well: an equivalence keeps
     the left-hand side it is triggered by and gains the right-hand
     side in the form the goal is in. *)
  fun consequent_conv conv term =
    if boolSyntax.is_forall term then
      Conv.QUANT_CONV (consequent_conv conv) term
    else if boolSyntax.is_imp_only term then
      Conv.RAND_CONV (consequent_conv conv) term
    else if boolSyntax.is_eq term then Conv.RAND_CONV conv term
    else conv term

  fun attempt rule theorem =
    SOME (rule theorem)
    handle Portable.Interrupt => raise Portable.Interrupt
         | HOL_ERR _ => NONE
         | Conv.UNCHANGED => NONE
in
  fun ambient_forms ctxt theorem =
    let
      val ss = clasimp_ss_of ctxt
      val forms =
        [attempt (simpLib.SIMP_RULE ss []) theorem,
         attempt (Conv.CONV_RULE (consequent_conv (simpLib.SIMP_CONV ss [])))
           theorem]
      fun add (NONE, kept) = kept
        | add (SOME form, kept) =
            if aconv (concl form) boolSyntax.T orelse
               List.exists (fn k => aconv (concl k) (concl form)) kept
            then kept
            else kept @ [form]
    in
      List.foldl add [theorem] forms
    end
end

(* Isabelle's first-order step lambda-lifts before it searches: an
   abstraction standing in an argument position becomes a constant with
   a defining equation, so a fact whose function variable has to take
   that abstraction as its value is instantiated first-order and the
   result is used without a beta step.  HOL4's clausifier carries the
   same transformation (normalForms.extract_lambdas) but does not run
   it, so the instantiation leaves a redex the search cannot reduce and
   the step is not taken.

   An abstraction argument of a constant of theory bool or min is the
   body of a binder rather than data, and is descended into instead;
   an eta-contractible one already names a function; and one mentioning
   a variable an enclosing binder binds cannot be named by a goal-level
   variable.  Naming happens whenever there is anything to name, as it
   does in Isabelle: the defining equation goes into the goal with the
   name, so the search is given back everything the abstraction said. *)
local
  fun binder_head head =
    is_const head andalso
    let val {Thy, ...} = dest_thy_const head
    in Thy = "bool" orelse Thy = "min" end

  fun scan bound term found =
    if is_abs term then
      let val (variable, body) = dest_abs term
      in scan (variable :: bound) body found end
    else if is_comb term then
      let
        val (head, arguments) = strip_comb term
        val opaque = binder_head head
        fun argument (argument_term, found) =
          let val found as (seen, abstractions) = scan bound argument_term found
          in
            if is_abs argument_term andalso not opaque andalso
               not (HOLset.member (seen, argument_term)) andalso
               not (Lib.can Term.eta_conv argument_term) andalso
               (null bound orelse
                not (List.exists (fn v => boolSyntax.tmem v bound)
                       (free_vars argument_term)))
            then (HOLset.add (seen, argument_term),
                  argument_term :: abstractions)
            else found
          end
      in
        List.foldl argument (scan bound head found) arguments
      end
    else found

  fun abstractions terms =
    (* Cons the first eligible occurrence, as deduplicating the reversed
       traversal with op_mk_set did. *)
    #2 (List.foldl (fn (term, found) => scan [] term found)
          (Term.empty_tmset, []) terms)

  fun definition (name, abstraction) =
    let
      val (variables, body) = strip_abs abstraction
    in
      boolSyntax.list_mk_forall
        (variables,
         boolSyntax.mk_eq (list_mk_comb (name, variables), body))
    end

  fun beta_theorem (name, abstraction) =
    let
      val (variables, _) = strip_abs abstraction
    in
      Thm.GENL variables
        (Drule.LIST_BETA_CONV (list_mk_comb (abstraction, variables)))
    end
in
  fun LAMBDA_LIFT_TAC (assumptions, conclusion) _ =
    let
      val lifted = abstractions (conclusion :: assumptions)
      val _ =
        if null lifted then
          raise ERR "LAMBDA_LIFT_TAC" "no abstraction stands in an argument"
        else ()
      val avoid = free_varsl (conclusion :: assumptions)
      val names =
        snd (List.foldl
               (fn (abstraction, (avoid, names)) =>
                  let
                    val name =
                      variant avoid
                        (mk_var ("lifted", type_of abstraction))
                  in (name :: avoid, (name, abstraction) :: names) end)
               (avoid, []) lifted)
      val forwards = map (fn (name, a) => a |-> name) names
      val backwards = map (fn (name, a) => name |-> a) names
      val goal =
        (map (subst forwards) assumptions,
         boolSyntax.list_mk_imp
           (map definition names, subst forwards conclusion))
    in
      ([goal],
       fn theorems =>
         List.foldl
           (fn (entry, theorem) => Thm.MP theorem (beta_theorem entry))
           (Thm.INST backwards (hd theorems)) names)
    end
end

(* The forms are computed once for each context the tactic runs in. *)
fun AMBIENT_METIS_TAC theorems =
  let
    val forms = memoUtil.keyed_memo (Lib.curry Portable.pointer_eq)
      (fn ctxt => List.concat (map (ambient_forms ctxt) theorems))
  in
    fn goal => fn ctxt =>
      Tactical.THEN
        (Tactical.TRY LAMBDA_LIFT_TAC, metisLib.METIS_TAC (forms ctxt))
        goal ctxt
  end

end
