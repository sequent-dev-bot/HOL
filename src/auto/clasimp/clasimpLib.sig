(* All source-sensitive public inputs/outputs are explicitly tracked. *)
signature clasimpLib =
sig
  include Abbrev

  (* clasimp.trace.  The tactics read its level from their context with
     traceUtil.level_of. *)
  val tracer : traceUtil.tracer

  (* The safe side-condition solver of the clasimp simpset.  It discharges
     only goals justified without witness instantiation or unsafe search,
     which is what makes it usable in a normalisation phase.  Exported so
     that simpsets derived elsewhere (aesop) share this one solver stack
     rather than restating it. *)
  val safe_solver : Traverse.ssolver

  (* The subgoaler of the clasimp simpset: the traversal's own recursion,
     then, on a side condition [QUANTIFY_CONDITIONS] left existentially
     closed, a match of the condition against the context assumptions
     that reads the witnesses off it.  Exported because a simpset rebuilt
     from [ssfrags_of] keeps only what the fragments carry, and the
     subgoaler is not one of those -- a caller that rebuilds this simpset
     restates it, as it already restates the solvers and the condition
     depth. *)
  val witness_subgoaler : Traverse.subgoaler
  (* The same witness search with candidate charges for each context
     theorem match, and normalization/application charges for replay. *)
  val witness_subgoaler_budgeted :
    searchBudget.budget -> Traverse.subgoaler

  (* Replaces the conditional congruence of a simpset by the weak form,
     which simplifies the condition and leaves the branches to whatever
     case split the caller arranges.  Exported so that the simpsets
     derived elsewhere in this layer (aesop) share the arrangement
     rather than restating it.  Reports a simpset with no conditional
     congruence to replace rather than returning it unchanged. *)
  val weaken_cond_congruence : simpLib.simpset -> simpLib.simpset

  (* The conditional-rewrite depth of this layer's simpsets. *)
  val cond_depth : int

  (* A derivation from srw_ss that takes the bottom-up declarations as a
     layer of their own, so that a declaration does not repeat it.
     [base] is applied to the lift of srw_ss without that layer and
     memoised on the rest of srw_ss; [layered derived add] is memoised on
     the layer, and [add] puts the layer on a simpset.  Exported so that
     the simpsets derived elsewhere in this layer (aesop) share it. *)
  val layered_srw_derivation :
    {base : simpLib.simpset -> 'b,
     layered : 'b Susp.susp ->
               (simpLib.simpset -> simpLib.simpset) -> 'a} ->
    simpLib.simpset -> 'a

  val clasimp_ss : unit -> simpLib.simpset

  (* The simpset of that context's srw_ss and [arith] set; clasimp_ss ()
     is it at the ambient context. *)
  val clasimp_ss_of : Context.t -> simpLib.simpset

  (* From-scratch certified LHS-view candidates, for derivation and its
     exactness/performance checks. Each triple retains its original
     source and name. This does not install views or alter rewrite
     controls. Derivation has a finite per-source allowance; the caller's
     charge callback is shared by both normalization attempts. *)
  val derive_lhs_views : (unit -> unit) -> simpLib.simpset ->
    (simpLib.thname option * thm * thm) list

  datatype lhs_view_rejection =
      NoReducibleArguments | UnchangedLHS | JoinableLHS
    | RenamingUnstable | DerivationLimited | UnsupportedLHS
  type lhs_view_entry =
    {origin : simpLib.rewrite_source,
     source : simpLib.thname option * thm, view : thm option,
     rejection : lhs_view_rejection option, footprint : term list,
     abstraction_positions : (KernelSig.kernelid * int) list,
     normalization : int}
  (* The same derivation including rejected sources, visited dependencies
     and replay charges. Each entry retains its native source handle;
     installed views are not sources for another derivation.
     An unchanged LHS after failed conditional work
     is distinguished from an indexed proof of irreducibility. *)
  val derive_lhs_view_entries : (unit -> unit) -> simpLib.simpset ->
    lhs_view_entry list
  (* Fresh derivation with a complete explicit abstraction-position policy,
     for comparison with invocation tables adjusted by supplied rules. *)
  val derive_lhs_view_entries_with_positions : (unit -> unit) ->
    simpLib.simpset -> (KernelSig.kernelid * int) list -> lhs_view_entry list

  type lhs_view_table
  (* Eight identity-memoized tables with exact dependency invalidation.
     Each table owns lazy viewed/decision bases, including policy-adjusted
     tables; materializing them does not re-derive an earlier raw policy.
     This constructor does not install a table in the public tactics.
     Stats describe construction work; identity hits do no derivation. *)
  val make_lhs_view_cache : (unit -> unit) ->
    simpLib.simpset -> lhs_view_table
  val lhs_view_table_entries : lhs_view_table -> lhs_view_entry list
  val lhs_view_table_generation : lhs_view_table -> int
  val lhs_view_table_stats : lhs_view_table ->
    {derived : int, reused : int, rebuild : bool, normalization : int}

  type working_simpset
  (* Eight lazy identity-memoized working states, backed by the bounded
     incremental table cache. A viewed simpset installs one named fragment
     with native-source controls; its decision base retains those views.
     Plain decisions never force view construction. A failed construction
     can be retried and does not insert a partial predecessor table. *)
  val make_working_simpset_cache : (unit -> unit) ->
    simpLib.simpset -> working_simpset
  val working_original : working_simpset -> simpLib.simpset
  val working_view_table : working_simpset -> lhs_view_table
  val working_full_simpset : working_simpset -> simpLib.simpset
  (* The simpset stripped of its order and linear-arithmetic procedures,
     and which of them it had: the fragments, and the lin_arith solver,
     which a simpset may carry without the fragment *)
  val working_decision_base : working_simpset ->
    {stripped : simpLib.simpset, order : bool, linarith : bool,
     solver : bool}
  val working_plain_decision_base : working_simpset ->
    {stripped : simpLib.simpset, order : bool, linarith : bool,
     solver : bool}
  (* The default state is owned by the stateful derivation hook. Explicit
     simpsets test the last requested default's identity first, then use
     the same bounded cache without forcing an unused default derivation.
     Public tactic placement of view construction remains independent. *)
  val clasimp_working_simpset : unit -> working_simpset
  (* The working state of that context's srw_ss and [arith] set. *)
  val clasimp_working_simpset_of : Context.t -> working_simpset
  val working_simpset_of : simpLib.simpset -> working_simpset

  type supplied_rule_binding
  (* Compile originals before a first pass without priming the ambient set;
     deferred views retain their origins and remaining allowances. *)
  val prepare_supplied_rules : simpLib.simpset -> thm list ->
    supplied_rule_binding
  val supplied_rule_controls : supplied_rule_binding -> thm list
  val supplied_rule_originals : supplied_rule_binding -> thm list
  (* Use cached compiled positions, including filter/exclusion decisions,
     together with the given ambient set; never recompile raw arguments. *)
  val supplied_rule_policy : (unit -> unit) -> simpLib.simpset ->
    supplied_rule_binding -> Traverse.child_first_policy
  val install_supplied_rules : supplied_rule_binding ->
    simpLib.simpset -> simpLib.simpset

  type supplied_view_binding
  (* Detect ambient converses by one parallel rewrite, then derive bound
     originals against the ambient table with those occurrences suspended.
     The 256-entry memo keys theorem identity, the table generation for
     each stage and its effective abstraction policy. Hits replay every
     recorded normalization charge. Completed stages survive a later
     cutoff; incomplete groups do not. Eight derived ambient tables cache
     exact suspension sets and supplied abstraction positions. The ambient
     and supplied entries share the surviving invocation policy. This
     constructor does not bind public tactics. *)
  val make_supplied_view_cache : unit ->
    (unit -> unit) -> lhs_view_table -> supplied_rule_binding ->
    supplied_view_binding
  val supplied_view_entries : supplied_view_binding -> lhs_view_entry list
  val supplied_view_controls : supplied_view_binding -> thm list
  (* Ambient table after suspension and abstraction-policy adjustment, and
     the exact original ambient occurrences suspended for this binding. *)
  val supplied_view_table : supplied_view_binding -> lhs_view_table
  val supplied_view_suspended : supplied_view_binding ->
    simpLib.rewrite_source list
  val supplied_view_stats : supplied_view_binding ->
    {normalization : int, derived : int, memoized : int}
  val supplied_view_policy : (unit -> unit) -> supplied_view_binding ->
    Traverse.child_first_policy
  (* Materialize the binding's adjusted ambient table, sharing its cached
     viewed simpset and decision base without re-deriving the raw table.
     This does not install supplied originals or select public placement. *)
  val working_simpset_for : supplied_view_binding -> working_simpset
  val install_supplied_views : supplied_view_binding ->
    simpLib.simpset -> simpLib.simpset
  (* Add only views after a first pass; never reinstall the originals. *)
  val add_supplied_views : supplied_view_binding ->
    simpLib.simpset -> simpLib.simpset

  type supplied_converse_binding
  (* Before a first pass, detect converses from native patterns without
     forcing ambient views. The binding owns the caller's normalization
     callback; late views continue charging it without repeating detection.
     Eight
     native inventories and masked sets, plus 256 completed theorem groups,
     are retained; hits replay charges and incomplete groups are absent. *)
  val make_supplied_converse_cache : unit -> (unit -> unit) ->
    simpLib.simpset -> supplied_rule_binding -> supplied_converse_binding
  val supplied_converse_rules : supplied_converse_binding ->
    supplied_rule_binding
  val supplied_converse_working : supplied_converse_binding ->
    simpLib.simpset
  val supplied_converse_policy : supplied_converse_binding ->
    Traverse.child_first_policy
  val supplied_converse_suspended : supplied_converse_binding ->
    simpLib.rewrite_source list
  val supplied_converse_stats : supplied_converse_binding ->
    {normalization : int, derived : int, memoized : int}
  val make_supplied_view_cache_after : unit -> lhs_view_table ->
    supplied_converse_binding -> supplied_view_binding

  type bound_simplification
  (* The early binding already reflects invocation rewrite controls.
     Prepare the runtime basis once, install its originals once, and
     retain a lazy table provider without selecting public placement.
     Requested views attach to that same installed simpset and share its
     remaining original/ambient allowances. Existing supplied occurrences
     keep precedence over newly attached ambient views. The provider may
     be eager, deferred or backed by a persisted table. *)
  val make_bound_simplification :
    (simpLib.simpset -> simpLib.simpset) -> (unit -> lhs_view_table) ->
    supplied_converse_binding -> bound_simplification
  val bound_simplification_simpset : bool -> bound_simplification ->
    simpLib.simpset
  val bound_simplification_policy : bound_simplification ->
    Traverse.child_first_policy
  (* Select raw or viewed state explicitly; each consumer retains the
     installed originals and their solver context. Extra arguments are
     local/dynamic rules, not the already bound original citations. *)
  val asm_full_simp_bound : bool -> bound_simplification -> thm list -> tactic
  val safe_asm_full_simp_bound : bool -> bound_simplification ->
    thm list -> tactic
  val cascade_safe_simp_bound : bool -> bound_simplification ->
    thm list -> tactic
  (* Apply simp directives before early binding; table placement stays lazy.
     Requirement payloads share native origins; checks recur per simp step.
     Assumption controls recur over each pass's current context. Callers
     resolve goal-dependent abbreviations and label references first;
     the public standalone entry points perform that resolution. *)
  (* The first argument is the clasimp.trace level, read with
     traceUtil.level_of tracer, at which binding reports the ambient
     converses it suspends. *)
  val prepare_bound_simplification :
    traceUtil.level -> (simpLib.simpset -> simpLib.simpset) ->
    (unit -> unit) -> simpLib.simpset -> thm list -> bound_simplification
  val add_simp_wrapper_bound : bool -> bound_simplification -> thm list ->
    clasetLib.claset -> clasetLib.claset
  val add_safe_simp_wrapper_bound : bool -> bound_simplification -> thm list ->
    clasetLib.claset -> clasetLib.claset

  (* [with_extensionality ss simplify] runs [simplify] and, where it
     leaves a goal whose conclusion is an equation between functions,
     takes that equation pointwise and runs [simplify] again.  HOL4's
     library states applied what the source states at the function
     level, so a goal at the function level cannot meet the rule that
     settles it; this is the one step that brings the two together.
     Which of the two readings the equation is taken in is read off
     [ss], as [reads_as_membership] below says.  It wraps a method's
     simplification, not a step inside a search.  Exported so that a
     method built from HOL4's simplifier directly -- the parity corpus
     builds its simp method that way -- takes the step the layer's own
     methods take, rather than restating it. *)
  val with_extensionality : simpLib.simpset -> tactic -> tactic

  (* True where the pointwise reading of an equation between functions is
     its membership and not its application: a side is headed by a
     constant the simpset states a membership fact about -- some rewrite
     of its own has [_ IN c ...] for a left-hand side, as the [set],
     image and intersection rules do.  A constant-headed side that is a
     predicate short of an argument and no set has every fact stated
     applied, and read as a membership meets none of them.  It asks this
     of the equation it is given: a caller whose own pass reaches
     equations below the goal's conclusion asks it of each of those.
     The closure collects the compiled heads when an equation needs
     them, including installed views and respecting removals and filters.
     Exported for the same reason as [states_a_reading] below. *)
  val reads_as_membership : simpLib.simpset -> term -> bool

  (* True of a rewrite that states how an equation between functions is
     to be read -- its own left-hand side is such an equation, which is
     what [fun_eq_iff] and a membership reading are and what no other
     rewrite is.  The extensional steps above impose a reading of their
     own, and they stand down where one of these takes the equation
     first.  Exported so that a method built from HOL4's simplifier
     directly -- the parity corpus builds its recipes that way -- can
     make the same decision about its own set-equality pass. *)
  val states_a_reading : thm -> bool

  (* True if a supplied rewrite applies to the function equation as given.
     The rewrites may be quantified or conjoined. *)
  val reads_as_supplied : thm list -> term -> bool

  (* Bind citations once, suspending ambient converses for this invocation.
     Public ambient views remain pending the construction-placement choice. *)
  val asm_full_simp : simpLib.simpset -> thm list -> tactic
  val safe_asm_full_simp : simpLib.simpset -> thm list -> tactic

  val add_simp_wrapper :
    simpLib.simpset -> thm list -> clasetLib.claset -> clasetLib.claset
  val add_safe_simp_wrapper :
    simpLib.simpset -> thm list -> clasetLib.claset -> clasetLib.claset

  (* Pure [iff] decision tree.  Callers choose where to install the
     derived claset rules and the normalized simpset rewrite. *)
  val iff_declaration :
    string -> thm ->
    {rules :
       (clasetRules.rulespec * (string * thm)) list,
     rewrite : thm}

  (* Installs the rules of an iff_declaration.  They are derived rather than
     named by the user, so a duplicate among them is dropped silently. *)
  val add_iff_rules :
    (clasetRules.rulespec * (string * thm)) list ->
    clasetLib.claset -> clasetLib.claset

  val remove_iff : string -> unit

  (* An [iff] whose simpset half is installed as a low-priority reducer,
     so that the traversal offers it a subject the rewrites and the
     descent have already left alone.  Isabelle's simplifier rewrites the
     innermost redex first and so never offers such a rule anything else;
     HOL4's rewrites the outermost first, where a rule about an arbitrary
     term of a type -- [x <> NONE] -- fires above every rule about that
     term's own head.  The claset halves are those of [iff]. *)
  val remove_iff_bottom_up : string -> unit

  (* The same declaration without the claset halves, for a law the source
     declares [simp] and not [iff].  Isabelle's miniscoping laws are the
     family: fired above a quantifier's body, as HOL4's order would fire
     an ordinary rewrite, such a law pushes the quantifier past a side
     whose own antecedent the body had not yet been read with. *)
  val remove_simp_bottom_up : string -> unit

  (* The simpset half of that declaration, for a rewrite a caller
     installs for one invocation instead of declaring: a fragment whose
     rewrites the traversal reaches only once the rewrites and the
     descent have both left a node alone.  A rule whose left side reads
     an arbitrary term of its subject's type fires, in HOL4's order,
     above every rule about the subject's own head; in this fragment it
     is offered the subject the other rules have finished with, which is
     the only subject Isabelle's order ever offers it.  The rewrites are
     unconditional equations, as the declaration's are. *)
  val normalised_subject_fragment : thm list -> simpLib.ssfrag
  (* Ordinary comparison/default clients keep their independent engine. *)
  val normalised_subject_fragment_ordinary : thm list -> simpLib.ssfrag

  (* Whether the simplifier can make a rewrite of this argument that is
     able to fire.  A conditional rule whose conclusion is an equation
     between variables prepares to a rewrite matching every equation in
     the goal whose condition the match determines nothing of, which the
     simplifier then tries to discharge at each of them; an invocation
     declares such an argument to its claset instead of its simpset.  A
     caller that hands its arguments to a simpset directly asks here
     first. *)
  val simp_argument_can_fire : thm -> bool

  val extend_invocation :
    {iff_prefix : string, simp_rules : thm list, iff_rules : thm list,
     claset : clasetLib.claset, simpset : simpLib.simpset,
     context : Context.t} ->
    clasetLib.claset * simpLib.simpset

  (* Shared packaging for theorem-list clasimp tactics. The body receives
     the temporary claset, temporary simpset, and unchanged simp controls.
     CS consumers inside the callback reuse compiled supplied origins and
     its fact environment. The binding expires on return or exception. *)
  val process_clasimp_args :
    (clasetLib.claset -> simpLib.simpset -> thm list -> tactic) ->
    clasetLib.claset -> simpLib.simpset -> thm list -> tactic

  (* Keep declaration payloads apart from ambient view reducers. Resolve
     labels before one binding; retain the invocation fact environment. *)
  val process_clasimp_bound_args : clasetLib.fact_consumer ->
    searchBudget.budget -> (simpLib.simpset -> simpLib.simpset) ->
    (bound_simplification -> clasetLib.claset ->
     clasetFacts.environment -> tactic) ->
    clasetLib.claset -> simpLib.simpset -> thm list -> tactic

  (* Retry open work with certified fact/rule transport, retaining the
     bound originals, policy and fact environment. Derivation restores
     remaining quotas; aliases require compiled sources. The boolean selects
     raw or viewed state explicitly, without choosing a public default. *)
  val process_clasimp_bound_fact_views : bool -> clasetLib.fact_consumer ->
    searchBudget.budget -> (simpLib.simpset -> simpLib.simpset) ->
    (bound_simplification -> clasetLib.claset ->
     clasetFacts.environment -> tactic) ->
    clasetLib.claset -> simpLib.simpset -> thm list -> tactic

  (* Contextual AUTO, FORCE, FASTFORCE, SLOWSIMP, BESTSIMP and CLARSIMP
     retain the supplied claset, then retry unfinished goals with
     certified rule views in the supplied simpset's form. The retry
     shares one budget and preserves the original rule role and support. *)
  val CS_AUTO_TAC :
    {blast : int, depth : int} ->
    clasetLib.claset -> simpLib.simpset -> tactic
  type force_slice =
    {candidates : int, applications : int, normalization : int}
  type force_schedule =
    {best : force_slice, tableau : force_slice, depth : force_slice,
     blast_depth : int, classical_depth : int}
  (* Each positive slice is doubled after a yield. First-best, depth and
     tableau retain their search state across turns. *)
  val force_schedule : force_schedule ref
  val CS_FORCE_TAC :
    clasetLib.claset -> simpLib.simpset -> tactic
  val CS_FASTFORCE_TAC :
    clasetLib.claset -> simpLib.simpset -> tactic
  val CS_SLOWSIMP_TAC :
    clasetLib.claset -> simpLib.simpset -> tactic
  val CS_BESTSIMP_TAC :
    clasetLib.claset -> simpLib.simpset -> tactic
  val CS_CLARSIMP_TAC :
    clasetLib.claset -> simpLib.simpset -> tactic

  (* Driver stages retain one bound invocation across direct and nested
     simplification. View selection remains explicit for table placement. *)
  val auto_bound : {blast : int, depth : int} -> bool ->
    bound_simplification -> clasetLib.claset -> tactic
  val force_bound : searchBudget.budget -> bool ->
    bound_simplification -> clasetLib.claset -> tactic
  val fastforce_bound : bool ->
    bound_simplification -> clasetLib.claset -> tactic
  val slowsimp_bound : bool ->
    bound_simplification -> clasetLib.claset -> tactic
  val bestsimp_bound : bool ->
    bound_simplification -> clasetLib.claset -> tactic
  val clarsimp_bound : bool ->
    bound_simplification -> clasetLib.claset -> tactic

  val AUTO_DEPTH_TAC :
    {blast : int, depth : int} -> thm list -> tactic
  val AUTO_TAC : thm list -> tactic
  val FORCE_TAC : thm list -> tactic
  val FORCE_TAC_BUDGETED :
    searchBudget.budget -> thm list -> tactic
  val FASTFORCE_TAC : thm list -> tactic
  val SLOWSIMP_TAC : thm list -> tactic
  val BESTSIMP_TAC : thm list -> tactic
  val CLARSIMP_TAC : thm list -> tactic
  (* The supplied invocation budget charges child-first normalization.
     LimitReached propagates as a typed resource outcome. *)
  val CLARSIMP_TAC_BUDGETED :
    searchBudget.budget -> thm list -> tactic

  (* METIS_TAC with each fact offered in the ambient normal form as well
     as its own.  A first-order step runs on a goal the simplification
     before it normalised, and a library lemma is not stated in that
     normal form; offering both spellings is what lets the fact meet the
     goal, and it can only add to what METIS_TAC would have found. *)
  val AMBIENT_METIS_TAC : thm list -> tactic

  (* Name each abstraction that stands in an argument position with a
     goal-level variable and carry its defining equation into the goal.
     A first-order search can then instantiate a function variable with
     the name, where instantiating it with the abstraction itself leaves
     a redex the search has no rule to reduce. *)
  val LAMBDA_LIFT_TAC : tactic
end
