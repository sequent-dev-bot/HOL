(* Copyright (c) 2009-2011 Tjark Weber. All rights reserved. *)

(* Proof reconstruction for Z3: replaying Z3's proofs in HOL *)

structure Z3_ProofReplay =
struct

local

  open boolLib
  fun profile name f x =
    Profile.profile_with_exn_name name f x

  open Z3_Proof

  val op ++ = bossLib.++
  val op >> = Tactical.>>
  val op |-> = Lib.|->

  val ERR = Feedback.mk_HOL_ERR "Z3_ProofReplay"
  val WARNING = Feedback.HOL_WARNING "Z3_ProofReplay"

  val asserted_membership_diagnostic =
    "HOLSMT_TRANSLATION_ASSERTED_MEMBERSHIP"
  val unsupported_rewrite_diagnostic =
    "HOLSMT_Z3_REWRITE_UNSUPPORTED"
  val unsupported_hyp_removal_diagnostic =
    "HOLSMT_Z3_HYP_REMOVAL_UNSUPPORTED"

  (* Dedicated-theory failures must cross the generic rewrite handlers
     without inviting arithmetic or unification fallbacks. *)
  exception FP_REWRITE_ERROR of exn
  exception BAG_REWRITE_ERROR of exn
  exception STRING_REWRITE_ERROR of exn
  exception BV_REWRITE_ERROR of exn
  exception DEFINITION_REWRITE_ERROR of exn
  exception ORDINARY_DEFINITION_UNIFICATION_DECLINE
  exception ASSERTED_EQUALITY_REWRITE_ERROR of exn

  val ALL_DISTINCT_NIL = HolSmtTheory.ALL_DISTINCT_NIL
  val ALL_DISTINCT_CONS = HolSmtTheory.ALL_DISTINCT_CONS
  val NOT_MEM_NIL = HolSmtTheory.NOT_MEM_NIL
  val NOT_MEM_CONS = HolSmtTheory.NOT_MEM_CONS
  val AND_T = HolSmtTheory.AND_T
  val T_AND = HolSmtTheory.T_AND
  val F_OR = HolSmtTheory.F_OR
  val CONJ_CONG = HolSmtTheory.CONJ_CONG
  val NOT_NOT_ELIM = HolSmtTheory.NOT_NOT_ELIM
  val NOT_NOT_INTRO = HolSmtTheory.NOT_NOT_INTRO
  val NOT_REVERSE = HolSmtTheory.NOT_REVERSE
  val NOT_FALSE = HolSmtTheory.NOT_FALSE
  val NNF_CONJ = HolSmtTheory.NNF_CONJ
  val NNF_DISJ = HolSmtTheory.NNF_DISJ
  val NNF_NOT_NOT = HolSmtTheory.NNF_NOT_NOT
  val NEG_IFF_1_1 = HolSmtTheory.NEG_IFF_1_1
  val NEG_IFF_1_2 = HolSmtTheory.NEG_IFF_1_2
  val NEG_IFF_2_1 = HolSmtTheory.NEG_IFF_2_1
  val NEG_IFF_2_2 = HolSmtTheory.NEG_IFF_2_2
  val DISJ_ELIM_1 = HolSmtTheory.DISJ_ELIM_1
  val DISJ_ELIM_2 = HolSmtTheory.DISJ_ELIM_2
  val IMP_DISJ_1 = HolSmtTheory.IMP_DISJ_1
  val IMP_DISJ_2 = HolSmtTheory.IMP_DISJ_2
  val IMP_FALSE = HolSmtTheory.IMP_FALSE
  val AND_IMP_INTRO_SYM = HolSmtTheory.AND_IMP_INTRO_SYM
  val VALID_IFF_TRUE = HolSmtTheory.VALID_IFF_TRUE

  (* Instantiate `thm` (types and free variables) so its conclusion becomes
     `t`.  Fails if no such instantiation exists. *)
  fun exact_inst thm t =
    Drule.INST_TY_TERM (Term.match_term (Thm.concl thm) t) thm

  (* [Library.gen_instantiation] has one documented ordinary-decline shape.
     Catch only that shape; kernel failures and resource exceptions must not
     become invitations to try a more expensive definition procedure. *)
  fun with_expected_instantiation_fallback instantiate fallback input =
    instantiate input
    handle Feedback.HOL_ERR holerr =>
      if Feedback.top_structure_of holerr = "Library" andalso
         Feedback.top_function_of holerr = "gen_instantiation" andalso
         not (SmtResource.is_resource_gate holerr) then
        fallback input
      else
        raise Feedback.HOL_ERR holerr

  fun gen_instantiation_with_expected_fallback fallback input =
    with_expected_instantiation_fallback Library.gen_instantiation
      fallback input

  structure Definition_Graph = Graph(
    type key = Term.term
    val ord = Term.var_compare
    val pp = fn _ => HOLPP.add_string "<proof-variable>"
  )

  (***************************************************************************)
  (* functions that manipulate/access "global" state                         *)
  (***************************************************************************)

  type state = {
    (* The exact assertions emitted for the original goal.  An [asserted]
       proof node is admissible only when its parsed term is a member of this
       set; this is the enforcement half of translation round-trip identity. *)
    allowed_asserted_hyps : Term.term HOLset.set,
    (* keeps track of assumptions; (only) these may remain in the
       final theorem *)
    asserted_hyps : Term.term HOLset.set,
    (* keeps track of definitions introduced by Z3; these get added during the
       proof and are deleted at the end, just before returning the final
       theorem.  Each is an equality with a proof variable on at least one
       side.  Its stored orientation is retained; when both sides are proof
       variables, the stored left side is the established definition name. *)
    definition_hyps : Term.term HOLset.set,
    (* Proof variables still eligible for a definition.  [state_define]
       removes an oriented definition's established left-hand name once,
       instead of rescanning every prior definition at each rewrite. *)
    flexible_vars : Term.term HOLset.set,
    (* stores certain theorems (proved by 'rewrite' or 'th_lemma') for
       later retrieval, to avoid re-reproving them *)
    thm_cache : Thm.thm Net.net,
    large_thm_cache : (Term.term * Thm.thm) list,
    (* contains all of the variables that Z3 has defined *)
    var_set : Term.term HOLset.set,
    (* Parser-discovered FP decomposition associations.  These are hints, not
       hypotheses: fp(3)(bit-decomposition) must prove a definition before
       adding it through [state_define]. *)
    bit_decompositions : bit_decomposition list,
    (* Exact per-translation operator provenance.  Only definitions selected
       by SmtLib's EncodedSymbol records may be unfolded during replay. *)
    translation_definitions : SmtLib.emitted_definition list,
    (* One mutable atom cache for the complete proof replay.  Every general
       reduction node in this state shares its owning-theory expansions. *)
    skeleton_context : SmtSkeletonProve.context,
    word_context : SmtWordGraph.context,
    (* General regex-index consequences are derived from the asserted DAG.
       Share their checked specializations across all nodes in one proof. *)
    string_index_cache : SmtStringProve.contextual_index_cache,
    z3_version : string
  }

  fun state_assert (s : state) (t : Term.term) : state =
    {
      allowed_asserted_hyps = #allowed_asserted_hyps s,
      asserted_hyps = HOLset.add (#asserted_hyps s, t),
      definition_hyps = #definition_hyps s,
      flexible_vars = #flexible_vars s,
      thm_cache = #thm_cache s,
      large_thm_cache = #large_thm_cache s,
      var_set = #var_set s,
      bit_decompositions = #bit_decompositions s,
      translation_definitions = #translation_definitions s,
      skeleton_context = #skeleton_context s,
      word_context = #word_context s,
      string_index_cache = #string_index_cache s,
      z3_version = #z3_version s
    }

  fun oriented_definition_parts var_set definition =
    let
      val (left, right) = boolSyntax.dest_eq definition
      fun eligible term =
        Term.is_var term andalso HOLset.member (var_set, term)
    in
      if eligible left then SOME (left, right)
      else if eligible right then SOME (right, left)
      else NONE
    end
    handle Feedback.HOL_ERR _ => NONE

  fun oriented_definition_name var_set definition =
    Option.map Lib.fst (oriented_definition_parts var_set definition)

  fun state_define (s : state) (terms : Term.term list) : state =
    let
      val newly_rigid = List.mapPartial
        (oriented_definition_name (#var_set s)) terms
      fun make_rigid (name, flexible) =
        HOLset.delete (flexible, name)
        handle HOLset.NotFound => flexible
    in {
      allowed_asserted_hyps = #allowed_asserted_hyps s,
      asserted_hyps = #asserted_hyps s,
      definition_hyps = HOLset.addList (#definition_hyps s, terms),
      flexible_vars = List.foldl make_rigid (#flexible_vars s) newly_rigid,
      thm_cache = #thm_cache s,
      large_thm_cache = #large_thm_cache s,
      var_set = #var_set s,
      bit_decompositions = #bit_decompositions s,
      translation_definitions = #translation_definitions s,
      skeleton_context = #skeleton_context s,
      word_context = #word_context s,
      string_index_cache = #string_index_cache s,
      z3_version = #z3_version s
    } end

  (* Net indexing walks the unfolded term.  A large shared conclusion is
     cheap as a DAG but can be prohibitively expensive to index.  Keep such
     theorems in an exact-match cache instead. *)
  fun state_cache_thm (s : state) (thm : Thm.thm) : state =
    let
      val conclusion = Thm.concl thm
      val large = SmtResource.term_nodes_up_to 16384 conclusion > 16384
    in {
      allowed_asserted_hyps = #allowed_asserted_hyps s,
      asserted_hyps = #asserted_hyps s,
      definition_hyps = #definition_hyps s,
      flexible_vars = #flexible_vars s,
      thm_cache = if large then #thm_cache s
                  else Net.insert (conclusion, thm) (#thm_cache s),
      large_thm_cache =
        if large then (conclusion, thm) :: #large_thm_cache s
        else #large_thm_cache s,
      var_set = #var_set s,
      bit_decompositions = #bit_decompositions s,
      translation_definitions = #translation_definitions s,
      skeleton_context = #skeleton_context s,
      word_context = #word_context s,
      string_index_cache = #string_index_cache s,
      z3_version = #z3_version s
    } end

  fun state_inst_cached_thm (s : state) (t : Term.term) : Thm.thm =
    let
      val available = HOLset.union (#asserted_hyps s, #definition_hyps s)
      fun instantiate thm =
        let val thm = exact_inst thm t in
          if HOLset.isSubset (Thm.hypset thm, available) then thm
          else raise ERR "state_inst_cached_thm" "unavailable hypothesis"
        end
      fun lookup_net () =
        Lib.tryfind instantiate (Net.match t (#thm_cache s))
      fun exact_large (saved, thm) =
        CPC_ProofReplay.sharing_aware_aconv saved t andalso
        HOLset.isSubset (Thm.hypset thm, available)
    in
      if not (List.null (#large_thm_cache s)) andalso
         SmtResource.term_nodes_up_to 16384 t > 16384 then
        (case List.find exact_large (#large_thm_cache s) of
           SOME (_, thm) => thm
         | NONE => lookup_net ())
      else lookup_net ()
    end

  (* FP decomposition theorems carry proof-local packed-word definitions.
     Instantiating one cached decomposition at a different FP/BV pair creates
     a second definition for the same skolem and breaks checked definition
     elimination.  FP replay therefore reuses only the exact recorded
     conclusion; its cheap proforma rung can simply re-prove other instances. *)
  fun state_exact_cached_thm (s : state) (t : Term.term) : Thm.thm =
    let
      fun lookup_net () =
        Lib.tryfind
          (fn thm =>
            if Thm.concl thm ~~ t then thm
            else raise ERR "state_exact_cached_thm"
              "different conclusion")
          (Net.match t (#thm_cache s))
    in
      if not (List.null (#large_thm_cache s)) andalso
         SmtResource.term_nodes_up_to 16384 t > 16384 then
        (case List.find
           (fn (saved, _) =>
             CPC_ProofReplay.sharing_aware_aconv saved t)
           (#large_thm_cache s) of
           SOME (_, thm) => thm
         | NONE => lookup_net ())
      else lookup_net ()
    end

  (***************************************************************************)
  (* auxiliary functions                                                     *)
  (***************************************************************************)

  (* |- l1 \/ l2 \/ ... \/ ln \/ t   |- ~l1   |- ~l2   |- ...   |- ~ln
     -----------------------------------------------------------------
                                  |- t

     The input clause (including "t") is really treated as a set of
     literals: the resolvents need not be in the correct order, "t"
     need not be the rightmost disjunct (and if "t" is a disjunction,
     its disjuncts may even be spread throughout the input clause).
     Note also that "t" may be F, in which case it need not be present
     in the input clause.

     We treat all "~li" as atomic, even if they are negated
     disjunctions. *)
  fun unit_resolution (thms, t) =
  let
    val _ = if List.null thms then
        raise ERR "unit_resolution" ""
      else ()
    fun disjuncts dict (disj, thm) =
    let
      val (l, r) = boolSyntax.dest_disj disj
      (* |- l \/ r ==> ... *)
      val thm = Thm.DISCH disj thm
      val l_imp_concl = Thm.MP thm (Thm.DISJ1 (Thm.ASSUME l) r)
      val r_imp_concl = Thm.MP thm (Thm.DISJ2 l (Thm.ASSUME r))
    in
      disjuncts (disjuncts dict (l, l_imp_concl)) (r, r_imp_concl)
    end
    handle Feedback.HOL_ERR _ =>
      Redblackmap.insert (dict, disj, thm)
    fun prove_from_disj dict disj =
      Redblackmap.find (dict, disj)
      handle Redblackmap.NotFound =>
        let
          val (l, r) = boolSyntax.dest_disj disj
          val l_th = prove_from_disj dict l
          val r_th = prove_from_disj dict r
        in
          Thm.DISJ_CASES (Thm.ASSUME disj) l_th r_th
        end
    val dict = disjuncts (Redblackmap.mkDict Term.compare) (t, Thm.ASSUME t)
    (* derive 't' from each negated resolvent *)
    val dict = List.foldl (fn (th, dict) =>
      let
        val lit = Thm.concl th
        val (is_neg, neg_lit) = (true, boolSyntax.dest_neg lit)
          handle Feedback.HOL_ERR _ =>
            (false, boolSyntax.mk_neg lit)
        (* |- neg_lit ==> F *)
        val th = if is_neg then
            Thm.NOT_ELIM th
          else
            Thm.MP (Thm.SPEC lit NOT_FALSE) th
        (* neg_lit |- t *)
        val th = Thm.CCONTR t (Thm.MP th (Thm.ASSUME neg_lit))
      in
        Redblackmap.insert (dict, neg_lit, th)
      end) dict (List.tl thms)
    (* derive 't' from ``F`` (just in case ``F`` is a disjunct) *)
    val dict = Redblackmap.insert
      (dict, boolSyntax.F, Thm.CCONTR t (Thm.ASSUME boolSyntax.F))
    val clause = Thm.concl (List.hd thms)
    val clause_imp_t = prove_from_disj dict clause
  in
    Thm.MP (Thm.DISCH clause clause_imp_t) (List.hd thms)
  end

  (* e.g.,   "(A --> B) --> C --> D" acc   ==>   [A, B, C, D] @ acc *)
  fun strip_fun_tys ty acc =
    let
      val (dom, rng) = Type.dom_rng ty
    in
      strip_fun_tys dom (strip_fun_tys rng acc)
    end
    handle Feedback.HOL_ERR _ => ty :: acc

  (* approximate: only descends into combination terms and function types *)
  fun term_contains_real_ty tm =
    let val (rator, rand) = Term.dest_comb tm
    in
      term_contains_real_ty rator orelse term_contains_real_ty rand
    end
    handle Feedback.HOL_ERR _ =>
      List.exists (Lib.equal realSyntax.real_ty)
        (strip_fun_tys (Term.type_of tm) [])

  val type_contains = Library.type_contains  (* shared, see Library.sml *)

  fun term_contains_measure pred tm =
    let
      val seen = ref Term.empty_tmset
      val visited = ref 0
      fun visit subterm =
        if HOLset.member (!seen, subterm) then false
        else
          (visited := !visited + 1;
           seen := HOLset.add (!seen, subterm);
           pred subterm orelse
           case Term.dest_term subterm of
             Term.COMB (rator, rand) => visit rator orelse visit rand
           | Term.LAMB (_, body) => visit body
           | _ => false)
      val found = visit tm
    in
      {found = found, visited = !visited}
    end

  fun term_contains_type_measure pred =
    term_contains_measure
      (fn subterm => type_contains pred (Term.type_of subterm))

  fun term_contains_type pred tm =
    #found (term_contains_type_measure pred tm)

  fun has_arith_atom tm =
    term_contains_type
      (fn ty =>
        Type.compare (ty, intSyntax.int_ty) = EQUAL orelse
        Type.compare (ty, realSyntax.real_ty) = EQUAL) tm

  fun has_word_atom tm =
    term_contains_type wordsSyntax.is_word_type tm

  fun exact_decimal_index function_name text =
    let
      val n = String.size text
      fun all_digits i = i = n orelse
        (Char.isDigit (String.sub (text, i)) andalso all_digits (i + 1))
      val _ = n > 0 andalso all_digits 0 orelse
        raise ERR function_name
          "fpa2bv symbol has a malformed numeric identifier"
    in
      case Int.fromString text of
        SOME index => index
      | NONE => raise ERR function_name
          "fpa2bv numeric identifier is outside the supported range"
    end

  fun fp_k_index version var =
    let
      val name = Lib.fst (Term.dest_var var)
      val {prefix, packed_suffix} = fp_skolem_naming version
      val prefix_size = String.size prefix
      val _ = String.isPrefix prefix name orelse
        raise ERR "fp_k_index"
          ("fpa2bv symbol violates the naming contract for Z3 anchor " ^
           version)
      val digits = String.extract (name, prefix_size, NONE)
      val n = String.size digits
      val _ = n > 0 andalso String.sub (digits, n - 1) = packed_suffix orelse
        raise ERR "fp_k_index"
          ("fpa2bv packed symbol violates the suffix contract for Z3 " ^
           "anchor " ^ version)
    in
      exact_decimal_index "fp_k_index"
        (String.substring (digits, 0, n - 1))
    end

  fun fp_inferred_packed_vars_in version registered =
    List.filter
      (fn var => wordsSyntax.is_word_type (Term.type_of var) andalso
        Lib.can (fp_k_index version) var)
      (HOLset.listItems registered)

  fun fp_inferred_packed_vars_with_provenance version registered assertions =
    if List.exists SmtFpProve.has_fp_theory_term assertions then
      fp_inferred_packed_vars_in version registered
    else
      []

  (* Validate the complete fpa2bv allocation at once.  A packed word owns
     exactly its declared width of Boolean skolems; no unallocated Boolean
     fpa2bv names may remain.  Z3 may interleave unrelated skolem identifiers,
     so ordering is deterministic but identifiers need not be consecutive.
     Returning [] on an incoherent allocation makes admission fail closed. *)
  fun fp_per_bit_definitions_in version packed_vars registered =
  let
    fun compare_index (left, right) =
      Int.compare (fp_k_index version left, fp_k_index version right)
    val bv_vars = Listsort.sort compare_index packed_vars
    val _ = List.all (fn bv =>
      wordsSyntax.is_word_type (Term.type_of bv) andalso
      HOLset.member (registered, bv)) bv_vars orelse
      raise ERR "fp_per_bit_definitions"
        "packed fpa2bv symbol is absent or has the wrong sort"
    val bool_vars = Listsort.sort compare_index
      (List.filter
        (fn var => Term.type_of var = Type.bool andalso
          Lib.can (fp_k_index version) var)
        (HOLset.listItems registered))
    fun allocate ([], remaining, definitions) =
          if List.null remaining then List.rev definitions
          else raise ERR "fp_per_bit_definitions"
            "unallocated fpa2bv Boolean skolems"
      | allocate (bv :: bvs, remaining, definitions) =
          let
            val width = Arbnum.toInt (wordsSyntax.size_of bv)
            val _ = List.length remaining >= width orelse
              raise ERR "fp_per_bit_definitions"
                "too few fpa2bv Boolean skolems"
            val bits = List.take (remaining, width)
            val remaining = List.drop (remaining, width)
            fun definition (offset, bit) =
              boolSyntax.mk_eq (bit, wordsSyntax.mk_word_bit
                (numSyntax.term_of_int offset, bv))
          in
            allocate (bvs, remaining,
              List.revAppend
                (List.map definition
                   (ListPair.zip (List.tabulate (width, Lib.I), bits)),
                 definitions))
          end
  in
    allocate (bv_vars, bool_vars, [])
  end
  handle Fail _ => []
       | Option.Option => []
       | Overflow => []
       | Feedback.HOL_ERR _ => []

  fun fp_packed_vars (state : state) =
    case List.map
        (fn ({bv_var, ...} : bit_decomposition) => bv_var)
        (#bit_decompositions state) of
      [] =>
        fp_inferred_packed_vars_with_provenance
          (#z3_version state) (#var_set state)
          (HOLset.listItems (#allowed_asserted_hyps state))
    | recorded => recorded

  fun fp_per_bit_definitions (state : state) =
    fp_per_bit_definitions_in (#z3_version state)
      (fp_packed_vars state) (#var_set state)

  (* A word can disappear syntactically after fpa2bv lowering while its
     validated per-bit skolems remain.  Only bits from a complete coherent
     allocation are provenance; a lone or merely name-shaped variable is
     not. *)
  fun has_allocated_fp_bv_atom_in version packed registered target =
    let
      val definitions = fp_per_bit_definitions_in
        version packed registered
      val allocated = HOLset.addList (Term.empty_tmset,
        List.map (Lib.fst o boolSyntax.dest_eq) definitions)
    in
      not (List.null definitions) andalso
      #found (term_contains_measure
        (fn subterm => Term.is_var subterm andalso
          HOLset.member (allocated, subterm)) target)
    end

  fun has_allocated_fp_bv_atom (state : state) target =
    has_allocated_fp_bv_atom_in (#z3_version state)
      (fp_packed_vars state) (#var_set state) target

  fun require_bv_family function_name target =
    if has_word_atom target then ()
    else raise ERR function_name "goal is outside the bit-vector family"

  fun is_function_type ty =
    Lib.can Type.dom_rng ty

  fun has_array_atom tm =
    Lib.can (HolKernel.find_term (fn subtm =>
      combinSyntax.is_update_comb subtm orelse
      (Term.is_comb subtm andalso
       let val rator = Lib.fst (Term.dest_comb subtm)
       in
         (Term.is_var rator andalso is_function_type (Term.type_of rator))
         orelse combinSyntax.is_update_comb rator
       end) orelse
      (Term.is_var subtm andalso is_function_type (Term.type_of subtm)))) tm

  (* returns "|- l = r", provided 'l' and 'r' are conjunctions that can be
     obtained from each other using associativity, commutativity and
     idempotence of conjunction, and identity of "T" wrt. conjunction.

     If 'r' is "F", 'l' must either contain "F" as a conjunct, or 'l'
     must contain both a literal and its negation. *)
  fun rewrite_conj (l, r) =
    let
      val Tl = boolSyntax.mk_conj (boolSyntax.T, l)
      val Tr = boolSyntax.mk_conj (boolSyntax.T, r)
      val Tl_eq_Tr = Drule.CONJUNCTS_AC (Tl, Tr)
      val p = Term.mk_var ("p", Type.bool)
      val q = Term.mk_var ("q", Type.bool)
    in
      Thm.MP (Thm.INST [p |-> l, q |-> r] T_AND) Tl_eq_Tr
    end
    handle Feedback.HOL_ERR _ =>
      if Feq r then
        let
          val l_imp_F = Thm.DISCH l (Library.gen_contradiction (Thm.ASSUME l))
        in
          Drule.EQF_INTRO (Thm.NOT_INTRO l_imp_F)
        end
      else
        raise ERR "rewrite_conj" ""

  (* returns "|- l = r", provided 'l' and 'r' are disjunctions that can be
     obtained from each other using associativity, commutativity and
     idempotence of disjunction, and identity of "F" wrt. disjunction.

     If 'r' is "T", 'l' must contain "T" as a disjunct, or 'l' must contain
     both a literal and its negation. *)
  fun rewrite_disj (l, r) =
    let
      val Fl = boolSyntax.mk_disj (boolSyntax.F, l)
      val Fr = boolSyntax.mk_disj (boolSyntax.F, r)
      val Fl_eq_Fr = Drule.DISJUNCTS_AC (Fl, Fr)
      val p = Term.mk_var ("p", Type.bool)
      val q = Term.mk_var ("q", Type.bool)
    in
      Thm.MP (Thm.INST [p |-> l, q |-> r] F_OR) Fl_eq_Fr
    end
    handle Feedback.HOL_ERR _ =>
      if Teq r then
        Drule.EQT_INTRO (Library.gen_excluded_middle l)
      else
        raise ERR "rewrite_disj" ""

  (* |- r1 /\ ... /\ rn = ~(s1 \/ ... \/ sn)

     Note that q <=> p may be negated to p <=> ~q.  Also, p <=> ~q may
     be negated to p <=> q. *)
  fun rewrite_nnf (l, r) =
  let
    val disj = boolSyntax.dest_neg r
    val conj_ths = Drule.CONJUNCTS (Thm.ASSUME l)
    (* transform equivalences in 'l' into equivalences as they appear
       in 'disj' *)
    val conj_dict = List.foldl (fn (th, dict) => Redblackmap.insert
      (dict, Thm.concl th, th)) (Redblackmap.mkDict Term.compare) conj_ths
    val var_p = Term.mk_var ("p", Type.bool)
    val var_q = Term.mk_var ("q", Type.bool)
    (* we map over equivalences in 'disj', possibly obtaining the
       negation of each one by forward reasoning from a suitable
       theorem in 'conj_dict' *)
    val iff_ths = List.mapPartial (Lib.total (fn t =>
      let
        val (p, q) = boolSyntax.dest_eq t  (* may fail *)
        val neg_q = boolSyntax.mk_neg q  (* may fail (because of type) *)
      in
        let
          val th = Redblackmap.find (conj_dict, boolSyntax.mk_eq (p, neg_q))
        in
          (* l |- ~(p <=> q) *)
          Thm.MP (Thm.INST [var_p |-> p, var_q |-> q] NEG_IFF_2_1) th
        end
        handle Redblackmap.NotFound =>
          let
            val q = boolSyntax.dest_neg q  (* may fail *)
            val th = Redblackmap.find (conj_dict, boolSyntax.mk_eq (q, p))
          in
            (* l |- ~(p <=> ~q) *)
            Thm.MP (Thm.INST [var_p |-> p, var_q |-> q] NEG_IFF_1_1) th
          end
      end)) (boolSyntax.strip_disj disj)
    (* [l, disj] |- F *)
    val F_th = unit_resolution (Thm.ASSUME disj :: conj_ths @ iff_ths,
      boolSyntax.F)
    fun disjuncts dict (thmfun, concl) =
    let
      val (l, r) = boolSyntax.dest_disj concl  (* may fail *)
    in
      disjuncts (disjuncts dict (fn th => thmfun (Thm.DISJ1 th r), l))
        (fn th => thmfun (Thm.DISJ2 l th), r)
    end
    handle Feedback.HOL_ERR _ =>  (* 'concl' is not a disjunction *)
      let
        (* |- concl ==> disjunction *)
        val th = Thm.DISCH concl (thmfun (Thm.ASSUME concl))
        (* ~disjunction |- ~concl *)
        val th = Drule.UNDISCH (Drule.CONTRAPOS th)
        val th = Thm.MP (Thm.SPEC (boolSyntax.dest_neg concl) NOT_NOT_ELIM) th
          handle Feedback.HOL_ERR _ => th
        val t = Thm.concl th
        val dict = Redblackmap.insert (dict, t, th)
      in
        (* if 't' is a negated equivalence, we check whether it can be
           transformed into an equivalence that is present in 'l' *)
        let
          val (p, q) = boolSyntax.dest_eq (boolSyntax.dest_neg t) (* may fail *)
          val neg_q = boolSyntax.mk_neg q  (* may fail (because of type) *)
        in
          let
            val _ = Redblackmap.find (conj_dict, boolSyntax.mk_eq (p, neg_q))
            (* ~disjunction |- p <=> ~q *)
            val subst = [var_p |-> p, var_q |-> q]
            val th1 = Thm.MP (Thm.INST subst NEG_IFF_2_2) th
            val dict = Redblackmap.insert (dict, Thm.concl th1, th1)
          in
            let
              val q = boolSyntax.dest_neg q  (* may fail *)
              val _ = Redblackmap.find (conj_dict, boolSyntax.mk_eq (q, p))
              (* ~disjunction |- q <=> p *)
              val subst = [var_p |-> p, var_q |-> q]
              val th1 = Thm.MP (Thm.INST subst NEG_IFF_1_2) th
            in
              Redblackmap.insert (dict, Thm.concl th1, th1)
            end
            handle Redblackmap.NotFound => dict
                 | Feedback.HOL_ERR _ => dict
          end
          handle Redblackmap.NotFound =>
            (* p <=> ~q is not a conjunction in 'l', so we skip
               deriving it; but we possibly still need to derive
               q <=> p *)
            let
              val q = boolSyntax.dest_neg q  (* may fail *)
              val _ = Redblackmap.find (conj_dict, boolSyntax.mk_eq (q, p))
              (* ~disjunction |- q <=> p *)
              val subst = [var_p |-> p, var_q |-> q]
              val th1 = Thm.MP (Thm.INST subst NEG_IFF_1_2) th
            in
              Redblackmap.insert (dict, Thm.concl th1, th1)
            end
            handle Redblackmap.NotFound => dict
                 | Feedback.HOL_ERR _ => dict
        end
        handle Feedback.HOL_ERR _ =>  (* 't' is not an equivalence *)
          dict
      end  (* disjuncts *)
    val dict = disjuncts (Redblackmap.mkDict Term.compare) (Lib.I, disj)
    (* derive ``T`` (just in case ``T`` is a conjunct) *)
    val dict = Redblackmap.insert (dict, boolSyntax.T, boolTheory.TRUTH)
    (* proves a conjunction 'conj', provided each conjunct is proved
      in 'dict' *)
    fun prove_conj dict conj =
      Redblackmap.find (dict, conj)
      handle Redblackmap.NotFound =>
        let
          val (l, r) = boolSyntax.dest_conj conj
        in
          Thm.CONJ (prove_conj dict l) (prove_conj dict r)
        end
    val r_imp_l = Thm.DISCH r (prove_conj dict l)
    val l_imp_r = Thm.DISCH l (Thm.NOT_INTRO (Thm.DISCH disj F_th))
  in
    Drule.IMP_ANTISYM_RULE l_imp_r r_imp_l
  end

  (* returns |- ~MEM x [a; b; c] = x <> a /\ x <> b /\ x <> c; fails
     if not applied to a term of the form ``~MEM x [a; b; c]`` *)
  fun NOT_MEM_CONV tm =
  let
    val (x, list) = listSyntax.dest_mem (boolSyntax.dest_neg tm)
  in
    let
      val (h, t) = listSyntax.dest_cons list
      (* |- ~MEM x (h::t) = (x <> h) /\ ~MEM x t *)
      val th1 = Drule.ISPECL [x, h, t] NOT_MEM_CONS
      val (neq, notmem) = boolSyntax.dest_conj (boolSyntax.rhs
        (Thm.concl th1))
      (* |- ~MEM x t = rhs *)
      val th2 = NOT_MEM_CONV notmem
      (* |- (x <> h) /\ ~MEM x t = (x <> h) /\ rhs *)
      val th3 = Thm.AP_TERM (Term.mk_comb (boolSyntax.conjunction, neq)) th2
      (* |- ~MEM x (h::t) = (x <> h) /\ rhs *)
      val th4 = Thm.TRANS th1 th3
    in
      if Teq (boolSyntax.rhs (Thm.concl th2)) then
        Thm.TRANS th4 (Thm.SPEC neq AND_T)
      else
        th4
    end
    handle Feedback.HOL_ERR _ =>  (* 'list' is not a cons *)
      if listSyntax.is_nil list then
        (* |- ~MEM x [] = T *)
        Drule.ISPEC x NOT_MEM_NIL
      else
        raise ERR "NOT_MEM_CONV" ""
  end

  (* returns "|- ALL_DISTINCT [x; y; z] = (x <> y /\ x <> z) /\ y <>
     z" (note the parentheses); fails if not applied to a term of the
     form ``ALL_DISTINCT [x; y; z]`` *)
  fun ALL_DISTINCT_CONV tm =
  let
    val list = listSyntax.dest_all_distinct tm
  in
    let
      val (h, t) = listSyntax.dest_cons list
      (* |- ALL_DISTINCT (h::t) = ~MEM h t /\ ALL_DISTINCT t *)
      val th1 = Drule.ISPECL [h, t] ALL_DISTINCT_CONS
      val (notmem, alldistinct) = boolSyntax.dest_conj
        (boolSyntax.rhs (Thm.concl th1))
      (* |- ~MEM h t = something *)
      val th2 = NOT_MEM_CONV notmem
      val something = boolSyntax.rhs (Thm.concl th2)
      (* |- ALL_DISTINCT t = rhs *)
      val th3 = ALL_DISTINCT_CONV alldistinct
      val rhs = boolSyntax.rhs (Thm.concl th3)
      val var_names = ["p", "q", "r", "s"]
      val redexes = List.map (fn v => Term.mk_var (v, Type.bool)) var_names
      val residues = [notmem, something, alldistinct, rhs]
      val substs = List.map Lib.|-> (ListPair.zip (redexes, residues))
      val th4 = Thm.INST substs CONJ_CONG
      (* |- ~MEM h t /\ ALL_DISTINCT t = something /\ rhs *)
      val th5 = Thm.MP (Thm.MP th4 th2) th3
      (* |- ALL_DISTINCT (h::t) = something /\ rhs *)
      val th6 = Thm.TRANS th1 th5
    in
      if Teq rhs then Thm.TRANS th6 (Thm.SPEC something AND_T)
      else th6
    end
    handle Feedback.HOL_ERR _ =>  (* 'list' is not a cons *)
      (* |- ALL_DISTINCT [] = T *)
      Thm.INST_TYPE [Type.alpha |-> listSyntax.dest_nil list]
        ALL_DISTINCT_NIL
  end

  (* returns |- (x = y) = (y = x), provided ``y = x`` is LESS than ``x
     = y`` wrt. Term.compare; fails if applied to a term that is not
     an equation; may raise Conv.UNCHANGED *)
  fun REORIENT_SYM_CONV tm =
  let
    val tm' = boolSyntax.mk_eq (Lib.swap (boolSyntax.dest_eq tm))
  in
    if Term.compare (tm', tm) = LESS then
      Conv.SYM_CONV tm
    else
      raise Conv.UNCHANGED
  end

  (* returns |- ALL_DISTINCT ... /\ T = ... *)
  fun rewrite_all_distinct (l, r) =
  let
    fun ALL_DISTINCT_AND_T_CONV t =
      ALL_DISTINCT_CONV t
        handle Feedback.HOL_ERR _ =>
          let
            val all_distinct = Lib.fst (boolSyntax.dest_conj t)
            val all_distinct_th = ALL_DISTINCT_CONV all_distinct
          in
            Thm.TRANS (Thm.SPEC all_distinct AND_T) all_distinct_th
          end
    val REORIENT_CONV = Conv.ONCE_DEPTH_CONV REORIENT_SYM_CONV
    (* since ALL_DISTINCT may be present in both 'l' and 'r', we
       normalize both 'l' and 'r' *)
    val l_eq_l' = Conv.THENC (ALL_DISTINCT_AND_T_CONV, REORIENT_CONV) l
    val r_eq_r' = Conv.THENC (fn t => ALL_DISTINCT_AND_T_CONV t
      handle Feedback.HOL_ERR _ => raise Conv.UNCHANGED, REORIENT_CONV) r
      handle Conv.UNCHANGED => Thm.REFL r
    (* get rid of parentheses *)
    val l'_eq_r' = Drule.CONJUNCTS_AC (boolSyntax.rhs (Thm.concl l_eq_l'),
      boolSyntax.rhs (Thm.concl r_eq_r'))
  in
    Thm.TRANS (Thm.TRANS l_eq_l' l'_eq_r') (Thm.SYM r_eq_r')
  end

  (* Returns a proof of `t` given a list of theorems as inputs. It relies on
     `metisLib.METIS_TAC` to find a proof. The returned theorem will have as
     hypotheses all the hypotheses of all the input theorems. *)
  fun metis_prove (thms, t) =
  let
    (* Gather all the hypotheses of all theorems together into a set of
       assumptions *)
    fun join_fn (thm, asm_set) = HOLset.union (asm_set, Thm.hypset thm)
    val asms = List.foldl join_fn Term.empty_tmset thms
  in
    Tactical.TAC_PROOF ((HOLset.listItems asms, t), metisLib.METIS_TAC thms)
  end

  val nnf_rewrites = [
    boolTheory.DE_MORGAN_THM,
    boolTheory.NOT_IMP,
    boolTheory.IMP_DISJ_THM,
    boolTheory.NOT_FORALL_THM,
    boolTheory.NOT_EXISTS_THM,
    boolTheory.NOT_CLAUSES,
    boolTheory.AND_CLAUSES,
    boolTheory.OR_CLAUSES,
    boolTheory.IMP_CLAUSES,
    boolTheory.EQ_CLAUSES
  ]

  fun nnf_structural_prove (thms, t) =
  let
    fun join_fn (thm, asm_set) = HOLset.union (asm_set, Thm.hypset thm)
    val asms = List.foldl join_fn Term.empty_tmset thms
    fun is_refl_eq thm =
      let val (l, r) = boolSyntax.dest_eq (Thm.concl thm)
      in l ~~ r end
      handle Feedback.HOL_ERR _ => false
    val rewrite_thms = List.filter (not o is_refl_eq) thms
    fun oriented_premise thm =
      if Thm.concl thm ~~ t then
        thm
      else
        let
          val (tl, tr) = boolSyntax.dest_eq t
          val (cl, cr) = boolSyntax.dest_eq (Thm.concl thm)
        in
          if tl ~~ cr andalso tr ~~ cl then Thm.SYM thm
          else raise ERR "nnf_structural_prove" "premise does not match"
        end
    fun reflexive_target () =
      let val (l, r) = boolSyntax.dest_eq t
      in Thm.ALPHA l r end
  in
    Lib.tryfind oriented_premise thms
    handle Feedback.HOL_ERR _ =>
    reflexive_target ()
    handle Feedback.HOL_ERR _ =>
    SmtResource.with_resource_step_time "Skeleton" "z3-nnf-taut"
      (fn target =>
        let
          val maximum = SmtResource.max_term_nodes_for "Skeleton"
          val observed = SmtResource.dag_nodes_up_to maximum target
          val _ = SmtResource.check_dag_size_with_limit
            "Skeleton" "z3-nnf-taut" maximum observed
        in
          Tactical.TAC_PROOF ((HOLset.listItems asms, target),
            PURE_REWRITE_TAC (rewrite_thms @ nnf_rewrites) THEN
            bossLib.SIMP_TAC bossLib.bool_ss
              (rewrite_thms @ nnf_rewrites) THEN
            tautLib.TAUT_TAC)
        end) t
  end

  fun nnf_prove (thms, t) =
    profile "nnf[structural]" nnf_structural_prove (thms, t)
    handle Feedback.HOL_ERR _ =>
      profile "nnf[metis-fallback]" metis_prove (thms, t)

  (* The terms the proofs below name are built, not parsed: a constant a
     client theory exports must not capture them. *)
  local
    val a = Term.mk_var ("a", intSyntax.int_ty)
    val b = Term.mk_var ("b", intSyntax.int_ty)
    val n = Term.mk_var ("n", intSyntax.int_ty)
  in
  val INT_LE_RMUL_EXP = Library.prove(
    ``!a b n:int. 0 <= n ==> a <= b ==> a * n <= b * n``,
    (* GEN_TAC renames a bound variable away from a constant of its name,
       so fix the names before the steps that use them. *)
    MAP_EVERY X_GEN_TAC [a, b, n] THEN
    REPEAT STRIP_TAC THEN
    bossLib.tmCases_on (boolSyntax.mk_eq (n, intSyntax.zero_tm)) [] THENL [
      bossLib.ASM_SIMP_TAC intLib.int_ss [],
      SUBGOAL_THEN (intSyntax.mk_less (intSyntax.zero_tm, n)) ASSUME_TAC THENL
        [intLib.ARITH_TAC, ALL_TAC] THEN
      bossLib.tmCases_on (boolSyntax.mk_eq (a, b)) [] THENL [
        bossLib.ASM_SIMP_TAC intLib.int_ss [],
        SUBGOAL_THEN (intSyntax.mk_less (a, b)) ASSUME_TAC THENL
          [intLib.ARITH_TAC, ALL_TAC] THEN
        Tactic.MP_TAC (Drule.SPECL [a, b, n]
          intExtensionTheory.INT_LT_RMUL_EXP) THEN
        intLib.ARITH_TAC
      ]
    ])
  end

  val INT_LE_LMUL_EXP = Library.prove(
    ``!a b n:int. 0 <= n ==> a <= b ==> n * a <= n * b``,
    metisLib.METIS_TAC [INT_LE_RMUL_EXP, integerTheory.INT_MUL_COMM])

  local
    val x1 = Term.mk_var ("x1", intSyntax.int_ty)
    val x2 = Term.mk_var ("x2", intSyntax.int_ty)
    val y1 = Term.mk_var ("y1", intSyntax.int_ty)
    val y2 = Term.mk_var ("y2", intSyntax.int_ty)
    fun product_le ((p, q), (r, s)) =
      intSyntax.mk_leq (intSyntax.mk_mult (p, q), intSyntax.mk_mult (r, s))
  in
  val INT_LE_MUL2 = Library.prove(
    ``!x1 x2 y1 y2:int.
        0 <= x1 /\ 0 <= y1 /\ x1 <= x2 /\ y1 <= y2 ==>
        x1 * y1 <= x2 * y2``,
    MAP_EVERY X_GEN_TAC [x1, x2, y1, y2] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (product_le ((x1, y1), (x2, y1))) ASSUME_TAC THENL
      [metisLib.METIS_TAC [INT_LE_RMUL_EXP], ALL_TAC] THEN
    SUBGOAL_THEN (product_le ((x2, y1), (x2, y2))) ASSUME_TAC THENL
      [metisLib.METIS_TAC [INT_LE_LMUL_EXP, integerTheory.INT_LE_TRANS],
       ALL_TAC] THEN
    metisLib.METIS_TAC [integerTheory.INT_LE_TRANS])
  end

  fun int_product_bound_tac (asl, w) =
  let
    fun dest_not_leq_mult tm =
      let
        val (_, product) = intSyntax.dest_leq (boolSyntax.dest_neg tm)
        val (x, y) = intSyntax.dest_mult product
      in
        (x, y)
      end
    fun dest_lower_bound tm = SOME (intSyntax.dest_leq tm)
      handle Feedback.HOL_ERR _ => NONE
    fun lower_bounds_for x =
      List.mapPartial (fn tm =>
        case dest_lower_bound tm of
          SOME (lower, upper) => if upper ~~ x then SOME lower else NONE
        | NONE => NONE) asl
    fun candidate_tacs (x, y) =
      List.concat (map (fn x_lower =>
        map (fn y_lower =>
          Tactic.MP_TAC (Drule.SPECL [x_lower, x, y_lower, y] INT_LE_MUL2) THEN
          bossLib.FULL_SIMP_TAC
            (bossLib.arith_ss ++ intSimps.INT_RWTS_ss ++
             intSimps.INT_ARITH_ss) [] THEN
          intLib.ARITH_TAC) (lower_bounds_for y)) (lower_bounds_for x))
    val tacs = List.concat (List.mapPartial (fn tm =>
      SOME (candidate_tacs (dest_not_leq_mult tm))
      handle Feedback.HOL_ERR _ => NONE) asl)
    fun first [] _ = raise ERR "int_product_bound_tac"
      ("failed: " ^ Hol_pp.term_to_string w)
      | first (tac :: tacs) goal =
          tac goal handle Feedback.HOL_ERR _ => first tacs goal
  in
    first tacs (asl, w)
  end

  fun int_product_prove t =
    Tactical.TAC_PROOF (([], t),
      PURE_REWRITE_TAC [integerTheory.INT_GE] THEN
      (metisLib.METIS_TAC
         [integerTheory.INT_LE_MUL, integerTheory.INT_LE_SQUARE, INT_LE_MUL2]
       ORELSE
       REPEAT STRIP_TAC THEN int_product_bound_tac))

  local
    val x = Term.mk_var ("x", realSyntax.real_ty)
    val y = Term.mk_var ("y", realSyntax.real_ty)
    val zero = realSyntax.zero_tm
  in
  val REAL_ZERO_FACTOR_NONNEG = Library.prove(
    ``!x:real. !y:real. x <= 0 ==> x >= 0 ==> 0 <= x * y``,
    MAP_EVERY X_GEN_TAC [x, y] THEN
    Tactical.REPEAT STRIP_TAC THEN
    (* x >= 0 ==> x <= 0 ==> x = 0 *)
    Tactic.MP_TAC
      (RealField.REAL_ARITH
        (boolSyntax.mk_imp (realSyntax.mk_geq (x, zero),
           boolSyntax.mk_imp (realSyntax.mk_leq (x, zero),
                              boolSyntax.mk_eq (x, zero))))) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_TAC THEN
    ASM_REWRITE_TAC
      [realTheory.REAL_MUL_LZERO, realTheory.REAL_LE_REFL])
  end

  val REAL_ZERO_FACTOR_NONNEG_CLAUSE = Library.prove(
    ``!x:real. !y:real. 0 <= x * y \/ ~(x <= 0) \/ ~(x >= 0)``,
    metisLib.METIS_TAC [REAL_ZERO_FACTOR_NONNEG])

  fun real_zero_factor_clause_prove t =
  let
    fun strip_disj tm =
      let val (l, r) = boolSyntax.dest_disj tm
      in l :: strip_disj r end
      handle Feedback.HOL_ERR _ => [tm]

    fun is_real_zero tm = tm ~~ realSyntax.zero_tm

    fun dest_nonneg_product lit =
      let
        val (l, r) = realSyntax.dest_leq lit
      in
        if is_real_zero l then realSyntax.dest_mult r
        else raise ERR "dest_nonneg_product" ""
      end
      handle Feedback.HOL_ERR _ =>
      let
        val (l, r) = realSyntax.dest_geq lit
      in
        if is_real_zero r then realSyntax.dest_mult l
        else raise ERR "dest_nonneg_product" ""
      end

    fun dest_neg_le_zero lit =
      let
        val (l, r) = realSyntax.dest_leq (boolSyntax.dest_neg lit)
      in
        if is_real_zero r then SOME l else NONE
      end
      handle Feedback.HOL_ERR _ =>
      let
        val (l, r) = realSyntax.dest_geq (boolSyntax.dest_neg lit)
      in
        if is_real_zero l then SOME r else NONE
      end
      handle Feedback.HOL_ERR _ => NONE

    fun dest_neg_ge_zero lit =
      let
        val (l, r) = realSyntax.dest_geq (boolSyntax.dest_neg lit)
      in
        if is_real_zero r then SOME l else NONE
      end
      handle Feedback.HOL_ERR _ =>
      let
        val (l, r) = realSyntax.dest_leq (boolSyntax.dest_neg lit)
      in
        if is_real_zero l then SOME r else NONE
      end
      handle Feedback.HOL_ERR _ => NONE

    val lits = strip_disj t
    val le_zero_vars = List.mapPartial dest_neg_le_zero lits
    val ge_zero_vars = List.mapPartial dest_neg_ge_zero lits

    fun find_bound_pair x =
      List.exists (fn y => x ~~ y) le_zero_vars andalso
      List.exists (fn y => x ~~ y) ge_zero_vars

    fun prove_for_factor (x, y) =
      if find_bound_pair x then
        let
          val thm = Drule.SPECL [x, y] REAL_ZERO_FACTOR_NONNEG_CLAUSE
        in
          metis_prove ([thm, realTheory.real_ge, realTheory.REAL_MUL_COMM], t)
        end
      else
        raise ERR "real_zero_factor_clause_prove" ""

    fun prove_from_lit lit =
      let
        val (l, r) = dest_nonneg_product lit
      in
        prove_for_factor (l, r)
        handle Feedback.HOL_ERR _ => prove_for_factor (r, l)
      end
  in
    Lib.tryfind prove_from_lit lits
  end

  val ediv_tm = Term.prim_mk_const {Thy = "integer", Name = "ediv"}
  val emod_tm = Term.prim_mk_const {Thy = "integer", Name = "emod"}

  (* Collect divisors from the whole integer div/mod family.  Canonical
     totalization may expose raw [ediv]/[emod], so this is deliberately keyed
     by operation identity and arity rather than by a recorded clause shape. *)
  fun ediv_emod_divisors target =
    let
      fun divisor term =
        case boolSyntax.strip_comb term of
          (head, [_, denominator]) =>
            if List.exists (Term.same_const head)
                 [ediv_tm, emod_tm,
                  SmtReplayCanon.smt_ediv_total_tm,
                  SmtReplayCanon.smt_emod_total_tm] then
              SOME denominator
            else NONE
        | _ => NONE
      fun add (denominator, denominators) =
        if List.exists (Term.aconv denominator) denominators then denominators
        else denominator :: denominators
    in
      List.foldl add []
        (List.mapPartial divisor (Library.subterms target))
    end

  (* Built, not parsed: a constant a client theory exports must not
     capture x, y or k. *)
  local
    open boolSyntax
    val x = Term.mk_var ("x", realSyntax.real_ty)
    val y = Term.mk_var ("y", realSyntax.real_ty)
    val k = Term.mk_var ("k", realSyntax.real_ty)
    val y_is_zero = mk_eq (y, realSyntax.zero_tm)
    val x_rdiv_y =
      Term.list_mk_comb
        (Term.prim_mk_const {Thy = "HolSmt", Name = "smt_rdiv"}, [x, y])
  in
  (* y = 0 \/ x = y * smt_rdiv x y *)
  val SMT_RDIV_CANCEL_CLAUSE = Library.prove(
    mk_disj (y_is_zero, mk_eq (x, realSyntax.mk_mult (y, x_rdiv_y))),
    Tactic.ASM_CASES_TAC y_is_zero THENL [
      ASM_REWRITE_TAC [],
      bossLib.ASM_SIMP_TAC (bossLib.srw_ss())
        [HolSmtTheory.smt_rdiv_eq_div, realTheory.REAL_DIV_LMUL]
    ])

  (* smt_rdiv x y = k ==> y = 0 \/ y * k = x *)
  val SMT_RDIV_INTRO_CANCEL_CLAUSE = Library.prove(
    mk_imp (mk_eq (x_rdiv_y, k),
            mk_disj (y_is_zero, mk_eq (realSyntax.mk_mult (y, k), x))),
    bossLib.METIS_TAC [SMT_RDIV_CANCEL_CLAUSE])
  end

  val ground_subterm_eval_max_nodes = 4096
  val ground_subterm_eval_max_calls = 8
  val ground_subterm_eval_steps_per_call = 100000

  (* One bounded pass over an arithmetic obligation.  At an open node the
     conversion visits each immediate child once.  At a closed compound it
     spends one EVAL budget: a changed compound is selected and its children
     are not visited; an unchanged compound is not selected and the pass
     continues once through its children.  Thus every node is attempted at
     most once and maximal closed compounds changed by bounded EVAL are never
     revisited.  The 4096-node preflight and eight-attempt guard are hard:
     exceeding either raises without returning a rewrite.  Each EVAL call
     instead has a soft 100000-step stopper.  Reaching it may return a
     partially changed kernel theorem, and the conversion accepts that proved
     partial rewrite.  Wholly unchanged inputs raise without manufacturing a
     rewrite. *)
  fun ground_subterm_eval_conv target =
    let
      val nodes = SmtResource.term_nodes_up_to
        ground_subterm_eval_max_nodes target
      val _ = nodes <= ground_subterm_eval_max_nodes orelse
        raise ERR "ground_subterm_eval_conv"
          ("resource limit: input exceeds " ^
           Int.toString ground_subterm_eval_max_nodes ^
           " syntax nodes")
      val calls = ref 0
      fun eval_closed tm =
        let
          val _ = !calls < ground_subterm_eval_max_calls orelse
            raise ERR "ground_subterm_eval_conv"
              ("resource limit: more than " ^
               Int.toString ground_subterm_eval_max_calls ^
               " closed-compound attempts")
          val _ = calls := !calls + 1
          val th = bossLib.EVALn ground_subterm_eval_steps_per_call tm
          val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl th)
        in
          if lhs ~~ rhs then raise Conv.UNCHANGED else th
        end
      fun one_pass tm =
        if List.null (Term.free_vars tm) then
          if Term.is_comb tm orelse Term.is_abs tm then
            (eval_closed tm
             handle Conv.UNCHANGED =>
               descend tm)
          else raise Conv.UNCHANGED
        else
          descend tm
      and descend tm =
        if Term.is_comb tm then
          let
            val (rator, rand) = Term.dest_comb tm
            val rator_thm = SOME (one_pass rator)
              handle Conv.UNCHANGED => NONE
            val rand_thm = SOME (one_pass rand)
              handle Conv.UNCHANGED => NONE
          in
            case (rator_thm, rand_thm) of
              (SOME rator_thm, SOME rand_thm) =>
                Thm.MK_COMB (rator_thm, rand_thm)
            | (SOME rator_thm, NONE) => Thm.AP_THM rator_thm rand
            | (NONE, SOME rand_thm) => Thm.AP_TERM rator rand_thm
            | (NONE, NONE) => raise Conv.UNCHANGED
          end
        else if Term.is_abs tm then
          let
            val (binder, body) = Term.dest_abs tm
          in
            Thm.ABS binder (one_pass body)
          end
        else raise Conv.UNCHANGED
    in
      Conv.CHANGED_CONV one_pass target
    end

  fun profiled_ground_subterm_eval_conv target =
    profile "arith-linear(5)(ground-subterm-eval)"
      ground_subterm_eval_conv target

  (* Returns a proof of `t` using arithmetic decision procedures. This function
     is used by both `z3_th_lemma_arith` and `z3_rewrite`. *)
  fun arith_prove t =
    (* E1(a): exact instantiation decides the rdiv intro-cancel clause. *)
    profile "arith(1)(rdiv-intro-cancel)"
      (exact_inst SMT_RDIV_INTRO_CANCEL_CLAUSE) t
    handle Feedback.HOL_ERR _ =>
    (* E1(a): exact instantiation decides the rdiv cancel clause. *)
    profile "arith(2)(rdiv-cancel)" (exact_inst SMT_RDIV_CANCEL_CLAUSE) t
    handle Feedback.HOL_ERR _ =>
    (* E1(a): proved rdiv normalization ends in linear real arithmetic. *)
    profile "arith(3)(rdiv-normalize)" arith_prove_smt_rdiv t
    handle Feedback.HOL_ERR _ =>
    (* E1(a): the nested procedure decides linear int/real arithmetic. *)
    profile "arith(4)(linear)" arith_prove_linear t
    handle Feedback.HOL_ERR _ =>
    (* E1(b): div/mod replay is general with a loud two-divisor boundary. *)
    profile "arith(5)(ediv-emod)" arith_prove_ediv_emod t
    handle Feedback.HOL_ERR _ =>
    (* E1(b): this handles general matched nonlinear integer products. *)
    profile "arith(6)(integer-product-bounds)" int_product_prove t
    handle Feedback.HOL_ERR _ =>
    (* E1(b): this handles the real zero-factor clause family. *)
    profile "arith(7)(real-zero-factor)" real_zero_factor_clause_prove t
    handle Feedback.HOL_ERR _ =>
      (* nonlinear fallback: only after linear tactics fail, to avoid
         expensive SOS certificate search on goals linear tactics handle *)
      if Library.is_nonlinear t andalso
         not (Library.contains_nonpolynomial_arithmetic t) then
        (* E1(b): the general NLA procedure fails loudly at its boundary. *)
        profile "arith(8)(nla)" Library.nla_prove t
      else raise ERR "arith_prove" (Hol_pp.term_to_string t)

  and arith_prove_smt_rdiv t =
    let
      val t_eq_t' =
        simpLib.SIMP_CONV (bossLib.srw_ss())
          [HolSmtTheory.smt_rdiv_eq_div] t
        handle Conv.UNCHANGED => Thm.REFL t
      val t' = boolSyntax.rhs (Thm.concl t_eq_t')
    in
      if Term.aconv t t' then
        raise ERR "arith_prove_smt_rdiv" "no concrete division normalization"
      else
        Thm.EQ_MP (Thm.SYM t_eq_t') (arith_prove_linear t')
    end

  and arith_prove_ediv_emod t =
    let
      (* Unfold totalized div/mod before the shared alias canonicalizer: its
         canonical emod spelling is an ediv polynomial, while Z3 conclusions
         can compare a totalized operation with the corresponding raw one.
         Keeping both raw operations aligned after the proved zero/nonzero
         definition split lets the arithmetic ladder handle any dividend. *)
      val unfold_total_conv = Rewrite.PURE_REWRITE_CONV
        [HolSmtTheory.smt_ediv_total_def,
         HolSmtTheory.smt_emod_total_def]
      val totalization = unfold_total_conv t
        handle Conv.UNCHANGED => Thm.REFL t
      val unfolded = boolSyntax.rhs (Thm.concl totalization)
      val aliases = SmtReplayCanon.cpc_term_canon_conv unfolded
      val normalization = Thm.TRANS totalization aliases
      val normalized = boolSyntax.rhs (Thm.concl normalization)
      val divisors = ediv_emod_divisors normalized
      val _ = not (List.null divisors) orelse
        raise ERR "arith_prove_ediv_emod" "no integer div/mod operation"
      (* Three sign branches are complete for each divisor but multiply
         across unrelated divisors.  This rung is the bounded two-divisor
         fragment; larger formulas fail closed and continue down the replay
         ladder instead of starting exponential case expansion.  Dividend
         and denominator expressions themselves remain unrestricted. *)
      val _ = List.length divisors <= 2 orelse
        raise ERR "arith_prove_ediv_emod"
          "outside bounded two-divisor integer div/mod arithmetic"
      val simplify = bossLib.ASM_SIMP_TAC intLib.int_ss
        [integerTheory.EDIV_DEF, integerTheory.EMOD_DEF,
         integerTheory.INT_ABS, integerTheory.INT_DIV_0,
         integerTheory.INT_MOD0]
      fun finish () =
        Tactical.TRY intLib.ARITH_TAC
        THEN simplify
        THEN Tactical.TRY intLib.ARITH_TAC
      fun split [] = finish ()
        | split (denominator :: rest) =
            let
              val zero = boolSyntax.mk_eq
                (denominator, intSyntax.zero_tm)
              val positive = intSyntax.mk_less
                (intSyntax.zero_tm, denominator)
              val negative = intSyntax.mk_less
                (denominator, intSyntax.zero_tm)
            in
              (* Split zero first so both sign branches retain the explicit
                 nonzero fact needed by INT_DIV_0 and INT_MOD0. *)
              Tactic.ASM_CASES_TAC zero THENL
                [Tactical.TRY intLib.ARITH_TAC THEN split rest,
                 Tactic.ASM_CASES_TAC positive THENL
                   [Tactical.TRY intLib.ARITH_TAC THEN split rest,
                    SUBGOAL_THEN negative ASSUME_TAC THENL
                      [intLib.ARITH_TAC,
                       Tactical.TRY intLib.ARITH_TAC THEN split rest]]]
            end
      val proof = Tactical.TAC_PROOF (([], normalized), split divisors)
    in
      Thm.EQ_MP (Thm.SYM normalization) proof
    end

  and arith_prove_linear t =
    let
      fun arith_tactic rung (goal as (_, term)) =
        if term_contains_real_ty term then
          profile ("arith-linear(" ^ rung ^ ")(real)")
            RealField.REAL_ARITH_TAC goal
        else
          profile ("arith-linear(" ^ rung ^ ")(int)") intLib.ARITH_TAC goal
      val TRY = Tactical.TRY
    in
      Tactical.TAC_PROOF (([], t),
        (* E1(a): proved unfolding normalizes the integer div/mod syntax. *)
        (* rewrite the `ediv` and `emod` symbols so that the arithmetic
           decision procedures can solve terms containing these functions *)
        profile "arith-linear(1)(unfold-div-mod)"
          (PURE_REWRITE_TAC[integerTheory.EDIV_DEF, integerTheory.EMOD_DEF])
        (* the next rewrites are a workaround for this issue:
           https://github.com/HOL-Theorem-Prover/HOL/issues/1207 *)
        (* E1(a): proved alias rewriting preserves the linear fragment. *)
        >> profile "arith-linear(2)(normalize-aliases)"
          (PURE_REWRITE_TAC
            [integerTheory.INT_ABS, integerTheory.NUM_OF_INT])
        (* E1(a): ARITH decides the normalized linear int/real fragment. *)
        >> TRY (arith_tactic "3")
        (* E1(a): the arithmetic simpsets decide polynomial normalization. *)
        >> profile "arith-linear(4)(polynomial-normalize)"
          (bossLib.RW_TAC
            (bossLib.arith_ss ++ intSimps.INT_RWTS_ss ++
             intSimps.INT_ARITH_ss ++ realSimps.REAL_ARITH_ss)
            [Conv.GSYM integerTheory.INT_NEG_MINUS1])
        (* E1(a): bounded evaluation decides closed arithmetic subterms. *)
        >> TRY (Tactic.CONV_TAC profiled_ground_subterm_eval_conv)
        (* E1(a): the final ARITH pass decides the remaining linear goal. *)
        >> TRY (arith_tactic "6"))
    end

  (***************************************************************************)
  (* implementation of Z3's inference rules                                  *)
  (***************************************************************************)

  (* The Z3 documentation is rather outdated (as of version 2.11) and
     imprecise with respect to the semantics of Z3's inference rules.
     Ultimately, the most reliable way to determine the semantics is
     by observation: I applied Z3 to a large collection of SMT-LIB
     benchmarks, and from the resulting proofs I inferred what each
     inference rule does.  Therefore the implementation below may not
     cover rare corner cases that were not exercised by any benchmark
     in the collection. *)

  fun z3_and_elim (state, thm, t) =
    (state, Library.conj_elim (thm, t))

  (* SMT's n-ary [distinct] and width-annotated word literals can parse
     back with different HOL wrappers.  Normalize only these proved
     encoding identities and Boolean units, never arbitrary consequences
     of an assertion.  In particular, do not solve the asserted formula. *)
  val assertion_unit_rewrites =
    List.take (Drule.CONJUNCTS (Drule.SPEC_ALL boolTheory.AND_CLAUSES), 2) @
    List.take (List.drop
      (Drule.CONJUNCTS (Drule.SPEC_ALL boolTheory.OR_CLAUSES), 2), 2)

  fun assertion_word_literal_conv target =
    if wordsSyntax.is_w2w target andalso
       wordsSyntax.is_n2w (Lib.snd (Term.dest_comb target)) then
      wordsLib.WORD_EVAL_CONV target
    else raise ERR "assertion_word_literal_conv" "not a literal word cast"

  fun assertion_encoding_conv target =
    Conv.QCONV (Conv.DEPTH_CONV (Conv.FIRST_CONV
      (ALL_DISTINCT_CONV :: assertion_word_literal_conv ::
       List.map Conv.REWR_CONV
         (wordsTheory.w2w_id :: assertion_unit_rewrites)))) target

  fun z3_asserted (state : state, t) =
  let
    val allowed = HOLset.listItems (#allowed_asserted_hyps state)
    fun reject () =
      raise ERR "z3_asserted"
        (asserted_membership_diagnostic ^
         ": proof asserted a term outside {~goal} U assumptions; term=" ^
         Library.term_to_string t)
    fun regroup () =
      let
        fun source theorem =
          Drule.CONJUNCTS
            (Thm.EQ_MP (assertion_encoding_conv (Thm.concl theorem))
              theorem)
        val sources = List.concat (List.map (source o Thm.ASSUME) allowed)
        val conversion = assertion_encoding_conv t
        fun derive target =
          case List.find (Term.aconv target o Thm.concl) sources of
            SOME theorem => theorem
          | NONE =>
              if Teq target then boolTheory.TRUTH
              else
                case Lib.total boolSyntax.dest_conj target of
                  SOME (left, right) => Thm.CONJ (derive left) (derive right)
                | NONE => reject ()
      in
        Thm.EQ_MP (Thm.SYM conversion)
          (derive (boolSyntax.rhs (Thm.concl conversion)))
      end
    (* ASSUME is applied only to original translation inputs.  Z3 may merge
       assertions, reassociate them, or project an input conjunction; all
       such nodes retain the original hypotheses through kernel CONJ rules. *)
    val theorem =
      if List.exists (Term.aconv t) allowed then Thm.ASSUME t
      else regroup ()
    val state = List.foldl
      (fn (hypothesis, state) => state_assert state hypothesis)
      state (Thm.hyp theorem)
  in
    (state, theorem)
  end

  fun z3_commutativity (state, t) =
  let
    val (x, y) = boolSyntax.dest_eq (boolSyntax.lhs t)
    val xy = boolSyntax.mk_eq (x, y)
    val yx = boolSyntax.mk_eq (y, x)
    (* Specializing EQ_SYM_EQ traverses the unfolded arguments.  Derive its
       instance from kernel symmetry while retaining their DAG sharing. *)
    val forward = Thm.DISCH xy (Thm.SYM (Thm.ASSUME xy))
    val backward = Thm.DISCH yx (Thm.SYM (Thm.ASSUME yx))
  in
    (state, Drule.IMP_ANTISYM_RULE forward backward)
  end

  (* Instances of Tseitin-style propositional tautologies:
     (or (not (and p q)) p)
     (or (not (and p q)) q)
     (or (and p q) (not p) (not q))
     (or (not (or p q)) p q)
     (or (or p q) (not p))
     (or (or p q) (not q))
     (or (not (iff p q)) (not p) q)
     (or (not (iff p q)) p (not q))
     (or (iff p q) (not p) (not q))
     (or (iff p q) p q)
     (or (not (ite a b c)) (not a) b)
     (or (not (ite a b c)) a c)
     (or (ite a b c) (not a) (not b))
     (or (ite a b c) a (not c))
     (or (not (not a)) (not a))
     (or (not a) a)

     Also
     (or p (= x (ite p y x)))

     Also
     ~ALL_DISTINCT [x; y; z] \/ (x <> y /\ x <> z /\ y <> z)
     ~(ALL_DISTINCT [x; y; z] /\ T) \/ (x <> y /\ x <> z /\ y <> z)

     There is a complication: 't' may contain arbitarily many
     irrelevant (nested) conjuncts/disjuncts, i.e.,
     conjunction/disjunction in the above tautologies can be of
     arbitrary arity.

     For the most part, 'z3_def_axiom' could be implemented by a
     single call to TAUT_PROVE.  The (partly less general)
     implementation below, however, is considerably faster.
  *)
  val def_axiom_skeleton_context = SmtSkeletonProve.new_context []
  val def_axiom_skeleton_owners = Redblackmap.mkDict Term.compare

  type def_axiom_cache_entry =
    {target : term, theorem : Thm.thm}
  type def_axiom_cache_statistics =
    {enabled : bool,
     limit : int,
     lookups : int,
     hits : int,
     misses : int,
     inserts : int,
     capacity_refusals : int,
     failures : int,
     skeleton_attempts : int,
     entries : int,
     peak_entries : int}
  type def_axiom_cache_state =
    {limit : int,
     entries : (term, def_axiom_cache_entry) Redblackmap.dict ref,
     lookups : int ref,
     hits : int ref,
     misses : int ref,
     inserts : int ref,
     capacity_refusals : int ref,
     failures : int ref,
     skeleton_attempts : int ref,
     cardinality : int ref,
     peak_cardinality : int ref}

  val max_def_axiom_cache_entries = 2048
  val current_def_axiom_cache =
    ref (NONE : def_axiom_cache_state option)
  val def_axiom_cache_boundary_depth = ref 0
  val empty_def_axiom_cache_statistics : def_axiom_cache_statistics =
    {enabled = false, limit = max_def_axiom_cache_entries,
     lookups = 0, hits = 0, misses = 0, inserts = 0,
     capacity_refusals = 0, failures = 0, skeleton_attempts = 0,
     entries = 0, peak_entries = 0}
  val last_def_axiom_cache_statistics =
    ref empty_def_axiom_cache_statistics

  fun new_def_axiom_cache limit : def_axiom_cache_state =
    {limit = Int.max (0, limit),
     entries = ref (Redblackmap.mkDict Term.compare),
     lookups = ref 0,
     hits = ref 0,
     misses = ref 0,
     inserts = ref 0,
     capacity_refusals = ref 0,
     failures = ref 0,
     skeleton_attempts = ref 0,
     cardinality = ref 0,
     peak_cardinality = ref 0}

  fun def_axiom_cache_statistics enabled
      ({limit, lookups, hits, misses, inserts, capacity_refusals,
        failures, skeleton_attempts, cardinality, peak_cardinality, ...}
       : def_axiom_cache_state) : def_axiom_cache_statistics =
    {enabled = enabled, limit = limit, lookups = !lookups, hits = !hits,
     misses = !misses, inserts = !inserts,
     capacity_refusals = !capacity_refusals, failures = !failures,
     skeleton_attempts = !skeleton_attempts, entries = !cardinality,
     peak_entries = !peak_cardinality}

  fun def_axiom_cache_statistics_text
      ({enabled, limit, lookups, hits, misses, inserts, capacity_refusals,
        failures, skeleton_attempts, entries, peak_entries}
       : def_axiom_cache_statistics) =
    "def_cache_enabled=" ^ Bool.toString enabled ^
    " def_cache_limit=" ^ Int.toString limit ^
    " def_cache_lookups=" ^ Int.toString lookups ^
    " def_cache_hits=" ^ Int.toString hits ^
    " def_cache_misses=" ^ Int.toString misses ^
    " def_cache_inserts=" ^ Int.toString inserts ^
    " def_cache_capacity_refusals=" ^ Int.toString capacity_refusals ^
    " def_cache_failures=" ^ Int.toString failures ^
    " def_cache_skeleton_attempts=" ^ Int.toString skeleton_attempts ^
    " def_cache_entries=" ^ Int.toString entries ^
    " def_cache_peak_entries=" ^ Int.toString peak_entries

  fun current_def_axiom_cache_statistics () =
    case !current_def_axiom_cache of
      NONE => !last_def_axiom_cache_statistics
    | SOME cache => def_axiom_cache_statistics true cache

  fun current_def_axiom_cache_text () =
    def_axiom_cache_statistics_text
      (case !current_def_axiom_cache of
         NONE => empty_def_axiom_cache_statistics
       | SOME cache => def_axiom_cache_statistics true cache)

  fun detach_def_axiom_cache () =
    let
      val detached = !current_def_axiom_cache
      val _ = current_def_axiom_cache := NONE
      val _ = def_axiom_cache_boundary_depth := 0
    in
      detached
    end

  fun finish_def_axiom_cache NONE =
        (SmtResource.invoke_e0_diagnostic_hook
           "def-axiom-cache-summary";
         last_def_axiom_cache_statistics :=
           empty_def_axiom_cache_statistics)
    | finish_def_axiom_cache (SOME cache) =
        (SmtResource.invoke_e0_diagnostic_hook
           "def-axiom-cache-summary";
         last_def_axiom_cache_statistics :=
           def_axiom_cache_statistics true cache)

  fun with_def_axiom_cache_boundary_for limit replay input =
    if !def_axiom_cache_boundary_depth > 0 then replay input
    else
      let
        val enabled = not (Library.no_fastpath ())
        val fresh =
          if enabled then SOME (new_def_axiom_cache limit) else NONE
        val initial_statistics =
          (case fresh of
             SOME cache => def_axiom_cache_statistics true cache
           | NONE => empty_def_axiom_cache_statistics)
        val _ = last_def_axiom_cache_statistics := initial_statistics
        val _ = current_def_axiom_cache := fresh
        val _ = def_axiom_cache_boundary_depth := 1
        fun clear () =
          finish_def_axiom_cache (detach_def_axiom_cache ())
        val outcome = Exn.capture replay input
      in
        case outcome of
          Exn.Res result =>
            (case Exn.capture clear () of
               Exn.Res _ => result
             | Exn.Exn cleanup_exn =>
                 SmtResource.resolve_diagnostic_exception cleanup_exn
                   (fn () => ()) (fn _ => result))
        | Exn.Exn replay_exn =>
            SmtResource.resolve_diagnostic_exception replay_exn clear
              (fn original => raise original)
      end

  fun with_def_axiom_cache_boundary replay input =
    with_def_axiom_cache_boundary_for max_def_axiom_cache_entries
      replay input

  fun validate_def_axiom_cache_theorem target theorem =
    let
      val _ = HOLset.isEmpty (Thm.hypset theorem) orelse
        raise ERR "validate_def_axiom_cache_theorem"
          "cached def-axiom theorem has hypotheses"
      val _ = Library.check_oracle_tags "Z3_ProofReplay"
        "def-axiom-cache" theorem
      val _ = Term.aconv (Thm.concl theorem) target orelse
        raise ERR "validate_def_axiom_cache_theorem"
          "cached def-axiom conclusion is not alpha-equivalent"
    in
      theorem
    end

  fun reanchor_def_axiom_cache_theorem target theorem =
    let
      val theorem = validate_def_axiom_cache_theorem target theorem
      val exact = Thm.EQ_MP
        (Thm.ALPHA (Thm.concl theorem) target) theorem
      val _ = validate_def_axiom_cache_theorem target exact
      val _ = Portable.pointer_eq (Thm.concl exact, target) orelse
        raise ERR "reanchor_def_axiom_cache_theorem"
          "kernel alpha transport lost the current target occurrence"
    in
      exact
    end

  fun cache_terminal_exception exn =
    SmtResource.terminal_diagnostic_exception exn

  fun note_def_axiom_cache_failure cache exn =
    if cache_terminal_exception exn then raise exn
    else
      (#misses cache := !(#misses cache) + 1;
       #failures cache := !(#failures cache) + 1;
       NONE)

  fun probe_def_axiom_cache target =
    case !current_def_axiom_cache of
      NONE => NONE
    | SOME cache =>
        let
          val _ = #lookups cache := !(#lookups cache) + 1
          val result =
            case Redblackmap.peek (!(#entries cache), target) of
              NONE => NONE
            | SOME {target = saved, theorem} =>
                if Term.aconv saved target then
                  SOME (reanchor_def_axiom_cache_theorem target theorem)
                else raise ERR "probe_def_axiom_cache"
                  "Term.compare collision was not alpha-equivalent"
        in
          case result of
            SOME theorem =>
              (#hits cache := !(#hits cache) + 1; SOME theorem)
          | NONE => (#misses cache := !(#misses cache) + 1; NONE)
        end
        handle exn => note_def_axiom_cache_failure cache exn

  fun insert_def_axiom_cache target theorem =
    case !current_def_axiom_cache of
      NONE => ()
    | SOME cache =>
        let
          val theorem = validate_def_axiom_cache_theorem target theorem
          val cardinality = !(#cardinality cache)
          val entries = #entries cache
          val replacing = Option.isSome
            (Redblackmap.peek (!entries, target))
        in
          if cardinality >= #limit cache andalso not replacing then
            #capacity_refusals cache := !(#capacity_refusals cache) + 1
          else
            let
              val entry = {target = target, theorem = theorem}
              val next = cardinality + (if replacing then 0 else 1)
            in
              entries := Redblackmap.insert
                (!entries, target, entry);
              #inserts cache := !(#inserts cache) + 1;
              #cardinality cache := next;
              #peak_cardinality cache :=
                Int.max (!(#peak_cardinality cache), next)
            end
        end
        handle exn =>
          if cache_terminal_exception exn then raise exn
          else #failures cache := !(#failures cache) + 1

  fun note_def_axiom_skeleton_attempt () =
    case !current_def_axiom_cache of
      NONE => ()
    | SOME cache => #skeleton_attempts cache :=
        !(#skeleton_attempts cache) + 1

  type local_structure = unit -> string
  type proof_step_state =
    {id : int, rule : string, status : string,
     local_info : local_structure option}
  val active_proof_step = ref (NONE : proof_step_state option)
  val latest_proof_step = ref (NONE : proof_step_state option)
  val first_failed_proof_step = ref (NONE : proof_step_state option)
  val replay_completed_steps = ref 0

  datatype measured_route =
      MeasuredDefAxiom
    | MeasuredSkeletonCongruence

  type sampled_node_key = term * hol_type * int

  fun sampled_node_key_compare
      ((left, left_type, left_depth),
       (right, right_type, right_depth)) =
    case Term.compare (left, right) of
      EQUAL =>
        (case Type.compare (left_type, right_type) of
           EQUAL => Int.compare (left_depth, right_depth)
         | order => order)
    | order => order

  type route_measurement =
    {calls : int ref,
     targets : (term, int) Redblackmap.dict ref,
     target_calls_observed : int ref,
     targets_unique : int ref,
     target_repeats_lower_bound : int ref,
     target_max_multiplicity : int ref,
     targets_untracked : int ref,
     target_preflight_truncations : int ref,
     target_coverage_complete : bool ref,
     sampled_subnodes : (sampled_node_key, int) Redblackmap.dict ref,
     sampled_observations : int ref,
     sampled_unique : int ref,
     sampled_repeats_lower_bound : int ref,
     sampled_max_multiplicity : int ref,
     sampled_targets_truncated : int ref,
     sampled_scan_truncations : int ref,
     sampled_entry_truncations : int ref,
     sampled_errors : int ref,
     sampled_coverage_complete : bool ref}
  type skeleton_measurement =
    {successes : int ref,
     target_dag_nodes : int ref,
     skeleton_dag_nodes : int ref,
     normalized_dag_nodes : int ref,
     sat_dag_nodes : int ref,
     distinct_atoms : int ref,
     residual_atoms : int ref,
     graph_nodes : int ref,
     graph_observations : int ref,
     graph_edges : int ref,
     graph_type_nodes : int ref,
     graph_type_observations : int ref,
     graph_type_edges : int ref,
     graph_leaf_transport_nodes : int ref,
     graph_leaf_transport_time : Time.time ref,
     node_cache_hits : int ref,
     node_pointer_hits : int ref,
     node_reanchor_attempts : int ref,
     node_reanchor_successes : int ref,
     node_reanchor_fallbacks : int ref,
     node_reanchor_time : Time.time ref,
     sat_time : Time.time ref,
     total_time : Time.time ref}
  datatype pending_sat_shape =
      PendingSatShapeUntracked
    | PendingSatShapeHit
    | PendingSatShapeMiss of term
  type sat_shape_measurement =
    {cache_limit : int,
     calls : int ref,
     calls_observed : int ref,
     shapes : (term, int) Redblackmap.dict ref,
     unique : int ref,
     repeats : int ref,
     max_multiplicity : int ref,
     untracked : int ref,
     errors : int ref,
     coverage_complete : bool ref,
     cache_entries : (term, unit) Redblackmap.dict ref,
     cache_lookups : int ref,
     cache_hits : int ref,
     cache_inserts : int ref,
     cache_capacity_refusals : int ref,
     pending : pending_sat_shape list ref,
     pending_calls : int ref,
     completed_calls : int ref,
     completed_wall : Time.time ref,
     cache_hit_completed_calls : int ref,
     cache_hit_sat_wall : Time.time ref,
     cache_hit_sat_max_wall : Time.time ref}
  type replay_measurement =
    {def_axiom : route_measurement,
     skeleton_congruence : route_measurement,
     skeleton : skeleton_measurement,
     sat_shapes : sat_shape_measurement,
     total_sample_scans : int ref,
     total_sampled_observations : int ref,
     diagnostic_errors : int ref}

  (* Bounds entered 1,377 def-axiom skeleton calls.  This retains at most
     2,048 whole-target roots.  Subnode data is a deterministic lower-bound
     sample: 64 scope-canonical nodes and 256 scan steps per target.  The
     invocation caps cover every one of the 2,048 observed calls. *)
  val max_measured_target_calls = 2048
  val max_sampled_subnodes_per_target = 64
  val max_sample_scans_per_target = 256
  val max_sampled_observations = 131072
  val max_sample_scans = 524288
  val max_measured_sat_shape_calls = 2048
  val max_sat_shape_cache_entries = 2048
  val max_sat_shape_nodes =
    8 * SmtResource.max_skeleton_replay_dag_nodes + 32

  fun new_route_measurement () : route_measurement =
    {calls = ref 0,
     targets = ref (Redblackmap.mkDict Term.compare),
     target_calls_observed = ref 0,
     targets_unique = ref 0,
     target_repeats_lower_bound = ref 0,
     target_max_multiplicity = ref 0,
     targets_untracked = ref 0,
     target_preflight_truncations = ref 0,
     target_coverage_complete = ref true,
     sampled_subnodes = ref
       (Redblackmap.mkDict sampled_node_key_compare),
     sampled_observations = ref 0,
     sampled_unique = ref 0,
     sampled_repeats_lower_bound = ref 0,
     sampled_max_multiplicity = ref 0,
     sampled_targets_truncated = ref 0,
     sampled_scan_truncations = ref 0,
     sampled_entry_truncations = ref 0,
     sampled_errors = ref 0,
     sampled_coverage_complete = ref true}

  fun new_skeleton_measurement () : skeleton_measurement =
    {successes = ref 0,
     target_dag_nodes = ref 0,
     skeleton_dag_nodes = ref 0,
     normalized_dag_nodes = ref 0,
     sat_dag_nodes = ref 0,
     distinct_atoms = ref 0,
     residual_atoms = ref 0,
     graph_nodes = ref 0,
     graph_observations = ref 0,
     graph_edges = ref 0,
     graph_type_nodes = ref 0,
     graph_type_observations = ref 0,
     graph_type_edges = ref 0,
     graph_leaf_transport_nodes = ref 0,
     graph_leaf_transport_time = ref Time.zeroTime,
     node_cache_hits = ref 0,
     node_pointer_hits = ref 0,
     node_reanchor_attempts = ref 0,
     node_reanchor_successes = ref 0,
     node_reanchor_fallbacks = ref 0,
     node_reanchor_time = ref Time.zeroTime,
     sat_time = ref Time.zeroTime,
     total_time = ref Time.zeroTime}

  fun new_sat_shape_measurement cache_limit : sat_shape_measurement =
    {cache_limit = cache_limit,
     calls = ref 0,
     calls_observed = ref 0,
     shapes = ref (Redblackmap.mkDict Term.compare),
     unique = ref 0,
     repeats = ref 0,
     max_multiplicity = ref 0,
     untracked = ref 0,
     errors = ref 0,
     coverage_complete = ref true,
     cache_entries = ref (Redblackmap.mkDict Term.compare),
     cache_lookups = ref 0,
     cache_hits = ref 0,
     cache_inserts = ref 0,
     cache_capacity_refusals = ref 0,
     pending = ref [],
     pending_calls = ref 0,
     completed_calls = ref 0,
     completed_wall = ref Time.zeroTime,
     cache_hit_completed_calls = ref 0,
     cache_hit_sat_wall = ref Time.zeroTime,
     cache_hit_sat_max_wall = ref Time.zeroTime}

  fun new_replay_measurement () : replay_measurement =
    {def_axiom = new_route_measurement (),
     skeleton_congruence = new_route_measurement (),
     skeleton = new_skeleton_measurement (),
     sat_shapes = new_sat_shape_measurement max_sat_shape_cache_entries,
     total_sample_scans = ref 0,
     total_sampled_observations = ref 0,
     diagnostic_errors = ref 0}

  val current_replay_measurement =
    ref (NONE : replay_measurement option)
  val last_replay_measurement_summary = ref "measurement_enabled=false"

  fun measured_route statistics MeasuredDefAxiom = #def_axiom statistics
    | measured_route statistics MeasuredSkeletonCongruence =
        #skeleton_congruence statistics

  fun route_measurement_text name
      ({calls, target_calls_observed, targets_unique,
        target_repeats_lower_bound, target_max_multiplicity,
        targets_untracked, target_preflight_truncations,
        target_coverage_complete, sampled_observations,
        sampled_unique, sampled_repeats_lower_bound,
        sampled_max_multiplicity, sampled_targets_truncated,
        sampled_scan_truncations, sampled_entry_truncations, sampled_errors,
        sampled_coverage_complete, ...}
       : route_measurement) =
      name ^ "_calls_started=" ^ Int.toString (!calls) ^
      " " ^ name ^ "_target_calls_observed=" ^
        Int.toString (!target_calls_observed) ^
      " " ^ name ^ "_targets_unique_observed=" ^
        Int.toString (!targets_unique) ^
      " " ^ name ^ "_target_repeats_observed_lower_bound=" ^
        Int.toString (!target_repeats_lower_bound) ^
      " " ^ name ^ "_target_max_multiplicity_observed_lower_bound=" ^
        Int.toString (!target_max_multiplicity) ^
      " " ^ name ^ "_targets_untracked=" ^
        Int.toString (!targets_untracked) ^
      " " ^ name ^ "_target_preflight_truncations=" ^
        Int.toString (!target_preflight_truncations) ^
      " " ^ name ^ "_target_coverage_complete=" ^
        Bool.toString (!target_coverage_complete) ^
      " " ^ name ^ "_sampled_observations=" ^
        Int.toString (!sampled_observations) ^
      " " ^ name ^ "_sampled_unique_observed=" ^
        Int.toString (!sampled_unique) ^
      " " ^ name ^ "_sampled_repeats_observed_lower_bound=" ^
        Int.toString (!sampled_repeats_lower_bound) ^
      " " ^ name ^ "_sampled_max_multiplicity_observed_lower_bound=" ^
        Int.toString (!sampled_max_multiplicity) ^
      " " ^ name ^ "_sampled_targets_truncated=" ^
        Int.toString (!sampled_targets_truncated) ^
      " " ^ name ^ "_sampled_scan_truncations=" ^
        Int.toString (!sampled_scan_truncations) ^
      " " ^ name ^ "_sampled_entry_truncations=" ^
        Int.toString (!sampled_entry_truncations) ^
      " " ^ name ^ "_sampled_errors=" ^
        Int.toString (!sampled_errors) ^
      " " ^ name ^ "_sampled_coverage_complete=" ^
        Bool.toString (!sampled_coverage_complete)

  fun skeleton_measurement_text
      ({successes, target_dag_nodes, skeleton_dag_nodes,
        normalized_dag_nodes, sat_dag_nodes, distinct_atoms, residual_atoms,
        graph_nodes, graph_observations, graph_edges, graph_type_nodes,
        graph_type_observations, graph_type_edges, graph_leaf_transport_nodes,
        graph_leaf_transport_time,
        node_cache_hits, node_pointer_hits, node_reanchor_attempts,
        node_reanchor_successes, node_reanchor_fallbacks, node_reanchor_time,
        sat_time, total_time} : skeleton_measurement) =
    " skeleton_successes=" ^ Int.toString (!successes) ^
    " skeleton_target_dag_sum=" ^ Int.toString (!target_dag_nodes) ^
    " skeleton_skeleton_dag_sum=" ^ Int.toString (!skeleton_dag_nodes) ^
    " skeleton_normalized_dag_sum=" ^
      Int.toString (!normalized_dag_nodes) ^
    " skeleton_sat_dag_sum=" ^ Int.toString (!sat_dag_nodes) ^
    " skeleton_distinct_atoms_sum=" ^ Int.toString (!distinct_atoms) ^
    " skeleton_residual_atoms_sum=" ^ Int.toString (!residual_atoms) ^
    " skeleton_graph_nodes_sum=" ^ Int.toString (!graph_nodes) ^
    " skeleton_graph_observations_sum=" ^
      Int.toString (!graph_observations) ^
    " skeleton_graph_edges_sum=" ^ Int.toString (!graph_edges) ^
    " skeleton_graph_type_nodes_sum=" ^ Int.toString (!graph_type_nodes) ^
    " skeleton_graph_type_observations_sum=" ^
      Int.toString (!graph_type_observations) ^
    " skeleton_graph_type_edges_sum=" ^ Int.toString (!graph_type_edges) ^
    " skeleton_graph_leaf_transport_nodes_sum=" ^
      Int.toString (!graph_leaf_transport_nodes) ^
    " skeleton_graph_leaf_transport_wall=" ^
      Time.toString (!graph_leaf_transport_time) ^
    " skeleton_node_cache_hits=" ^ Int.toString (!node_cache_hits) ^
    " skeleton_node_pointer_hits=" ^ Int.toString (!node_pointer_hits) ^
    " skeleton_node_reanchor_attempts=" ^
      Int.toString (!node_reanchor_attempts) ^
    " skeleton_node_reanchor_successes=" ^
      Int.toString (!node_reanchor_successes) ^
    " skeleton_node_reanchor_fallbacks=" ^
      Int.toString (!node_reanchor_fallbacks) ^
    " skeleton_node_reanchor_wall=" ^ Time.toString (!node_reanchor_time) ^
    " skeleton_sat_wall=" ^ Time.toString (!sat_time) ^
    " skeleton_total_wall=" ^ Time.toString (!total_time)

  fun sat_shape_measurement_text
      ({cache_limit, calls, calls_observed, unique, repeats,
        max_multiplicity, untracked, errors, coverage_complete,
        cache_entries, cache_lookups, cache_hits, cache_inserts,
        cache_capacity_refusals, pending_calls, completed_calls,
        completed_wall, cache_hit_completed_calls, cache_hit_sat_wall,
        cache_hit_sat_max_wall, ...} : sat_shape_measurement) =
    " sat_shape_calls_started=" ^ Int.toString (!calls) ^
    " sat_shape_calls_observed=" ^ Int.toString (!calls_observed) ^
    " sat_shape_unique_observed=" ^ Int.toString (!unique) ^
    " sat_shape_repeats_observed_lower_bound=" ^
      Int.toString (!repeats) ^
    " sat_shape_max_multiplicity_observed_lower_bound=" ^
      Int.toString (!max_multiplicity) ^
    " sat_shape_untracked=" ^ Int.toString (!untracked) ^
    " sat_shape_errors=" ^ Int.toString (!errors) ^
    " sat_shape_coverage_complete=" ^
      Bool.toString (!coverage_complete) ^
    " sat_shape_cache_limit=" ^ Int.toString cache_limit ^
    " sat_shape_cache_lookups=" ^ Int.toString (!cache_lookups) ^
    " sat_shape_cache_hits=" ^ Int.toString (!cache_hits) ^
    " sat_shape_cache_inserts=" ^ Int.toString (!cache_inserts) ^
    " sat_shape_cache_capacity_refusals=" ^
      Int.toString (!cache_capacity_refusals) ^
    " sat_shape_cache_entries=" ^
      Int.toString (Redblackmap.numItems (!cache_entries)) ^
    " sat_shape_pending_calls=" ^ Int.toString (!pending_calls) ^
    " sat_shape_sat_completed_calls=" ^ Int.toString (!completed_calls) ^
    " sat_shape_sat_completed_wall=" ^ Time.toString (!completed_wall) ^
    " sat_shape_cache_hit_completed_calls=" ^
      Int.toString (!cache_hit_completed_calls) ^
    " sat_shape_cache_hit_sat_wall=" ^ Time.toString (!cache_hit_sat_wall) ^
    " sat_shape_cache_hit_sat_max_wall=" ^
      Time.toString (!cache_hit_sat_max_wall)

  fun replay_measurement_text statistics =
    "measurement_enabled=true " ^
    route_measurement_text "def_attempt" (#def_axiom statistics) ^ " " ^
    route_measurement_text "cong" (#skeleton_congruence statistics) ^
    skeleton_measurement_text (#skeleton statistics) ^
    sat_shape_measurement_text (#sat_shapes statistics) ^
    " measurement_sample_scans=" ^
      Int.toString (!(#total_sample_scans statistics)) ^
    " measurement_sampled_observations=" ^
      Int.toString (!(#total_sampled_observations statistics)) ^
    " measurement_diagnostic_errors=" ^
      Int.toString (!(#diagnostic_errors statistics))

  fun current_replay_measurement_text () =
    case !current_replay_measurement of
      NONE => !last_replay_measurement_summary
    | SOME statistics => replay_measurement_text statistics

  fun reset_replay_measurement () =
    (last_replay_measurement_summary := "measurement_enabled=false";
     current_replay_measurement :=
       if SmtResource.e0_enabled () then SOME (new_replay_measurement ())
       else NONE)

  fun detach_replay_measurement () =
    let val detached = !current_replay_measurement
    in current_replay_measurement := NONE; detached end

  fun finish_replay_measurement NONE = ()
    | finish_replay_measurement (SOME statistics) =
        (SmtResource.invoke_e0_diagnostic_hook "measurement-summary";
         last_replay_measurement_summary := replay_measurement_text statistics)

  fun terminal_diagnostic_exception exn =
    SmtResource.terminal_diagnostic_exception exn

  fun mark_target_diagnostic_error statistics route_statistics =
    (#diagnostic_errors statistics := !(#diagnostic_errors statistics) + 1;
     #targets_untracked route_statistics :=
       !(#targets_untracked route_statistics) + 1;
     #target_coverage_complete route_statistics := false)

  fun mark_sample_diagnostic_error statistics route_statistics =
    (#diagnostic_errors statistics := !(#diagnostic_errors statistics) + 1;
     #sampled_errors route_statistics :=
       !(#sampled_errors route_statistics) + 1;
     #sampled_coverage_complete route_statistics := false)

  fun record_measured_target route target =
    case !current_replay_measurement of
      NONE => ()
    | SOME statistics =>
        let
          val route_statistics = measured_route statistics route
          val calls = #calls route_statistics
          val targets = #targets route_statistics
          val _ = calls := !calls + 1
          fun terminal_or_mark_target exn =
            if terminal_diagnostic_exception exn then raise exn
            else (mark_target_diagnostic_error statistics route_statistics;
                  false)
          fun terminal_or_mark_sample exn =
            if terminal_diagnostic_exception exn then raise exn
            else mark_sample_diagnostic_error statistics route_statistics
          fun skip_preflight () =
            (#target_preflight_truncations route_statistics :=
               !(#target_preflight_truncations route_statistics) + 1;
             #targets_untracked route_statistics :=
               !(#targets_untracked route_statistics) + 1;
             #target_coverage_complete route_statistics := false;
             #sampled_coverage_complete route_statistics := false)
          fun target_preflight () =
            if SmtResource.dag_nodes_up_to
                SmtResource.max_skeleton_replay_dag_nodes target >
                SmtResource.max_skeleton_replay_dag_nodes
            then (skip_preflight (); false)
            else true
          fun commit_target () =
            if !(#target_calls_observed route_statistics) >=
                max_measured_target_calls then
              (#targets_untracked route_statistics :=
                 !(#targets_untracked route_statistics) + 1;
               #target_coverage_complete route_statistics := false;
               #sampled_coverage_complete route_statistics := false;
               false)
            else
              let
                val previous = Redblackmap.peek (!targets, target)
                val count = Option.getOpt (previous, 0) + 1
                val updated = Redblackmap.insert (!targets, target, count)
              in
                targets := updated;
                #target_calls_observed route_statistics :=
                  !(#target_calls_observed route_statistics) + 1;
                (case previous of
                   NONE => #targets_unique route_statistics :=
                     !(#targets_unique route_statistics) + 1
                 | SOME _ => #target_repeats_lower_bound route_statistics :=
                     !(#target_repeats_lower_bound route_statistics) + 1);
                #target_max_multiplicity route_statistics := Int.max
                  (!(#target_max_multiplicity route_statistics), count);
                true
              end
          val seen = ref ([] : (term * int list) list)
          val sampled = ref 0
          val scans = ref 0
          val next_scope = ref 0
          fun same_seen (term, scope) (saved, saved_scope) =
            scope = saved_scope andalso Portable.pointer_eq (term, saved)
          fun canonical term binders : sampled_node_key =
            (List.foldl (fn (binder, body) => Term.mk_abs (binder, body))
               term binders,
             Term.type_of term, List.length binders)
          fun add_sample key =
            let
              val samples = #sampled_subnodes route_statistics
              val previous = Redblackmap.peek (!samples, key)
              val count = Option.getOpt (previous, 0) + 1
              val updated = Redblackmap.insert (!samples, key, count)
            in
              samples := updated;
              sampled := !sampled + 1;
              #sampled_observations route_statistics :=
                !(#sampled_observations route_statistics) + 1;
              #total_sampled_observations statistics :=
                !(#total_sampled_observations statistics) + 1;
              (case previous of
                 NONE => #sampled_unique route_statistics :=
                   !(#sampled_unique route_statistics) + 1
               | SOME _ => #sampled_repeats_lower_bound route_statistics :=
                   !(#sampled_repeats_lower_bound route_statistics) + 1);
              #sampled_max_multiplicity route_statistics := Int.max
                (!(#sampled_max_multiplicity route_statistics), count)
            end
          fun loop [] = ()
            | loop pending =
                if !sampled >= max_sampled_subnodes_per_target then
                  (#sampled_targets_truncated route_statistics :=
                     !(#sampled_targets_truncated route_statistics) + 1;
                   #sampled_coverage_complete route_statistics := false)
                else if !scans >= max_sample_scans_per_target orelse
                    !(#total_sample_scans statistics) >= max_sample_scans then
                  (#sampled_scan_truncations route_statistics :=
                     !(#sampled_scan_truncations route_statistics) + 1;
                   #sampled_coverage_complete route_statistics := false)
                else if !(#total_sampled_observations statistics) >=
                    max_sampled_observations then
                  (#sampled_entry_truncations route_statistics :=
                     !(#sampled_entry_truncations route_statistics) + 1;
                   #sampled_coverage_complete route_statistics := false)
                else
                  let
                    val (term, binders, scope) = hd pending
                    val pending = tl pending
                    val _ = scans := !scans + 1
                    val _ = #total_sample_scans statistics :=
                      !(#total_sample_scans statistics) + 1
                  in
                    if List.exists (same_seen (term, scope)) (!seen) then
                      loop pending
                    else
                      let
                        val _ = seen := (term, scope) :: !seen
                        val _ = add_sample (canonical term binders)
                        val pending =
                          if Term.is_comb term then
                            let val (operator, operand) = Term.dest_comb term
                            in
                              (operator, binders, scope) ::
                              (operand, binders, scope) :: pending
                            end
                          else if Term.is_abs term then
                            let
                              val (binder, body) = Term.dest_abs term
                              val stamp = !next_scope
                              val _ = next_scope := stamp + 1
                            in
                              (body, binder :: binders, stamp :: scope) ::
                                pending
                            end
                          else pending
                      in
                        loop pending
                      end
                  end
          fun sample () =
            (SmtResource.invoke_e0_diagnostic_hook "measurement-sample";
             loop [(target, [], [])])
          val admitted = target_preflight ()
            handle exn => terminal_or_mark_target exn
          val committed = admitted andalso
            (commit_target () handle exn => terminal_or_mark_target exn)
        in
          if committed then
            (sample () handle exn => terminal_or_mark_sample exn)
          else ()
        end

  fun add_metric destination amount = destination :=
    SmtResource.saturated_add (!destination) amount

  fun record_skeleton_metrics
      (metrics : SmtSkeletonProve.metrics) =
    case !current_replay_measurement of
      NONE => ()
    | SOME statistics =>
        let val skeleton = #skeleton statistics
        in
          #successes skeleton := !(#successes skeleton) + 1;
          add_metric (#target_dag_nodes skeleton) (#target_dag_nodes metrics);
          add_metric (#skeleton_dag_nodes skeleton)
            (#skeleton_dag_nodes metrics);
          add_metric (#normalized_dag_nodes skeleton)
            (#normalized_dag_nodes metrics);
          add_metric (#sat_dag_nodes skeleton) (#sat_dag_nodes metrics);
          add_metric (#distinct_atoms skeleton) (#distinct_atoms metrics);
          add_metric (#residual_atoms skeleton) (#residual_atoms metrics);
          add_metric (#graph_nodes skeleton) (#graph_nodes metrics);
          add_metric (#graph_observations skeleton)
            (#graph_observations metrics);
          add_metric (#graph_edges skeleton) (#graph_edges metrics);
          add_metric (#graph_type_nodes skeleton) (#graph_type_nodes metrics);
          add_metric (#graph_type_observations skeleton)
            (#graph_type_observations metrics);
          add_metric (#graph_type_edges skeleton) (#graph_type_edges metrics);
          add_metric (#graph_leaf_transport_nodes skeleton)
            (#graph_leaf_transport_nodes metrics);
          #graph_leaf_transport_time skeleton := Time.+
            (!(#graph_leaf_transport_time skeleton),
             #graph_leaf_transport_seconds metrics);
          #sat_time skeleton := Time.+
            (!(#sat_time skeleton), #sat_seconds metrics);
          #total_time skeleton := Time.+
            (!(#total_time skeleton), #total_seconds metrics)
        end
        handle exn =>
          if terminal_diagnostic_exception exn then raise exn
          else #diagnostic_errors statistics :=
            !(#diagnostic_errors statistics) + 1

  fun canonical_sat_shape target =
    let
      val observed = SmtResource.dag_nodes_up_to max_sat_shape_nodes target
      val _ = if observed <= max_sat_shape_nodes then ()
        else raise ERR "canonical_sat_shape"
          "checked SAT target exceeded the diagnostic shape bound"
      val nodes = ref (Redblackmap.mkDict Term.compare)
      val variables = ref (Redblackmap.mkDict Term.compare)
      val next_variable = ref 0
      fun canonical_variable variable =
        case Redblackmap.peek (!variables, variable) of
          SOME result => result
        | NONE =>
            let
              val index = !next_variable
              val result = Term.mk_var
                ("__holsmt_sat_shape_" ^ Int.toString index, Type.bool)
            in
              next_variable := index + 1;
              variables := Redblackmap.insert
                (!variables, variable, result);
              result
            end
      fun visit_children [] result = List.rev result
        | visit_children (child :: rest) result =
            visit_children rest (visit child :: result)
      and visit term =
        case Redblackmap.peek (!nodes, term) of
          SOME result => result
        | NONE =>
            let
              val result =
                if Term.is_var term andalso Term.type_of term = Type.bool then
                  canonical_variable term
                else
                  case SmtSkeletonProve.skeleton_children term of
                    SOME [] => term
                  | SOME children =>
                      let
                        val (head, _) = boolSyntax.strip_comb term
                      in
                        List.foldl
                          (fn (child, function) =>
                            Term.mk_comb (function, child))
                          head (visit_children children [])
                      end
                  | NONE => raise ERR "canonical_sat_shape"
                      "checked SAT target contains an opaque non-variable"
              val _ = nodes := Redblackmap.insert (!nodes, term, result)
            in
              result
            end
      val _ = if Term.type_of target = Type.bool then ()
        else raise ERR "canonical_sat_shape"
          "checked SAT target is not Boolean"
    in
      visit target
    end

  fun record_sat_shape_target
      (measurement : sat_shape_measurement) target =
    let
      val calls = #calls measurement
      val _ = calls := !calls + 1
      fun push pending =
        (#pending measurement := pending :: !(#pending measurement);
         #pending_calls measurement := !(#pending_calls measurement) + 1)
      fun mark_error () =
        (#errors measurement := !(#errors measurement) + 1;
         #untracked measurement := !(#untracked measurement) + 1;
         #coverage_complete measurement := false;
         push PendingSatShapeUntracked;
         false)
      fun record () =
        if !calls > max_measured_sat_shape_calls then
          (#untracked measurement := !(#untracked measurement) + 1;
           #coverage_complete measurement := false;
           push PendingSatShapeUntracked;
           true)
        else
          let
            val shape = canonical_sat_shape target
            val shapes = #shapes measurement
            val previous = Redblackmap.peek (!shapes, shape)
            val count = Option.getOpt (previous, 0) + 1
            val _ = shapes := Redblackmap.insert (!shapes, shape, count)
            val _ = #calls_observed measurement :=
              !(#calls_observed measurement) + 1
            val _ =
              case previous of
                NONE => #unique measurement := !(#unique measurement) + 1
              | SOME _ => #repeats measurement :=
                  !(#repeats measurement) + 1
            val _ = #max_multiplicity measurement := Int.max
              (!(#max_multiplicity measurement), count)
            val cache = #cache_entries measurement
            val _ = #cache_lookups measurement :=
              !(#cache_lookups measurement) + 1
          in
            case Redblackmap.peek (!cache, shape) of
              SOME () =>
                (#cache_hits measurement :=
                   !(#cache_hits measurement) + 1;
                 push PendingSatShapeHit;
                 true)
            | NONE =>
                (push (PendingSatShapeMiss shape); true)
          end
    in
      record () handle exn =>
        if terminal_diagnostic_exception exn then raise exn else mark_error ()
    end

  fun record_sat_shape_completion
      (measurement : sat_shape_measurement) elapsed =
    let
      fun mark_error () =
        (#errors measurement := !(#errors measurement) + 1;
         #coverage_complete measurement := false;
         false)
      fun complete pending =
        case pending of
          PendingSatShapeUntracked => true
        | PendingSatShapeHit =>
            (#cache_hit_completed_calls measurement :=
               !(#cache_hit_completed_calls measurement) + 1;
             #cache_hit_sat_wall measurement := Time.+
               (!(#cache_hit_sat_wall measurement), elapsed);
             #cache_hit_sat_max_wall measurement :=
               if Time.compare
                    (elapsed, !(#cache_hit_sat_max_wall measurement)) = GREATER
               then elapsed
               else !(#cache_hit_sat_max_wall measurement);
             true)
        | PendingSatShapeMiss shape =>
            let val cache = #cache_entries measurement
            in
              case Redblackmap.peek (!cache, shape) of
                SOME () => true
              | NONE =>
                  if Redblackmap.numItems (!cache) <
                      #cache_limit measurement then
                    (cache := Redblackmap.insert (!cache, shape, ());
                     #cache_inserts measurement :=
                       !(#cache_inserts measurement) + 1;
                     true)
                  else
                    (#cache_capacity_refusals measurement :=
                       !(#cache_capacity_refusals measurement) + 1;
                     true)
            end
      fun record () =
        let
          val _ = #completed_calls measurement :=
            !(#completed_calls measurement) + 1
          val _ = #completed_wall measurement := Time.+
            (!(#completed_wall measurement), elapsed)
        in
          case !(#pending measurement) of
            [] => mark_error ()
          | pending :: rest =>
              (#pending measurement := rest;
               #pending_calls measurement :=
                 !(#pending_calls measurement) - 1;
               complete pending)
        end
    in
      record () handle exn =>
        if terminal_diagnostic_exception exn then raise exn else mark_error ()
    end

  fun observe_skeleton_sat_target target =
    case !current_replay_measurement of
      NONE => ()
    | SOME statistics =>
        if record_sat_shape_target (#sat_shapes statistics) target then ()
        else #diagnostic_errors statistics :=
          !(#diagnostic_errors statistics) + 1

  fun observe_skeleton_sat_completion (_, elapsed) =
    case !current_replay_measurement of
      NONE => ()
    | SOME statistics =>
        if record_sat_shape_completion (#sat_shapes statistics) elapsed then ()
        else #diagnostic_errors statistics :=
          !(#diagnostic_errors statistics) + 1

  fun observe_skeleton_node_cache event =
    case !current_replay_measurement of
      NONE => ()
    | SOME statistics =>
        let val skeleton = #skeleton statistics
        in
          case event of
            SmtSkeletonProve.NodeCachePointerHit =>
              (add_metric (#node_cache_hits skeleton) 1;
               add_metric (#node_pointer_hits skeleton) 1)
          | SmtSkeletonProve.NodeCacheStructuralReanchorAttempt =>
              (add_metric (#node_cache_hits skeleton) 1;
               add_metric (#node_reanchor_attempts skeleton) 1)
          | SmtSkeletonProve.NodeCacheStructuralReanchorSuccess =>
              add_metric (#node_reanchor_successes skeleton) 1
          | SmtSkeletonProve.NodeCacheStructuralReanchorFallback =>
              add_metric (#node_reanchor_fallbacks skeleton) 1
          | SmtSkeletonProve.NodeCacheReanchorTime elapsed =>
              #node_reanchor_time skeleton := Time.+
                (!(#node_reanchor_time skeleton), elapsed)
        end
        handle exn =>
          if terminal_diagnostic_exception exn then raise exn
          else #diagnostic_errors statistics :=
            !(#diagnostic_errors statistics) + 1

  fun proof_step_state id rule status local_info : proof_step_state =
    {id = id, rule = rule, status = status, local_info = local_info}

  fun set_latest_proof_step id rule status local_info =
    (latest_proof_step := SOME
      (proof_step_state id rule status local_info);
     if OS.Process.getEnv "HOL4_Z3_REPLAY_TRACE" = SOME "1" andalso
        (!replay_completed_steps < 20 orelse
         !replay_completed_steps >= 350 andalso
         !replay_completed_steps < 700) then
       (Feedback.HOL_MESG
         ("Z3 replay step: id=" ^ Int.toString id ^
          " rule=" ^ rule ^ " status=" ^ status ^
          " completed=" ^ Int.toString (!replay_completed_steps));
        TextIO.flushOut TextIO.stdOut)
     else ())

  fun track_proof_step_with_local id rule local_info action input =
    let
      val previous_step = !active_proof_step
      fun restore () = active_proof_step := previous_step
      fun fail exn =
        (case !first_failed_proof_step of
           NONE =>
             first_failed_proof_step := SOME
               (proof_step_state id rule "failure" local_info)
         | SOME _ => ();
         raise exn)
      fun work () =
        (active_proof_step := SOME
           (proof_step_state id rule "active" local_info);
         set_latest_proof_step id rule "start" local_info;
         action input handle exn => fail exn)
    in
      Portable.finally restore work ()
    end

  fun track_proof_step id rule action input =
    track_proof_step_with_local id rule NONE action input

  fun capture_skeleton_obligation (state : state) target exn =
    case OS.Process.getEnv "HOL4_SMT_E0_CAPTURE_DIR" of
      NONE => ()
    | SOME directory =>
        let
          val _ = SmtResource.invoke_e0_diagnostic_hook
            "capture-skeleton-obligation"
          val maximum = SmtResource.max_skeleton_replay_dag_nodes
          val structure_metrics =
            SmtResource.bounded_structure maximum target
          val digest =
            if #complete structure_metrics then
              SOME (SmtResource.bounded_graph_digest (maximum + 1) target)
            else NONE
          val proof_id =
            case !active_proof_step of
              SOME {id, ...} => Int.toString id
            | NONE => "root-or-unbound"
          val digest_text =
            case digest of
              SOME data => #digest data
            | NONE => "unavailable-oversized"
          val serialization =
            case digest of
              SOME data => #serialization data
            | NONE => "<oversized>"
          val serialization_bytes =
            case digest of
              SOME data => #serialization_bytes data
            | NONE => 0
          val message =
            "obligation rule=def_axiom proof_id=" ^ proof_id ^
            " nodes=" ^ Int.toString (#dag_nodes structure_metrics) ^
            " edges=" ^ Int.toString (#edges structure_metrics) ^
            " binder_depth=" ^
              Int.toString (#max_binder_depth structure_metrics) ^
            " identifier_bytes=" ^
              Int.toString (#max_identifier_bytes structure_metrics) ^
            " asserted_dependencies=" ^
              Int.toString (HOLset.numItems (#asserted_hyps state)) ^
            " definition_dependencies=" ^
              Int.toString (HOLset.numItems (#definition_hyps state)) ^
            " allowed_assertions=" ^
              Int.toString (HOLset.numItems (#allowed_asserted_hyps state)) ^
            " digest=" ^ digest_text ^
            " exception=" ^ SmtResource.exception_class exn
          val _ = SmtResource.emit_e0 message
          val _ = OS.FileSys.mkDir directory handle SysErr _ => ()
          val path = OS.Path.concat
            (directory, "first-skeleton-obligation.meta")
          val _ =
            if OS.FileSys.access (path, []) then ()
            else Library.write_strings_to_file path
              [message, "\nserialization_bytes=",
               Int.toString serialization_bytes,
               "\nserialization=", serialization, "\n"]
        in () end

  fun replay_snapshot_step () =
    case !first_failed_proof_step of
      SOME {id, rule, status, ...} => SOME (id, rule, status)
    | NONE =>
        case !active_proof_step of
          SOME {id, rule, ...} => SOME (id, rule, "active")
        | NONE =>
            case !latest_proof_step of
              SOME {id, rule, status, ...} => SOME (id, rule, status)
            | NONE => NONE

  fun replay_snapshot_local () =
    case !first_failed_proof_step of
      SOME {local_info, ...} => local_info
    | NONE =>
        case !active_proof_step of
          SOME {local_info, ...} => local_info
        | NONE =>
            case !latest_proof_step of
              SOME {local_info, ...} => local_info
            | NONE => NONE

  fun clear_step_local NONE = NONE
    | clear_step_local (SOME {id, rule, status, ...}) =
        SOME (proof_step_state id rule status NONE)

  fun clear_replay_local_structures () =
    (active_proof_step := clear_step_local (!active_proof_step);
     latest_proof_step := clear_step_local (!latest_proof_step);
     first_failed_proof_step := clear_step_local (!first_failed_proof_step))

  fun replay_local_structure_count () =
    let
      fun present NONE = 0
        | present (SOME {local_info = NONE, ...}) = 0
        | present (SOME {local_info = SOME _, ...}) = 1
    in
      present (!active_proof_step) + present (!latest_proof_step) +
      present (!first_failed_proof_step)
    end

  fun emit_replay_snapshot exn =
    let
      val step =
        case replay_snapshot_step () of
          NONE => "id=unavailable rule=unavailable status=unavailable"
        | SOME (id, rule, status) =>
            "id=" ^ Int.toString id ^ " rule=" ^ rule ^
            " status=" ^ status
      val local_text =
        case replay_snapshot_local () of
          NONE => "local=unavailable"
        | SOME describe =>
            describe ()
            handle diagnostic_exn =>
              if terminal_diagnostic_exception diagnostic_exn then
                raise diagnostic_exn
              else "local=unavailable diagnostic_exception=" ^
                SmtResource.exception_class diagnostic_exn
      val measurement_text =
        (current_replay_measurement_text () handle diagnostic_exn =>
          if terminal_diagnostic_exception diagnostic_exn then
            raise diagnostic_exn
          else "measurement_unavailable=true measurement_exception=" ^
            SmtResource.exception_class diagnostic_exn)
      val cache_text =
        (current_def_axiom_cache_text () handle diagnostic_exn =>
          if terminal_diagnostic_exception diagnostic_exn then
            raise diagnostic_exn
          else "def_cache_unavailable=true def_cache_exception=" ^
            SmtResource.exception_class diagnostic_exn)
      val message = SmtResource.bounded_text 4096
        ("replay-snapshot " ^ step ^ " exception=" ^
         SmtResource.exception_class exn ^ " " ^ cache_text ^ " " ^
         measurement_text ^ " " ^ local_text)
    in
      SmtResource.emit_e0_replay_snapshot message;
      SmtResource.emit_profile_summary ()
    end

  fun with_e0_replay_boundary_for duration replay input =
    if not (SmtResource.e0_enabled ()) then replay input
    else
      (Timeout.apply duration replay input
       handle exn => SmtResource.resolve_diagnostic_exception exn
         (fn () => emit_replay_snapshot exn)
         (fn original => raise original))

  val replay_measurement_boundary_depth = ref 0

  fun with_fresh_e0_replay_boundary_for duration replay input =
    if !replay_measurement_boundary_depth > 0 then
      with_e0_replay_boundary_for duration replay input
    else
      let
        val _ = replay_measurement_boundary_depth := 1
        val _ = active_proof_step := NONE
        val _ = latest_proof_step := NONE
        val _ = first_failed_proof_step := NONE
        val _ = reset_replay_measurement ()
        fun run () =
          case !current_replay_measurement of
            NONE => with_e0_replay_boundary_for duration replay input
          | SOME _ => SmtSkeletonProve.with_sat_observers
              (SOME observe_skeleton_sat_target)
              (SOME observe_skeleton_sat_completion)
              (with_e0_replay_boundary_for duration replay) input
        fun clear () =
          let
            val detached = detach_replay_measurement ()
            val _ = replay_measurement_boundary_depth := 0
            val _ = clear_replay_local_structures ()
          in
            finish_replay_measurement detached
          end
        val outcome = Exn.capture run ()
      in
        case outcome of
          Exn.Res result =>
            (case Exn.capture clear () of
               Exn.Res _ => result
             | Exn.Exn cleanup_exn =>
                 SmtResource.resolve_diagnostic_exception cleanup_exn
                   (fn () => ()) (fn _ => result))
        | Exn.Exn replay_exn =>
            SmtResource.resolve_diagnostic_exception replay_exn clear
              (fn original => raise original)
      end

  fun with_e0_replay_boundary replay input =
    with_fresh_e0_replay_boundary_for (Time.fromSeconds 90) replay input

  fun admitted_def_axiom_measure measure target =
    let
      val maximum = SmtResource.max_skeleton_replay_dag_nodes
      val observed = SmtResource.profile_phase
        "skeleton/admission-bounded"
        (SmtResource.dag_nodes_up_to maximum) target
      val _ = SmtResource.check_dag_size_for
        "Skeleton" "z3-def-axiom" observed
      val structure_metrics = SmtResource.profile_phase
        "skeleton/admission-structure"
        (SmtResource.bounded_structure maximum) target
      val _ = SmtResource.emit_e0
        ("structure stage=skeleton-admission nodes=" ^
         Int.toString observed ^ " edges=" ^
         Int.toString (#edges structure_metrics) ^ " binder_depth=" ^
         Int.toString (#max_binder_depth structure_metrics) ^
         " identifier_bytes=" ^
         Int.toString (#max_identifier_bytes structure_metrics) ^
         " complete=" ^ Bool.toString (#complete structure_metrics))
    in
      SmtResource.profile_phase "skeleton/measurement-full"
        measure target
    end

  val max_def_axiom_boolean_spine_nodes = 512
  val max_def_axiom_boolean_comparisons = 4096
  val max_def_axiom_atom_compare_nodes = 256
  val max_def_axiom_atom_compare_work = 131072

  datatype def_axiom_disjunction_step =
      DefAxiomDisjunctionLeft of term
    | DefAxiomDisjunctionRight of term

  datatype def_axiom_conjunction_shape =
      DefAxiomConjunctionLeaf
    | DefAxiomConjunctionNode of
        def_axiom_conjunction_shape * def_axiom_conjunction_shape

  datatype def_axiom_disjunction_shape =
      DefAxiomDisjunctionLeaf of int
    | DefAxiomDisjunctionNode of
        def_axiom_disjunction_shape * def_axiom_disjunction_shape

  datatype def_axiom_conjunction_step =
      DefAxiomConjunctionLeft of term
    | DefAxiomConjunctionRight of term

  exception DEF_AXIOM_DECLINE of string * string
  exception DEF_AXIOM_STRUCTURAL_UNEXPECTED of exn

  fun bounded_def_axiom_work counter maximum kind =
    (counter := !counter + 1;
     if !counter <= maximum then ()
     else raise DEF_AXIOM_DECLINE
       ("def_axiom_boolean_spine",
        kind ^ " exceeds its structural bound"))

  fun def_axiom_decline function message =
    raise DEF_AXIOM_DECLINE (function, message)

  fun try_def_axiom_candidates prove [] =
        def_axiom_decline "def_axiom_conjunction_clause"
          "no conjunction candidate has all complementary disjuncts"
    | try_def_axiom_candidates prove (candidate :: rest) =
        prove candidate
        handle decline as DEF_AXIOM_DECLINE (function, _) =>
          if function = "def_axiom_conjunction_clause" then
            try_def_axiom_candidates prove rest
          else raise decline

  fun def_axiom_conjunction_member same_term target =
    let
      val _ = boolSyntax.is_disj target orelse
        def_axiom_decline "def_axiom_conjunction_member"
          "target is not a disjunction"
      val (left, right) = boolSyntax.dest_disj target
      val _ = boolSyntax.is_neg left orelse
        def_axiom_decline "def_axiom_conjunction_member"
          "left disjunct is not negated"
      val conjunction = boolSyntax.dest_neg left
      val spine_nodes = ref 0
      fun visit current theorem =
        (bounded_def_axiom_work spine_nodes
           max_def_axiom_boolean_spine_nodes "Boolean spine";
         if same_term (current, right) then SOME theorem
         else
           if boolSyntax.is_conj current then
             let val (left, right) = boolSyntax.dest_conj current
             in
               (case visit left (Thm.CONJUNCT1 theorem) of
                  SOME result => SOME result
                | NONE => visit right (Thm.CONJUNCT2 theorem))
             end
           else NONE)
      val member =
        case visit conjunction (Thm.ASSUME conjunction) of
          SOME theorem => theorem
        | NONE => def_axiom_decline "def_axiom_conjunction_member"
            "right disjunct is not a bounded conjunction member"
    in
      Drule.IMP_ELIM (Thm.DISCH conjunction member)
    end

  fun def_axiom_conjunction_clause same_term target =
    let
      val disjunction_nodes = ref 0
      val conjunction_nodes = ref 0

      fun disjuncts path current result =
        (bounded_def_axiom_work disjunction_nodes
           max_def_axiom_boolean_spine_nodes "disjunction spine";
         if boolSyntax.is_disj current then
           let val (left, right) = boolSyntax.dest_disj current
           in
             disjuncts (DefAxiomDisjunctionLeft right :: path) left
               (disjuncts
                 (DefAxiomDisjunctionRight left :: path) right result)
           end
         else (current, path) :: result)

      fun conjunction current =
        (bounded_def_axiom_work conjunction_nodes
           max_def_axiom_boolean_spine_nodes "conjunction spine";
         if boolSyntax.is_conj current then
           let
             val (left, right) = boolSyntax.dest_conj current
             val (left_shape, left_leaves) = conjunction left
             val (right_shape, right_leaves) = conjunction right
           in
             (DefAxiomConjunctionNode (left_shape, right_shape),
              left_leaves @ right_leaves)
           end
         else (DefAxiomConjunctionLeaf, [current]))

      fun lift_disjunction (step, theorem) =
        case step of
          DefAxiomDisjunctionLeft right => Thm.DISJ1 theorem right
        | DefAxiomDisjunctionRight left => Thm.DISJ2 left theorem

      fun introduce_disjunction path theorem =
        List.foldl lift_disjunction theorem path

      fun make_conjunction shape theorems =
        case (shape, theorems) of
          (DefAxiomConjunctionLeaf, theorem :: rest) => (theorem, rest)
        | (DefAxiomConjunctionNode (left, right), _) =>
            let
              val (left_theorem, rest) = make_conjunction left theorems
              val (right_theorem, rest) = make_conjunction right rest
            in
              (Thm.CONJ left_theorem right_theorem, rest)
            end
        | _ => raise ERR "def_axiom_conjunction_clause"
            "conjunction theorem list has the wrong length"

      fun complement literal candidate =
        if boolSyntax.is_neg literal then
          same_term (boolSyntax.dest_neg literal, candidate)
        else if boolSyntax.is_neg candidate then
          same_term (literal, boolSyntax.dest_neg candidate)
        else false

      val target_disjuncts = disjuncts [] target []

      fun prove_candidate (candidate, candidate_path) =
        let
          val (shape, leaves) = conjunction candidate
          fun complement_for literal =
            case List.find
                (fn (disjunct, _) => complement literal disjunct)
                target_disjuncts of
              SOME result => result
            | NONE => def_axiom_decline "def_axiom_conjunction_clause"
                "a conjunction leaf has no complementary disjunct"
          val leaves_and_complements =
            List.map (fn leaf => (leaf, complement_for leaf)) leaves

          fun finish assumptions =
            let
              val (theorem, rest) =
                make_conjunction shape (List.rev assumptions)
              val _ = List.null rest orelse
                raise ERR "def_axiom_conjunction_clause"
                  "unused conjunction leaf theorem"
            in
              introduce_disjunction candidate_path theorem
            end

          fun cases [] assumptions = finish assumptions
            | cases ((literal, (opposite, opposite_path)) :: rest)
                assumptions =
                (if boolSyntax.is_neg literal then
                   let val atom = boolSyntax.dest_neg literal
                   in
                     Thm.DISJ_CASES (Thm.SPEC atom boolTheory.EXCLUDED_MIDDLE)
                       (introduce_disjunction opposite_path
                         (Thm.ASSUME opposite))
                       (cases rest (Thm.ASSUME literal :: assumptions))
                   end
                 else
                     Thm.DISJ_CASES
                       (Thm.SPEC literal boolTheory.EXCLUDED_MIDDLE)
                       (cases rest (Thm.ASSUME literal :: assumptions))
                       (introduce_disjunction opposite_path
                         (Thm.ASSUME opposite)))
        in
          cases leaves_and_complements []
        end

    in
      try_def_axiom_candidates prove_candidate
        (List.filter (boolSyntax.is_conj o Lib.fst) target_disjuncts)
    end

  fun def_axiom_member_schema target =
    let
      val _ = boolSyntax.is_disj target orelse
        def_axiom_decline "def_axiom_conjunction_member"
          "target is not a disjunction"
      val (left, right) = boolSyntax.dest_disj target
      val _ = boolSyntax.is_neg left orelse
        def_axiom_decline "def_axiom_conjunction_member"
          "left disjunct is not negated"
      val actual_conjunction = boolSyntax.dest_neg left
      val spine_nodes = ref 0
      val comparison_work = ref 0
      val member_variable = Term.genvar Type.bool
      val substitution = ref ([] : {redex : term, residue : term} list)

      fun add_work amount =
        (comparison_work := !comparison_work + amount;
         if !comparison_work <= max_def_axiom_atom_compare_work then ()
         else def_axiom_decline "def_axiom_conjunction_member"
           "Boolean atom comparison work exceeds its structural bound")

      fun same_member actual =
        if Portable.pointer_eq (actual, right) then true
        else
          let
            val actual_nodes = SmtResource.term_nodes_up_to
              max_def_axiom_atom_compare_nodes actual
            val right_nodes = SmtResource.term_nodes_up_to
              max_def_axiom_atom_compare_nodes right
            val _ = add_work (actual_nodes + right_nodes)
          in
            actual_nodes <= max_def_axiom_atom_compare_nodes andalso
            right_nodes <= max_def_axiom_atom_compare_nodes andalso
            Term.aconv actual right
          end

      fun opaque actual =
        let val variable = Term.genvar Type.bool
        in
          substitution := {redex = variable, residue = actual} ::
            !substitution;
          variable
        end

      fun search ([], []) = def_axiom_decline
            "def_axiom_conjunction_member"
            "right disjunct is not a bounded conjunction member"
        | search ([], back) = search (List.rev back, [])
        | search ((actual, path) :: front, back) =
            (bounded_def_axiom_work spine_nodes
               max_def_axiom_boolean_spine_nodes "conjunction spine";
             if same_member actual then (actual, path)
             else if boolSyntax.is_conj actual then
               let
                 val (left, right) = boolSyntax.dest_conj actual
               in
                 search (front,
                   (right, DefAxiomConjunctionRight left :: path) ::
                   (left, DefAxiomConjunctionLeft right :: path) :: back)
               end
             else search (front, back))

      fun rebuild (step, member) =
        case step of
          DefAxiomConjunctionLeft right =>
            boolSyntax.mk_conj (member, opaque right)
        | DefAxiomConjunctionRight left =>
            boolSyntax.mk_conj (opaque left, member)

      val (actual_member, path) = search ([(actual_conjunction, [])], [])
      val _ = substitution :=
        {redex = member_variable, residue = actual_member} :: !substitution
      val conjunction = List.foldl rebuild member_variable path
    in
      {schematic = boolSyntax.mk_disj
         (boolSyntax.mk_neg conjunction, member_variable),
       substitution = !substitution}
    end

  type def_axiom_schema_binding =
    {actual : term, schematic : term, tree_nodes : int}

  (* Build only the Boolean structure used by the clause derivation.  Each
     unrelated disjunct and conjunction leaf is an opaque schematic atom, so
     a large shared theory term is inspected only when it is a candidate for
     one of the complementary literals. *)
  fun def_axiom_clause_schema target =
    let
      val disjunction_nodes = ref 0
      val conjunction_nodes = ref 0
      val comparisons = ref 0
      val comparison_work = ref 0
      val next_id = ref 0

      fun add_work amount =
        (comparison_work := !comparison_work + amount;
         if !comparison_work <= max_def_axiom_atom_compare_work then ()
         else def_axiom_decline "def_axiom_conjunction_clause"
           "Boolean atom comparison work exceeds its structural bound")

      fun term_nodes actual = SmtResource.term_nodes_up_to
        max_def_axiom_atom_compare_nodes actual

      fun same_actual (left, left_nodes) (right, right_nodes) =
        (bounded_def_axiom_work comparisons
           max_def_axiom_boolean_comparisons "Boolean atom comparisons";
         if Portable.pointer_eq (left, right) then true
         else
           (add_work (left_nodes + right_nodes);
            left_nodes <= max_def_axiom_atom_compare_nodes andalso
            right_nodes <= max_def_axiom_atom_compare_nodes andalso
            Term.aconv left right))

      fun disjunction current entries =
        (bounded_def_axiom_work disjunction_nodes
           max_def_axiom_boolean_spine_nodes "disjunction spine";
         if boolSyntax.is_disj current then
           let
             val (left, right) = boolSyntax.dest_disj current
             val (left_shape, entries) = disjunction left entries
             val (right_shape, entries) = disjunction right entries
           in
             (DefAxiomDisjunctionNode (left_shape, right_shape), entries)
           end
         else
           let
             val id = !next_id
             val _ = next_id := id + 1
           in
             (DefAxiomDisjunctionLeaf id, (id, current) :: entries)
           end)

      fun conjunction current =
        (bounded_def_axiom_work conjunction_nodes
           max_def_axiom_boolean_spine_nodes "conjunction spine";
         if boolSyntax.is_conj current then
           let
             val (left, right) = boolSyntax.dest_conj current
             val (left_shape, left_leaves) = conjunction left
             val (right_shape, right_leaves) = conjunction right
           in
             (DefAxiomConjunctionNode (left_shape, right_shape),
              left_leaves @ right_leaves)
           end
         else (DefAxiomConjunctionLeaf, [current]))

      fun make_conjunction shape terms =
        case (shape, terms) of
          (DefAxiomConjunctionLeaf, term :: rest) => (term, rest)
        | (DefAxiomConjunctionNode (left, right), _) =>
            let
              val (left_term, rest) = make_conjunction left terms
              val (right_term, rest) = make_conjunction right rest
            in
              (boolSyntax.mk_conj (left_term, right_term), rest)
            end
        | _ => def_axiom_decline "def_axiom_conjunction_clause"
            "conjunction schema list has the wrong length"

      fun literal actual =
        if boolSyntax.is_neg actual then
          (true, boolSyntax.dest_neg actual)
        else (false, actual)

      val (disjunction_shape, reversed_entries) = disjunction target []
      val entries = List.rev reversed_entries

      fun prove_candidate (candidate_id, candidate) =
        let
          val (candidate_shape, leaves) = conjunction candidate
          val replacements = Array.array (!next_id, NONE : term option)
          val bindings = ref ([] : def_axiom_schema_binding list)
          val substitution = ref
            ([] : {redex : term, residue : term} list)

          fun matching_binding actual actual_nodes
              ({actual = saved, tree_nodes, ...} :
               def_axiom_schema_binding) =
            same_actual (actual, actual_nodes) (saved, tree_nodes)

          fun variable_for actual =
            let val actual_nodes = term_nodes actual
            in
              case List.find (matching_binding actual actual_nodes)
                  (!bindings) of
                SOME {schematic, ...} => schematic
              | NONE =>
                  let
                    val schematic = Term.genvar Type.bool
                    val binding =
                      {actual = actual, schematic = schematic,
                       tree_nodes = actual_nodes}
                  in
                    bindings := binding :: !bindings;
                    substitution :=
                      {redex = schematic, residue = actual} :: !substitution;
                    schematic
                  end
            end

          fun find_opposite negated base base_nodes =
            case List.find
                (fn (_, disjunct) =>
                  let val (other_negated, other_base) = literal disjunct
                  in
                    negated <> other_negated andalso
                    same_actual (base, base_nodes)
                      (other_base, term_nodes other_base)
                  end) entries of
              SOME result => result
            | NONE => def_axiom_decline "def_axiom_conjunction_clause"
                "a conjunction leaf has no complementary disjunct"

          fun set_replacement id schematic =
            case Array.sub (replacements, id) of
              NONE => Array.update (replacements, id, SOME schematic)
            | SOME previous =>
                if Term.aconv previous schematic then ()
                else def_axiom_decline "def_axiom_conjunction_clause"
                  "one disjunct has inconsistent complementary literals"

          fun make_leaf actual =
            let
              val (negated, base) = literal actual
              val base_nodes = term_nodes base
              val variable = variable_for base
              val schematic =
                if negated then boolSyntax.mk_neg variable else variable
              val complement =
                if negated then variable else boolSyntax.mk_neg variable
              val (opposite_id, _) =
                find_opposite negated base base_nodes
              val _ = set_replacement opposite_id complement
            in
              schematic
            end

          val schematic_leaves = List.map make_leaf leaves
          val (schematic_candidate, rest) =
            make_conjunction candidate_shape schematic_leaves
          val _ = List.null rest orelse
            raise ERR "def_axiom_conjunction_clause"
              "unused conjunction schema leaf"
          val _ = set_replacement candidate_id schematic_candidate

          fun opaque actual =
            let val variable = Term.genvar Type.bool
            in
              substitution := {redex = variable, residue = actual} ::
                !substitution;
              variable
            end

          fun make_disjunction shape =
            case shape of
              DefAxiomDisjunctionLeaf id =>
                (case Array.sub (replacements, id) of
                   SOME schematic => schematic
                 | NONE => opaque (Lib.assoc id entries))
            | DefAxiomDisjunctionNode (left, right) =>
                boolSyntax.mk_disj
                  (make_disjunction left, make_disjunction right)
          val schematic = make_disjunction disjunction_shape
        in
          {schematic = schematic, substitution = !substitution}
        end

      val candidates = List.filter (boolSyntax.is_conj o Lib.snd) entries
    in
      try_def_axiom_candidates prove_candidate candidates
    end

  fun instantiate_def_axiom_schematic target substitution theorem =
    let
      val _ = List.null (Thm.hyp theorem) orelse
        raise ERR "instantiate_def_axiom_schematic"
          "schematic theorem has hypotheses"
      val _ = Library.check_oracle_tags "Z3_ProofReplay"
        "def-axiom-structural" theorem
      val instantiated = Thm.INST substitution theorem
      val spine_nodes = ref 0
      val alpha_work = ref 0
      fun add_alpha_work amount =
        (alpha_work := !alpha_work + amount;
         if !alpha_work <= max_def_axiom_atom_compare_work then ()
         else raise SmtSkeletonProve.REANCHOR_LIMIT)
      fun small_alpha left right =
        let
          val left_nodes = SmtResource.term_nodes_up_to
            max_def_axiom_atom_compare_nodes left
          val right_nodes = SmtResource.term_nodes_up_to
            max_def_axiom_atom_compare_nodes right
          val _ = add_alpha_work (left_nodes + right_nodes)
        in
          if left_nodes <= max_def_axiom_atom_compare_nodes andalso
             right_nodes <= max_def_axiom_atom_compare_nodes then
            Thm.ALPHA left right
          else raise SmtSkeletonProve.REANCHOR_LIMIT
        end
      fun congruence left right child_theorems =
        let
          val theorem = SmtSkeletonProve.connective_congruence
            left child_theorems
        in
          Thm.TRANS (Thm.TRANS (Thm.REFL left) theorem) (Thm.REFL right)
        end
      fun visit left right =
        (bounded_def_axiom_work spine_nodes
           max_def_axiom_boolean_spine_nodes "Boolean transport spine";
         if Portable.pointer_eq (left, right) then Thm.REFL left
         else if boolSyntax.is_neg left andalso boolSyntax.is_neg right then
           congruence left right
             [visit (boolSyntax.dest_neg left) (boolSyntax.dest_neg right)]
         else if boolSyntax.is_conj left andalso
                 boolSyntax.is_conj right then
           let
             val (left1, left2) = boolSyntax.dest_conj left
             val (right1, right2) = boolSyntax.dest_conj right
           in
             congruence left right
               [visit left1 right1, visit left2 right2]
           end
         else if boolSyntax.is_disj left andalso
                 boolSyntax.is_disj right then
           let
             val (left1, left2) = boolSyntax.dest_disj left
             val (right1, right2) = boolSyntax.dest_disj right
           in
             congruence left right
               [visit left1 right1, visit left2 right2]
           end
         else small_alpha left right)
      val occurrence_equality = visit target (Thm.concl instantiated)
      val result = Thm.EQ_MP (Thm.SYM occurrence_equality) instantiated
      val _ = Portable.pointer_eq (Thm.concl result, target) orelse
        raise ERR "instantiate_def_axiom_schematic"
          "structural theorem lost the exact target occurrence"
    in
      result
    end

  fun def_axiom_skeleton_prove state target =
    (record_measured_target MeasuredDefAxiom target;
     SmtResource.with_resource_step_time
      "Skeleton" "z3-def-axiom"
      (fn target =>
        let
          fun trace_stage stage =
            if OS.Process.getEnv "HOL4_Z3_REPLAY_TRACE" = SOME "1" andalso
               !replay_completed_steps < 20 then
              (Feedback.HOL_MESG ("Z3 def-axiom: " ^ stage);
               TextIO.flushOut TextIO.stdOut)
            else ()
          val _ = trace_stage "measure"
          val _ = admitted_def_axiom_measure (fn _ => ()) target
          fun skeleton_prove () =
            let
              val _ = SmtResource.profile_phase
                "skeleton/ownership-ownerless" (fn () => ()) ()
              val cached = probe_def_axiom_cache target
              fun prove () =
                let
                  val _ = note_def_axiom_skeleton_attempt ()
                in
                  case profile "def-axiom(1)(skeleton-worker)"
                      (SmtSkeletonProve.with_node_cache_observer
                        (case !current_replay_measurement of
                           NONE => NONE
                         | SOME _ => SOME observe_skeleton_node_cache)
                        (fn () => SmtSkeletonProve.attempt_with_owners
                          def_axiom_skeleton_context
                          def_axiom_skeleton_owners
                          (SmtSkeletonProve.term_measure target) target)) () of
                    SmtSkeletonProve.Proved result =>
                      let
                        val theorem = #theorem result
                        val _ = record_skeleton_metrics (#metrics result)
                        val _ = insert_def_axiom_cache target theorem
                      in
                        theorem
                      end
                  | SmtSkeletonProve.Declined =>
                      raise ERR "z3_def_axiom" "checked skeleton declined"
                end
            in
              case cached of
                SOME theorem => theorem
              | NONE => prove ()
            end
          fun is_structural_decline function =
            List.exists (fn name => function = name)
              ["def_axiom_boolean_spine",
               "def_axiom_conjunction_member",
               "def_axiom_conjunction_clause"]
          fun structural_fallback action fallback =
            action ()
            handle SmtSkeletonProve.REANCHOR_LIMIT => fallback ()
                 | DEF_AXIOM_DECLINE (function, message) =>
                     if is_structural_decline function then fallback ()
                     else raise DEF_AXIOM_DECLINE (function, message)
                 | Feedback.HOL_ERR holerr =>
                     if SmtResource.is_resource_gate holerr then
                       raise Feedback.HOL_ERR holerr
                     else raise DEF_AXIOM_STRUCTURAL_UNEXPECTED
                       (Feedback.HOL_ERR holerr)
          fun structural_prove () =
            let
              fun skeleton () = profile "def-axiom(1d)(skeleton)"
                (fn () => (trace_stage "skeleton";
                  skeleton_prove ())) ()
              fun proforma () =
                (trace_stage "proforma";
                 Library.require_fastpath "Z3 def-axiom proforma" target
                  (profile "def-axiom(1c)(proforma)"
                    (Z3_ProformaThms.prove
                      Z3_ProformaThms.def_axiom_thms)) target)
                handle Feedback.HOL_ERR holerr =>
                  if SmtResource.is_resource_gate holerr then
                    raise Feedback.HOL_ERR holerr
                  else
                    (profile "def-axiom(1c2)(clause-frontier)"
                      (SmtSkeletonProve.clause_frontier_prove
                        max_def_axiom_boolean_spine_nodes) target
                     handle Feedback.HOL_ERR _ => skeleton ())
              fun direct () =
                let
                  fun prove_schema profile_name schema theorem_prove =
                    profile profile_name
                      (fn target =>
                        let
                          val {schematic, substitution} = schema target
                          val comparisons = ref 0
                          fun same_schematic (left, right) =
                            (bounded_def_axiom_work comparisons
                               max_def_axiom_boolean_comparisons
                               "schematic Boolean comparisons";
                             Term.aconv left right)
                        in
                          instantiate_def_axiom_schematic target substitution
                            (theorem_prove same_schematic schematic)
                        end) target
                  fun conjunction_clause () = structural_fallback
                    (fn () => (trace_stage "conjunction-clause";
                      prove_schema
                      "def-axiom(1b)(conjunction-clause)"
                      def_axiom_clause_schema
                      def_axiom_conjunction_clause))
                    proforma
                in
                  structural_fallback
                    (fn () => (trace_stage "conjunction-member";
                      prove_schema
                      "def-axiom(1a)(conjunction-member)"
                      def_axiom_member_schema
                      def_axiom_conjunction_member))
                    conjunction_clause
                end
            in
              direct ()
            end
        in
          structural_prove ()
        end) target)
    handle exn as Feedback.HOL_ERR holerr =>
      if SmtResource.is_resource_gate holerr then
        SmtResource.resolve_diagnostic_exception exn
          (fn () => capture_skeleton_obligation state target exn)
          (fn original => raise original)
      else raise exn

  fun bounded_taut_prove category case_id target =
    SmtResource.with_resource_step_time category case_id
      (fn target =>
        let
          val maximum = SmtResource.max_term_nodes_for category
          val observed = SmtResource.dag_nodes_up_to maximum target
          val _ = SmtResource.check_dag_size_with_limit
            category case_id maximum observed
        in
          tautLib.TAUT_PROVE target
        end) target

  fun bounded_conditional_word_prove category case_id target =
    let
      (* Splitting conditionals is exponential in their Boolean spine.
         This helper is a small finite-word rewrite rung; larger shared
         character DAGs stay on their dedicated bounded routes. *)
      val maximum = 128
      val _ = has_word_atom target orelse
        raise ERR "bounded_conditional_word_prove"
          "goal is outside the finite-word fragment"
      val _ = not (has_arith_atom target) orelse
        raise ERR "bounded_conditional_word_prove"
          "mixed arithmetic/word goal is outside this fragment"
      fun oversized_word subterm =
        wordsSyntax.is_word_type (Term.type_of subterm) andalso
        Arbnum.toInt (wordsSyntax.size_of subterm) > 8
        handle Overflow => true
      val _ = not (#found
          (term_contains_measure oversized_word target)) orelse
        raise ERR "bounded_conditional_word_prove"
          "conditional word width exceeds the admission bound"
      val _ = #found (term_contains_measure boolSyntax.is_cond target)
        orelse raise ERR "bounded_conditional_word_prove"
          "finite-word goal contains no conditional"
      val observed = SmtResource.dag_nodes_up_to maximum target
      val _ = observed <= maximum orelse
        raise ERR "bounded_conditional_word_prove"
          "conditional finite-word DAG exceeds the admission bound"
    in
      SmtResource.with_resource_step_time category case_id
        (fn target =>
          (SmtResource.check_resource_goal category case_id target;
           Tactical.prove (target,
             Tactical.REPEAT Tactic.COND_CASES_TAC THEN
             Tactical.REPEAT (POP_ASSUM MP_TAC) THEN
             Tactic.CONV_TAC blastLib.BBLAST_CONV))) target
    end

  fun def_axiom_guarded_conditional target =
    let
      fun trace_guard stage =
        if OS.Process.getEnv "HOL4_Z3_REPLAY_TRACE" = SOME "1" andalso
           !replay_completed_steps >= 550 then
          (Feedback.HOL_MESG ("Z3 guarded axiom: " ^ stage);
           TextIO.flushOut TextIO.stdOut)
        else ()
      val _ = trace_guard "begin"
      fun prove disjunct proposition =
        let
          val negated = boolSyntax.is_neg disjunct
          val condition =
            if negated then boolSyntax.dest_neg disjunct
            else disjunct
          val (left, right) = boolSyntax.dest_eq proposition
          fun candidate (conditional_on_left, conditional, other) =
            let
              val (guard, then_branch, else_branch) =
                boolSyntax.dest_cond conditional
              val _ = trace_guard "shape"
              val guard_matches =
                Portable.pointer_eq (guard, condition) orelse
                Term.aconv guard condition
              val branch =
                if negated then then_branch else else_branch
              val branch_matches = guard_matches andalso
                (Portable.pointer_eq (branch, other) orelse
                 Term.aconv branch other)
              val _ = trace_guard
                ("candidate guard=" ^ Bool.toString guard_matches ^
                 " branch=" ^ Bool.toString branch_matches)
            in
              if guard_matches andalso branch_matches then
                SOME (conditional_on_left, other,
                  then_branch, else_branch)
              else NONE
            end
          val candidates =
            (if boolSyntax.is_cond left then
               [(true, left, right)] else []) @
            (if boolSyntax.is_cond right then
               [(false, right, left)] else [])
          fun first_matching [] =
                raise ERR "def_axiom_guarded_conditional"
                  "disjunct does not guard an equal branch"
            | first_matching (next :: rest) =
                (case candidate next of
                   SOME selected => selected
                 | NONE => first_matching rest)
          val (conditional_on_left, other, then_branch, else_branch) =
            first_matching candidates
          val _ = trace_guard "matched"
          val p = Term.genvar Type.bool
          val x = Term.genvar (Term.type_of other)
          val y = Term.genvar (Term.type_of other)
          val schematic_conditional =
            boolSyntax.mk_cond (p,
              if negated then x else y,
              if negated then y else x)
          val schematic_equality =
            if conditional_on_left then
              boolSyntax.mk_eq (schematic_conditional, x)
            else boolSyntax.mk_eq (x, schematic_conditional)
          val schema_goal = boolSyntax.mk_disj
            (if negated then boolSyntax.mk_neg p else p,
             schematic_equality)
          val schema = Tactical.TAC_PROOF (([], schema_goal),
            Tactical.THEN (Tactic.BOOL_CASES_TAC p,
              bossLib.ASM_SIMP_TAC boolSimps.bool_ss []))
          val _ = trace_guard "schema-proved"
          val instantiated = Thm.INST
            [{redex = p, residue = condition},
             {redex = x, residue = other},
             {redex = y, residue =
                if negated then else_branch else then_branch}]
            schema
          val _ = trace_guard "instantiated"
        in instantiated end
      val (left, right) = boolSyntax.dest_disj target
      val theorem = prove left right
        handle Feedback.HOL_ERR _ =>
          let val symmetric = prove right left
          in
            Thm.EQ_MP
              (Drule.SPECL [right, left] boolTheory.DISJ_COMM)
              symmetric
          end
      val _ = Term.aconv (Thm.concl theorem) target orelse
        raise ERR "def_axiom_guarded_conditional"
          "schema endpoint mismatch"
    in theorem end

  fun rewrite_boolean_constant_schema target =
    let
      val (left, right) = boolSyntax.dest_eq target
      val (inner, outer, inner_on_left) =
        if boolSyntax.is_eq left then (left, right, true)
        else if boolSyntax.is_eq right then (right, left, false)
        else raise ERR "rewrite_boolean_constant_schema"
          "no inner Boolean equality"
      val (first, second) = boolSyntax.dest_eq inner
    in
      (* Reflexive equality is a kernel fact at every HOL type, including
         opaque theory sorts.  It is not a theory-specific FP obligation or
         an independent propositional atom. *)
      if Term.aconv outer boolSyntax.T andalso Term.aconv first second then
        let val theorem = Drule.EQT_INTRO (Thm.ALPHA first second) in
          if inner_on_left then theorem else Thm.SYM theorem
        end
      else let
      val (constant, proposition, constant_on_left) =
        if Term.aconv first boolSyntax.T orelse
           Term.aconv first boolSyntax.F then
          (first, second, true)
        else if Term.aconv second boolSyntax.T orelse
                Term.aconv second boolSyntax.F then
          (second, first, false)
        else raise ERR "rewrite_boolean_constant_schema"
          "inner equality has no Boolean constant"
      val _ = Term.type_of proposition = Type.bool orelse
        raise ERR "rewrite_boolean_constant_schema"
          "inner equality is not Boolean"
      val _ = Term.aconv outer
        (if Term.aconv constant boolSyntax.F then
           boolSyntax.mk_neg proposition else proposition) orelse
        raise ERR "rewrite_boolean_constant_schema"
          "outer proposition does not match"
      val variable = Term.genvar Type.bool
      val inner_schema =
        if constant_on_left then boolSyntax.mk_eq (constant, variable)
        else boolSyntax.mk_eq (variable, constant)
      val outer_schema =
        if Term.aconv constant boolSyntax.F then
          boolSyntax.mk_neg variable else variable
      val goal =
        if inner_on_left then
          boolSyntax.mk_eq (inner_schema, outer_schema)
        else boolSyntax.mk_eq (outer_schema, inner_schema)
      val schema = tautLib.TAUT_PROVE goal
      val theorem = Thm.INST
        [{redex = variable, residue = proposition}] schema
      val _ = Term.aconv (Thm.concl theorem) target orelse
        raise ERR "rewrite_boolean_constant_schema"
          "schema endpoint mismatch"
    in theorem end
    end

  fun rewrite_fp_sub_boolean_normal_form target =
    let
      val (left, right) = boolSyntax.dest_eq target
      val _ = boolSyntax.is_neg left andalso
        boolSyntax.is_neg right andalso
        boolSyntax.is_forall (boolSyntax.dest_neg left) andalso
        boolSyntax.is_forall (boolSyntax.dest_neg right) orelse
        raise ERR "rewrite_fp_sub_boolean_normal_form"
          "not a negated quantified rewrite"
      fun sub_operator term =
        let
          val (head, _) = boolSyntax.strip_comb term
          val {Thy, Name, ...} = Term.dest_thy_const head
        in Thy = "smtfloat" andalso Name = "smtfp_sub" end
        handle Feedback.HOL_ERR _ => false
      val _ = Lib.can (HolKernel.find_term sub_operator) target orelse
        raise ERR "rewrite_fp_sub_boolean_normal_form"
          "no floating-point subtraction"
    in
      SmtResource.with_resource_step_time
        "FloatingPoint" "z3-rewrite-fp-sub-boolean"
        (fn target =>
          (SmtResource.check_resource_goal
             "FloatingPoint" "z3-rewrite-fp-sub-boolean" target;
           Tactical.TAC_PROOF (([], target),
             Rewrite.REWRITE_TAC
               [smtfloatReplayRoundingTheory.smtfp_sub_add_negate,
                boolTheory.IMP_DISJ_THM,
                boolTheory.CONJ_ASSOC]))) target
    end

  fun rewrite_fp_pack_roundtrip target =
    let
      fun is_pack term =
        let
          val (head, _) = boolSyntax.strip_comb term
          val {Thy, Name, ...} = Term.dest_thy_const head
        in Thy = "smtfloat" andalso Name = "smtfp_pack_bv" end
        handle Feedback.HOL_ERR _ => false
      val pack = HolKernel.find_term is_pack target
      val (_, value) = Term.dest_comb pack
      val schema = smtfloatTheory.smtfp_bits_pack_bv
      val (_, quantified) = boolSyntax.dest_imp (Thm.concl schema)
      val (schema_value, _) = boolSyntax.dest_forall quantified
      val schema = Drule.INST_TY_TERM
        (Term.match_term schema_value value) schema
      val (_, quantified) = boolSyntax.dest_imp (Thm.concl schema)
      val (_, body) = boolSyntax.dest_forall quantified
      val schema_pack = HolKernel.find_term is_pack body
      val packed_word = Term.mk_var
        ("packed_word", Term.type_of schema_pack)
      val schema = Drule.INST_TY_TERM
        (Term.match_term packed_word pack) schema
      val schema = bossLib.SIMP_RULE (bossLib.srw_ss()) [] schema
      val theorem = Thm.SPEC value schema
      val theorem =
        if Term.aconv (Thm.concl theorem) target then theorem
        else Thm.SYM theorem
      val _ = Term.aconv (Thm.concl theorem) target orelse
        raise ERR "rewrite_fp_pack_roundtrip"
          "packed reconstruction does not match the target"
    in theorem end

  fun rewrite_fp_packed_atom target =
    let
      val (left, right) = boolSyntax.dest_eq target
      val (original_atom, _, _) =
        if SmtFpGraph.lower_atom_domain left then
          (left, right, true)
        else if SmtFpGraph.lower_atom_domain right then
          (right, left, false)
        else raise ERR "rewrite_fp_packed_atom"
          "no supported floating-point atom"
      val _ =
        case Lib.total boolSyntax.dest_eq original_atom of
          SOME (first, _) =>
            if Term.type_of first = Type.bool then ()
            else raise ERR "rewrite_fp_packed_atom"
              "floating-point value equality needs circuit replay"
        | NONE => ()
      fun is_fp_type ty =
        let val {Thy, Tyop, ...} = Type.dest_thy_type ty
        in Thy = "smtfloat" andalso Tyop = "smtfp" end
        handle Feedback.HOL_ERR _ => false
      val sources = ref ([] : Term.term list)
      val source_seen = ref (HOLset.empty Term.compare)
      fun collect term =
        if HOLset.member (!source_seen, term) then ()
        else
          (source_seen := HOLset.add (!source_seen, term);
           if is_fp_type (Term.type_of term) andalso
              not (Term.is_var term) then
             if List.exists (fn saved => Term.aconv saved term) (!sources)
             then () else sources := term :: !sources
           else List.app collect (SmtResource.term_children term))
      val _ = collect original_atom
      val source_variables =
        List.map (Term.genvar o Term.type_of) (!sources)
      val source_pairs = ListPair.zip (!sources, source_variables)
      val abstraction_memo = ref
        (Redblackmap.mkDict Term.compare :
          (Term.term, Term.term) Redblackmap.dict)
      fun abstract term =
        case Redblackmap.peek (!abstraction_memo, term) of
          SOME result => result
        | NONE =>
            let
              val result =
                case List.find
                    (fn (source, _) => Term.aconv source term)
                    source_pairs of
                  SOME (_, variable) => variable
                | NONE =>
                    if Term.is_comb term then
                      Term.mk_comb
                        (abstract (Term.rator term),
                         abstract (Term.rand term))
                    else term
              val _ = abstraction_memo :=
                Redblackmap.insert (!abstraction_memo, term, result)
            in result end
      val schematic_target = abstract target
      val shared_target =
        SmtResource.term_nodes_up_to
          SmtResource.max_bitblast_term_nodes schematic_target >
        SmtResource.max_bitblast_term_nodes
      val (left, right) = boolSyntax.dest_eq schematic_target
      val (atom, encoded, atom_on_left) =
        if SmtFpGraph.lower_atom_domain left then
          (left, right, true)
        else (right, left, false)
      fun packed term =
        let
          val (head, _) = boolSyntax.strip_comb term
          val {Thy, Name, ...} = Term.dest_thy_const head
        in Thy = "smtfloat" andalso Name = "smtfp_pack_bv" end
        handle Feedback.HOL_ERR _ => false
      val _ = Lib.can (HolKernel.find_term packed) encoded orelse
        raise ERR "rewrite_fp_packed_atom"
          "encoded side has no packed floating-point word"
      fun node_conversion term =
        if packed term then
          Conv.REWR_CONV smtfloatTheory.smtfp_pack_bv_def term
        else
          (SmtFpGraph.convert_word_projection term
           handle Conv.UNCHANGED =>
             if shared_target andalso
                SmtResource.term_nodes_up_to 256 term <= 256 andalso
                (wordsSyntax.is_word_extract term orelse
                 (case Lib.total boolSyntax.dest_eq term of
                    SOME (left, _) =>
                      wordsSyntax.is_word_type (Term.type_of left)
                  | NONE => false)) then
               simpLib.SIMP_CONV
                 (simpLib.++
                   (bossLib.srw_ss(), wordsLib.WORD_EXTRACT_ss)) []
                 term
             else raise Conv.UNCHANGED)
      fun phase name f x =
        if shared_target then
          SmtResource.with_resource_step_time
            "FloatingPoint" name f x
        else f x
      fun convert () =
        let
          val atom_theorem = phase "z3-fp-packed-atom-lower"
            SmtFpGraph.lower_atom atom
          val word_theorem =
            phase "z3-fp-packed-word-lower"
              (SmtWordGraph.normalize_with_node_conversion
                node_conversion) encoded
          val word_residue = boolSyntax.rhs (Thm.concl word_theorem)
          val simplified =
            if shared_target then Thm.REFL word_residue
            else
              (simpLib.SIMP_CONV
                (simpLib.++
                  (bossLib.srw_ss(), wordsLib.WORD_EXTRACT_ss)) []
                word_residue
               handle Conv.UNCHANGED => Thm.REFL word_residue)
          val encoded_theorem = Thm.TRANS word_theorem simplified
          val equality_head = Term.rator (Term.rator schematic_target)
          val normalized =
            if atom_on_left then Thm.MK_COMB
              (Thm.MK_COMB (Thm.REFL equality_head, atom_theorem),
               encoded_theorem)
            else Thm.MK_COMB
              (Thm.MK_COMB (Thm.REFL equality_head,
                 encoded_theorem), atom_theorem)
          val residue = boolSyntax.rhs (Thm.concl normalized)
          val source_facts =
            if shared_target then
              List.map
                (fn (source, variable) =>
                  let
                    val descriptor = phase "z3-fp-packed-source"
                      SmtFpGraph.represent source
                    val theorem = #representation descriptor
                    val fields = boolSyntax.rhs (Thm.concl theorem)
                  in (boolSyntax.mk_eq (variable, fields), theorem) end)
                source_pairs
            else []
          val antecedents = List.map Lib.fst source_facts
          val implication = boolSyntax.list_mk_imp
            (antecedents, residue)
          val proof =
            if shared_target then
              CPC_ProofReplay.prove_boolean_circuit implication
            else tautLib.TAUT_PROVE residue
          val assumptions = List.map Thm.ASSUME antecedents
          val residue_proved = Drule.LIST_MP assumptions proof
          val schematic = Thm.EQ_MP
            (Thm.SYM normalized) residue_proved
          val schematic = List.foldr
            (fn (fact, theorem) => Thm.DISCH fact theorem)
            schematic antecedents
          val substitutions = ListPair.mapEq
            (fn (source, variable) =>
              {redex = variable, residue = source})
            (!sources, source_variables)
          val instantiated = phase "z3-fp-packed-atom-instantiate"
            (Thm.INST substitutions) schematic
          val result = Drule.LIST_MP
            (List.map Lib.snd source_facts) instantiated
          val _ = CPC_ProofReplay.sharing_aware_aconv
            (Thm.concl result) target orelse
            raise ERR "rewrite_fp_packed_atom"
              "abstracted proof endpoint mismatch"
        in result end
    in
      if shared_target then
        let
          val nodes = SmtResource.dag_nodes_up_to
            (SmtResource.max_skeleton_replay_dag_nodes + 1)
            schematic_target
          val _ = SmtResource.check_dag_size_for
            "FloatingPoint" "z3-rewrite-fp-packed-atom" nodes
        in convert () end
      else SmtResource.with_resource_step_time
        "FloatingPoint" "z3-rewrite-fp-packed-atom"
        (fn target =>
          (SmtResource.check_resource_goal
             "FloatingPoint" "z3-rewrite-fp-packed-atom" target;
           convert ())) schematic_target
    end

  (* A Z3 definition axiom may be a shared Boolean circuit over word
     operations.  Normalize those operations by checked word theorems, then
     replay the remaining propositional circuit with a checked SAT proof.
     This keeps shared bit-vector structure intact instead of repeatedly
     splitting the same conditional branches. *)
  fun def_axiom_word_circuit target =
    let
      val maximum = SmtResource.max_skeleton_replay_dag_nodes
      val nodes = SmtResource.dag_nodes_up_to (maximum + 1) target
      val _ = nodes <= maximum andalso
        term_contains_type wordsSyntax.is_word_type target orelse
        raise ERR "def_axiom_word_circuit"
          "goal is outside the bounded word-circuit domain"
    in
      SmtResource.with_resource_step_time "BitVector"
        "z3-def-axiom-word-circuit"
        (fn target =>
          let
            val normalized = SmtWordGraph.normalize target
            val residue = boolSyntax.rhs (Thm.concl normalized)
            val circuit =
              CPC_ProofReplay.prove_boolean_circuit residue
            val theorem = Thm.EQ_MP (Thm.SYM normalized) circuit
            val _ = Term.aconv (Thm.concl theorem) target orelse
              raise ERR "def_axiom_word_circuit"
                "normalized proof endpoint mismatch"
          in theorem end) target
    end

  fun def_axiom_case_split target =
    Tactical.TAC_PROOF (([], target),
      Tactical.THEN
        (Tactical.REPEAT Tactic.COND_CASES_TAC,
         bossLib.ASM_SIMP_TAC boolSimps.bool_ss
           [boolTheory.EQ_SYM_EQ]))

  fun def_axiom_word_circuit_route target =
    (profile "def-axiom(2)(word-circuit)"
      def_axiom_word_circuit target)
    handle HolSatLib.SAT_cex _ =>
      raise ERR "def_axiom_word_circuit_route"
        "checked SAT abstraction declined"
         | Conv.UNCHANGED =>
      raise ERR "def_axiom_word_circuit_route"
        "word normalization left the goal unchanged"

  fun z3_def_axiom (state, t) =
    (* Recognize excluded-middle clauses from their Boolean spine before
       generic proforma matching.  This avoids traversing deeply shared
       character and bit-vector atoms merely to bind one proposition. *)
    (state, Library.gen_excluded_middle t)
    handle Feedback.HOL_ERR holerr =>
      if SmtResource.is_resource_gate holerr then
        raise Feedback.HOL_ERR holerr
      else
    (* Apply bounded structural definition-clause rules before abstracting
       arbitrary theory atoms into the generic checked-SAT skeleton.  All
       routes share the same admission and step-time gate. *)
    (state, profile "def-axiom(1)(bounded)"
      (def_axiom_skeleton_prove state) t)
    handle DEF_AXIOM_STRUCTURAL_UNEXPECTED exn => raise exn
         | Feedback.HOL_ERR holerr =>
      if SmtResource.is_resource_gate holerr then
        raise Feedback.HOL_ERR holerr
      else
    (state, def_axiom_word_circuit_route t)
    handle Feedback.HOL_ERR holerr =>
      if SmtResource.is_resource_gate holerr then
        raise Feedback.HOL_ERR holerr
      else
    (* Array-encoded Set literals appear in Z3's Tseitin clauses as a
       select of the parsed EMPTY/UNIV predicate.  Normalize those recorded
       const-array forms before the propositional def-axiom cases below. *)
    (state, SmtArrayProve.set_simp_prove t)
    handle Feedback.HOL_ERR holerr =>
      if SmtResource.is_resource_gate holerr then
        raise Feedback.HOL_ERR holerr
      else
    (* or (or ... p ...) (not p) *)
    (* or (or ... (not p) ...) p *)
    (state, Library.gen_excluded_middle t)
    handle Feedback.HOL_ERR holerr =>
      if SmtResource.is_resource_gate holerr then
        raise Feedback.HOL_ERR holerr
      else
    (* ~ALL_DISTINCT [x; y; z] \/ x <> y /\ x <> z /\ y <> z *)
    (* ~(ALL_DISTINCT [x; y; z] /\ T) \/ x <> y /\ x <> z /\ y <> z *)
    let
      val (l, r) = boolSyntax.dest_disj t
      val all_distinct = boolSyntax.dest_neg l
      val all_distinct_th = ALL_DISTINCT_CONV all_distinct
        handle Feedback.HOL_ERR _ =>
          let
            val all_distinct = Lib.fst (boolSyntax.dest_conj all_distinct)
            val all_distinct_th = ALL_DISTINCT_CONV all_distinct
          in
            Thm.TRANS (Thm.SPEC all_distinct AND_T) all_distinct_th
          end
      (* get rid of parentheses *)
      val l_eq_r = Thm.TRANS all_distinct_th (Drule.CONJUNCTS_AC
        (boolSyntax.rhs (Thm.concl all_distinct_th), r))
    in
      (state, Drule.IMP_ELIM (Lib.fst (Thm.EQ_IMP_RULE l_eq_r)))
    end
    handle Feedback.HOL_ERR holerr =>
      if SmtResource.is_resource_gate holerr then
        raise Feedback.HOL_ERR holerr
      else
      (state, def_axiom_case_split t)

  (* (!x. ?y. !z. P) = P *)
  fun z3_elim_unused (state, t) =
  let
    val (lhs, rhs) = boolSyntax.dest_eq t
    fun get_forall_thms term : term * thm * thm =
    let
      val (var, body) = boolSyntax.dest_forall term
      val th1 = Thm.DISCH term (Thm.SPEC var (Thm.ASSUME term))
      val th2 = Thm.DISCH body (Thm.GEN var (Thm.ASSUME body))
    in
      (body, th1, th2)
    end
    fun get_exists_thms term : term * thm * thm =
    let
      val (var, body) = boolSyntax.dest_exists term
      val th1 = Thm.DISCH term (Thm.CHOOSE (var, Thm.ASSUME term)
        (Thm.ASSUME body))
      val th2 = Thm.DISCH body (Thm.EXISTS (term, var) (Thm.ASSUME body))
    in
      (body, th1, th2)
    end
    fun strip_some_quants term =
    let
      val (body, th1, th2) =
        if boolSyntax.is_forall term then
          get_forall_thms term
        else
          get_exists_thms term
      val strip_th = Drule.IMP_ANTISYM_RULE th1 th2
    in
      if body ~~ rhs then
        strip_th  (* stripped enough quantifiers *)
      else
        Thm.TRANS strip_th (strip_some_quants body)
      end
  in
    (state, strip_some_quants lhs)
  end

  (* introduces a local hypothesis (which must be discharged by
     'z3_lemma' at some later point in the proof) *)
  fun hypothesis_char_next_route prove fallback =
    prove ()
    handle Feedback.HOL_ERR holerr =>
      if SmtResource.is_resource_gate holerr then
        raise Feedback.HOL_ERR holerr
      else fallback ()

  fun z3_hypothesis_theorem_with
      free_variable_present char_domain char_prove assume t =
    let
      fun fallback () = SmtResource.profile_phase
        "hypothesis/fallback-assume" assume t
      val open_hypothesis = SmtResource.profile_phase
        "hypothesis/free-variable-presence" free_variable_present t
    in
      if open_hypothesis then fallback ()
      else
        let
          val character_domain = SmtResource.profile_phase
            "hypothesis/char-domain-admission" char_domain t
        in
          if character_domain then
            hypothesis_char_next_route
              (fn () => SmtResource.profile_phase
                "hypothesis/char-proof" char_prove t)
              fallback
          else fallback ()
        end
    end

  fun z3_hypothesis_theorem t =
    z3_hypothesis_theorem_with
      Term.has_free_vars SmtStringProve.char_word_expansion_domain
      SmtStringProve.char_prove Thm.ASSUME t

  fun z3_hypothesis (state, t) =
      (state, z3_hypothesis_theorem t)

  (* `apply-def` unfolds a name introduced by `intro-def`.

     Z3 documents this rule as deriving ``F ~ n`` from a proof that ``n`` is a
     name for ``F``.  This parser represents equivalence modulo naming (``~``)
     as HOL equality, and `z3_intro_def` records the underlying definitional
     equality as a hypothesis. *)
  fun z3_apply_def (state, thm, t) =
  let
    fun oriented_def def =
      let
        val def_thm = Thm.ASSUME def
      in
        if Thm.concl def_thm ~~ t then
          def_thm
        else
          let val sym_def_thm = Thm.SYM def_thm
          in
            if Thm.concl sym_def_thm ~~ t then
              sym_def_thm
            else
              raise ERR "z3_apply_def" "definition has wrong orientation"
          end
      end
    val def_thm = Lib.tryfind oriented_def (HOLset.listItems (Thm.hypset thm))
  in
    (state, def_thm)
  end

  (*   ... |- ~p
     ------------
     ... |- p = F *)
  fun z3_iff_false (state, thm, _) =
    (state, Drule.EQF_INTRO thm)

  (*   ... |- p
     ------------
     ... |- p = T *)
  fun z3_iff_true (state, thm, _) =
    (state, Thm.MP (Thm.SPEC (Thm.concl thm) VALID_IFF_TRUE) thm)

  (* `intro-def` introduces a name for a term.

     `t` will be in one of the following schematic forms:

     1. name = term

     2. ~name \/ term

     3. (name \/ ~term) /\ (~name \/ term)

     ... or, when the term is of the form `if cond then t1 else t2`:

     4. (~cond \/ (name = t1)) /\ (cond \/ (name = t2))

     We then instantiate the following theorem:

     name = term |- t

     The introduced assumption is added to a set of hypotheses (i.e. the set
     of introduced definitions) stored in `state`. Since the variable names
     used in these definitions are local names introduced by Z3 for the
     purposes of completing the proof and should not otherwise be relevant in
     either the remaining hypotheses or the conclusion of the final theorem,
     we can remove all such definitions at the end of the proof.

     We must take an additional precaution: if `term` is a Z3-defined variable
     and it is "smaller" than `name`, then we must actually return the theorem:

     term = name |- t

     This is done to avoid ending up with circular definitions in the final
     theorem. *)

  (* A :lambda-def axiom is printed pointwise, while replay records the
     underlying function definition.  HOL's first-order matcher deliberately
     refuses to instantiate a schematic function with a term containing the
     matched binders, so derive every binder arity by iteration.  Repeated
     AP_THM followed by beta is the kernel derivation underlying the
     corresponding FUN_EQ_THM instance. *)
  fun z3_intro_def_lambda (state, t) =
  let
    val (vars, body) = boolSyntax.strip_forall t
    val _ = if List.null vars then raise ERR "z3_intro_def_lambda"
      "pointwise axiom has no binders" else ()
    val (lhs, rhs) = boolSyntax.dest_eq body
    fun named_application side =
      let
        val (name, args) = strip_comb side
      in
        if Term.is_var name andalso
           HOLset.member (#var_set state, name) andalso
           Lib.list_eq Term.aconv args vars
        then SOME name
        else NONE
      end
    val (name, term, name_on_left) =
      case (named_application lhs, named_application rhs) of
        (SOME name, _) => (name, rhs, true)
      | (_, SOME name) => (name, lhs, false)
      | _ => raise ERR "z3_intro_def_lambda"
          ("unsupported :lambda-def intro-def shape: " ^
           "pointwise axiom does not define a Z3 name")
    val residue = Term.list_mk_abs (vars, term)
    val def = boolSyntax.mk_eq (name, residue)
    val def_thm = Thm.ASSUME def
    val applied = List.foldl (fn (var, thm) => Thm.AP_THM thm var)
      def_thm vars
    val applied_rhs = Lib.snd (boolSyntax.dest_eq (Thm.concl applied))
    val beta = Conv.TOP_DEPTH_CONV Thm.BETA_CONV applied_rhs
    val pointwise = Thm.TRANS applied beta
    val pointwise = if name_on_left then pointwise else Thm.SYM pointwise
    val inst_thm = List.foldr (fn (var, thm) => Thm.GEN var thm)
      pointwise vars
    val _ = if Thm.concl inst_thm ~~ t then ()
      else raise ERR "z3_intro_def_lambda"
        "derived :lambda-def has the wrong conclusion"
  in
    (state_define state [def], inst_thm)
  end

  fun z3_intro_def_general (state, target) =
  let
    val names = List.filter (fn variable =>
      HOLset.member (#var_set state, variable)) (Term.free_vars target)
    fun contains variable term =
      List.exists (Term.aconv variable) (Term.free_vars term)
    fun orient (name, residue) =
      if Library.is_def_oriented (#var_set state) (name, residue) then
        boolSyntax.mk_eq (name, residue)
      else
        boolSyntax.mk_eq (residue, name)
    fun prove_definition (name, residue) =
      let
        val definition = orient (name, residue)
        val condition =
          let
            val (left, right) = boolSyntax.dest_eq definition
          in
            case Lib.total boolSyntax.dest_cond right of
              SOME (condition, _, _) => SOME condition
            | NONE =>
                case Lib.total boolSyntax.dest_cond left of
                  SOME (condition, _, _) => SOME condition
                | NONE => NONE
          end
        val tactic =
          case condition of
            SOME condition =>
              Tactical.THEN
                (Tactic.ASM_CASES_TAC condition,
                 bossLib.ASM_SIMP_TAC boolSimps.bool_ss
                   [boolTheory.EQ_SYM_EQ])
          | NONE =>
              Tactical.THEN
                (Tactical.REPEAT Tactic.COND_CASES_TAC,
                 bossLib.ASM_SIMP_TAC boolSimps.bool_ss
                   [boolTheory.EQ_SYM_EQ])
        val theorem = Tactical.TAC_PROOF (([definition], target),
          tactic)
      in
        (state_define state [definition], theorem)
      end
    fun ordinary_candidates name =
      List.map (fn residue => (name, residue))
        (List.filter (fn residue =>
          Type.compare (Term.type_of residue, Term.type_of name) = EQUAL andalso
          not (Term.aconv residue name) andalso not (contains name residue))
          (Library.subterms target))
    fun equality_with_name name equation =
      let val (left, right) = boolSyntax.dest_eq equation in
        if Term.aconv left name andalso not (contains name right) then right
        else if Term.aconv right name andalso not (contains name left) then left
        else raise ERR "z3_intro_def_general" "equality has another name"
      end
    fun conditional_candidate name =
      let
        val (first, second) = boolSyntax.dest_conj target
        val (first_guard, first_equality) = boolSyntax.dest_disj first
        val (second_guard, second_equality) = boolSyntax.dest_disj second
        val condition = boolSyntax.dest_neg first_guard
        val _ = Term.aconv condition second_guard orelse
          raise ERR "z3_intro_def_general" "conditional guards differ"
        val then_value = equality_with_name name first_equality
        val else_value = equality_with_name name second_equality
      in
        (name, boolSyntax.mk_cond (condition, then_value, else_value))
      end
    val candidates = List.concat (List.map (fn name =>
      (conditional_candidate name :: ordinary_candidates name)
      handle Feedback.HOL_ERR _ => ordinary_candidates name) names)
  in
    Lib.tryfind prove_definition candidates
  end

  fun z3_intro_def (args as (_, t)) =
    if boolSyntax.is_forall t then z3_intro_def_lambda args
    else z3_intro_def_general args
      handle Feedback.HOL_ERR holerr =>
        raise ERR "z3_intro_def"
          ("general intro-def reconstruction failed: " ^
           Feedback.message_of holerr)

  (*  [l1, ..., ln] |- F
     --------------------
     |- ~l1 \/ ... \/ ~ln

     'z3_lemma' could be implemented (essentially) by a single call to
     'TAUT_PROVE'.  The (less general) implementation below, however,
     is considerably faster. *)
  fun z3_lemma (state, thm, t) =
  let
    fun prove_literal maybe_no_hyp (th, lit) =
    let
      val (is_neg, neg_lit) = (true, boolSyntax.dest_neg lit)
        handle Feedback.HOL_ERR _ => (false, boolSyntax.mk_neg lit)
    in
      if maybe_no_hyp orelse HOLset.member (Thm.hypset th, neg_lit) then
        let
          val concl = Thm.concl th
          val th1 = Thm.DISCH neg_lit th
          val p = Term.mk_var ("p", Type.bool)
          val q = Term.mk_var ("q", Type.bool)
        in
          if is_neg then (
            if Feq concl then
              (* [...] |- ~neg_lit *)
              Thm.NOT_INTRO th1
            else
              (* [...] |- ~neg_lit \/ concl *)
              Thm.MP (Thm.INST [p |-> neg_lit, q |-> concl] IMP_DISJ_1) th1
          ) else
            if Feq concl then
              (* [...] |- lit *)
              Thm.MP (Thm.SPEC lit IMP_FALSE) th1
            else
              (* [...] |- lit \/ concl *)
              Thm.MP (Thm.INST [p |-> lit, q |-> concl] IMP_DISJ_2) th1
        end
      else
        raise ERR "z3_lemma" ""
    end
    fun prove (th, disj) =
      prove_literal false (th, disj)
        handle Feedback.HOL_ERR _ =>
          let
            val (l, r) = boolSyntax.dest_disj disj
          in
            (* We do NOT break 'l' apart recursively (because that would be
               slightly tricky to implement, and require associativity of
               disjunction).  Thus, 't' must be parenthesized to the right
               (e.g., "l1 \/ (l2 \/ l3)"). *)
            prove_literal true (prove (th, r), l)
          end
  in
    (state, prove (thm, t))
  end

  val conversion_equal = Library.conversion_equal "conversion_equal"

  val beta_equal = conversion_equal Thm.BETA_CONV
  val eta_equal = conversion_equal Drule.ETA_CONV

  (* |- l1 = r1  ...  |- ln = rn
     ----------------------------
     |- f l1 ... ln = f r1 ... rn

     C1 also exercises this rule below abstractions.  The ABS branch keeps the
     binder explicit, while beta and eta are closing rungs after structural
     application congruence has failed. *)
  (* Congruence below a lambda: `|- (\x. lbody) = (\x. rbody)` from a proof of
     `|- lbody = rbody`.  Both binders are alpha-converted to a fresh variable
     first, so a free variable on either side cannot be captured.  `prove_body`
     supplies the body equality. *)
  fun abs_congruence prove_body (l, r) =
  let
    val (lvar, _) = Term.dest_abs l
    val (rvar, _) = Term.dest_abs r
    val _ = if Term.type_of lvar = Term.type_of rvar then ()
      else raise ERR "abs_congruence" "lambda binder type mismatch"
    val var =
      if not (List.exists (Term.term_eq lvar) (Term.free_vars r)) then
        lvar
      else if not (List.exists (Term.term_eq rvar) (Term.free_vars l)) then
        rvar
      else
        Term.genvar (Term.type_of lvar)
    val lalpha = if Term.term_eq lvar var then Thm.REFL l
      else Drule.ALPHA_CONV var l
    val ralpha = if Term.term_eq rvar var then Thm.REFL r
      else Drule.ALPHA_CONV var r
    val (_, lbody) = Term.dest_abs
      (Lib.snd (boolSyntax.dest_eq (Thm.concl lalpha)))
    val (_, rbody) = Term.dest_abs
      (Lib.snd (boolSyntax.dest_eq (Thm.concl ralpha)))
    val body_thm = prove_body (lbody, rbody)
  in
    Thm.TRANS lalpha (Thm.TRANS (Thm.ABS var body_thm) (Thm.SYM ralpha))
  end

  fun monotonicity_prove (thms, t) =
  let
    val l_r_thms = List.map
      (fn thm => (boolSyntax.dest_eq (Thm.concl thm), thm)) thms
    fun from_premise (l, r) =
      Lib.tryfind (fn ((l', r'), thm) =>
        Thm.TRANS (Thm.ALPHA l l') (Thm.TRANS thm (Thm.ALPHA r' r))
          handle Feedback.HOL_ERR _ =>
            Thm.TRANS (Thm.ALPHA l r')
              (Thm.TRANS (Thm.SYM thm) (Thm.ALPHA l' r))) l_r_thms
    fun abs_equal (l, r) = abs_congruence make_equal (l, r)
    and comb_equal (l, r) =
      let
        val (l_op, l_arg) = Term.dest_comb l
        val (r_op, r_arg) = Term.dest_comb r
      in
        Thm.MK_COMB (make_equal (l_op, r_op), make_equal (l_arg, r_arg))
      end
    and make_equal (l, r) =
      Thm.ALPHA l r
      handle Feedback.HOL_ERR _ => from_premise (l, r)
      handle Feedback.HOL_ERR _ => abs_equal (l, r)
      handle Feedback.HOL_ERR _ => comb_equal (l, r)
      handle Feedback.HOL_ERR _ => beta_equal (l, r)
      handle Feedback.HOL_ERR _ => eta_equal (l, r)
    val (l, r) = boolSyntax.dest_eq t
  in
    make_equal (l, r)
    handle Feedback.HOL_ERR _ =>
      (* Z3 also labels the injectivity of seq.unit followed by Char
         repacking as monotonicity.  The sequence characters in this schema
         are bounded by construction, so use the checked injectivity bridge
         rather than treating the premise as a congruence equality. *)
      Lib.tryfind (fn premise =>
        let
          fun apply theorem =
            let val result = Drule.MATCH_MP
              smtstringz3Theory.seq_unit_nth_i_word18_inj theorem
            in
              if Term.aconv (Thm.concl result) t then result
              else if Term.aconv (Thm.concl (Thm.SYM result)) t then
                Thm.SYM result
              else raise ERR "monotonicity_prove"
                "seq.unit injectivity conclusion mismatch"
            end
        in
          apply premise handle Feedback.HOL_ERR _ => apply (Thm.SYM premise)
        end) thms
    handle Feedback.HOL_ERR _ =>
      (* surprisingly, 'l' is sometimes of the form ``x /\ y ==> z``
         and must be transformed into ``x ==> y ==> z`` before any
         of the theorems in 'thms' can be applied - this is arguably
         a bug in Z3 (2.11) *)
      let
        val (xy, z) = boolSyntax.dest_imp l
        val (x, y) = boolSyntax.dest_conj xy
        val var_names = ["p", "q", "r"]
        val redexes = List.map (fn v => Term.mk_var (v, Type.bool)) var_names
        val substs = List.map Lib.|-> (ListPair.zip (redexes, [x, y, z]))
        val th1 = Thm.INST substs AND_IMP_INTRO_SYM
        val l' = Lib.snd (boolSyntax.dest_eq (Thm.concl th1))
      in
        Thm.TRANS th1 (make_equal (l', r))
      end
  end

  fun z3_monotonicity (state, thms, t) =
    (state,
     if SmtRegLanProve.is_equiv t orelse
        List.exists (SmtRegLanProve.is_equiv o Thm.concl) thms then
       SmtRegLanProve.congruence thms t
     else monotonicity_prove (thms, t))

  fun z3_mp (state, thm1, thm2, t) =
    (state, Thm.MP thm2 thm1 handle Feedback.HOL_ERR _ => Thm.EQ_MP thm2 thm1)

  (* `z3_mp_eq` implements the inference rule corresponding to `Thm.EQ_MP` *)
  fun z3_mp_eq (state, thm1, thm2, t) =
    (state, Thm.EQ_MP thm2 thm1)

  (* `z3_nnf_neg` creates a proof for a negative NNF step.

     The structural rung rewrites with Boolean/quantifier NNF theorems and
     premise equivalences. METIS remains only as a profiled last resort. *)
  fun z3_nnf_neg (state, thms, t) =
    (state, nnf_prove (thms, t))

  (* `z3_nnf_pos` creates a proof for a positive NNF step.

     The structural rung rewrites with Boolean/quantifier NNF theorems and
     premise equivalences. METIS remains only as a profiled last resort. *)
  fun z3_nnf_pos (state, thms, t) =
    (state, nnf_prove (thms, t))

  (* proof-bind records exactly which free variables in a pointwise premise
     are bound by the surrounding NNF step.  Keep the pointwise theorem for
     ordinary rewriting and add its checked forall congruence; ABS/FORALL_EQ
     rejects any attempt to capture a variable occurring in a hypothesis. *)
  fun z3_nnf_bound z3_nnf (state, bound_thms, t) =
  let
    (* The congruence is an extra rewrite, not a precondition: a premise that
       is not a boolean equation, or whose binder occurs in its hypotheses,
       still feeds the rungs the NNF machinery is built around, so an
       unliftable premise must not abort the whole step. *)
    fun lift ([], thm) = [thm]
      | lift (vars, thm) =
          let
            val lifted = List.foldr
              (fn (var, result) => Drule.FORALL_EQ var result) thm vars
          in
            [thm, lifted]
          end
          handle Feedback.HOL_ERR _ => [thm]
    val thms = List.concat (List.map lift bound_thms)
  in
    z3_nnf (state, thms, t)
  end

  (* The C1 HO corpus uses only nnf-pos.  Existing 4.15 FO certificates also
     put proof-bind below nnf-neg, so retain the same checked lifting there to
     avoid regressing the pre-existing replay surface. *)
  val z3_nnf_neg_bound = z3_nnf_bound z3_nnf_neg
  val z3_nnf_pos_bound = z3_nnf_bound z3_nnf_pos

  (* ~(... \/ p \/ ...)
     ------------------
             ~p         *)
  fun z3_not_or_elim (state, thm, t) =
  let
    val (is_neg, neg_t) = (true, boolSyntax.dest_neg t)
      handle Feedback.HOL_ERR _ =>
        (false, boolSyntax.mk_neg t)
    val disj = boolSyntax.dest_neg (Thm.concl thm)
    (* neg_t |- disj *)
    val th1 = Library.disj_intro (Thm.ASSUME neg_t, disj)
    (* |- ~disj ==> ~neg_t *)
    val th1 = Drule.CONTRAPOS (Thm.DISCH neg_t th1)
    (* |- ~neg_t *)
    val th1 = Thm.MP th1 thm
  in
    (state, if is_neg then th1 else Thm.MP (Thm.SPEC t NOT_NOT_ELIM) th1)
  end

  (*
     ------------------------------------------  QUANT_INST [u1,...,un]
       |- ~(!x1...xn. t) \/ t[u1/x1]...[un/xn]
  *)
  fun z3_quant_inst (state, terms, t) =
  let
    val t1 = Lib.fst (boolSyntax.dest_disj t)
    val t2 = boolSyntax.dest_neg t1
    val p_term = Term.mk_var ("p", Type.bool)
    val thm1 = Thm.INST [p_term |-> t2] HolSmtTheory.NOT_P_OR_P
    val thm2 = Thm.ASSUME t1
    val thm3_quant = Thm.ASSUME t2
    val thm3 = Drule.SPECL terms thm3_quant
    val thm = Drule.DISJ_CASES_UNION thm1 thm2 thm3
    (* The following is a quick workaround for the following Z3 issue:
       https://github.com/Z3Prover/z3/issues/7154
       The fix seems to be scheduled to be released in the Z3 version after
       v4.12.6. *)
    val thm' =
      if Thm.concl thm !~ t then
        metis_prove ([thm], t)
      else
        thm
  in
    (state, thm')
  end

  (*                     P = Q
     ---------------------------------------------
     (!x. ?y. !z. P x y z) = (!a. ?b. !c. Q a b c)

     The proof-bind variables are the binders introduced by this inference.
     Target binders determine only their logical kind; their variables are
     alpha-renamed to the annotation before rigidly checking the pointwise
     premise. *)
  fun quant_intro_annotation_mismatch detail =
    raise ERR "quant_intro_annotation_mismatch"
      ("quant_intro_annotation_mismatch: quant-intro proof-bind " ^
       "annotation mismatch: " ^ detail)

  fun z3_quant_intro (state, annotation, thm, t) =
  let
    datatype binder_kind = ForallBinder | ExistsBinder | AbsBinder

    (* Z3's quant-intro also introduces lambda binders for higher-order
       sequence functions. *)
    fun dest_binder term : (binder_kind * term * term) option =
      if boolSyntax.is_forall term then
        let val (var, body) = boolSyntax.dest_forall term
        in SOME (ForallBinder, var, body) end
      else if boolSyntax.is_exists term then
        let val (var, body) = boolSyntax.dest_exists term
        in SOME (ExistsBinder, var, body) end
      else if Term.is_abs term then
        let val (var, body) = Term.dest_abs term
        in SOME (AbsBinder, var, body) end
      else
        NONE

    fun kind_name ForallBinder = "forall"
      | kind_name ExistsBinder = "exists"
      | kind_name AbsBinder = "lambda"

    fun same_kind (ForallBinder, ForallBinder) = true
      | same_kind (ExistsBinder, ExistsBinder) = true
      | same_kind (AbsBinder, AbsBinder) = true
      | same_kind _ = false

    (* Peel exactly the annotated block and rename its target variables to
       the proof-bind variables.  This is recursive over the annotation, so
       neither supported binder forms nor arity depend on corpus examples. *)
    fun peel side term =
      let
        fun recurse [] body kinds = (List.rev kinds, body)
          | recurse (annotated :: rest) body kinds =
              (case dest_binder body of
                NONE => quant_intro_annotation_mismatch
                  (side ^ " has fewer binders than its annotation")
              | SOME (kind, target, residue) =>
                  if Type.compare
                      (Term.type_of annotated, Term.type_of target) = EQUAL
                  then recurse rest
                    (Term.subst [target |-> annotated] residue)
                    (kind :: kinds)
                  else quant_intro_annotation_mismatch
                    (side ^ " binder type differs from its annotation"))
      in
        recurse annotation term []
      end

    fun check_kinds [] = ()
      | check_kinds ((left, right) :: rest) =
          if same_kind (left, right) then check_kinds rest
          else quant_intro_annotation_mismatch
            ("conclusion binder kinds differ (" ^ kind_name left ^
             " versus " ^ kind_name right ^ ")")

    (* Replace H[v1,...,vn] by its universal closure as a hypothesis.  The
       closure still entails H at the current variables, but none of those
       variables remains free in the hypotheses seen by ABS/FORALL_EQ/
       EXISTS_EQ. *)
    fun close_hypothesis hyp result =
      let
        val captured = List.filter (fn var => Term.free_in var hyp) annotation
      in
        if List.null captured then result
        else
          let
            val closed = boolSyntax.list_mk_forall (captured, hyp)
            val instance = Drule.SPECL captured (Thm.ASSUME closed)
          in
            Drule.PROVE_HYP instance result
          end
      end

    fun add_binder (ForallBinder, var) result =
          Drule.FORALL_EQ var result
      | add_binder (ExistsBinder, var) result =
          Drule.EXISTS_EQ var result
      | add_binder (AbsBinder, var) result = Thm.ABS var result

    val _ = if List.null annotation then
        quant_intro_annotation_mismatch "annotation is empty"
      else if List.all Term.is_var annotation then ()
      else quant_intro_annotation_mismatch
        "annotation contains a non-variable binder"
    val (lhs, rhs) = boolSyntax.dest_eq t
      handle Feedback.HOL_ERR _ => quant_intro_annotation_mismatch
        "conclusion is not an equality"
    val (lhs_kinds, annotated_lhs) = peel "left conclusion" lhs
    val (rhs_kinds, annotated_rhs) = peel "right conclusion" rhs
    val _ = check_kinds (ListPair.zip (lhs_kinds, rhs_kinds))
    val (premise_lhs, premise_rhs) = boolSyntax.dest_eq (Thm.concl thm)
      handle Feedback.HOL_ERR _ => quant_intro_annotation_mismatch
        "pointwise premise is not an equality"
    val _ = if premise_lhs ~~ annotated_lhs then ()
      else quant_intro_annotation_mismatch
        ("annotated left conclusion body is not alpha-equal to the " ^
         "pointwise premise")
    val _ = if premise_rhs ~~ annotated_rhs then ()
      else quant_intro_annotation_mismatch
        ("annotated right conclusion body is not alpha-equal to the " ^
         "pointwise premise")
    val thm = List.foldl
      (fn (hyp, result) => close_hypothesis hyp result) thm (Thm.hyp thm)
    val _ = if List.exists
        (fn hyp => List.exists (fn var => Term.free_in var hyp) annotation)
        (Thm.hyp thm)
      then raise ERR "z3_quant_intro"
        "an annotated binder remains free in a premise hypothesis"
      else ()
    val thm = List.foldr
      (fn (binder, result) => add_binder binder result) thm
      (ListPair.zip (lhs_kinds, annotation))
    (* rename variables on rhs if necessary *)
    val (_, intermediate_rhs) = boolSyntax.dest_eq (Thm.concl thm)
    val thm = Thm.TRANS thm (Thm.ALPHA intermediate_rhs rhs)
  in
    (state, thm)
  end

  (* A proof for `R t t`, where R is a reflexive relation. The only `R` that are
     used are equivalence modulo namings, equality and equivalence, i.e. `~`,
     `=` or `iff`, all represented in HOL4 terms as `boolSyntax.mk_eq`. *)
  fun z3_refl (state, t) =
  if SmtRegLanProve.is_equiv t then
    let val (left, right) = SmtRegLanProve.dest_equiv t in
      if Term.aconv left right then (state, SmtRegLanProve.refl left)
      else raise ERR "z3_refl" "regular-language endpoints differ"
    end
  else let
    val (lhs, rhs) = boolSyntax.dest_eq t
  in
    (state, Thm.ALPHA lhs rhs)
  end

  fun word_arith_prove target =
    Drule.EQT_ELIM (wordsLib.WORD_ARITH_CONV target)
      handle Conv.UNCHANGED => raise ERR "word_arith_prove" "unchanged"

  (* A counterexample means only that this decision procedure cannot prove
     the current rewrite.  Normalize that signal to the ladder's ordinary
     HOL_ERR failure so the next procedure (and, after BBLAST, the existing
     arithmetic route) still gets a chance. *)
  fun word_decider_attempt name prove target =
    prove target
      handle HolSatLib.SAT_cex _ =>
        raise ERR name "word decision procedure found a counterexample"
           | HolSatLib.SAT_satisfiable _ =>
        raise ERR name "word decision procedure found a counterexample"

  fun bv_resource_prove_after_admission case_id prove target =
    SmtResource.with_resource_step_time "BitVector" case_id
      (fn target =>
        (SmtResource.check_resource_goal "BitVector" case_id target;
         prove target)) target

  fun bv_resource_prove case_id prove target =
    (require_bv_family case_id target;
     bv_resource_prove_after_admission case_id prove target)

  fun bv_next_rung first second target =
    first target
    handle Feedback.HOL_ERR holerr =>
      if SmtResource.is_resource_gate holerr then
        raise Feedback.HOL_ERR holerr
      else
        second target

  fun word_decide_raw target =
    (* E1(a): BBLAST decides the finite bit-vector fragment. *)
    profile "word-decide(1)(BBLAST)"
      (word_decider_attempt "word_decide(BBLAST)"
        (Feedback.trace ("print blast counterexamples", 0)
          blastLib.BBLAST_PROVE)) target

  fun word_decide target =
    bv_resource_prove "word-decide" word_decide_raw target

  fun occurring_translation_definitions definitions target =
    List.filter
      (fn definition =>
        let
          val head = SmtLib.emitted_definition_head definition
          fun matches subterm =
            if Term.is_const head andalso Term.is_const subterm then
              Term.same_const head subterm
            else
              subterm ~~ head
        in
          #found (term_contains_measure matches target)
        end)
      definitions

  (* A definition can admit the BV rewrite rung only when its registered,
     kernel-checked unfolding itself exposes the word family.  Merely
     occurring in the target is not enough: integer totalizations, for
     example, are emitted definitions but do not make an integer goal BV. *)
  fun definition_exposes_bv_family definition =
    has_word_atom (Thm.concl
      (SmtLib.emitted_definition_theorem definition))

  datatype bv_rewrite_route =
      DirectBV of SmtLib.emitted_definition list
    | LoweredBV
    | DefinedBV of SmtLib.emitted_definition list
    | OutsideBV

  fun classify_bv_rewrite direct_bv lowered_bv definitions target =
    let
      val occurring = List.filter definition_exposes_bv_family
        (occurring_translation_definitions definitions target)
    in
      if direct_bv target then DirectBV occurring
      else if lowered_bv target then LoweredBV
      else if List.null occurring then OutsideBV
      else DefinedBV occurring
    end

  (* One resource envelope owns the complete rewrite(17) operation: both
     size checks, the kernel normalization, and the final BBLAST.  Filtering
     definitions before entering this boundary prevents unrelated emitted
     definitions from admitting or charging a non-BV rewrite. *)
  fun rewrite17_under_budget normalize decide definitions target =
    let
      val theorems = List.map SmtLib.emitted_definition_theorem definitions
      val _ = not (List.null definitions) orelse
        raise ERR "rewrite17_under_budget"
          "translation emitted no definitional symbols"
      val normalization = normalize theorems target
      val (normalization_lhs, normalized) =
        boolSyntax.dest_eq (Thm.concl normalization)
      val _ = normalization_lhs ~~ target orelse
        raise ERR "rewrite17_under_budget"
          "normalization theorem has the wrong left-hand side"
      val _ = not (Term.aconv target normalized) orelse
        raise ERR "rewrite17_under_budget"
          "translation definitions did not occur in rewrite"
      val _ = require_bv_family "rewrite17_under_budget" normalized
      val _ = SmtResource.check_resource_goal
        "BitVector" "rewrite(17)" normalized
      val decision = decide normalized
    in
      Thm.EQ_MP (Thm.SYM normalization) decision
    end
    handle Conv.UNCHANGED =>
      raise ERR "rewrite17_under_budget"
        "translation definitions did not occur in rewrite"

  fun rewrite17 normalize decide definitions target =
    bv_resource_prove_after_admission "rewrite(17)"
      (rewrite17_under_budget normalize decide definitions) target

  fun rewrite16 rewrite_profile target =
    bv_resource_prove_after_admission "rewrite(16)"
      (Library.require_fastpath "Z3 rewrite WORD_ARITH_CONV" target
        (rewrite_profile "rewrite(16)(WORD_ARITH_CONV)"
          (word_decider_attempt "z3_rewrite(WORD_ARITH_CONV)"
            word_arith_prove))) target

  fun bv_rewrite_prove_with_word_prover word_prover
      rewrite_profile direct_bv lowered_bv
      pre_bblast definitions target =
    let
      val route = classify_bv_rewrite
        direct_bv lowered_bv definitions target
      val decomposition_attempted = ref false
      fun decompose_once target =
        if !decomposition_attempted then
          raise ERR "bv_rewrite_prove" "congruence already declined"
        else (decomposition_attempted := true; pre_bblast target)
      fun shared_circuit legacy target =
        if SmtResource.term_nodes_up_to 257 target <= 256 then legacy target
        else
          let
            fun circuit target = bv_next_rung
              (rewrite_profile "rewrite(18)(word-graph)"
                (SmtResource.with_resource_step_time
                  "BitVector" "word-circuit-replay"
                  (word_decider_attempt "z3_rewrite(word-graph)"
                    word_prover))) legacy target
          in
            (* SAT observes quantified formulas as opaque atoms.  First
               isolate checked body equalities by binder congruence rather
               than expand their word circuits beneath the binder.  Keep
               original-target admission and every recursive resource gate;
               an ordinary decline still reaches the complete circuit path. *)
            if SmtResource.contains Term.is_abs target then
              bv_next_rung
                (bv_resource_prove_after_admission
                  "rewrite(18)(binder-congruence)" decompose_once)
                circuit target
            else circuit target
          end
      fun rewrite17_production definitions target =
        rewrite_profile "rewrite(17)(translator-definitions+word)"
          (rewrite17 Rewrite.PURE_REWRITE_CONV word_decide_raw definitions)
          target
      fun rewrite18 case_id boolean_residue target =
        bv_resource_prove_after_admission case_id
          (fn target =>
            let
              (* A Boolean consequence of lowered word atoms can be proved
                 without expanding the atoms.  SAT's checked propositional
                 proof is only a preflight for the lowered Boolean route;
                 a counterexample to the abstraction is inconclusive. *)
              fun propositional target =
                rewrite_profile "rewrite(18)(lowered-boolean-sat)"
                  (SmtResource.with_resource_step_time "Skeleton"
                    "z3-lowered-bv-propositional"
                    (fn target =>
                      (SmtResource.check_resource_goal "Skeleton"
                         "z3-lowered-bv-propositional" target;
                       SmtSkeletonProve.checked_sat_prove target))) target
                handle HolSatLib.SAT_cex _ =>
                  raise ERR "bv_rewrite_prove"
                    "lowered Boolean abstraction has a counterexample"
                     | Feedback.HOL_ERR _ =>
                  raise ERR "bv_rewrite_prove"
                    "lowered Boolean abstraction declined"
              (* Congruence can isolate a small word rewrite inside any
                 shared application skeleton.  BBLAST remains complete. *)
              val word_route = bv_next_rung decompose_once
                (rewrite_profile "rewrite(18)(BBLAST)"
                  (word_decider_attempt "z3_rewrite(BBLAST)"
                    (Feedback.trace ("print blast counterexamples", 0)
                      blastLib.BBLAST_PROVE)))
            in
              if boolean_residue then
                bv_next_rung propositional word_route target
              else word_route target
            end) target
    in
      case route of
        DirectBV occurring =>
          shared_circuit (bv_next_rung (rewrite16 rewrite_profile)
            (if List.null occurring then
               rewrite18 "rewrite(18)" false
             else
               bv_next_rung (rewrite17_production occurring)
                 (rewrite18 "rewrite(18)" false))) target
      | LoweredBV =>
          (* Boolean fpa2bv residue bypasses inapplicable WORD_ARITH and
             definition scans, but uses the same gated complete BBLAST. *)
          shared_circuit
            (rewrite18 "rewrite(18)(lowered-bv)" true) target
      | DefinedBV occurring => rewrite17_production occurring target
      | OutsideBV =>
          raise ERR "bv_rewrite_prove" "goal is outside the BV rewrite family"
    end

  val bv_rewrite_prove_with_pre_bblast =
    bv_rewrite_prove_with_word_prover SmtWordGraph.prove

  fun no_pre_bblast _ =
    raise ERR "bv_rewrite_prove" "no pre-BBLAST decomposition"

  fun bv_rewrite_prove_with_context rewrite_profile direct_bv lowered_bv
      definitions target =
    bv_rewrite_prove_with_pre_bblast rewrite_profile direct_bv lowered_bv
      no_pre_bblast definitions target

  fun bv_rewrite_prove rewrite_profile pre_bblast (state : state) =
    bv_rewrite_prove_with_word_prover
      (SmtWordGraph.prove_in (#word_context state)) rewrite_profile has_word_atom
      (has_allocated_fp_bv_atom state) pre_bblast
      (#translation_definitions state)

  fun fp_bit_decompositions (state : state) =
    List.map
      (fn ({fp_var, bv_var, equation} : bit_decomposition) =>
        {fp_var = fp_var, bv_var = bv_var, equation = equation}
          : SmtFpProve.bit_decomposition)
      (#bit_decompositions state)

  fun is_pack_of fp_var tm =
    let
      val (head, argument) = Term.dest_comb tm
      val {Thy, Name, ...} = Term.dest_thy_const head
    in
      Thy = "smtfloat" andalso Name = "smtfp_pack_bv" andalso
      argument ~~ fp_var
    end
    handle Feedback.HOL_ERR _ => false

  (* Recursive replay can encounter one decomposition while proving a later
     dependency, then return to the same parser-recorded rewrite.  Reusing
     the already established packed definition is sound; a conflicting
     proof-local definition remains ineligible. *)
  fun eligible_fp_bit_decompositions (state : state) =
    let
      val definitions = HOLset.listItems (#definition_hyps state)
      fun eligible ({fp_var, bv_var, ...} : SmtFpProve.bit_decomposition) =
        case List.filter
            (fn definition =>
              case Lib.total boolSyntax.dest_eq definition of
                SOME (lhs, _) => lhs ~~ bv_var
              | NONE => false)
            definitions of
          [] => true
        | matching =>
            List.all
              (fn definition =>
                is_pack_of fp_var (Lib.snd
                  (boolSyntax.dest_eq definition)))
              matching
    in
      List.filter eligible (fp_bit_decompositions state)
    end

  (* This is Boolean normalization underneath a negated existential.
     HOL's simplifier descends through every quantifier, so this procedure
     covers any binder count without a one-binder proforma. *)
  fun quantified_boolean_rewrite_prove target =
    let
      fun dest_negated_exists tm =
        let
          val existential = boolSyntax.dest_neg tm
          val _ = boolSyntax.is_exists existential orelse
            raise ERR "quantified_boolean_rewrite_prove"
              "rewrite operand is not a negated existential"
          val (variables, body) = boolSyntax.strip_exists existential
          val _ = List.null variables andalso
            raise ERR "quantified_boolean_rewrite_prove"
              "negated existential has no binders"
        in body end
      val (left, right) = boolSyntax.dest_eq target
      val _ = (dest_negated_exists left; dest_negated_exists right)
        handle Feedback.HOL_ERR _ =>
        raise ERR "quantified_boolean_rewrite_prove"
          "rewrite is not between negated existential formulas"
    in
      Tactical.TAC_PROOF (([], target),
        bossLib.SIMP_TAC boolSimps.bool_ss [boolTheory.IMP_DISJ_THM])
    end

  fun assert_rewrite_definitions state definitions =
    List.app (fn definition =>
      let val (lhs, _) = boolSyntax.dest_eq definition in
        if HOLset.member (#var_set state, lhs) then ()
        else raise ERR "z3_rewrite"
          ("unification produced a definition outside the proof variable " ^
           "set: " ^ Library.term_to_string definition)
      end) definitions

  (* Canonicalize Boolean polarity before the proof-local unifier.  Even
     negation prefixes are eliminated with NOT_NOT_INTRO; if the remaining
     sides have opposite polarity, NOT_REVERSE reduces the obligation to a
     checked complementary definition.  No proposition is assumed. *)
  fun boolean_normalized_unification (lhs, rhs, var_set) =
    let
      fun normalize tm =
        if boolSyntax.is_neg tm andalso
           boolSyntax.is_neg (boolSyntax.dest_neg tm) then let
          val body = boolSyntax.dest_neg (boolSyntax.dest_neg tm)
          val step = Thm.SYM (Thm.SPEC body NOT_NOT_INTRO)
        in
          Thm.TRANS step (normalize body)
        end else Thm.REFL tm
      val lhs_normalized = normalize lhs
      val rhs_normalized = normalize rhs
      val lhs' = boolSyntax.rhs (Thm.concl lhs_normalized)
      val rhs' = boolSyntax.rhs (Thm.concl rhs_normalized)
      datatype unification = Direct of Thm.thm
        | RightNegation of Term.term * Thm.thm
        | LeftNegation of Term.term * Thm.thm
      fun no_complementary_unification _ =
        raise ORDINARY_DEFINITION_UNIFICATION_DECLINE
      fun left_negation input =
        if boolSyntax.is_neg lhs' then
          let
            val lhs_body = boolSyntax.dest_neg lhs'
          in
            with_expected_instantiation_fallback
              (fn input => LeftNegation
                (lhs_body, Library.gen_instantiation input))
              no_complementary_unification
              (lhs_body, boolSyntax.mk_neg rhs', var_set)
          end
        else no_complementary_unification input
      fun complementary input =
        if boolSyntax.is_neg rhs' then
          let
            val rhs_body = boolSyntax.dest_neg rhs'
          in
            with_expected_instantiation_fallback
              (fn input => RightNegation
                (rhs_body, Library.gen_instantiation input))
              left_negation
              (rhs_body, boolSyntax.mk_neg lhs', var_set)
          end
        else left_negation input
      val plan = with_expected_instantiation_fallback
        (Direct o Library.gen_instantiation) complementary
        (lhs', rhs', var_set)
      val p = Term.mk_var ("p", Type.bool)
      val q = Term.mk_var ("q", Type.bool)
      val unified =
        case plan of
          Direct theorem => theorem
        | RightNegation (rhs_body, premise) =>
            Thm.MP (Thm.INST [p |-> rhs_body, q |-> lhs'] NOT_REVERSE)
              premise
        | LeftNegation (lhs_body, premise) =>
            Thm.SYM
              (Thm.MP (Thm.INST [p |-> lhs_body, q |-> rhs'] NOT_REVERSE)
                premise)
    in
      Thm.TRANS lhs_normalized
        (Thm.TRANS unified (Thm.SYM rhs_normalized))
    end

  (* Only exhaustion of the documented unification alternatives is an
     ordinary ladder decline.  Any HOL_ERR from theorem construction or an
     unclassified unifier failure must escape the surrounding broad rewrite
     handlers through [DEFINITION_REWRITE_ERROR]. *)
  fun definition_unification_boundary action =
    action ()
    handle ORDINARY_DEFINITION_UNIFICATION_DECLINE =>
      raise ERR "z3_rewrite" "proof-local unification declined"
         | Feedback.HOL_ERR holerr =>
      raise DEFINITION_REWRITE_ERROR (Feedback.HOL_ERR holerr)

  fun has_arithmetic_operator target =
    SmtResource.contains (fn tm =>
      Term.is_const tm andalso
      let val {Thy, ...} = Term.dest_thy_const tm in
        Thy = "integer" orelse Thy = "real" orelse Thy = "intreal"
      end) target

  fun linear_arithmetic_rewrite_prove target =
    let
      fun arithmetic_variable variable =
        SmtReplayCanon.is_arith_type (Term.type_of variable)
      val _ = HOLset.foldl (fn (variable, accepted) =>
        accepted andalso arithmetic_variable variable) true
        (Term.FVL_dag [target] Term.empty_tmset) orelse
        raise ERR "linear_arithmetic_rewrite_prove"
          "rewrite has a non-arithmetic variable"
      val _ = has_arithmetic_operator target orelse
        raise ERR "linear_arithmetic_rewrite_prove"
          "rewrite has no integer or real operator"
      val _ = not (SmtResource.contains boolSyntax.is_cond target) orelse
        raise ERR "linear_arithmetic_rewrite_prove"
          "conditional rewrite is outside polynomial normal form"
    in
      SmtReplayCanon.arith_poly_norm_prove target
    end

  fun unsupported_rewrite version attempts target =
    ERR "z3_rewrite"
      (unsupported_rewrite_diagnostic ^
       ": proof rule=rewrite; z3-version=" ^ version ^
       "; attempted fragment classes=[" ^
       String.concatWith ", " attempts ^
       "]; parsed HOL conclusion=" ^ Library.term_to_string target)

  datatype recursive_rewrite_site =
      RecursiveSkeleton
    | RecursiveEquality
    | RecursiveAbstraction

  (* A recursive rewrite returns through a fresh [z3_rewrite] exception
     boundary.  Re-wrap only resource gates so that the enclosing rewrite
     handler's ordinary HOL_ERR fallback cannot consume them.  All other
     recursive failures retain the existing fall-through semantics. *)
  fun recursive_rewrite_boundary _ recurse input =
    recurse input
    handle Feedback.HOL_ERR holerr =>
      if SmtResource.is_resource_gate holerr then
        raise BV_REWRITE_ERROR (Feedback.HOL_ERR holerr)
      else
        raise Feedback.HOL_ERR holerr

  (* Normalize only with definitions that replay has already checked.  Each
     theorem is oriented away from its proof-local Z3 name, and PURE_REWRITE
     builds the congruence proof while instantiating that theorem.  The
     normalized proposition is discharged by its arithmetic owner (including
     the ediv/emod ladder) or by kernel reflexivity; definitions never become
     a general-purpose contextual rewrite set. *)
  fun checked_definition_normalization var_set definitions target =
    let
      fun oriented definition =
        let
          val theorem = Thm.ASSUME definition
          val (left, right) = boolSyntax.dest_eq definition
        in
          if Term.is_var left andalso HOLset.member (var_set, left) then
            SOME theorem
          else if Term.is_var right andalso HOLset.member (var_set, right) then
            SOME (Thm.SYM theorem)
          else
            NONE
        end
        handle Feedback.HOL_ERR _ => NONE
      val _ = List.length definitions <= 128 orelse
        raise ERR "definition_normalization_prove"
          "too many checked proof-local definitions"
      val rewrite_theorems = List.mapPartial oriented definitions
      val _ = not (List.null rewrite_theorems) orelse
        raise ERR "definition_normalization_prove"
          "no checked proof-local equality definition"
      val normalization =
        Library.checked_definition_rewrite_conv rewrite_theorems target
      val normalized = boolSyntax.rhs (Thm.concl normalization)
      val _ = not (Term.aconv target normalized) orelse
        raise ERR "definition_normalization_prove"
          "checked definitions do not occur in target"
    in
      (normalization, normalized)
    end
    handle Conv.UNCHANGED =>
      raise ERR "definition_normalization_prove"
        "checked definitions do not occur in target"

  fun definition_normalization_prove_with remember
      var_set definitions target =
    let
      val (normalization, normalized) =
        checked_definition_normalization var_set definitions target
      val () = remember (normalization, normalized)
      fun reflexive () =
        let val (left, right) = boolSyntax.dest_eq normalized
        in
          if Term.aconv left right then Thm.ALPHA left right
          else raise ERR "definition_normalization_prove"
            "normalized equality is not reflexive"
        end
      val decision = reflexive ()
        handle Feedback.HOL_ERR _ =>
          let val variables = HOLset.listItems
            (Term.FVL_dag [normalized] Term.empty_tmset) in
            if not (List.null variables) andalso
               List.all (SmtReplayCanon.is_arith_type o Term.type_of) variables
            then profile "definition-normalization(owner:arithmetic)"
              arith_prove normalized
            else raise ERR "definition_normalization_prove"
              "normalized target has no selected owning prover"
          end
    in
      Thm.EQ_MP (Thm.SYM normalization) decision
    end

  fun definition_normalization_prove var_set definitions =
    definition_normalization_prove_with ignore var_set definitions

  val NEGATED_IMPLICATION_ANTECEDENT = Library.prove
    (``!p q. ~(p ==> q) ==> p``, tautLib.TAUT_TAC)

  (* Extract equality facts by a fixed, structurally decreasing derivation.
     The source theorem remains an exact hypothesis throughout.  In
     particular, this does not inspect consequents, disjunctions, or arbitrary
     first-order consequences of the assertion. *)
  fun asserted_equality_theorems assertions =
    let
      val max_facts = 64
      val max_nodes = 256
      val _ = List.length assertions <= max_nodes orelse
        raise ERR "asserted_equality_theorems"
          "too many replayed assertions for equality extraction"
      val facts_seen = ref 0
      val nodes_seen = ref 0
      fun derive depth theorem =
        let
          val _ = nodes_seen := !nodes_seen + 1
          val _ = !nodes_seen <= max_nodes orelse
            raise ERR "asserted_equality_theorems"
              "assertion structure exceeds equality extraction node bound"
          val conclusion = Thm.concl theorem
          val _ = depth <= max_facts orelse
            raise ERR "asserted_equality_theorems"
              "assertion structure exceeds equality extraction bound"
        in
          if boolSyntax.is_eq conclusion then
            (facts_seen := !facts_seen + 1;
             !facts_seen <= max_facts orelse
               raise ERR "asserted_equality_theorems"
                 "too many explicit equality components";
             [theorem])
          else if boolSyntax.is_conj conclusion then
            derive (depth + 1) (Thm.CONJUNCT1 theorem) @
            derive (depth + 1) (Thm.CONJUNCT2 theorem)
          else
            let
              val implication = boolSyntax.dest_neg conclusion
              val (antecedent_term, consequent_term) =
                boolSyntax.dest_imp implication
              val antecedent = Thm.MP
                (Drule.SPECL [antecedent_term, consequent_term]
                  NEGATED_IMPLICATION_ANTECEDENT) theorem
            in
              derive (depth + 1) antecedent
            end
            handle Feedback.HOL_ERR _ => []
        end
      val facts = List.concat
        (List.map (derive 0 o Thm.ASSUME) assertions)
      val _ = List.length facts = !facts_seen orelse
        raise ERR "asserted_equality_theorems"
          "internal equality extraction count mismatch"
    in
      facts
    end

  (* Substitution is the only use made of replayed assertions.  Most solve-eqs
     residues become reflexive immediately.  Integer min/max certificates use
     complementary < and <= conditionals; after substitution that narrowly
     admitted linear-conditional residue is sent to the existing arithmetic
     owner, with no assertion context. *)
  fun asserted_equality_substitution_prove assertions target =
    let
      val equalities = asserted_equality_theorems assertions
      val _ = not (List.null equalities) orelse
        raise ERR "asserted_equality_substitution_prove"
          "no structurally derived asserted equality"
      fun prove_with rewrite_theorems =
        let
          val substitution = Rewrite.PURE_REWRITE_CONV rewrite_theorems target
          val substituted = boolSyntax.rhs (Thm.concl substitution)
          fun reflexive () =
            let val (left, right) = boolSyntax.dest_eq substituted
            in
              if Term.aconv left right then Thm.ALPHA left right
              else raise ERR "asserted_equality_substitution_prove"
                "substituted equality is not reflexive"
            end
          fun integer_conditional () =
            let
              val conditionals = List.filter
                (Lib.can boolSyntax.dest_cond) (Library.subterms substituted)
              fun add (conditional, unique) =
                if List.exists (Term.aconv conditional) unique then unique
                else conditional :: unique
              val unique = List.foldl add [] conditionals
              val _ = SmtResource.term_nodes_up_to 4096 substituted <= 4096
                orelse raise ERR "asserted_equality_substitution_prove"
                  "integer conditional residue exceeds 4096 syntax nodes"
              val _ = not (List.null unique) andalso
                  List.length unique <= 4 orelse
                raise ERR "asserted_equality_substitution_prove"
                  "outside bounded integer min/max conditional family"
              val _ = List.all
                (fn variable => Term.type_of variable = intSyntax.int_ty)
                (Term.free_vars substituted) orelse
                raise ERR "asserted_equality_substitution_prove"
                  "conditional residue has a non-integer variable"
            in
              Tactical.TAC_PROOF (([], substituted),
                Tactical.REPEAT Tactic.COND_CASES_TAC THEN
                intLib.ARITH_TAC)
            end
          val decision = reflexive ()
            handle Feedback.HOL_ERR _ => integer_conditional ()
        in
          Thm.EQ_MP (Thm.SYM substitution) decision
        end
      fun attempt rewrite_theorems = prove_with rewrite_theorems
        handle Conv.UNCHANGED =>
          raise ERR "asserted_equality_substitution_prove"
            "explicit equalities do not occur in target"
      val oriented = equalities
      val reversed = List.map Thm.SYM equalities
    in
      attempt oriented
      handle Feedback.HOL_ERR holerr =>
        if SmtResource.is_resource_gate holerr then
          raise Feedback.HOL_ERR holerr
        else attempt reversed
    end

    fun z3_rewrite (state, t) =
  let
    val (l, r) = boolSyntax.dest_eq t
    (* Admit String rewrites before the generic Boolean ladder walks a large
       concatenation spine.  The dedicated String budget owns this boundary
       and supplies the stable String/rewrite diagnostic. *)
    val _ = if SmtStringProve.has_string_theory_term t then
      SmtResource.check_resource_goal "String" "rewrite" t
    else ()
    val attempts = ref ([] : string list)
    val deferred_unification = ref (NONE : (thm * term list) option)
    val checked_normalization =
      ref (NONE : (thm * term) option)
    val pre_bblast_skeleton_attempted = ref false
    val pre_bblast_state = ref (NONE : state option)
    fun record_attempt fragment =
      if List.exists (Lib.equal fragment) (!attempts) then ()
      else attempts := !attempts @ [fragment]
    fun rewrite_profile fragment name prove input =
      (record_attempt fragment; profile name prove input)
    fun skeleton_congruence () =
      let
        fun same_head (left, right) =
          let
            val (left_head, _) = boolSyntax.strip_comb left
            val (right_head, _) = boolSyntax.strip_comb right
          in
            Term.aconv left_head right_head orelse
              raise ERR "skeleton_congruence" "skeleton heads differ"
          end
        fun child (state, left_parent, right_parent) (left, right) =
          if Term.term_eq left right then
            (state, Thm.REFL left)
          else if Term.aconv left right then
            (state, Thm.ALPHA left right)
          else
            let
              (* Every caller peels a connective, application or binder.
                 The recursive obligations are its proper children; counting
                 their unfolded trees would destroy circuit sharing. *)
              val target = boolSyntax.mk_eq (left, right)
              val (state', theorem) = recursive_rewrite_boundary
                RecursiveSkeleton z3_rewrite (state, target)
              (* Reject a circular use when this residue is itself one of the
                 original assertions.  Checked definition hypotheses stay. *)
              val _ = List.exists (fn hypothesis =>
                  Term.aconv hypothesis target) (Thm.hyp theorem) andalso
                raise ERR "skeleton_congruence"
                  "recursive residue was deferred as its own assumption"
              val exact = Thm.EQ_MP
                (Thm.ALPHA (Thm.concl theorem) target) theorem
            in
              (state', exact)
            end
        fun unary dest (state, left, right) =
          let
            val _ = same_head (left, right)
            val (left_body, right_body) = (dest left, dest right)
            val (state', body_theorem) =
              child (state, left, right) (left_body, right_body)
          in
            (state', Thm.AP_TERM (Term.rator left) body_theorem)
          end
        fun binary dest (state, left, right) =
          let
            val _ = same_head (left, right)
            val (left_first, left_second) = dest left
            val (right_first, right_second) = dest right
            val (state', first_theorem) = child (state, left, right)
              (left_first, right_first)
            val (state'', second_theorem) = child (state', left, right)
              (left_second, right_second)
            val head = Term.rator (Term.rator left)
            val theorem = Thm.MK_COMB
              (Thm.MK_COMB (Thm.REFL head, first_theorem), second_theorem)
          in
            (state'', theorem)
          end
        fun quantified dest (state, left, right) =
          let
            val _ = same_head (left, right)
            val _ = dest left
            val _ = dest right
            val state_ref = ref state
            val abstraction_theorem = abs_congruence
              (fn (left_body, right_body) =>
                let
                  val (state', body_theorem) =
                    child (!state_ref, left, right)
                      (left_body, right_body)
                in
                  state_ref := state'; body_theorem
                end)
              (Term.rand left, Term.rand right)
          in
            (!state_ref,
             Thm.AP_TERM (Term.rator left) abstraction_theorem)
          end
        fun conditional (state, left, right) =
          let
            val (left_guard, left_yes, left_no) = boolSyntax.dest_cond left
            val (right_guard, right_yes, right_no) = boolSyntax.dest_cond right
            fun propositional_guard guard =
              let
                val target = boolSyntax.mk_eq (left_guard, guard)
                val measure = admitted_def_axiom_measure
                  SmtSkeletonProve.term_measure target
              in
                case SmtSkeletonProve.attempt_with_owners
                    def_axiom_skeleton_context
                    def_axiom_skeleton_owners measure target of
                  SmtSkeletonProve.Proved result => SOME (#theorem result)
                | SmtSkeletonProve.Declined => NONE
              end
            fun build state guard_theorem yes no flipped =
              let
                val (state', yes_theorem) = child (state, left, right)
                  (left_yes, yes)
                val (state'', no_theorem) = child (state', left, right)
                  (left_no, no)
                val head = Term.rator (Term.rator (Term.rator left))
                val congruence = Thm.MK_COMB
                  (Thm.MK_COMB
                    (Thm.MK_COMB (Thm.REFL head, guard_theorem),
                     yes_theorem), no_theorem)
                val result = if flipped then Thm.TRANS congruence
                    (Conv.REWR_CONV HolSmtTheory.COND_NEG
                      (boolSyntax.rhs (Thm.concl congruence)))
                  else congruence
              in (state'', result) end
          in
            case propositional_guard right_guard of
              SOME theorem =>
                build state theorem right_yes right_no false
            | NONE =>
                case propositional_guard (boolSyntax.mk_neg right_guard) of
                  SOME theorem =>
                    build state theorem right_no right_yes true
                | NONE =>
                    let val (state', theorem) = child (state, left, right)
                        (left_guard, right_guard)
                    in build state' theorem right_yes right_no false end
          end
        fun boolean_equality term =
          let val (left, right) = boolSyntax.dest_eq term in
            Term.type_of left = Type.bool andalso
            Term.type_of right = Type.bool
          end
          handle Feedback.HOL_ERR _ => false
        val result =
          if boolSyntax.is_neg l andalso boolSyntax.is_neg r then
            unary boolSyntax.dest_neg (state, l, r)
          else if boolSyntax.is_conj l andalso boolSyntax.is_conj r then
            binary boolSyntax.dest_conj (state, l, r)
          else if boolSyntax.is_disj l andalso boolSyntax.is_disj r then
            binary boolSyntax.dest_disj (state, l, r)
          else if boolSyntax.is_imp l andalso boolSyntax.is_disj r then
            let
              val bridge = Conv.REWR_CONV boolTheory.IMP_DISJ_THM l
              val normalized = boolSyntax.rhs (Thm.concl bridge)
              val (state', aligned) =
                binary boolSyntax.dest_disj (state, normalized, r)
            in (state', Thm.TRANS bridge aligned) end
          else if boolSyntax.is_disj l andalso boolSyntax.is_imp r then
            let
              val bridge = Conv.REWR_CONV boolTheory.IMP_DISJ_THM r
              val normalized = boolSyntax.rhs (Thm.concl bridge)
              val (state', aligned) =
                binary boolSyntax.dest_disj (state, l, normalized)
            in (state', Thm.TRANS aligned (Thm.SYM bridge)) end
          else if boolSyntax.is_imp l andalso boolSyntax.is_imp r then
            binary boolSyntax.dest_imp (state, l, r)
          else if boolean_equality l andalso boolean_equality r then
            binary boolSyntax.dest_eq (state, l, r)
          else if boolSyntax.is_cond l andalso boolSyntax.is_cond r then
            conditional (state, l, r)
          else if boolSyntax.is_forall l andalso boolSyntax.is_forall r then
            quantified boolSyntax.dest_forall (state, l, r)
          else if boolSyntax.is_exists l andalso boolSyntax.is_exists r then
            quantified boolSyntax.dest_exists (state, l, r)
          else if Term.is_comb l andalso Term.is_comb r then
            let
              val _ = same_head (l, r)
              val (left_operator, left_operand) = Term.dest_comb l
              val (right_operator, right_operand) = Term.dest_comb r
              val (state', operator_theorem) = child (state, l, r)
                (left_operator, right_operator)
              val (state'', operand_theorem) = child (state', l, r)
                (left_operand, right_operand)
            in
              (state'', Thm.MK_COMB
                (operator_theorem, operand_theorem))
            end
          else
            raise ERR "skeleton_congruence"
              "rewrite does not have a shared supported skeleton head"
        val (state', theorem) = result
        val exact = Thm.EQ_MP (Thm.ALPHA (Thm.concl theorem) t) theorem
      in
        (state_cache_thm state' exact, exact)
      end
    fun pre_bblast_skeleton _ =
      let
        (* The state update is transactional: recursive definitions and
           theorem-cache entries become visible only after the complete
           congruence proof succeeds.  Ordinary decline leaves BBLAST with
           the original state, while recursive resource gates stay terminal
           through [bv_next_rung]. *)
        val _ = pre_bblast_skeleton_attempted := true
        val _ = record_measured_target MeasuredSkeletonCongruence t
        val (state', theorem) =
          rewrite_profile "boolean/binder-skeleton"
            "rewrite(25a)(skeleton-congruence)" skeleton_congruence ()
        val _ = pre_bblast_state := SOME state'
      in
        theorem
      end
  in
    (* E1(a): kernel reflexivity decides the reflexive-equality fragment. *)
    if l ~~ r then
      (state, Thm.REFL l)
    else
      case Lib.total rewrite_boolean_constant_schema t of
        SOME theorem => (state, theorem)
      | NONE =>
      (* E1(a): this decides Boolean AC-idempotent conjunction/disjunction. *)
      rewrite_profile "propositional-AC" "rewrite(1)(conj/disj)" (fn () =>
      if boolSyntax.is_conj l then
        (state, rewrite_conj (l, r))
      else if boolSyntax.is_disj l then
        (state, rewrite_disj (l, r))
      else
        raise ERR "" "") ()
    handle Feedback.HOL_ERR _ =>

    (* |- r1 /\ ... /\ rn = ~(s1 \/ ... \/ sn) *)
    (* E1(a): resolution decides the exact Z3 NNF shape implemented here:
       a conjunction of literals/equivalences equals the negation of a
       disjunction, including the two checked negated-equivalence variants. *)
    (state, rewrite_profile "propositional-NNF" "rewrite(2)(nnf)"
      rewrite_nnf (l, r))
    handle Feedback.HOL_ERR _ =>

    (* A Boolean tautology does not become an FP-specific obligation merely
       because an atom has FP type.  Decide the complete propositional
       fragment before entering the terminal FP ladder, while preserving the
       established cost order for non-FP rewrite families. *)

    (* Once an FP-shaped rewrite enters its dedicated ladder, failure at its
       unsupported rung is terminal.  In particular, generic unification
       must not turn an unsupported FP rewrite into a proof-local definition.
       FP_REWRITE_ERROR crosses the handlers below and is converted back to a
       structured HOL_ERR at the function boundary. *)
    if SmtFpProve.has_fp_theory_term t then
      let
        fun bounded_propositional target =
          rewrite_profile "propositional"
            "rewrite(fp-preflight)(skeleton)"
            (SmtResource.with_resource_step_time
              "Skeleton" "z3-rewrite-propositional"
              (fn target =>
                let
                  val measure = admitted_def_axiom_measure
                    SmtSkeletonProve.term_measure target
                in
                  (* This rung decides only propositional identities:
                     theory atoms remain opaque.  A SAT abstraction declines
                     to the FP procedure, not to a tree-expanding tautology
                     search or an unrelated theory reduction. *)
                  case SmtSkeletonProve.attempt_with_owners
                      def_axiom_skeleton_context
                      def_axiom_skeleton_owners measure target of
                    SmtSkeletonProve.Proved result => #theorem result
                  | SmtSkeletonProve.Declined =>
                      raise ERR "bounded_propositional"
                        "rewrite requires floating-point theory semantics"
                end)) target
      in
      ((state, bounded_propositional t)
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else
       ((* E1(c): exact FP theorem reuse is a redundant performance cache. *)
        (state, rewrite_profile "cached-checked-theorems"
           "rewrite(3)(cache-fp)"
           (fn target =>
             Library.require_fastpath "Z3 rewrite FP theorem cache" target
               (state_exact_cached_thm state) target) t)
        handle Feedback.HOL_ERR _ =>
          let
            val eligible_decompositions =
              eligible_fp_bit_decompositions state
            val all_decompositions = fp_bit_decompositions state
            (* E1(b): checked lowering is the general selected FP rewrite
               procedure and fails loudly at its unsupported/D4 boundary. *)
            val thm = rewrite_profile "floating-point"
              "rewrite(4)(fp)"
              (SmtFpProve.fp_prove_with_word_prover
                (SmtWordGraph.prove_in (#word_context state)) arith_prove
                eligible_decompositions all_decompositions) t
              handle Feedback.HOL_ERR holerr =>
                raise FP_REWRITE_ERROR (Feedback.HOL_ERR holerr)
            val definitions = Thm.hyp thm
            val state = state_define (state_cache_thm state thm) definitions
          in
            (state, thm)
          end))
      end
    else
      (* FP has first refusal.  Z3's bag encoding then gets the count-array
         ladder before generic proformas; its [(_ map +)] terms parse to
         pointwise Int lambdas.  Native Seq follows with its bounded list
         ladder. *)
      (let
         (* E1(b): the general Bag prover fails loudly outside its family. *)
         val thm = rewrite_profile "bags" "rewrite(5)(bag)"
           (SmtBagProve.bag_prove_with_arith arith_prove) t
       in
         (state_cache_thm state thm, thm)
       end
       handle Feedback.HOL_ERR holerr =>
         if SmtResource.is_resource_gate holerr then
           raise BAG_REWRITE_ERROR (Feedback.HOL_ERR holerr)
         else
         (let
            (* E1(b): the general Seq prover has an explicit family gate. *)
            val thm = rewrite_profile "sequences" "rewrite(6)(seq)"
              SmtSeqProve.seq_prove t
          in
            (state_cache_thm state thm, thm)
          end
          handle Feedback.HOL_ERR holerr =>
            if SmtResource.is_resource_gate holerr then
              raise Feedback.HOL_ERR holerr
            else
              (* E1(a): canonicalization decides polynomial normal forms. *)
              (state, rewrite_profile "polynomial-normal-form"
                "rewrite(7)(poly-normal-form)"
                linear_arithmetic_rewrite_prove t)
              handle Feedback.HOL_ERR _ =>
              (* E1(a): simplification decides quantified Boolean normality. *)
              (state, rewrite_profile "quantified-propositional"
                "rewrite(8)(quantified-boolean)"
                quantified_boolean_rewrite_prove t)
              handle Feedback.HOL_ERR _ =>
              (* E1(c): rewrite proformas are redundant performance caches. *)
              (state, rewrite_profile "proforma-fastpaths"
                "rewrite(9)(proforma)"
                (fn target =>
                  Library.require_fastpath "Z3 rewrite proforma" target
                    Z3_ProformaThms.prove_rewrite target)
                t)
              handle Feedback.HOL_ERR _ =>
              (* Shared application structure is a kernel congruence
                 obligation even when its result has function type.  Try
                 that checked decomposition before admitting the equality
                 as an Array extensionality problem. *)
              (if is_function_type (Term.type_of l) andalso
                  Term.is_comb l andalso Term.is_comb r then
                 (pre_bblast_skeleton_attempted := true;
                  record_measured_target MeasuredSkeletonCongruence t;
                  rewrite_profile "boolean/binder-skeleton"
                    "rewrite(9a)(skeleton-congruence)"
                    skeleton_congruence ())
               else raise ERR "z3_rewrite"
                 "no function-valued application congruence")
              handle Feedback.HOL_ERR _ =>
                let
                (* E1(b): the budgeted array/set procedure covers selected
                   beta, update, symbolic-index and extensional shapes and
                   fails loudly outside them or at its D4 boundary. *)
                val thm = rewrite_profile "arrays/set"
                  "rewrite(10)(array-set)"
                  SmtArrayProve.array_prove t
              in
                (state_cache_thm state thm, thm)
              end))

    handle Feedback.HOL_ERR holerr =>
    if SmtResource.is_resource_gate holerr then
      raise Feedback.HOL_ERR holerr
    else
      (* E1(c): theorem reuse is a redundant performance cache. *)
      (state, rewrite_profile "cached-checked-theorems"
        "rewrite(11)(cache)"
        (fn target =>
          Library.require_fastpath "Z3 rewrite theorem cache" target
            (state_inst_cached_thm state) target) t)

    handle Feedback.HOL_ERR _ =>

    (* Z3's String theory emits rewrite steps for literal normalization,
       ground `str.*` evaluation, and regex normalization. *)
    let
      (* E1(b): the general String/regex procedure has a loud boundary. *)
      val thm = rewrite_profile "strings/regex" "rewrite(12)(string)"
        SmtStringProve.string_rewrite_prove t
    in
      (state_cache_thm state thm, thm)
    end

    handle Feedback.HOL_ERR holerr =>
      if SmtResource.is_resource_gate holerr then
        raise STRING_REWRITE_ERROR (Feedback.HOL_ERR holerr)
      else

        (* |- ALL_DISTINCT ... /\ T = ... *)
        (* E1(a): recursive expansion decides literal-list distinctness. *)
        (state, rewrite_profile "datatype-literal-distinctness"
          "rewrite(13)(all_distinct)"
          rewrite_all_distinct (l, r))
    handle Feedback.HOL_ERR _ =>

    (* Existing checked definitions normalize fresh proof names before the
       unifier is allowed to invent another definition for the same name. *)
    (let
       val theorem = rewrite_profile "proof-local-definition-normalization"
         "rewrite(13a)(definition-normalization)"
         (definition_normalization_prove_with
           (fn result => checked_normalization := SOME result)
           (#var_set state)
           (HOLset.listItems (#definition_hyps state))) t
     in
       (state_cache_thm state theorem, theorem)
     end
     handle Feedback.HOL_ERR holerr =>
       if SmtResource.is_resource_gate holerr then
         raise DEFINITION_REWRITE_ERROR (Feedback.HOL_ERR holerr)
       else raise Feedback.HOL_ERR holerr)
    handle Feedback.HOL_ERR _ =>

    (* Resolve proof-local names before arithmetic.  These rewrites are not
       arithmetic tautologies until the fresh Z3 variable is recorded as a
       definition, and nonlinear fallback can otherwise spend a long time on
       the deliberately underconstrained formula. *)
    (* E1(a): one checked unifier decides proof-local definitions.  Safe
       definitions return immediately; bare aliases are saved for the end so
       semantic theory procedures retain their established priority. *)
    definition_unification_boundary (fn () =>
      let
        fun normalized_unification input =
          case !checked_normalization of
            NONE => boolean_normalized_unification input
          | SOME (normalization, normalized) =>
              let
                val (normalized_left, normalized_right) =
                  boolSyntax.dest_eq normalized
                val theorem = boolean_normalized_unification
                  (normalized_left, normalized_right,
                   #flexible_vars state)
              in
                Thm.EQ_MP (Thm.SYM normalization) theorem
              end
        val thm = rewrite_profile "proof-local-definitions"
          "rewrite(14)(unification)"
          (fn () => gen_instantiation_with_expected_fallback
            normalized_unification
            (l, r, #flexible_vars state)) ()
        val asl = Thm.hyp thm
        val old_definitions = #definition_hyps state
        val new_definitions = List.filter
          (fn definition =>
            not (HOLset.member (old_definitions, definition))) asl
        val _ = assert_rewrite_definitions state new_definitions
        fun is_safe_early_definition tm =
          let val (name, residue) = boolSyntax.dest_eq tm
          in Term.type_of name = Type.bool orelse not (Term.is_var residue) end
        val safe = List.all is_safe_early_definition new_definitions
      in
        if List.null new_definitions then
          (state_cache_thm state thm, thm)
        else if safe then
          (state_define (state_cache_thm state thm) new_definitions, thm)
        else
          (deferred_unification := SOME (thm, new_definitions);
           raise ORDINARY_DEFINITION_UNIFICATION_DECLINE)
      end)

    handle Feedback.HOL_ERR _ =>

    (* Relate Z3's per-bit Boolean skolems to the packed BV skolem recorded
       by rewrite(4)(fp) or inferred by the exact-allocation fallback above.
       The resulting theorem retains only checked definitional hypotheses,
       which final replay eliminates as usual. *)
    (let
       val free_vars = Term.FVL_dag [t] Term.empty_tmset
       val packed_vars = fp_packed_vars state
       val _ = List.exists
           (fn var => HOLset.member (free_vars, var)) packed_vars orelse
         raise ERR "z3_rewrite" "no FP packed word in rewrite"
       val definitions = fp_per_bit_definitions state @
         HOLset.listItems (#definition_hyps state)
       (* E1(a): checked definitions reduce this fragment to BV blasting. *)
       val thm =
         (rewrite_profile "floating-point/bit-vectors"
            "rewrite(15)(fp-packed-bits)"
            (SmtFpProve.definition_bitblast_prove_with
              (SmtWordGraph.prove_in (#word_context state)) definitions) t
          handle Feedback.HOL_ERR holerr =>
            if SmtResource.is_resource_gate holerr then
              raise Feedback.HOL_ERR holerr
            else
              rewrite_profile "bit-vectors"
                "rewrite(15a)(conditional-BBLAST)"
                (bounded_conditional_word_prove "BitVector"
                  "z3-rewrite-conditional-fp-word") t)
       val state = state_define (state_cache_thm state thm) (Thm.hyp thm)
     in
       (state, thm)
     end
     handle Feedback.HOL_ERR holerr =>
       if SmtResource.is_resource_gate holerr then
         raise FP_REWRITE_ERROR (Feedback.HOL_ERR holerr)
       else
         raise Feedback.HOL_ERR holerr)

    handle Feedback.HOL_ERR _ =>

    let
      (* This semantic bridge is shared before and after arithmetic.  Word
         counterexamples are normalized to the ladder's ordinary failure, so
         they cannot bypass either occurrence or the later general rungs. *)
      fun smt_rdiv_prove () =
        (* E1(a): proved normalization decides side-condition-closed rdiv. *)
        rewrite_profile "linear-real-division" "rewrite(19)(smt-rdiv)"
          (simpLib.SIMP_PROVE (bossLib.srw_ss())
            [HolSmtTheory.smt_rdiv_eq_div]) t
      val thm =
        (bv_rewrite_prove (rewrite_profile "bit-vectors")
           pre_bblast_skeleton state t
         handle Feedback.HOL_ERR holerr =>
           if SmtResource.is_resource_gate holerr then
             raise BV_REWRITE_ERROR (Feedback.HOL_ERR holerr)
           else

        (* Before arithmetic, use the semantic bridge whenever simp can
           discharge the non-zero divisor condition. *)
        smt_rdiv_prove ()
        handle Feedback.HOL_ERR _ =>

        (* E1(b): arithmetic combines complete linear and loud NLA routes. *)
        rewrite_profile "linear/nonlinear-arithmetic" "rewrite(20)(arith)"
          arith_prove t

        )
        handle Feedback.HOL_ERR _ =>

        smt_rdiv_prove ()
        handle Feedback.HOL_ERR _ =>

        (* E1(b): the TypeBase-driven simplification/cases/exhaustiveness/
           acyclicity procedure is general for selected registered datatype
           facts and fails loudly outside those shapes. *)
        rewrite_profile "datatypes" "rewrite(21)(datatype)"
          SmtDatatypeProve.datatype_prove t

    in
      (case !pre_bblast_state of
         SOME state' => (state', thm)
       | NONE => (state_cache_thm state thm, thm))
    end

    handle Feedback.HOL_ERR _ =>

    (* Congruence one level below a Boolean equality.  Lambda definitions
       often appear as [(f = lhs) = (f = rhs)]; prove [lhs = rhs] through
       the ordinary rewrite ladder, then lift that checked theorem through
       the shared equality context with a kernel congruence step. *)
    (* E1(a): recursive kernel congruence decides shared Boolean equality. *)
    rewrite_profile "higher-order-congruence/beta/eta"
      "rewrite(22)(equality-congruence)" (fn () =>
      let
        val (ll, lr) = boolSyntax.dest_eq l
        val (rl, rr) = boolSyntax.dest_eq r
        (* [lift] rebuilds the equality around the proved argument; the
           partial applications of [=] come from [l] itself, so they are
           already instantiated at the argument type. *)
        val (sub_l, sub_r, lift) =
          if ll ~~ rl then
            (lr, rr, Thm.AP_TERM (Term.rator l))
          else if lr ~~ rr then
            (ll, rl, fn sub_thm =>
              Thm.AP_THM (Thm.AP_TERM (Term.rator (Term.rator l)) sub_thm) lr)
          else raise ERR "z3_rewrite" "no shared equality argument"
        val (state', sub_thm) = recursive_rewrite_boundary
          RecursiveEquality z3_rewrite
          (state, boolSyntax.mk_eq (sub_l, sub_r))
        val lifted = lift sub_thm
        val thm = Thm.EQ_MP (Thm.ALPHA (Thm.concl lifted) t) lifted
      in
        (state_cache_thm state' thm, thm)
      end) ()
    handle Feedback.HOL_ERR _ =>

    (* Congruence below a lambda; the shared `abs_congruence` handles the
       capture-avoiding binder alignment, while the body is replayed through
       `z3_rewrite` (threading the state via `state_ref`). *)
    (* E1(a): kernel abstraction congruence decides lambda bodies. *)
    rewrite_profile "higher-order-congruence/beta/eta"
      "rewrite(23)(abs-congruence)" (fn () =>
      let
        val state_ref = ref state
        val thm = abs_congruence (fn (lbody, rbody) =>
          let
            val (state', body_thm) = recursive_rewrite_boundary
              RecursiveAbstraction z3_rewrite
              (!state_ref, boolSyntax.mk_eq (lbody, rbody))
          in
            state_ref := state'; body_thm
          end) (l, r)
      in
        (!state_ref, thm)
      end) ()
    handle Feedback.HOL_ERR _ =>

    (* E1(a): kernel beta conversion decides beta equality. *)
    (state, rewrite_profile "higher-order-congruence/beta/eta"
      "rewrite(24)(beta)" beta_equal (l, r))
    handle Feedback.HOL_ERR _ =>

    (* E1(a): kernel eta conversion decides eta equality. *)
    (state, rewrite_profile "higher-order-congruence/beta/eta"
      "rewrite(25)(eta)" eta_equal (l, r))
    handle Feedback.HOL_ERR _ =>

    (* Binder-bearing BV targets already tried this general decomposition
       before BBLAST.  If both routes declined, do not repeat partially
       completed recursive work.  Other targets reach the original fallback
       here after every semantic theory rung has declined. *)
    (if !pre_bblast_skeleton_attempted then
       raise ERR "z3_rewrite"
         "skeleton congruence already declined before BBLAST"
     else
       (record_measured_target MeasuredSkeletonCongruence t;
        rewrite_profile "boolean/binder-skeleton"
          "rewrite(25a)(skeleton-congruence)" skeleton_congruence ()))
    handle Feedback.HOL_ERR _ =>

    (* Proof-local terms have already reached the general unifier before the
       theory-specific procedures above.  The examples below document why
       that semantic path exists.
       As a motivating example, when proving `(if x < y then x else y) <= x`,
       Z3 v4.12.4 asks us to prove the following rewrite as one of the proof
       steps:

       ~(x + -1 * (if x + -1 * y >= 0 then y else x) >= 0) <=>
       ~(x + -1 * $var$(z3name!0) >= 0)

       ... where z3name!0 is a variable declared by Z3 at the beginning of its
       proof certificate, but which we know nothing about at this point.

       We use the following function to unify both sides of the equality such
       that we obtain instantiations for these variables invented by Z3 (i.e. in
       this example, we'll obtain ``z3name!0 = if x + -1 * y >= 0 then y else x``):

       > Unify.simp_unify_terms [] ``<lhs>`` ``<rhs>``;

       val it = [{redex = ``$var$(z3name!0)``, residue =
         ``if x + -1 * y >= 0 then y else x``}]: (term, term) subst

       We then prove the theorem by substituting the variable(s) and add
       ``z3name!0 = if ... then y else x`` to the list of Z3-provided
       definitions (as in the `z3_intro_def` handler), to make sure it gets
       removed from the set of hypotheses of the final theorem. *)

    (* solve-eqs may substitute only explicit equality facts reconstructed from
       assertions that this proof has already replayed. *)
    (let
       val theorem = rewrite_profile "asserted-equality-substitution"
         "rewrite(25c)(asserted-equality-substitution)"
         (asserted_equality_substitution_prove
           (HOLset.listItems (#asserted_hyps state))) t
     in
       (state_cache_thm state theorem, theorem)
     end
     handle Feedback.HOL_ERR holerr =>
       if SmtResource.is_resource_gate holerr then
         raise ASSERTED_EQUALITY_REWRITE_ERROR (Feedback.HOL_ERR holerr)
       else raise Feedback.HOL_ERR holerr)
    handle Feedback.HOL_ERR _ =>

    (case !deferred_unification of
       SOME (thm, asl) =>
         profile "rewrite(14)(unification:deferred-alias-return)"
           (fn () =>
             (state_define (state_cache_thm state thm) asl, thm)) ()
     | NONE => raise ERR "z3_rewrite" "no deferred proof-local definition")

    handle Feedback.HOL_ERR _ =>

    profile "rewrite(26)(unsupported)"
      (fn target =>
        raise unsupported_rewrite (#z3_version state) (!attempts) target) t
  end
  handle FP_REWRITE_ERROR error => raise error
       | BAG_REWRITE_ERROR error => raise error
       | STRING_REWRITE_ERROR error => raise error
       | BV_REWRITE_ERROR error => raise error
       | DEFINITION_REWRITE_ERROR error => raise error
       | ASSERTED_EQUALITY_REWRITE_ERROR error => raise error

  fun z3_rewrite_entry (state, target) =
  if SmtRegLanProve.is_equiv target then
    (state, SmtRegLanProve.rewrite target)
  else
  (* Perform the String resource admission before canonical orientation.  The
     latter is a generic conversion and can otherwise walk an oversized
     String concatenation spine before the owning budget gets a chance to
     reject it. *)
  let
    val direct_string_equality =
      case Lib.total boolSyntax.dest_eq target of
        SOME (left, right) =>
          Library.type_contains_string (Term.type_of left) orelse
          Library.type_contains_string (Term.type_of right)
      | NONE => false
    val _ = if direct_string_equality then
      SmtResource.check_resource_goal "String" "rewrite" target
    else ()
  in
  case Lib.total rewrite_boolean_constant_schema target of
    SOME theorem => (state, theorem)
  | NONE =>
  (case SOME (rewrite_fp_packed_atom target)
      handle Feedback.HOL_ERR holerr =>
        if SmtResource.is_resource_gate holerr then
          raise Feedback.HOL_ERR holerr
        else NONE
           | SmtFpGraph.Declined _ => NONE of
     SOME theorem => (state, theorem)
   | NONE =>
  (case SOME (rewrite_fp_sub_boolean_normal_form target)
      handle Feedback.HOL_ERR holerr =>
        if SmtResource.is_resource_gate holerr then
          raise Feedback.HOL_ERR holerr
        else NONE of
     SOME theorem => (state, theorem)
   | NONE => let
    val trace = OS.Process.getEnv "HOL4_Z3_REPLAY_TRACE" = SOME "1" andalso
      !replay_completed_steps < 100
    val _ = if trace then
      (Feedback.HOL_MESG "Z3 rewrite: begin";
       TextIO.flushOut TextIO.stdOut) else ()
    val orientation =
      profile "rewrite(entry)(canonical-orientation)"
        (Conv.QCHANGED_CONV SmtReplayCanon.z3_rewrite_canon_conv) target
      handle Conv.UNCHANGED => Thm.REFL target
    val _ = if trace then
      (Feedback.HOL_MESG "Z3 rewrite: canonicalized";
       TextIO.flushOut TextIO.stdOut) else ()
    val canonical = boolSyntax.rhs (Thm.concl orientation)
    val (state, theorem) = z3_rewrite (state, canonical)
    val _ = if trace then
      (Feedback.HOL_MESG "Z3 rewrite: proved";
       TextIO.flushOut TextIO.stdOut) else ()
  in
    (state, Thm.EQ_MP (Thm.SYM orientation) theorem)
  end))
  end

  (* |- ~(!x. P x y) <=> ~(P (sk y) y)
     |- (?x. P x y) <=> P (sk y) y *)
  fun z3_skolem (state, t) =
  let
    val lhs = Lib.fst (boolSyntax.dest_eq t)
    fun skolem_theorem term =
      if boolSyntax.is_exists term then
        HolSmtTheory.SKOLEM_EXISTS
      else
        case Lib.total boolSyntax.dest_neg term of
          SOME body =>
            if boolSyntax.is_forall body then
              HolSmtTheory.SKOLEM_FORALL
            else
              raise ERR "z3_skolem" "expected a quantified formula"
        | NONE => raise ERR "z3_skolem" "expected a quantified formula"
    fun definition {redex, residue} =
      if HOLset.member (#var_set state, redex) then
        redex |-> Thm.ASSUME (boolSyntax.mk_eq (redex, residue))
      else
        raise ERR "z3_skolem"
          "match produced a definition for a non-Z3 variable"
    fun instantiate accumulated substs =
      let
        fun reverse {redex, residue} = redex |-> Thm.SYM residue
        val conversion = Drule.SUBST_CONV
          (List.map (reverse o definition) substs) t
          (Thm.concl accumulated)
      in
        Thm.EQ_MP conversion accumulated
      end
    fun higher_order accumulated =
      let
        val rigid = HOLset.difference
          (Term.FVL_dag [t] Term.empty_tmset, #var_set state)
        val (substs, tyins) =
          HolKernel.ho_match_term [] rigid t (Thm.concl accumulated)
        val _ = List.null tyins orelse
          raise ERR "z3_skolem" "match instantiated a fixed type variable"
        (* Applied witnesses need lambda definitions.  Check their beta
           instance against the SELECT theorem before recording them. *)
        val conversion = Drule.SUBST_CONV
          (List.map definition substs) t t
        val conversion = Conv.CONV_RULE
          (Conv.RAND_CONV (Conv.TOP_DEPTH_CONV Thm.BETA_CONV)) conversion
        val accumulated = Conv.CONV_RULE
          (Conv.TOP_DEPTH_CONV Thm.BETA_CONV) accumulated
      in
        Thm.EQ_MP (Thm.SYM conversion) accumulated
      end
    (* Z3 may skolemize all or only a prefix of a binder block.  Peel at
       least one binder (this is the [sk] rule), then stop at the first
       prefix whose conclusion matches the recorded result. *)
    fun peel current accumulated =
      let
        val step = Conv.HO_REWR_CONV
          (Drule.SELECT_RULE (skolem_theorem current)) current
        val accumulated = Thm.TRANS accumulated step
        fun matched theorem =
          case Lib.total (Term.match_term t) (Thm.concl theorem) of
            SOME (substs, _) => SOME (instantiate theorem substs)
          | NONE => Lib.total higher_order theorem
      in
        case matched accumulated of
          SOME theorem => theorem
        | NONE =>
            let
              (* Simplify only the skolemized side, and only after the exact
                 prefix misses.  Simplifying the whole equivalence would also
                 turn [~(!x. ~P x)] into an existential, losing Z3's left
                 side; doing it eagerly penalizes every ordinary skolem. *)
              val normalized = Conv.CONV_RULE
                (Conv.RAND_CONV
                  (simpLib.SIMP_CONV boolSimps.bool_ss [])) accumulated
            in
              case matched normalized of
                SOME theorem => theorem
              | NONE => peel (boolSyntax.rhs (Thm.concl step)) accumulated
            end
      end
    val thm = peel lhs (Thm.REFL lhs)
    val asl = Thm.hyp thm
  in
    (state_define state asl, thm)
  end

  fun z3_symm (state, thm, t) =
    (state, if SmtRegLanProve.is_equiv (Thm.concl thm) then
       SmtRegLanProve.sym thm else Thm.SYM thm)

  datatype th_lemma_cache_policy =
      D1PerformanceCache
    | SemanticProofLocalLookup

  fun skeleton_general_attempt state target =
    (SmtResource.check_dag_size_for "Skeleton" "general-reduction"
       (SmtResource.dag_nodes_up_to
          (SmtResource.max_skeleton_replay_dag_nodes + 1) target);
     SmtSkeletonDispatch.attempt (#skeleton_context state) target)

  fun skeleton_general_success result =
    profile "th_lemma[general](success)"
      (fn () => #theorem result) ()

  fun th_lemma_wrapper cache_policy (name : string)
    (th_lemma_implementation : state * Term.term -> state * Thm.thm)
    (state, thms, t) : state * Thm.thm =
  let
    val t' = boolSyntax.list_mk_imp (List.map Thm.concl thms, t)
    val has_proforma = name = "arith" orelse name = "array"
    val cache_rung = if has_proforma then "2" else "1"
    fun cached target =
      case cache_policy of
        D1PerformanceCache =>
          (* E1(c): fallback re-proves this redundant cache's family. *)
          Library.require_fastpath "Z3 th-lemma theorem cache" target
            (state_inst_cached_thm state) target
      | SemanticProofLocalLookup =>
          (* E1(a): finite checked-state lookup and instantiation is complete. *)
          state_inst_cached_thm state target
    fun checked_general target =
      case skeleton_general_attempt state target of
        SmtSkeletonDispatch.Proved result =>
          (state, skeleton_general_success result)
      | SmtSkeletonDispatch.Declined =>
          th_lemma_implementation (state, target)
    fun general () =
      ((state,
        profile ("th_lemma[" ^ name ^ "](" ^ cache_rung ^ ")(cache)")
          cached t')
      handle Feedback.HOL_ERR _ =>
        (* do actual work to derive the theorem *)
        checked_general t')
    val (state, thm) =
      if has_proforma then
        ((state,
          (* E1(c): th-lemma proformas are redundant performance caches. *)
          profile ("th_lemma[" ^ name ^ "](1)(proforma)")
            (fn target =>
              Library.require_fastpath "Z3 th-lemma proforma" target
                (Z3_ProformaThms.prove
                  Z3_ProformaThms.th_lemma_thms) target)
            t')
         handle Feedback.HOL_ERR _ => general ())
      else general ()
  in
    (state, Drule.LIST_MP thms thm)
  end

  (* Bags have no Z3 proof-theory tag: their encoded count arrays arrive at
     the arith or array registry entries below.  Retain a dedicated wrapper
     nevertheless so the bag route has the same cache/proforma discipline and
     profile identity as every other checked theory re-prover. *)
  val z3_th_lemma_bag =
    th_lemma_wrapper D1PerformanceCache "bag" (fn (state, t) =>
    let
      (* E1(b): the general Bag prover fails loudly outside its family. *)
      val thm = profile "th_lemma[bag](2)(bag_prove)"
        (SmtBagProve.bag_prove_with_arith arith_prove) t
    in
      (state_cache_thm state thm, thm)
    end)

  val bv_th_lemma_prove_raw =
  let
    (* Keep SIMP_TAC for conditional rewrites.  A 2026-07-08 Poly/ML 5.9.2
       retry with PURE_REWRITE_TAC did not reproduce the old segfault in the
       unit phase, but the full selftest run did not finish promptly after
       entering functional tests. *)
    val COND_REWRITE_TAC = simpLib.SIMP_TAC
      simpLib.empty_ss [boolTheory.COND_RAND, boolTheory.COND_RATOR]
    val PROFILED_BBLAST_CONV =
      blastLib.BBLAST_CONV_WITH_PROFILES
        (profile "th_lemma[bv](3)(COND_BBLAST:WORD_SIMP_CONV)")
        (profile "th_lemma[bv](3)(COND_BBLAST:BIT_TAUT_CONV)")
  in
    fn t =>
      (* E1(a): conditional normalization plus BBLAST decides BV.  Profile
         the actual simplification and propositional phases inside the
         complete converter; no speculative word-equality shortcut
         precedes this route. *)
      profile "th_lemma[bv](3)(COND_BBLAST)" Tactical.prove (t,
        Tactical.THEN
          (COND_REWRITE_TAC, Tactic.CONV_TAC PROFILED_BBLAST_CONV))
  end

  fun bv_concat_schema_prove target =
    let
      val _ = boolSyntax.is_eq target orelse
        raise ERR "bv_concat_schema_prove"
          "not a word equality"
      val (left, _) = boolSyntax.dest_eq target
      val _ = wordsSyntax.is_word_type (Term.type_of left) orelse
        raise ERR "bv_concat_schema_prove"
          "equality is not over words"
      val substitutions = ref
        ([] : {redex : Term.term, residue : Term.term} list)
      val sources = ref ([] : (Term.term * Term.term) list)
      val memo = ref
        (Redblackmap.mkDict Term.compare :
          (Term.term, Term.term) Redblackmap.dict)
      fun payload term =
        if wordsSyntax.is_word_literal term then term
        else
          case List.find (fn (source, _) => Term.aconv source term)
              (!sources) of
            SOME (_, variable) => variable
          | NONE =>
              let
                val variable = Term.genvar (Term.type_of term)
                val _ = sources := (term, variable) :: !sources
                val _ = substitutions :=
                  {redex = variable, residue = term} :: !substitutions
              in variable end
      fun abstract term =
        case Redblackmap.peek (!memo, term) of
          SOME result => result
        | NONE =>
            let
              val result =
                if wordsSyntax.is_word_concat term then
                  let
                    val (first, second) =
                      wordsSyntax.dest_word_concat term
                    fun argument part =
                      if wordsSyntax.is_word_concat part then
                        abstract part
                      else payload part
                  in wordsSyntax.mk_word_concat
                    (argument first, argument second) end
                else if Term.is_comb term then
                  Term.mk_comb
                    (abstract (Term.rator term),
                     abstract (Term.rand term))
                else term
              val _ = memo := Redblackmap.insert (!memo, term, result)
            in result end
      val schematic = abstract target
      val _ = List.null (!substitutions) andalso
        raise ERR "bv_concat_schema_prove"
          "no concatenation payload to abstract"
      val _ = if OS.Process.getEnv "HOL4_Z3_REPLAY_TRACE" = SOME "1" then
        (Feedback.HOL_MESG
          ("Z3 BV concat schema: payloads=" ^
           Int.toString (List.length (!substitutions)) ^
           " nodes=" ^
           Int.toString (SmtResource.dag_nodes_up_to 10001 schematic));
         TextIO.flushOut TextIO.stdOut)
        else ()
      val law = blastLib.BBLAST_PROVE schematic
        handle Feedback.HOL_ERR holerr =>
          (if OS.Process.getEnv "HOL4_Z3_REPLAY_TRACE" = SOME "1" then
             (Feedback.HOL_MESG
               ("Z3 BV concat schema: declined=" ^
                Feedback.message_of holerr);
              TextIO.flushOut TextIO.stdOut)
           else ();
           raise Feedback.HOL_ERR holerr)
             | HolSatLib.SAT_cex _ =>
          raise ERR "bv_concat_schema_prove"
            "schematic word lemma has a counterexample"
      val _ = if OS.Process.getEnv "HOL4_Z3_REPLAY_TRACE" = SOME "1" then
        (Feedback.HOL_MESG "Z3 BV concat schema: proved";
         TextIO.flushOut TextIO.stdOut)
        else ()
      val theorem = Thm.INST (!substitutions) law
      val _ = Term.aconv (Thm.concl theorem) target orelse
        raise ERR "bv_concat_schema_prove"
          "schema endpoint mismatch"
    in theorem end

  fun bv_th_lemma_prove target =
    (require_bv_family "bv-th-lemma" target;
     bv_resource_prove_after_admission
       "bv-th-lemma" bv_concat_schema_prove target
     handle Feedback.HOL_ERR holerr =>
       if SmtResource.is_resource_gate holerr then
         raise Feedback.HOL_ERR holerr
       else bv_resource_prove_after_admission
         "bv-th-lemma" bv_th_lemma_prove_raw target)

  fun bv_th_lemma_basic_branch prove decline fallback target =
    if has_word_atom target then
      bv_next_rung prove fallback target
    else
      decline target

  fun arith_bv_fallback t fallback holerr =
    if SmtResource.is_resource_gate holerr then
      raise Feedback.HOL_ERR holerr
    else if has_word_atom t then
      fallback t
    else
      raise Feedback.HOL_ERR holerr

  (* The single production entry for TASK_19's propositionally-valid modulo
     atom-expansion class.  Admission is a code-level precondition in the
     dispatcher; a normal decline/failure lets the owning legacy theory rung
     run, while resource rejection always terminates the ladder. *)
  val z3_th_lemma_arith_generic =
    th_lemma_wrapper D1PerformanceCache "arith" (fn (state, t) =>
    let
      (* Arithmetic certificates for Char comparisons contain the same
         let-expanded bit sums as Char certificates.  Compact and normalize
         those sums before invoking linear arithmetic; EQ_MP below transports
         the checked result back to Z3's exact declared clause. *)
      val is_character_arithmetic =
        SmtStringProve.char_word_expansion_domain t
      val normalization =
        if is_character_arithmetic then
          SmtStringProve.compact_char_word_core t
          handle Feedback.HOL_ERR holerr =>
            if SmtResource.is_resource_gate holerr then
              raise Feedback.HOL_ERR holerr
            else Thm.REFL t
        else Thm.REFL t
      val normalized = boolSyntax.rhs (Thm.concl normalization)
        handle Feedback.HOL_ERR _ => raise ERR "z3_th_lemma_arith"
          ("normalizer did not return an equality: " ^
           Library.thm_to_string normalization)
      (* Z3's mixed Char/arithmetic clauses expose Boolean guards as
         conditional integer weights.  Prove the admitted additive bound
         directly from general endpoint lemmas, avoiding an exponential
         conditional split. *)
      fun weighted_sum_arith_prove target =
        let
          val conditionals = HolKernel.find_terms boolSyntax.is_cond target
          fun strip_clause term antecedents =
            if boolSyntax.is_neg term then
              (List.rev antecedents, term)
            else
              case Lib.total boolSyntax.dest_imp term of
                SOME (antecedent, consequent) =>
                  strip_clause consequent (antecedent :: antecedents)
              | NONE => (List.rev antecedents, term)
          val (antecedents, conclusion) = strip_clause target []
          fun endpoint_bound lower conditional =
            let
              val (guard, upper, lower_endpoint) =
                boolSyntax.dest_cond conditional
              val _ = Term.aconv lower_endpoint intSyntax.zero_tm orelse
                raise ERR "endpoint_bound" "nonzero lower endpoint"
              val assumed_guard =
                if lower then guard else boolSyntax.mk_neg guard
              val bound = if lower then
                  intSyntax.mk_leq (upper, conditional)
                else intSyntax.mk_leq (conditional, lower_endpoint)
              fun prove_from premise =
                let
                  val implication = boolSyntax.mk_imp (premise, bound)
                  val theorem = simpLib.SIMP_PROVE
                    (simpLib.++
                      (bossLib.srw_ss(), intSimps.INT_REDUCE_ss))
                    [integerTheory.int_ge,
                     smtstringz3Theory.char_bit_word18,
                     smtstringz3Theory.int_cond_weight_nonpositive,
                     smtstringz3Theory.int_cond_weight_nonnegative,
                     smtstringz3Theory.int_cond_weight_at_least]
                    implication
                in
                  Thm.MP theorem (Thm.ASSUME premise)
                end
              fun normalize_guard term =
                boolSyntax.rhs (Thm.concl
                  (simpLib.SIMP_CONV
                    (simpLib.++
                      (bossLib.srw_ss(), intSimps.INT_REDUCE_ss))
                    [smtstringz3Theory.char_bit_word18] term))
                handle Conv.UNCHANGED => term
              val expected_guard = normalize_guard assumed_guard
              val theorem =
                case List.find
                    (fn premise => Term.aconv
                      (normalize_guard premise) expected_guard)
                    antecedents of
                  SOME premise => prove_from premise
                | NONE => raise ERR "endpoint_bound"
                    "normalized endpoint guard is not an antecedent"
            in
              (if lower then upper else lower_endpoint, theorem)
            end
          fun nonnegative_fact conditional =
            let
              val theorem = Drule.SPEC_ALL
                smtstringz3Theory.int_cond_weight_nonnegative
              val proposition = intSyntax.mk_leq
                (intSyntax.zero_tm, conditional)
              val substitution =
                Term.match_term (Thm.concl theorem) proposition
            in
              Drule.INST_TY_TERM substitution theorem
            end
          fun lower_bound_term term =
            if intSyntax.is_plus term then
              let
                val (left, right) = intSyntax.dest_plus term
                val (left_bound, left_theorem) = lower_bound_term left
                val (right_bound, right_theorem) = lower_bound_term right
                val combined = Drule.MATCH_MP integerTheory.INT_LE_ADD2
                  (Thm.CONJ left_theorem right_theorem)
              in
                (intSyntax.mk_plus (left_bound, right_bound), combined)
              end
            else
              case Lib.total (endpoint_bound true) term of
                SOME result => result
              | NONE =>
                  case Lib.total nonnegative_fact term of
                    SOME theorem => (intSyntax.zero_tm, theorem)
                  | NONE => if List.null (Term.free_vars term) then
                      (term, Thm.SPEC term integerTheory.INT_LE_REFL)
                    else raise ERR "lower_bound_term"
                      "non-literal additive leaf"
          fun upper_bound_fact conditional =
            let
              val theorem = Drule.SPEC_ALL
                smtstringz3Theory.int_cond_weight_upper_bound
              val (_, upper, _) = boolSyntax.dest_cond conditional
              val proposition = intSyntax.mk_leq (conditional, upper)
              val substitution =
                Term.match_term (Thm.concl theorem) proposition
            in
              Drule.INST_TY_TERM substitution theorem
            end
          fun upper_bound_term term =
            if intSyntax.is_plus term then
              let
                val (left, right) = intSyntax.dest_plus term
                val (left_bound, left_theorem) = upper_bound_term left
                val (right_bound, right_theorem) = upper_bound_term right
                val combined = Drule.MATCH_MP integerTheory.INT_LE_ADD2
                  (Thm.CONJ left_theorem right_theorem)
              in
                (intSyntax.mk_plus (left_bound, right_bound), combined)
              end
            else
              case Lib.total (endpoint_bound false) term of
                SOME result => result
              | NONE =>
                  case Lib.total upper_bound_fact term of
                    SOME theorem =>
                      let val (_, upper, _) = boolSyntax.dest_cond term
                      in (upper, theorem) end
                  | NONE => if List.null (Term.free_vars term) then
                      (term, Thm.SPEC term integerTheory.INT_LE_REFL)
                    else raise ERR "upper_bound_term"
                      "non-literal additive leaf"
          val conclusion_body = Lib.total boolSyntax.dest_neg conclusion
          val logical_inputs = antecedents @
            (case conclusion_body of SOME body => [body] | NONE => [])
          fun denied_threshold antecedent =
            let
              val inequality = boolSyntax.dest_neg antecedent
              val (left, right) = intSyntax.dest_leq inequality
            in
              if List.null (Term.free_vars left) then
                SOME (antecedent, true, left, right)
              else if List.null (Term.free_vars right) then
                SOME (antecedent, false, right, left)
              else NONE
            end
            handle Feedback.HOL_ERR _ => NONE
          val (denied, is_lower, threshold, code) =
            case List.mapPartial denied_threshold antecedents of
              quadruple :: _ => quadruple
            | [] => raise ERR "weighted_sum_arith_prove"
                "no denied threshold"
          fun contains needle haystack = not (List.null
            (HolKernel.find_terms (Term.aconv needle) haystack))
          val difference_antecedent =
            case List.find (fn antecedent =>
              contains code antecedent andalso not (List.null
                (HolKernel.find_terms boolSyntax.is_cond antecedent)))
              logical_inputs of
              SOME antecedent => antecedent
            | NONE => raise ERR "weighted_sum_arith_prove"
                "no difference antecedent"
          fun code_difference term =
            let
              val (left, right) = intSyntax.dest_plus term
            in
              if Term.aconv left code then SOME right
              else if Term.aconv right code then SOME left
              else NONE
            end
            handle Feedback.HOL_ERR _ => NONE
          val negative_sum =
            case List.mapPartial code_difference
              (HolKernel.find_terms intSyntax.is_plus
                difference_antecedent) of
              term :: _ => term
            | [] => raise ERR "weighted_sum_arith_prove"
                "no code difference"
          val (factor_left, factor_right) =
            intSyntax.dest_mult negative_sum
          val sum =
            if List.null (HolKernel.find_terms boolSyntax.is_cond factor_left)
            then factor_right else factor_left
          val contradiction =
            if is_lower then
              let
                val (_, raw_bound) = lower_bound_term sum
                val bound = simpLib.SIMP_RULE
                  (simpLib.++ (boolSimps.bool_ss,
                    intSimps.INT_REDUCE_ss)) [] raw_bound
                val (derived_threshold, _) =
                  intSyntax.dest_leq (Thm.concl bound)
                val threshold_to_derived = intLib.ARITH_PROVE
                  (intSyntax.mk_leq (threshold, derived_threshold))
                  handle Feedback.HOL_ERR _ =>
                    raise ERR "weighted_sum_arith_prove"
                      ("lower threshold comparison failed: " ^
                       Library.term_to_string threshold ^ " <= " ^
                       Library.term_to_string derived_threshold)
                val threshold_at_most_sum = Drule.MATCH_MP
                  integerTheory.INT_LE_TRANS
                  (Thm.CONJ threshold_to_derived bound)
                val sum_at_most_code = intSyntax.mk_leq (sum, code)
                val equivalence = boolSyntax.mk_eq
                  (difference_antecedent, sum_at_most_code)
                val substitution = Term.match_term
                  (Thm.concl
                    smtstringz3Theory.int_nonnegative_add_neg_mul)
                  equivalence
                val bridge = Drule.INST_TY_TERM substitution
                  smtstringz3Theory.int_nonnegative_add_neg_mul
                val difference = Thm.EQ_MP bridge
                  (Thm.ASSUME difference_antecedent)
                val threshold_at_most_code = Drule.MATCH_MP
                  integerTheory.INT_LE_TRANS
                  (Thm.CONJ threshold_at_most_sum difference)
              in
                Thm.MP (Thm.NOT_ELIM (Thm.ASSUME denied))
                  threshold_at_most_code
              end
            else
              let
                val (_, raw_bound) = upper_bound_term sum
                val bound = simpLib.SIMP_RULE
                  (simpLib.++ (boolSimps.bool_ss,
                    intSimps.INT_REDUCE_ss)) [] raw_bound
                val (_, derived_threshold) =
                  intSyntax.dest_leq (Thm.concl bound)
                val derived_to_threshold = intLib.ARITH_PROVE
                  (intSyntax.mk_leq (derived_threshold, threshold))
                  handle Feedback.HOL_ERR _ =>
                    raise ERR "weighted_sum_arith_prove"
                      ("upper threshold comparison failed: " ^
                       Library.term_to_string derived_threshold ^ " <= " ^
                       Library.term_to_string threshold)
                val sum_at_most_threshold = Drule.MATCH_MP
                  integerTheory.INT_LE_TRANS
                  (Thm.CONJ bound derived_to_threshold)
                val code_at_most_sum = intSyntax.mk_leq (code, sum)
                val equivalence = boolSyntax.mk_eq
                  (difference_antecedent, code_at_most_sum)
                val substitution = Term.match_term
                  (Thm.concl
                    smtstringz3Theory.int_nonpositive_add_neg_mul)
                  equivalence
                val bridge = Drule.INST_TY_TERM substitution
                  smtstringz3Theory.int_nonpositive_add_neg_mul
                val difference = Thm.EQ_MP bridge
                  (Thm.ASSUME difference_antecedent)
                val code_at_most_threshold = Drule.MATCH_MP
                  integerTheory.INT_LE_TRANS
                  (Thm.CONJ difference sum_at_most_threshold)
              in
                Thm.MP (Thm.NOT_ELIM (Thm.ASSUME denied))
                  code_at_most_threshold
              end
          val proved_conclusion =
            case conclusion_body of
              SOME body => Thm.MP (Thm.SPEC body boolTheory.IMP_F)
                (Thm.DISCH body contradiction)
            | NONE => Thm.MP
                (Thm.SPEC conclusion boolTheory.FALSITY) contradiction
          val exact = List.foldr
            (fn (antecedent, theorem) => Thm.DISCH antecedent theorem)
            proved_conclusion antecedents
          val _ = Term.aconv (Thm.concl exact) target orelse
            raise ERR "weighted_sum_arith_prove"
              ("target mismatch; actual=" ^
               Library.term_to_string (Thm.concl exact) ^
               "; expected=" ^ Library.term_to_string target)
        in
          exact
        end
      fun contextual_arith_prove target =
        Tactical.prove (target,
          Tactical.THEN
            (Tactical.REPEAT Tactic.STRIP_TAC,
             Tactical.THEN
               (bossLib.FULL_SIMP_TAC
                  (simpLib.++ (bossLib.srw_ss(),
                    intSimps.INT_REDUCE_ss)) [],
                intLib.ARITH_TAC)))
      fun bounded_char_arith case_id prove target =
        SmtResource.with_resource_step_time "String" case_id prove target
      fun conditional_endpoint_prove target =
        let
          val guards = HOLset.listItems (HOLset.fromList Term.compare
            (List.map (fn conditional =>
               let val (guard, _, _) = boolSyntax.dest_cond conditional
               in guard end)
             (HolKernel.find_terms boolSyntax.is_cond target)))
          val guard =
            case guards of
              [guard] => guard
            | _ => raise ERR "conditional_endpoint_prove"
                "not a one-guard endpoint clause"
        in
          Tactical.prove (target,
            Tactical.THEN
              (Tactical.REPEAT Tactic.STRIP_TAC,
               Tactical.THEN
                 (Tactic.ASM_CASES_TAC guard,
                  bossLib.FULL_SIMP_TAC
                    (simpLib.++
                      (bossLib.srw_ss(), intSimps.INT_REDUCE_ss))
                    [integerTheory.int_ge])))
        end
      fun weighted_char_arith target =
        bounded_char_arith "z3-char-weighted-sum"
          weighted_sum_arith_prove target
      fun generic_normalized () =
        profile "th_lemma[arith](3)" arith_prove normalized
        handle Feedback.HOL_ERR holerr =>
          (* E1(a): ordinary legacy arith-tagged BV failures end in complete
             BBLAST. Resource refusals must terminate this ladder. *)
          arith_bv_fallback normalized
            (profile "th_lemma[arith](4)(bv)" bv_th_lemma_prove) holerr
      fun denied_closed_threshold antecedent =
        let
          val inequality = boolSyntax.dest_neg antecedent
          val (left, right) = intSyntax.dest_leq inequality
        in
          List.null (Term.free_vars left) orelse
          List.null (Term.free_vars right)
        end
        handle Feedback.HOL_ERR _ => false
      val (normalized_antecedents, _) = boolSyntax.strip_imp normalized
      val is_weighted_clause =
        List.exists denied_closed_threshold normalized_antecedents
      val normalized_thm =
        if Term.aconv normalized boolSyntax.T then boolTheory.TRUTH
        else if not is_character_arithmetic then generic_normalized ()
        else if List.null
          (HolKernel.find_terms boolSyntax.is_cond normalized)
        then
          (profile "th_lemma[arith](contextual-char)"
             (bounded_char_arith "z3-contextual-char"
               contextual_arith_prove) normalized
           handle Feedback.HOL_ERR holerr =>
             if SmtResource.is_resource_gate holerr then
               raise Feedback.HOL_ERR holerr
             else generic_normalized ())
        else
          (profile "th_lemma[arith](conditional-endpoint)"
             (bounded_char_arith "z3-char-conditional-endpoint"
               conditional_endpoint_prove) normalized
           handle Feedback.HOL_ERR holerr =>
             if SmtResource.is_resource_gate holerr then
               raise Feedback.HOL_ERR holerr
             else if is_weighted_clause then
               (* The weighted proof owns closed-threshold contradiction
                  clauses.  Letting a rejected member enter generic
                  arithmetic repeats broad proof search and can hide its
                  exact shape. *)
               profile "th_lemma[arith](char-conditionals)"
                 weighted_char_arith normalized
             else generic_normalized ())
      val thm = Thm.EQ_MP (Thm.SYM normalization) normalized_thm
        handle Feedback.HOL_ERR _ => raise ERR "z3_th_lemma_arith"
          ("failed to transport normalized theorem: normalization=" ^
           Library.thm_to_string normalization ^ "; theorem=" ^
           Library.thm_to_string normalized_thm)
    in
      (* cache 'thm' *)
      (state_cache_thm state thm, thm)
    end)

  val z3_th_lemma_array_generic =
    th_lemma_wrapper D1PerformanceCache "array" (fn (state, t) =>
    (let
       (* E1(b): the budgeted array procedure covers selected beta, update,
          symbolic-index and extensional shapes and fails loudly outside
          them or at its D4 boundary. *)
       val thm = profile "th_lemma[array](3)(array_prove)"
         SmtArrayProve.array_prove t
     in
       (* cache 'thm' *)
       (state_cache_thm state thm, thm)
     end
     handle Feedback.HOL_ERR holerr =>
      if SmtResource.is_resource_gate holerr then
        raise Feedback.HOL_ERR holerr
      else
        raise ERR "z3_th_lemma_array"
          ("unsupported th-lemma shape: theory=array; checked replay is only " ^
           "implemented for function-update select/store/extensionality " ^
           "lemmas; conclusion=" ^ Library.term_to_string t)))

  fun th_lemma_target (_, thms, t) =
    boolSyntax.list_mk_imp (List.map Thm.concl thms, t)

  fun z3_th_lemma_arith (args as (state, thms, _)) =
    let
      val target = th_lemma_target args
      fun legacy () =
        if SmtBagProve.has_native_bag_encoding target then
          z3_th_lemma_bag args
        else
          z3_th_lemma_arith_generic args
      fun bounded_propositional () =
        let
          val theorem = profile "th_lemma[arith](outer-taut)"
            (bounded_taut_prove "Skeleton" "z3-arith-outer-taut") target
        in
          (state, Drule.LIST_MP thms theorem)
        end
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else legacy ()
    in
      case skeleton_general_attempt state target of
        SmtSkeletonDispatch.Proved result =>
          (state, Drule.LIST_MP thms (skeleton_general_success result))
      | SmtSkeletonDispatch.Declined => bounded_propositional ()
    end

  fun z3_th_lemma_array args =
    if SmtBagProve.has_native_bag_encoding (th_lemma_target args) then
      z3_th_lemma_bag args
    else
      z3_th_lemma_array_generic args

  val z3_th_lemma_basic =
    th_lemma_wrapper D1PerformanceCache "basic" (fn (state, t) =>
    let
      fun unsupported attempts =
        raise ERR "z3_th_lemma_basic"
          ("unsupported th-lemma shape: theory=basic; " ^
           "attempted fragment classes=[" ^
           String.concatWith ", " (List.rev attempts) ^
           "]; checked replay is implemented for Boolean, arithmetic, " ^
           "bit-vector and array equality simplification lemmas; " ^
           "conclusion=" ^ Library.term_to_string t)

      fun metis attempts =
        (* E1(b): METIS is general proof search with a loud boundary. *)
        profile "th_lemma[basic](6)(METIS)" metis_prove ([], t)
        handle Feedback.HOL_ERR _ => unsupported
          ("first-order-proof-search" :: attempts)

      fun array attempts =
        if has_array_atom t then
          ((* E1(b): the budgeted selected array/set procedure has a loud
               unsupported/resource boundary. *)
           profile "th_lemma[basic](5)(array)" SmtArrayProve.array_prove t
           handle Feedback.HOL_ERR holerr =>
             if SmtResource.is_resource_gate holerr then
               raise Feedback.HOL_ERR holerr
             else metis ("array" :: attempts))
        else metis attempts

      fun bv attempts =
        bv_th_lemma_basic_branch
          (* E1(a): the terminal BBLAST route decides bit-vectors. *)
          (profile "th_lemma[basic](4)(bv)" bv_th_lemma_prove)
          (fn _ => array attempts)
          (fn _ => array ("bv" :: attempts)) t

      fun arith attempts =
        if has_arith_atom t then
          ((* E1(b): arithmetic has complete linear and loud NLA routes. *)
           profile "th_lemma[basic](3)(arith)" arith_prove t
           handle Feedback.HOL_ERR _ => bv ("arith" :: attempts))
        else bv attempts

      (* E1(a): TAUT_PROVE decides the propositional fragment. *)
      val thm = profile "th_lemma[basic](2)(TAUT_PROVE)"
        (bounded_taut_prove "Skeleton" "z3-basic-taut") t
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else arith ["boolean"]
    in
      (* cache 'thm' *)
      (state_cache_thm state thm, thm)
    end)

  val z3_th_lemma_bv =
    th_lemma_wrapper D1PerformanceCache "bv" (fn (state, t) =>
      let
        val thm = bv_th_lemma_prove t
      in
        (* cache 'thm' *)
        (state_cache_thm state thm, thm)
      end)

  val z3_th_lemma_datatype =
    th_lemma_wrapper D1PerformanceCache "datatype" (fn (state, t) =>
      let
        (* E1(b): TypeBase-driven reconstruction is general for selected
           registered datatype facts and fails loudly outside those shapes. *)
        val thm = profile "th_lemma[datatype](2)"
          SmtDatatypeProve.datatype_prove t
      in
        (* cache 'thm' *)
        (state_cache_thm state thm, thm)
      end)

  fun th_lemma_metadata_has_subkind subkinds
      ({subkind, ...} : th_lemma_metadata) =
    case subkind of
      SOME s => List.exists (Lib.equal s) subkinds
    | NONE => false

  fun advanced_th_lemma_obligation_theory ({theory, ...}
      : th_lemma_metadata) =
    case theory of
      "floating-point" => "fp"
    | "fpa" => "fp"
    | "sequence" => "seq"
    | "sequences" => "seq"
    | "strings" => "string"
    | "str" => "string"
    | "regex" => "regexp"
    | "re" => "regexp"
    | other => other

  fun advanced_th_lemma_obligation metadata =
  let
    val theory = advanced_th_lemma_obligation_theory metadata
    val feature_suffix =
      if theory = "nonlinear-arith" then "nonlinear-arith" else theory
    val feature = "proof-rule:th-lemma-" ^ feature_suffix
  in
    {missing_feature = feature, failing_case_ids = [feature]}
  end

  fun unsupported_advanced_th_lemma_message (state : state)
      (metadata : th_lemma_metadata) t =
  let
    val {missing_feature, failing_case_ids} =
      advanced_th_lemma_obligation metadata
  in
    "unsupported th-lemma shape: " ^
    th_lemma_metadata_to_string metadata ^
    "; z3_version=" ^ #z3_version state ^
    "; missing feature: " ^ missing_feature ^
    "; failing case IDs: " ^ String.concatWith ", " failing_case_ids ^
    "; proof-format limitation=Z3 does not emit a checked certificate " ^
    "for HolSmt replay of this advanced theory family; conclusion=" ^
    Library.term_to_string t
  end

  fun z3_th_lemma_advanced_unsupported metadata =
    th_lemma_wrapper SemanticProofLocalLookup
      ("advanced:" ^ #theory metadata) (fn (state, t) =>
      (* E1(b): an uncached advanced family reaches this loud boundary. *)
      profile ("th_lemma[advanced:" ^ #theory metadata ^
        "](2)(unsupported)")
        (fn target =>
          raise ERR "z3_th_lemma_advanced_unsupported"
            (unsupported_advanced_th_lemma_message state metadata target)) t)

  (* Defensive only: no th-lemma-fp occurrence was observed in any of the
     TASK_02 proofs from supported Z3 4.11.2--4.15.3.  Keep the route checked
     nonetheless, with the FP shape gate ahead of every prover rung. *)
  fun z3_th_lemma_fp _ (state, thms, t) =
  let
    val t' = boolSyntax.list_mk_imp (List.map Thm.concl thms, t)
    fun traced_head term =
      let val (head, _) = boolSyntax.strip_comb term in
        if Term.is_const head then
          let val {Thy, Name, ...} = Term.dest_thy_const head
          in Thy ^ "$" ^ Name end
        else if Term.is_var head then "variable"
        else "compound"
      end
    fun trace_fp stage =
      if (OS.Process.getEnv "HOL4_Z3_REPLAY_TRACE" = SOME "full" orelse
          OS.Process.getEnv "HOL4_Z3_REPLAY_TRACE" = SOME "1" andalso
          !replay_completed_steps < 700) then
        (Feedback.HOL_MESG
          ("Z3 FP lemma: " ^ stage ^ " nodes=" ^
           Int.toString (SmtResource.dag_nodes_up_to 1025 t') ^
           " completed=" ^ Int.toString (!replay_completed_steps) ^
           (case Lib.total boolSyntax.dest_eq t of
              SOME (left, right) =>
                " heads=" ^ traced_head left ^ "," ^ traced_head right
            | NONE => " head=" ^ traced_head t) ^
           (if stage = "begin" andalso
               OS.Process.getEnv "HOL4_Z3_REPLAY_TRACE" = SOME "full" andalso
               Option.isSome (Term.term_size_bounded 3000 t') then
              " target=" ^ SmtResource.bounded_text 2500
                (Library.term_to_string t')
            else ""));
         TextIO.flushOut TextIO.stdOut)
      else ()
    fun symbolic_fp target =
      SmtFpProve.fp_prove_with_decompositions_and_arith
        arith_prove [] target
    fun shared_fp_circuit target =
      let
        val seen = ref (HOLset.empty Term.compare)
        val fp_sources = ref ([] : Term.term list)
        val rounding_sources = ref ([] : Term.term list)
        val (rounding_var, _) = boolSyntax.dest_forall
          (Thm.concl smtfloatReplayRoundingTheory.smtfp_rounding_onehot)
        val rounding_type = Term.type_of rounding_var
        fun is_fp_source term =
          (let val {Thy, Tyop, ...} =
                 Type.dest_thy_type (Term.type_of term)
           in Thy = "smtfloat" andalso Tyop = "smtfp" andalso
              (Term.is_var term orelse boolSyntax.is_select term) end)
          handle Feedback.HOL_ERR _ => false
        fun collect term =
          if HOLset.member (!seen, term) then ()
          else
            (seen := HOLset.add (!seen, term);
             if is_fp_source term then
               fp_sources := term :: !fp_sources else ();
             if Term.type_of term = rounding_type andalso
                (Term.is_var term orelse boolSyntax.is_select term) then
               rounding_sources := term :: !rounding_sources
             else ();
             List.app collect (SmtResource.term_children term))
        val _ = collect target
        fun canonical_fact source =
          let
            val base = Drule.ISPECL [source]
              (Drule.GEN_ALL
                smtfloatReplayRoundingTheory.smtfp_rep_canonical_fields)
            val beta = Conv.TOP_DEPTH_CONV Thm.BETA_CONV
              (Thm.concl base)
              handle Conv.UNCHANGED => Thm.REFL (Thm.concl base)
          in Thm.EQ_MP beta base end
        val facts = List.map canonical_fact (!fp_sources) @
          List.map (fn mode => Thm.SPEC mode
            smtfloatReplayRoundingTheory.smtfp_rounding_onehot)
            (!rounding_sources)
        val implication = List.foldr boolSyntax.mk_imp target
          (List.map Thm.concl facts)
        val normalized =
          SmtResource.with_resource_step_time "BitVector"
            "z3-fp-shared-word-normalize"
            SmtWordGraph.normalize implication
          handle Conv.UNCHANGED => Thm.REFL implication
        val residue = boolSyntax.rhs (Thm.concl normalized)
        val circuit =
          CPC_ProofReplay.prove_boolean_circuit residue
        val proved = Thm.EQ_MP (Thm.SYM normalized) circuit
        val proof = List.foldl
          (fn (fact, theorem) => Thm.MP theorem fact) proved facts
        val _ = List.null (Thm.hyp proof) andalso
          Term.aconv (Thm.concl proof) target orelse
          raise ERR "z3_th_lemma_fp"
            "shared circuit proof did not close the exact target"
      in proof end
    fun circuit_or_symbolic target =
      if SmtResource.dag_nodes_up_to 257 target <= 256 then
        (symbolic_fp target
         handle (original as Feedback.HOL_ERR holerr) =>
           if SmtResource.is_resource_gate holerr then
             raise original
           else
             (trace_fp "symbolic declined; shared circuit begin";
              shared_fp_circuit target
              handle Feedback.HOL_ERR circuit_err =>
                if SmtResource.is_resource_gate circuit_err then
                  raise Feedback.HOL_ERR circuit_err
                else raise original
                   | HolSatLib.SAT_cex _ => raise original
                   | HolSatLib.SAT_satisfiable _ => raise original))
      else
        (trace_fp "shared circuit begin";
         shared_fp_circuit target
         handle Feedback.HOL_ERR holerr =>
           if SmtResource.is_resource_gate holerr then
             raise Feedback.HOL_ERR holerr
           else
             (trace_fp ("shared circuit declined: " ^
               SmtResource.bounded_text 160
                 (Feedback.message_of holerr));
              symbolic_fp target)
              | HolSatLib.SAT_cex _ =>
             (trace_fp "shared circuit declined: SAT abstraction";
              symbolic_fp target)
              | HolSatLib.SAT_satisfiable _ =>
             (trace_fp "shared circuit declined: SAT abstraction";
              symbolic_fp target))
    val () =
      if SmtFpProve.has_fp_theory_term t' then ()
      else SmtFpProve.unsupported t'
    val _ = trace_fp "begin"
    val (general, thm) =
      case Lib.total (state_inst_cached_thm state) t' of
        SOME cached => (true, cached)
      | NONE =>
        (case skeleton_general_attempt state t' of
          SmtSkeletonDispatch.Proved result =>
            (true, skeleton_general_success result)
        | SmtSkeletonDispatch.Declined =>
          (* E1(b): checked lowering is the general selected FP th-lemma
             procedure and fails loudly at its unsupported/D4 boundary. *)
          (false,
           (profile "th_lemma[fp](pack-roundtrip)"
              rewrite_fp_pack_roundtrip t'
            handle Feedback.HOL_ERR holerr =>
              if SmtResource.is_resource_gate holerr then
                raise Feedback.HOL_ERR holerr
              else
                (trace_fp
                   ("pack-roundtrip declined: " ^
                    Feedback.message_of holerr);
                 profile "th_lemma[fp](packed-atom)"
                   rewrite_fp_packed_atom t'
                 handle Feedback.HOL_ERR holerr =>
                   if SmtResource.is_resource_gate holerr then
                     raise Feedback.HOL_ERR holerr
                   else profile "th_lemma[fp](1)"
                     circuit_or_symbolic t')
                 | SmtFpGraph.Declined _ =>
              profile "th_lemma[fp](1)"
                circuit_or_symbolic t')))
    val _ = trace_fp "proved"
    val state' =
      if general then state
      else
        (trace_fp "cache begin";
         let val cached = state_cache_thm state thm
         in trace_fp "cache end"; cached end)
    val _ = trace_fp "apply begin"
    val applied = Drule.LIST_MP thms thm
    val _ = trace_fp "apply end"
  in
    (state', applied)
  end

  fun z3_th_lemma_advanced metadata =
    if advanced_th_lemma_obligation_theory metadata = "fp" then
      z3_th_lemma_fp metadata
    else
      z3_th_lemma_advanced_unsupported metadata

  fun unsupported_string_th_lemma_message dispatch_theory
      (state : state) (metadata : th_lemma_metadata) t =
  let
    val {missing_feature, failing_case_ids} =
      advanced_th_lemma_obligation metadata
  in
    "unsupported th-lemma shape: theory=" ^ dispatch_theory ^ "; " ^
    th_lemma_metadata_to_string metadata ^
    "; z3_version=" ^ #z3_version state ^
    "; missing feature: " ^ missing_feature ^
    "; failing case IDs: " ^ String.concatWith ", " failing_case_ids ^
    "; proof-format limitation=the checked string prover has no rung for " ^
    "this clause shape; conclusion=" ^ Library.term_to_string t
  end

  (* All String th-lemma routes use this single transition.  A resource gate
     is a terminal structured rejection, whereas an ordinary HOL_ERR means
     only that the next checked route may be attempted. *)
  fun string_th_lemma_next_route attempt fallback =
    attempt ()
    handle Feedback.HOL_ERR holerr =>
      if SmtResource.is_resource_gate holerr then
        raise Feedback.HOL_ERR holerr
      else
        fallback ()

  (* `gate` runs the theory preconditions that must surface their own
     enumerated diagnostic.  Deciding this before the prover keeps the gate
     distinguishable from an ordinary prover failure — the contextual rung
     below would otherwise mask a gated clause behind the generic unsupported
     message. *)
  fun string_th_lemma_wrapper dispatch_theory gate metadata prover
      (state, thms, t) =
  let
    val t' = boolSyntax.list_mk_imp (List.map Thm.concl thms, t)
    val context = HOLset.listItems (#asserted_hyps state)
    val () = gate t'
    (* Run the bounded DAG-aware family scan before the common attempt.  Once
       the String/character metadata guard has admitted the node, every
       target is offered: owned bridge atoms may be reduced while symbolic
       String leaves remain as propositional residuals. *)
    val _ = SmtStringProve.check_string_family_admission t'
    fun theory () =
      (* E1(b): the general String/regex procedure gates its family. *)
      profile ("th_lemma[" ^ dispatch_theory ^ "](1)(theory)")
        prover t'
    fun contextual () =
      (* E1(b): contextual String/regex replay fails loudly at exit. *)
      profile ("th_lemma[" ^ dispatch_theory ^ "](2)(contextual)")
        (SmtStringProve.string_contextual_prove_cached
          (#string_index_cache state) context) t'
    fun unsupported () =
      raise ERR ("z3_th_lemma_" ^ dispatch_theory)
        (unsupported_string_th_lemma_message dispatch_theory
          state metadata t')
    fun legacy () =
      if not (List.null context) andalso
         SmtStringProve.has_contextual_index_target t'
      then
        string_th_lemma_next_route contextual (fn () =>
          string_th_lemma_next_route theory unsupported)
      else
        string_th_lemma_next_route theory (fn () =>
          string_th_lemma_next_route contextual unsupported)
    val (general, thm) =
      case skeleton_general_attempt state t' of
        SmtSkeletonDispatch.Proved result =>
          (true, skeleton_general_success result)
      | SmtSkeletonDispatch.Declined => (false, legacy ())
  in
    (if general orelse dispatch_theory = "char" then state
     else state_cache_thm state thm,
     Drule.LIST_MP thms thm)
  end

  val z3_th_lemma_native_seq =
    th_lemma_wrapper D1PerformanceCache "seq" (fn (state, t) =>
    let
      val thm =
        (* E1(b): the general Seq procedure gates its supported family. *)
        profile "th_lemma[seq](2)(seq_prove)" SmtSeqProve.seq_prove t
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else
            (* E1(b): contextual Seq replay fails loudly at its boundary. *)
            profile "th_lemma[seq](3)(contextual)"
            (SmtSeqProve.seq_contextual_prove
              (HOLset.listItems (#asserted_hyps state))) t
    in
      (state_cache_thm state thm, thm)
    end)

  (* Z3's `seq` tag covers both Phase-4 Strings and polymorphic sequences.
     The latter are native HOL lists, while String remains on its dedicated
     carrier.  Keep the existing string wrapper intact for the former and
     select the native re-prover before any string-specific fallback. *)
  fun z3_th_lemma_seq metadata (args as (state, thms, t)) =
    let
      val target = boolSyntax.list_mk_imp (List.map Thm.concl thms, t)
      fun string_route () =
        string_th_lemma_wrapper "seq" SmtStringProve.check_seq_type
          metadata (SmtStringProve.string_prove arith_prove) args
      fun direct_head_tail theorem =
        let
          fun attempt theorem =
            let
              val substitution = Term.match_term (Thm.concl theorem) t
              val instance = Drule.INST_TY_TERM substitution theorem
              val _ = Term.aconv (Thm.concl instance) t orelse
                raise ERR "z3_th_lemma_seq" "direct instance mismatch"
            in
              instance
            end
          val theorem = Drule.SPEC_ALL theorem
          val instance = attempt theorem
            handle Feedback.HOL_ERR _ => attempt (Thm.SYM theorem)
        in
          (state, instance)
        end
      val direct = Lib.total (Lib.tryfind direct_head_tail)
        [smtstringz3Theory.seq_head_tail_word18,
         smtstringz3Theory.seq_head_tail_word18_z3_index,
         smtstringz3Theory.seq_head_tail_word18_eq,
         smtstringz3Theory.smtstr_from_code_length_valid_clause,
         smtstringz3Theory.smtstr_to_code_length_one_lower_clause,
         smtstringz3Theory.smtstr_to_code_length_one_upper_clause,
         smtstringz3Theory.char_seq_unit_inv,
         smtstringz3Theory.seq_head_tail_word18_z3_index]
    in
      case direct of
        SOME result => result
      | NONE => if SmtSeqProve.has_seq_type target then
        z3_th_lemma_native_seq args
      else
        case (SOME (SmtStringProve.replay_parametric_seq_prove target)
              handle Feedback.HOL_ERR holerr =>
                if SmtResource.is_resource_gate holerr then
                  raise Feedback.HOL_ERR holerr
                else NONE) of
          SOME theorem => (state, Drule.LIST_MP thms theorem)
        | NONE => string_route ()
    end

  fun z3_th_lemma_char metadata =
    string_th_lemma_wrapper "char" (fn _ => ()) metadata
      SmtStringProve.char_prove

  fun z3_trans (state, thm1, thm2, t) =
    (state, if SmtRegLanProve.is_equiv t then
       SmtRegLanProve.trans thm1 thm2 else Thm.TRANS thm1 thm2)

  (* `z3_trans_star` is supposed to handle multiple symmetry and transitivity
     rules. Z3 provides the following example:

     A1 |- R a b   A2 |- R c b   A3 |- R c d
     --------------------------------------- trans*
                A1 u A2 u A3 |- R a d

     Although more generally, the proof rule is supposed to handle any number of
     theorems passed as arguments and any path between the elements.

     R must be a symmetric and transitive relation. Equality is the only
     relation observed in Z3 proof traces, so replay equality chains directly
     and keep METIS only as a measurable fallback. *)

  fun trans_star_exact_prove (thms, t) =
  let
    fun term_eq (t1, t2) = Term.compare (t1, t2) = EQUAL
    fun term_member tm = List.exists (fn tm' => term_eq (tm, tm'))
    val (lhs, rhs) = boolSyntax.dest_eq t
      handle Feedback.HOL_ERR _ =>
        raise ERR "trans_star_exact_prove"
          ("conclusion is not an equation: " ^ Library.term_to_string t)
    fun edge_thms thm =
      let
        val (l, r) = boolSyntax.dest_eq (Thm.concl thm)
          handle Feedback.HOL_ERR _ =>
            raise ERR "trans_star_exact_prove"
              ("premise is not an equation: " ^
               Library.term_to_string (Thm.concl thm))
      in
        [(l, r, thm), (r, l, Thm.SYM thm)]
      end
    val edges = List.concat (List.map edge_thms thms)
    fun outgoing tm =
      List.filter (fn (from, _, _) => term_eq (from, tm)) edges
    fun search [] _ = NONE
      | search ((node, path) :: rest) visited =
          if term_eq (node, rhs) then
            SOME (List.rev path)
          else
            let
              fun add_edge ((_, next, thm), (queue, visited')) =
                if term_member next visited' then
                  (queue, visited')
                else
                  ((next, thm :: path) :: queue, next :: visited')
              val (new_queue, visited') =
                List.foldl add_edge ([], visited) (outgoing node)
            in
              search (rest @ List.rev new_queue) visited'
            end
    fun chain [] = Thm.ALPHA lhs rhs
      | chain (thm :: thms') =
          List.foldl (fn (next, acc) => Thm.TRANS acc next) thm thms'
  in
    case search [(lhs, [])] [lhs] of
      SOME path => chain path
    | NONE =>
        raise ERR "trans_star_exact_prove"
          ("no equality path from " ^ Library.term_to_string lhs ^
           " to " ^ Library.term_to_string rhs ^ " through " ^
           Int.toString (List.length thms) ^ " premise(s)")
  end

  fun z3_trans_star (state, thms, t) =
    if SmtRegLanProve.is_equiv t then
      (state, SmtRegLanProve.congruence thms t)
    else (state, profile "trans_star[exact]"
      trans_star_exact_prove (thms, t))
    handle (exact_err as Feedback.HOL_ERR _) =>
      (state, profile "trans_star[metis-fallback]" metis_prove (thms, t))
      handle Feedback.HOL_ERR _ => raise exact_err

  fun z3_true_axiom (state, t) =
    (state, boolTheory.TRUTH)

  fun z3_unit_resolution (state, thms, t) =
    (state, unit_resolution (thms, t))

  (* end of inference rule implementations *)

  (***************************************************************************)
  (* proof traversal, turning proofterms into theorems                       *)
  (***************************************************************************)

  fun take _ [] = []
    | take 0 _ = []
    | take n (x :: xs) = x :: take (n - 1) xs

  fun term_diag tm =
    Library.term_to_string tm
    handle _ => "<unprintable term>"

  fun thm_diag thm =
    Library.thm_to_string thm
    handle _ => "<unprintable theorem>"

  fun list_summary item_to_string items =
  let
    val total = List.length items
    val shown = take 3 items
    val body = String.concatWith ", " (List.map item_to_string shown)
    val more = if total > List.length shown then ", ..." else ""
  in
    "[" ^ body ^ more ^ "]"
  end

  fun term_set_summary label set =
    label ^ "=" ^ Int.toString (HOLset.numItems set) ^ " " ^
    list_summary term_diag (HOLset.listItems set)

  fun state_summary (state : state) =
    String.concatWith "; " [
      term_set_summary "asserted_hyps" (#asserted_hyps state),
      term_set_summary "definition_hyps" (#definition_hyps state),
      term_set_summary "z3_vars" (#var_set state),
      "bit_decompositions=" ^ Int.toString
        (List.length (#bit_decompositions state)),
      "translation_definitions=" ^ Int.toString
        (List.length (#translation_definitions state)),
      "z3_version=" ^ #z3_version state
    ]

  fun proofterm_replay_handler (AND_ELIM _) = "and_elim"
    | proofterm_replay_handler (APPLY_DEF _) = "apply_def"
    | proofterm_replay_handler (ASSERTED _) = "asserted"
    | proofterm_replay_handler (COMMUTATIVITY _) = "commutativity"
    | proofterm_replay_handler (DEF_AXIOM _) = "def_axiom"
    | proofterm_replay_handler (ELIM_UNUSED _) = "elim_unused"
    | proofterm_replay_handler (HYPOTHESIS _) = "hypothesis"
    | proofterm_replay_handler (IFF_FALSE _) = "iff_false"
    | proofterm_replay_handler (IFF_TRUE _) = "iff_true"
    | proofterm_replay_handler (INTRO_DEF _) = "intro_def"
    | proofterm_replay_handler (LEMMA _) = "lemma"
    | proofterm_replay_handler (MONOTONICITY _) = "monotonicity"
    | proofterm_replay_handler (MP _) = "mp"
    | proofterm_replay_handler (MP_EQ _) = "mp_eq"
    | proofterm_replay_handler (NNF_NEG _) = "nnf_neg"
    | proofterm_replay_handler (NNF_POS _) = "nnf_pos"
    | proofterm_replay_handler (NOT_OR_ELIM _) = "not_or_elim"
    | proofterm_replay_handler (PROOF_BIND _) = "proof_bind"
    | proofterm_replay_handler (QUANT_INST _) = "quant_inst"
    | proofterm_replay_handler (QUANT_INTRO _) = "quant_intro"
    | proofterm_replay_handler (REFL _) = "refl"
    | proofterm_replay_handler (REWRITE _) = "rewrite"
    | proofterm_replay_handler (SKOLEM _) = "skolem"
    | proofterm_replay_handler (SYMM _) = "symm"
    | proofterm_replay_handler (TH_LEMMA_ARITH _) = "th_lemma[arith]"
    | proofterm_replay_handler (TH_LEMMA_ARRAY _) = "th_lemma[array]"
    | proofterm_replay_handler (TH_LEMMA_BASIC _) = "th_lemma[basic]"
    | proofterm_replay_handler (TH_LEMMA_BV _) = "th_lemma[bv]"
    | proofterm_replay_handler (TH_LEMMA_DATATYPE _) = "th_lemma[datatype]"
    | proofterm_replay_handler (TH_LEMMA_SEQ _) = "th_lemma[seq]"
    | proofterm_replay_handler (TH_LEMMA_CHAR _) = "th_lemma[char]"
    | proofterm_replay_handler (TH_LEMMA_ADVANCED _) = "th_lemma[advanced]"
    | proofterm_replay_handler (TRANS _) = "trans"
    | proofterm_replay_handler (TRANS_STAR _) = "trans_star"
    | proofterm_replay_handler (TRUE_AXIOM _) = "true_axiom"
    | proofterm_replay_handler (UNIT_RESOLUTION _) = "unit_resolution"
    | proofterm_replay_handler (ID id) = "@" ^ Int.toString id
    | proofterm_replay_handler (THEOREM _) = "<replayed theorem>"

  fun proofterm_rule (ID id) = "@" ^ Int.toString id
    | proofterm_rule (THEOREM _) = "<replayed theorem>"
    | proofterm_rule (TH_LEMMA_ARITH (metadata, _, _)) =
        th_lemma_rule_name metadata
    | proofterm_rule (TH_LEMMA_ARRAY (metadata, _, _)) =
        th_lemma_rule_name metadata
    | proofterm_rule (TH_LEMMA_BASIC (metadata, _, _)) =
        th_lemma_rule_name metadata
    | proofterm_rule (TH_LEMMA_BV (metadata, _, _)) =
        th_lemma_rule_name metadata
    | proofterm_rule (TH_LEMMA_DATATYPE (metadata, _, _)) =
        th_lemma_rule_name metadata
    | proofterm_rule (TH_LEMMA_SEQ (metadata, _, _)) =
        th_lemma_rule_name metadata
    | proofterm_rule (TH_LEMMA_CHAR (metadata, _, _)) =
        th_lemma_rule_name metadata
    | proofterm_rule (TH_LEMMA_ADVANCED (metadata, _, _)) =
        th_lemma_rule_name metadata
    | proofterm_rule pt =
        (case lookup_rule_by_handler (proofterm_replay_handler pt) of
          SOME rule => #name rule
        | NONE => proofterm_replay_handler pt)

  fun proofterm_concl (AND_ELIM (_, concl)) = SOME concl
    | proofterm_concl (APPLY_DEF (_, concl)) = SOME concl
    | proofterm_concl (ASSERTED concl) = SOME concl
    | proofterm_concl (COMMUTATIVITY concl) = SOME concl
    | proofterm_concl (DEF_AXIOM concl) = SOME concl
    | proofterm_concl (ELIM_UNUSED concl) = SOME concl
    | proofterm_concl (HYPOTHESIS concl) = SOME concl
    | proofterm_concl (IFF_FALSE (_, concl)) = SOME concl
    | proofterm_concl (IFF_TRUE (_, concl)) = SOME concl
    | proofterm_concl (INTRO_DEF concl) = SOME concl
    | proofterm_concl (LEMMA (_, concl)) = SOME concl
    | proofterm_concl (MONOTONICITY (_, concl)) = SOME concl
    | proofterm_concl (MP (_, _, concl)) = SOME concl
    | proofterm_concl (MP_EQ (_, _, concl)) = SOME concl
    | proofterm_concl (NNF_NEG (_, concl)) = SOME concl
    | proofterm_concl (NNF_POS (_, concl)) = SOME concl
    | proofterm_concl (NOT_OR_ELIM (_, concl)) = SOME concl
    | proofterm_concl (PROOF_BIND _) = NONE
    | proofterm_concl (QUANT_INST (_, concl)) = SOME concl
    | proofterm_concl (QUANT_INTRO (_, concl)) = SOME concl
    | proofterm_concl (REFL concl) = SOME concl
    | proofterm_concl (REWRITE concl) = SOME concl
    | proofterm_concl (SKOLEM concl) = SOME concl
    | proofterm_concl (SYMM (_, concl)) = SOME concl
    | proofterm_concl (TH_LEMMA_ARITH (_, _, concl)) = SOME concl
    | proofterm_concl (TH_LEMMA_ARRAY (_, _, concl)) = SOME concl
    | proofterm_concl (TH_LEMMA_BASIC (_, _, concl)) = SOME concl
    | proofterm_concl (TH_LEMMA_BV (_, _, concl)) = SOME concl
    | proofterm_concl (TH_LEMMA_DATATYPE (_, _, concl)) = SOME concl
    | proofterm_concl (TH_LEMMA_SEQ (_, _, concl)) = SOME concl
    | proofterm_concl (TH_LEMMA_CHAR (_, _, concl)) = SOME concl
    | proofterm_concl (TH_LEMMA_ADVANCED (_, _, concl)) = SOME concl
    | proofterm_concl (TRANS (_, _, concl)) = SOME concl
    | proofterm_concl (TRANS_STAR (_, concl)) = SOME concl
    | proofterm_concl (TRUE_AXIOM concl) = SOME concl
    | proofterm_concl (UNIT_RESOLUTION (_, concl)) = SOME concl
    | proofterm_concl (ID _) = NONE
    | proofterm_concl (THEOREM thm) = SOME (Thm.concl thm)

  (* Construct timeout attribution only while unwinding the E0 boundary.
     Direct premises are sampled without descending into the proof tree, and
     the conclusion uses the same fixed DAG bound as skeleton diagnostics. *)
  fun proofterm_local_structure proofterm =
    let
      val premise_limit = 64
      fun premise_ref (ID id) = "@" ^ Int.toString id
        | premise_ref (THEOREM _) = "theorem"
        | premise_ref premise = proofterm_replay_handler premise
      fun sample (0, rest, refs, count) =
            (List.rev refs, count, not (List.null rest))
        | sample (_, [], refs, count) = (List.rev refs, count, false)
        | sample (remaining, premise :: rest, refs, count) =
            sample (remaining - 1, rest,
              SmtResource.bounded_text 64 (premise_ref premise) :: refs,
              count + 1)
      val (premise_refs, premise_count, premises_more) =
        sample (premise_limit, proofterm_premises proofterm, [], 0)
      val premise_text = SmtResource.bounded_text 2048
        (String.concatWith "," premise_refs)
      val conclusion_text =
        case proofterm_concl proofterm of
          NONE => "conclusion=unavailable"
        | SOME conclusion =>
            let
              val maximum = SmtResource.max_skeleton_replay_dag_nodes
              val structure_metrics =
                SmtResource.bounded_structure maximum conclusion
              val prefix =
                "conclusion_nodes=" ^
                Int.toString (#dag_nodes structure_metrics) ^
                " conclusion_edges=" ^
                Int.toString (#edges structure_metrics) ^
                " conclusion_binder_depth=" ^
                Int.toString (#max_binder_depth structure_metrics) ^
                " conclusion_identifier_bytes=" ^
                Int.toString (#max_identifier_bytes structure_metrics) ^
                " conclusion_complete=" ^
                Bool.toString (#complete structure_metrics)
            in
              if #complete structure_metrics then
                let
                  val digest = SmtResource.bounded_graph_digest
                    (maximum + 1) conclusion
                in
                  prefix ^ " conclusion_digest=" ^ #digest digest ^
                  " conclusion_serialization_bytes=" ^
                  Int.toString (#serialization_bytes digest) ^
                  " conclusion_serialization=" ^ #serialization digest
                end
              else
                prefix ^
                " conclusion_digest=unavailable-oversized" ^
                " conclusion_serialization=<oversized>"
            end
    in
      "local_rule=" ^ SmtResource.bounded_text 96
        (proofterm_rule_name proofterm) ^
      " direct_premises_shown=" ^ Int.toString premise_count ^
      " direct_premises_more=" ^ Bool.toString premises_more ^
      " direct_premise_refs=[" ^ premise_text ^ "] " ^ conclusion_text
    end

  fun proofterm_ref (ID id) = "ID " ^ Int.toString id
    | proofterm_ref (THEOREM thm) = "THEOREM(" ^ term_diag (Thm.concl thm) ^ ")"
    | proofterm_ref pt =
        case proofterm_concl pt of
          SOME concl => proofterm_rule pt ^ "(" ^ term_diag concl ^ ")"
        | NONE => proofterm_rule pt

  fun rule_application name pts concl =
    name ^ "(premises=" ^ list_summary proofterm_ref pts ^
    ", conclusion=" ^ term_diag concl ^ ")"

  fun hol_err_diag holerr =
    Feedback.top_structure_of holerr ^ "." ^
    Feedback.top_function_of holerr ^ ": " ^
    Feedback.message_of holerr
    handle Feedback.HOL_ERR _ => Feedback.message_of holerr

  fun raise_replay_error function state name pts concl thms holerr =
    if SmtResource.is_resource_gate holerr then
      raise Feedback.HOL_ERR holerr
    else
      raise ERR function
        ("Z3 proof replay failure\n" ^
         "proof rule: " ^ name ^ "\n" ^
         "local proof subterm: " ^ rule_application name pts concl ^ "\n" ^
         "parsed HOL conclusion: " ^ term_diag concl ^ "\n" ^
         "replay state: " ^ state_summary state ^ "\n" ^
         "premise HOL theorems: " ^ list_summary thm_diag thms ^ "\n" ^
         "underlying HOL_ERR: " ^ hol_err_diag holerr)

  fun raise_final_error stage state thm holerr =
    raise ERR "check_proof"
      ("Z3 proof replay finalization failure\n" ^
       "stage: " ^ stage ^ "\n" ^
       "replay state: " ^ state_summary state ^ "\n" ^
       "local theorem: " ^ thm_diag thm ^ "\n" ^
       "underlying HOL_ERR: " ^ hol_err_diag holerr)

  (* We use a depth-first post-order traversal of the proof, checking
     each premise of a proofterm (i.e., deriving the corresponding
     theorem) before checking the proofterm's inference itself.
     Proofterms that have proof IDs then cause the proof to be updated
     (at this ID) immediately after they have been checked, so that
     future uses of the same proof ID merely require a lookup in the
     proof (rather than a new derivation of the theorem).  To achieve
     a tail-recursive implementation, we use continuation-passing
     style. *)

  fun check_thm (name, thm, concl) =
    if Thm.concl thm !~ concl then
      raise ERR "check_thm" (name ^ ": conclusion is " ^ Library.term_to_string
        (Thm.concl thm) ^ ", expected: " ^ Library.term_to_string concl)
    else if !Library.trace > 2 then
      Feedback.HOL_MESG
        ("HolSmtLib: " ^ name ^ " proved: " ^ Library.thm_to_string thm)
    else ()

  fun zero_prems (state : state, proof : proof)
      (name : string)
      (z3_rule_fn : state * Term.term -> state * Thm.thm)
      (concl : Term.term)
      (continuation : (state * proof) * Thm.thm -> (state * proof) * Thm.thm)
      : (state * proof) * Thm.thm =
  let
       val (state, thm) = profile name z3_rule_fn (state, concl)
      handle Feedback.HOL_ERR holerr =>
        raise_replay_error name state name [] concl [] holerr
           | HolSatLib.SAT_cex cex =>
        raise ERR name
          ("Z3 proof replay decision procedure found a counterexample\n" ^
           "proof rule: " ^ name ^ "\n" ^
           "parsed HOL conclusion: " ^ term_diag concl ^ "\n" ^
           "replay state: " ^ state_summary state ^ "\n" ^
           "counterexample theorem: " ^ thm_diag cex)
    val _ = profile "check_thm" check_thm (name, thm, concl)
      handle Feedback.HOL_ERR holerr =>
        raise_replay_error "check_thm" state name [] concl [thm] holerr
  in
    continuation ((state, proof), thm)
  end

  fun one_arg_zero_prems (state : state, proof : proof)
      (name : string)
      (z3_rule_fn : state * 'a * Term.term -> state * Thm.thm)
      (arg : 'a, concl : Term.term)
      (continuation : (state * proof) * Thm.thm -> (state * proof) * Thm.thm)
      : (state * proof) * Thm.thm =
  let
    val (state, thm) = profile name z3_rule_fn (state, arg, concl)
      handle Feedback.HOL_ERR holerr =>
        raise_replay_error name state name [] concl [] holerr
    val _ = profile "check_thm" check_thm (name, thm, concl)
      handle Feedback.HOL_ERR holerr =>
        raise_replay_error "check_thm" state name [] concl [thm] holerr
  in
    continuation ((state, proof), thm)
  end

  fun one_prem (state_proof : state * proof)
      (name : string)
      (z3_rule_fn : state * Thm.thm * Term.term -> state * Thm.thm)
      (pt : proofterm, concl : Term.term)
      (continuation : (state * proof) * Thm.thm -> (state * proof) * Thm.thm)
      : (state * proof) * Thm.thm =
    thm_of_proofterm (state_proof, pt) (continuation o
      (fn ((state, proof), thm) =>
        let
          val (state, thm) = profile name z3_rule_fn (state, thm, concl)
            handle Feedback.HOL_ERR holerr =>
              raise_replay_error name state name [pt] concl [thm] holerr
          val _ = profile "check_thm" check_thm (name, thm, concl)
            handle Feedback.HOL_ERR holerr =>
              raise_replay_error "check_thm" state name [pt] concl [thm] holerr
        in
          ((state, proof), thm)
        end))

  and quant_intro_prem (state_proof : state * proof)
      (name : string)
      (z3_rule_fn : state * Term.term list * Thm.thm * Term.term ->
        state * Thm.thm)
      (pt : proofterm, concl : Term.term)
      (continuation : (state * proof) * Thm.thm -> (state * proof) * Thm.thm)
      : (state * proof) * Thm.thm =
    let
      val (vars, body) =
        case pt of
          PROOF_BIND ([], _) =>
            quant_intro_annotation_mismatch "annotation is empty"
        | PROOF_BIND pair => pair
        | _ => quant_intro_annotation_mismatch
            "premise is not an immediate proof-bind annotation"
    in
      thm_of_proofterm (state_proof, body) (continuation o
        (fn ((state, proof), thm) =>
          let
            val (state, thm) = profile name z3_rule_fn
              (state, vars, thm, concl)
              handle Feedback.HOL_ERR holerr =>
                raise_replay_error name state name [pt] concl [thm] holerr
            val _ = profile "check_thm" check_thm (name, thm, concl)
              handle Feedback.HOL_ERR holerr =>
                raise_replay_error "check_thm" state name [pt] concl
                  [thm] holerr
          in
            ((state, proof), thm)
          end))
    end

  and two_prems (state_proof : state * proof)
      (name : string)
      (z3_rule_fn : state * Thm.thm * Thm.thm * Term.term -> state * Thm.thm)
      (pt1 : proofterm, pt2 : proofterm, concl : Term.term)
      (continuation : (state * proof) * Thm.thm -> (state * proof) * Thm.thm)
      : (state * proof) * Thm.thm =
    thm_of_proofterm (state_proof, pt1) (continuation o
      (fn (state_proof, thm1) =>
        thm_of_proofterm (state_proof, pt2) (fn ((state, proof), thm2) =>
          let
            val (state, thm) = profile name z3_rule_fn
              (state, thm1, thm2, concl)
                handle Feedback.HOL_ERR holerr =>
                  raise_replay_error name state name [pt1, pt2] concl
                    [thm1, thm2] holerr
            val _ = profile "check_thm" check_thm (name, thm, concl)
              handle Feedback.HOL_ERR holerr =>
                raise_replay_error "check_thm" state name [pt1, pt2] concl
                  [thm1, thm2, thm] holerr
          in
            ((state, proof), thm)
          end)))

  and list_prems (state : state, proof : proof)
      (name : string)
      (z3_rule_fn : state * Thm.thm list * Term.term -> state * Thm.thm)
      ([] : proofterm list, concl : Term.term)
      (continuation : (state * proof) * Thm.thm -> (state * proof) * Thm.thm)
      (acc : Thm.thm list)
      : (state * proof) * Thm.thm =
    let
      val acc = List.rev acc
      val (state, thm) = profile name z3_rule_fn (state, acc, concl)
        handle Feedback.HOL_ERR holerr =>
          raise_replay_error name state name [] concl acc holerr
      val _ = profile "check_thm" check_thm (name, thm, concl)
        handle Feedback.HOL_ERR holerr =>
          raise_replay_error "check_thm" state name [] concl (thm :: acc) holerr
    in
      continuation ((state, proof), thm)
    end
    | list_prems (state_proof : state * proof)
      (name : string)
      (z3_rule_fn : state * Thm.thm list * Term.term -> state * Thm.thm)
      (pt :: pts : proofterm list, concl : Term.term)
      (continuation : (state * proof) * Thm.thm -> (state * proof) * Thm.thm)
      (acc : Thm.thm list)
      : (state * proof) * Thm.thm =
    thm_of_proofterm (state_proof, pt)
      (fn (state_proof, thm) =>
        list_prems state_proof name z3_rule_fn (pts, concl) continuation
          (thm :: acc))

  and list_bound_prems (state : state, proof : proof)
      (name : string)
      (z3_rule_fn : state * (Term.term list * Thm.thm) list * Term.term ->
        state * Thm.thm)
      ([] : proofterm list, concl : Term.term)
      (continuation : (state * proof) * Thm.thm -> (state * proof) * Thm.thm)
      (acc : (Term.term list * Thm.thm) list)
      : (state * proof) * Thm.thm =
    let
      val acc = List.rev acc
      val thms = List.map Lib.snd acc
      val (state, thm) = profile name z3_rule_fn (state, acc, concl)
        handle Feedback.HOL_ERR holerr =>
          raise_replay_error name state name [] concl thms holerr
      val _ = profile "check_thm" check_thm (name, thm, concl)
        handle Feedback.HOL_ERR holerr =>
          raise_replay_error "check_thm" state name [] concl
            (thm :: thms) holerr
    in
      continuation ((state, proof), thm)
    end
    | list_bound_prems (state_proof : state * proof)
      (name : string)
      (z3_rule_fn : state * (Term.term list * Thm.thm) list * Term.term ->
        state * Thm.thm)
      (pt :: pts : proofterm list, concl : Term.term)
      (continuation : (state * proof) * Thm.thm -> (state * proof) * Thm.thm)
      (acc : (Term.term list * Thm.thm) list)
      : (state * proof) * Thm.thm =
    let
      val (vars, body) =
        case pt of
          PROOF_BIND pair => pair
        | _ => ([], pt)
    in
      thm_of_proofterm (state_proof, body) (fn (state_proof, thm) =>
        list_bound_prems state_proof name z3_rule_fn (pts, concl)
          continuation ((vars, thm) :: acc))
    end

  and thm_of_proofterm (state_proof, AND_ELIM x) continuation =
        one_prem state_proof "and_elim" z3_and_elim x continuation
    | thm_of_proofterm (state_proof, APPLY_DEF x) continuation =
        one_prem state_proof "apply_def" z3_apply_def x continuation
    | thm_of_proofterm (state_proof, ASSERTED x) continuation =
        zero_prems state_proof "asserted" z3_asserted x continuation
    | thm_of_proofterm (state_proof, COMMUTATIVITY x) continuation =
        zero_prems state_proof "commutativity" z3_commutativity x continuation
    | thm_of_proofterm (state_proof, DEF_AXIOM x) continuation =
        zero_prems state_proof "def_axiom" z3_def_axiom x continuation
    | thm_of_proofterm (state_proof, ELIM_UNUSED x) continuation =
        zero_prems state_proof "elim_unused" z3_elim_unused x continuation
    | thm_of_proofterm (state_proof, HYPOTHESIS x) continuation =
        zero_prems state_proof "hypothesis" z3_hypothesis x continuation
    | thm_of_proofterm (state_proof, IFF_FALSE x) continuation =
        one_prem state_proof "iff_false" z3_iff_false x continuation
    | thm_of_proofterm (state_proof, IFF_TRUE x) continuation =
        one_prem state_proof "iff_true" z3_iff_true x continuation
    | thm_of_proofterm (state_proof, INTRO_DEF x) continuation =
        zero_prems state_proof "intro_def" z3_intro_def x continuation
    | thm_of_proofterm (state_proof, LEMMA x) continuation =
        one_prem state_proof "lemma" z3_lemma x continuation
    | thm_of_proofterm (state_proof, MONOTONICITY x) continuation =
        list_prems state_proof "monotonicity" z3_monotonicity x continuation []
    | thm_of_proofterm (state_proof, MP x) continuation =
        two_prems state_proof "mp" z3_mp x continuation
    | thm_of_proofterm (state_proof, MP_EQ x) continuation =
        two_prems state_proof "mp~" z3_mp_eq x continuation
    | thm_of_proofterm (state_proof, NNF_NEG x) continuation =
        list_bound_prems state_proof "nnf_neg" z3_nnf_neg_bound x
          continuation []
    | thm_of_proofterm (state_proof, NNF_POS x) continuation =
        list_bound_prems state_proof "nnf_pos" z3_nnf_pos_bound x
          continuation []
    | thm_of_proofterm (state_proof, NOT_OR_ELIM x) continuation =
        one_prem state_proof "not_or_elim" z3_not_or_elim x continuation
    | thm_of_proofterm (state_proof, PROOF_BIND (_, body)) continuation =
        (* proof-bind is a binder annotation rather than a logical rule.  The
           consumers that need the preserved variables (the NNF rules) destruct
           the annotation themselves; everywhere else — including an empty
           annotation — it erases to its body, which is the theorem the
           surrounding rule expects. *)
        thm_of_proofterm (state_proof, body) continuation
    | thm_of_proofterm (state_proof, QUANT_INST x) continuation =
        one_arg_zero_prems state_proof "quant_inst" z3_quant_inst x continuation
    | thm_of_proofterm (state_proof, QUANT_INTRO x) continuation =
        quant_intro_prem state_proof "quant_intro" z3_quant_intro x
          continuation
    | thm_of_proofterm (state_proof, REFL x) continuation =
        zero_prems state_proof "refl" z3_refl x continuation
    | thm_of_proofterm (state_proof, REWRITE x) continuation =
        zero_prems state_proof "rewrite" z3_rewrite_entry x continuation
    | thm_of_proofterm (state_proof, SKOLEM x) continuation =
        zero_prems state_proof "skolem" z3_skolem x continuation
    | thm_of_proofterm (state_proof, SYMM x) continuation =
        one_prem state_proof "symm" z3_symm x continuation
    | thm_of_proofterm (state_proof, TH_LEMMA_ARITH (metadata, pts, concl))
        continuation =
        list_prems state_proof (th_lemma_rule_name metadata)
          z3_th_lemma_arith (pts, concl) continuation []
    | thm_of_proofterm (state_proof, TH_LEMMA_ARRAY (metadata, pts, concl))
        continuation =
        list_prems state_proof (th_lemma_rule_name metadata)
          z3_th_lemma_array (pts, concl) continuation []
    | thm_of_proofterm (state_proof, TH_LEMMA_BASIC (metadata, pts, concl))
        continuation =
        list_prems state_proof (th_lemma_rule_name metadata)
          z3_th_lemma_basic (pts, concl) continuation []
    | thm_of_proofterm (state_proof, TH_LEMMA_BV (metadata, pts, concl))
        continuation =
        list_prems state_proof (th_lemma_rule_name metadata)
          z3_th_lemma_bv (pts, concl) continuation []
    | thm_of_proofterm (state_proof, TH_LEMMA_DATATYPE
        (metadata, pts, concl)) continuation =
        list_prems state_proof (th_lemma_rule_name metadata)
          z3_th_lemma_datatype (pts, concl) continuation []
    | thm_of_proofterm (state_proof, TH_LEMMA_SEQ (metadata, pts, concl))
        continuation =
        list_prems state_proof (th_lemma_rule_name metadata)
          (z3_th_lemma_seq metadata) (pts, concl) continuation []
    | thm_of_proofterm (state_proof, TH_LEMMA_CHAR (metadata, pts, concl))
        continuation =
        list_prems state_proof (th_lemma_rule_name metadata)
          (z3_th_lemma_char metadata) (pts, concl) continuation []
    | thm_of_proofterm (state_proof, TH_LEMMA_ADVANCED (metadata, pts, concl))
        continuation =
        list_prems state_proof (th_lemma_rule_name metadata)
          (z3_th_lemma_advanced metadata) (pts, concl) continuation []
    | thm_of_proofterm (state_proof, TRANS x) continuation =
        two_prems state_proof "trans" z3_trans x continuation
    | thm_of_proofterm (state_proof, TRANS_STAR x) continuation =
        list_prems state_proof "trans*" z3_trans_star x continuation []
    | thm_of_proofterm (state_proof, TRUE_AXIOM x) continuation =
        zero_prems state_proof "true_axiom" z3_true_axiom x continuation
    | thm_of_proofterm (state_proof, UNIT_RESOLUTION x) continuation =
        list_prems state_proof "unit_resolution" z3_unit_resolution x
          continuation []
    | thm_of_proofterm ((state, proof), ID id) continuation =
        (case Redblackmap.peek (proof_steps proof, id) of
          SOME (THEOREM thm) =>
            continuation ((state, proof), thm)
        | SOME pt =>
            let
              val rule = proofterm_rule_name pt
              val local_info =
                if SmtResource.e0_enabled () then
                  SOME (fn () => proofterm_local_structure pt)
                else NONE
              fun cache_result ((state, proof), thm) =
                let
                  val _ =
                    if !Library.trace > 2 then
                      Feedback.HOL_MESG
                        ("HolSmtLib: updating proof at ID " ^
                         Int.toString id)
                    else ()
                  val steps = Redblackmap.insert
                    (proof_steps proof, id, THEOREM thm)
                  val proof = update_proof_steps proof steps
                  val _ =
                    set_latest_proof_step id rule "end" local_info
                  val _ = replay_completed_steps :=
                    !replay_completed_steps + 1
                  val _ =
                    if (OS.Process.getEnv "HOL4_Z3_REPLAY_TRACE" =
                        SOME "1" orelse
                        OS.Process.getEnv "HOL4_Z3_REPLAY_TRACE" =
                        SOME "full") andalso
                       !replay_completed_steps mod 100 = 0 then
                      (Feedback.HOL_MESG
                        ("Z3 replay progress: completed=" ^
                         Int.toString (!replay_completed_steps) ^
                         " id=" ^ Int.toString id ^
                         " rule=" ^ rule);
                       TextIO.flushOut TextIO.stdOut)
                    else ()
                in
                  ((state, proof), thm)
                end
              fun replay () =
                (if !Library.trace > 2 then
                   Feedback.HOL_MESG
                     ("HolSmtLib: replaying proof at ID " ^ Int.toString id)
                 else ();
                 (* Nested IDs restore this ID when they return. *)
                 thm_of_proofterm ((state, proof), pt) cache_result)
              val result =
                case local_info of
                  SOME _ =>
                    track_proof_step_with_local id rule local_info replay ()
                | NONE => track_proof_step id rule replay ()
            in
              (* The ID owns only its local derivation and cache insertion.
                 Restore the previous active ID before the caller's CPS
                 continuation starts, so later work cannot be attributed to
                 an already completed child. *)
              continuation result
            end
        | NONE =>
            raise ERR "thm_of_proofterm"
              ("proof has no proofterm for ID " ^ Int.toString id))
    | thm_of_proofterm (state_proof, THEOREM thm) continuation =
        continuation (state_proof, thm)

  (* Remove the definitions `defs` from the set of hypotheses in `thm`,
     returning the resulting theorem, i.e.:

     A u defs |- t
     -------------  remove_definitions (defs, var_set)
       A |- t

     Each definition in `defs` must be an equality with a variable from
     `var_set` on either side.  That variable must not be free in `t` nor in
     `A`; its stored equality orientation is preserved.

     There is a major complication: some definitions reference variables in
     other definitions and they may even be duplicated (with and without
     expansion), e.g.:

     z1 = x + 1
     z2 = x + 1 + 2
     z2 = z1 + 2
     z3 = 3 + y

     Furthermore, another major complication is that such nested definitions
     can easily cause exponential term blow-up in case all such definitions were
     to be fully expanded (e.g. by substituting each variable with one of its
     definitions), which might occur in a naive attempt at removing these
     definitions. Therefore, a more careful implementation is warranted.

     In general, the variable references can form a directed acyclic graph. For
     efficiency purposes (explained later), we first find a variable that is not
     referenced in any definition of the other variables.

     In the above example, one such variable could be `z2` or `z3` (we'll pick
     `z2` for this example), but not `z1`, since it is referenced in one of the
     definitions of `z2`.

     We then perform the following:

     1. Gather all definitions of this variable. In this example, the
     definitions for ``z2`` would be:

     z2 = z1 + 2
     z2 = x + 1 + 2

     2. Instantiate the variable with one of its definitions (chosen
     arbitrarily). In this example, it could result in the following hypotheses:

     z1 + 2 = z1 + 2
     z1 + 2 = x + 1 + 2

     3. For each of these hypotheses, we create a theorem proving the hypothesis
     so that we can remove it with Drule.PROVE_HYP. To prove such a theorem,
     first we unify the terms on both sides of the equality, such that we obtain
     new definitions for the variables in these hypotheses. For the first one,
     no new definitions are needed, which means such a theorem can be proven
     with REFL. For the second one, we get:

     z1 = x + 1

     We can then substitute `z1` with `x + 1`, then use REFL to prove the
     theorem. This is implemented in `Library.gen_instantiation`. Note that this
     theorem will have `z1 = x + 1` in its set of hypotheses, which
     Drule.PROVE_HYP then adds to the set of hypotheses of `thm`.

     However, this new hypothesis will be removed later when we process `z1`.
     Often, these additional hypotheses are identical to pre-existing ones, so
     they get deduplicated when added to the set of hypotheses of `thm`. By
     processing variables in this specific order, we thus avoid doing a lot of
     repeated work of removing the same definitions over and over again.

     Once all the definitions of the variable we've chosen are removed, we
     recurse into this same function, with the new set of definitions that are
     to be removed (corresponding to one less variable). Note that in general,
     at no point we needed to fully expand a definition (unless it's already
     expanded).  Initial aggregate dependency summaries are computed once per
     elimination pass.  A pass with no ordinary leaf performs an optional
     second per-RHS summary pass for the SCC graph.  Recursive passes can
     therefore rescan surviving definitions, giving a quadratic number of
     summary computations in the number of definitions in the worst case. *)

  fun prove_self_word_identity
      (definition, lhs, rhs, self_dependent, _) =
    (if self_dependent andalso
        wordsSyntax.is_word_type (Term.type_of lhs) then
       SOME (profile
         "check_proof(remove_definitions:self-word-identity)"
         (fn definition =>
           if Term.is_var rhs andalso rhs ~~ lhs then
             Thm.REFL lhs
           else
             bv_resource_prove "remove-definitions-self-word-identity"
               (word_decider_attempt
                 "remove_definitions:self-word-identity"
                 (Feedback.trace ("print blast counterexamples", 0)
                   blastLib.BBLAST_PROVE)) definition) definition)
     else NONE)
    handle Feedback.HOL_ERR holerr =>
      if SmtResource.is_resource_gate holerr then
        raise Feedback.HOL_ERR holerr
      else NONE

  fun with_definition_dependency var_set definition consume =
    let
      val (lhs, rhs) = Option.valOf
        (oriented_definition_parts var_set definition)
      val (stored_left, stored_right) = boolSyntax.dest_eq definition
      val name_on_left = Term.is_var stored_left andalso
        Term.term_eq stored_left lhs
      val () =
        if name_on_left orelse
           (Term.is_var stored_right andalso Term.term_eq stored_right lhs) then
          ()
        else
          raise ERR "with_definition_dependency"
            "oriented name is absent from stored definition"
      val dependencies = Term.FVL_dag [rhs] Term.empty_tmset
      val entry = (definition, lhs, rhs,
        HOLset.member (dependencies, lhs), name_on_left)
    in
      consume (entry, dependencies)
    end

  fun align_instantiated_definition_hypothesis
      (name_on_left, inst, residue, theorem) =
    let
      (* The selected name does not occur in [residue], by the elimination
         occurs-check.  Constructing the post-INST hypothesis from these
         existing nodes therefore avoids substituting through a shared RHS. *)
      val target =
        if name_on_left then boolSyntax.mk_eq (inst, residue)
        else boolSyntax.mk_eq (residue, inst)
      val candidate = if name_on_left then theorem else Thm.SYM theorem
    in
      Thm.EQ_MP (Thm.ALPHA (Thm.concl candidate) target) candidate
    end

  fun word_list_outer_candidate (left, right) =
    if bitstringSyntax.is_v2w right then SOME (left, right, true)
    else if bitstringSyntax.is_v2w left then SOME (right, left, false)
    else NONE

  fun checked_word_list_definition
      var_set (name_on_left, left, right) =
    case word_list_outer_candidate (left, right) of
      NONE => NONE
    | SOME (word, vector, vector_on_right) =>
        SmtResource.with_resource_step_time "BitVector"
          "remove-definitions-word-list-instantiation"
          (fn () =>
            let
              val concrete = boolSyntax.mk_eq (left, right)
              val () = SmtResource.check_resource_goal "BitVector"
                "remove-definitions-word-list-instantiation" concrete
              val (list_tm, index_ty) = bitstringSyntax.dest_v2w vector
              val detailed =
                if listSyntax.is_list list_tm andalso
                   wordsSyntax.is_word_type (Term.type_of word) andalso
                   fcpSyntax.is_numeric_type index_ty andalso
                   fcpSyntax.is_numeric_type
                     (wordsSyntax.dest_word_type (Term.type_of word)) then
                  let
                    val (bits, _) = listSyntax.dest_list list_tm
                    val width = List.length bits
                    val word_width = fcpSyntax.dest_int_numeric_type
                      (wordsSyntax.dest_word_type (Term.type_of word))
                    val vector_width =
                      fcpSyntax.dest_int_numeric_type index_ty
                    val valid_bits = List.all
                      (fn bit => Term.is_var bit andalso
                        Term.type_of bit = Type.bool andalso
                        HOLset.member (var_set, bit)) bits
                    val valid_dimensions = word_width = width andalso
                      vector_width = width
                    val valid =
                      if not (valid_bits andalso valid_dimensions) then false
                      else
                        let
                          val bit_set = HOLset.addList
                            (HOLset.empty Term.var_compare, bits)
                          val word_variables =
                            Term.FVL_dag [word] Term.empty_tmset
                        in
                          HOLset.numItems bit_set = width andalso
                          List.all
                            (fn bit => not
                              (HOLset.member (word_variables, bit))) bits
                        end
                  in
                    if valid then SOME (bits, index_ty) else NONE
                  end
                else NONE
            in
              case detailed of
                NONE => NONE
              | SOME (bits, index_ty) =>
                  let
                    val width = List.length bits
                    val word_var = Term.mk_var
                      ("packed_definition_word", Term.type_of word)
                    fun bit_definition (index, bit) =
                      boolSyntax.mk_eq (bit, wordsSyntax.mk_word_bit
                        (numSyntax.term_of_int (width - index - 1),
                         word_var))
                    val definitions = List.map bit_definition
                      (ListPair.zip (List.tabulate (width, Lib.I), bits))
                    val schema_vector = bitstringSyntax.mk_v2w
                      (listSyntax.mk_list (bits, Type.bool), index_ty)
                    val conclusion = boolSyntax.mk_eq
                      (word_var, schema_vector)
                    val schema = boolSyntax.list_mk_imp
                      (definitions, conclusion)
                    val () = require_bv_family
                      "remove-definitions-word-list-instantiation" schema
                    val () = SmtResource.check_resource_goal "BitVector"
                      "remove-definitions-word-list-instantiation" schema
                    val theorem = Tactical.TAC_PROOF
                      ((definitions, conclusion),
                       Tactical.THEN
                         (bossLib.ASM_SIMP_TAC (bossLib.srw_ss()) [],
                          blastLib.BBLAST_TAC))
                    val theorem = Thm.INST [word_var |-> word] theorem
                    val theorem =
                      if vector_on_right then theorem else Thm.SYM theorem
                  in
                    SOME (align_instantiated_definition_hypothesis
                      (name_on_left, left, right, theorem))
                  end
            end) ()

  fun remove_definitions (defs, var_set, thm): Thm.thm =
  let
    (* Replay state remembers definitions established by earlier steps even
       when the final theorem no longer depends on them.  Definition
       elimination concerns theorem hypotheses, not the historical state. *)
    val defs = HOLset.intersection (defs, Thm.hypset thm)
  in
    if HOLset.isEmpty defs then
      thm
    else
      let
        (* Discharging a ground definition is an optimization, not an
           obligation: anything left behind stays an ordinary hypothesis for
           `remove_hyps` to deal with, exactly as it did before this shortcut
           existed.  A definition that does not evaluate is therefore skipped
           rather than failing the whole replay. *)
        fun prove_ground_def def =
          let
            val thm = bossLib.EVAL def
          in
            if boolSyntax.is_eq (Thm.concl thm) andalso
               Lib.snd (boolSyntax.dest_eq (Thm.concl thm)) ~~ boolSyntax.T
            then SOME (Drule.EQT_ELIM thm)
            else NONE
          end
          handle Feedback.HOL_ERR holerr =>
            if SmtResource.is_resource_gate holerr then
              raise Feedback.HOL_ERR holerr
            else NONE
        fun is_var_def def = Option.isSome
          (oriented_definition_parts var_set def)
        val (ground_defs, defs) =
          List.partition (not o is_var_def) (HOLset.listItems defs)
        fun discharge_ground_def (def, thm) =
          case prove_ground_def def of
            SOME def_thm => Drule.PROVE_HYP def_thm thm
          | NONE => thm
        val thm = HOLset.foldl discharge_ground_def
          thm (HOLset.addList (Term.empty_tmset, ground_defs))
        (* Substituting fpa2bv's per-bit definitions can turn its packed-word
           definition into the cyclic-looking but valid identity
           [w = v2w (GENLIST (flip word_bit w) ...)].  Only a definition that
           actually references its own name can have this role. *)
        (* Compute the initial aggregate RHS summary once for each definition
           in this pass.  Its self bit is retained in the compact entry; the
           full set is immediately folded into the aggregate only when that
           definition remains.  The cycle-only SCC fallback below may make one
           additional summarized pass. *)
        fun process_definition
            (definition, (remaining, theorem, referenced)) =
          with_definition_dependency var_set definition
          (fn (entry, dependencies) =>
            case prove_self_word_identity entry of
              SOME identity =>
                (remaining, Drule.PROVE_HYP identity theorem, referenced)
            | NONE =>
                (entry :: remaining, theorem,
                 HOLset.union (dependencies, referenced)))
        val (entries, thm, ref_set) = List.foldl process_definition
          ([], thm, Term.empty_tmset) defs
      in
        if List.null entries then thm
        else
      let
        (* Retain both the exact stored equality and its oriented name/residue.
           The exact orientation is needed after [INST]: reverse definitions
           become [residue = inst], whereas the generated discharge theorem is
           naturally proved as [inst = residue]. *)
        val lhs_l = List.map (fn (_, lhs, _, _, _) => lhs) entries
        (* `ref_set` contains variables referenced by remaining definitions. *)
        (* `def_set` will contain the set of all variables being defined.
           It should always be a subset of `var_set`. *)
        val def_set = List.foldl (Lib.flip HOLset.add) Term.empty_tmset lhs_l

        (* `unref_set` will contain the set of all the variables being defined
           but not being referenced *)
        val unref_set = HOLset.difference (def_set, ref_set)

        (* The initial summaries above identify ordinary DAG leaves without
           retaining one set per definition.  Only when no leaf exists, build
           temporary per-RHS summaries and an SCC graph.  A packed fpa2bv word
           may participate in the benign cycle
           [k = pack x], [k = v2w bs], [b_i = bit i k].  If no ordinary DAG
           leaf exists, select a multiply-defined packed word with no direct
           self-definition and an anchor RHS outside the candidate variable's
           own SCC.  The checked word-list family below then breaks the cycle
           into Boolean definitions. *)
        fun cycle_selection () =
          let
            fun summarize (entry as (_, _, residue, _, _)) =
              (entry, HOLset.intersection
                (Term.FVL_dag [residue] Term.empty_tmset, def_set))
            val summaries = List.map summarize entries
            val graph = HOLset.foldl
              (fn (name, graph) =>
                Definition_Graph.new_node (name, ()) graph)
              Definition_Graph.empty def_set
            fun add_dependencies
                (((_, name, _, _, _), dependencies), graph) =
              HOLset.foldl
                (fn (dependency, graph) =>
                  Definition_Graph.add_edge (name, dependency) graph)
                graph dependencies
            val graph = List.foldl add_dependencies graph summaries
            val components = Definition_Graph.strong_conn graph
            fun own_component var = Option.valOf
              (List.find (List.exists (fn member => Term.term_eq member var))
                components)
            fun classify (var, (candidates, preferred, direct_self_count)) =
              let
                val component = own_component var
                val definitions = List.filter
                  (fn ((_, lhs, _, _, _), _) => Term.term_eq lhs var)
                  summaries
                val directly_self_dependent = List.exists
                  (fn ((_, _, _, self_dependent, _), _) => self_dependent)
                  definitions
                fun outside_own_component (_, dependencies) =
                  List.all
                    (fn member => not (HOLset.member (dependencies, member)))
                    component
                val independent =
                  if directly_self_dependent orelse
                     List.length definitions <= 1 then NONE
                  else List.find outside_own_component definitions
                val (candidates, preferred) =
                  case independent of
                    SOME ((_, _, residue, _, _), _) =>
                      (HOLset.add (candidates, var),
                       (var, residue) :: preferred)
                  | NONE => (candidates, preferred)
              in
                (candidates, preferred,
                 if directly_self_dependent then direct_self_count + 1
                 else direct_self_count)
              end
          in
            HOLset.foldl classify (Term.empty_tmset, [], 0) def_set
          end
        val cycle_selection =
          if HOLset.isEmpty unref_set then
            SOME (cycle_selection ())
          else NONE
        val elimination_set =
          case cycle_selection of
            SOME (duplicate_set, _, _) => duplicate_set
          | NONE => unref_set
        val () =
          if HOLset.isEmpty elimination_set then
            let
              val direct_self_count =
                case cycle_selection of
                  SOME (_, _, count) => count
                | NONE => 0
            in
              raise ERR "remove_definitions"
                ("no unreferenced variables; definition_count=" ^
                 Int.toString (List.length entries) ^
                 "; defined_variable_count=" ^
                 Int.toString (HOLset.numItems def_set) ^
                 "; direct_self_candidate_count=" ^
                 Int.toString direct_self_count)
            end
          else
            ()

        (* Pick an arbitrary eliminable variable. *)
        val var = Option.valOf
          (HOLset.find (fn _ => true) elimination_set)

        (* Get all the variable's definitions *)
        fun filter_def (_, name, residue, _, name_on_left) =
          if Term.term_eq name var then SOME (residue, name_on_left) else NONE
        val defs_to_remove = List.mapPartial filter_def entries

        (* An ordinary leaf can use either definition.  In the exceptional
           duplicate-cycle branch, use the checked residue with no dependency
           from the candidate variable's own SCC; choosing the packed vector
           instead would turn its bit definitions into self-cycles. *)
        val inst =
          case cycle_selection of
            NONE => Lib.fst (List.hd defs_to_remove)
          | SOME (_, preferred, _) =>
              Lib.snd (Option.valOf
                (List.find (fn (name, _) => Term.term_eq name var) preferred))

        (* For an ordinary leaf, preserve the established unifier-first route.
           Only the SCC duplicate branch tries the complete packed-word family
           first, preventing a still-flexible anchor from being redefined as
           the vector and merely renaming the same cycle. *)
        fun syntax_decline _ = raise ERR "word_list_instantiation"
          "definition is not an independent packed-word family"
        fun checked_family (name_on_left, left, right) =
          case checked_word_list_definition var_set
              (name_on_left, left, right) of
            SOME theorem => theorem
          | NONE => syntax_decline ()
        fun ordinary_first (name_on_left, left, right) =
          with_expected_instantiation_fallback
            (fn input => align_instantiated_definition_hypothesis
              (name_on_left, left, right, Library.gen_instantiation input))
            (fn (left, right, _) =>
              checked_family (name_on_left, left, right))
            (left, right, var_set)
        fun ordinary_after_family (name_on_left, left, right) =
          with_expected_instantiation_fallback
            (fn input => align_instantiated_definition_hypothesis
              (name_on_left, left, right, Library.gen_instantiation input))
            syntax_decline (left, right, var_set)
        fun prove_definition (residue, name_on_left) =
          if Portable.pointer_eq (inst, residue) then
            align_instantiated_definition_hypothesis
              (name_on_left, inst, residue, Thm.REFL inst)
          else
            case cycle_selection of
              NONE => ordinary_first (name_on_left, inst, residue)
            | SOME _ =>
                (case checked_word_list_definition var_set
                    (name_on_left, inst, residue) of
                   SOME theorem => theorem
                 | NONE =>
                     ordinary_after_family (name_on_left, inst, residue))
        val hyp_thms = List.map
          prove_definition defs_to_remove

        (* Build every discharge theorem before traversing the global theorem
           with INST.  Only then remove the exact post-INST hypotheses. *)
        val thm = Thm.INST [var |-> inst] thm
        fun remove_hyp (hyp_thm, thm) = Drule.PROVE_HYP hyp_thm thm
        val thm = List.foldl remove_hyp thm hyp_thms

        (* Compute the new set of definitions to remove when recursing.
           Basically, it's all the definitions in `thm`, i.e. all hypotheses of
           the form ``var = def``, where ``var`` is in `var_set` *)
        fun is_definition hyp = Option.isSome
          (oriented_definition_parts var_set hyp)
        fun add_def (hyp, set) =
          if is_definition hyp then HOLset.add (set, hyp) else set
        val new_defs = HOLset.foldl add_def Term.empty_tmset (Thm.hypset thm)
      in
        (* Recurse to remove the remaining variables' definitions *)
        remove_definitions (new_defs, var_set, thm)
      end
      end
  end

  (* Finalization may reconcile only beta/eta spelling differences with an
     original assumption.  Semantic proof obligations belong to their proof
     nodes; accepting them here would silently rescue an incomplete replay
     rule. *)
  fun remove_hyps (asl, g, thm) : Thm.thm =
  let
    val expected = boolSyntax.mk_neg g :: asl
    val expected_set = HOLset.addList (Term.empty_tmset, expected)
    val bad_hyps = HOLset.difference (Thm.hypset thm, expected_set)
    fun changed conversion term =
      (conversion term, true) handle Conv.UNCHANGED => (Thm.REFL term, false)
    fun canonical_normalization term =
      let
        val (beta, used_beta) = changed
          (Conv.TOP_DEPTH_CONV Thm.BETA_CONV) term
        val beta_term = boolSyntax.rhs (Thm.concl beta)
        val (eta, used_eta) = changed
          (Conv.TOP_DEPTH_CONV Drule.ETA_CONV) beta_term
      in
        {theorem = Thm.TRANS beta eta,
         used_beta = used_beta,
         used_eta = used_eta}
      end
    val normalized_expected = List.map (fn assumption =>
      (assumption, canonical_normalization assumption)) expected
    fun remove_hyp (hyp, theorem) =
      let
        val hyp_result = canonical_normalization hyp
        val hyp_normalization = #theorem hyp_result
        val normalized_hyp = boolSyntax.rhs (Thm.concl hyp_normalization)
        fun lookup [] =
              raise ERR "remove_hyps"
                (unsupported_hyp_removal_diagnostic ^
                 ": stage=hyp_removal; policy=beta-eta-canonical-lookup; " ^
                 "extra hypothesis=" ^ Library.term_to_string hyp)
          | lookup ((assumption, result) :: rest) =
              let
                val normalization = #theorem result
                val matches = Term.aconv
                  (boolSyntax.rhs (Thm.concl normalization)) normalized_hyp
                fun matched () =
                  Thm.EQ_MP (Thm.SYM hyp_normalization)
                    (Thm.EQ_MP normalization (Thm.ASSUME assumption))
                val used_beta = #used_beta hyp_result orelse
                  #used_beta result
                val used_eta = #used_eta hyp_result orelse #used_eta result
              in
                if not matches then lookup rest
                else if used_eta andalso not used_beta then
                  profile "check_proof(hyp_removal:eta-only-lookup)"
                    matched ()
                else if used_beta then
                  profile "check_proof(hyp_removal:beta-lookup)" matched ()
                else
                  profile "check_proof(hyp_removal:exact-lookup)" matched ()
              end
        val hyp_theorem = profile
          "check_proof(hyp_removal:beta-eta-lookup)" lookup
          normalized_expected
      in
        Drule.PROVE_HYP hyp_theorem theorem
      end
  in
    HOLset.foldl remove_hyp thm bad_hyps
  end

  (* A reflexive equality is independently derivable by the kernel, whatever
     spelling Z3 chose for its sides. *)
  fun is_reflexive_equality hyp =
    case Lib.total boolSyntax.dest_eq hyp of
      SOME (lhs, rhs) => Term.aconv lhs rhs
    | NONE => false

  fun remove_extra_hyps (asserted, thm) =
  let
    val extra_hyps = HOLset.difference (Thm.hypset thm, asserted)
    fun remove_hyp (hyp, thm) =
      if is_reflexive_equality hyp then
        Drule.PROVE_HYP (Thm.REFL (Lib.fst (boolSyntax.dest_eq hyp))) thm
      else
        thm
  in
    HOLset.foldl remove_hyp thm extra_hyps
  end
in
  (* For unit tests *)
  val hypothesis_theorem_for_test = z3_hypothesis_theorem
  val hypothesis_theorem_with_for_test = z3_hypothesis_theorem_with
  val hypothesis_char_next_route_for_test = hypothesis_char_next_route
  val asserted_membership_diagnostic = asserted_membership_diagnostic
  val unsupported_rewrite_diagnostic = unsupported_rewrite_diagnostic
  val unsupported_hyp_removal_diagnostic =
    unsupported_hyp_removal_diagnostic
  val remove_definitions = remove_definitions
  fun prove_self_word_identity_for_test
      (definition, lhs, rhs, self_dependent) =
    prove_self_word_identity
      (definition, lhs, rhs, self_dependent, true)
  val align_instantiated_definition_hypothesis_for_test =
    align_instantiated_definition_hypothesis
  val checked_word_list_definition_for_test = checked_word_list_definition
  fun definition_dependency_summary_for_test definition =
    let
      val variables = Term.FVL_dag [definition] Term.empty_tmset
    in
    with_definition_dependency variables definition
      (fn ((_, _, _, self_dependent, _), dependencies) =>
        {self_dependent = self_dependent,
         free_variables = HOLset.numItems dependencies})
    end
  val gen_instantiation_with_expected_fallback_for_test =
    gen_instantiation_with_expected_fallback
  val with_expected_instantiation_fallback_for_test =
    with_expected_instantiation_fallback
  fun definition_unification_boundary_for_test action =
    definition_unification_boundary action
    handle DEFINITION_REWRITE_ERROR error => raise error
  fun ordinary_definition_unification_decline_for_test () =
    definition_unification_boundary
      (fn () => raise ORDINARY_DEFINITION_UNIFICATION_DECLINE)
  val remove_extra_hyps = remove_extra_hyps
  val remove_hyps_for_test = remove_hyps
  val quantified_boolean_rewrite_prove_for_test =
    quantified_boolean_rewrite_prove
  val beta_equal_for_test = beta_equal
  val eta_equal_for_test = eta_equal
  val monotonicity_prove_for_test = monotonicity_prove
  val arith_prove_for_test = arith_prove
  val arith_prove_ediv_emod_for_test = arith_prove_ediv_emod
  val definition_normalization_prove_for_test =
    definition_normalization_prove
  val asserted_equality_substitution_prove_for_test =
    asserted_equality_substitution_prove
  val ground_subterm_eval_conv_for_test =
    profiled_ground_subterm_eval_conv
  val ground_subterm_eval_max_nodes_for_test =
    ground_subterm_eval_max_nodes
  val ground_subterm_eval_max_calls_for_test =
    ground_subterm_eval_max_calls
  val word_decide_for_test = word_decide
  val admitted_def_axiom_measure_for_test = admitted_def_axiom_measure
  fun def_axiom_candidate_exception_for_test raised =
    try_def_axiom_candidates (fn (_ : unit) => raise raised) [()]
  fun def_axiom_candidate_decline_for_test () =
    try_def_axiom_candidates
      (fn first =>
        if first then def_axiom_decline
          "def_axiom_conjunction_clause" "injected ordinary decline"
        else 17) [true, false]
  val with_e0_replay_boundary = with_e0_replay_boundary
  val max_def_axiom_cache_entries_for_test = max_def_axiom_cache_entries
  val with_def_axiom_cache_boundary_for_test =
    with_def_axiom_cache_boundary_for
  fun def_axiom_cache_statistics_for_test () =
    current_def_axiom_cache_statistics ()
  fun def_axiom_cache_retained_entries_for_test () =
    case !current_def_axiom_cache of
      NONE => 0
    | SOME cache => !(#cardinality cache)
  fun replay_snapshot_state_for_test () = replay_snapshot_step ()
  fun replay_local_structure_count_for_test () =
    replay_local_structure_count ()
  fun replay_measurement_state_size_for_test () =
    case !current_replay_measurement of
      NONE => 0
    | SOME statistics =>
        Redblackmap.numItems (!(#targets (#def_axiom statistics))) +
        Redblackmap.numItems
          (!(#sampled_subnodes (#def_axiom statistics))) +
        Redblackmap.numItems
          (!(#targets (#skeleton_congruence statistics))) +
        Redblackmap.numItems
          (!(#sampled_subnodes (#skeleton_congruence statistics))) +
        Redblackmap.numItems (!(#shapes (#sat_shapes statistics))) +
        Redblackmap.numItems
          (!(#cache_entries (#sat_shapes statistics)))
  fun last_replay_measurement_for_test () =
    !last_replay_measurement_summary
  fun e0_replay_timeout_for_test duration =
    let
      fun spin n =
        spin (if n = 1000000 then 0 else n + 1)
      fun nested () = track_proof_step 271828 "fixture-inner"
        (SmtResource.profile_phase "fixture/nested-timeout" spin) 0
      fun outer () = track_proof_step 314159 "fixture-outer" nested ()
    in
      SmtResource.with_e0_invocation
        (with_fresh_e0_replay_boundary_for duration outer) ()
    end
  fun e0_replay_continuation_timeout_for_test duration =
    let
      fun spin n = spin (if n = 1000000 then 0 else n + 1)
      fun derive () =
        (set_latest_proof_step 161803 "fixture-local" "end" NONE; ())
      fun continue () = SmtResource.profile_phase
        "fixture/continuation-timeout" spin 0
      fun replay () =
        let val result =
          track_proof_step 161803 "fixture-local" derive ()
        in
          continue result
        end
    in
      SmtResource.with_e0_invocation
        (with_fresh_e0_replay_boundary_for duration replay) ()
    end
  fun e0_replay_quota_timeout_for_test duration =
    let
      val p = Term.mk_var ("p", Type.bool)
      fun deepen 0 term = term
        | deepen n term = deepen (n - 1) (boolSyntax.mk_neg term)
      val conclusion = deepen 4100 p
      val premises = REWRITE conclusion ::
        List.tabulate (69, fn index => ID (1000 + index))
      val proofterm = UNIT_RESOLUTION
        (premises, conclusion)
      val rule = proofterm_rule_name proofterm
      val repeated_left = boolSyntax.mk_disj (p, boolSyntax.mk_neg p)
      val repeated_right = boolSyntax.mk_disj (p, boolSyntax.mk_neg p)
      fun spin n = spin (if n = 1000000 then 0 else n + 1)
      fun replay () =
        (record_measured_target MeasuredDefAxiom repeated_left;
         record_measured_target MeasuredDefAxiom repeated_right;
         record_measured_target MeasuredSkeletonCongruence
           (boolSyntax.mk_eq (repeated_left, repeated_right));
         SmtResource.exhaust_e0_message_quota_for_test ();
         SmtResource.emit_e0 "fixture=ordinary-quota-exhausted";
         track_proof_step_with_local 57721 rule
           (SOME (fn () => proofterm_local_structure proofterm))
           (SmtResource.profile_phase "fixture/quota-timeout" spin) 0)
    in
      SmtResource.with_e0_invocation_for_test
        (with_fresh_e0_replay_boundary_for duration replay) ()
    end
  fun e0_replay_nested_local_timeout_for_test duration =
    let
      val p = Term.mk_var ("parent_atom", Type.bool)
      val q = Term.mk_var ("child_atom", Type.bool)
      val parent_proofterm = REWRITE (boolSyntax.mk_eq (p, p))
      val child_proofterm = REWRITE (boolSyntax.mk_eq (q, q))
      val parent_rule = proofterm_rule_name parent_proofterm
      val child_rule = proofterm_rule_name child_proofterm
      val parent_local =
        SOME (fn () => proofterm_local_structure parent_proofterm)
      val child_local =
        SOME (fn () => proofterm_local_structure child_proofterm)
      fun spin n = spin (if n = 1000000 then 0 else n + 1)
      fun child () =
        (set_latest_proof_step 8222 child_rule "end" child_local; ())
      fun parent () =
        (track_proof_step_with_local 8222 child_rule child_local child ();
         set_latest_proof_step 8111 parent_rule "end" parent_local)
      fun replay () =
        let
          val _ = track_proof_step_with_local 8111 parent_rule
            parent_local parent ()
        in
          SmtResource.profile_phase
            "fixture/nested-local-continuation-timeout" spin 0
        end
    in
      SmtResource.with_e0_invocation
        (with_fresh_e0_replay_boundary_for duration replay) ()
    end
  fun bv_family_measure_for_test target =
    term_contains_type_measure wordsSyntax.is_word_type target
  fun bv_rewrite_prove_for_test target =
    bv_rewrite_prove_with_context profile has_word_atom (fn _ => false)
      [] target
  val bv_rewrite16_for_test = rewrite16 profile
  fun bv_rewrite_prove_with_definitions_for_test definitions target =
    bv_rewrite_prove_with_context profile has_word_atom (fn _ => false)
      definitions target
  fun bv_rewrite_lowered_with_pre_bblast_for_test pre_bblast target =
    bv_rewrite_prove_with_pre_bblast profile (fn _ => false) (fn _ => true)
      pre_bblast [] target
  fun bv_rewrite_lowered_for_test version packed registered target =
    bv_rewrite_prove_with_context profile (fn _ => false)
      (has_allocated_fp_bv_atom_in version packed registered) [] target
  fun bv_rewrite_inferred_lowered_for_test version registered assertions
      target =
    let val packed = fp_inferred_packed_vars_with_provenance
      version registered assertions
    in
      bv_rewrite_lowered_for_test version packed registered target
    end
  fun bv_rewrite17_with_workers_for_test normalize decide definitions target =
    rewrite17 normalize decide definitions target
  val bv_next_rung_for_test = bv_next_rung
  val bv_th_lemma_prove_for_test = bv_th_lemma_prove
  val bv_th_lemma_basic_branch_for_test = bv_th_lemma_basic_branch
  val arith_bv_fallback_for_test = arith_bv_fallback
  val string_th_lemma_next_route_for_test = string_th_lemma_next_route

  fun skeleton_general_sequence_for_test targets =
    let
      val context = SmtSkeletonDispatch.new_context arith_prove
    in
      {procedure_names = SmtSkeletonDispatch.procedure_names context,
       results = List.map (SmtSkeletonDispatch.prove context) targets,
       cache_size = SmtSkeletonProve.cache_size context}
    end

  fun skeleton_general_admits_for_test target =
    case SmtSkeletonDispatch.attempt
        (SmtSkeletonDispatch.new_context arith_prove) target of
      SmtSkeletonDispatch.Proved _ => true
    | SmtSkeletonDispatch.Declined => false

  fun skeleton_general_word_branch_for_test word_expand fallback target =
    let
      fun unable _ = SmtSkeletonProve.Unable
      val context = SmtSkeletonProve.new_context
        [{name = "char-word", expand = unable},
         {name = "word", expand = word_expand},
         {name = "ground-regex", expand = unable},
         {name = "arithmetic", expand = unable}]
    in
      case SmtSkeletonDispatch.attempt context target of
        SmtSkeletonDispatch.Proved result => #theorem result
      | SmtSkeletonDispatch.Declined => fallback target
    end

  fun skeleton_general_arithmetic_branch_for_test arith_prove fallback
      target =
    let
      val context = SmtSkeletonDispatch.new_context arith_prove
    in
      case SmtSkeletonDispatch.attempt context target of
        SmtSkeletonDispatch.Proved result => #theorem result
      | SmtSkeletonDispatch.Declined => fallback target
    end

  fun skeleton_general_branch_for_test fallback target =
    case SmtSkeletonDispatch.attempt
        (SmtSkeletonDispatch.new_context arith_prove) target of
      SmtSkeletonDispatch.Proved result => #theorem result
    | SmtSkeletonDispatch.Declined => fallback target

  fun skeleton_duplicate_registry_for_test target =
    let
      fun unable _ = SmtSkeletonProve.Unable
      val context = SmtSkeletonProve.new_context
        [{name = "word", expand = unable},
         {name = "word", expand = unable}]
    in
      SmtSkeletonDispatch.attempt context target
    end

  fun recursive_rewrite_outer_for_test site recurse fallback input =
    ((recursive_rewrite_boundary site recurse input
      handle Feedback.HOL_ERR _ => fallback input)
     handle BV_REWRITE_ERROR error => raise error)

  fun skeleton_recursive_rewrite_for_test recurse fallback input =
    recursive_rewrite_outer_for_test
      RecursiveSkeleton recurse fallback input

  fun equality_recursive_rewrite_for_test recurse fallback input =
    recursive_rewrite_outer_for_test
      RecursiveEquality recurse fallback input

  fun abstraction_recursive_rewrite_for_test recurse fallback input =
    recursive_rewrite_outer_for_test
      RecursiveAbstraction recurse fallback input

  fun initial_replay_state allowed_asserted_hyps definitions proof : state = {
    allowed_asserted_hyps = allowed_asserted_hyps,
    asserted_hyps = Term.empty_tmset,
    definition_hyps = Term.empty_tmset,
    flexible_vars = proof_vars proof,
    thm_cache = Net.empty,
    large_thm_cache = [],
    var_set = proof_vars proof,
    bit_decompositions = proof_bit_decompositions proof,
    translation_definitions = definitions,
    skeleton_context = SmtSkeletonDispatch.new_context arith_prove,
    word_context = SmtWordGraph.new_context (),
    string_index_cache = SmtStringProve.new_contextual_index_cache (),
    z3_version = proof_version proof
  }

  (* Unit replay helpers do not have an original goal.  Derive their allowed
     set from the complete synthetic proof value so they continue to exercise
     individual rules.  Production replay never uses this helper: it supplies
     the original goal's assertions explicitly below. *)
  fun proof_asserted_hyps_with_work proof =
  let
    val work = ref 0
    (* Stable parser IDs avoid expanding a shared annotation body.  The
       visit count is linear; balanced-map bookkeeping is O(V log V). *)
    val visited_local_nodes = ref (Redblackmap.mkDict Int.compare)
    fun first_local id =
      if Option.isSome (Redblackmap.peek (!visited_local_nodes, id)) then false
      else (visited_local_nodes := Redblackmap.insert
              (!visited_local_nodes, id, ()); true)
    fun add_list pts set = List.foldl (fn (pt, set) => add pt set) set pts
    and add pt set =
      (work := !work + 1;
      case pt of
        AND_ELIM (p, _) => add p set
      | APPLY_DEF (p, _) => add p set
      | ASSERTED t => HOLset.add (set, t)
      | COMMUTATIVITY _ => set
      | DEF_AXIOM _ => set
      | ELIM_UNUSED _ => set
      | HYPOTHESIS _ => set
      | IFF_FALSE (p, _) => add p set
      | IFF_TRUE (p, _) => add p set
      | INTRO_DEF _ => set
      | LEMMA (p, _) => add p set
      | MONOTONICITY (ps, _) => add_list ps set
      | MP (p, q, _) => add q (add p set)
      | MP_EQ (p, q, _) => add q (add p set)
      | NNF_NEG (ps, _) => add_list ps set
      | NNF_POS (ps, _) => add_list ps set
      | NOT_OR_ELIM (p, _) => add p set
      | PROOF_BIND (_, p) => add p set
      | QUANT_INST _ => set
      | QUANT_INTRO (p, _) => add p set
      | REFL _ => set
      | REWRITE _ => set
      | SKOLEM _ => set
      | SYMM (p, _) => add p set
      | TH_LEMMA_ARITH (_, ps, _) => add_list ps set
      | TH_LEMMA_ARRAY (_, ps, _) => add_list ps set
      | TH_LEMMA_BASIC (_, ps, _) => add_list ps set
      | TH_LEMMA_BV (_, ps, _) => add_list ps set
      | TH_LEMMA_DATATYPE (_, ps, _) => add_list ps set
      | TH_LEMMA_SEQ (_, ps, _) => add_list ps set
      | TH_LEMMA_CHAR (_, ps, _) => add_list ps set
      | TH_LEMMA_ADVANCED (_, ps, _) => add_list ps set
      | TRANS (p, q, _) => add q (add p set)
      | TRANS_STAR (ps, _) => add_list ps set
      | TRUE_AXIOM _ => set
      | UNIT_RESOLUTION (ps, _) => add_list ps set
      | ID _ => set
      | THEOREM _ => set)
  in
    (Redblackmap.foldl (fn (_, pt, set) => add pt set)
       Term.empty_tmset (proof_steps proof), !work)
  end

  fun proof_asserted_hyps proof = Lib.fst (proof_asserted_hyps_with_work proof)

  (* Exercise the semantic advanced-family cache policy without manufacturing
     an otherwise unsupported Z3 proof node.  The same finite checked-state
     lookup must remain available when D-mode disables performance caches. *)
  fun replay_advanced_with_cached_for_test cached target =
  let
    val metadata = mk_th_lemma_metadata
      ("nonlinear-arith", SOME "lemma", ["1"])
    val state = state_cache_thm
      (initial_replay_state Term.empty_tmset []
        (empty_proof "4.12.4")) cached
    val (_, thm) = z3_th_lemma_advanced metadata (state, [], target)
  in
    thm
  end

  fun replay_root_with_definitions_for_test definitions proof : Thm.thm =
  let
    val state = initial_replay_state (proof_asserted_hyps proof)
      definitions proof
    val ((_, _), thm) = thm_of_proofterm ((state, proof), ID 0) Lib.I
  in
    thm
  end

  fun replay_root_for_test proof : Thm.thm =
    replay_root_with_definitions_for_test [] proof

  fun rewrite_with_checked_definitions_for_test
      variables definitions target =
    let
      val proof = update_proof_vars (empty_proof "4.12.4") variables
      val state = state_define
        (initial_replay_state Term.empty_tmset [] proof) definitions
      val (state, theorem) = z3_rewrite (state, target)
    in
      {theorem = theorem,
       definitions = HOLset.listItems (#definition_hyps state)}
    end

  fun flexible_rewrite_variables_for_test variables definitions =
    let
      val proof = update_proof_vars (empty_proof "4.12.4") variables
      val state = state_define
        (initial_replay_state Term.empty_tmset [] proof) definitions
    in
      #flexible_vars state
    end

  fun incremental_definition_state_for_test variables batches =
    let
      val proof = update_proof_vars (empty_proof "4.12.4") variables
      val initial = initial_replay_state Term.empty_tmset [] proof
      val state = List.foldl
        (fn (definitions, state) => state_define state definitions)
        initial batches
    in
      {flexible = #flexible_vars state,
       definitions = #definition_hyps state}
    end

  fun def_axiom_for_test target : Thm.thm =
  let
    val proof = empty_proof "4.11.2"
    val state = initial_replay_state Term.empty_tmset [] proof
  in
    Lib.snd (z3_def_axiom (state, target))
  end

  fun def_axiom_cache_sequence_for_test limit targets =
  let
    fun replay () = List.map def_axiom_for_test targets
    val theorems = with_def_axiom_cache_boundary_for limit replay ()
  in
    {theorems = theorems,
     statistics = !last_def_axiom_cache_statistics,
     retained_entries = def_axiom_cache_retained_entries_for_test ()}
  end

  fun def_axiom_cache_failure_for_test limit targets =
  let
    fun replay () =
      (List.app (ignore o def_axiom_for_test) targets;
       raise Fail "def-axiom cache fixture failure")
    val failed =
      ((with_def_axiom_cache_boundary_for limit replay (); false)
       handle Fail "def-axiom cache fixture failure" => true)
  in
    {failed = failed,
     statistics = !last_def_axiom_cache_statistics,
     retained_entries = def_axiom_cache_retained_entries_for_test ()}
  end

  fun def_axiom_cache_raise_for_test limit targets raised =
  let
    fun replay () =
      (List.app (ignore o def_axiom_for_test) targets; raise raised)
  in
    with_def_axiom_cache_boundary_for limit replay ()
  end

  fun def_axiom_cache_gate_for_test limit target =
  let
    fun replay () = ignore (def_axiom_for_test target)
    val gated =
      ((with_def_axiom_cache_boundary_for limit replay (); false)
       handle Feedback.HOL_ERR holerr =>
         if SmtResource.is_resource_gate holerr then true
         else raise Feedback.HOL_ERR holerr)
  in
    {gated = gated,
     statistics = !last_def_axiom_cache_statistics,
     retained_entries = def_axiom_cache_retained_entries_for_test ()}
  end

  fun def_axiom_cache_nested_for_test limit outer_target inner_target =
  let
    fun inner () = ignore (def_axiom_for_test inner_target)
    fun outer () =
      (ignore (def_axiom_for_test outer_target);
       with_def_axiom_cache_boundary_for limit inner ();
       ignore (def_axiom_for_test outer_target))
    val _ = with_def_axiom_cache_boundary_for limit outer ()
  in
    {statistics = !last_def_axiom_cache_statistics,
     retained_entries = def_axiom_cache_retained_entries_for_test ()}
  end

  fun def_axiom_cache_probe_failure_for_test target =
  let
    fun replay () =
      let
        val first = def_axiom_for_test target
        val cache = valOf (!current_def_axiom_cache)
        val bad = {target = target, theorem = Thm.ASSUME target}
        val _ = #entries cache := Redblackmap.insert
          (!(#entries cache), target, bad)
        val second = def_axiom_for_test target
      in
        (first, second)
      end
    val theorems = with_def_axiom_cache_boundary_for 8 replay ()
  in
    {theorems = theorems,
     statistics = !last_def_axiom_cache_statistics,
     retained_entries = def_axiom_cache_retained_entries_for_test ()}
  end

  fun e0_measurement_targets_for_test
      {def_axiom_targets, congruence_targets, force_invocation_truncation,
       fail} =
  let
    fun replay () =
      (if force_invocation_truncation then
         (case !current_replay_measurement of
            NONE => ()
          | SOME statistics =>
              #total_sampled_observations statistics :=
                max_sampled_observations)
       else ();
       List.app (record_measured_target MeasuredDefAxiom)
         def_axiom_targets;
       List.app (record_measured_target MeasuredSkeletonCongruence)
         congruence_targets;
       if fail then raise Fail "measurement fixture failure" else ())
    val failed =
      ((SmtResource.with_e0_invocation_for_test
          (with_fresh_e0_replay_boundary_for (Time.fromSeconds 5) replay) ();
        false)
       handle Fail "measurement fixture failure" => true)
  in
    {failed = failed,
     summary = !last_replay_measurement_summary,
     retained_terms = replay_measurement_state_size_for_test ()}
  end

  fun e0_measurement_sample_failure_for_test target =
  let
    fun hook site =
      if site = "measurement-sample" then
        raise Fail "injected sample failure"
      else ()
  in
    SmtResource.with_e0_diagnostic_hook_for_test hook
      (fn () => e0_measurement_targets_for_test
        {def_axiom_targets = [target], congruence_targets = [],
         force_invocation_truncation = false, fail = false}) ()
  end

  fun e0_measurement_preserves_result_for_test target =
  let
    fun replay () =
      (record_measured_target MeasuredSkeletonCongruence target; target)
    val result = SmtResource.with_e0_invocation_for_test
      (with_fresh_e0_replay_boundary_for (Time.fromSeconds 5) replay) ()
  in
    {result = result, summary = !last_replay_measurement_summary,
     retained_terms = replay_measurement_state_size_for_test ()}
  end

  fun capture_diagnostic_precedence_for_test original =
    SmtResource.resolve_diagnostic_exception original
      (fn () => SmtResource.invoke_e0_diagnostic_hook
        "capture-skeleton-obligation") (fn primary => raise primary)

  fun e0_def_axiom_measurement_for_test targets =
  let
    fun replay () = List.app (fn target =>
      ignore (def_axiom_for_test target)) targets
    val _ = SmtResource.with_e0_invocation_for_test
      (with_fresh_e0_replay_boundary_for (Time.fromSeconds 30) replay) ()
  in
    {summary = !last_replay_measurement_summary,
     retained_terms = replay_measurement_state_size_for_test ()}
  end

  fun e0_direct_skeleton_measurement_for_test targets =
  let
    val context = SmtSkeletonProve.new_context []
    val owners = Redblackmap.mkDict Term.compare
    fun replay () = List.app (fn target =>
      ignore (SmtSkeletonProve.prove_with_owners context owners
        (SmtResource.term_measure target) target)) targets
    val _ = SmtResource.with_e0_invocation_for_test
      (with_fresh_e0_replay_boundary_for (Time.fromSeconds 30) replay) ()
  in
    {summary = !last_replay_measurement_summary,
     retained_terms = replay_measurement_state_size_for_test ()}
  end

  fun e0_disabled_sat_observer_for_test target =
  let
    val target_calls = ref 0
    val completion_calls = ref 0
    val context = SmtSkeletonProve.new_context []
    val owners = Redblackmap.mkDict Term.compare
    fun replay () = #theorem (SmtSkeletonProve.prove_with_owners
      context owners (SmtResource.term_measure target) target)
    val theorem = SmtSkeletonProve.with_sat_observers
      (SOME (fn _ => target_calls := !target_calls + 1))
      (SOME (fn _ => completion_calls := !completion_calls + 1))
      (with_fresh_e0_replay_boundary_for (Time.fromSeconds 30) replay) ()
  in
    {observer_calls = !target_calls,
     completion_observer_calls = !completion_calls, theorem = theorem,
     summary = !last_replay_measurement_summary,
     retained_terms = replay_measurement_state_size_for_test ()}
  end

  fun e0_measurement_exception_for_test raised target =
  let
    fun replay () =
      (record_measured_target MeasuredDefAxiom target; raise raised)
    val propagated =
      ((SmtResource.with_e0_invocation_for_test
          (with_fresh_e0_replay_boundary_for (Time.fromSeconds 5) replay) ();
        false)
       handle exn => General.exnName exn = General.exnName raised)
  in
    {propagated = propagated,
     summary = !last_replay_measurement_summary,
     retained_terms = replay_measurement_state_size_for_test ()}
  end

  fun e0_nested_measurement_for_test (outer_target, inner_target) =
  let
    fun inner () = record_measured_target MeasuredDefAxiom inner_target
    fun outer () =
      (record_measured_target MeasuredDefAxiom outer_target;
       with_fresh_e0_replay_boundary_for (Time.fromSeconds 5) inner ();
       record_measured_target MeasuredDefAxiom outer_target)
    val _ = SmtResource.with_e0_invocation_for_test
      (with_fresh_e0_replay_boundary_for (Time.fromSeconds 5) outer) ()
  in
    {summary = !last_replay_measurement_summary,
     retained_terms = replay_measurement_state_size_for_test ()}
  end

  fun e0_partial_node_cache_metrics_for_test fail =
  let
    fun replay () =
      (List.app observe_skeleton_node_cache
         [SmtSkeletonProve.NodeCachePointerHit,
          SmtSkeletonProve.NodeCacheStructuralReanchorAttempt,
          SmtSkeletonProve.NodeCacheStructuralReanchorFallback,
          SmtSkeletonProve.NodeCacheReanchorTime
            (Time.fromMilliseconds 7)];
       if fail then raise Fail "partial cache fixture" else ())
    val failed =
      ((SmtResource.with_e0_invocation_for_test
          (with_fresh_e0_replay_boundary_for (Time.fromSeconds 5) replay) ();
        false)
       handle Fail "partial cache fixture" => true)
  in
    {failed = failed,
     summary = !last_replay_measurement_summary,
     retained_terms = replay_measurement_state_size_for_test ()}
  end

  fun sat_shape_opportunity_for_test cache_limit targets =
  let
    val measurement = new_sat_shape_measurement cache_limit
    fun record target =
      let val result = record_sat_shape_target measurement target
          val _ = record_sat_shape_completion measurement Time.zeroTime
      in result end
    val results = List.map record targets
  in
    {all_recorded = List.all Lib.I results,
     summary = sat_shape_measurement_text measurement,
     retained_shapes = Redblackmap.numItems (!(#shapes measurement)) +
       Redblackmap.numItems (!(#cache_entries measurement))}
  end

  fun sat_shape_timing_for_test cache_limit observations =
  let
    val measurement = new_sat_shape_measurement cache_limit
    fun record (target, elapsed) =
      (ignore (record_sat_shape_target measurement target);
       ignore (record_sat_shape_completion measurement elapsed))
    val _ = List.app record observations
  in
    {summary = sat_shape_measurement_text measurement,
     completed_calls = !(#completed_calls measurement),
     completed_wall = !(#completed_wall measurement),
     cache_hit_completed_calls =
       !(#cache_hit_completed_calls measurement),
     cache_hit_sat_wall = !(#cache_hit_sat_wall measurement),
     cache_hit_sat_max_wall = !(#cache_hit_sat_max_wall measurement)}
  end

  fun sat_shape_pairing_for_test (repeated_target, nested_target) =
  let
    val interrupted = new_sat_shape_measurement 8
    val _ = record_sat_shape_target interrupted repeated_target
    val _ = record_sat_shape_target interrupted repeated_target
    val _ = record_sat_shape_completion interrupted
      (Time.fromMilliseconds 5)
    val _ = record_sat_shape_target interrupted repeated_target
    val _ = record_sat_shape_completion interrupted
      (Time.fromMilliseconds 7)
    val nested = new_sat_shape_measurement 8
    val _ = record_sat_shape_target nested repeated_target
    val _ = record_sat_shape_completion nested Time.zeroTime
    val _ = record_sat_shape_target nested repeated_target
    val _ = record_sat_shape_target nested nested_target
    val _ = record_sat_shape_completion nested (Time.fromMilliseconds 3)
    val _ = record_sat_shape_completion nested (Time.fromMilliseconds 11)
  in
    {interrupted_summary = sat_shape_measurement_text interrupted,
     interrupted_hits = !(#cache_hits interrupted),
     interrupted_hit_completed_calls =
       !(#cache_hit_completed_calls interrupted),
     interrupted_hit_wall = !(#cache_hit_sat_wall interrupted),
     nested_summary = sat_shape_measurement_text nested,
     nested_hits = !(#cache_hits nested),
     nested_inserts = !(#cache_inserts nested),
     nested_hit_completed_calls = !(#cache_hit_completed_calls nested),
     nested_hit_wall = !(#cache_hit_sat_wall nested)}
  end

  fun e0_disabled_measurement_for_test target =
  let
    val _ = current_replay_measurement := NONE
    val _ = last_replay_measurement_summary := "measurement_enabled=false"
    val _ = record_measured_target MeasuredDefAxiom target
  in
    {summary = !last_replay_measurement_summary,
     retained_terms = replay_measurement_state_size_for_test ()}
  end

  fun replay_root_with_state_for_test proof =
  let
    val state = initial_replay_state (proof_asserted_hyps proof) [] proof
    val ((state, _), thm) = thm_of_proofterm ((state, proof), ID 0) Lib.I
  in
    {asserted_hyps = HOLset.listItems (#asserted_hyps state),
     definition_hyps = HOLset.listItems (#definition_hyps state),
     thm = thm}
  end

  (* returns a theorem that concludes ``F``, with its hypotheses (a
     subset of) those asserted in the proof *)
  fun check_proof_impl definitions (asl, g, proof) : Thm.thm =
  let
    val _ = replay_completed_steps := 0
    val _ = if !Library.trace > 1 then
        Feedback.HOL_MESG "HolSmtLib: checking Z3 proof"
      else ()

    (* initial state *)
    val allowed_asserted_hyps = HOLset.addList
      (Term.empty_tmset, boolSyntax.mk_neg g :: asl)
    val state = initial_replay_state allowed_asserted_hyps definitions proof

    (* ID 0 denotes the proof's root node *)
    val ((state, _), thm) = thm_of_proofterm ((state, proof), ID 0) Lib.I

    val _ = Feq (Thm.concl thm) orelse
      raise ERR "check_proof" "final conclusion is not 'F'"

    (* remove the definitions introduced by Z3 from the set of hypotheses *)
    val final_thm = profile "check_proof(remove_definitions)" remove_definitions
      (#definition_hyps state, #var_set state, thm)
      handle Feedback.HOL_ERR holerr =>
        raise_final_error "remove_definitions" state thm holerr

    (* workaround for Z3 bug *)
    val final_thm = profile "check_proof(remove_extra_hyps)" remove_extra_hyps
      (#asserted_hyps state, final_thm)
      handle Feedback.HOL_ERR holerr =>
        raise_final_error "remove_extra_hyps" state final_thm holerr

    (* if the final theorem contains hyps that are not in `asl`, it likely means
       that we've run into a Z3 issue where it slightly modifies the original
       assumptions; as a workaround we try to remove those hyps here *)
    val final_thm = profile "check_proof(hyp_removal)" remove_hyps
      (asl, g, final_thm)
      handle Feedback.HOL_ERR holerr =>
        raise_final_error "hyp_removal" state final_thm holerr

    (* check that the final theorem contains no hyps other than those that have
       been asserted or those used by the hypothesis-removal workaround above *)
    val allowed_hyps = HOLset.union (#asserted_hyps state,
      HOLset.addList (Term.empty_tmset, boolSyntax.mk_neg g :: asl))
    val _ = profile "check_proof(hypcheck)" HOLset.isSubset
      (Thm.hypset final_thm, allowed_hyps) orelse
      raise ERR "check_proof" "final theorem contains additional hyp(s)"
      handle Feedback.HOL_ERR holerr =>
        raise_final_error "hypcheck" state final_thm holerr
  in
    final_thm
  end


  fun check_proof_with_definitions definitions args : Thm.thm =
    with_def_axiom_cache_boundary
      (SmtResource.with_e0_invocation
        (with_e0_replay_boundary
          (profile "check_proof(total)" (check_proof_impl definitions)))) args

  fun check_proof args : Thm.thm = check_proof_with_definitions [] args

end  (* local *)

end
