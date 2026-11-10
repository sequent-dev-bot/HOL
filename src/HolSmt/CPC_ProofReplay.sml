(* Checked replay for cvc5's native CPC proof calculus. *)

structure CPC_ProofReplay =
struct

local
  open CPC_Proof

  val ERR = Feedback.mk_HOL_ERR "CPC_ProofReplay"

  val reglan_ty =
    Type.mk_thy_type {Thy = "smtstring", Tyop = "reglan", Args = []}

  val rare_seq_contains_refl = Library.prove
    (``!(x:'a list). IS_SUBLIST x x``,
     Tactical.THEN
       (bossLib.RW_TAC (bossLib.srw_ss())
          [rich_listTheory.IS_SUBLIST_APPEND],
        Tactical.THEN
          (Tactic.EXISTS_TAC ``[]:'a list``,
           Tactical.THEN
             (Tactic.EXISTS_TAC ``[]:'a list``,
              bossLib.RW_TAC (bossLib.srw_ss()) []))))

  fun profile name f x =
    Profile.profile_with_exn_name name f x

  fun profile_event name = Profile.profile name (fn () => ()) ()

  (* Opt-in diagnostics.  Timers include exceptional exits and never select
     a proof route.  The command loop can enable them for a step interval. *)
  val resolution_profile_enabled = ref false
  val _ = Feedback.register_btrace
    ("CPC_resolution_profile", resolution_profile_enabled)
  val resolution_profile_counts = ref ([] : (string * int) list)
  fun resolution_profile name action input =
    if !resolution_profile_enabled then
      profile ("CPC(resolution-detail:" ^ name ^ ")") action input
    else action input
  fun resolution_count name amount =
    if not (!resolution_profile_enabled) then ()
    else
      let
        fun add [] = [(name, amount)]
          | add ((key, value) :: rest) =
              if key = name then (key, value + amount) :: rest
              else (key, value) :: add rest
      in resolution_profile_counts := add (!resolution_profile_counts) end


  val max_exact_provenance_dag_nodes = 256

  fun provenance_term_summary limit root =
    let
      val bucket_count = 4093
      val seen = Array.array (bucket_count, [] : Term.term list)
      fun string_hash string =
        let
          fun loop index hash =
            if index = String.size string then hash
            else loop (index + 1)
              ((hash * 33 + Char.ord (String.sub (string, index))) mod
               bucket_count)
        in loop 0 5381 end
      fun hash depth term =
        if Term.is_var term then
          (string_hash (Lib.fst (Term.dest_var term)) + 11) mod bucket_count
        else if Term.is_const term then
          (string_hash (#Name (Term.dest_thy_const term)) + 17) mod
          bucket_count
        else if depth = 0 then
          if Term.is_abs term then 23 else 29
        else if Term.is_abs term then
          let val (variable, body) = Term.dest_abs term in
            (31 * hash (depth - 1) variable + hash (depth - 1) body + 37)
            mod bucket_count
          end
        else
          let val (operator, operand) = Term.dest_comb term in
            (31 * hash (depth - 1) operator +
             hash (depth - 1) operand + 41) mod bucket_count
          end
      fun seen_term term =
        let
          val index = hash 2 term
          val bucket = Array.sub (seen, index)
        in
          if List.exists (fn saved => Portable.pointer_eq (term, saved))
               bucket then true
          else (Array.update (seen, index, term :: bucket); false)
        end
      fun visit [] count = (false, count, true)
        | visit (term :: pending) count =
            if Term.is_abs term then (true, count, true)
            else if seen_term term then visit pending count
            else if count >= limit then (false, count, false)
            else visit
              (List.revAppend (SmtResource.term_children term, pending))
              (count + 1)
    in visit [root] 0 end

  fun provenance_term_has_abs root =
    #1 (provenance_term_summary (Option.valOf Int.maxInt) root)

  fun use_compact_provenance term =
    let
      val (has_abs, _, complete) = provenance_term_summary
        max_exact_provenance_dag_nodes term
    in has_abs orelse complete end

  fun provenance_shape AtomicProvenance = "atom"
    | provenance_shape (ApplicationProvenance (head, operands)) =
        "application(" ^ head ^ "," ^
        String.concatWith "," (List.map provenance_shape operands) ^ ")"
    | provenance_shape (BinderProvenance (head, body)) =
        "binder(" ^ head ^ "," ^ provenance_shape body ^ ")"
    | provenance_shape (BinderBlockProvenance (head, size, body)) =
        "binder-block(" ^ head ^ "," ^ Int.toString size ^ "," ^
        provenance_shape body ^ ")"
    | provenance_shape (EqualityProvenance (left, right)) =
        "equality(" ^ provenance_shape left ^ "," ^
        provenance_shape right ^ ")"
    | provenance_shape (ConjunctionProvenance (_, operands)) =
        "conjunction(" ^
        String.concatWith "," (List.map provenance_shape operands) ^ ")"
    | provenance_shape (UnavailableProvenance reason) =
        "unavailable(" ^ reason ^ ")"
    | provenance_shape (AmbiguousProvenance reason) =
        "ambiguous(" ^ reason ^ ")"

  (* Exact provenance that proves an occurrence contains no conjunction can
     be represented by the atomic no-conjunction marker once it enters the
     live step table.  Parsed command occurrences remain fully structured,
     so a later CONG still has the exact source tree it must rewrite.  An
     unavailable or ambiguous occurrence is deliberately not compacted: it
     may contain a conjunction and must continue to fail closed. *)
  fun definitely_no_conjunction AtomicProvenance = true
    | definitely_no_conjunction (ApplicationProvenance (_, operands)) =
        List.all definitely_no_conjunction operands
    | definitely_no_conjunction (BinderProvenance (_, body)) =
        definitely_no_conjunction body
    | definitely_no_conjunction (BinderBlockProvenance (_, _, body)) =
        definitely_no_conjunction body
    | definitely_no_conjunction (EqualityProvenance (left, right)) =
        definitely_no_conjunction left andalso
        definitely_no_conjunction right
    | definitely_no_conjunction (ConjunctionProvenance _) = false
    | definitely_no_conjunction (UnavailableProvenance _) = false
    | definitely_no_conjunction (AmbiguousProvenance _) = false

  fun contains_binder_block provenance =
    case provenance of
      BinderBlockProvenance _ => true
    | ApplicationProvenance (_, operands) =>
        List.exists contains_binder_block operands
    | BinderProvenance (_, body) => contains_binder_block body
    | EqualityProvenance (left, right) =>
        contains_binder_block left orelse contains_binder_block right
    | ConjunctionProvenance (_, operands) =>
        List.exists contains_binder_block operands
    | _ => false

  fun contains_binder_block_dag root =
    let
      val bucket_count = 4093
      val seen = Array.array
        (bucket_count, [] : term_provenance list)
      fun string_hash string =
        let
          fun loop index hash =
            if index = String.size string then hash
            else loop (index + 1)
              ((hash * 33 + Char.ord (String.sub (string, index))) mod
               bucket_count)
        in loop 0 5381 end
      fun index item =
        case item of
          AtomicProvenance => 0
        | ApplicationProvenance (head, operands) =>
            (17 * string_hash head + List.length operands) mod bucket_count
        | BinderProvenance (head, _) =>
            (31 * string_hash head + 1) mod bucket_count
        | BinderBlockProvenance (head, size, _) =>
            (37 * string_hash head + size) mod bucket_count
        | EqualityProvenance _ => 41
        | ConjunctionProvenance (_, operands) =>
            (43 + List.length operands) mod bucket_count
        | UnavailableProvenance reason =>
            (47 * string_hash reason) mod bucket_count
        | AmbiguousProvenance reason =>
            (53 * string_hash reason) mod bucket_count
      fun known item =
        let
          val bucket = index item
          val entries = Array.sub (seen, bucket)
        in
          if List.exists
               (fn saved => Portable.pointer_eq (item, saved)) entries then true
          else
            (Array.update (seen, bucket, item :: entries); false)
        end
      fun visit item =
        if known item then false
        else
          case item of
            BinderBlockProvenance _ => true
          | ApplicationProvenance (_, operands) => List.exists visit operands
          | BinderProvenance (_, body) => visit body
          | EqualityProvenance (left, right) =>
              visit left orelse visit right
          | ConjunctionProvenance (_, operands) => List.exists visit operands
          | _ => false
    in visit root end

  fun has_binder_shell provenance =
    case provenance of
      BinderBlockProvenance _ => true
    | BinderProvenance _ => true
    | ApplicationProvenance ("not", [operand]) =>
        has_binder_shell operand
    | _ => false

  (* Live metadata retains equality endpoints and source binder blocks because
     semantic rules consume those exact boundaries even when no conjunction
     occurs below them.  Other conjunction-irrelevant application and binder
     shells can still be collapsed to keep large arithmetic proofs bounded. *)
  fun compact_live_provenance provenance =
    let
      type summary = term_provenance * bool * bool
      val buckets = Array.array
        (4093, [] : (term_provenance * summary) list)
      fun string_hash string =
        let
          fun loop index hash =
            if index = String.size string then hash
            else loop (index + 1)
              ((hash * 33 + Char.ord (String.sub (string, index))) mod 4093)
        in loop 0 5381 end
      fun tag item =
        case item of
          AtomicProvenance => 0
        | ApplicationProvenance (head, operands) =>
            (17 * string_hash head + List.length operands) mod 4093
        | BinderProvenance (head, _) =>
            (31 * string_hash head + 1) mod 4093
        | BinderBlockProvenance (head, size, _) =>
            (37 * string_hash head + size) mod 4093
        | EqualityProvenance _ => 41
        | ConjunctionProvenance (_, operands) =>
            (43 + List.length operands) mod 4093
        | UnavailableProvenance reason =>
            (47 * string_hash reason) mod 4093
        | AmbiguousProvenance reason =>
            (53 * string_hash reason) mod 4093
      fun lookup [] _ = NONE
        | lookup ((saved, result) :: rest) item =
            if Portable.pointer_eq (saved, item) then SOME result
            else lookup rest item
      fun summarize item =
        let
          val bucket = tag item
        in
          case lookup (Array.sub (buckets, bucket)) item of
            SOME result => result
          | NONE =>
              let
                val result =
                  case item of
                    AtomicProvenance => (AtomicProvenance, true, false)
                  | UnavailableProvenance _ => (item, false, false)
                  | AmbiguousProvenance _ => (item, false, false)
                  | EqualityProvenance (left, right) =>
                      let
                        val (left', left_clear, left_block) = summarize left
                        val (right', right_clear, right_block) =
                          summarize right
                      in
                        (EqualityProvenance (left', right'),
                         left_clear andalso right_clear,
                         left_block orelse right_block)
                      end
                  | ConjunctionProvenance (source, operands) =>
                      let
                        val summaries = List.map summarize operands
                      in
                        (ConjunctionProvenance
                           (source, List.map #1 summaries), false,
                         List.exists #3 summaries)
                      end
                  | ApplicationProvenance (head, operands) =>
                      let
                        val summaries = List.map summarize operands
                        val clear = List.all #2 summaries
                        val block = List.exists #3 summaries
                        val compact = if clear andalso not block then
                            AtomicProvenance
                          else ApplicationProvenance
                            (head, List.map #1 summaries)
                      in (compact, clear, block) end
                  | BinderProvenance (head, body) =>
                      let
                        val (body', clear, block) = summarize body
                        val compact = if clear andalso not block then
                            AtomicProvenance
                          else BinderProvenance (head, body')
                      in (compact, clear, block) end
                  | BinderBlockProvenance (head, size, body) =>
                      let
                        val (body', clear, _) = summarize body
                      in
                        (BinderBlockProvenance (head, size, body'),
                         clear, true)
                      end
                val _ = Array.update (buckets, bucket,
                  (item, result) :: Array.sub (buckets, bucket))
              in result end
        end
    in #1 (summarize provenance) end

  fun term_contains_conjunction term =
    not (List.null (HolKernel.find_terms boolSyntax.is_conj term))

  (* CPC's n-ary [and] elaborates to [list_mk_conj], hence to this
     right-associated HOL shape.  Unlike source-occurrence provenance, these
     operand boundaries are present in the checked theorem itself. *)
  fun right_associated_conjuncts term =
    let val (left, right) = boolSyntax.dest_conj term in
      left ::
      (case Lib.total boolSyntax.dest_conj right of
         SOME _ => right_associated_conjuncts right
       | NONE => [right])
    end

  (* A proof step can legitimately omit its raw source occurrence after the
     theorem has been kernel-checked.  The only topology that a later
     conclusion-less CPC rule needs to recover is an AND operand boundary;
     its right-associated HOL encoding is checked directly above.  Keep every
     other shell unavailable.  In particular, do not rebuild equality or
     application trees from a large checked theorem: source-occurrence facts
     are not recoverable from them, and retaining them defeats live-proof
     compaction. *)
  fun recovered_checked_provenance reason term =
    let
      fun recover term =
        case Lib.total boolSyntax.dest_conj term of
          SOME _ =>
            ConjunctionProvenance
              (ParsedConjunction,
               List.map recover (right_associated_conjuncts term))
        | NONE => UnavailableProvenance
            ("checked result has no recoverable AND boundary: " ^ reason)
    in recover term end

  (* A successful kernel theorem proves when no conjunction occurrence is
     present at all.  In that case Atomic is exact, while equality boundaries
     remain visible in HOL and can be retained recursively.  Any theorem that
     does contain a conjunction needs occurrence-specific parsed/semantic
     provenance; never guess its erased n-ary grouping here. *)
  fun conjunction_free_semantic_provenance reason term =
    if term_contains_conjunction term then UnavailableProvenance reason
    else
      case Lib.total boolSyntax.dest_eq term of
        SOME (left, right) => EqualityProvenance
          (conjunction_free_semantic_provenance reason left,
           conjunction_free_semantic_provenance reason right)
      | NONE => AtomicProvenance

  (* E1(c): repeated-conclusion theorem reuse is a redundant performance
     cache.  It is opt-in because Net matching is structural and can dominate
     replay of a large, already explicit CPC proof DAG.  Actual insert/probe
     work also passes through the one shared fast-path resource boundary
     below. *)
  val theorem_cache_enabled =
    OS.Process.getEnv "HOL4_CPC_THEOREM_CACHE" = SOME "1" andalso
    not (Library.no_fastpath ())

  (* The theorem cache is a replay acceleration only: CPC's explicit premise
     graph is the authoritative liveness relation.  Retain just small,
     hypothesis-free results, whose contexts cannot capture a large scope,
     and periodically replace the cache as a whole.  This keeps memoization
     bounded independently of certificate size without changing which kernel
     theorem a rule is required to reconstruct. *)
  val max_cached_theorem_dag_nodes = 256

  val max_cached_theorem_entries = 1024

  fun cacheable_theorem theorem =
    HOLset.isEmpty (Thm.hypset theorem) andalso
    SmtResource.dag_nodes_up_to
      (max_cached_theorem_dag_nodes + 1) (Thm.concl theorem) <=
    max_cached_theorem_dag_nodes

  fun theorem_cache_fastpath target prove input =
    Library.require_fastpath "CPC theorem cache" target prove input

  fun optional_fastpath fastpath target worker input =
    SOME (fastpath target worker input)
    handle Feedback.HOL_ERR holerr =>
      if Library.is_fastpath_refusal holerr then NONE
      else raise Feedback.HOL_ERR holerr

  type cache_stats = {
    hits : int ref,
    misses : int ref,
    context_rejections : int ref,
    omitted_bypasses : int ref,
    cardinality : int ref,
    peak_cardinality : int ref,
    step_cardinality : int ref
  }

  fun new_cache_stats () : cache_stats = {
    hits = ref 0,
    misses = ref 0,
    context_rejections = ref 0,
    omitted_bypasses = ref 0,
    cardinality = ref 0,
    peak_cardinality = ref 0,
    step_cardinality = ref 0
  }

  type cached_theorem = {
    thm : Thm.thm
  }

  datatype cache_probe_outcome =
      CacheProbeHit of {
        theorem : Thm.thm,
        context_rejections : int,
        hypfree : bool
      }
    | CacheProbeMiss of {
        context_rejections : int
      }

  type replay_result = {
    thm : Thm.thm,
    located : located_term,
    clause : SmtClause.clause option
  }

  type replayed_step = {
    rule_name : string,
    result : replay_result
  }

  fun result_theorem ({thm, ...} : replay_result) = thm

  fun result_located ({located, ...} : replay_result) = located

  fun result_provenance result = #provenance (result_located result)

  fun step_theorem ({result, ...} : replayed_step) = result_theorem result

  fun step_located ({result, ...} : replayed_step) = result_located result

  fun step_provenance step = #provenance (step_located step)

  fun clause_from_located theorem (located : located_term) =
    if not (Term.aconv (Thm.concl theorem) (#term located)) then NONE
    else Option.map (fn literals => SmtClause.from_literals literals theorem)
      (source_clause_literals located)

  fun clause_result reason clause : replay_result =
    let val theorem = SmtClause.theorem clause in
      {thm = theorem,
       located = {term = Thm.concl theorem,
         provenance = UnavailableProvenance reason},
       clause = SOME clause}
    end

  fun exact_result provenance theorem : replay_result =
    let
      val term = Thm.concl theorem
      val clause = clause_from_located theorem
        {term = term, provenance = provenance}
      val provenance =
        case provenance of
          UnavailableProvenance reason =>
            recovered_checked_provenance reason term
        | AmbiguousProvenance reason =>
            if SmtResource.dag_nodes_up_to
                 (max_exact_provenance_dag_nodes + 1) term >
               max_exact_provenance_dag_nodes orelse
               term_contains_conjunction term then
              AmbiguousProvenance reason
            else conjunction_free_semantic_provenance reason term
        | exact =>
            if not (use_compact_provenance term) andalso
               not (contains_binder_block_dag exact) then
              UnavailableProvenance
                "exact provenance exceeds the compact metadata budget"
            else exact
    in
      {thm = theorem, located = {term = term, provenance = provenance},
       clause = clause}
    end

  fun unavailable_result reason theorem =
    exact_result (UnavailableProvenance reason) theorem

  (* Use when a rule intentionally declines semantic occurrence recovery.
     Unlike [unavailable_result], this does not scan a potentially shared DAG
     merely to discover that its result contains no conjunction. *)
  fun raw_unavailable_result reason theorem = {
    thm = theorem,
    located = {term = Thm.concl theorem,
      provenance = UnavailableProvenance reason},
    clause = NONE
  }

  fun located_result where_ theorem (located : located_term) =
    if Term.aconv (Thm.concl theorem) (#term located) then
      {thm = theorem, located = located,
       clause = clause_from_located theorem located}
    else raise ERR where_
      ("CPC theorem/result provenance mismatch: theorem=" ^
       Library.term_to_string (Thm.concl theorem) ^ "; located=" ^
       Library.term_to_string (#term located))

  type state = {
    asserted_hyps : Term.term HOLset.set,
    scope_hyps : Term.term list,
    (* Retained for shared canonicalization: TASK_12 consumes these exact
       per-translation emitted-definition records. *)
    translation_definitions : SmtLib.emitted_definition list,
    (* The theorem and its exact occurrence provenance are installed as one
       live entry.  Reusing an id therefore replaces both synchronously. *)
    steps : (string, replayed_step) Redblackmap.dict,
    (* The read side is intentional: CPC commonly repeats normalized facts. *)
    thm_cache : cached_theorem Net.net,
    cache_stats : cache_stats
  }

  fun initial_state definitions asserted_hyps : state = {
    asserted_hyps = HOLset.addList (Term.empty_tmset, asserted_hyps),
    scope_hyps = [],
    translation_definitions = definitions,
    steps = Redblackmap.mkDict String.compare,
    thm_cache = Net.empty,
    cache_stats = new_cache_stats ()
  }

  fun cache_thm_with_fastpath fastpath state thm =
    if not theorem_cache_enabled then
      (profile_event "CPC(cache:insert_disabled)";
       state)
    else if not (cacheable_theorem thm) then
      (profile_event "CPC(cache:insert_not_cacheable)";
       state)
    else
      let
        val stats = #cache_stats state
        val reset = !(#cardinality stats) >= max_cached_theorem_entries
        val thm_cache = if reset then Net.empty else #thm_cache state
        val () = if reset then profile_event "CPC(cache:reset)" else ()
      in
      case optional_fastpath fastpath (Thm.concl thm)
          (fn () => Net.insert (Thm.concl thm, {thm = thm})
            thm_cache) () of
        NONE =>
        (profile_event "CPC(cache:insert_budget_refused)";
         state)
      | SOME thm_cache => let
          val cardinality = if reset then 1 else !(#cardinality stats) + 1
          val () = #cardinality stats := cardinality
          val () = #peak_cardinality stats :=
            Int.max (!(#peak_cardinality stats), cardinality)
          val () = profile_event "CPC(cache:insert)"
        in {
          asserted_hyps = #asserted_hyps state,
          scope_hyps = #scope_hyps state,
          translation_definitions = #translation_definitions state,
          steps = #steps state,
          thm_cache = thm_cache,
          cache_stats = stats
        } end
      end

  fun cache_thm state thm =
    cache_thm_with_fastpath theorem_cache_fastpath state thm

  fun cache_step state id rule_name (result : replay_result) =
  let
    val stats = #cache_stats state
    val () = #step_cardinality stats := !(#step_cardinality stats) + 1
    val theorem = result_theorem result
    val located = result_located result
    (* The replay boundary has already checked the exact conclusion before
       installing this synchronized theorem/provenance pair. *)
    val result = {thm = theorem,
      located = {term = #term located,
        provenance = compact_live_provenance (#provenance located)},
      clause = #clause result}
  in {
    asserted_hyps = #asserted_hyps state,
    scope_hyps = #scope_hyps state,
    translation_definitions = #translation_definitions state,
    steps = Redblackmap.insert (#steps state, id,
      {rule_name = rule_name, result = result}),
    thm_cache = #thm_cache state,
    cache_stats = stats
  } end

  fun remove_step state id =
    case Redblackmap.peek (#steps state, id) of
      NONE => state
    | SOME _ =>
        let
          val steps = Lib.fst (Redblackmap.remove (#steps state, id))
        in {
          asserted_hyps = #asserted_hyps state,
          scope_hyps = #scope_hyps state,
          translation_definitions = #translation_definitions state,
          steps = steps,
          thm_cache = #thm_cache state,
          cache_stats = #cache_stats state
        } end

  fun assert_hyp state tm = {
    asserted_hyps = HOLset.add (#asserted_hyps state, tm),
    scope_hyps = #scope_hyps state,
    translation_definitions = #translation_definitions state,
    steps = #steps state,
    thm_cache = #thm_cache state,
    cache_stats = #cache_stats state
  }

  fun push_scope_hyp state tm = {
    asserted_hyps = #asserted_hyps state,
    scope_hyps = tm :: #scope_hyps state,
    translation_definitions = #translation_definitions state,
    steps = #steps state,
    thm_cache = #thm_cache state,
    cache_stats = #cache_stats state
  }

  fun pop_scope_hyp state =
    case #scope_hyps state of
      tm :: rest => (tm, {
        asserted_hyps = #asserted_hyps state,
        scope_hyps = rest,
        translation_definitions = #translation_definitions state,
        steps = #steps state,
        thm_cache = #thm_cache state,
        cache_stats = #cache_stats state
      })
    | [] => raise ERR "scope" "CPC scope step has no matching assume-push"

  fun find_step what state id : replayed_step =
    Redblackmap.find (#steps state, id)
    handle Redblackmap.NotFound =>
      raise ERR what ("CPC premise step '" ^ id ^ "' was not found")

  fun lookup_step state id = step_theorem
    (find_step "lookup_step" state id)

  fun lookup_premises state ids = List.map (lookup_step state) ids

  fun lookup_rule state id =
    #rule_name (find_step "lookup_rule" state id)

  fun cached_thm_with_fastpath fastpath state tm =
    if not theorem_cache_enabled then
      (profile_event "CPC(cache:probe_disabled)";
       raise ERR "cached_thm" "CPC theorem cache is disabled")
    else let
        fun compute () =
          let
            val available = HOLset.addList
              (#asserted_hyps state, #scope_hyps state)
            fun conclusion_matches cached =
              Term.aconv (Thm.concl (#thm cached)) tm
            fun context_available cached =
              HOLset.isSubset (Thm.hypset (#thm cached), available)
            fun is_raw_assumption cached =
              HOLset.member
                (Thm.hypset (#thm cached), Thm.concl (#thm cached))
            val candidates = List.filter conclusion_matches
              (Net.match tm (#thm_cache state))
            val matches = List.filter context_available candidates
            val rejected = List.filter
              (not o context_available) candidates
            val derived = List.filter (not o is_raw_assumption) matches
            val context_rejections = List.length rejected
          in
            case List.find (fn _ => true)
                (case derived of [] => matches | _ => derived) of
              SOME cached => CacheProbeHit {
                theorem = #thm cached,
                context_rejections = context_rejections,
                hypfree = HOLset.isEmpty (Thm.hypset (#thm cached))
              }
            | NONE => CacheProbeMiss {
                context_rejections = context_rejections
              }
          end

        fun commit_rejections count =
          let
            val stats = #cache_stats state
            val () = #context_rejections stats :=
              !(#context_rejections stats) + count
            fun emit 0 = ()
              | emit remaining =
                  (profile_event "CPC(cache:context_rejected)";
                   emit (remaining - 1))
          in
            emit count
          end

        fun commit outcome =
          case outcome of
            CacheProbeHit {theorem, context_rejections, hypfree} =>
              (commit_rejections context_rejections;
               #hits (#cache_stats state) :=
                 !(#hits (#cache_stats state)) + 1;
               profile_event "CPC(cache:hit)";
               if hypfree then profile_event "CPC(cache:hypfree_hit)"
               else ();
               theorem)
          | CacheProbeMiss {context_rejections} =>
              (commit_rejections context_rejections;
               #misses (#cache_stats state) :=
                 !(#misses (#cache_stats state)) + 1;
               profile_event "CPC(cache:miss)";
               raise ERR "cached_thm"
                 "no alpha-identical cached CPC theorem")
      in
        case optional_fastpath fastpath tm compute () of
          NONE =>
            (profile_event "CPC(cache:probe_budget_refused)";
             raise ERR "cached_thm" "CPC theorem cache budget refused")
        | SOME outcome => profile "CPC(cache:probe)" commit outcome
      end

  fun cached_thm state tm =
    cached_thm_with_fastpath theorem_cache_fastpath state tm

  fun cache_stats state =
    let val stats = #cache_stats state in {
      hits = !(#hits stats),
      misses = !(#misses stats),
      context_rejections = !(#context_rejections stats),
      omitted_bypasses = !(#omitted_bypasses stats),
      cardinality = !(#cardinality stats),
      peak_cardinality = !(#peak_cardinality stats),
      step_cardinality = !(#step_cardinality stats)
    } end

  fun profile_cardinalities state =
    let
      val stats = cache_stats state
      val peak = #peak_cardinality stats
      val steps = #step_cardinality stats
    in
      profile_event ("CPC(cache:peak=" ^ Int.toString peak ^ ")");
      profile_event ("CPC(steps:cardinality=" ^ Int.toString steps ^ ")")
    end

  (* Tactics receive the original theorems as lemmas, but their goal context
     must be exactly the union of the original hypotheses.  Replacing theorem
     premises with fresh assumptions loses provenance (and lets METIS
     instantiate problem variables), which is unsound for CPC replay. *)
  fun metis_prove thms target =
    let
      val hyps = List.foldl
        (fn (thm, acc) => HOLset.union (acc, Thm.hypset thm))
        Term.empty_tmset thms
    in
      profile "CPC(rung:resolution/METIS)" Tactical.TAC_PROOF
        ((HOLset.listItems hyps, target), metisLib.METIS_TAC thms)
    end

  fun expect_one_arg name args =
    case args of [arg] => arg
    | _ => raise ERR name "expected exactly one CPC :args term"

  fun expect_one_premise name prems =
    case prems of [prem] => prem
    | _ => raise ERR name "expected exactly one CPC premise"

  val reglan_equiv_tm = Term.prim_mk_const
    {Thy = "smtstring", Name = "reglan_equiv"}

  fun dest_reglan_equiv proposition =
    case boolSyntax.strip_comb proposition of
      (head, [left, right]) =>
        if Term.same_const head reglan_equiv_tm then (left, right)
        else raise ERR "dest_reglan_equiv" "not RegLan equivalence"
    | _ => raise ERR "dest_reglan_equiv" "not binary RegLan equivalence"

  fun is_reglan_equiv proposition = Lib.can dest_reglan_equiv proposition

  val replay_reglan_refl = SmtRegLanProve.refl
  val replay_reglan_sym = SmtRegLanProve.sym
  val replay_reglan_trans = SmtRegLanProve.trans
  val reglan_congruence_theorems = SmtRegLanProve.congruence_theorems

  fun replay_reglan_cong conclusion prems =
    case conclusion of
      SOME target => metis_prove (prems @ reglan_congruence_theorems) target
    | NONE => raise ERR "cong"
        "RegLan congruence requires a declared exact conclusion"

  fun replay_reglan_cong_from_source source prems =
    let
      val (left, right) = dest_reglan_equiv source
      val (left_premise, right_premise) =
        case prems of
          [left_premise, right_premise] =>
            (left_premise, right_premise)
        | _ => raise ERR "cong"
            "RegLan relation congruence expects two operand premises"
      fun orient operand premise =
        let val (source, destination) =
          dest_reglan_equiv (Thm.concl premise)
        in
          if Term.aconv source operand then premise
          else if Term.aconv destination operand then replay_reglan_sym premise
          else raise ERR "cong"
            "RegLan congruence premise does not start at its source operand"
        end
      val left_premise = orient left left_premise
      val right_premise = orient right right_premise
    in
      Drule.MATCH_MP smtstringTheory.reglan_equiv_equiv_eq
        (Thm.CONJ left_premise right_premise)
    end

  (* Omitted-conclusion CONG/NARY_CONG steps name the source application in
     :args.  Infer the other endpoint only for constructors proved respectful
     of language equivalence, consuming every supplied premise exactly once.
     Unchanged operands receive reflexivity; an unrelated premise is a loud
     failure rather than evidence for an opaque RegLan context. *)
  fun replay_reglan_producer_cong_from_source source prems =
    let
      val remaining = ref prems
      fun take orient operand fallback =
        let
          fun search skipped [] = (fallback operand, operand)
            | search skipped (premise :: rest) =
                (case Lib.total (orient operand) premise of
                   SOME result =>
                     (remaining := List.revAppend (skipped, rest); result)
                 | NONE => search (premise :: skipped) rest)
        in
          search [] (!remaining)
        end
      fun orient_reglan operand premise =
        let
          val (left, right) = dest_reglan_equiv (Thm.concl premise)
        in
          if Term.aconv left operand then (premise, right)
          else if Term.aconv right operand then
            (replay_reglan_sym premise, left)
          else raise ERR "cong"
            "RegLan premise does not rewrite this constructor operand"
        end
      fun orient_equality operand premise =
        let
          val (left, right) = boolSyntax.dest_eq (Thm.concl premise)
        in
          if Term.aconv left operand then (premise, right)
          else if Term.aconv right operand then (Thm.SYM premise, left)
          else raise ERR "cong"
            "equality premise does not rewrite this constructor operand"
        end
      fun reglan_operand operand =
        take orient_reglan operand replay_reglan_refl
      fun equality_operand operand =
        take orient_equality operand Thm.REFL
      fun require_consumed () =
        if List.null (!remaining) then ()
        else raise ERR "cong"
          "RegLan constructor congruence has an unrelated premise"
      fun named thy name head =
        case Lib.total Term.dest_thy_const head of
          SOME {Thy, Name, ...} => Thy = thy andalso Name = name
        | NONE => false
      fun semantic_target destination =
        let
          val _ = require_consumed ()
          val target = Term.list_mk_comb
            (reglan_equiv_tm, [source, destination])
        in
          metis_prove (prems @ reglan_congruence_theorems) target
        end
      val (head, operands) = boolSyntax.strip_comb source
      fun unary make =
        case operands of
          [regex] =>
            let val (_, regex') = reglan_operand regex
            in semantic_target (make regex') end
        | _ => raise ERR "cong" "RegLan unary constructor has wrong arity"
      fun binary make =
        case operands of
          [left, right] =>
            let
              val (_, left') = reglan_operand left
              val (_, right') = reglan_operand right
            in
              semantic_target (make left' right')
            end
        | _ => raise ERR "cong" "RegLan binary constructor has wrong arity"
      fun rebuild operator arguments = Term.list_mk_comb (operator, arguments)
      fun conditional () =
        let
          val (test, yes, no) = boolSyntax.dest_cond source
          val (_, test') = equality_operand test
          val (_, yes') = reglan_operand yes
          val (_, no') = reglan_operand no
        in
          semantic_target (boolSyntax.mk_cond (test', yes', no'))
        end
    in
      if boolSyntax.is_cond source then conditional ()
      else if named "smtstring" "reglan_star" head orelse
              named "smtstring" "reglan_comp" head orelse
              named "smtstring" "reglan_plus" head orelse
              named "smtstring" "reglan_opt" head then
        unary (fn regex => rebuild head [regex])
      else if named "smtstring" "reglan_concat" head orelse
              named "smtstring" "reglan_union" head orelse
              named "smtstring" "reglan_inter" head orelse
              named "smtstring" "reglan_diff" head then
        binary (fn left => fn right => rebuild head [left, right])
      else
        raise ERR "cong"
          "semantic RegLan premise occurs under an opaque producer"
    end

  fun replay_reglan_consumer_cong_from_source source prems =
    let
      val (head, operands) = boolSyntax.strip_comb source
      val _ =
        (case Lib.total Term.dest_thy_const head of
           SOME {Thy = "smtstring", Name = "smt_in_re", ...} => ()
         | _ => raise ERR "cong"
             "semantic RegLan premise occurs under an opaque function")
      val (string, regex) =
        case operands of
          [string, regex] => (string, regex)
        | _ => raise ERR "cong" "smt_in_re has wrong arity"
      val (string_premise, regex_premise) =
        case prems of
          [string_premise, regex_premise] =>
            (string_premise, regex_premise)
        | _ => raise ERR "cong"
            "smt_in_re congruence expects two operand premises"
      val (string_source, string_destination) =
        boolSyntax.dest_eq (Thm.concl string_premise)
      val (string_premise, string_destination) =
        if Term.aconv string_source string then
          (string_premise, string_destination)
        else if Term.aconv string_destination string then
          (Thm.SYM string_premise, string_source)
        else raise ERR "cong"
          "string congruence premise does not start at its source operand"
      val (regex_source, regex_destination) =
        dest_reglan_equiv (Thm.concl regex_premise)
      val (regex_premise, regex_destination) =
        if Term.aconv regex_source regex then
          (regex_premise, regex_destination)
        else if Term.aconv regex_destination regex then
          (replay_reglan_sym regex_premise, regex_source)
        else raise ERR "cong"
          "RegLan congruence premise does not start at its source operand"
      fun membership string regex = Term.list_mk_comb
        (Term.prim_mk_const {Thy = "smtstring", Name = "smt_in_re"},
         [string, regex])
      val binder = Term.variant
        (Term.free_vars source @ Term.free_vars (Thm.concl string_premise))
        (Term.mk_var ("cpc_string", Term.type_of string))
      val string_lift = Conv.BETA_RULE (Thm.AP_TERM
        (Term.mk_abs (binder, membership binder regex)) string_premise)
      val regex_target = boolSyntax.mk_imp
        (Thm.concl regex_premise,
         boolSyntax.mk_eq
           (membership string_destination regex,
            membership string_destination regex_destination))
      val generic = Drule.SPEC_ALL
        smtstringTheory.smt_in_re_equiv_eq
      val specialized = Drule.INST_TY_TERM
        (Term.match_term (Thm.concl generic) regex_target) generic
      val regex_lift = Thm.MP specialized regex_premise
    in
      Thm.TRANS string_lift regex_lift
    end

  fun replay_refl conclusion args =
    case conclusion of
      SOME eq =>
        (case Lib.total dest_reglan_equiv eq of
           SOME (left, right) =>
             if Term.aconv left right then replay_reglan_refl left
             else raise ERR "refl"
               "CPC RegLan refl conclusion is not reflexive"
         | NONE =>
             let val (left, right) = boolSyntax.dest_eq eq in
               if Term.aconv left right then Thm.REFL left
               else raise ERR "refl" "CPC refl conclusion is not reflexive"
             end)
    | NONE =>
        let val argument = expect_one_arg "refl" args in
          if Type.compare
              (Term.type_of argument, reglan_ty) = EQUAL
          then replay_reglan_refl argument
          else Thm.REFL argument
        end

  fun replay_eq_refl args =
    Drule.EQT_INTRO (Thm.REFL (expect_one_arg "eq-refl" args))

  fun replay_instantiate args prems =
    Drule.SPECL args (expect_one_premise "instantiate" prems)

  fun conversion_equal name conv target =
    Library.conversion_equal name conv (boolSyntax.dest_eq target)

  fun replay_beta_reduce args =
    conversion_equal "beta-reduce"
      (Conv.TOP_DEPTH_CONV Thm.BETA_CONV)
      (expect_one_arg "beta-reduce" args)

  fun replay_lambda_elim args =
    conversion_equal "lambda-elim"
      (Conv.TOP_DEPTH_CONV Drule.ETA_CONV)
      (expect_one_arg "lambda-elim" args)

  (* CPC's HO_CONG omits both :args and its conclusion.  For an n-ary
     application cvc5 emits the function equality followed by one equality
     per argument, which is exactly a left-to-right fold of the HOL kernel's
     MK_COMB rule over the curried application. *)
  fun replay_ho_cong prems =
    case prems of
      function_equality :: (argument_equalities as _ :: _) =>
        (List.foldl
           (fn (argument_equality, applied) =>
              Thm.MK_COMB (applied, argument_equality))
           function_equality argument_equalities
         handle Feedback.HOL_ERR holerr =>
           raise ERR "ho_cong"
             ("MK_COMB rejected CPC premise types: " ^
              Feedback.message_of holerr))
    | _ => raise ERR "ho_cong"
        "expected a function equality and at least one argument equality"

  (* A CPC congruence step supplies the source term in :args and equality
     premises for the subterms rewritten by cvc5.  Reconstruct its context as
     a HOL lambda and use AP_TERM; this is the kernel congruence rule, not a
     rewriting oracle. *)
  fun replace_first old replacement root =
    let
      val bucket_count = 4093
      val failed_buckets =
        Array.array (bucket_count, [] : Term.term list)
      fun name_hash name =
        let
          fun loop index hash =
            if index = String.size name then hash
            else loop (index + 1)
              ((hash * 33 + Char.ord (String.sub (name, index))) mod
               bucket_count)
        in loop 0 5381 end
      fun hash term =
        if Term.is_var term then name_hash (#1 (Term.dest_var term))
        else if Term.is_const term then
          name_hash (#Name (Term.dest_thy_const term))
        else if Term.is_abs term then 17
        else
          let val (operator, _) = Term.dest_comb term in
            (23 + (if Term.is_const operator then
                     name_hash (#Name (Term.dest_thy_const operator))
                   else 29)) mod bucket_count
          end
          handle Feedback.HOL_ERR _ => 31
      fun was_failed term =
        let val bucket = Array.sub (failed_buckets, hash term)
        in List.exists (fn saved => Portable.pointer_eq (saved, term)) bucket end
      fun record_failed term =
        let val index = hash term
        in Array.update
             (failed_buckets, index,
              term :: Array.sub (failed_buckets, index)) end
      fun search tm =
        if Portable.pointer_eq (tm, old) orelse Term.aconv tm old then
          SOME (if Portable.pointer_eq (old, replacement) then tm
                else replacement)
        else if was_failed tm then NONE
        else
          let
            val result =
              if Term.is_abs tm then
                let val (variable, body) = Term.dest_abs tm in
                  Option.map (fn body' => Term.mk_abs (variable, body'))
                    (search body)
                end
              else
                let
                  val (rator, rand) = Term.dest_comb tm
                in
                  case search rator of
                    SOME rator' => SOME (Term.mk_comb (rator', rand))
                  | NONE => Option.map
                      (fn rand' => Term.mk_comb (rator, rand')) (search rand)
                end
                handle Feedback.HOL_ERR _ => NONE
            val _ = case result of NONE => record_failed tm | SOME _ => ()
          in result end
    in search root end

  fun contains_abs tm =
    Term.is_abs tm orelse
    (let val (rator, rand) = Term.dest_comb tm in
       contains_abs rator orelse contains_abs rand
     end handle _ => false)

  fun contains_abs_dag root = provenance_term_has_abs root

  fun expose_true_equality premise =
    let
      val (left, right) = boolSyntax.dest_eq (Thm.concl premise)
    in
      if Term.aconv left boolSyntax.T then
        Thm.EQ_MP premise boolTheory.TRUTH
      else if Term.aconv right boolSyntax.T then
        Thm.EQ_MP (Thm.SYM premise) boolTheory.TRUTH
      else premise
    end
    handle Feedback.HOL_ERR _ => premise

  fun replay_cong conclusion args prems =
    let
      val source = expect_one_arg "cong" args
      fun expose_congruence premise =
        let val exposed = expose_true_equality premise in
          if boolSyntax.is_eq (Thm.concl exposed) then exposed
          else premise
        end
      fun nontrivial premise =
        if Term.aconv (Thm.concl premise) boolSyntax.T then
          false
        else
          let val (left, right) = boolSyntax.dest_eq (Thm.concl premise)
          in not (Term.aconv left right) end
          handle Feedback.HOL_ERR _ => true
      val prems = List.filter nontrivial
        (List.map expose_congruence prems)
      fun apply premise current =
        let
          val (premise, occurrence) =
            let val (left, _) = boolSyntax.dest_eq (Thm.concl premise) in
              case replace_first left left current of
                SOME occurrence => (premise, occurrence)
              | NONE =>
                  let
                    val (_, right) = boolSyntax.dest_eq (Thm.concl premise)
                  in
                    case replace_first right right current of
                      SOME occurrence => (Thm.SYM premise, occurrence)
                    | NONE => raise ERR "cong"
                        ("CPC congruence premise has no occurrence in its :args term; " ^
                         "current=" ^ Library.term_to_string current ^
                         "; premise=" ^ Library.thm_to_string premise)
                  end
            end
          val (left, right) = boolSyntax.dest_eq (Thm.concl premise)
          val left_key = occurrence
          val failed = Array.array (4093, [] : Term.term list)
          fun string_hash string =
            let
              fun loop index hash =
                if index = String.size string then hash
                else loop (index + 1)
                  ((hash * 33 + Char.ord (String.sub (string, index))) mod
                   4093)
            in loop 0 5381 end
          fun spine (term, arity) =
            if Term.is_comb term then spine (Term.rator term, arity + 1)
            else (term, arity)
          fun pointer_hash term =
            let val (head, arity) = spine (term, 0) in
              if Term.is_const head then
                (37 * string_hash (#Name (Term.dest_thy_const head)) + arity)
                mod 4093
              else if Term.is_var head then
                (41 * string_hash (#1 (Term.dest_var head)) + arity) mod 4093
              else (43 + arity) mod 4093
            end
          fun known_failed term =
            List.exists (fn saved => Portable.pointer_eq (saved, term))
              (Array.sub (failed, pointer_hash term))
          fun record_failed term =
            let val index = pointer_hash term in
              Array.update (failed, index,
                term :: Array.sub (failed, index))
            end
          fun anchor term theorem =
            if Portable.pointer_eq
                 (boolSyntax.lhs (Thm.concl theorem), term) then theorem
            else Thm.TRANS (Thm.REFL term) theorem
          fun lift term =
            if Portable.pointer_eq (term, left) orelse
               Portable.pointer_eq (term, left_key) then
              SOME (anchor term premise)
            else if known_failed term then NONE
            else
              let
                val result =
                  if Term.is_abs term then
                    let val (variable, body) = Term.dest_abs term in
                      Option.map
                        (fn theorem => anchor term (Thm.ABS variable theorem))
                        (lift body)
                    end
                  else
                    let
                      val (operator, operand) = Term.dest_comb term
                    in
                      case lift operator of
                        SOME theorem =>
                          SOME (anchor term
                            (Thm.MK_COMB (theorem, Thm.REFL operand)))
                      | NONE => Option.map
                          (fn theorem => anchor term
                            (Thm.MK_COMB (Thm.REFL operator, theorem)))
                          (lift operand)
                    end
                    handle Feedback.HOL_ERR _ => NONE
                val _ = case result of
                    NONE => record_failed term
                  | SOME _ => ()
              in result end
        in
          case lift current of
            SOME theorem => theorem
          | NONE => raise ERR "cong"
              "kernel congruence path did not contain the premise endpoint"
        end
      fun loop current accumulated [] = accumulated
        | loop current accumulated (premise :: rest) =
            let val next = apply premise current
                val (_, next_current) = boolSyntax.dest_eq (Thm.concl next)
                val accumulated = Thm.TRANS accumulated next
                  handle Feedback.HOL_ERR _ =>
                    raise ERR "cong"
                      ("CPC congruence rewrites do not compose; first=" ^
                       Library.term_to_string (Thm.concl accumulated) ^
                       "; next=" ^ Library.term_to_string (Thm.concl next))
            in loop next_current accumulated rest end
      fun quantified_cong () =
        case prems of
          [premise] =>
            let
              fun orient body =
                let val (left, right) = boolSyntax.dest_eq (Thm.concl premise)
                in
                  if Term.aconv body left then premise
                  else if Term.aconv body right then Thm.SYM premise
                  else raise ERR "cong"
                    "quantified congruence premise does not rewrite its body"
                end
              val (forall_variables, forall_body) =
                boolSyntax.strip_forall source
            in
              if List.null forall_variables then
                let
                  val (exists_variables, exists_body) =
                    boolSyntax.strip_exists source
                in
                  if List.null exists_variables then
                    raise ERR "cong" "source is not quantified"
                  else List.foldr
                    (fn (variable, theorem) =>
                      Drule.EXISTS_EQ variable theorem)
                    (orient exists_body) exists_variables
                end
              else List.foldr
                (fn (variable, theorem) =>
                  Drule.FORALL_EQ variable theorem)
                (orient forall_body) forall_variables
            end
        | _ => raise ERR "cong"
            "quantified congruence expects one nontrivial premise"
      fun structural_cong () =
        let
          val consume_premises =
            case conclusion of NONE => true | SOME _ => false
          val remaining = ref prems
          fun exact_rewrite tm =
            let
              fun search skipped premises =
                case premises of
                  [] => NONE
                | premise :: rest =>
                let
                  val (left, right) = boolSyntax.dest_eq (Thm.concl premise)
                  fun matched theorem =
                    let
                      val _ =
                        if consume_premises then
                          remaining := List.revAppend (skipped, rest)
                        else
                          ()
                    in
                      SOME theorem
                    end
                in
                  if Term.aconv tm left then
                    matched premise
                  else if Term.aconv tm right then
                    matched (Thm.SYM premise)
                  else
                    search (premise :: skipped) rest
                end
            in
              search [] (if consume_premises then !remaining else prems)
            end
          fun rewrite tm =
            case exact_rewrite tm of
              SOME theorem => theorem
            | NONE =>
                if Term.is_abs tm then
                  let val (variable, body) = Term.dest_abs tm
                  in Thm.ABS variable (rewrite body) end
                else
                  let val (rator, rand) = Term.dest_comb tm
                  in Thm.MK_COMB (rewrite rator, rewrite rand) end
                  handle Feedback.HOL_ERR _ => Thm.REFL tm
          val result = rewrite source
          val (left, right) = boolSyntax.dest_eq (Thm.concl result)
          val _ = not (Term.aconv left right) orelse
            raise ERR "cong" "structural congruence made no progress"
          val _ =
            case conclusion of
              SOME _ => ()
            | NONE =>
                if List.null (!remaining) then
                  ()
                else
                  raise ERR "cong"
                    "structural congruence left an unused premise"
        in
          result
        end
      fun targeted_cong () =
        let
          val target =
            case conclusion of
              SOME target => target
            | NONE => raise ERR "cong"
                "target-guided congruence needs a certificate conclusion"
          fun exact_rewrite left right premises =
            case premises of
              [] => NONE
            | premise :: rest =>
                let
                  val (prem_left, prem_right) =
                    boolSyntax.dest_eq (Thm.concl premise)
                in
                  if Term.aconv left prem_left andalso
                     Term.aconv right prem_right
                  then SOME premise
                  else if Term.aconv left prem_right andalso
                          Term.aconv right prem_left
                  then SOME (Thm.SYM premise)
                  else exact_rewrite left right rest
                end
          fun rewrite left right =
            if Term.aconv left right then Thm.REFL left
            else
              case exact_rewrite left right prems of
                SOME theorem => theorem
              | NONE =>
                  if Term.is_abs left andalso Term.is_abs right then
                    let
                      val (left_var, left_body) = Term.dest_abs left
                      val (right_var, right_body) = Term.dest_abs right
                      val _ = Term.aconv left_var right_var orelse
                        raise ERR "cong"
                          "target-guided congruence changed a binder"
                    in
                      Thm.ABS left_var (rewrite left_body right_body)
                    end
                  else
                    let
                      val (left_rator, left_rand) = Term.dest_comb left
                      val (right_rator, right_rand) = Term.dest_comb right
                    in
                      Thm.MK_COMB
                        (rewrite left_rator right_rator,
                         rewrite left_rand right_rand)
                    end
                    handle Feedback.HOL_ERR _ => raise ERR "cong"
                      "target-guided congruence cannot reconstruct conclusion"
          val (target_left, target_right) = boolSyntax.dest_eq target
        in
          if Term.aconv source target_left then
            rewrite target_left target_right
          else if Term.aconv source target_right then
            Thm.SYM (rewrite target_right target_left)
          else raise ERR "cong"
            "certificate conclusion does not contain the congruence source"
        end
      fun sequential_cong () =
        case prems of
          [] => Thm.REFL source
        | premise :: rest =>
            let
              val first = apply premise source
              val (_, first_current) = boolSyntax.dest_eq (Thm.concl first)
            in loop first_current first rest end
      fun matches_conclusion replay =
        let
          val result = replay ()
        in
          case conclusion of
            NONE => result
          | SOME target =>
              if Term.aconv (Thm.concl result) target then result
              else raise ERR "cong"
                "congruence strategy does not match certificate conclusion"
        end
      fun fallback_cong () =
        matches_conclusion sequential_cong
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else matches_conclusion structural_cong
    in
      matches_conclusion quantified_cong
      handle Feedback.HOL_ERR _ => matches_conclusion targeted_cong
      handle Feedback.HOL_ERR _ => fallback_cong ()
    end

  (* Exact compatibility is about the erased syntax topology, never the
     diagnostic source label carried by a conjunction.  Atomic nodes match
     only when both sides prove that no conjunction boundary was erased. *)
  fun provenance_topology_compatible left right =
    let
      fun lists [] [] = true
        | lists (x :: xs) (y :: ys) =
            provenance_topology_compatible x y andalso lists xs ys
        | lists _ _ = false
    in
      case (left, right) of
        (AtomicProvenance, other) =>
          definitely_no_conjunction other
      | (other, AtomicProvenance) =>
          definitely_no_conjunction other
      | (ApplicationProvenance (_, left_operands),
         ApplicationProvenance (_, right_operands)) =>
          (* Term.aconv at the candidate occurrence already proves that the
             elaborated HOL operators agree.  Raw CPC aliases and semantic
             replay constructors can give that same operator different
             diagnostic names, so occurrence compatibility is deliberately
             about retained child topology, not those source labels. *)
          lists left_operands right_operands
      | (BinderProvenance (_, left_body),
         BinderProvenance (_, right_body)) =>
          provenance_topology_compatible left_body right_body
      | (BinderBlockProvenance (_, left_size, left_body),
         BinderBlockProvenance (_, right_size, right_body)) =>
          left_size = right_size andalso
          provenance_topology_compatible left_body right_body
      | (EqualityProvenance (left_lhs, left_rhs),
         EqualityProvenance (right_lhs, right_rhs)) =>
          provenance_topology_compatible left_lhs right_lhs andalso
          provenance_topology_compatible left_rhs right_rhs
      | (ConjunctionProvenance (_, left_operands),
         ConjunctionProvenance (_, right_operands)) =>
          lists left_operands right_operands
      | _ => false
    end

  (* CPC congruence uses deterministic left-to-right preorder.  Resolve that
     occurrence once over the exact located tree, and lift the selected
     equality through the same path with kernel congruence.  Thus the theorem
     and the replacement provenance cannot disagree about which
     alpha-equivalent occurrence was rewritten. *)
  fun replay_exact_cong_result conclusion
      (source : located_term) (premise_steps : replayed_step list) =
    let
      (* Keep the parsed source's full occurrence tree.  Even a constructor
         that is conjunction-free before rewriting can contain the exact
         occurrence replaced by a conjunction-bearing endpoint.  Live step
         results may compact proven conjunction-free shells, but parsed CONG
         arguments must retain their constructor path to justify that lift. *)
      datatype occurrence_rewrite =
          OccurrenceAbsent
        | OccurrenceBlocked of string
        | OccurrenceRewritten of located_term * Thm.thm

      fun split_conjunction n term =
        if n = 1 then [term]
        else if n > 1 then
          let val (left, right) = boolSyntax.dest_conj term in
            left :: split_conjunction (n - 1) right
          end
        else raise ERR "cong_provenance"
          "conjunction provenance has no operands"

      fun mk_conjunction terms =
        case terms of
          [] => raise ERR "cong_provenance"
              "empty conjunction occurrence"
        | [term] => term
        | term :: rest => boolSyntax.mk_conj
            (term, mk_conjunction rest)

      fun binder_body head term =
        if head = "forall" then #2 (boolSyntax.dest_forall term)
        else if head = "exists" then #2 (boolSyntax.dest_exists term)
        else #2 (Term.dest_abs term)

      fun rebuild_binder head term body =
        if head = "forall" then
          boolSyntax.mk_forall (#1 (boolSyntax.dest_forall term), body)
        else if head = "exists" then
          boolSyntax.mk_exists (#1 (boolSyntax.dest_exists term), body)
        else Term.mk_abs (#1 (Term.dest_abs term), body)

      fun dest_binder_block head size term =
        let
          fun dest 0 current variables = (List.rev variables, current)
            | dest remaining current variables =
                let
                  val (variable, body) =
                    if head = "forall" then boolSyntax.dest_forall current
                    else if head = "exists" then
                      boolSyntax.dest_exists current
                    else Term.dest_abs current
                in
                  dest (remaining - 1) body (variable :: variables)
                end
        in
          if size >= 0 then dest size term []
          else raise ERR "cong_provenance" "negative binder-block size"
        end

      fun rebuild_binder_block head variables body =
        if head = "forall" then boolSyntax.list_mk_forall (variables, body)
        else if head = "exists" then
          boolSyntax.list_mk_exists (variables, body)
        else Term.list_mk_abs (variables, body)

      fun lift_binder_block head variables theorem =
        List.foldr
          (fn (variable, lifted) =>
            if head = "forall" then Drule.FORALL_EQ variable lifted
            else if head = "exists" then Drule.EXISTS_EQ variable lifted
            else Thm.ABS variable lifted)
          theorem variables

      fun checked_endpoints where_ theorem old replacement =
        let
          val (left, right) = boolSyntax.dest_eq (Thm.concl theorem)
            handle Feedback.HOL_ERR holerr =>
              raise ERR "cong_provenance"
                (where_ ^ " did not produce an equality theorem; theorem=" ^
                 Library.term_to_string (Thm.concl theorem) ^ "; " ^
                 Feedback.message_of holerr)
        in
          if Term.aconv left old andalso Term.aconv right replacement then
            theorem
          else raise ERR "cong_provenance"
            (where_ ^ " produced endpoints different from its exact path; " ^
             "source=" ^ Library.term_to_string old ^
             "; replacement=" ^ Library.term_to_string replacement ^
             "; theorem=" ^ Library.term_to_string (Thm.concl theorem))
        end

      fun lift_context parent rebuild child_theorem =
        let
          val (old_child, new_child) =
            boolSyntax.dest_eq (Thm.concl child_theorem)
          val hole = Term.variant
            (Term.free_vars parent @
             Term.free_vars (Thm.concl child_theorem))
            (Term.mk_var ("cpc_cong_hole", Term.type_of old_child))
          val old_parent = rebuild old_child
          val _ = Term.aconv old_parent parent orelse
            raise ERR "cong_provenance"
              "occurrence context does not rebuild its source"
          val context = Term.mk_abs (hole, rebuild hole)
          val lifted = Conv.CONV_RULE
            (Conv.TOP_DEPTH_CONV Thm.BETA_CONV)
            (Thm.AP_TERM context child_theorem)
        in
          checked_endpoints "lifted occurrence" lifted parent
            (rebuild new_child)
        end

      fun term_has_occurrence candidate term =
        Option.isSome (replace_first candidate candidate term)

      fun rewrite_atomic term candidate replacement replacement_provenance
          oriented =
        if definitely_no_conjunction replacement_provenance then
          let
            fun search current =
              if Term.aconv current candidate then
                OccurrenceRewritten
                  ({term = replacement, provenance = AtomicProvenance},
                   checked_endpoints "atomic root occurrence" oriented
                     current replacement)
              else if Term.is_abs current then
                let
                  val (variable, body) = Term.dest_abs current
                in
                  case search body of
                    OccurrenceAbsent => OccurrenceAbsent
                  | OccurrenceBlocked reason => OccurrenceBlocked reason
                  | OccurrenceRewritten
                      ({term = body', ...}, body_theorem) =>
                      let
                        val term' = Term.mk_abs (variable, body')
                        val theorem = Thm.ABS variable body_theorem
                          handle Feedback.HOL_ERR holerr =>
                            raise ERR "cong_provenance"
                              ("atomic binder lift failed; body=" ^
                               Library.term_to_string
                                 (Thm.concl body_theorem) ^ "; " ^
                               Feedback.message_of holerr)
                      in
                        OccurrenceRewritten
                          ({term = term', provenance = AtomicProvenance},
                           checked_endpoints "atomic binder occurrence"
                             theorem current term')
                      end
                end
              else
                (case Lib.total Term.dest_comb current of
                   NONE => OccurrenceAbsent
                 | SOME (operator, argument) =>
                  case search operator of
                    OccurrenceBlocked reason => OccurrenceBlocked reason
                  | OccurrenceRewritten
                      ({term = operator', ...}, operator_theorem) =>
                      let
                        val term' = Term.mk_comb (operator', argument)
                        val theorem = Thm.MK_COMB
                          (operator_theorem, Thm.REFL argument)
                          handle Feedback.HOL_ERR holerr =>
                            raise ERR "cong_provenance"
                              ("atomic operator lift failed; operator=" ^
                               Library.term_to_string
                                 (Thm.concl operator_theorem) ^
                               "; argument=" ^
                               Library.term_to_string argument ^ "; " ^
                               Feedback.message_of holerr)
                      in
                        OccurrenceRewritten
                          ({term = term', provenance = AtomicProvenance},
                           checked_endpoints "atomic operator occurrence"
                             theorem current term')
                      end
                  | OccurrenceAbsent =>
                      (case search argument of
                         OccurrenceAbsent => OccurrenceAbsent
                       | OccurrenceBlocked reason =>
                           OccurrenceBlocked reason
                       | OccurrenceRewritten
                           ({term = argument', ...}, argument_theorem) =>
                           let
                             val term' = Term.mk_comb (operator, argument')
                             val theorem = Thm.MK_COMB
                               (Thm.REFL operator, argument_theorem)
                               handle Feedback.HOL_ERR holerr =>
                                 raise ERR "cong_provenance"
                                   ("atomic argument lift failed; operator=" ^
                                    Library.term_to_string operator ^
                                    "; argument=" ^
                                    Library.term_to_string
                                      (Thm.concl argument_theorem) ^ "; " ^
                                    Feedback.message_of holerr)
                           in
                             OccurrenceRewritten
                               ({term = term',
                                 provenance = AtomicProvenance},
                                checked_endpoints
                                  "atomic argument occurrence" theorem
                                  current term')
                           end))
                handle Feedback.HOL_ERR holerr =>
                  OccurrenceBlocked
                    ("atomic traversal failed at " ^
                     Library.term_to_string current ^ "; " ^
                     Feedback.message_of holerr)
          in
            search term
          end
        else if term_has_occurrence candidate term then
          OccurrenceBlocked
            "opaque conjunction-free occurrence would gain a conjunction"
        else OccurrenceAbsent

      fun rewrite_children parent terms provenances rebuild_term
          rebuild_provenance candidate candidate_provenance replacement
          replacement_provenance oriented =
        let
          fun scan _ _ [] [] = OccurrenceAbsent
            | scan term_prefix provenance_prefix
                (term :: term_rest) (provenance :: provenance_rest) =
                (case rewrite_occurrence term provenance candidate
                    candidate_provenance replacement replacement_provenance
                    oriented of
                   OccurrenceAbsent =>
                     scan (term :: term_prefix)
                       (provenance :: provenance_prefix)
                       term_rest provenance_rest
                 | OccurrenceBlocked reason => OccurrenceBlocked reason
                 | OccurrenceRewritten
                     ({term = term', provenance = provenance'}, theorem) =>
                     let
                       val terms' = List.rev term_prefix @
                         term' :: term_rest
                       val provenances' = List.rev provenance_prefix @
                         provenance' :: provenance_rest
                       val parent' = rebuild_term terms'
                       val lifted = lift_context parent
                         (fn child => rebuild_term
                           (List.rev term_prefix @ child :: term_rest))
                         theorem
                     in
                       OccurrenceRewritten
                         ({term = parent',
                           provenance =
                             rebuild_provenance provenances'},
                          checked_endpoints "child occurrence" lifted parent
                            parent')
                     end)
            | scan _ _ _ _ = OccurrenceBlocked
                "occurrence children do not align with the elaborated term"
        in
          scan [] [] terms provenances
        end

      and rewrite_occurrence term provenance candidate
          candidate_provenance replacement replacement_provenance oriented =
        if Term.aconv term candidate andalso
           provenance_topology_compatible provenance candidate_provenance
        then
          OccurrenceRewritten
            ({term = replacement, provenance = replacement_provenance},
             checked_endpoints "root occurrence" oriented term replacement)
        else
          (case provenance of
             ConjunctionProvenance (_, operands) =>
               let
                 val terms = split_conjunction
                   (List.length operands) term
               in
                 rewrite_children term terms operands mk_conjunction
                   (fn children =>
                     ConjunctionProvenance
                       (CongruenceConjunction, children))
                   candidate candidate_provenance replacement
                   replacement_provenance oriented
               end
           | EqualityProvenance (left, right) =>
               let
                 val (left_term, right_term) = boolSyntax.dest_eq term
                 fun rebuild_term [left', right'] =
                       boolSyntax.mk_eq (left', right')
                   | rebuild_term _ = raise ERR "cong_provenance"
                       "equality occurrence children are malformed"
                 fun rebuild_provenance [left', right'] =
                       EqualityProvenance (left', right')
                   | rebuild_provenance _ =
                       UnavailableProvenance
                         "equality provenance children are malformed"
               in
                 rewrite_children term [left_term, right_term]
                   [left, right] rebuild_term rebuild_provenance
                   candidate candidate_provenance replacement
                   replacement_provenance oriented
               end
           | ApplicationProvenance (head, operands) =>
               let
                 val (operator, arguments) = boolSyntax.strip_comb term
                 fun rebuild_term children =
                   Term.list_mk_comb (operator, children)
                 fun rebuild_provenance children =
                   ApplicationProvenance (head, children)
                 fun arguments_result () =
                     rewrite_children term arguments operands rebuild_term
                       rebuild_provenance candidate candidate_provenance
                       replacement replacement_provenance oriented
               in
                 if definitely_no_conjunction provenance andalso
                    definitely_no_conjunction candidate_provenance andalso
                    definitely_no_conjunction replacement_provenance andalso
                    not (contains_binder_block provenance) andalso
                    not (contains_binder_block candidate_provenance) andalso
                    not (contains_binder_block replacement_provenance)
                 then
                   (* Raw CPC applications may be n-ary while their HOL
                      elaboration is nested binary.  Once all three trees
                      are proved conjunction-free, those erased boundaries
                      are semantically irrelevant: use the kernel term's
                      deterministic preorder and compact the rewritten
                      application to Atomic.  A conjunction-bearing source
                      or replacement still takes the exact structured path
                      below, so this case cannot guess an and boundary. *)
                   rewrite_atomic term candidate replacement
                     replacement_provenance oriented
                 else arguments_result ()
               end
           | BinderProvenance (head, body) =>
               let
                 val body_term = binder_body head term
               in
                 case rewrite_occurrence body_term body candidate
                     candidate_provenance replacement
                     replacement_provenance oriented of
                   OccurrenceAbsent => OccurrenceAbsent
                 | OccurrenceBlocked reason => OccurrenceBlocked reason
                 | OccurrenceRewritten
                     ({term = body', provenance = body_provenance}, theorem) =>
                     let
                       val term' = rebuild_binder head term body'
                       val variable =
                         if head = "forall" then
                           #1 (boolSyntax.dest_forall term)
                         else if head = "exists" then
                           #1 (boolSyntax.dest_exists term)
                         else #1 (Term.dest_abs term)
                       (* Quantifier congruence must deliberately bind the
                          free body variable on both sides.  A generic beta
                          context is capture-avoiding and would rename the
                          quantifier, leaving that variable free. *)
                       val lifted =
                         if head = "forall" then
                           Drule.FORALL_EQ variable theorem
                         else if head = "exists" then
                           Drule.EXISTS_EQ variable theorem
                         else Thm.ABS variable theorem
                       val _ = profile_event
                         ("CPC(cong:binder/" ^ head ^ ")")
                     in
                       OccurrenceRewritten
                         ({term = term',
                           provenance =
                             BinderProvenance (head, body_provenance)},
                          checked_endpoints "binder occurrence" lifted term
                            term')
                     end
               end
           | BinderBlockProvenance (head, size, body) =>
               let
                 val (variables, body_term) =
                   dest_binder_block head size term
               in
                 case rewrite_occurrence body_term body candidate
                     candidate_provenance replacement
                     replacement_provenance oriented of
                   OccurrenceAbsent => OccurrenceAbsent
                 | OccurrenceBlocked reason => OccurrenceBlocked reason
                 | OccurrenceRewritten
                     ({term = body', provenance = body_provenance}, theorem) =>
                     let
                       val term' = rebuild_binder_block head variables body'
                       val lifted = lift_binder_block head variables theorem
                       val _ = profile_event
                         ("CPC(cong:binder/" ^ head ^ ")")
                     in
                       OccurrenceRewritten
                         ({term = term',
                           provenance = BinderBlockProvenance
                             (head, size, body_provenance)},
                          checked_endpoints "binder-block occurrence" lifted
                            term term')
                     end
               end
           | AtomicProvenance =>
               if definitely_no_conjunction candidate_provenance andalso
                  not (contains_binder_block candidate_provenance) andalso
                  not (contains_binder_block replacement_provenance)
               then rewrite_atomic term candidate replacement
                 replacement_provenance oriented
               else OccurrenceAbsent
           | UnavailableProvenance reason =>
               if term_has_occurrence candidate term then
                 OccurrenceBlocked
                   ("source occurrence unavailable: " ^ reason)
               else OccurrenceAbsent
           | AmbiguousProvenance reason =>
               if term_has_occurrence candidate term then
                 OccurrenceBlocked
                   ("source occurrence ambiguous: " ^ reason)
               else OccurrenceAbsent)
          handle Feedback.HOL_ERR holerr =>
            OccurrenceBlocked
              ("occurrence traversal failed at " ^
               Library.term_to_string term ^ " [" ^
               provenance_shape provenance ^ "]; " ^
               Feedback.message_of holerr)

      fun expose_step (premise_step : replayed_step) =
        let
          val theorem = step_theorem premise_step
          val preserve_reflexive_occurrence =
            case (Lib.total boolSyntax.dest_eq (Thm.concl theorem),
                  step_provenance premise_step) of
              (SOME (left, right),
               EqualityProvenance
                 (left_provenance, right_provenance)) =>
                Term.aconv left right andalso
                left_provenance <> right_provenance
            | _ => false
          val exposed = if preserve_reflexive_occurrence then theorem
            else expose_true_equality theorem
          val use_exposed = boolSyntax.is_eq (Thm.concl exposed)
          val provenance =
            if not use_exposed then step_provenance premise_step
            else
              (case (Lib.total boolSyntax.dest_eq (Thm.concl theorem),
                     step_provenance premise_step) of
                 (SOME (left, right), EqualityProvenance
                    (left_provenance, right_provenance)) =>
                   if Term.aconv left boolSyntax.T then right_provenance
                   else if Term.aconv right boolSyntax.T then left_provenance
                   else step_provenance premise_step
               | _ => step_provenance premise_step)
        in
          if use_exposed then
            {rule_name = #rule_name premise_step,
             result = exact_result provenance exposed}
          else premise_step
        end

      fun nontrivial (premise_step : replayed_step) =
        if Term.aconv (Thm.concl (step_theorem premise_step))
             boolSyntax.T then false
        else
          let val (left, right) = boolSyntax.dest_eq
            (Thm.concl (step_theorem premise_step))
          in
            not (Term.aconv left right) orelse
            (case step_provenance premise_step of
               EqualityProvenance
                 (left_provenance, right_provenance) =>
                 left_provenance <> right_provenance
             | _ => false)
          end
          handle Feedback.HOL_ERR _ => true

      fun apply_premise
          (premise_step : replayed_step, current : located_term) =
        let
          val theorem = step_theorem premise_step
          val (left, right) = boolSyntax.dest_eq (Thm.concl theorem)
          val (left_provenance, right_provenance) =
            case step_provenance premise_step of
              EqualityProvenance pair => pair
            | UnavailableProvenance reason =>
                raise ERR "cong_provenance"
                  ("congruence equality unavailable: " ^ reason)
            | AmbiguousProvenance reason =>
                raise ERR "cong_provenance"
                  ("congruence equality ambiguous: " ^ reason)
            | _ => raise ERR "cong_provenance"
                "premise lacks equality occurrence provenance"
          fun apply candidate candidate_provenance replacement
              replacement_provenance oriented =
            rewrite_occurrence (#term current) (#provenance current)
              candidate candidate_provenance replacement
              replacement_provenance oriented
        in
          case apply left left_provenance right right_provenance theorem of
            OccurrenceRewritten result =>
              (profile_event "CPC(cong:exact/rewrite)"; result)
          | OccurrenceBlocked reason =>
              raise ERR "cong_provenance"
                ("left occurrence rewrite blocked for " ^
                 Library.term_to_string (Thm.concl theorem) ^ "; " ^
                 reason)
          | OccurrenceAbsent =>
              (case apply right right_provenance left left_provenance
                  (Thm.SYM theorem) of
                 OccurrenceRewritten result =>
                   (profile_event "CPC(cong:exact/rewrite)"; result)
               | OccurrenceBlocked reason =>
                   raise ERR "cong_provenance"
                     ("right occurrence rewrite blocked for " ^
                      Library.term_to_string (Thm.concl theorem) ^ "; " ^
                      reason)
               | OccurrenceAbsent => raise ERR "cong_provenance"
                   ("premise does not rewrite an exact source occurrence; " ^
                    "source=" ^ Library.term_to_string (#term current) ^
                    "; source-provenance=" ^
                    provenance_shape (#provenance current) ^
                    "; premise=" ^
                    Library.term_to_string (Thm.concl theorem) ^
                    "; premise-provenance=" ^
                    provenance_shape (step_provenance premise_step)))
        end

      val rewrite_steps = List.filter nontrivial
        (List.map expose_step premise_steps)
      fun compose (premise_step, (current, accumulated)) =
        let
          val (next, rewrite_theorem) =
            apply_premise (premise_step, current)
          val theorem = Thm.TRANS accumulated rewrite_theorem
            handle Feedback.HOL_ERR holerr =>
              raise ERR "cong_provenance"
                ("exact congruence rewrites do not compose: " ^
                 Feedback.message_of holerr)
        in
          (next, theorem)
        end

      (* Structural CONG visits source occurrences in preorder and consumes
         the first still-live premise matching each node.  Order the exact
         premise applications by that same topology-aware traversal; the
         subsequent rewrite and kernel lifting are still performed by the
         single resolver above, so path selection cannot diverge. *)
      fun structural_step current remaining =
        let
          fun root_match term provenance (_, premise_step) =
            let
              val (left, right) = boolSyntax.dest_eq
                (Thm.concl (step_theorem premise_step))
              val (left_provenance, right_provenance) =
                case step_provenance premise_step of
                  EqualityProvenance pair => pair
                | _ => raise ERR "cong_provenance"
                    "structural congruence premise lacks exact endpoints"
            in
              (Term.aconv term left andalso
               provenance_topology_compatible provenance left_provenance)
              orelse
              (Term.aconv term right andalso
               provenance_topology_compatible provenance right_provenance)
            end
            handle Feedback.HOL_ERR _ => false
          fun atomic_match term (_, premise_step) =
            let
              val (left, right) = boolSyntax.dest_eq
                (Thm.concl (step_theorem premise_step))
              val (left_provenance, right_provenance) =
                case step_provenance premise_step of
                  EqualityProvenance pair => pair
                | _ => raise ERR "cong_provenance"
                    "structural congruence premise lacks exact endpoints"
            in
              (definitely_no_conjunction left_provenance andalso
               definitely_no_conjunction right_provenance) andalso
              (term_has_occurrence left term orelse
               term_has_occurrence right term)
            end
            handle Feedback.HOL_ERR _ => false
          fun first predicate = List.find predicate remaining
          fun descend term provenance =
            case first (root_match term provenance) of
              SOME indexed => SOME indexed
            | NONE =>
                (case provenance of
                   ConjunctionProvenance (_, operands) =>
                     descend_list
                       (split_conjunction (List.length operands) term)
                       operands
                 | EqualityProvenance (left, right) =>
                     let val (left_term, right_term) = boolSyntax.dest_eq term
                     in descend_list [left_term, right_term] [left, right] end
                 | ApplicationProvenance (_, operands) =>
                     let
                       val (operator, arguments) = boolSyntax.strip_comb term
                     in
                       (case first (atomic_match operator) of
                          SOME indexed => SOME indexed
                        | NONE => descend_list arguments operands)
                     end
                 | BinderProvenance (head, body) =>
                     descend (binder_body head term) body
                 | BinderBlockProvenance (head, size, body) =>
                     descend (#2 (dest_binder_block head size term)) body
                 | AtomicProvenance => first (atomic_match term)
                 | UnavailableProvenance _ => NONE
                 | AmbiguousProvenance _ => NONE)
          and descend_list [] [] = NONE
            | descend_list (term :: terms)
                (provenance :: provenances) =
                (case descend term provenance of
                   SOME indexed => SOME indexed
                 | NONE => descend_list terms provenances)
            | descend_list _ _ = NONE
        in
          descend (#term current) (#provenance current)
        end

      fun remove_index wanted entries =
        List.filter (fn (index, _) => index <> wanted) entries

      fun structural_fold current accumulated remaining =
        case remaining of
          [] => (current, accumulated)
        | _ =>
            (case structural_step current remaining of
               NONE => raise ERR "cong_provenance"
                 "structural congruence left an exact premise unused"
             | SOME (index, premise_step) =>
                 let
                   val (next, rewrite_theorem) =
                     apply_premise (premise_step, current)
                   val theorem = Thm.TRANS accumulated rewrite_theorem
                 in
                   structural_fold next theorem
                     (remove_index index remaining)
                 end)

      val indexed_steps = ListPair.zip
        (List.tabulate (List.length rewrite_steps, Lib.I), rewrite_steps)
      val (result, theorem) =
        (structural_fold source (Thm.REFL (#term source)) indexed_steps
         handle Feedback.HOL_ERR structural_error =>
           (List.foldl compose
              (source, Thm.REFL (#term source)) rewrite_steps
            handle Feedback.HOL_ERR sequential_error =>
              raise ERR "cong_provenance"
                ("structural exact route: " ^
                 Feedback.message_of structural_error ^
                 "; sequential exact route: " ^
                 Feedback.message_of sequential_error)))
      val _ =
        case conclusion of
          NONE => ()
        | SOME target =>
            if Term.aconv (Thm.concl theorem) target then ()
            else raise ERR "cong"
              "exact congruence differs from the certificate conclusion"
      val provenance = EqualityProvenance
        (#provenance source, #provenance result)
    in
      exact_result provenance theorem
    end
  (* Discharge [prems] against a theory prover by proving the implication
     they guard, then eliminating them. *)
  fun prove_from_prems prove prems target =
    Drule.LIST_MP prems
      (prove (boolSyntax.list_mk_imp (List.map Thm.concl prems, target)))

  (* Arithmetic procedures normally regard free variables as their atoms, but
     reject some compound terms even when those terms are semantically opaque
     to the certificate step.  Abstract every maximal selected atom uniformly
     across premises and target, prove the resulting implication, and then
     instantiate the fresh variables back.  INST and LIST_MP keep this wholly
     proof-producing; the selector describes a term class, not recorded proof
     shapes. *)
  fun prove_from_prems_abstracting prove is_atom prems target =
    let
      fun insert tm atoms =
        if List.exists (Term.aconv tm) atoms then atoms else tm :: atoms
      fun collect tm atoms =
        if is_atom tm then insert tm atoms
        else
          (case Lib.total Term.dest_comb tm of
             SOME (operator, operand) =>
               collect operand (collect operator atoms)
           | NONE =>
               (case Lib.total Term.dest_abs tm of
                  SOME (_, body) => collect body atoms
                | NONE => atoms))
      val atoms = List.foldl
        (fn (theorem, accumulated) =>
          collect (Thm.concl theorem) accumulated)
        (collect target []) prems
      val _ = List.null atoms andalso
        raise ERR "prove_from_prems_abstracting" "no selected atoms"
      val replacements = List.map
        (fn atom => (Term.genvar (Term.type_of atom), atom)) atoms
      val abstraction = List.map
        (fn (variable, atom) => {redex = atom, residue = variable})
        replacements
      fun abstract tm = Term.subst abstraction tm
      val abstract_implication = boolSyntax.list_mk_imp
        (List.map (abstract o Thm.concl) prems, abstract target)
      val abstract_theorem = prove abstract_implication
        handle Feedback.HOL_ERR holerr =>
          raise ERR "prove_from_prems_abstracting"
            ("could not prove abstract implication " ^
             Library.term_to_string abstract_implication ^ "; " ^
             Feedback.message_of holerr)
      val concrete_theorem = Thm.INST
        (List.map (fn (variable, atom) =>
          {redex = variable, residue = atom}) replacements)
        abstract_theorem
    in
      Drule.LIST_MP prems concrete_theorem
    end

  fun canonical_term target =
    boolSyntax.rhs (Thm.concl (SmtReplayCanon.cpc_canon_conv target))

  fun canonical_operand target = boolSyntax.rhs
    (Thm.concl (SmtReplayCanon.cpc_operand_canon_conv target))

  fun canonical_conclusion conclusion = Option.map canonical_term conclusion

  (* Normalize the certificate conclusion with 'canon', check that the
     replayed result matches it, and map the result back to the conclusion
     the certificate declared.  The aconv check is the security-relevant
     step, so every restoration rung shares this one implementation. *)
  fun restore_with canon what name conclusion theorem =
    case conclusion of
      NONE => theorem
    | SOME target =>
        let
          val target_norm = canon target
          val normalized_target = boolSyntax.rhs (Thm.concl target_norm)
          val _ = Term.aconv (Thm.concl theorem) normalized_target orelse
            raise ERR name
              (what ^ " result differs from the certificate conclusion; " ^
               "result=" ^ Library.term_to_string (Thm.concl theorem) ^
               "; target=" ^ Library.term_to_string normalized_target)
        in
          Thm.EQ_MP (Thm.SYM target_norm) theorem
        end

  val restore_canonical_conclusion =
    restore_with SmtReplayCanon.cpc_canon_conv "canonical"

  fun canonical_premises prems =
    List.map SmtReplayCanon.cpc_canon_rule prems

  (* Transport an occurrence tree through the same canonical conversion used
     by a semantic replay route.  A recorded boundary survives only when
     canonicalizing each child independently produces the corresponding
     child of the route's actual normalized term. *)
  fun align_canonical_provenance canon original normalized provenance =
    let
      fun normalized_term term = boolSyntax.rhs (Thm.concl (canon term))
      fun split_conjunction n term =
        if n = 1 then [term]
        else
          let val (left, right) = boolSyntax.dest_conj term in
            left :: split_conjunction (n - 1) right
          end
      fun aligned_children originals normalizeds provenances =
        if List.length originals <> List.length normalizeds orelse
           List.length originals <> List.length provenances
        then raise ERR "canonical_provenance"
          "canonical occurrence children do not align"
        else ListPair.mapEq
          (fn ((old_term, new_term), child_provenance) =>
            let
              val expected = normalized_term old_term
              val _ = Term.aconv expected new_term orelse
                raise ERR "canonical_provenance"
                  "canonical child differs from the semantic route"
            in
              align_canonical_provenance canon old_term new_term
                child_provenance
            end)
          (ListPair.zip (originals, normalizeds), provenances)
    in
      if Term.aconv original normalized then provenance
      else
        (case provenance of
           ConjunctionProvenance (source, operands) =>
             let
               val n = List.length operands
               val originals = split_conjunction n original
             in
               if n > 1 andalso not (boolSyntax.is_conj normalized) then
                 (* Canonicalization may erase neutral conjuncts.  Retain the
                    one surviving occurrence only when every other child
                    independently normalizes to truth. *)
                 (case List.filter
                     (fn (child, _) =>
                        not (Term.aconv (normalized_term child) boolSyntax.T))
                     (ListPair.zip (originals, operands)) of
                    [(child, occurrence)] =>
                      if Term.aconv (normalized_term child) normalized then
                        align_canonical_provenance canon child normalized
                          occurrence
                      else UnavailableProvenance
                        "canonical surviving conjunct differs from result"
                  | _ => UnavailableProvenance
                      "canonical conjunction lost its occurrence boundary")
               else
                 ConjunctionProvenance
                   (source, aligned_children originals
                     (split_conjunction n normalized) operands)
             end
         | EqualityProvenance (left, right) =>
             let
               val (original_left, original_right) =
                 boolSyntax.dest_eq original
               val (normalized_left, normalized_right) =
                 boolSyntax.dest_eq normalized
               val children =
                 (aligned_children [original_left, original_right]
                    [normalized_left, normalized_right] [left, right]
                  handle Feedback.HOL_ERR _ =>
                    (* cpc_canon_conv may deterministically orient an
                       equality.  Transport the endpoints through that same
                       swap instead of attaching the old order to the new
                       theorem. *)
                    aligned_children [original_right, original_left]
                      [normalized_left, normalized_right] [right, left])
             in
               case children of
                 [left', right'] => EqualityProvenance (left', right')
               | _ => raise ERR "canonical_provenance"
                   "canonical equality children are malformed"
             end
         | ApplicationProvenance (head, operands) =>
             if definitely_no_conjunction provenance andalso
                not (term_contains_conjunction normalized)
             then AtomicProvenance
             else let
               val (original_operator, originals) =
                 boolSyntax.strip_comb original
               val (normalized_operator, normalizeds) =
                 boolSyntax.strip_comb normalized
               val _ = Term.aconv original_operator normalized_operator orelse
                 raise ERR "canonical_provenance"
                   "canonical application operator changed"
             in
               ApplicationProvenance
                 (head, aligned_children originals normalizeds operands)
             end
         | BinderProvenance _ =>
             if definitely_no_conjunction provenance andalso
                not (term_contains_conjunction normalized)
             then AtomicProvenance
             else UnavailableProvenance
               "canonical binder transformation lacks exact child alignment"
         | BinderBlockProvenance (kind, count, body) =>
             let
               val strip =
                 if kind = "forall" then boolSyntax.strip_forall
                 else if kind = "exists" then boolSyntax.strip_exists
                 else if kind = "lambda" then Term.strip_abs
                 else raise ERR "canonical_provenance"
                   "unknown binder-block constructor"
               val (old_binders, old_body) = strip original
               val (new_binders, new_body) = strip normalized
               val _ = List.length old_binders = count andalso
                 List.length new_binders = count andalso
                 ListPair.allEq (fn (old, new) => Term.aconv old new)
                   (old_binders, new_binders) andalso
                 Term.aconv (normalized_term old_body) new_body orelse
                   raise ERR "canonical_provenance"
                     "canonical binder body does not align"
             in
               BinderBlockProvenance (kind, count,
                 align_canonical_provenance canon old_body new_body body)
             end
         | AtomicProvenance =>
             if term_contains_conjunction normalized then
               UnavailableProvenance
                 "canonical atomic occurrence introduced a conjunction"
             else AtomicProvenance
         | UnavailableProvenance reason => UnavailableProvenance reason
         | AmbiguousProvenance reason => AmbiguousProvenance reason)
    end
    handle Feedback.HOL_ERR holerr => UnavailableProvenance
      ("canonical occurrence alignment failed: " ^
       Feedback.message_of holerr)

  (* Relate integer and real atoms before abstracting casts.  The three
     parametric embedding theorems cover equality and both order relations;
     greater-than spellings are already canonicalized to reversed less-than
     relations.  This replaces per-shape relation lifts and works for
     arbitrary linear integer expressions.  Build the rewrite net once. *)
  val cast_arithmetic_canon_conv = SmtReplayCanon.compose
    [SmtReplayCanon.cpc_term_canon_conv,
     Conv.TOP_DEPTH_CONV
       (Rewrite.PURE_REWRITE_CONV
         [Conv.GSYM intrealTheory.real_of_int_11,
          Conv.GSYM intrealTheory.real_of_int_lt,
          Conv.GSYM intrealTheory.real_of_int_le]),
     SmtReplayCanon.cpc_term_canon_conv]

  fun prove_cast_arithmetic prems target =
    let
      (* Push casts through integer arithmetic first, so algebraically related
         casts share one abstract real atom.  Real linear arithmetic then sees
         the polynomial shell, and INST restores the exact division/floor
         terms without assuming anything about them. *)
      val target_normalization = cast_arithmetic_canon_conv target
      val normalized_target =
        boolSyntax.rhs (Thm.concl target_normalization)
      val normalized_prems = List.map
        (Conv.CONV_RULE cast_arithmetic_canon_conv) prems
      val normalized_proof = prove_from_prems_abstracting
        RealField.REAL_ARITH intrealSyntax.is_real_of_int
        normalized_prems normalized_target
    in
      Thm.EQ_MP (Thm.SYM target_normalization) normalized_proof
    end

  (* Neutral arithmetic identities.  PURE_REWRITE_CONV builds its net when
     applied to the theorem list, so these nets are built once at load. *)
  val int_neutral_arithmetic =
    [integerTheory.INT_MUL_LZERO,
     integerTheory.INT_MUL_RZERO,
     integerTheory.INT_ADD_LID,
     integerTheory.INT_ADD_RID]

  val int_neutral_arithmetic_conv =
    Rewrite.PURE_REWRITE_CONV int_neutral_arithmetic

  val neutral_arithmetic_conv = Rewrite.PURE_REWRITE_CONV
    (int_neutral_arithmetic @
     [realTheory.REAL_MUL_LZERO,
      realTheory.REAL_MUL_RZERO,
      realTheory.REAL_ADD_LID,
      realTheory.REAL_ADD_RID])

  val ground_neutral_arithmetic_conv = Rewrite.PURE_REWRITE_CONV
    [integerTheory.INT_MUL_RZERO,
     integerTheory.INT_ADD_LID,
     integerTheory.INT_ADD_RID]

  (* cvc5 alternates between these definitionally equal integer spellings
     inside congruence sources and equality endpoints.  Keep one recursive,
     kernel-checked view so both terms follow the same semantic route. *)
  val cpc_integer_spelling_conv = Conv.QCONV
    (Rewrite.PURE_REWRITE_CONV
      [Conv.GSYM integerTheory.INT_NEG_LMUL,
       integerTheory.INT_MUL_LID,
       integerTheory.INT_LT_LE1,
       integerTheory.INT_GE,
       integerTheory.INT_ADD_LID,
       (* CPC rules may expose HOL's Euclidean operators after the
          translation-derived totalization identity has been consumed.
          These are representation aliases, not emitted constants. *)
       integerTheory.EDIV_DEF,
       integerTheory.EMOD_DEF])

  fun compose_normal_form_conv first second tm =
    let
      val canonical = first tm
      val canonical_tm = boolSyntax.rhs (Thm.concl canonical)
      val normalized = second canonical_tm
    in
      Thm.TRANS canonical normalized
    end

  val cpc_integer_normal_form_conv = compose_normal_form_conv
    SmtReplayCanon.cpc_canon_conv cpc_integer_spelling_conv

  (* CPC's total-division bounds theorem contains positive- and
     negative-divisor implications.  Ground divisor guards are semantic
     arithmetic, not definition unfolding; normalize them in their own rung
     so an omitted-conclusion EQ_RESOLVE need not weaken strong provenance. *)
  val cpc_ground_arithmetic_guard_conv = Conv.QCONV
    (bossLib.SIMP_CONV (bossLib.srw_ss ()) [])

  (* The only definition identities in the strong canonicalizer come from
     this proof's emitted-symbol records.  Build the rewrite net from that
     closed table, and record consumption only when one of its definitions
     actually changes the term. *)
  fun strong_cpc_canon_conv definitions =
    let
      val definition_identities =
        List.map SmtLib.emitted_definition_theorem definitions
      val definition_heads =
        List.map SmtLib.emitted_definition_head definitions
      val definition_conv =
        Rewrite.PURE_REWRITE_CONV definition_identities
      fun is_enabled head =
        List.exists (Term.same_const head) definition_heads
      fun contains_head head term =
        Lib.can (HolKernel.find_term (fn candidate =>
          Term.is_const candidate andalso
          Term.same_const candidate head)) term
      fun count_head head term =
        List.length (HolKernel.find_terms (fn candidate =>
          Term.is_const candidate andalso
          Term.same_const candidate head) term)
      fun unkeyed_heads term = List.mapPartial
        (fn ({replay_head, ...} : SmtLib.emitted_definition_spec) =>
          if not (is_enabled replay_head) andalso
             contains_head replay_head term then
            SOME (replay_head, count_head replay_head term)
          else NONE)
        (SmtLib.all_emitted_definition_specs ())
      fun require_unkeyed_heads_preserved heads term =
        if List.all (fn (head, count) => count_head head term = count)
            heads then ()
        else raise ERR "strong_cpc_canon_conv"
          "conversion changed an un-emitted replay head"
      fun unfold_emitted_definition current =
        let
          val theorem = definition_conv current
          val normalized = boolSyntax.rhs (Thm.concl theorem)
          val _ = not (Term.aconv current normalized) orelse
            raise Conv.UNCHANGED
          val () = profile_event "CPC(canon:translator-definition)"
        in theorem end
      fun finish current =
        if not (Term.has_free_vars current) then
          bossLib.SIMP_CONV (bossLib.srw_ss ())
            [HolSmtTheory.smt_rdiv_eq_div,
             intrealTheory.INT_FLOOR] current
        else bossLib.SIMP_CONV (bossLib.srw_ss ()) [] current
      fun arithmetic_decision current =
        let
          val normalization =
            SmtReplayCanon.arith_poly_norm_conversion current
          val normalized = boolSyntax.rhs (Thm.concl normalization)
          val decision =
            Drule.EQT_INTRO
              (simpLib.SIMP_PROVE (bossLib.srw_ss ())
                [] normalized)
            handle Feedback.HOL_ERR _ =>
              Drule.EQF_INTRO
                (simpLib.SIMP_PROVE (bossLib.srw_ss ())
                  []
                  (boolSyntax.mk_neg normalized))
        in
          Thm.TRANS normalization decision
        end
        handle Feedback.HOL_ERR _ => raise Conv.UNCHANGED
             | Conv.UNCHANGED => raise Conv.UNCHANGED
      fun convert tm =
        let
          (* A CPC rule may introduce an auxiliary total operator (notably
             div_total in mod_total bounds) that the original translation
             did not emit.  Without the matching record, canonicalization
             must preserve its exact occurrence count. *)
          val unkeyed = unkeyed_heads tm
          (* This is a canonicalizer, so an already-canonical term is a
             successful reflexive result. *)
          val theorem = Conv.QCONV (SmtReplayCanon.compose
              [unfold_emitted_definition,
               SmtReplayCanon.cpc_operand_canon_conv,
               cpc_integer_spelling_conv,
               wordsLib.WORD_LOGIC_CONV,
               finish, arithmetic_decision]) tm
          val normalized = boolSyntax.rhs (Thm.concl theorem)
          val () = require_unkeyed_heads_preserved unkeyed normalized
        in
          theorem
        end
    in
      convert
    end

  fun restore_strong_canonical_conclusion canon name conclusion theorem =
    restore_with canon "strong canonical" name conclusion
      (Conv.CONV_RULE canon theorem)

  (* Canonicalization can discharge a premise completely.  Such a proof is
     logically neutral in the surrounding chain, but its hypotheses must
     still contribute to the result; a kernel conjunction projection carries
     them without depending on the premise's solver-specific spelling. *)
  fun retain_support kept support = Thm.CONJUNCT1 (Thm.CONJ kept support)

  fun retain_all theorem supports =
    List.foldl (fn (support, kept) => retain_support kept support)
      theorem supports

  fun is_reflexive_equality theorem =
    case Lib.total dest_reglan_equiv (Thm.concl theorem) of
      SOME (left, right) => Term.aconv left right
    | NONE =>
        (case Lib.total boolSyntax.dest_eq (Thm.concl theorem) of
           SOME (left, right) => Term.aconv left right
         | NONE => false)

  fun is_reflexive_boolean_equality theorem =
    case Lib.total boolSyntax.dest_eq (Thm.concl theorem) of
      SOME (left, right) =>
        Type.compare (Term.type_of left, Type.bool) = EQUAL andalso
        Term.aconv left right
    | NONE => false

  (* Canonicalization changes only sharing and binder names.  The kernel's
     DAG-aware ALPHA rule checks that exact invariant at the endpoints;
     rebuilding a second congruence theorem at every descendant is redundant.
     The parser interner supplies a candidate, never an equality oracle. *)
  fun canonical_term_conv root =
    let val canonical = CPC_ProofParser.intern_cpc_term root in
      if Portable.pointer_eq (root, canonical) then Thm.REFL root
      else Thm.ALPHA root canonical
    end

  fun replay_trans prems =
    case prems of
      [] => raise ERR "trans" "expected CPC equality premises"
    | first :: rest =>
        if is_reglan_equiv (Thm.concl first) then
          List.foldl (fn (next, accumulated) =>
            replay_reglan_trans accumulated next) first rest
        else
        let
          fun attempt work = SOME (work ()) handle Feedback.HOL_ERR _ => NONE
          fun compose th accumulated =
            if Term.aconv (Thm.concl accumulated) boolSyntax.T then
              retain_support accumulated th
            else if Term.aconv (Thm.concl th) boolSyntax.T then
              retain_support th accumulated
            else if is_reflexive_equality accumulated then
              retain_support th accumulated
            else if is_reflexive_equality th then
              retain_support accumulated th
            else case attempt (fn () => Thm.TRANS accumulated th) of
              SOME result => result
            | NONE =>
              (case attempt (fn () => Thm.TRANS accumulated (Thm.SYM th)) of
                 SOME result => result
               | NONE =>
                 (case attempt (fn () => Thm.TRANS (Thm.SYM accumulated) th) of
                    SOME result => result
                  | NONE =>
                    (case attempt
                        (fn () =>
                          Thm.TRANS (Thm.SYM accumulated) (Thm.SYM th)) of
                       SOME result => result
                     | NONE => raise ERR "trans"
                         ("canonical CPC equality premises do not compose; " ^
                          "first=" ^ Library.thm_to_string accumulated ^
                          "; next=" ^ Library.thm_to_string th))))
        in
          List.foldl (fn (th, accumulated) => compose th accumulated)
            first rest
        end

  fun equality_endpoint side provenance =
    case provenance of
      EqualityProvenance (left, right) => if side = 0 then left else right
    | UnavailableProvenance reason => UnavailableProvenance
        ("trans equality endpoint unavailable: " ^ reason)
    | AmbiguousProvenance reason => AmbiguousProvenance
        ("trans equality endpoint ambiguous: " ^ reason)
    | _ => UnavailableProvenance
        "trans premise lacks equality occurrence provenance"

  (* A translated equality can be a purely propositional identity rather
     than the bridge between the neighboring equality endpoints.  Recognize
     such identities with a deliberately bounded kernel proof, so TRANS does
     not have to normalize an increasingly shared Boolean context merely to
     discover that the premise is logically neutral. *)
  fun bounded_propositional_tautology theorem =
    let
      val goal = Thm.concl theorem
      val node_limit = 256
      val atom_limit = 16
      val nodes = ref 0
      val atoms = ref ([] : Term.term list)
      fun add_atom term =
        if List.exists (fn saved => Term.aconv saved term) (!atoms) then ()
        else if List.length (!atoms) >= atom_limit then
          raise ERR "trans" "propositional neutral atom bound exceeded"
        else atoms := term :: !atoms
      fun visit term =
        let
          val _ = nodes := !nodes + 1
          val _ = !nodes <= node_limit orelse
            raise ERR "trans" "propositional neutral node bound exceeded"
        in
          if Term.aconv term boolSyntax.T orelse
             Term.aconv term boolSyntax.F then ()
          else if boolSyntax.is_neg term then
            visit (boolSyntax.dest_neg term)
          else if boolSyntax.is_conj term then
            let val (left, right) = boolSyntax.dest_conj term
            in visit left; visit right end
          else if boolSyntax.is_disj term then
            let val (left, right) = boolSyntax.dest_disj term
            in visit left; visit right end
          else if boolSyntax.is_imp term then
            let val (left, right) = boolSyntax.dest_imp term
            in visit left; visit right end
          else if boolSyntax.is_eq term andalso
                  Type.compare
                    (Term.type_of (boolSyntax.lhs term), Type.bool) = EQUAL
          then
            let val (left, right) = boolSyntax.dest_eq term
            in visit left; visit right end
          else add_atom term
        end
      val _ = visit goal
      val _ = tautLib.TAUT_PROVE goal
    in true end
    handle Feedback.HOL_ERR _ => false

  fun replay_trans_with_provenance
      (premise_steps : replayed_step list) =
    let
      fun attempt work = SOME (work ()) handle Feedback.HOL_ERR _ => NONE
      fun compose (next_step, (accumulated, accumulated_provenance)) =
        let
          val next = step_theorem next_step
          val next_provenance = step_provenance next_step
          fun endpoints accumulated_side next_side theorem =
            let
              val (left, right) = boolSyntax.dest_eq (Thm.concl theorem)
              fun exact_if_conjunction_free term provenance =
                case provenance of
                  UnavailableProvenance reason =>
                    conjunction_free_semantic_provenance reason term
                | AmbiguousProvenance reason =>
                    conjunction_free_semantic_provenance reason term
                | exact => exact
            in
              (theorem, EqualityProvenance
                (exact_if_conjunction_free left
                   (equality_endpoint accumulated_side
                     accumulated_provenance),
                 exact_if_conjunction_free right
                   (equality_endpoint next_side next_provenance)))
            end
        in
          if Term.aconv (Thm.concl accumulated) boolSyntax.T then
            (retain_support accumulated next, next_provenance)
          else if Term.aconv (Thm.concl next) boolSyntax.T then
            (retain_support next accumulated, accumulated_provenance)
          else if is_reflexive_equality accumulated then
            (retain_support next accumulated, next_provenance)
          else if is_reflexive_equality next then
            (retain_support accumulated next, accumulated_provenance)
          else
            case attempt (fn () => endpoints 0 1
                (Thm.TRANS accumulated next)) of
              SOME result => result
            | NONE =>
                (case attempt (fn () => endpoints 0 0
                    (Thm.TRANS accumulated (Thm.SYM next))) of
                   SOME result => result
                 | NONE =>
                     (case attempt (fn () => endpoints 1 1
                         (Thm.TRANS (Thm.SYM accumulated) next)) of
                        SOME result => result
                      | NONE =>
                          (case attempt (fn () => endpoints 1 0
                              (Thm.TRANS (Thm.SYM accumulated)
                                (Thm.SYM next))) of
                             SOME result => result
                           | NONE =>
                               if bounded_propositional_tautology
                                    accumulated then
                                 (retain_support next accumulated,
                                  next_provenance)
                               else if bounded_propositional_tautology next
                               then
                                 (retain_support accumulated next,
                                  accumulated_provenance)
                               else raise ERR "trans"
                                 "equality premises do not compose")))
        end
    in
      case premise_steps of
        [] => raise ERR "trans" "expected CPC equality premises"
      | first :: rest => List.foldl compose
          (step_theorem first, step_provenance first) rest
    end

  (* Use canonical forms to recognize tautological support premises without
     replacing the theorem stored for the CPC step.  Later rules can depend
     on its exact shape (notably TRUE_ELIM consuming [T = p]). *)
  fun replay_canonical_trans strong_canon prems =
    let
      (* E1(b): this terminal is the general canonical-form procedure for
         CPC trans.  It derives totalization identities from this proof's
         emitted-symbol table and otherwise uses only general canonical
         conversions.  It is coverage-bearing, so it is never a fast path. *)
      fun canonical_view theorem = expose_true_equality
        (Conv.CONV_RULE (Conv.BINOP_CONV strong_canon) theorem)
        handle Feedback.HOL_ERR _ => theorem
             | Conv.UNCHANGED => theorem
      fun compose (next, accumulated) =
        (* A non-reflexive equality may normalize to [T] or [x = x], but
           it is still the bridge to the next endpoint in a TRANS chain.
           Only an originally reflexive theorem is neutral. *)
        if is_reflexive_equality accumulated then
          retain_support next accumulated
        else if is_reflexive_equality next then
          retain_support accumulated next
        else
          profile "CPC(rung:canonical_trans/canonical)" (fn () =>
            replay_trans
              [canonical_view accumulated, canonical_view next]) ()
    in
      case prems of
        [] => raise ERR "trans" "expected CPC equality premises"
      | first :: rest => List.foldl compose first rest
    end

  fun replay_canonical_trans_with_provenance strong_canon
      (premise_steps : replayed_step list) =
    let
      fun try work fallback =
        work () handle Feedback.HOL_ERR _ => fallback ()
                      | Conv.UNCHANGED => fallback ()
      fun compose (next_step, accumulated_result) =
        let
          val (accumulated, accumulated_provenance) = accumulated_result
          val next_result =
            (step_theorem next_step, step_provenance next_step)
          val (next, next_provenance) = next_result
          (* Canonicalize only the two candidate middle endpoints, prove the
             bridge between those exact terms, and compose the unmodified
             oriented premise theorems around it.  Whole-equality conversion
             can collapse a non-reflexive CPC bridge to T and lose which
             outer endpoint this TRANS route selected. *)
          fun canonical_bridge accumulated_side next_side =
            let
              val accumulated' = if accumulated_side = 1 then accumulated
                else Thm.SYM accumulated
              val next' = if next_side = 0 then next else Thm.SYM next
              val (_, middle_left) = boolSyntax.dest_eq
                (Thm.concl accumulated')
              val (middle_right, _) = boolSyntax.dest_eq (Thm.concl next')
              fun extend conv theorem =
                let
                  val current = boolSyntax.rhs (Thm.concl theorem)
                  val refinement = Conv.QCONV conv current
                in
                  Thm.TRANS theorem refinement
                end
              fun finish left_norm right_norm =
                let
                  val bridge = Thm.TRANS left_norm (Thm.SYM right_norm)
                  val theorem = Thm.TRANS accumulated'
                    (Thm.TRANS bridge next')
                  val provenance = EqualityProvenance
                    (equality_endpoint (1 - accumulated_side)
                       accumulated_provenance,
                     equality_endpoint (1 - next_side) next_provenance)
                in
                  (theorem, provenance)
                end
              fun refine [] _ = raise ERR "trans"
                    "canonical middle endpoints have distinct normal forms"
                | refine (conv :: rest) (left_norm, right_norm) =
                    let
                      val left_norm' = extend conv left_norm
                      val right_norm' = extend conv right_norm
                      val normalized_left = boolSyntax.rhs
                        (Thm.concl left_norm')
                      val normalized_right = boolSyntax.rhs
                        (Thm.concl right_norm')
                    in
                      if Term.aconv normalized_left normalized_right then
                        finish left_norm' right_norm'
                      else refine rest (left_norm', right_norm')
                    end
            in
              refine
                [SmtReplayCanon.cpc_canon_conv,
                 cpc_integer_spelling_conv,
                 strong_canon,
                 SmtReplayCanon.reorient_equality_conv]
                (Thm.REFL middle_left, Thm.REFL middle_right)
            end
          fun canonical_orientations () =
            try (fn () => canonical_bridge 1 0) (fn () =>
              try (fn () => canonical_bridge 1 1) (fn () =>
                try (fn () => canonical_bridge 0 0) (fn () =>
                  canonical_bridge 0 1)))
        in
          if is_reflexive_equality accumulated then
            (retain_support next accumulated, next_provenance)
          else if is_reflexive_equality next then
            (retain_support accumulated next, accumulated_provenance)
          else
            (* E1(b) general terminal.  Its deterministic normal-form
               procedure accumulates kernel equalities through the shared
               CPC and integer-spelling phases, the table-derived strong
               phase, and a final equality orientation.  An earlier match is
               a completed canonical comparison, not an optional cache route.
               The original endpoint theorems and provenance remain
               unchanged. *)
            profile
              "CPC(rung:canonical_trans/provenance-canonical)"
              canonical_orientations ()
        end
    in
      case premise_steps of
        [] => raise ERR "trans" "expected CPC equality premises"
      | first :: rest => List.foldl compose
          (step_theorem first, step_provenance first) rest
    end

  fun replay_eq_resolve prems =
    let
    in case prems of
      [left, right] =>
        if Term.aconv (Thm.concl left) boolSyntax.F then left
        else if Term.aconv (Thm.concl right) boolSyntax.F then right
        else if is_reflexive_boolean_equality right then
          retain_support left right
        else if is_reflexive_boolean_equality left then
          retain_support right left
        else
          (Thm.EQ_MP right left
           handle Feedback.HOL_ERR _ =>
             (Thm.EQ_MP (Thm.SYM right) left
              handle Feedback.HOL_ERR _ =>
                (Thm.EQ_MP left right
                handle Feedback.HOL_ERR _ =>
                  (Thm.EQ_MP (Thm.SYM left) right
                   handle Feedback.HOL_ERR _ =>
                     raise ERR "eq_resolve"
                       ("canonical premises do not rewrite one another; " ^
                        "left=" ^
                       Library.term_to_string (Thm.concl left) ^
                       "; right=" ^
                       Library.term_to_string (Thm.concl right))))))
    | _ => raise ERR "eq_resolve" "expected two CPC premises"
    end

  fun eq_resolve_result_provenance provenance =
    case provenance of
      ConjunctionProvenance (_, operands) =>
        ConjunctionProvenance (EqResolveConjunction, operands)
    | other => other

  fun equality_side_provenance side provenance =
    case provenance of
      EqualityProvenance (left, right) =>
        eq_resolve_result_provenance
          (if side = 0 then left else right)
    | UnavailableProvenance reason => UnavailableProvenance
        ("eq_resolve equality-side provenance unavailable: " ^ reason)
    | AmbiguousProvenance reason => AmbiguousProvenance
        ("eq_resolve equality-side provenance ambiguous: " ^ reason)
    | _ => UnavailableProvenance
        "eq_resolve premise lacks equality occurrence provenance"

  (* Mirror the kernel EQ_MP orientation exactly.  This is semantic
     propagation from the equality side actually selected, not a lookup by
     the result term. *)
  fun replay_eq_resolve_with_provenance
      ([left_step, right_step] : replayed_step list) =
    let
      val left = step_theorem left_step
      val right = step_theorem right_step
      fun occurrence_reflexive step =
        case step_provenance step of
          EqualityProvenance (left, right) => left = right
        | _ => true
    in
      if Term.aconv (Thm.concl left) boolSyntax.F then
        (left, step_provenance left_step)
      else if Term.aconv (Thm.concl right) boolSyntax.F then
        (right, step_provenance right_step)
      else if is_reflexive_boolean_equality right andalso
              occurrence_reflexive right_step then
        (retain_support left right, step_provenance left_step)
      else if is_reflexive_boolean_equality left andalso
              occurrence_reflexive left_step then
        (retain_support right left, step_provenance right_step)
      else
        ((Thm.EQ_MP right left,
          equality_side_provenance 1 (step_provenance right_step))
         handle Feedback.HOL_ERR _ =>
           ((Thm.EQ_MP (Thm.SYM right) left,
             equality_side_provenance 0 (step_provenance right_step))
            handle Feedback.HOL_ERR _ =>
              ((Thm.EQ_MP left right,
                equality_side_provenance 1 (step_provenance left_step))
               handle Feedback.HOL_ERR _ =>
                 (Thm.EQ_MP (Thm.SYM left) right,
                  equality_side_provenance 0
                    (step_provenance left_step)))))
    end
    | replay_eq_resolve_with_provenance _ =
        raise ERR "eq_resolve" "expected two CPC premises"

  (* EQ_RESOLVE sometimes connects propositions only after datatype/record
     canonicalization.  Keep the conversion equalities so the normalized
     proposition can be transported back to the exact side consumed by
     EQ_MP; normalizing both premise theorems would discard that link. *)
  fun replay_canonical_eq_resolve strong_canon prems =
    let
      fun attempt work = SOME (work ()) handle Feedback.HOL_ERR _ => NONE
      fun stage name work =
        work () handle Feedback.HOL_ERR holerr =>
          raise ERR "eq_resolve"
            (name ^ " failed: " ^ Feedback.message_of holerr)
      fun resolve canon proposition equality =
        let
          val (left, right) = stage "equality decomposition"
            (fn () => boolSyntax.dest_eq (Thm.concl equality))
          val proposition_norm =
            stage "proposition canonicalization" (fn () =>
              canon (Thm.concl proposition))
          val normalized_proposition =
            stage "normalized proposition extraction" (fn () =>
              boolSyntax.rhs (Thm.concl proposition_norm))
          val normalized_proof = stage "proposition transport" (fn () =>
            Thm.EQ_MP proposition_norm proposition)
          fun prove_side side =
            let
              val side_norm = canon side
              val normalized_side = boolSyntax.rhs (Thm.concl side_norm)
              val _ = Term.aconv normalized_proposition normalized_side orelse
                raise ERR "eq_resolve"
                  ("canonical proposition does not match equality side; " ^
                   "proposition=" ^
                   Library.term_to_string normalized_proposition ^
                   "; side=" ^ Library.term_to_string normalized_side)
            in
              Thm.EQ_MP (Thm.SYM side_norm) normalized_proof
            end
        in
          case attempt (fn () => Thm.EQ_MP equality (prove_side left)) of
            SOME theorem => theorem
          | NONE => Thm.EQ_MP (Thm.SYM equality) (prove_side right)
        end
    in
      case prems of
        [proposition, equality] =>
          (resolve SmtReplayCanon.cpc_operand_canon_conv
           proposition equality
           handle Feedback.HOL_ERR _ =>
             (resolve cpc_integer_normal_form_conv proposition equality
              handle Feedback.HOL_ERR _ =>
                (resolve cpc_ground_arithmetic_guard_conv
                   proposition equality
                 handle Feedback.HOL_ERR _ =>
                   resolve strong_canon proposition equality)))
      | _ => raise ERR "eq_resolve" "expected two CPC premises"
    end

  fun replay_canonical_eq_resolve_with_provenance canon
      ([proposition_step, equality_step] : replayed_step list) =
    let
      val proposition = step_theorem proposition_step
      val equality = step_theorem equality_step
      val (left, right) = boolSyntax.dest_eq (Thm.concl equality)
      val proposition_norm = canon (Thm.concl proposition)
      val normalized_proposition = boolSyntax.rhs
        (Thm.concl proposition_norm)
      val normalized_proof = Thm.EQ_MP proposition_norm proposition
      fun prove_side side =
        let
          val side_norm = canon side
          val normalized_side = boolSyntax.rhs (Thm.concl side_norm)
          val _ = Term.aconv normalized_proposition normalized_side orelse
            raise ERR "eq_resolve"
              "canonical proposition does not match equality side"
        in
          Thm.EQ_MP (Thm.SYM side_norm) normalized_proof
        end
    in
      ((Thm.EQ_MP equality (prove_side left),
        equality_side_provenance 1 (step_provenance equality_step))
       handle Feedback.HOL_ERR _ =>
         (Thm.EQ_MP (Thm.SYM equality) (prove_side right),
          equality_side_provenance 0 (step_provenance equality_step)))
    end
    | replay_canonical_eq_resolve_with_provenance _ _ =
        raise ERR "eq_resolve" "expected two CPC premises"
  (* cvc5's SYMM rule also preserves the negation of an equality.  HOL's
     Thm.SYM covers the equality form directly; derive the disequality form
     from the same premise rather than treating it as a trusted rewrite. *)
  fun replay_symm prems =
    let
      val premise = expect_one_premise "symm" prems
    in
      (if is_reglan_equiv (Thm.concl premise) then
         replay_reglan_sym premise
       else case Lib.total boolSyntax.dest_neg (Thm.concl premise) of
         SOME relation =>
           if is_reglan_equiv relation then
             let
               val (left, right) = dest_reglan_equiv relation
               val target = boolSyntax.mk_neg
                 (Term.list_mk_comb (reglan_equiv_tm, [right, left]))
             in
               metis_prove
                 [premise, smtstringTheory.reglan_equiv_sym] target
             end
           else Thm.SYM premise
       | NONE => Thm.SYM premise)
      handle Feedback.HOL_ERR _ =>
        let
          val (left, right) = boolSyntax.dest_eq
            (boolSyntax.dest_neg (Thm.concl premise))
        in metis_prove [premise]
          (boolSyntax.mk_neg (boolSyntax.mk_eq (right, left))) end
    end

  fun replay_symm_result ([premise_step] : replayed_step list) =
    let
      val premise = step_theorem premise_step
    in
      (let
         val theorem = Thm.SYM premise
         val provenance =
           case step_provenance premise_step of
             EqualityProvenance (left, right) =>
               EqualityProvenance (right, left)
           | UnavailableProvenance reason => UnavailableProvenance
               ("symm equality endpoints unavailable: " ^ reason)
           | AmbiguousProvenance reason => AmbiguousProvenance
               ("symm equality endpoints ambiguous: " ^ reason)
           | _ => UnavailableProvenance
               "symm premise lacks equality occurrence provenance"
       in
         exact_result provenance theorem
       end
       handle Feedback.HOL_ERR _ => unavailable_result
         "symm used disequality reconstruction without equality endpoints"
         (replay_symm [premise]))
    end
    | replay_symm_result _ =
        raise ERR "symm" "expected exactly one CPC premise"

  fun replay_contra prems =
    case prems of
      [left, right] =>
        if Term.aconv (Thm.concl left) boolSyntax.F then left
        else if Term.aconv (Thm.concl right) boolSyntax.F then right
        else Library.gen_contradiction (Thm.CONJ left right)
    | _ => raise ERR "contra" "expected a proposition and its negation"
  fun replay_false_intro prems =
    Drule.EQF_INTRO (expect_one_premise "false_intro" prems)

  fun replay_false_elim prems =
    Drule.EQF_ELIM (expect_one_premise "false_elim" prems)

  fun replay_true_elim prems =
    let
      val premise = expect_one_premise "true_elim" prems
      val conclusion = Thm.concl premise
      (* A conclusion-less CPC TRANS can preserve a Boolean normal form at
         an endpoint, rather than the literal [true] named by CVC's internal
         term.  Reconstruct its truth structurally.  This is deliberately
         not a general simplifier: normal-form connectives are rebuilt by
         kernel inferences and leaves must be reflexive equalities. *)
      fun prove_true_normal_form term =
        let
          val _ = SmtResource.check_dag_size_for "Skeleton"
            "cpc-true-elim-normalization"
            (SmtResource.dag_nodes_up_to
              (SmtResource.max_skeleton_replay_dag_nodes + 1) term)
          fun prove term =
            if Term.aconv term boolSyntax.T then boolTheory.TRUTH
            else
              case Lib.total boolSyntax.dest_conj term of
                SOME (left, right) => Thm.CONJ (prove left) (prove right)
              | NONE =>
                  (case Lib.total boolSyntax.dest_disj term of
                     SOME (left, right) =>
                       (Thm.DISJ1 (prove left) right
                        handle Feedback.HOL_ERR _ =>
                          Thm.DISJ2 left (prove right))
                   | NONE =>
                       (case Lib.total boolSyntax.dest_imp term of
                          SOME (left, right) => Thm.DISCH left (prove right)
                        | NONE =>
                            let val (left, right) = boolSyntax.dest_eq term in
                              if Term.aconv left right then Thm.REFL left
                              else if Type.compare
                                  (Term.type_of left, Type.bool) = EQUAL then
                                Thm.TRANS (Drule.EQT_INTRO (prove left))
                                  (Thm.SYM
                                    (Drule.EQT_INTRO (prove right)))
                              else raise ERR "true_elim"
                                "Boolean normal form has a non-reflexive leaf"
                            end))
          val theorem = SmtResource.with_resource_step_time "Skeleton"
            "cpc-true-elim-normalization" prove term
        in theorem
        end
    in
      if Term.aconv conclusion boolSyntax.T then premise
      else
        let val (left, right) = boolSyntax.dest_eq conclusion in
          (* CPC [true_elim] removes either orientation of an equality with
             truth.  HOL's [EQT_ELIM] has one orientation, so normalize the
             checked equality first rather than relying on certificate
             orientation. *)
          if Term.aconv right boolSyntax.T then Drule.EQT_ELIM premise
          else if Term.aconv left boolSyntax.T then
            Drule.EQT_ELIM (Thm.SYM premise)
          else
            (* Congruence and transitivity can leave an evaluable Boolean
               normal form in place of CPC's literal [true].  Establish that
               normal form by its checked Boolean structure before eliminating
               it. *)
            (Thm.EQ_MP (Thm.SYM premise) (prove_true_normal_form right)
             handle Feedback.HOL_ERR _ =>
               Thm.EQ_MP premise (prove_true_normal_form left))
        end
    end

  fun replay_true_elim_result ([premise_step] : replayed_step list) =
    let
      val premise = step_theorem premise_step
      val theorem = replay_true_elim [premise]
      val provenance =
        if Term.aconv (Thm.concl premise) boolSyntax.T then
          step_provenance premise_step
        else
          let
            val (left, right) = boolSyntax.dest_eq (Thm.concl premise)
            val result = Thm.concl theorem
          in
            case step_provenance premise_step of
              EqualityProvenance (left_provenance, right_provenance) =>
                if Term.aconv left boolSyntax.T andalso
                   Term.aconv right result then right_provenance
                else if Term.aconv right boolSyntax.T andalso
                        Term.aconv left result then left_provenance
                else UnavailableProvenance
                  "true_elim equality sides do not identify its result"
            | provenance => provenance
          end
          handle Feedback.HOL_ERR _ => UnavailableProvenance
            "true_elim premise lacks equality occurrence provenance"
    in exact_result provenance theorem end
    | replay_true_elim_result _ =
        raise ERR "true_elim" "expected exactly one CPC premise"

  fun replay_true_intro prems =
    Drule.EQT_INTRO (expect_one_premise "true_intro" prems)

  fun replay_evaluate conclusion args =
    let val arg = expect_one_arg "evaluate" args
        val th = bossLib.EVAL arg
    in
      case conclusion of
        NONE => th
      | SOME target =>
          if Term.aconv (Thm.concl th) target then th
          else raise ERR "evaluate"
            "CPC evaluate result differs from its declared conclusion"
    end

  fun conjunction_source_name ParsedConjunction = "parsed"
    | conjunction_source_name AndIntroConjunction = "and_intro"
    | conjunction_source_name ArithReductionConjunction =
        "arith_reduction"
    | conjunction_source_name EqResolveConjunction = "eq_resolve"
    | conjunction_source_name CongruenceConjunction = "congruence"

  fun replay_and_elim conclusion args (premise_step : replayed_step) =
    let
      val premise = step_theorem premise_step
      val conjunction = Thm.concl premise
      val index =
        Arbnum.toInt (numSyntax.dest_numeral (intSyntax.dest_injected
          (expect_one_arg "and_elim" args)))
      fun split n term =
        if n = 1 then [term]
        else if n > 1 then
            let val (left, right) = boolSyntax.dest_conj term in
              left :: split (n - 1) right
            end
        else raise ERR "and_elim"
            "CPC conjunction provenance arity must be positive"
      fun recover_without_provenance provenance =
        let
          val conjunct = List.nth (right_associated_conjuncts conjunction,
                                   index)
            handle Feedback.HOL_ERR _ => raise ERR "and_elim"
              ("CPC and_elim premise has no recoverable conjunction: " ^
               provenance_shape provenance)
              | Subscript => raise ERR "and_elim"
              ("CPC conjunction index " ^ Int.toString index ^
               " is outside the recovered arity for premise " ^
               Library.term_to_string conjunction)
          val theorem = Library.conj_elim (premise, conjunct)
          val _ = profile_event "CPC(and_elim:recovered)"
        in (theorem,
            recovered_checked_provenance
              "and_elim selected an operand after metadata compaction"
              conjunct)
        end
      fun replay_with_provenance (source, conjunct_provenances) =
        let
          val arity = List.length conjunct_provenances
          val _ = arity >= 2 orelse raise ERR "and_elim"
            "CPC and_elim conjunction provenance has fewer than two operands"
          val conjuncts = split arity conjunction
            handle Feedback.HOL_ERR _ => raise ERR "and_elim"
              ("CPC conjunction provenance arity " ^ Int.toString arity ^
               " does not match premise " ^
               Library.term_to_string conjunction)
          val conjunct = List.nth (conjuncts, index)
            handle Subscript => raise ERR "and_elim"
              ("CPC conjunction index " ^ Int.toString index ^
               " is outside parsed arity " ^ Int.toString arity ^
               " for premise " ^ Library.term_to_string conjunction)
          val selected_provenance = List.nth (conjunct_provenances, index)
            handle Subscript => raise ERR "and_elim"
              ("CPC conjunction provenance index " ^ Int.toString index ^
               " is outside arity " ^ Int.toString arity)
          val _ = profile_event ("CPC(and_elim:provenance/" ^
            conjunction_source_name source ^ ")")
        in (Library.conj_elim (premise, conjunct), selected_provenance) end
      val (theorem, provenance) =
        case step_provenance premise_step of
          ConjunctionProvenance pair => replay_with_provenance pair
        | unavailable => recover_without_provenance unavailable
      val _ = case conclusion of
          NONE => ()
        | SOME target =>
            if Term.aconv target (Thm.concl theorem) then ()
            else raise ERR "and_elim"
              "declared CPC result differs from its indexed conjunct"
    in
      (theorem, provenance)
    end

  fun tautology name target =
    profile "CPC(rung:rewrite/METIS)" Tactical.TAC_PROOF
      (([], target), metisLib.METIS_TAC [])
    handle Feedback.HOL_ERR _ =>
      profile "CPC(rung:rewrite/TAUT)" tautLib.TAUT_PROVE target
    handle Feedback.HOL_ERR _ =>
      raise ERR name "could not prove the captured CPC rewrite shape"

  fun xor_tautology target =
    Tactical.TAC_PROOF (([], target),
      Tactical.THEN
        (profile "CPC(xor_tautology:simp)"
           (bossLib.SIMP_TAC (bossLib.srw_ss())
             [HolSmtTheory.xor_def]),
         profile "CPC(xor_tautology:taut)" tautLib.TAUT_TAC))

  fun tautological_consequence premise target =
    Thm.MP (tautLib.TAUT_PROVE
      (boolSyntax.mk_imp (Thm.concl premise, target))) premise

  fun tautological_consequences premises target =
    let
      val implication = List.foldr
        (fn (premise, body) => boolSyntax.mk_imp (Thm.concl premise, body))
        target premises
    in
      List.foldl (fn (premise, result) => Thm.MP result premise)
        (tautLib.TAUT_PROVE implication) premises
    end

  fun sat_clause_consequences premises target =
    let
      val atoms = ref ([] : (Term.term * Term.term) list)
      fun atom_variable atom =
        case List.find
            (fn (saved, _) => Portable.pointer_eq (atom, saved) orelse
              Term.aconv atom saved)
            (!atoms) of
          SOME (_, variable) => variable
        | NONE =>
            let
              val variable = Term.genvar Type.bool
              val _ = atoms := (atom, variable) :: !atoms
            in variable end
      fun abstract_literal literal =
        if Term.aconv literal boolSyntax.T orelse
           Term.aconv literal boolSyntax.F then literal
        else
          case Lib.total boolSyntax.dest_neg literal of
            SOME atom => boolSyntax.mk_neg (atom_variable atom)
          | NONE => atom_variable literal
      fun abstract_clause clause =
        case Lib.total boolSyntax.dest_disj clause of
          SOME (left, right) => boolSyntax.mk_disj
            (abstract_clause left, abstract_clause right)
        | NONE => abstract_literal clause
      val abstract_premises = List.map
        (abstract_clause o Thm.concl) premises
      val abstract_target = abstract_clause target
      val implication = List.foldr
        (fn (premise, body) => boolSyntax.mk_imp (premise, body))
        abstract_target abstract_premises
      val implication_theorem = HolSatLib.SAT_PROVE implication
        handle HolSatLib.SAT_cex _ =>
          raise ERR "resolution" "abstract clause implication is not valid"
      val substitutions = List.map
        (fn (atom, variable) => {redex = variable, residue = atom})
        (!atoms)
      val instantiated = Thm.INST substitutions implication_theorem
    in
      List.foldl (fn (premise, theorem) => Thm.MP theorem premise)
        instantiated premises
    end

  fun resolve_binary_disjunction prems target =
    (case prems of
      [disjunction_thm, negated_thm] =>
        let
          val (left, right) = boolSyntax.dest_disj (Thm.concl disjunction_thm)
          fun normalize_negated expected theorem =
            if Term.aconv (Thm.concl theorem) (boolSyntax.mk_neg expected) then
              theorem
            else raise ERR "resolution"
              "canonical negated literal does not match its pivot"
          fun resolve eliminated result =
            let
              val negated_thm = normalize_negated eliminated negated_thm
              val contradiction = Thm.MP negated_thm (Thm.ASSUME eliminated)
              val from_false = Thm.MP (Thm.SPEC result boolTheory.FALSITY)
                contradiction
              val from_result = Thm.ASSUME result
            in
              Thm.DISJ_CASES disjunction_thm from_false from_result
            end
          fun resolve_positive left_branch negated_right =
            let
              val positive = boolSyntax.dest_neg negated_right
              val _ = Term.aconv (Thm.concl negated_thm) positive orelse
                raise ERR "resolution" "positive literal does not match clause"
              val contradiction = Thm.MP (Thm.ASSUME negated_right) negated_thm
              val from_false = Thm.MP
                (Thm.SPEC left_branch boolTheory.FALSITY) contradiction
              val from_left = Thm.ASSUME left_branch
            in
              Thm.DISJ_CASES disjunction_thm from_left from_false
            end
        in
          if Term.aconv left target then
            (SOME (resolve_positive left right)
             handle Feedback.HOL_ERR _ => SOME (resolve right left))
          else if Term.aconv right target then SOME (resolve left right)
          else NONE
        end
    | _ => NONE)
    handle _ => NONE

  (* A resolution chain may close directly on complementary unit clauses.
     This is a primitive kernel contradiction, not a disjunction rewrite. *)
  fun resolve_complementary_literals prems target =
    (if Term.aconv target boolSyntax.F then SOME (replay_contra prems)
     else NONE)
    handle _ => NONE

  (* The Seq RARE names have deliberately narrow, recorded schemas.  Keeping
     them out of the generic RARE ladder means an unrecognised Seq rule stays
     a named CPC obligation rather than becoming an accidental simplifier. *)
  fun replay_seq_rewrite name prems conclusion args =
    let
      fun prove_string target =
        List.foldl (fn (premise, proof) => Drule.PROVE_HYP premise proof)
          (SmtStringProve.string_contextual_prove
            (List.map Thm.concl prems) target) prems
      fun substr_concat_target (prefix, suffix, start, length) =
        let
          val string_ty = Term.type_of prefix
          val concat = Term.mk_thy_const {Thy = "smtstring",
            Name = "smtstr_concat", Ty = Type.--> (string_ty,
              Type.--> (string_ty, string_ty))}
          val substr = Term.mk_thy_const {Thy = "smtstring",
            Name = "smtstr_substr", Ty = Type.--> (string_ty,
              Type.--> (intSyntax.int_ty, Type.--> (intSyntax.int_ty,
                string_ty)))}
        in
          boolSyntax.mk_eq
            (Term.list_mk_comb (substr,
               [Term.list_mk_comb (concat, [prefix, suffix]), start, length]),
             Term.list_mk_comb (substr, [prefix, start, length]))
        end
    in
      case (name, conclusion, args) of
        ("str-substr-concat1", SOME target, [prefix, suffix, start, length]) =>
          let val expected = substr_concat_target (prefix, suffix, start, length)
          in
            if Term.aconv target expected then prove_string target
            else raise ERR name "conclusion does not match arguments"
          end
      | ("str-substr-concat1", NONE, [prefix, suffix, start, length]) =>
          prove_string (substr_concat_target (prefix, suffix, start, length))
      | (_, _, [target]) => SmtSeqProve.seq_prove target
      | _ => raise ERR name "expected one Seq rewrite proposition"
    end

  fun is_smtstr_type ty =
    Type.compare (ty, Type.mk_thy_type
      {Thy = "smtstring", Tyop = "smtstr", Args = []}) = EQUAL

  fun instantiate_smtstr theorem sequence =
    case List.filter (fn variable =>
        is_smtstr_type (Term.type_of variable))
      (Term.free_vars (Thm.concl theorem)) of
      [variable] => Thm.INST
        [{redex = variable, residue = sequence}] theorem
    | _ => raise ERR "instantiate_smtstr" "expected one String variable"

  fun replay_seq_rev_rev args =
    case args of
      [sequence] =>
        if is_smtstr_type (Term.type_of sequence) then
          instantiate_smtstr smtstringTheory.smtstr_rev_rev sequence
        else Drule.ISPEC sequence listTheory.REVERSE_REVERSE
    | _ => raise ERR "seq-rev-rev" "expected one sequence argument"

  fun replay_str_contains_refl args =
    case args of
      [sequence] =>
        if is_smtstr_type (Term.type_of sequence) then
          Drule.EQT_INTRO (instantiate_smtstr
            smtstringTheory.smtstr_contains_refl sequence)
        else
          let
            val sequence_ty = Term.type_of sequence
            val empty = listSyntax.mk_nil (listSyntax.eltype sequence)
            val contains = Term.mk_thy_const {Thy = "rich_list",
              Name = "IS_SUBLIST", Ty = Type.--> (sequence_ty,
                Type.--> (sequence_ty, Type.bool))}
            val target = Term.list_mk_comb (contains, [sequence, sequence])
            val proof = Tactical.TAC_PROOF (([], target),
              Tactical.THEN
                (bossLib.RW_TAC (bossLib.srw_ss ())
                   [rich_listTheory.IS_SUBLIST_APPEND],
                 Tactical.THEN (Tactic.EXISTS_TAC empty,
                   Tactical.THEN (Tactic.EXISTS_TAC empty,
                     bossLib.SIMP_TAC (bossLib.srw_ss ()) []))))
          in
            Drule.EQT_INTRO proof
          end
    | _ => raise ERR "str-contains-refl" "expected one sequence argument"

  fun replay_str_substr_full_eq args =
    case args of
      [sequence, length] =>
        if is_smtstr_type (Term.type_of sequence) then
          let
            val theorem = instantiate_smtstr
              smtstringTheory.smtstr_substr_full sequence
            val expected_length = Term.list_mk_comb
              (Term.mk_thy_const {Thy = "smtstring", Name = "smtstr_len",
                 Ty = Type.--> (Term.type_of sequence, intSyntax.int_ty)},
               [sequence])
          in
            if Term.aconv length expected_length then theorem
            else raise ERR "str-substr-full-eq" "length argument does not match"
          end
        else
          let
            val sequence_ty = Term.type_of sequence
            val extract = Term.mk_thy_const {Thy = "HolSmt",
              Name = "smt_seq_extract", Ty = Type.--> (sequence_ty,
                Type.--> (intSyntax.int_ty,
                  Type.--> (intSyntax.int_ty, sequence_ty)))}
            val expected_length = Term.mk_comb (intSyntax.int_injection,
              listSyntax.mk_length sequence)
            val target = boolSyntax.mk_eq
              (Term.list_mk_comb (extract,
                 [sequence, intSyntax.zero_tm, expected_length]), sequence)
          in
            if Term.aconv length expected_length then SmtSeqProve.seq_prove target
            else raise ERR "str-substr-full-eq" "length argument does not match"
          end
    | _ => raise ERR "str-substr-full-eq"
        "expected a sequence and its length"

  fun replay_string_at_elim sequence index =
    Drule.SPECL [sequence, index] smtstringTheory.smtstr_at_def

  fun replay_seq_at_elim conclusion args =
    case (conclusion, args) of
      (SOME target, [sequence, index]) =>
        if is_smtstr_type (Term.type_of sequence) then
          let val thm = replay_string_at_elim sequence index in
            if Term.aconv target (Thm.concl thm) then thm
            else raise ERR "str-at-elim" "String conclusion does not match"
          end
        else SmtSeqProve.seq_prove target
    | (NONE, [sequence, index]) =>
        if is_smtstr_type (Term.type_of sequence) then
          replay_string_at_elim sequence index
        else
          let
            val sequence_ty = Term.type_of sequence
            val at = Term.mk_thy_const {Thy = "HolSmt", Name = "smt_seq_at",
              Ty = Type.--> (sequence_ty,
                Type.--> (intSyntax.int_ty, sequence_ty))}
            val extract = Term.mk_thy_const {
              Thy = "HolSmt", Name = "smt_seq_extract",
              Ty = Type.--> (sequence_ty, Type.--> (intSyntax.int_ty,
                Type.--> (intSyntax.int_ty, sequence_ty)))}
            val target = boolSyntax.mk_eq
              (Term.list_mk_comb (at, [sequence, index]),
               Term.list_mk_comb (extract,
                 [sequence, index, intSyntax.one_tm]))
          in
            SmtSeqProve.seq_prove target
          end
    | _ => raise ERR "str-at-elim" "expected sequence and index arguments"

  fun replay_sets_ext prems =
    case prems of
      [premise] =>
        let
          val (left, right) = boolSyntax.dest_eq
            (boolSyntax.dest_neg (Thm.concl premise))
          val (element, range) = Type.dom_rng (Term.type_of left)
          val _ = Type.compare (range, Type.bool) = EQUAL orelse
            raise ERR "sets_ext" "expected two Sets"
          val variable = Term.variant (Term.all_varsl [left, right])
            (Term.mk_var ("sets_deq_diff_x", element))
          val witness = boolSyntax.mk_select (variable, boolSyntax.mk_neg
            (boolSyntax.mk_eq (Term.mk_comb (left, variable),
              Term.mk_comb (right, variable))))
          val target = boolSyntax.mk_neg (boolSyntax.mk_eq
            (Term.mk_comb (left, witness), Term.mk_comb (right, witness)))
        in
          SmtResource.with_resource_step_time "Set" "extensionality"
            (fn () =>
              (SmtResource.check_resource_goal "Set" "extensionality" target;
               Drule.PROVE_HYP premise
                 (Tactical.TAC_PROOF (([Thm.concl premise], target),
                   bossLib.METIS_TAC
                     [boolTheory.FUN_EQ_THM, boolTheory.SELECT_THM])))) ()
        end
    | _ => raise ERR "sets_ext" "expected one disequality premise"

  (* Set rewrites are deliberately driven by the certificate conclusion.
     Their names are closed explicitly in CPC_Proof's frozen inventory; this
     makes a future sets-* rule a versioned, loud registry error rather than
     a generic simplifier admission.  The actual proof is shared with the
     ArrayEx/set ladder because D13 represents a Set as [a -> bool]. *)
  fun replay_sets state name prems conclusion args =
    let
      fun empty set = pred_setSyntax.mk_empty (pred_setSyntax.eltype set)
      fun singleton element = pred_setSyntax.mk_insert
        (element, pred_setSyntax.mk_empty (Term.type_of element))
      fun card set = Term.mk_comb
        (intSyntax.int_injection, pred_setSyntax.mk_card set)
      fun prove target =
        if name = "sets-card-union" orelse name = "sets-card-minus" then
          let
            val context =
              HOLset.listItems (#asserted_hyps state) @ #scope_hyps state @
              List.map Thm.concl prems
            fun prove_tac context target tactic =
              SmtResource.with_resource_step_time "Set" "cardinality"
                (fn () =>
                  (SmtResource.check_resource_goal "Set" "cardinality"
                     target;
                   Tactical.TAC_PROOF ((context, target), tactic))) ()
            val (left, right) =
              case args of
                [left, right] => (left, right)
              | _ => raise ERR name "wrong cardinality arguments"
            val s = Term.genvar (Term.type_of left)
            val t = Term.genvar (Term.type_of right)
            val finite_sets =
              if name = "sets-card-union" then [s, t] else [s]
            val conditions = List.map pred_setSyntax.mk_finite finite_sets
            val intersection = pred_setSyntax.mk_inter (s, t)
            val bound_term = numSyntax.mk_leq
              (pred_setSyntax.mk_card intersection,
               if name = "sets-card-union" then
                 numSyntax.mk_plus
                   (pred_setSyntax.mk_card s, pred_setSyntax.mk_card t)
               else pred_setSyntax.mk_card s)
            val bound = prove_tac conditions bound_term
              (bossLib.METIS_TAC
                [pred_setTheory.CARD_INTER_LESS_EQ,
                 arithmeticTheory.LESS_EQ_ADD,
                 arithmeticTheory.LESS_EQ_TRANS])
            val equation =
              if name = "sets-card-union" then
                boolSyntax.mk_eq (card (pred_setSyntax.mk_union (s, t)),
                  intSyntax.mk_minus
                    (intSyntax.mk_plus (card s, card t), card intersection))
              else
                boolSyntax.mk_eq (card (pred_setSyntax.mk_diff (s, t)),
                  intSyntax.mk_minus (card s, card intersection))
            (* Prove before instantiating: simplification of concrete sets
               can otherwise hide CARD_DIFF_EQN and the subtraction bound. *)
            val schematic = prove_tac (Thm.concl bound :: conditions) equation
              (bossLib.ASM_SIMP_TAC (bossLib.srw_ss ())
                [pred_setTheory.CARD_UNION_EQN,
                 pred_setTheory.CARD_DIFF_EQN,
                 integerTheory.INT_OF_NUM_ADD,
                 integerTheory.INT_SUB])
            val substitution = [{redex = s, residue = left},
                                {redex = t, residue = right}]
            val instantiated = Thm.INST substitution
              (Drule.PROVE_HYP bound schematic)
            val finiteness = List.map
              (fn condition => prove_tac context
                (Term.subst substitution condition)
                (bossLib.ASM_SIMP_TAC (bossLib.srw_ss ()) [])) conditions
            val proof = List.foldl
              (fn (finite, proved) => Drule.PROVE_HYP finite proved)
              instantiated finiteness
            val proof =
              if Term.aconv (Thm.concl proof) target then proof
              else Drule.PROVE_HYP proof
                (prove_tac [Thm.concl proof] target
                  (bossLib.ASM_SIMP_TAC (bossLib.srw_ss ()) []))
          in
            List.foldl (fn (premise, proved) => Drule.PROVE_HYP premise proved)
              proof prems
          end
        else if name = "sets-eval-op" then
          (Tactical.TAC_PROOF (([], target),
             bossLib.SIMP_TAC (bossLib.srw_ss ()) [])
           handle Feedback.HOL_ERR _ => SmtArrayProve.array_prove target)
        else if SmtArrayProve.has_set_term target then
          SmtArrayProve.array_prove target
        else
          raise ERR name
            ("set rule conclusion has no native Set term: " ^
             Library.term_to_string target)
      fun omitted_target () =
        case (name, args) of
          ("sets-card-union", [left, right]) =>
            boolSyntax.mk_eq (card (pred_setSyntax.mk_union (left, right)),
              intSyntax.mk_minus
                (intSyntax.mk_plus (card left, card right),
                 card (pred_setSyntax.mk_inter (left, right))))
        | ("sets-card-minus", [left, right]) =>
            boolSyntax.mk_eq (card (pred_setSyntax.mk_diff (left, right)),
              intSyntax.mk_minus (card left,
                card (pred_setSyntax.mk_inter (left, right))))
        | ("sets-card-emp", [set, _]) =>
            boolSyntax.mk_eq (card set, intSyntax.zero_tm)
        | ("sets-card-singleton", [element]) =>
            boolSyntax.mk_eq (card (singleton element),
              intSyntax.term_of_int (Arbint.fromInt 1))
        | ("sets-choose-singleton", [element]) =>
            boolSyntax.mk_eq (pred_setSyntax.mk_choice (singleton element),
              element)
        | ("sets-eval-op", [target]) => target
        | ("sets-insert-elim", [target]) => target
        | ("sets-inter-comm", [left, right]) =>
            boolSyntax.mk_eq (pred_setSyntax.mk_inter (left, right),
              pred_setSyntax.mk_inter (right, left))
        | ("sets-inter-member", [element, left, right]) =>
            boolSyntax.mk_eq
              (pred_setSyntax.mk_in
                 (element, pred_setSyntax.mk_inter (left, right)),
               boolSyntax.mk_conj (pred_setSyntax.mk_in (element, left),
                 pred_setSyntax.mk_in (element, right)))
        | ("sets-is-empty-elim", [set, _]) =>
            let val is_empty = boolSyntax.mk_eq (set, empty set)
            in boolSyntax.mk_eq (is_empty, is_empty) end
        | ("sets-is-singleton-elim", [set]) =>
            boolSyntax.mk_eq (pred_setSyntax.mk_sing set,
              boolSyntax.mk_eq (set,
                singleton (pred_setSyntax.mk_choice set)))
        | ("sets-member-emp", [element, set, _]) =>
            boolSyntax.mk_eq (pred_setSyntax.mk_in (element, set),
              boolSyntax.F)
        | ("sets-member-singleton", [element, singleton_element]) =>
            boolSyntax.mk_eq
              (pred_setSyntax.mk_in (element, singleton singleton_element),
               boolSyntax.mk_eq (element, singleton_element))
        | ("sets-minus-member", [element, left, right]) =>
            boolSyntax.mk_eq
              (pred_setSyntax.mk_in
                 (element, pred_setSyntax.mk_diff (left, right)),
               boolSyntax.mk_conj (pred_setSyntax.mk_in (element, left),
                 boolSyntax.mk_neg (pred_setSyntax.mk_in (element, right))))
        | ("sets-minus-self", [set, _]) =>
            boolSyntax.mk_eq (pred_setSyntax.mk_diff (set, set), empty set)
        | ("sets-subset-elim", [left, right]) =>
            boolSyntax.mk_eq (pred_setSyntax.mk_subset (left, right),
              boolSyntax.mk_eq (pred_setSyntax.mk_union (left, right), right))
        | ("sets-union-comm", [left, right]) =>
            boolSyntax.mk_eq (pred_setSyntax.mk_union (left, right),
              pred_setSyntax.mk_union (right, left))
        | ("sets-union-member", [element, left, right]) =>
            boolSyntax.mk_eq
              (pred_setSyntax.mk_in
                 (element, pred_setSyntax.mk_union (left, right)),
               boolSyntax.mk_disj (pred_setSyntax.mk_in (element, left),
                 pred_setSyntax.mk_in (element, right)))
        | _ => raise ERR name
            "omitted conclusion has an unsupported recorded argument shape"
    in
      prove (case conclusion of SOME target => target | NONE => omitted_target ())
    end

  fun replay_rare_rewrite name args =
    let
      val smt_ediv_total_tm = Term.prim_mk_const
        {Thy = "HolSmt", Name = "smt_ediv_total"}
      val smt_emod_total_tm = Term.prim_mk_const
        {Thy = "HolSmt", Name = "smt_emod_total"}
      fun smt_ediv_total (a, b) = Term.list_mk_comb
        (smt_ediv_total_tm, [a, b])
      fun smt_emod_total (a, b) = Term.list_mk_comb
        (smt_emod_total_tm, [a, b])
      fun smtstring_app constant arguments =
        Term.list_mk_comb
          (Term.prim_mk_const {Thy = "smtstring", Name = constant},
           arguments)
      fun bool_xor (left, right) = Term.list_mk_comb
        (Term.prim_mk_const {Thy = "HolSmt", Name = "xor"},
         [left, right])
      fun int_literal n =
        intSyntax.term_of_int (Arbint.fromInt n)
      fun arith_leq (left, right) =
        intSyntax.mk_leq (left, right)
        handle Feedback.HOL_ERR _ => realSyntax.mk_leq (left, right)
      fun arith_geq (left, right) =
        intSyntax.mk_geq (left, right)
        handle Feedback.HOL_ERR _ => realSyntax.mk_geq (left, right)
      fun arith_ite_lift relation
          [condition, then_term, else_term, right] =
        let
          val target = boolSyntax.mk_eq
            (relation
               (boolSyntax.mk_cond (condition, then_term, else_term), right),
             boolSyntax.mk_cond
               (condition, relation (then_term, right),
                relation (else_term, right)))
        in
          Tactical.TAC_PROOF (([], target),
            Tactical.THEN (Tactic.COND_CASES_TAC,
              bossLib.SIMP_TAC boolSimps.bool_ss []))
        end
        | arith_ite_lift _ _ =
            raise ERR name "expected condition, branches, and right operand"
      fun guard_not_zero term = boolSyntax.mk_neg
        (boolSyntax.mk_eq (term, intSyntax.zero_tm))
      fun guarded name guard target tactic =
        let
          val thm = Tactical.TAC_PROOF (([guard], target), tactic)
        in
          (Thm.MP thm
             (Tactical.TAC_PROOF (([], guard), intLib.ARITH_TAC))
           handle Feedback.HOL_ERR _ => thm)
        end
      fun guard_thm guard =
        Tactical.TAC_PROOF (([], guard), intLib.ARITH_TAC)
        handle Feedback.HOL_ERR _ => Thm.ASSUME guard
      fun distinct_lemma target =
        Tactical.TAC_PROOF (([], target),
          bossLib.SIMP_TAC (bossLib.srw_ss())
            [HolSmtTheory.ALL_DISTINCT_NIL,
             HolSmtTheory.ALL_DISTINCT_CONS])
      fun total_eq_ediv a b =
        Drule.SPECL [a, b] HolSmtTheory.smt_ediv_total_eq_ediv
      fun total_eq_emod a b =
        Drule.SPECL [a, b] HolSmtTheory.smt_emod_total_eq_emod
      fun list_terms term =
        #1 (listSyntax.dest_list term)
        handle Feedback.HOL_ERR _ =>
          raise ERR name "expected a CPC :list argument"
      fun fold_int operation terms =
        case terms of
          [] => intSyntax.zero_tm
        | first :: rest => List.foldl
            (fn (right, left) => operation (left, right)) first rest
      fun mod_context c ts r ss operation =
        let
          val ts = list_terms ts
          val ss = list_terms ss
          val inner = smt_emod_total (r, c)
          val left_context = fold_int operation (ts @ [inner] @ ss)
          val right_context = fold_int operation (ts @ [r] @ ss)
          val target = boolSyntax.mk_eq
            (smt_emod_total (left_context, c),
             smt_emod_total (right_context, c))
          val guard = guard_not_zero c
        in
          guarded name guard target
            (bossLib.ASM_SIMP_TAC (bossLib.srw_ss())
              [HolSmtTheory.smt_emod_total_def,
               integerTheory.EMOD_DEF,
               integerTheory.INT_MOD_MOD,
               integerTheory.INT_MOD_ADD_MULTIPLES])
        end
      fun mod_context_add args =
        (case args of
           [c, ts, r, ss] => mod_context c ts r ss intSyntax.mk_plus
         | _ => raise ERR name "expected c, ts, r, ss arguments")
      fun mod_context_mult args =
        (case args of
           [c, ts, r, ss] => mod_context c ts r ss intSyntax.mk_mult
         | _ => raise ERR name "expected c, ts, r, ss arguments")
    in case (name, args) of
      ("exists-elim", [target]) =>
        let
        in
          Tactical.TAC_PROOF (([], target),
            bossLib.SIMP_TAC (bossLib.srw_ss()) [boolTheory.NOT_FORALL_THM])
        end
    | ("bool-double-not-elim", [p]) =>
        let
          val variable = Term.genvar Type.bool
          val law = tautLib.TAUT_PROVE (boolSyntax.mk_eq
            (boolSyntax.mk_neg (boolSyntax.mk_neg variable), variable))
        in Thm.INST [{redex = variable, residue = p}] law end
    | ("bool-impl-elim", [left, right]) =>
        let
          val left_variable = Term.genvar Type.bool
          val right_variable = Term.genvar Type.bool
          val law = tautLib.TAUT_PROVE (boolSyntax.mk_eq
            (boolSyntax.mk_imp (left_variable, right_variable),
             boolSyntax.mk_disj
               (boolSyntax.mk_neg left_variable, right_variable)))
        in
          Thm.INST
            [{redex = left_variable, residue = left},
             {redex = right_variable, residue = right}] law
        end
    | ("bool-eq-false", [p]) =>
        let
          val variable = Term.genvar Type.bool
          val law = tautLib.TAUT_PROVE (boolSyntax.mk_eq
            (boolSyntax.mk_eq (variable, boolSyntax.F),
             boolSyntax.mk_neg variable))
        in Thm.INST [{redex = variable, residue = p}] law end
    | ("bool-eq-true", [p]) =>
        let
          val variable = Term.genvar Type.bool
          val law = tautLib.TAUT_PROVE (boolSyntax.mk_eq
            (boolSyntax.mk_eq (variable, boolSyntax.T), variable))
        in Thm.INST [{redex = variable, residue = p}] law end
    | ("bool-xor-comm", [left, right]) =>
        let
          val left_variable = Term.genvar Type.bool
          val right_variable = Term.genvar Type.bool
          val law = xor_tautology (boolSyntax.mk_eq
            (bool_xor (left_variable, right_variable),
             bool_xor (right_variable, left_variable)))
        in
          Thm.INST
            [{redex = left_variable, residue = left},
             {redex = right_variable, residue = right}] law
        end
    | ("bool-xor-false", [p]) =>
        let
          val variable = Term.genvar Type.bool
          val law = xor_tautology (boolSyntax.mk_eq
            (bool_xor (variable, boolSyntax.F), variable))
        in Thm.INST [{redex = variable, residue = p}] law end
    | ("bool-xor-true", [p]) =>
        let
          val variable = Term.genvar Type.bool
          val law = xor_tautology (boolSyntax.mk_eq
            (bool_xor (variable, boolSyntax.T),
             boolSyntax.mk_neg variable))
        in Thm.INST [{redex = variable, residue = p}] law end
    | ("bool-impl-false1", [p]) =>
        Tactical.TAC_PROOF
          (([], boolSyntax.mk_eq
            (boolSyntax.mk_imp (p, boolSyntax.F), boolSyntax.mk_neg p)),
           bossLib.SIMP_TAC boolSimps.bool_ss [])
    | ("bool-impl-true1", [p]) =>
        tautology name (boolSyntax.mk_eq
          (boolSyntax.mk_imp (p, boolSyntax.T), boolSyntax.T))
    | ("bool-impl-true2", [p]) =>
        tautology name (boolSyntax.mk_eq
          (boolSyntax.mk_imp (boolSyntax.T, p), p))
    | ("bool-eq-nrefl", [p]) =>
        tautology name (boolSyntax.mk_eq
          (boolSyntax.mk_eq (p, boolSyntax.mk_neg p), boolSyntax.F))
    | ("eq-symm", [left, right]) =>
        let
          val left_right = boolSyntax.mk_eq (left, right)
          val right_left = boolSyntax.mk_eq (right, left)
          val forward = Thm.DISCH left_right
            (Thm.SYM (Thm.ASSUME left_right))
          val backward = Thm.DISCH right_left
            (Thm.SYM (Thm.ASSUME right_left))
        in Drule.IMP_ANTISYM_RULE forward backward end
    | ("bool-not-eq-elim2", [left, right]) =>
        tautology name (boolSyntax.mk_eq
          (boolSyntax.mk_neg (boolSyntax.mk_eq (left, right)),
           boolSyntax.mk_eq (left, boolSyntax.mk_neg right)))
    | ("bool-not-eq-elim1", [left, right]) =>
        tautology name (boolSyntax.mk_eq
          (boolSyntax.mk_neg (boolSyntax.mk_eq (left, right)),
           boolSyntax.mk_eq (boolSyntax.mk_neg left, right)))
    | ("str-lt-elim", [left, right]) =>
        let
          val lt = smtstring_app "smtstr_lt" [left, right]
          val le = smtstring_app "smtstr_le" [left, right]
          val target =
            boolSyntax.mk_eq
              (lt, boolSyntax.mk_conj
                (boolSyntax.mk_neg (boolSyntax.mk_eq (left, right)), le))
        in
          SmtStringProve.string_rewrite_prove target
        end
    | ("str-is-digit-elim", [string]) =>
        let
          val is_digit = smtstring_app "smtstr_is_digit" [string]
          val code = smtstring_app "smtstr_to_code" [string]
          val target =
            boolSyntax.mk_eq
              (is_digit, boolSyntax.mk_conj
                (intSyntax.mk_leq (int_literal 48, code),
                 intSyntax.mk_leq (code, int_literal 57)))
        in
          SmtStringProve.string_rewrite_prove target
        end
    | ("distinct-elim", [target]) => distinct_lemma target
    | ("distinct-false", [target]) => distinct_lemma target
    | ("eq-ite-lift", operands as [_, _, _, _]) =>
        arith_ite_lift boolSyntax.mk_eq operands
    | ("arith-leq-ite-lift", operands) =>
        arith_ite_lift arith_leq operands
    | ("arith-geq-ite-lift", operands) =>
        arith_ite_lift arith_geq operands
    | ("bool-or-de-morgan", [left, right, _]) =>
        tautology name (boolSyntax.mk_eq
          (boolSyntax.mk_neg (boolSyntax.mk_disj (left, right)),
           boolSyntax.mk_conj (boolSyntax.mk_neg left, boolSyntax.mk_neg right)))
    | ("bool-and-de-morgan", [left, right, _]) =>
        tautology name (boolSyntax.mk_eq
          (boolSyntax.mk_neg (boolSyntax.mk_conj (left, right)),
           boolSyntax.mk_disj (boolSyntax.mk_neg left, boolSyntax.mk_neg right)))
    | ("bool-implies-de-morgan", [left, right]) =>
        tautology name (boolSyntax.mk_eq
          (boolSyntax.mk_neg (boolSyntax.mk_imp (left, right)),
           boolSyntax.mk_conj (left, boolSyntax.mk_neg right)))
    | ("distinct-binary-elim", [left, right]) =>
        let
          val distinct = listSyntax.mk_all_distinct
            (listSyntax.mk_list ([left, right], Term.type_of left))
          val target = boolSyntax.mk_eq
            (distinct, boolSyntax.mk_neg (boolSyntax.mk_eq (left, right)))
        in
          Tactical.TAC_PROOF (([], target),
            bossLib.SIMP_TAC (bossLib.srw_ss())
              [HolSmtTheory.ALL_DISTINCT_NIL,
               HolSmtTheory.ALL_DISTINCT_CONS])
        end
    | ("array-read-over-write-split",
       [array, index, value, update_index]) =>
        let
          val base = Drule.ISPECL [array, update_index, value, index]
            combinTheory.APPLY_UPDATE_THM
            handle Feedback.HOL_ERR holerr =>
              raise ERR "array-read-over-write-split"
                ("APPLY_UPDATE_THM instantiation failed: " ^
                 Feedback.message_of holerr)
          val condition_eq = Drule.ISPECL [update_index, index]
            boolTheory.EQ_SYM_EQ
            handle Feedback.HOL_ERR holerr =>
              raise ERR "array-read-over-write-split"
                ("EQ_SYM_EQ instantiation failed: " ^
                 Feedback.message_of holerr)
          val condition = Term.mk_var ("condition", Type.bool)
          val context = Term.mk_abs (condition,
            boolSyntax.mk_cond
              (condition, value, Term.mk_comb (array, index)))
          val rhs_eq = Conv.BETA_RULE (Thm.AP_TERM context condition_eq)
            handle Feedback.HOL_ERR holerr =>
              raise ERR "array-read-over-write-split"
                ("conditional congruence failed: " ^
                 Feedback.message_of holerr)
        in
          Thm.TRANS base rhs_eq
          handle Feedback.HOL_ERR holerr =>
            raise ERR "array-read-over-write-split"
              ("read-over-write composition failed: " ^
               Feedback.message_of holerr)
        end
    | ("array-read-over-write", [array, index, value]) =>
        Drule.ISPECL [index, value, array] combinTheory.UPDATE_APPLY1
    | ("array-read-over-write2", [array, update_index, index, value]) =>
        let
          val guard = boolSyntax.mk_eq
            (boolSyntax.mk_eq (update_index, index), boolSyntax.F)
          val target = boolSyntax.mk_eq
            (Term.mk_comb
               (Term.mk_comb
                 (combinSyntax.mk_update (update_index, value), array),
                index),
             Term.mk_comb (array, index))
        in
          Tactical.TAC_PROOF (([guard], target),
            bossLib.ASM_SIMP_TAC (bossLib.srw_ss ())
              [combinTheory.APPLY_UPDATE_THM])
        end
    | ("array-store-overwrite", [array, index, old_value, new_value]) =>
        Drule.ISPECL [array, index, old_value, new_value]
          combinTheory.UPDATE_EQ
    | ("array-store-self", [array, index]) =>
        Drule.ISPECL [array, index] combinTheory.APPLY_UPDATE_ID
    | ("array-store-swap",
       [array, left_index, right_index, left_value, right_value]) =>
        let
          val guard = boolSyntax.mk_eq
            (boolSyntax.mk_eq (left_index, right_index), boolSyntax.F)
          fun update index value base =
            Term.mk_comb (combinSyntax.mk_update (index, value), base)
          val target = boolSyntax.mk_eq
            (update right_index right_value
               (update left_index left_value array),
             update left_index left_value
               (update right_index right_value array))
        in
          Tactical.TAC_PROOF (([guard], target),
            bossLib.ASM_SIMP_TAC (bossLib.srw_ss ())
              [combinTheory.UPDATE_COMMUTES])
        end
    | ("absorb", [target]) =>
        let
          fun schematic_absorb () =
            let
              val (left, right) = boolSyntax.dest_eq target
              val variable = Term.genvar Type.bool
              fun instantiate law operand = Thm.INST
                [{redex = variable, residue = operand}] law
              val conj_left_law = tautLib.TAUT_PROVE (boolSyntax.mk_eq
                (boolSyntax.mk_conj (boolSyntax.F, variable), boolSyntax.F))
              val conj_right_law = tautLib.TAUT_PROVE (boolSyntax.mk_eq
                (boolSyntax.mk_conj (variable, boolSyntax.F), boolSyntax.F))
              val disj_left_law = tautLib.TAUT_PROVE (boolSyntax.mk_eq
                (boolSyntax.mk_disj (boolSyntax.T, variable), boolSyntax.T))
              val disj_right_law = tautLib.TAUT_PROVE (boolSyntax.mk_eq
                (boolSyntax.mk_disj (variable, boolSyntax.T), boolSyntax.T))
              fun nested_absorb dest absorber left_law right_law term =
                if Term.aconv term absorber then Thm.REFL term
                else
                  let
                    val (first, second) = dest term
                    val (application, _) = Term.dest_comb term
                    val (operator, _) = Term.dest_comb application
                    fun through_right theorem =
                      let
                        val congruence = Thm.MK_COMB
                          (Thm.MK_COMB (Thm.REFL operator,
                            Thm.REFL first), theorem)
                        val congruence = Thm.TRANS
                          (Thm.REFL term) congruence
                      in Thm.TRANS congruence
                        (instantiate right_law first) end
                    fun through_left theorem =
                      let
                        val congruence = Thm.MK_COMB
                          (Thm.MK_COMB (Thm.REFL operator, theorem),
                            Thm.REFL second)
                        val congruence = Thm.TRANS
                          (Thm.REFL term) congruence
                      in Thm.TRANS congruence
                        (instantiate left_law second) end
                  in
                    through_right
                      (nested_absorb dest absorber left_law right_law second)
                    handle Feedback.HOL_ERR _ =>
                      through_left
                        (nested_absorb dest absorber left_law right_law first)
                  end
            in
              if Term.aconv right boolSyntax.F andalso
                 Option.isSome (Lib.total boolSyntax.dest_conj left) then
                nested_absorb boolSyntax.dest_conj boolSyntax.F
                  conj_left_law conj_right_law left
              else if Term.aconv right boolSyntax.T andalso
                      Option.isSome (Lib.total boolSyntax.dest_disj left) then
                nested_absorb boolSyntax.dest_disj boolSyntax.T
                  disj_left_law disj_right_law left
              else case Lib.total boolSyntax.dest_conj left of
                SOME (first, second) =>
                  if Term.aconv first boolSyntax.F andalso
                     Term.aconv right boolSyntax.F then
                    instantiate
                      (tautLib.TAUT_PROVE (boolSyntax.mk_eq
                        (boolSyntax.mk_conj (boolSyntax.F, variable),
                         boolSyntax.F))) second
                  else if Term.aconv second boolSyntax.F andalso
                          Term.aconv right boolSyntax.F then
                    instantiate
                      (tautLib.TAUT_PROVE (boolSyntax.mk_eq
                        (boolSyntax.mk_conj (variable, boolSyntax.F),
                         boolSyntax.F))) first
                  else raise ERR "absorb" "not conjunction absorption"
              | NONE =>
                  (case Lib.total boolSyntax.dest_disj left of
                     SOME (first, second) =>
                       if Term.aconv first boolSyntax.T andalso
                          Term.aconv right boolSyntax.T then
                         instantiate
                           (tautLib.TAUT_PROVE (boolSyntax.mk_eq
                             (boolSyntax.mk_disj

                                (boolSyntax.T, variable), boolSyntax.T)))
                           second
                       else if Term.aconv second boolSyntax.T andalso
                               Term.aconv right boolSyntax.T then
                         instantiate
                           (tautLib.TAUT_PROVE (boolSyntax.mk_eq
                             (boolSyntax.mk_disj
                                (variable, boolSyntax.T), boolSyntax.T)))
                           first
                       else raise ERR "absorb" "not disjunction absorption"
                   | NONE => raise ERR "absorb" "not Boolean absorption")
            end
        in
          schematic_absorb ()
          handle Feedback.HOL_ERR _ =>
            (profile "CPC(rung:RARE/absorb/simp)" Tactical.TAC_PROOF
               (([], target), bossLib.SIMP_TAC boolSimps.bool_ss [])
             handle Feedback.HOL_ERR _ =>
               profile "CPC(rung:RARE/absorb/word_arith)"
                 wordsLib.WORD_ARITH_PROVE target)
        end
    | ("arith-div-total-zero-real", [term]) =>
        Tactical.TAC_PROOF
          (([], boolSyntax.mk_eq
            (realSyntax.mk_div (term, realSyntax.zero_tm),
             realSyntax.zero_tm)),
           bossLib.SIMP_TAC realSimps.real_ss [realTheory.REAL_DIV_ZERO])
    | ("arith-div-total-zero-int", [term]) =>
        Tactical.TAC_PROOF
          (([], boolSyntax.mk_eq
            (realSyntax.mk_div (intrealSyntax.mk_real_of_int term,
               realSyntax.zero_tm),
             realSyntax.zero_tm)),
           bossLib.SIMP_TAC realSimps.real_ss [realTheory.REAL_DIV_ZERO])
    | ("arith-int-div-total", [a, b]) =>
        Thm.SYM
          (Thm.MP (total_eq_ediv a b)
            (guard_thm (guard_not_zero b)))
    | ("arith-int-div-total-one", [a]) =>
        Thm.SPEC a HolSmtTheory.smt_ediv_total_one
    | ("arith-int-div-total-zero", [a]) =>
        Thm.SPEC a HolSmtTheory.smt_ediv_total_zero
    | ("arith-int-div-total-neg", [a, b]) =>
        Thm.MP (Drule.SPECL [a, b] HolSmtTheory.smt_ediv_total_neg)
          (guard_thm (intSyntax.mk_less (b, intSyntax.zero_tm)))
    | ("arith-int-mod-total", [a, b]) =>
        Thm.SYM
          (Thm.MP (total_eq_emod a b)
            (guard_thm (guard_not_zero b)))
    | ("arith-int-mod-total-one", [a]) =>
        Thm.SPEC a HolSmtTheory.smt_emod_total_one
    | ("arith-int-mod-total-zero", [a]) =>
        Thm.SPEC a HolSmtTheory.smt_emod_total_zero
    | ("arith-int-mod-total-neg", [a, b]) =>
        Thm.MP (Drule.SPECL [a, b] HolSmtTheory.smt_emod_total_neg)
          (guard_thm (intSyntax.mk_less (b, intSyntax.zero_tm)))
    | ("arith-divisible-elim", [n, t]) =>
        let
          val guard = guard_not_zero n
          val divisible = intSyntax.mk_divides (n, t)
          val target = boolSyntax.mk_eq
            (smt_emod_total (t, n), intSyntax.zero_tm)
          val total_eq = Thm.MP
            (Drule.SPECL [t, n] HolSmtTheory.smt_emod_total_eq_emod)
            (Thm.ASSUME guard)
          val remainder_zero = Tactical.TAC_PROOF
            (([guard, divisible],
              boolSyntax.mk_eq
                (SmtLib_Theories.mk_int_emod (t, n), intSyntax.zero_tm)),
             Tactical.THEN
               (bossLib.SIMP_TAC (bossLib.srw_ss())
                  [integerTheory.EMOD_DEF, integerTheory.INT_ABS],
                Tactical.THEN (Tactic.COND_CASES_TAC,
                  metisLib.METIS_TAC
                    [integerTheory.INT_DIVIDES_MOD0,
                     integerTheory.INT_DIVIDES_NEG])))
        in
          Thm.TRANS total_eq remainder_zero
        end
    | ("arith-mod-over-mod-1", [c, r]) =>
        let
          val guard = guard_not_zero c
          val target = boolSyntax.mk_eq
            (smt_emod_total (smt_emod_total (r, c), c),
             smt_emod_total (r, c))
        in
          guarded name guard target
            (bossLib.ASM_SIMP_TAC (bossLib.srw_ss())
              [HolSmtTheory.smt_emod_total_def,
               integerTheory.EMOD_DEF,
               integerTheory.INT_MOD_MOD])
        end
    | ("arith-mod-over-mod", args) => mod_context_add args
    | ("arith-mod-over-mod-mult", args) => mod_context_mult args
    | _ => raise ERR name "unsupported CPC RARE rewrite argument shape"
    end

  fun replay_rare_rewrite_with_provenance name
      (located_args : located_term list) =
    let
      val args = List.map (fn located => #term located) located_args
      val theorem = replay_rare_rewrite name args
      fun semantic_provenance () =
        conjunction_free_semantic_provenance
          ("CPC RARE rewrite " ^ name ^
           " produced a result containing an exact conjunction")
          (Thm.concl theorem)
      fun exact_argument_or_semantic located =
        if Term.aconv (#term located) (Thm.concl theorem) then
          #provenance located
        else semantic_provenance ()
      val provenance =
        case (name, located_args) of
          ("bool-double-not-elim", [located]) =>
            let val operand = #provenance located in
              EqualityProvenance
                (ApplicationProvenance ("not",
                   [ApplicationProvenance ("not", [operand])]), operand)
            end
        | ("eq-symm", [left, right]) =>
            let
              val left_provenance = #provenance left
              val right_provenance = #provenance right
            in
              EqualityProvenance
                (EqualityProvenance
                   (left_provenance, right_provenance),
                 EqualityProvenance
                   (right_provenance, left_provenance))
            end
        | ("bool-eq-false", [located]) =>
            let val operand = #provenance located in
              EqualityProvenance
                (EqualityProvenance
                   (operand, AtomicProvenance),
                 ApplicationProvenance ("not", [operand]))
            end
        | (_, [located]) => exact_argument_or_semantic located
        | _ => semantic_provenance ()
    in
      (theorem, provenance)
    end

  fun replay_aci_norm args =
    let
      val target = expect_one_arg "aci_norm" args
      val reflexive =
        boolSyntax.is_eq target andalso
        let val (left, right) = boolSyntax.dest_eq target
        in Term.aconv left right end
      fun conjunction_implication source destination =
        let
          val assumption = Thm.ASSUME source
          (* ACI normalization compares each destination leaf against the
             source collection.  This must be an indexed exact term set:
             the former linear search makes a large bit-blasted clause
             quadratic in its leaves.  [Term.compare] is alpha-aware, so a
             successful lookup is precisely the equality required by the
             kernel inference below. *)
          val leaves = ref (Redblackmap.mkDict Term.compare :
            (Term.term, Thm.thm) Redblackmap.dict)
          val seen = ref (Redblackmap.mkDict Term.compare)
          fun remember term theorem =
            case Redblackmap.peek (!leaves, term) of
              SOME _ => ()
            | NONE =>
                leaves := Redblackmap.insert (!leaves, term, theorem)
          fun collect term theorem =
            case SmtSkeletonProve.pointer_cache_peek (!seen) term of
              SOME () => ()
            | NONE =>
                (seen := SmtSkeletonProve.pointer_cache_insert
                   (!seen) term ();
                 if Term.aconv term boolSyntax.T then ()
                 else
                   case Lib.total boolSyntax.dest_conj term of
                     SOME (left, right) =>
                       (collect left (Thm.CONJUNCT1 theorem);
                        collect right (Thm.CONJUNCT2 theorem))
                   | NONE => remember term theorem)
          val _ = collect source assumption
          fun leaf_theorem term =
            case Redblackmap.peek (!leaves, term) of
              SOME theorem => theorem
            | NONE => raise ERR "aci_norm"
                "conjunction normalization changed a leaf"
          val memo = ref (Redblackmap.mkDict Term.compare)
          fun derive term =
            case SmtSkeletonProve.pointer_cache_peek (!memo) term of
              SOME theorem => theorem
            | NONE =>
                let
                  val theorem =
                    if Term.aconv term boolSyntax.T then boolTheory.TRUTH
                    else
                      case Lib.total boolSyntax.dest_conj term of
                        SOME (left, right) =>
                          Thm.CONJ (derive left) (derive right)
                      | NONE => leaf_theorem term
                  val _ = memo := SmtSkeletonProve.pointer_cache_insert
                    (!memo) term theorem
                in theorem end
        in Thm.DISCH source (derive destination) end
      fun conjunction_aci () =
        let
          val (left, right) = boolSyntax.dest_eq target
          val _ = boolSyntax.is_conj left orelse
                  boolSyntax.is_conj right orelse
                  Term.aconv left boolSyntax.T orelse
                  Term.aconv right boolSyntax.T orelse
            raise ERR "aci_norm" "not a conjunction ACI equality"
          val forward = conjunction_implication left right
          val reverse = conjunction_implication right left
        in Drule.IMP_ANTISYM_RULE forward reverse end
      fun disjunction_implication source destination =
        let
          (* Index a representative destination path for each leaf.  The
             previous [contains] search walked the destination afresh for
             every source leaf; this is the same exact ACI construction with
             linear indexing and logarithmic leaf lookup. *)
          val destination_paths = ref (Redblackmap.mkDict Term.compare :
            (Term.term, bool list) Redblackmap.dict)
          fun remember term path =
            case Redblackmap.peek (!destination_paths, term) of
              SOME _ => ()
            | NONE =>
                destination_paths := Redblackmap.insert
                  (!destination_paths, term, List.rev path)
          fun index term path =
            if Term.aconv term boolSyntax.T orelse
               Term.aconv term boolSyntax.F then ()
            else
              case Lib.total boolSyntax.dest_disj term of
                SOME (left, right) =>
                  (index left (true :: path); index right (false :: path))
              | NONE => remember term path
          val _ = index destination []
          fun from_false theorem =
            Thm.MP (Thm.SPEC destination boolTheory.FALSITY) theorem
          fun place theorem term [] = theorem
            | place theorem term (left_branch :: rest) =
                let val (left, right) = boolSyntax.dest_disj term in
                  if left_branch then
                    Thm.DISJ1 (place theorem left rest) right
                  else Thm.DISJ2 left (place theorem right rest)
                end
          fun inject theorem =
            let val leaf = Thm.concl theorem in
              if Term.aconv leaf boolSyntax.F then from_false theorem
              else if Term.aconv destination boolSyntax.T then boolTheory.TRUTH
              else
                case Redblackmap.peek (!destination_paths, leaf) of
                  SOME path => place theorem destination path
                | NONE => raise ERR "aci_norm"
                    "disjunction normalization changed a leaf"
            end
          val memo = ref (Redblackmap.mkDict Term.compare)
          fun derive term theorem =
            case SmtSkeletonProve.pointer_cache_peek (!memo) term of
              SOME result => result
            | NONE =>
                let
                  val result =
                    if Term.aconv term boolSyntax.F then from_false theorem
                    else
                      case Lib.total boolSyntax.dest_disj term of
                        SOME (left, right) =>
                          Thm.DISJ_CASES theorem
                            (derive left (Thm.ASSUME left))
                            (derive right (Thm.ASSUME right))
                      | NONE => inject theorem
                  val _ = memo := SmtSkeletonProve.pointer_cache_insert
                    (!memo) term result
                in result end
        in Thm.DISCH source (derive source (Thm.ASSUME source)) end
      fun disjunction_aci () =
        let
          val (left, right) = boolSyntax.dest_eq target
          val _ = boolSyntax.is_disj left orelse
                  boolSyntax.is_disj right orelse
                  Term.aconv left boolSyntax.F orelse
                  Term.aconv right boolSyntax.F orelse
            raise ERR "aci_norm" "not a disjunction ACI equality"
          val forward = disjunction_implication left right
          val reverse = disjunction_implication right left
        in Drule.IMP_ANTISYM_RULE forward reverse end
      fun boolean_aci () =
        conjunction_aci ()
        handle Feedback.HOL_ERR _ => disjunction_aci ()
      fun word_ac () =
        let
          val (left, right) = boolSyntax.dest_eq target
          val (left_head, left_arguments) = boolSyntax.strip_comb left
          val (right_head, right_arguments) = boolSyntax.strip_comb right
          val _ = Term.same_const left_head right_head andalso
                  List.length left_arguments = 2 andalso
                  List.length right_arguments = 2 orelse
            raise ERR "aci_norm" "different word AC operators"
          val {Thy, Name, ...} = Term.dest_thy_const left_head
          val _ = Thy = "words" andalso
                  List.exists (fn saved => Name = saved)
                    ["word_and", "word_or", "word_xor"] orelse
            raise ERR "aci_norm" "not a word AC operator"
          (* AC abstraction also needs exact term indexing: a list makes a
             wide word expression repeatedly compare every accumulated atom.
             The structural dictionary is alpha-aware, matching the
             equivalence used by the final instantiated kernel theorem. *)
          val atoms = ref (Redblackmap.mkDict Term.compare :
            (Term.term, Term.term) Redblackmap.dict)
          fun atom term =
            case Redblackmap.peek (!atoms, term) of
              SOME variable => variable
            | NONE =>
                let
                  val variable = Term.genvar (Term.type_of term)
                  val _ = atoms := Redblackmap.insert
                    (!atoms, term, variable)
                in variable end
          fun abstract term =
            let val (head, arguments) = boolSyntax.strip_comb term in
              if Term.same_const head left_head andalso
                 List.length arguments = 2 then
                Term.list_mk_comb (head, List.map abstract arguments)
              else atom term
            end
            handle Feedback.HOL_ERR _ => atom term
          val generic_target = boolSyntax.mk_eq
            (abstract left, abstract right)
          val _ = Redblackmap.numItems (!atoms) <= 64 orelse
            raise ERR "aci_norm" "word AC schema has too many leaves"
          val laws =
            if Name = "word_and" then
              (wordsTheory.WORD_AND_ASSOC, wordsTheory.WORD_AND_COMM)
            else if Name = "word_or" then
              (wordsTheory.WORD_OR_ASSOC, wordsTheory.WORD_OR_COMM)
            else
              (wordsTheory.WORD_XOR_ASSOC, wordsTheory.WORD_XOR_COMM)
          val generic = Drule.EQT_ELIM
              (Conv.AC_CONV laws generic_target)
            handle Feedback.HOL_ERR _ =>
              wordsLib.WORD_ARITH_PROVE generic_target
          val substitutions = List.map
            (fn (term, variable) => {redex = variable, residue = term})
            (Redblackmap.listItems (!atoms))
        in Thm.INST substitutions generic end
    in
      if reflexive then Thm.REFL (Lib.fst (boolSyntax.dest_eq target))
      else (boolean_aci ()
        handle Feedback.HOL_ERR _ => word_ac ()
        handle Feedback.HOL_ERR _ =>
          profile "CPC(rung:word/aci_norm)" wordsLib.WORD_ARITH_PROVE target)
      handle Feedback.HOL_ERR holerr =>
        if SmtResource.is_resource_gate holerr then
          raise Feedback.HOL_ERR holerr
        else
          (profile "CPC(rung:seq/aci_norm)" SmtSeqProve.seq_prove target
           handle Feedback.HOL_ERR holerr =>
             if SmtResource.is_resource_gate holerr then
               raise Feedback.HOL_ERR holerr
             else
               (profile "CPC(rung:string/aci_norm)"
                  SmtStringProve.string_rewrite_prove target
                handle Feedback.HOL_ERR holerr =>
                  if SmtResource.is_resource_gate holerr then
                    raise Feedback.HOL_ERR holerr
                  else
                    profile "CPC(rung:word/aci_norm_tautology)"
                      (tautology "aci_norm") target))
    end

  fun replay_bv_xor_duplicate args =
    case args of
      word :: _ =>
        let
          val zero = wordsSyntax.mk_word
            (Arbnum.zero, fcpLib.index_to_num (wordsSyntax.dim_of word))
          val target = boolSyntax.mk_eq
            (wordsSyntax.mk_word_xor (word, word), zero)
        in
          Tactical.TAC_PROOF (([], target),
            bossLib.SIMP_TAC (bossLib.srw_ss()) [wordsTheory.WORD_XOR_CLAUSES])
        end
    | [] => raise ERR "bv-xor-duplicate" "expected a bit-vector argument"

  fun replay_bv_not_idemp args =
    let
      val word = expect_one_arg "bv-not-idemp" args
      val target = boolSyntax.mk_eq
        (wordsSyntax.mk_word_1comp (wordsSyntax.mk_word_1comp word), word)
    in
      Tactical.TAC_PROOF (([], target),
        bossLib.SIMP_TAC (bossLib.srw_ss()) [wordsTheory.WORD_NOT_NOT])
    end

  fun replay_bv_shl_by_const_0 args =
    case args of
      word :: _ =>
        let
          val zero = wordsSyntax.mk_word
            (Arbnum.zero, fcpLib.index_to_num (wordsSyntax.dim_of word))
          val target = boolSyntax.mk_eq
            (wordsSyntax.mk_word_lsl_bv (word, zero), word)
        in
          Tactical.TAC_PROOF (([], target),
            bossLib.SIMP_TAC (bossLib.srw_ss())
              [wordsTheory.word_lsl_bv_def, wordsTheory.w2n_n2w,
               wordsTheory.SHIFT_ZERO])
        end
    | [] => raise ERR "bv-shl-by-const-0" "expected a bit-vector argument"

  fun replay_bv_shl_by_const_2 args =
    case args of
      word :: amount :: _ =>
        let
          val amount = numSyntax.dest_numeral
            (intSyntax.dest_injected amount)
          val width = fcpLib.index_to_num (wordsSyntax.dim_of word)
          val amount_word = wordsSyntax.mk_word (amount, width)
          val zero = wordsSyntax.mk_word (Arbnum.zero, width)
          val target = boolSyntax.mk_eq
            (wordsSyntax.mk_word_lsl_bv (word, amount_word), zero)
        in
          Tactical.TAC_PROOF (([], target),
            bossLib.SIMP_TAC (bossLib.srw_ss())
              [wordsTheory.word_lsl_bv_def, wordsTheory.w2n_n2w,
               wordsTheory.LSL_LIMIT])
        end
    | _ => raise ERR "bv-shl-by-const-2"
        "expected a bit-vector and a constant shift amount"

  fun replay_bv_ashr_by_const_0 args =
    case args of
      word :: _ =>
        let
          val zero = wordsSyntax.mk_word
            (Arbnum.zero, fcpLib.index_to_num (wordsSyntax.dim_of word))
          val target = boolSyntax.mk_eq
            (wordsSyntax.mk_word_asr_bv (word, zero), word)
        in
          Tactical.TAC_PROOF (([], target),
            bossLib.SIMP_TAC (bossLib.srw_ss())
              [wordsTheory.word_asr_bv_def, wordsTheory.w2n_n2w,
               wordsTheory.SHIFT_ZERO])
        end
    | [] => raise ERR "bv-ashr-by-const-0" "expected a bit-vector argument"

  fun replay_bv_lshr_by_const_0 args =
    case args of
      word :: _ =>
        let
          val zero = wordsSyntax.mk_word
            (Arbnum.zero, fcpLib.index_to_num (wordsSyntax.dim_of word))
          val target = boolSyntax.mk_eq
            (wordsSyntax.mk_word_lsr_bv (word, zero), word)
        in
          Tactical.TAC_PROOF (([], target),
            bossLib.SIMP_TAC (bossLib.srw_ss())
              [wordsTheory.word_lsr_bv_def, wordsTheory.w2n_n2w,
               wordsTheory.SHIFT_ZERO])
        end
    | [] => raise ERR "bv-lshr-by-const-0" "expected a bit-vector argument"

  fun replay_bv_poly_norm args =
    let
      val target = expect_one_arg "bv_poly_norm" args
      val trace_large =
        OS.Process.getEnv "HOL4_CPC_REPLAY_SHAPE" = SOME "1"
      fun shape depth term =
        if depth = 0 then "..."
        else if Term.is_var term then "var"
        else if Term.is_const term then
          let val {Thy, Name, ...} = Term.dest_thy_const term
          in Thy ^ "$" ^ Name end
        else if Term.is_comb term then
          let val (head, arguments) = boolSyntax.strip_comb term
          in
            "(" ^ shape (depth - 1) head ^
            String.concat (List.map
              (fn argument => " " ^ shape (depth - 1) argument)
              arguments) ^ ")"
          end
        else "abs"
      val _ =
        case OS.Process.getEnv "HOL4_CPC_REPLAY_SHAPE" of
          SOME "1" => Feedback.HOL_MESG ("CPCBVSHAPE " ^ shape 5 target)
        | _ => ()
      fun traced name prover argument =
        let
          val timer = Timer.startRealTimer ()
          val _ = if trace_large then
              Feedback.HOL_MESG ("CPCBVROUTE start=" ^ name)
            else ()
          val theorem = prover argument
          val _ = if trace_large then
              Feedback.HOL_MESG
                ("CPCBVROUTE done=" ^ name ^ " time=" ^
                 Time.toString (Timer.checkRealTimer timer))
            else ()
        in theorem end
      fun schematic_one_bit () =
        let
          val (_, bit_equality) = boolSyntax.dest_eq target
          val (_, bit_term) = boolSyntax.dest_eq bit_equality
          val variable = Term.genvar Type.bool
          fun abstract term =
            if Portable.pointer_eq (term, bit_term) orelse
               Term.aconv term bit_term then variable
            else if Term.is_comb term then
              let val (operator, operand) = Term.dest_comb term
              in Term.mk_comb (abstract operator, abstract operand) end
            else term
          val template = abstract target
          val template_theorem = Tactical.TAC_PROOF (([], template),
            Tactical.THEN
              (Tactic.BOOL_CASES_TAC variable, bossLib.EVAL_TAC))
        in
          Thm.INST [{redex = variable, residue = bit_term}]
            template_theorem
        end
      fun schematic_boolean_skeleton () =
        let
          val atoms = ref ([] : (Term.term * Term.term) list)
          val memo = ref ([] : (Term.term * Term.term) list)
          fun is_boolean_structure term =
            Term.aconv term boolSyntax.T orelse Term.aconv term boolSyntax.F orelse
            boolSyntax.is_eq term orelse boolSyntax.is_conj term orelse
            boolSyntax.is_disj term orelse boolSyntax.is_neg term orelse
            boolSyntax.is_imp term orelse boolSyntax.is_cond term
          fun atom term =
            case List.find (fn (saved, _) => Term.aconv saved term) (!atoms) of
              SOME (_, variable) => variable
            | NONE =>
                let val variable = Term.genvar Type.bool in
                  atoms := (term, variable) :: !atoms;
                  variable
                end
          fun abstract term =
            case List.find
                (fn (saved, _) => Portable.pointer_eq (term, saved)) (!memo) of
              SOME (_, result) => result
            | NONE =>
                let
                  val result =
                    if Term.type_of term = Type.bool andalso
                       not (is_boolean_structure term) then atom term
                    else if Term.is_comb term then
                      let val (operator, operand) = Term.dest_comb term
                      in Term.mk_comb (abstract operator, abstract operand) end
                    else term
                  val _ = memo := (term, result) :: !memo
                in result end
          val template = abstract target
          val theorem = blastLib.BBLAST_PROVE template
          val substitutions = List.map
            (fn (term, variable) => {redex = variable, residue = term})
            (!atoms)
        in Thm.INST substitutions theorem end
        handle HolSatLib.SAT_cex _ =>
          raise ERR "bv_poly_norm" "Boolean skeleton is not valid"
      fun schematic_word_constructors () =
        let
          val (left_word, _) = boolSyntax.dest_eq target
          val _ = wordsSyntax.dim_of left_word
          fun singleton_bit word =
            let
              val (bit, then_word, else_word) = boolSyntax.dest_cond word
              val then_value = wordsSyntax.dest_word_literal then_word
              val else_value = wordsSyntax.dest_word_literal else_word
            in
              if fcpLib.index_to_num (wordsSyntax.dim_of word) = Arbnum.one
                 andalso then_value = Arbnum.one andalso
                 else_value = Arbnum.zero then SOME bit
              else NONE
            end
            handle Feedback.HOL_ERR _ => NONE
          datatype structural_key =
              StructuralVariable of string * Type.hol_type
            | StructuralConstant of Term.term
            | StructuralApplication of int * int
            | StructuralOpaque of Term.term
          val structural_nodes = ref ([] : (structural_key * int) list)
          val structural_memo = ref ([] : (Term.term * int) list)
          val next_structural_id = ref 0
          fun same_key (StructuralVariable (left_name, left_type),
                        StructuralVariable (right_name, right_type)) =
                left_name = right_name andalso
                Type.compare (left_type, right_type) = EQUAL
            | same_key (StructuralConstant left, StructuralConstant right) =
                Term.same_const left right andalso
                Type.compare (Term.type_of left, Term.type_of right) = EQUAL
            | same_key (StructuralApplication (left_operator, left_operand),
                        StructuralApplication
                          (right_operator, right_operand)) =
                left_operator = right_operator andalso
                left_operand = right_operand
            | same_key (StructuralOpaque left, StructuralOpaque right) =
                Portable.pointer_eq (left, right)
            | same_key _ = false
          fun intern key =
            case List.find
                (fn (saved, _) => same_key (key, saved)) (!structural_nodes) of
              SOME (_, identity) => identity
            | NONE =>
                let val identity = !next_structural_id in
                  next_structural_id := identity + 1;
                  structural_nodes := (key, identity) :: !structural_nodes;
                  identity
                end
          fun structural_id term =
            case List.find
                (fn (saved, _) => Portable.pointer_eq (term, saved))
                (!structural_memo) of
              SOME (_, identity) => identity
            | NONE =>
                let
                  val key =
                    if Term.is_var term then
                      StructuralVariable (Term.dest_var term)
                    else if Term.is_const term then StructuralConstant term
                    else if Term.is_comb term then
                      let val (operator, operand) = Term.dest_comb term
                      in StructuralApplication
                        (structural_id operator, structural_id operand) end
                    else StructuralOpaque term
                  val identity = intern key
                  val _ = structural_memo :=
                    (term, identity) :: !structural_memo
                in identity end
          val seen = ref ([] : Term.term list)
          fun collect term =
            if List.exists
                 (fn saved => Portable.pointer_eq (term, saved)) (!seen) then
              []
            else
              let val _ = seen := term :: !seen in
                case singleton_bit term of
                  SOME bit => [bit]
                | NONE =>
                    if Term.is_comb term then
                      let val (operator, operand) = Term.dest_comb term
                      in collect operator @ collect operand end
                    else []
              end
          fun distinct (bit, bits) =
            if List.exists
                 (fn saved => structural_id bit = structural_id saved) bits then
              bits
            else bit :: bits
          val constructor_source =
            case singleton_bit left_word of
              SOME condition => condition
            | NONE => left_word
          val bits = List.rev
            (List.foldl distinct [] (collect constructor_source))
          val _ =
            case OS.Process.getEnv "HOL4_CPC_REPLAY_SHAPE" of
              SOME "1" => Feedback.HOL_MESG
                ("CPCBVWORD1 bits=" ^ Int.toString (List.length bits))
            | _ => ()
          val _ = not (List.null bits) orelse raise ERR "bv_poly_norm"
            "word constructor schema found no Boolean constructors"
          val _ = List.length bits <= 16 orelse
            raise ERR "bv_poly_norm"
              "word constructor schema exceeds sixteen Boolean inputs"
          val variables = List.map (fn _ => Term.genvar Type.bool) bits
          val replacements = ListPair.mapEq
            (fn (bit, variable) => (structural_id bit, variable))
            (bits, variables)
          fun replacement term pairs =
            case pairs of
              [] => NONE
            | (identity, variable) :: rest =>
                if structural_id term = identity then SOME variable
                else replacement term rest
          val memo = ref ([] : (Term.term * Term.term) list)
          fun abstract term =
            case List.find
                (fn (saved, _) => Portable.pointer_eq (term, saved)) (!memo) of
              SOME (_, result) => result
            | NONE =>
                let
                  val result =
                    case replacement term replacements of
                      SOME variable => variable
                    | NONE =>
                        if Term.is_comb term then
                          let val (operator, operand) = Term.dest_comb term
                          in Term.mk_comb
                            (abstract operator, abstract operand) end
                        else term
                  val _ = memo := (term, result) :: !memo
                in result end
          val template = abstract target
          val template_nodes = SmtResource.dag_nodes_up_to 257 template
          val _ =
            case OS.Process.getEnv "HOL4_CPC_REPLAY_SHAPE" of
              SOME "1" => Feedback.HOL_MESG
                ("CPCBVWORD1 nodes=" ^ Int.toString template_nodes ^
                 " shape=" ^ shape 8 template)
            | _ => ()
          val _ = SmtResource.check_dag_size_with_limit
            "BitVector" "word-constructor-schema" 256 template_nodes
          fun prove_template () =
            let
              val graph = SmtWordGraph.normalize template
                handle Conv.UNCHANGED => Thm.REFL template
              val graph_residue = boolSyntax.rhs (Thm.concl graph)
              val simplified = simpLib.SIMP_CONV
                (simpLib.++ (bossLib.srw_ss(), wordsLib.WORD_BIT_EQ_ss))
                [HolSmtTheory.xor_def, wordsTheory.word_compare_def]
                graph_residue
                handle Conv.UNCHANGED => Thm.REFL graph_residue
              val normalized = Thm.TRANS graph simplified
              val residue = boolSyntax.rhs (Thm.concl normalized)
              val residue_theorem =
                if Term.aconv residue boolSyntax.T then boolTheory.TRUTH
                else tautLib.TAUT_PROVE residue
                  handle Feedback.HOL_ERR _ => blastLib.BBLAST_PROVE residue
            in Thm.EQ_MP (Thm.SYM normalized) residue_theorem end
          val template_theorem = prove_template ()
          val substitutions = ListPair.mapEq
            (fn (variable, bit) => {redex = variable, residue = bit})
            (variables, bits)
        in Thm.INST substitutions template_theorem end
      fun schematic_bvite_words () =
        let
          fun is_holsmt_xor term =
            let
              val (operator, arguments) = boolSyntax.strip_comb term
              val {Thy, Name, ...} = Term.dest_thy_const operator
            in Thy = "HolSmt" andalso Name = "xor" andalso
               List.length arguments = 2 end
            handle Feedback.HOL_ERR _ => false
          val boolean_template = target
          fun fp_projection_conversion term =
            (SmtFpGraph.convert_word_projection term
             handle Conv.UNCHANGED =>
               let
                 val (head, arguments) = boolSyntax.strip_comb term
                 val {Thy, ...} = Term.dest_thy_const head
                 val _ = Thy = "fcp" orelse raise Conv.UNCHANGED
                 fun is_word_compare argument =
                   let
                     val (argument_head, _) =
                       boolSyntax.strip_comb argument
                     val {Thy, Name, ...} =
                       Term.dest_thy_const argument_head
                   in Thy = "words" andalso Name = "word_compare" end
                   handle Feedback.HOL_ERR _ => false
               in
                 if List.exists is_word_compare arguments then
                   Conv.REWR_CONV
                     smtfloatReplayRoundingTheory.word_compare_index term
                 else raise Conv.UNCHANGED
               end
             handle Empty => raise Conv.UNCHANGED
                  | Feedback.HOL_ERR holerr =>
                      if SmtResource.is_resource_gate holerr then
                        raise Feedback.HOL_ERR holerr
                      else raise Conv.UNCHANGED)
          val first_blast =
            SmtWordGraph.normalize_with_node_conversion
              fp_projection_conversion boolean_template
          val first_residue = boolSyntax.rhs (Thm.concl first_blast)
          val second_blast =
            (SmtWordGraph.normalize_with_node_conversion
               fp_projection_conversion first_residue
             handle Conv.UNCHANGED => Thm.REFL first_residue)
          val blasted = Thm.TRANS first_blast second_blast
          val blast_residue = boolSyntax.rhs (Thm.concl blasted)
          val circuit_memo =
            ref ([] : (Term.term * Term.term) list)
          val circuit_substitutions =
            ref ([] : {redex : Term.term, residue : Term.term} list)
          val circuit_definitions =
            ref ([] : (Term.term * Term.term) list)
          fun circuit_variable term =
            let
              val variable = Term.genvar Type.bool
              val _ = circuit_substitutions :=
                {redex = variable, residue = term} ::
                !circuit_substitutions
            in variable end
          fun circuit_leaf term = circuit_variable term
          fun circuit term =
            case List.find
                (fn (saved, _) => Portable.pointer_eq (term, saved) orelse
                  Term.aconv term saved)
                (!circuit_memo) of
              SOME (_, result) => result
            | NONE =>
                let
                  fun internal skeleton =
                    let
                      val variable = circuit_variable term
                      val _ = circuit_definitions :=
                        (term, boolSyntax.mk_eq (variable, skeleton)) ::
                        !circuit_definitions
                    in variable end
                  val result =
                    if Term.aconv term boolSyntax.T orelse
                       Term.aconv term boolSyntax.F then term
                    else if boolSyntax.is_neg term then
                      internal (boolSyntax.mk_neg
                        (circuit (boolSyntax.dest_neg term)))
                    else if boolSyntax.is_conj term then
                      let val (left, right) = boolSyntax.dest_conj term
                      in internal (boolSyntax.mk_conj
                        (circuit left, circuit right)) end
                    else if boolSyntax.is_disj term then
                      let val (left, right) = boolSyntax.dest_disj term
                      in internal (boolSyntax.mk_disj
                        (circuit left, circuit right)) end
                    else if boolSyntax.is_imp term then
                      let val (left, right) = boolSyntax.dest_imp term
                      in internal (boolSyntax.mk_imp
                        (circuit left, circuit right)) end
                    else if boolSyntax.is_eq term then
                      let
                        val (left, right) = boolSyntax.dest_eq term
                      in
                        if Term.type_of left = Type.bool then
                          internal (boolSyntax.mk_eq
                            (circuit left, circuit right))
                        else circuit_leaf term
                      end
                    else if boolSyntax.is_cond term then
                      let
                        val (condition, then_term, else_term) =
                          boolSyntax.dest_cond term
                      in
                        if Term.type_of then_term = Type.bool then
                          internal (boolSyntax.mk_cond
                            (circuit condition, circuit then_term,
                             circuit else_term))
                        else circuit_leaf term
                      end
                    else if is_holsmt_xor term then
                      let
                        val (left, right) = case boolSyntax.strip_comb term of
                          (_, [left, right]) => (left, right)
                        | _ => raise Fail "malformed xor"
                      in internal (boolSyntax.mk_neg (boolSyntax.mk_eq
                        (circuit left, circuit right))) end
                    else circuit_leaf term
                  val _ = circuit_memo := (term, result) :: !circuit_memo
                in result end
          val circuit_root = circuit blast_residue
          val definitions = List.rev (!circuit_definitions)
          val circuit_goal = List.foldr
            (fn ((_, definition), body) =>
              boolSyntax.mk_imp (definition, body))
            circuit_root definitions
          val circuit_theorem = HolSatLib.SAT_PROVE circuit_goal
            handle HolSatLib.SAT_cex _ =>
              raise ERR "bv_poly_norm" "Boolean circuit is not valid"
          val instantiated_circuit = Thm.INST (!circuit_substitutions)
            circuit_theorem
          fun discharge ((term, _), (index, theorem)) =
            let
              val definition_theorem =
                if is_holsmt_xor term then
                  Conv.REWR_CONV HolSmtTheory.xor_def term
                else Thm.REFL term
            in (index + 1, Thm.MP theorem definition_theorem) end
          val (_, residue_theorem) = List.foldl discharge
            (0, instantiated_circuit) definitions
          val generalized_theorem = Thm.EQ_MP (Thm.SYM blasted)
            residue_theorem
        in generalized_theorem end
      fun schematic_bvite () =
        let
          val (left_word, _) = boolSyntax.dest_eq target
          val (condition, then_word, else_word) =
            boolSyntax.dest_cond left_word
          fun collect_word_bits term =
            case Lib.total boolSyntax.dest_cond term of
              SOME (bit, _, _) =>
                if Term.type_of term = Type.bool then collect_word_bits bit
                else [bit]
            | NONE =>
                if Term.is_comb term then
                  let val (operator, operand) = Term.dest_comb term
                  in collect_word_bits operator @ collect_word_bits operand end
                else []
          fun insert (bit, bits) =
            if List.exists (fn saved => Term.aconv saved bit) bits then bits
            else bit :: bits
          val bits = List.rev (List.foldl insert []
            (collect_word_bits condition @ collect_word_bits then_word @
             collect_word_bits else_word))
          val _ = null bits andalso
            raise ERR "bv_poly_norm" "missing bvite bit encodings"
          val _ = List.length bits <= 8 orelse
            raise ERR "bv_poly_norm"
              "bvite schema exceeds bounded Boolean case split"
          val variables = List.map (fn _ => Term.genvar Type.bool) bits
          fun replacement term pairs =
            case pairs of
              [] => NONE
            | (bit, variable) :: rest =>
                if Term.aconv term bit then SOME variable
                else replacement term rest
          fun abstract term =
            case replacement term (ListPair.zip (bits, variables)) of
              SOME variable => variable
            | NONE =>
                if Term.is_comb term then
                  let val (operator, operand) = Term.dest_comb term
                  in Term.mk_comb (abstract operator, abstract operand) end
                else term
          val template = abstract target
          val template_theorem = Tactical.TAC_PROOF (([], template),
            Tactical.THEN
              (Tactical.EVERY (List.map Tactic.BOOL_CASES_TAC variables),
               bossLib.EVAL_TAC))
          val substitutions = ListPair.mapEq
            (fn (variable, bit) => {redex = variable, residue = bit})
            (variables, bits)
        in
          Thm.INST substitutions template_theorem
        end
      fun schematic_bvcomp () =
        let
          val (left_word, _) = boolSyntax.dest_eq target
          val (left_operand, right_operand) =
            wordsSyntax.dest_word_compare left_word
          fun word_bits term =
            case Lib.total boolSyntax.dest_cond term of
              SOME (bit, _, _) =>
                if Term.type_of term = Type.bool then [] else [bit]
            | NONE =>
                if Term.is_comb term then
                  let val (operator, operand) = Term.dest_comb term
                  in word_bits operator @ word_bits operand end
                else []
          val bits = List.map CPC_ProofParser.intern_cpc_term
            (word_bits left_operand @ word_bits right_operand)
          val _ = null bits andalso
            raise ERR "bv_poly_norm" "missing bit-vector comparison bits"
          val variables = List.map (fn _ => Term.genvar Type.bool) bits
          fun replacement term [] [] = NONE
            | replacement term (bit :: rest_bits)
                (variable :: rest_variables) =
                if Portable.pointer_eq (term, bit) orelse
                   Term.aconv term bit then SOME variable
                else replacement term rest_bits rest_variables
            | replacement _ _ _ = raise ERR "bv_poly_norm"
                "bit abstraction arity mismatch"
          fun abstract term =
            case replacement term bits variables of
              SOME variable => variable
            | NONE =>
                if Term.is_comb term then
                  let val (operator, operand) = Term.dest_comb term
                  in Term.mk_comb (abstract operator, abstract operand) end
                else term
          val template = abstract target
          val template_theorem = Tactical.TAC_PROOF (([], template),
            Tactical.THEN
              (Tactical.EVERY (List.map Tactic.BOOL_CASES_TAC variables),
               bossLib.EVAL_TAC))
          val substitutions = ListPair.mapEq
            (fn (variable, bit) => {redex = variable, residue = bit})
            (variables, bits)
        in
          Thm.INST substitutions template_theorem
        end
      fun boolean_word_normalization () =
        let
          val normalized = simpLib.SIMP_CONV (bossLib.srw_ss())
            [HolSmtTheory.xor_def] target
            handle Conv.UNCHANGED => Thm.REFL target
          val residue = boolSyntax.rhs (Thm.concl normalized)
          val residue_theorem = blastLib.BBLAST_PROVE residue
        in
          Thm.EQ_MP (Thm.SYM normalized) residue_theorem
        end
        handle HolSatLib.SAT_cex _ =>
          raise ERR "bv_poly_norm" "Boolean-normalized target is not valid"
      fun graph_normalization () =
        let
          val graph = SmtWordGraph.normalize target
            handle Conv.UNCHANGED => Thm.REFL target
          val graph_residue = boolSyntax.rhs (Thm.concl graph)
          val simplified = simpLib.SIMP_CONV
            (simpLib.++ (bossLib.srw_ss(), wordsLib.WORD_BIT_EQ_ss))
            [wordsTheory.word_compare_def] graph_residue
            handle Conv.UNCHANGED => Thm.REFL graph_residue
          val normalized = Thm.TRANS graph simplified
          val residue = boolSyntax.rhs (Thm.concl normalized)
          val residue_theorem =
            if Term.aconv residue boolSyntax.T then boolTheory.TRUTH
            else tautLib.TAUT_PROVE residue
              handle Feedback.HOL_ERR _ => blastLib.BBLAST_PROVE residue
        in
          Thm.EQ_MP (Thm.SYM normalized) residue_theorem
        end
        handle HolSatLib.SAT_cex _ =>
          raise ERR "bv_poly_norm" "graph-normalized residue is not valid"
      fun bitblast_equivalence () =
        let
          val (word_equality, bit_conjunction) = boolSyntax.dest_eq target
          val _ = Term.type_of word_equality = Type.bool orelse
            raise ERR "bv_poly_norm" "expected a Boolean word equality"
          val word_thm = profile "CPC(rung:word/bitblast_word_arith)"
            wordsLib.WORD_ARITH_PROVE word_equality
          fun prove_bit tm = Tactical.TAC_PROOF (([], tm),
            Tactical.THEN
              (bossLib.SIMP_TAC (bossLib.srw_ss())
                 [HolSmtTheory.xor_def], tautLib.TAUT_TAC))
          fun prove_bits tm =
            let val (left, right) = boolSyntax.dest_conj tm in
              Thm.CONJ (prove_bits left) (prove_bits right)
            end handle Feedback.HOL_ERR _ => prove_bit tm
          val bits_thm = prove_bits bit_conjunction
        in
          (* Both sides of this Boolean equality have just been established.
             Build the equality through truth directly: asking Taut to expand
             the bit-blasted operands makes this otherwise constant-size CPC
             step grow prohibitively. *)
          Thm.TRANS (Drule.EQT_INTRO word_thm)
            (Thm.SYM (Drule.EQT_INTRO bits_thm))
        end
        handle HolSatLib.SAT_cex _ =>
          raise ERR "bv_poly_norm" "bitblast equivalence is not valid"
      fun word_arithmetic () = wordsLib.WORD_ARITH_PROVE target
        handle HolSatLib.SAT_cex _ =>
          raise ERR "bv_poly_norm" "word arithmetic target is not valid"
      fun boolean_cases () =
        let
          val variables = List.filter
            (fn variable => Term.type_of variable = Type.bool)
            (Term.free_vars target)
        in
          Tactical.TAC_PROOF (([], target), Tactical.THEN
            (Tactical.EVERY (List.map Tactic.BOOL_CASES_TAC variables),
             bossLib.EVAL_TAC))
        end
      fun diagnosed_graph () = graph_normalization ()
    in
      traced "schematic_one_bit"
        (profile "CPC(rung:word/poly_norm_schematic_one_bit)"
          schematic_one_bit) ()
      handle Feedback.HOL_ERR _ =>
      traced "schematic_word_constructors"
        (profile "CPC(rung:word/poly_norm_schematic_word_constructors)"
          schematic_word_constructors) ()
      handle Feedback.HOL_ERR _ =>
      traced "schematic_bvite"
        (profile "CPC(rung:word/poly_norm_schematic_bvite)"
          schematic_bvite) ()
      handle Feedback.HOL_ERR _ =>
      traced "schematic_bvite_words"
        (profile "CPC(rung:word/poly_norm_schematic_bvite_words)"
          schematic_bvite_words) ()
      handle Feedback.HOL_ERR _ =>
      traced "schematic_bvcomp"
        (profile "CPC(rung:word/poly_norm_schematic_bvcomp)"
          schematic_bvcomp) ()
      handle Feedback.HOL_ERR _ =>
      traced "graph" (profile "CPC(rung:word/poly_norm_graph)"
        diagnosed_graph) ()
      handle Feedback.HOL_ERR _ =>
      traced "boolean_word"
        (profile "CPC(rung:word/poly_norm_boolean_word)"
          boolean_word_normalization) ()
      handle Feedback.HOL_ERR _ =>
      traced "bitblast_equivalence"
        (profile "CPC(rung:word/bitblast_equivalence)"
          bitblast_equivalence) ()
      handle Feedback.HOL_ERR _ =>
      traced "arith" (profile "CPC(rung:word/poly_norm_arith)"
        word_arithmetic) ()
      handle Feedback.HOL_ERR _ =>
      traced "boolean_cases"
        (profile "CPC(rung:word/poly_norm_boolean_cases)"
          boolean_cases) ()
      handle Feedback.HOL_ERR _ =>
        profile "CPC(rung:word/poly_norm_full_simp)" Tactical.TAC_PROOF
          (([], target),
          Tactical.THEN
            (bossLib.FULL_SIMP_TAC
               (simpLib.++ (simpLib.++ (simpLib.++
                 (bossLib.list_ss, boolSimps.COND_elim_ss), wordsLib.WORD_ss),
                wordsLib.WORD_BIT_EQ_ss)) [boolTheory.EQ_SYM_EQ],
             tautLib.TAUT_TAC))
    end

  fun replay_quant_unused_vars args =
    let val target = expect_one_arg "quant-unused-vars" args in
      Tactical.TAC_PROOF (([], target),
        bossLib.SIMP_TAC (bossLib.srw_ss()) [])
    end

  fun replay_quant_rewrite name args =
    let
      val target = expect_one_arg name args
    in
      if name = "quant-miniscope-and" then
        Tactical.TAC_PROOF (([], target),
          bossLib.SIMP_TAC bossLib.bool_ss [boolTheory.FORALL_AND_THM])
      else if name = "quant-miniscope-or" then
        Tactical.TAC_PROOF (([], target),
          bossLib.SIMP_TAC bossLib.bool_ss
            [boolTheory.LEFT_FORALL_OR_THM, boolTheory.RIGHT_FORALL_OR_THM])
      else if name = "quant-var-elim-eq" then
        Tactical.TAC_PROOF (([], target),
          bossLib.SIMP_TAC bossLib.bool_ss
            [Thm.SYM boolTheory.IMP_DISJ_THM,
             boolTheory.UNWIND_FORALL_THM1,
             boolTheory.UNWIND_FORALL_THM2])
      else Tactical.TAC_PROOF (([], target),
        bossLib.SIMP_TAC (bossLib.srw_ss()) [boolTheory.IMP_DISJ_THM])
    end

  fun replay_alpha_equiv args =
    let
      val source = case args of tm :: _ => tm
        | [] => raise ERR "alpha_equiv" "expected a quantified source term"
      fun replay mk_quant strip_quant =
        let
          val (bound_vars, body) = strip_quant source
          val n = List.length bound_vars
          val mappings = List.drop (args, 1)
          val _ = List.length mappings = 2 * n orelse
            raise ERR "alpha_equiv" "binder mapping arity does not match source"
          val old_vars = List.take (mappings, n)
          val new_vars = List.drop (mappings, n)
          val _ = ListPair.allEq (fn (bound, old) =>
            Term.aconv bound old) (bound_vars, old_vars) orelse
            raise ERR "alpha_equiv" "source binders do not match CPC mapping"
          val _ = List.all Term.is_var new_vars orelse
            raise ERR "alpha_equiv" "target CPC binders are not variables"
          val rhs = mk_quant (new_vars,
            Term.subst (ListPair.map (fn (old, new) =>
              {redex = old, residue = new}) (old_vars, new_vars)) body)
        in Thm.ALPHA source rhs end
    in
      replay boolSyntax.list_mk_forall boolSyntax.strip_forall
      handle Feedback.HOL_ERR _ =>
        replay boolSyntax.list_mk_exists boolSyntax.strip_exists
      handle Feedback.HOL_ERR _ =>
        replay Term.list_mk_abs Term.strip_abs
    end

  (* If the branches of a Boolean conditional are complements, cvc5 rewrites
     the conditional to equality between its condition and then-branch.  The
     sole premise records that complement relation; propositional replay
     checks the precise general shape. *)
  fun replay_ite_neg_branch args prems =
    case args of
      [condition, then_term, else_term] =>
        let
          val premise = expect_one_premise "ite-neg-branch" prems
          val target = boolSyntax.mk_eq
            (boolSyntax.mk_cond (condition, then_term, else_term),
             boolSyntax.mk_eq (condition, then_term))
        in
          tautological_consequence premise target
          handle Feedback.HOL_ERR _ =>
            raise ERR "ite-neg-branch"
              "premise does not establish complementary Boolean branches"
        end
    | _ => raise ERR "ite-neg-branch"
        "expected condition, then-branch, and else-branch arguments"

  fun replay_bv_poly_norm_eq args =
    tautology "bv_poly_norm_eq" (expect_one_arg "bv_poly_norm_eq" args)

  fun replay_not_implies_elim2 prems =
    let
      val premise = expect_one_premise "not_implies_elim2" prems
      val implication = boolSyntax.dest_neg (Thm.concl premise)
      val (_, conclusion) = boolSyntax.dest_imp implication
    in tautological_consequence premise (boolSyntax.mk_neg conclusion) end

  fun replay_not_implies_elim1 prems =
    let
      val premise = expect_one_premise "not_implies_elim1" prems
      val implication = boolSyntax.dest_neg (Thm.concl premise)
      val (antecedent, _) = boolSyntax.dest_imp implication
    in tautological_consequence premise antecedent end

  fun replay_implies_elim prems =
    let
      val premise = expect_one_premise "implies_elim" prems
      val (antecedent, consequent) = boolSyntax.dest_imp (Thm.concl premise)
      val law = Drule.ISPECL [antecedent, consequent]
        boolTheory.IMP_DISJ_THM
    in Thm.EQ_MP law premise end

  fun replay_factoring prems =
    let
      val premise = expect_one_premise "factoring" prems
      fun same left right = Portable.pointer_eq (left, right)
      fun unique [] = []
        | unique (tm :: rest) =
            tm :: unique (List.filter (fn other => not (same tm other)) rest)
      fun mk_disj [tm] = tm
        | mk_disj (tm :: rest) = boolSyntax.mk_disj (tm, mk_disj rest)
        | mk_disj [] = raise ERR "factoring" "empty CPC factoring clause"
      val conclusion = mk_disj
        (unique (boolSyntax.strip_disj (Thm.concl premise)))
      fun contains target literal =
        same target literal orelse
        (case Lib.total boolSyntax.dest_disj target of
           SOME (left, right) =>
             contains left literal orelse contains right literal
         | NONE => false)
      fun introduce theorem target =
        if same (Thm.concl theorem) target then theorem
        else
          let val (left, right) = boolSyntax.dest_disj target in
            if contains left (Thm.concl theorem) then
              Thm.DISJ1 (introduce theorem left) right
            else Thm.DISJ2 left (introduce theorem right)
          end
      fun derive theorem =
        if contains conclusion (Thm.concl theorem) then
          introduce theorem conclusion
        else
          let val (left, right) =
            boolSyntax.dest_disj (Thm.concl theorem)
          in
            Thm.DISJ_CASES theorem
              (derive (Thm.ASSUME left))
              (derive (Thm.ASSUME right))
          end
    in derive premise end

  fun mk_disj_terms [tm] = tm
    | mk_disj_terms (tm :: rest) = boolSyntax.mk_disj (tm, mk_disj_terms rest)
    | mk_disj_terms [] = boolSyntax.F

  (* The kernel comparison preserves physical DAG sharing and uses an
     operation-local identity memo.  Reuse it rather than retain a second
     alpha-equivalence engine and recount each candidate's entire DAG. *)
  val shared_aconv = Term.aconv

  val boolean_dag_bucket_count = 16381

  fun boolean_dag_string_hash string =
    let
      fun loop index hash =
        if index = String.size string then hash
        else loop (index + 1)
          ((hash * 33 + Char.ord (String.sub (string, index))) mod
           boolean_dag_bucket_count)
    in loop 0 5381 end

  fun boolean_dag_term_hash 0 term =
        if Term.is_var term then
          (boolean_dag_string_hash (#1 (Term.dest_var term)) + 11) mod
          boolean_dag_bucket_count
        else if Term.is_const term then
          (boolean_dag_string_hash (#Name (Term.dest_thy_const term)) + 17)
          mod boolean_dag_bucket_count
        else if Term.is_abs term then 23
        else 29
    | boolean_dag_term_hash depth term =
        if Term.is_comb term then
          (41 * boolean_dag_term_hash (depth - 1) (Term.rator term) +
           67 * boolean_dag_term_hash (depth - 1) (Term.rand term) + 31)
          mod boolean_dag_bucket_count
        else if Term.is_abs term then
          (73 * boolean_dag_term_hash (depth - 1) (Term.body term) + 37)
          mod boolean_dag_bucket_count
        else boolean_dag_term_hash 0 term

  (* Prove a shared Boolean circuit without expanding its unfolded tree.
     Every internal node receives a Tseitin variable; instantiation followed
     by reflexivity discharges the exact defining equations. *)
  fun prove_boolean_dag_tautology_with_leaf_conversion_using
      chunk_depth prover stops leaf_conversion label goal =
    let
      val bucket_count = boolean_dag_bucket_count
      fun bucket_index term = boolean_dag_term_hash 4 term
      val graph = SmtBooleanGraph.new
        {chunk_depth = chunk_depth, stops = stops,
         stop_conversion = leaf_conversion, leaf = fn term => term,
         unfold = fn _ => NONE}
      val root = #circuit graph goal
      val definitions = #definitions graph ()
      val substitutions = #substitutions graph ()
      val definition_term = boolSyntax.lhs (Thm.concl
        (SmtCircuitSat.balanced_equivalences
          (List.map (fn (_, definition, _) => Thm.REFL definition)
            definitions)))
      val template =
        if List.null definitions then root
        else boolSyntax.mk_imp (definition_term, root)
      val _ = List.length definitions <= 1200 orelse
        raise ERR "circuit" "Boolean circuit exceeds the direct SAT limit"
      val law = SmtResource.with_bitblast_step_time label prover template
      val theorem = Thm.INST substitutions law
      val result =
        if List.null definitions then theorem
        else
          let
            val antecedent = #1 (boolSyntax.dest_imp (Thm.concl theorem))
            fun prove_definition ((term, _, proof), instantiated) =
              let
                val base =
                  case proof of
                    SOME theorem =>
                      SmtSkeletonProve.anchor_left term theorem
                  | NONE => Thm.REFL term
              in Thm.EQ_MP (Thm.REFL instantiated) base end
            val instantiated_definitions = boolSyntax.strip_conj antecedent
            val proofs = ListPair.mapEq prove_definition
              (definitions, instantiated_definitions)
            val conjunction = SmtCircuitSat.balanced_conjunction proofs
          in Thm.MP theorem (Thm.EQ_MP (Thm.REFL antecedent) conjunction) end
      val alignment_memo = Array.array
        (bucket_count, [] : (Term.term * Term.term * Thm.thm) list)
      fun alignment_index left right =
        (boolean_dag_term_hash 3 left * 67 +
         boolean_dag_term_hash 3 right) mod bucket_count
      fun alignment_peek left right =
        case List.find (fn (saved_left, saved_right, _) =>
            Portable.pointer_eq (saved_left, left) andalso
            Portable.pointer_eq (saved_right, right))
            (Array.sub (alignment_memo, alignment_index left right)) of
          SOME (_, _, theorem) => SOME theorem
        | NONE => NONE
      fun alignment_insert left right theorem =
        let val index = alignment_index left right in
          Array.update
            (alignment_memo, index,
             (left, right, theorem) :: Array.sub (alignment_memo, index))
        end
      fun align left right =
        case alignment_peek left right of
          SOME theorem => theorem
        | NONE =>
            let
              val theorem =
                if Portable.pointer_eq (left, right) then Thm.REFL left
                else if Term.is_comb left andalso Term.is_comb right then
                  Thm.MK_COMB
                    (align (Term.rator left) (Term.rator right),
                     align (Term.rand left) (Term.rand right))
                else if Term.aconv left right then
                  SmtSkeletonProve.anchor_right right (Thm.REFL left)
                else raise ERR "circuit"
                  "instantiated Boolean circuit endpoint differs"
              val _ = alignment_insert left right theorem
            in theorem end
      val exact = Thm.EQ_MP (align (Thm.concl result) goal) result
    in exact end

  fun prove_boolean_dag_tautology_with_leaf_conversion
      stops leaf_conversion label goal =
    prove_boolean_dag_tautology_with_leaf_conversion_using
      NONE HolSatLib.SAT_PROVE stops leaf_conversion label goal

  fun prove_boolean_dag_tautology_compact label goal =
    prove_boolean_dag_tautology_with_leaf_conversion_using
      (SOME 3) HolSatLib.SAT_PROVE [] (fn _ => NONE) label goal

  fun prove_boolean_dag_tautology_stopping stops label goal =
    prove_boolean_dag_tautology_with_leaf_conversion stops
      (fn _ => NONE) label goal

  fun prove_boolean_dag_tautology label goal =
    prove_boolean_dag_tautology_stopping [] label goal

  fun xor_graph_tautology target =
    let
      val normalization =
        profile "CPC(xor_graph:simplify)"
          (simpLib.SIMP_CONV (bossLib.srw_ss())
            [HolSmtTheory.xor_def]) target
        handle Conv.UNCHANGED => Thm.REFL target
      val residue = boolSyntax.rhs (Thm.concl normalization)
      val law =
        if Term.aconv residue boolSyntax.T then boolTheory.TRUTH
        else
          (profile "CPC(xor_graph:sat)"
             (prove_boolean_dag_tautology "cpc-trans-xor-graph")
             residue
           handle HolSatLib.SAT_cex _ =>
             raise ERR "xor_graph_tautology"
               "normalized bridge is not propositionally valid")
    in
      Thm.EQ_MP (Thm.SYM normalization) law
    end

  fun prove_word_graph_tautology_uncached feature target =
    let
      fun trace_stage stage =
        if OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" = SOME "full" then
          (Feedback.HOL_MESG ("CPC word graph " ^ stage);
           TextIO.flushOut TextIO.stdOut)
        else ()
      fun node_conversion term =
        SmtFpGraph.convert_word_projection term
        handle Conv.UNCHANGED =>
          (Conv.REWR_CONV
             smtfloatReplayRoundingTheory.word_compare_index term
           handle Feedback.HOL_ERR _ =>
             (Conv.REWR_CONV HolSmtTheory.xor_def term
              handle Feedback.HOL_ERR _ => raise Conv.UNCHANGED))
             | Empty => raise Conv.UNCHANGED
             | Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else raise Conv.UNCHANGED
      fun normalize_all term =
        let
          fun loop 0 theorem = theorem
            | loop remaining theorem =
                let
                  val residue = boolSyntax.rhs (Thm.concl theorem)
                  val next =
                    SmtWordGraph.normalize_with_node_conversion
                      node_conversion residue
                    handle Conv.UNCHANGED => Thm.REFL residue
                  val next_residue = boolSyntax.rhs (Thm.concl next)
                in
                  if Term.aconv residue next_residue then theorem
                  else loop (remaining - 1) (Thm.TRANS theorem next)
                end
        in loop 8 (Thm.REFL term) end
      val _ = trace_stage "normalize begin"
      val conversion = SmtResource.with_bitblast_step_time
        (feature ^ "-normalize") normalize_all target
      val _ = trace_stage "normalize end"
      val residue = boolSyntax.rhs (Thm.concl conversion)
      (* Word-graph replay owns normalization of word/FP projections.  If it
         made no change, defer the untouched Boolean formula to the checked
         propositional/XOR rungs instead of bit-blasting the same circuit. *)
      val _ = if Portable.pointer_eq (residue, target) then
        raise Conv.UNCHANGED
      else ()
      fun sat suffix formula =
        prove_boolean_dag_tautology (feature ^ suffix) formula
      fun prove_residue () =
        (if boolSyntax.is_eq residue andalso
            Term.type_of (#1 (boolSyntax.dest_eq residue)) = Type.bool then
           let
             val (left, right) = boolSyntax.dest_eq residue
             val forward = sat "-sat-forward"
               (boolSyntax.mk_imp (left, right))
             val reverse = sat "-sat-reverse"
               (boolSyntax.mk_imp (right, left))
           in Drule.IMP_ANTISYM_RULE forward reverse end
         else sat "-sat" residue)
        handle HolSatLib.SAT_cex _ =>
          raise ERR "word_graph"
            "residue is not a Boolean tautology"
      val residue_theorem =
        if Term.aconv residue boolSyntax.T then boolTheory.TRUTH
        else (trace_stage "sat begin"; prove_residue ())
      val _ = trace_stage "sat end"
    in Thm.EQ_MP (Thm.SYM conversion) residue_theorem end

  val word_graph_tautology_cache = ref
    ([] : (Term.term * Term.term * Thm.thm) list)

  fun prove_word_graph_tautology feature target =
    let
      val (left, right) = boolSyntax.dest_eq target
      fun same (saved_left, saved_right, _) =
        Portable.pointer_eq (left, saved_left) andalso
        Portable.pointer_eq (right, saved_right)
    in
      case List.find same (!word_graph_tautology_cache) of
        SOME (_, _, theorem) => theorem
      | NONE =>
          let
            val theorem =
              prove_word_graph_tautology_uncached feature target
            val _ = word_graph_tautology_cache :=
              (left, right, theorem) :: !word_graph_tautology_cache
          in theorem end
    end

  (* A CPC nary_cong certificate supplies one premise for each immediate
     argument of its source application.  Reconstruct that application spine
     directly: descending through each argument is both unnecessary and can
     repeatedly traverse a shared bit-vector/FP circuit.  The fallback below
     retains the general occurrence-based reconstruction for non-flat input. *)
  fun replay_flat_nary_cong source prems =
    let
      fun expose premise =
        if boolSyntax.is_eq (Thm.concl premise) then premise
        else Drule.EQT_INTRO premise
      fun orient argument premise =
        let
          val premise = expose premise
          val (left, right) = boolSyntax.dest_eq (Thm.concl premise)
        in
          if Portable.pointer_eq (argument, left) then premise
          else if Portable.pointer_eq (argument, right) then Thm.SYM premise
          else if shared_aconv argument left then
            SmtSkeletonProve.anchor_left argument premise
          else if shared_aconv argument right then
            SmtSkeletonProve.anchor_left argument (Thm.SYM premise)
          else raise ERR "nary_cong"
            "premise does not rewrite an immediate source argument"
        end
      fun orient_all [] [] = []
        | orient_all (argument :: arguments) (premise :: premises) =
            orient argument premise :: orient_all arguments premises
        | orient_all _ _ = raise ERR "nary_cong"
            "certificate premise count differs from source application arity"
      val (head, arguments) = boolSyntax.strip_comb source
      val argument_equalities = orient_all arguments prems
      val theorem = List.foldl
        (fn (argument_equality, application_equality) =>
          Thm.MK_COMB (application_equality, argument_equality))
        (Thm.REFL head) argument_equalities
    in
      SmtSkeletonProve.anchor_left source theorem
    end

  fun replay_nary_cong source prems =
    replay_flat_nary_cong source prems
    handle Feedback.HOL_ERR error =>
      if SmtResource.is_resource_gate error then
        raise Feedback.HOL_ERR error
      else replay_direct_nary_cong source prems

  and replay_direct_nary_cong source prems =
    let
      fun expose premise =
        if boolSyntax.is_eq (Thm.concl premise) then premise
        else Drule.EQT_INTRO premise
      fun keyed premise =
        let
          val premise = expose premise
          val (left, right) = boolSyntax.dest_eq (Thm.concl premise)
        in (premise, left, right) end
      val remaining = ref (List.map keyed prems)
      fun exact_rewrite term =
        let
          fun search skipped candidates =
            case candidates of
              [] => NONE
            | candidate :: rest =>
                let
                  val (premise, left, right) = candidate
                  fun found theorem =
                    (remaining := List.revAppend (skipped, rest);
                     SOME theorem)
                  fun word_type value =
                    wordsSyntax.is_word_type (Term.type_of value)
                  fun same_head first second =
                    let
                      val (first_head, _) = boolSyntax.strip_comb first
                      val (second_head, _) = boolSyntax.strip_comb second
                    in Term.same_const first_head second_head end
                    handle Feedback.HOL_ERR _ => false
                  fun semantic endpoint theorem =
                    if word_type term andalso same_head term endpoint andalso
                       SmtResource.dag_nodes_up_to 200002 term > 200001 then
                      let
                        val bridge = prove_word_graph_tautology
                          "cpc-cong-word" (boolSyntax.mk_eq (term, endpoint))
                      in SOME (Thm.TRANS bridge theorem) end
                      handle Feedback.HOL_ERR holerr =>
                        if SmtResource.is_resource_gate holerr then
                          raise Feedback.HOL_ERR holerr
                        else NONE
                           | HolSatLib.SAT_cex _ =>
                          NONE
                    else NONE
                in
                  if Portable.pointer_eq (term, left) then found premise
                  else if Portable.pointer_eq (term, right) then
                    found (Thm.SYM premise)
                  else if shared_aconv term left then
                    found (SmtSkeletonProve.anchor_left term premise)
                  else if shared_aconv term right then
                    found (SmtSkeletonProve.anchor_left term
                      (Thm.SYM premise))
                  else
                    (case semantic left premise of
                       SOME theorem => found theorem
                     | NONE =>
                         (case semantic right (Thm.SYM premise) of
                            SOME theorem => found theorem
                          | NONE => search (candidate :: skipped) rest))
                end
        in search [] (!remaining) end
      val memo_bucket_count = 4093
      val memo = Array.array
        (memo_bucket_count, [] : (Term.term * Thm.thm) list)
      fun memo_name_hash name =
        let
          fun loop index hash =
            if index = String.size name then hash
            else loop (index + 1)
              ((hash * 33 + Char.ord (String.sub (name, index))) mod
               memo_bucket_count)
        in loop 0 5381 end
      fun memo_hash term =
        if Term.is_var term then memo_name_hash (#1 (Term.dest_var term))
        else if Term.is_const term then
          memo_name_hash (#Name (Term.dest_thy_const term))
        else if Term.is_abs term then 17
        else
          let val (operator, _) = Term.dest_comb term in
            (23 + (if Term.is_const operator then
                     memo_name_hash (#Name (Term.dest_thy_const operator))
                   else 29)) mod memo_bucket_count
          end
          handle Feedback.HOL_ERR _ => 31
      fun memo_peek term =
        List.find (fn (saved, _) => Portable.pointer_eq (saved, term))
          (Array.sub (memo, memo_hash term))
      fun memo_insert term theorem =
        let val index = memo_hash term in
          Array.update
            (memo, index, (term, theorem) :: Array.sub (memo, index))
        end
      fun anchor term theorem =
        if Portable.pointer_eq
             (boolSyntax.lhs (Thm.concl theorem), term) then theorem
        else SmtSkeletonProve.anchor_left term theorem
      fun rewrite term =
        case exact_rewrite term of
          SOME theorem => anchor term theorem
        | NONE =>
            (case memo_peek term of
               SOME (_, theorem) => theorem
             | NONE =>
                 let
                   val rebuilt =
                     if Term.is_abs term then
                       let val (variable, body) = Term.dest_abs term
                       in Thm.ABS variable (rewrite body) end
                     else if Term.is_comb term then
                       let val (operator, operand) = Term.dest_comb term
                       in Thm.MK_COMB (rewrite operator, rewrite operand) end
                     else Thm.REFL term
                   val theorem = anchor term rebuilt
                   val _ = memo_insert term theorem
                 in theorem end)
      val rewritten = rewrite source
      val (left, right) = boolSyntax.dest_eq (Thm.concl rewritten)
      val theorem =
        if not (shared_aconv left right) then rewritten
        else if not (List.null (!remaining)) andalso
                wordsSyntax.is_word_type (Term.type_of source) then
          SmtResource.with_bitblast_step_time
            "cpc-cong-word-normalize"
            (simpLib.SIMP_CONV simpLib.empty_ss
              [wordsTheory.word_compare_def]) source
        else rewritten
      val (left, right) = boolSyntax.dest_eq (Thm.concl theorem)
      val _ = not (shared_aconv left right) orelse
        let
          fun shape term =
            let
              val (head, _) = boolSyntax.strip_comb term
              val {Thy, Name, ...} = Term.dest_thy_const head
            in Thy ^ "$" ^ Name ^ ":" ^ Int.toString
              (SmtResource.dag_nodes_up_to 10000 term) end
            handle Feedback.HOL_ERR _ => "other"
          val (_, source_arguments) = boolSyntax.strip_comb source
          val candidates = List.concat (List.map
            (fn (_, candidate_left, candidate_right) =>
              [candidate_left, candidate_right]) (!remaining))
          val hypothesis_counts = String.concatWith ","
            (List.map (Int.toString o List.length o Thm.hyp o #1)
              (!remaining))
          fun difference path first second =
            if Portable.pointer_eq (first, second) then NONE
            else if Term.is_comb first andalso Term.is_comb second then
              (case difference (path ^ "r")
                  (Term.rand first) (Term.rand second) of
                 SOME result => SOME result
               | NONE => difference (path ^ "l")
                   (Term.rator first) (Term.rator second))
            else if Term.is_abs first andalso Term.is_abs second then
              difference (path ^ "b") (#2 (Term.dest_abs first))
                (#2 (Term.dest_abs second))
            else SOME (path, first, second)
          val difference_text =
            case (source_arguments, candidates) of
              (first :: _, second :: _) =>
                (case difference "" first second of
                   SOME (path, first, second) =>
                     " diff=" ^ path ^ ":" ^
                     Parse.term_to_string first ^ " <> " ^
                     Parse.term_to_string second
                 | NONE => " diff=pointer-equal")
            | _ => ""
        in raise ERR "nary_cong" "DAG congruence made no progress" end
    in theorem end

  fun replay_shared_trans prems =
    let
      fun compose (next, accumulated) =
        let
          val (accumulated_left, accumulated_right) =
            boolSyntax.dest_eq (Thm.concl accumulated)
          val (next_left, next_right) =
            boolSyntax.dest_eq (Thm.concl next)
        in
          if Term.aconv accumulated_right next_left then
            Thm.TRANS accumulated next
          else if Term.aconv accumulated_right next_right then
            Thm.TRANS accumulated (Thm.SYM next)
          else if Term.aconv accumulated_left next_left then
            Thm.TRANS (Thm.SYM accumulated) next
          else if Term.aconv accumulated_left next_right then
            Thm.TRANS (Thm.SYM accumulated) (Thm.SYM next)
          else raise ERR "trans" "DAG equality endpoints do not compose"
        end
    in
      case prems of
        [] => raise ERR "trans" "expected CPC equality premises"
      | first :: rest => List.foldl compose first rest
    end

  fun replay_shared_trans_result premise_steps =
    let
      fun shared_phase name work =
        if OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" = SOME "full" then
          let
            val timer = Timer.startCPUTimer ()
            val _ = Feedback.HOL_MESG ("CPC shared begin " ^ name)
            val _ = TextIO.flushOut TextIO.stdOut
            val result = profile ("CPC(trans:shared/" ^ name ^ ")")
              work ()
              handle exn =>
                let
                  val {nongc, ...} = Timer.checkCPUTimes timer
                  val _ = Feedback.HOL_MESG
                    ("CPC shared failed " ^ name ^ " cpu=" ^
                     Time.toString (#usr nongc))
                  val _ = TextIO.flushOut TextIO.stdOut
                in raise exn end
            val {nongc, ...} = Timer.checkCPUTimes timer
            val _ = Feedback.HOL_MESG
              ("CPC shared end " ^ name ^ " cpu=" ^
               Time.toString (#usr nongc))
            val _ = TextIO.flushOut TextIO.stdOut
          in result end
        else work ()
      fun same left right =
        shared_phase "compare" (fn () => shared_aconv left right)
      fun endpoints step =
        case step_provenance step of
          EqualityProvenance pair => SOME pair
        | _ => NONE
      fun compose (next_step, (accumulated, accumulated_provenance)) =
        let
          val next = step_theorem next_step
          val (accumulated_left, accumulated_right) =
            boolSyntax.dest_eq (Thm.concl accumulated)
          val (next_left, next_right) =
            boolSyntax.dest_eq (Thm.concl next)
          fun result theorem select =
            (theorem,
             case (accumulated_provenance, endpoints next_step) of
               (SOME accumulated_pair, SOME next_pair) =>
                 SOME (select (accumulated_pair, next_pair))
             | _ => NONE)
          fun canonical_pair left right =
            if same left right then
              (shared_phase "nodewise" (fn () =>
                 SmtSkeletonProve.bounded_nodewise_equality
                   SmtResource.max_skeleton_replay_dag_nodes left right),
               Thm.REFL right)
            else
            let
              val left_theorem = shared_phase "canonical_term"
                (fn () => canonical_term_conv left)
              val right_theorem = shared_phase "canonical_term"
                (fn () => canonical_term_conv right)
              val left_canonical = boolSyntax.rhs (Thm.concl left_theorem)
              val right_canonical = boolSyntax.rhs (Thm.concl right_theorem)
              val canonical_same =
                Portable.pointer_eq (left_canonical, right_canonical) orelse
                same left_canonical right_canonical
              val (left_theorem, right_theorem) =
                if canonical_same then (left_theorem, right_theorem)
                else
                  let
                    val bridge_target = boolSyntax.mk_eq
                      (left_canonical, right_canonical)
                    fun after_word () =
                      (profile "CPC(rung:trans/XOR_GRAPH)"
                         xor_graph_tautology bridge_target
                       handle Feedback.HOL_ERR holerr =>
                         if SmtResource.is_resource_gate holerr then
                           raise Feedback.HOL_ERR holerr
                         else
                           (profile "CPC(rung:trans/XOR_TAUT)"
                              xor_tautology bridge_target
                            handle Feedback.HOL_ERR holerr =>
                              if SmtResource.is_resource_gate holerr then
                                raise Feedback.HOL_ERR holerr
                              else shared_phase "bridge_aci" (fn () =>
                                replay_aci_norm [bridge_target])))
                    val bridge =
                      ((shared_phase "bridge_word" (fn () =>
                          prove_word_graph_tautology
                            "cpc-trans-word" bridge_target)
                        handle Conv.UNCHANGED => after_word ()
                         | Feedback.HOL_ERR holerr =>
                          if SmtResource.is_resource_gate holerr then
                            raise Feedback.HOL_ERR holerr
                          else after_word ())
                       handle Feedback.HOL_ERR holerr =>
                         if SmtResource.is_resource_gate holerr then
                           raise Feedback.HOL_ERR holerr
                         else
                           profile "CPC(rung:trans/TAUT)"
                             tautLib.TAUT_PROVE bridge_target)
                  in
                    (Thm.TRANS left_theorem bridge, right_theorem)
                  end
            in (left_theorem, right_theorem) end
          fun right_left () =
            let
              val (left_anchor, right_anchor) =
                canonical_pair accumulated_right next_left
              val accumulated = Thm.TRANS accumulated left_anchor
              val next = Thm.TRANS (Thm.SYM right_anchor) next
            in result (Thm.TRANS accumulated next)
              (fn ((left, _), (_, right)) => (left, right)) end
          fun right_right () =
            let
              val (left_anchor, right_anchor) =
                canonical_pair accumulated_right next_right
              val accumulated = Thm.TRANS accumulated left_anchor
              val next = Thm.TRANS (Thm.SYM right_anchor) (Thm.SYM next)
            in result (Thm.TRANS accumulated next)
              (fn ((left, _), (right, _)) => (left, right)) end
          fun left_left () =
            let
              val (left_anchor, right_anchor) =
                canonical_pair accumulated_left next_left
              val accumulated = Thm.TRANS (Thm.SYM accumulated) left_anchor
              val next = Thm.TRANS (Thm.SYM right_anchor) next
            in result (Thm.TRANS accumulated next)
              (fn ((_, right), (_, next_right)) => (right, next_right)) end
          fun left_right () =
            let
              val (left_anchor, right_anchor) =
                canonical_pair accumulated_left next_right
              val accumulated = Thm.TRANS (Thm.SYM accumulated) left_anchor
              val next = Thm.TRANS
                (Thm.SYM right_anchor) (Thm.SYM next)
            in result (Thm.TRANS accumulated next)
              (fn ((_, right), (next_left, _)) => (right, next_left)) end
        in
          if Portable.pointer_eq (accumulated_right, next_left) then
            result (Thm.TRANS accumulated next)
              (fn ((left, _), (_, right)) => (left, right))
          else if same accumulated_right next_left then
            right_left ()
          else if Portable.pointer_eq (accumulated_right, next_right) then
            result (Thm.TRANS accumulated (Thm.SYM next))
              (fn ((left, _), (right, _)) => (left, right))
          else if same accumulated_right next_right then
            right_right ()
          else if Portable.pointer_eq (accumulated_left, next_left) then
            result (Thm.TRANS (Thm.SYM accumulated) next)
              (fn ((_, right), (_, next_right)) => (right, next_right))
          else if same accumulated_left next_left then
            left_left ()
          else if Portable.pointer_eq (accumulated_left, next_right) then
            result (Thm.TRANS (Thm.SYM accumulated) (Thm.SYM next))
              (fn ((_, right), (next_left, _)) => (right, next_left))
          else if same accumulated_left next_right then
            left_right ()
          else
            (right_left ()
             handle Feedback.HOL_ERR _ => right_right ()
             handle Feedback.HOL_ERR _ => left_left ()
             handle Feedback.HOL_ERR _ => left_right ())
        end
      val (theorem, provenance) =
        case premise_steps of
          [] => raise ERR "trans" "expected CPC equality premises"
        | first :: rest =>
            List.foldl compose
              (step_theorem first, endpoints first) rest
    in
      case provenance of
        SOME (left, right) =>
          if provenance_term_has_abs (Thm.concl theorem) then
            exact_result (EqualityProvenance (left, right)) theorem
          else raw_unavailable_result
            "large transitivity result has no live binder" theorem
      | NONE => raw_unavailable_result
          "transitivity with unavailable input provenance" theorem
    end

  fun replay_reordering prems args =
    let
      val premise = expect_one_premise "reordering" prems
      val target = expect_one_arg "reordering" args
      fun same left right = shared_aconv left right
      fun contains target literal =
        same target literal orelse
        (case Lib.total boolSyntax.dest_disj target of
           SOME (left, right) =>
             contains left literal orelse contains right literal
         | NONE => false)
      fun introduce theorem into =
        if same (Thm.concl theorem) into then theorem
        else
          let val (left, right) = boolSyntax.dest_disj into in
            if contains left (Thm.concl theorem) then
              Thm.DISJ1 (introduce theorem left) right
            else
              Thm.DISJ2 left (introduce theorem right)
          end
      fun derive theorem =
        if contains target (Thm.concl theorem) then
          introduce theorem target
        else
          let
            val (left, right) = boolSyntax.dest_disj (Thm.concl theorem)
              handle Feedback.HOL_ERR _ => raise ERR "reordering"
                "source literal is absent from target clause"
          in
            Thm.DISJ_CASES theorem
              (derive (Thm.ASSUME left))
              (derive (Thm.ASSUME right))
          end
    in
      derive premise
      handle Feedback.HOL_ERR _ =>
        derive (Rewrite.PURE_REWRITE_RULE
          [Thm.CONJUNCT1 boolTheory.NOT_CLAUSES] premise)
    end

  fun replay_normalized_reordering canon prems target =
    let
      val normalized_prems = List.map (Conv.CONV_RULE canon) prems
      val target_norm = canon target
      val normalized_target = boolSyntax.rhs (Thm.concl target_norm)
      val theorem =
        if Term.aconv normalized_target boolSyntax.T then
          retain_all boolTheory.TRUTH normalized_prems
        else replay_reordering normalized_prems [normalized_target]
    in
      Thm.EQ_MP (Thm.SYM target_norm) theorem
    end

  val expand_real_div_conv = Conv.QCONV
    (Conv.TOP_DEPTH_CONV SmtReplayCanon.real_div_conv)

  fun real_div_reordering_conv strong_canon = compose_normal_form_conv
    expand_real_div_conv strong_canon

  fun replay_cnf_with_literals name args =
    let
      fun implication tm = boolSyntax.dest_imp tm
      fun equality tm = boolSyntax.dest_eq tm
      fun neg tm = boolSyntax.mk_neg tm
      fun strip_conjunction tm =
        (let val (left, right) = boolSyntax.dest_conj tm in
           strip_conjunction left @ strip_conjunction right
         end)
        handle Feedback.HOL_ERR _ => [tm]
      fun strip_disjunction tm =
        (let val (left, right) = boolSyntax.dest_disj tm in
           strip_disjunction left @ strip_disjunction right
         end)
        handle Feedback.HOL_ERR _ => [tm]
      fun xor tm =
        let
          val (f, right) = Term.dest_comb tm
          val (_, left) = Term.dest_comb f
        in (left, right) end
      fun ite tm = boolSyntax.dest_cond tm
      fun indexed_and as_ =
        case as_ of
          [conjunction, index_tm] =>
            let
              val index = Arbnum.toInt (numSyntax.dest_numeral
                (intSyntax.dest_injected index_tm))
            in
              List.nth (strip_conjunction conjunction, index)
                handle Subscript => raise ERR name
                  "CPC cnf_and_pos index is outside the conjunction"
            end
        | _ => raise ERR name "expected conjunction and index"
      fun indexed_or as_ =
        case as_ of
          [disjunction, index_tm] =>
            let
              val index = Arbnum.toInt (numSyntax.dest_numeral
                (intSyntax.dest_injected index_tm))
            in
              List.nth (strip_disjunction disjunction, index)
                handle Subscript => raise ERR name
                  "CPC cnf_or_neg index is outside the disjunction"
            end
        | _ => raise ERR name "expected disjunction and index"
      val literals =
        case (name, args) of
          ("cnf_implies_neg1", [imp]) =>
            let val (left, _) = implication imp in [left, imp] end
        | ("cnf_implies_neg2", [imp]) =>
            let val (_, right) = implication imp in [neg right, imp] end
        | ("cnf_implies_pos", [imp]) =>
            let val (left, right) = implication imp
            in [neg left, right, neg imp] end
        | ("cnf_and_pos", as_) =>
            let val conjunction = List.hd as_
            in [indexed_and as_, neg conjunction] end
        | ("cnf_and_neg", [conjunction]) =>
            (conjunction ::
              List.map neg (strip_conjunction conjunction))
        | ("cnf_or_neg", as_) =>
            let val disjunction = List.hd as_
            in [disjunction, neg (indexed_or as_)] end
        | ("cnf_or_pos", [disjunction]) =>
              (boolSyntax.mk_neg disjunction :: strip_disjunction disjunction)
        | ("cnf_equiv_neg1", [eq]) =>
            let val (left, right) = equality eq
            in [left, right, eq] end
        | ("cnf_equiv_neg2", [eq]) =>
            let val (left, right) = equality eq
            in [neg left, neg right, eq] end
        | ("cnf_equiv_pos1", [eq]) =>
            let val (left, right) = equality eq
            in [neg left, right, neg eq] end
        | ("cnf_equiv_pos2", [eq]) =>
            let val (left, right) = equality eq
            in [left, neg right, neg eq] end
        | ("cnf_xor_pos1", [x]) =>
            let val (left, right) = xor x
            in [neg x, left, right] end
        | ("cnf_xor_pos2", [x]) =>
            let val (left, right) = xor x
            in [neg x, neg left, neg right] end
        | ("cnf_xor_neg1", [x]) =>
            let val (left, right) = xor x
            in [x, neg left, right] end
        | ("cnf_xor_neg2", [x]) =>
            let val (left, right) = xor x
            in [x, left, neg right] end
        | ("cnf_ite_pos1", [if_term]) =>
            let val (condition, then_term, _) = ite if_term
            in [neg if_term, neg condition, then_term] end
        | ("cnf_ite_pos2", [if_term]) =>
            let val (condition, _, else_term) = ite if_term
            in [neg if_term, condition, else_term] end
        | ("cnf_ite_pos3", [if_term]) =>
            let val (_, then_term, else_term) = ite if_term
            in [neg if_term, then_term, else_term] end
        | ("cnf_ite_neg1", [if_term]) =>
            let val (condition, then_term, _) = ite if_term
            in [if_term, neg condition, neg then_term] end
        | ("cnf_ite_neg2", [if_term]) =>
            let val (condition, _, else_term) = ite if_term
            in [if_term, condition, neg else_term] end
        | ("cnf_ite_neg3", [if_term]) =>
            let val (_, then_term, else_term) = ite if_term
            in [if_term, neg then_term, neg else_term] end
        | _ => raise ERR name "unsupported CPC CNF rule argument shape"
      val conclusion = mk_disj_terms literals
      fun clause_from_implication implication =
        let
          val (premise, consequent) =
            boolSyntax.dest_imp (Thm.concl implication)
          val negated = boolSyntax.mk_neg premise
          val positive_case = Thm.DISJ1
            (Thm.MP implication (Thm.ASSUME premise)) negated
          val negative_case = Thm.DISJ2 consequent
            (Thm.ASSUME negated)
        in
          Thm.DISJ_CASES
            (Thm.SPEC premise boolTheory.EXCLUDED_MIDDLE)
            positive_case negative_case
        end
      fun schematic_equivalence_clause () =
        case args of
          [equality] =>
            let
              val (left, right) = boolSyntax.dest_eq equality
              val left_variable = Term.genvar Type.bool
              val right_variable = Term.genvar Type.bool
              val generic_equality = boolSyntax.mk_eq
                (left_variable, right_variable)
              val clause =
                case name of
                  "cnf_equiv_neg1" => mk_disj_terms
                    [left_variable, right_variable, generic_equality]
                | "cnf_equiv_neg2" => mk_disj_terms
                    [boolSyntax.mk_neg left_variable,
                     boolSyntax.mk_neg right_variable, generic_equality]
                | "cnf_equiv_pos1" => mk_disj_terms
                    [boolSyntax.mk_neg left_variable, right_variable,
                     boolSyntax.mk_neg generic_equality]
                | "cnf_equiv_pos2" => mk_disj_terms
                    [left_variable, boolSyntax.mk_neg right_variable,
                     boolSyntax.mk_neg generic_equality]
                | _ => raise ERR name "not an equivalence CNF rule"
              val law = tautLib.TAUT_PROVE clause
            in
              Thm.INST
                [{redex = left_variable, residue = left},
                 {redex = right_variable, residue = right}] law
            end
        | _ => raise ERR name "expected one equality argument"
      fun schematic_xor_clause () =
        case args of
          [x] =>
            let
              val (left, right) = xor x
              val (head, _) = boolSyntax.strip_comb x
              val left_variable = Term.genvar Type.bool
              val right_variable = Term.genvar Type.bool
              val generic_xor = Term.list_mk_comb
                (head, [left_variable, right_variable])
              val clause =
                case name of
                  "cnf_xor_pos1" => mk_disj_terms
                    [boolSyntax.mk_neg generic_xor,
                     left_variable, right_variable]
                | "cnf_xor_pos2" => mk_disj_terms
                    [boolSyntax.mk_neg generic_xor,
                     boolSyntax.mk_neg left_variable,
                     boolSyntax.mk_neg right_variable]
                | "cnf_xor_neg1" => mk_disj_terms
                    [generic_xor, boolSyntax.mk_neg left_variable,
                     right_variable]
                | "cnf_xor_neg2" => mk_disj_terms
                    [generic_xor, left_variable,
                     boolSyntax.mk_neg right_variable]
                | _ => raise ERR name "not an XOR CNF rule"
              val law = xor_tautology clause
            in
              Thm.INST
                [{redex = left_variable, residue = left},
                 {redex = right_variable, residue = right}] law
            end
        | _ => raise ERR name "expected one XOR argument"
      fun schematic_tree_clause destructor constructor aggregate negated =
        let
          fun build term =
            case Lib.total destructor term of
              SOME (left, right) =>
                let
                  val (left_tree, left_leaves, left_instances) = build left
                  val (right_tree, right_leaves, right_instances) = build right
                in
                  (constructor (left_tree, right_tree),
                   left_leaves @ right_leaves,
                   left_instances @ right_instances)
                end
            | NONE =>
                let val variable = Term.genvar Type.bool in
                  (variable, [variable],
                   [{redex = variable, residue = term}])
                end
          val (tree, leaves, instances) = build aggregate
          val clause =
            if negated then
              mk_disj_terms (tree :: List.map boolSyntax.mk_neg leaves)
            else
              mk_disj_terms (boolSyntax.mk_neg tree :: leaves)
        in
          Thm.INST instances (tautLib.TAUT_PROVE clause)
        end
      fun cnf_and_pos_prove () =
        case args of
          [conjunction, index_tm] =>
            let
              val index = Arbnum.toInt (numSyntax.dest_numeral
                (intSyntax.dest_injected index_tm))
              fun projections theorem =
                case Lib.total boolSyntax.dest_conj (Thm.concl theorem) of
                  SOME _ => projections (Thm.CONJUNCT1 theorem) @
                    projections (Thm.CONJUNCT2 theorem)
                | NONE => [theorem]
              val selected = List.nth
                (projections (Thm.ASSUME conjunction), index)
                handle Subscript => raise ERR name
                  "CPC cnf_and_pos index is outside the conjunction"
              val inclusion = Thm.DISCH conjunction selected
            in
              clause_from_implication inclusion
            end
        | _ => raise ERR name "expected conjunction and index"
      fun cnf_or_neg_prove () =
        case args of
          [disjunction, index_tm] =>
            let
              val index = Arbnum.toInt (numSyntax.dest_numeral
                (intSyntax.dest_injected index_tm))
              fun introductions term =
                case Lib.total boolSyntax.dest_disj term of
                  SOME (left, right) =>
                    List.map
                      (fn (literal, introduce) =>
                        (literal, fn theorem =>
                          Thm.DISJ1 (introduce theorem) right))
                      (introductions left) @
                    List.map
                      (fn (literal, introduce) =>
                        (literal, fn theorem =>
                          Thm.DISJ2 left (introduce theorem)))
                      (introductions right)
                | NONE => [(term, fn theorem => theorem)]
              val (selected, introduce) =
                List.nth (introductions disjunction, index)
                handle Subscript => raise ERR name
                  "CPC cnf_or_neg index is outside the disjunction"
              val inclusion = Thm.DISCH selected
                (introduce (Thm.ASSUME selected))
            in
              clause_from_implication inclusion
            end
        | _ => raise ERR name "expected disjunction and index"
      val theorem =
      if name = "cnf_and_pos" then cnf_and_pos_prove ()
      else if name = "cnf_and_neg" then
        schematic_tree_clause boolSyntax.dest_conj boolSyntax.mk_conj
          (List.hd args) true
      else if name = "cnf_or_neg" then cnf_or_neg_prove ()
      else if name = "cnf_or_pos" then
        schematic_tree_clause boolSyntax.dest_disj boolSyntax.mk_disj
          (List.hd args) false
      else if String.isPrefix "cnf_equiv_" name then
        schematic_equivalence_clause ()
      else if String.isPrefix "cnf_xor_" name then
        schematic_xor_clause ()
      else if String.isPrefix "cnf_ite_" name then
        Tactical.TAC_PROOF (([], conclusion),
          Tactical.THEN
            (Tactic.COND_CASES_TAC,
             tautLib.TAUT_TAC))
      else tautology name conclusion
    in (theorem, literals) end

  fun replay_cnf name args = #1 (replay_cnf_with_literals name args)

  fun replay_not_equiv_elim which prems =
    let
      val premise = expect_one_premise which prems
      val (left, right) = boolSyntax.dest_eq
        (boolSyntax.dest_neg (Thm.concl premise))
      val conclusion =
        if which = "not_equiv_elim1" then mk_disj_terms [left, right]
        else mk_disj_terms [boolSyntax.mk_neg left, boolSyntax.mk_neg right]
    in tautological_consequence premise conclusion end

  fun replay_equiv_elim which conclusion prems =
    let
      val premise = expect_one_premise which prems
      fun derived () =
        let
          val (left, right) = boolSyntax.dest_eq (Thm.concl premise)
          val target = if which = "equiv_elim1" then
              boolSyntax.mk_disj (boolSyntax.mk_neg left, right)
            else boolSyntax.mk_disj (left, boolSyntax.mk_neg right)
          val denied = Thm.ASSUME (boolSyntax.mk_neg target)
          fun contradict clause = Thm.MP (Thm.NOT_ELIM denied) clause
          val contradiction =
            if which = "equiv_elim1" then
              let
                val left_proof = Thm.CCONTR left
                  (contradict (Thm.DISJ1
                    (Thm.ASSUME (boolSyntax.mk_neg left)) right))
                val not_right = Thm.NOT_INTRO (Thm.DISCH right
                  (contradict (Thm.DISJ2
                    (boolSyntax.mk_neg left) (Thm.ASSUME right))))
                val right_proof = Thm.EQ_MP premise left_proof
              in Thm.MP (Thm.NOT_ELIM not_right) right_proof end
            else
              let
                val not_left = Thm.NOT_INTRO (Thm.DISCH left
                  (contradict (Thm.DISJ1 (Thm.ASSUME left)
                    (boolSyntax.mk_neg right))))
                val right_proof = Thm.CCONTR right
                  (contradict (Thm.DISJ2 left
                    (Thm.ASSUME (boolSyntax.mk_neg right))))
                val left_proof = Thm.EQ_MP (Thm.SYM premise) right_proof
              in Thm.MP (Thm.NOT_ELIM not_left) left_proof end
        in Thm.CCONTR target contradiction end
    in
      derived ()
      handle Feedback.HOL_ERR _ =>
        (case conclusion of
          SOME target => tautological_consequence premise target
        | NONE => if Term.aconv (Thm.concl premise) boolSyntax.T then premise
            else raise ERR which
              "non-equality premise requires a declared conclusion")
    end

  fun replay_equiv_elim2 conclusion prems =
    replay_equiv_elim "equiv_elim2" conclusion prems

  fun replay_equiv_elim1 conclusion prems =
    replay_equiv_elim "equiv_elim1" conclusion prems

  fun arith_prove target =
    profile "CPC(rung:arith/cases)" Library.arith_prove_with_cases target
    handle Feedback.HOL_ERR _ =>
      profile "CPC(rung:arith/full_simp)" Tactical.TAC_PROOF
        (([], target), bossLib.FULL_SIMP_TAC bossLib.arith_ss [])
    handle Feedback.HOL_ERR _ =>
      profile "CPC(rung:arith/int_arith)" Tactical.TAC_PROOF
        (([], target), intLib.ARITH_TAC)

  val arith_prove_from_prems = prove_from_prems arith_prove

  fun replay_arithmetic_eq_resolve_pair proposition equality =
    let
      val (left, right) = boolSyntax.dest_eq (Thm.concl equality)
      fun prove_side premise side =
        arith_prove_from_prems [premise] side
      val simplified =
        bossLib.SIMP_RULE (bossLib.srw_ss ()) [] proposition
      fun resolve_simplified () =
        Thm.EQ_MP equality simplified
        handle Feedback.HOL_ERR _ =>
          Thm.EQ_MP (Thm.SYM equality) simplified
      fun prove side =
        prove_side proposition side
        handle Feedback.HOL_ERR _ =>
          (* arith_reduction states both positive- and negative-divisor
             bounds as guarded implications.  Discharge literal guards in
             this semantic arithmetic rung, independently of strong
             definition canonicalization. *)
          prove_side simplified side
    in
      resolve_simplified ()
      handle Feedback.HOL_ERR _ => Thm.EQ_MP equality (prove left)
      handle Feedback.HOL_ERR _ =>
        Thm.EQ_MP (Thm.SYM equality) (prove right)
    end

  fun replay_arithmetic_eq_resolve prems =
    case prems of
      [left, right] =>
        (replay_arithmetic_eq_resolve_pair left right
         handle Feedback.HOL_ERR _ =>
           replay_arithmetic_eq_resolve_pair right left)
    | _ => raise ERR "eq_resolve" "expected two CPC premises"

  datatype eq_resolve_preflight_route =
      EqResolveCanonicalLarge
    | EqResolveCanonicalTrueHyp
    | EqResolveCanonicalReal
    | EqResolveArithmetic

  (* E1(c): this preflight chooses only the cheaper route to try first.  The
     unit pins exercise both reconstruction procedures for every branch, so
     none of these syntactic cost checks is allowed to decide coverage. *)
  fun eq_resolve_preflight_route prems =
    if List.exists (fn theorem =>
         SmtResource.term_nodes_up_to 1000 (Thm.concl theorem) > 1000)
         prems then
      EqResolveCanonicalLarge
    else if List.exists (fn theorem =>
         HOLset.member (Thm.hypset theorem, boolSyntax.T)) prems then
      EqResolveCanonicalTrueHyp
    else if List.exists (fn theorem =>
         not (List.null (HolKernel.find_terms (fn tm =>
           Type.compare (Term.type_of tm, realSyntax.real_ty) = EQUAL)
           (Thm.concl theorem)))) prems then
      EqResolveCanonicalReal
    else EqResolveArithmetic

  fun enabled_eq_resolve_preflight_route_with_worker worker prems =
    let
      val target = boolSyntax.list_mk_conj
        (case List.map Thm.concl prems of [] => [boolSyntax.T] | terms => terms)
    in
      optional_fastpath
        (Library.require_fastpath "CPC eq_resolve arithmetic preflight")
        target worker prems
    end

  fun enabled_eq_resolve_preflight_route prems =
    enabled_eq_resolve_preflight_route_with_worker
      eq_resolve_preflight_route prems

  fun eq_resolve_preflight_name route =
    case route of
      EqResolveCanonicalLarge => "canonical-large"
    | EqResolveCanonicalTrueHyp => "canonical-true-hyp"
    | EqResolveCanonicalReal => "canonical-real"
    | EqResolveArithmetic => "arithmetic"

  fun eq_resolve_preflight_diagnostic route =
    case route of
      EqResolveCanonicalLarge =>
        "large arithmetic equality uses canonical replay first"
    | EqResolveCanonicalTrueHyp =>
        "arithmetic preflight retains a trivial scope hypothesis"
    | EqResolveCanonicalReal =>
        "mixed real arithmetic uses canonical replay first"
    | EqResolveArithmetic =>
        "arithmetic eq_resolve route selected"

  fun replay_arith_abs_eq args =
    case args of
      [left, right] =>
        if Lib.equal (Term.type_of left) intSyntax.int_ty then
          let
            val target = boolSyntax.mk_eq
              (boolSyntax.mk_eq
                (intSyntax.mk_absval left, intSyntax.mk_absval right),
               boolSyntax.mk_disj
                 (boolSyntax.mk_eq (left, right),
                  boolSyntax.mk_eq (left, intSyntax.mk_negated right)))
            val instantiation =
              Term.match_term
                (Thm.concl integerTheory.INT_ABS_EQ_ABS) target
          in
            Drule.INST_TY_TERM instantiation integerTheory.INT_ABS_EQ_ABS
          end
        else
          let
            val target = boolSyntax.mk_eq
              (boolSyntax.mk_eq
                (realSyntax.mk_absval left, realSyntax.mk_absval right),
               boolSyntax.mk_disj
                 (boolSyntax.mk_eq (left, right),
                  boolSyntax.mk_eq (left, realSyntax.mk_negated right)))
          in arith_prove target end
    | _ => raise ERR "arith-abs-eq" "expected two arithmetic arguments"

  fun replay_arith_abs_int_gt args =
    case args of
      [left, right] =>
        let
          val zero = intSyntax.zero_tm
          val neg_left = intSyntax.mk_negated left
          val neg_right = intSyntax.mk_negated right
          val right_nonnegative = intSyntax.mk_geq (right, zero)
          val target = boolSyntax.mk_eq
            (intSyntax.mk_greater
               (intSyntax.mk_absval left, intSyntax.mk_absval right),
             boolSyntax.mk_cond
               (intSyntax.mk_geq (left, zero),
                boolSyntax.mk_cond
                  (right_nonnegative,
                   intSyntax.mk_greater (left, right),
                   intSyntax.mk_greater (left, neg_right)),
                boolSyntax.mk_cond
                  (right_nonnegative,
                   intSyntax.mk_greater (neg_left, right),
                   intSyntax.mk_greater (neg_left, neg_right))))
          val result = Drule.SPECL [left, right]
            HolSmtTheory.smt_int_abs_gt
        in
          if Term.aconv (Thm.concl result) target then result
          else raise ERR "arith-abs-int-gt"
            "instantiated rule does not match its CPC formula"
        end
    | _ => raise ERR "arith-abs-int-gt"
        "expected two integer arguments"

  (* cvc5 uses the same CPC arithmetic rules over Int and Real.  The HOL
     constructors are type-specific, so select the integer form first and
     fall back to the real form while retaining the certificate's shape. *)
  fun arith_less (left, right) =
    intSyntax.mk_less (left, right)
    handle Feedback.HOL_ERR _ => realSyntax.mk_less (left, right)

  fun arith_leq (left, right) =
    intSyntax.mk_leq (left, right)
    handle Feedback.HOL_ERR _ => realSyntax.mk_leq (left, right)

  fun arith_greater (left, right) =
    intSyntax.mk_greater (left, right)
    handle Feedback.HOL_ERR _ => realSyntax.mk_greater (left, right)

  fun arith_geq (left, right) =
    intSyntax.mk_geq (left, right)
    handle Feedback.HOL_ERR _ => realSyntax.mk_geq (left, right)

  fun arith_mult (left, right) =
    intSyntax.mk_mult (left, right)
    handle Feedback.HOL_ERR _ => realSyntax.mk_mult (left, right)

  fun arith_dest_greater tm =
    intSyntax.dest_greater tm
    handle Feedback.HOL_ERR _ => realSyntax.dest_greater tm

  fun arith_dest_less tm =
    intSyntax.dest_less tm
    handle Feedback.HOL_ERR _ => realSyntax.dest_less tm

  fun arith_dest_leq tm =
    intSyntax.dest_leq tm
    handle Feedback.HOL_ERR _ => realSyntax.dest_leq tm

  fun arith_dest_geq tm =
    intSyntax.dest_geq tm
    handle Feedback.HOL_ERR _ => realSyntax.dest_geq tm

  fun replay_arith_mult_abs_comparison prems conclusion =
    let
      datatype direct_factor_relation =
          DirectAbsEq of
            {theorem : Thm.thm, left : Term.term, right : Term.term}
        | DirectAbsGt of
            {theorem : Thm.thm, left : Term.term, right : Term.term}
      datatype strict_factor_relation =
          StrictAbsGt of
            {theorem : Thm.thm, left : Term.term, right : Term.term}
        | StrictAbsEqNonzero of
            {equality : Thm.thm, nonzero : Thm.thm,
             left : Term.term, right : Term.term}
      fun dest_abs term = intSyntax.dest_absval term
        handle Feedback.HOL_ERR _ => realSyntax.dest_absval term
      fun absval term = intSyntax.mk_absval term
        handle Feedback.HOL_ERR _ => realSyntax.mk_absval term
      fun zero term =
        if Lib.equal (Term.type_of term) intSyntax.int_ty then
          intSyntax.zero_tm
        else if Lib.equal (Term.type_of term) realSyntax.real_ty then
          realSyntax.zero_tm
        else raise ERR "arith_mult_abs_comparison"
          "expected integer or real absolute-value factors"
      fun dest_abs_equality theorem =
        let
          val (left, right) = boolSyntax.dest_eq (Thm.concl theorem)
        in (dest_abs left, dest_abs right) end
        handle Feedback.HOL_ERR _ =>
          raise ERR "arith_mult_abs_comparison"
            "expected an absolute-value equality"
      fun dest_abs_greater theorem =
        let
          val (left, right) = arith_dest_greater (Thm.concl theorem)
        in (dest_abs left, dest_abs right) end
        handle Feedback.HOL_ERR _ =>
          raise ERR "arith_mult_abs_comparison"
            "expected a strict absolute-value comparison"
      fun apply_context body theorem =
        let
          val variable = Term.genvar
            (Term.type_of (#1 (boolSyntax.dest_eq (Thm.concl theorem))))
          val context = Term.mk_abs (variable, body variable)
        in Conv.BETA_RULE (Thm.AP_TERM context theorem) end
      fun transport label equivalence theorem =
        let
          val (left, right) = boolSyntax.dest_eq (Thm.concl equivalence)
          val source = Thm.concl theorem
        in
          if Term.aconv source left then Thm.EQ_MP equivalence theorem
          else if Term.aconv source right then
            Thm.EQ_MP (Thm.SYM equivalence) theorem
          else raise ERR "arith_mult_abs_comparison"
            (label ^ " equivalence does not match the pairwise result")
        end
      fun finish result =
        case conclusion of
          NONE => result
        | SOME target =>
            if Term.aconv (Thm.concl result) target then result
            else raise ERR "arith_mult_abs_comparison"
              "reconstructed absolute-product relation does not match"
      fun require_same_type (left, right) =
        Lib.equal (Term.type_of left) (Term.type_of right) orelse
        raise ERR "arith_mult_abs_comparison"
          "all absolute-value factors must have the same arithmetic type"
      fun abs_mult_theorem (left, right) =
        if Lib.equal (Term.type_of left) intSyntax.int_ty then
          Drule.SPECL [left, right] integerTheory.INT_ABS_MUL
        else
          Drule.SPECL [left, right] realTheory.ABS_MUL
      fun abs_nonnegative term =
        if Lib.equal (Term.type_of term) intSyntax.int_ty then
          Drule.SPECL [term] integerTheory.INT_ABS_POS
        else
          Drule.SPECL [term] realTheory.ABS_POS
      fun greater_definition (left, right) =
        let
          val theorem =
            if Lib.equal (Term.type_of left) intSyntax.int_ty then
              integerTheory.INT_GT
            else realTheory.real_gt
        in
          Drule.SPECL [left, right] theorem
        end
      fun greater_as_less (left, right) theorem =
        transport "greater-to-less"
          (greater_definition (absval left, absval right)) theorem
      fun less_as_greater (left, right) theorem =
        transport "less-to-greater"
          (greater_definition (left, right)) theorem
      fun wrap_strict_products
          (left, right, factor, matching_factor, inner_relation) =
        let
          val left_bridge = abs_mult_theorem (left, factor)
          val right_bridge = abs_mult_theorem (right, matching_factor)
          val inner_right =
            arith_mult (absval right, absval matching_factor)
          val outer_left = absval (arith_mult (left, factor))
          val left_relation = apply_context
            (fn product => arith_greater (product, inner_right)) left_bridge
          val with_outer_left = transport
            "left absolute-product bridge" left_relation inner_relation
          val right_relation = apply_context
            (fn product => arith_greater (outer_left, product)) right_bridge
        in
          transport "right absolute-product bridge"
            right_relation with_outer_left
        end
      fun equality_pair first second =
        let
          val (left1, right1) = dest_abs_equality first
          val (left2, right2) = dest_abs_equality second
          val _ = require_same_type (left1, left2)
          val abs_right1 = #2 (boolSyntax.dest_eq (Thm.concl first))
          val abs_left2 = #1 (boolSyntax.dest_eq (Thm.concl second))
          val first_product = apply_context
            (fn factor => arith_mult (factor, abs_left2)) first
          val second_product = apply_context
            (fn factor => arith_mult (abs_right1, factor)) second
          val product_equality = Thm.TRANS first_product second_product
          val (left_bridge, right_bridge) =
            if Lib.equal (Term.type_of left1) intSyntax.int_ty then
              (Thm.SYM (Drule.SPECL [left1, left2]
                 integerTheory.INT_ABS_MUL),
               Drule.SPECL [right1, right2] integerTheory.INT_ABS_MUL)
            else
              (Drule.SPECL [left1, left2] realTheory.ABS_MUL,
               Thm.SYM (Drule.SPECL [right1, right2]
                 realTheory.ABS_MUL))
          val result = Thm.TRANS left_bridge
            (Thm.TRANS product_equality right_bridge)
        in result end
      fun strict_equal_pair
          (strict, left, right, equality, nonzero, factor,
           matching_factor) =
        (require_same_type (left, factor);
        if Lib.equal (Term.type_of left) intSyntax.int_ty then
          let
            val assumptions = Thm.CONJ strict
              (Thm.CONJ equality nonzero)
            val rule = Drule.SPECL
              [left, right, factor, matching_factor]
              HolSmtTheory.smt_int_abs_mul_gt
          in
            Thm.MP rule assumptions
          end
        else
          let
            val positive = transport "real absolute nonzero"
              (Drule.SPECL [factor] realTheory.ABS_NZ) nonzero
            val scaled_equivalence = Thm.MP
              (Drule.SPECL
                [absval right, absval left, absval factor]
                realTheory.REAL_LT_RMUL)
              positive
            val scaled_less = transport "positive real scaling"
              scaled_equivalence
              (greater_as_less (left, right) strict)
            val scaled = less_as_greater
              (arith_mult (absval left, absval factor),
               arith_mult (absval right, absval factor)) scaled_less
            val replace_right_factor = apply_context
              (fn right_factor =>
                arith_greater
                  (arith_mult (absval left, absval factor),
                   arith_mult (absval right, right_factor)))
              equality
            val inner = transport "equal real factor"
              replace_right_factor scaled
          in
            wrap_strict_products
              (left, right, factor, matching_factor, inner)
          end)
      fun strict_strict_pair
          (first, left, right, second, factor, matching_factor) =
        let
          val _ = require_same_type (left, factor)
          val first_less = greater_as_less (left, right) first
          val second_less = greater_as_less
            (factor, matching_factor) second
          val assumptions = Thm.CONJ (abs_nonnegative right)
            (Thm.CONJ (abs_nonnegative matching_factor)
              (Thm.CONJ first_less second_less))
          val rule =
            if Lib.equal (Term.type_of left) intSyntax.int_ty then
              Drule.SPECL
                [absval right, absval left, absval matching_factor,
                 absval factor]
                integerTheory.INT_LT_MUL2
            else
              Drule.SPECL
                [absval right, absval left, absval matching_factor,
                 absval factor]
                realTheory.REAL_LT_MUL2
          val inner_less = Thm.MP rule assumptions
          val inner = less_as_greater
            (arith_mult (absval left, absval factor),
             arith_mult (absval right, absval matching_factor)) inner_less
        in
          wrap_strict_products
            (left, right, factor, matching_factor, inner)
        end
      fun direct_relation theorem =
        if Lib.can dest_abs_greater theorem then
          let val (left, right) = dest_abs_greater theorem
          in DirectAbsGt
            {theorem = theorem, left = left, right = right}
          end
        else
          let val (left, right) = dest_abs_equality theorem
          in DirectAbsEq
            {theorem = theorem, left = left, right = right}
          end
      fun malformed_strict_tail () =
        raise ERR "arith_mult_abs_comparison"
          "expected |t| > |s| or (|t| = |s| and t <> 0)"
      fun dest_guarded_equality theorem =
        let
          val _ = boolSyntax.dest_conj (Thm.concl theorem)
          val equality = Thm.CONJUNCT1 theorem
          val nonzero = Thm.CONJUNCT2 theorem
          val (left, right) = dest_abs_equality equality
          val expected_zero = zero left
          val (guard_left, guard_right) =
            boolSyntax.dest_eq (boolSyntax.dest_neg (Thm.concl nonzero))
        in
          (equality, nonzero, left, right, expected_zero,
           guard_left, guard_right)
        end
        handle Feedback.HOL_ERR _ => malformed_strict_tail ()
      fun strict_tail_relation theorem =
        if Lib.can dest_abs_greater theorem then
          let val (left, right) = dest_abs_greater theorem
          in StrictAbsGt
            {theorem = theorem, left = left, right = right}
          end
        else if Lib.can dest_abs_equality theorem then
          raise ERR "arith_mult_abs_comparison"
            "strict mode requires a nonzero side condition on equal factors"
        else
          let
            val (equality, nonzero, left, right, expected_zero,
                 guard_left, guard_right) = dest_guarded_equality theorem
            val oriented_nonzero =
              if Term.aconv guard_left left andalso
                 Term.aconv guard_right expected_zero
              then nonzero
              else if Term.aconv guard_left expected_zero andalso
                      Term.aconv guard_right left
              then
                let
                  val expected = boolSyntax.mk_eq (left, expected_zero)
                  val symmetry = Thm.SYM (Thm.ASSUME expected)
                  val contradiction = Thm.MP (Thm.NOT_ELIM nonzero)
                    symmetry
                in
                  Thm.NOT_INTRO (Thm.DISCH expected contradiction)
                end
              else raise ERR "arith_mult_abs_comparison"
                "nonzero side condition does not match its left factor"
          in
            StrictAbsEqNonzero
              {equality = equality, nonzero = oriented_nonzero,
               left = left, right = right}
          end
      fun equality_fold (theorem, result) = equality_pair result theorem
      fun strict_fold (theorem, (result, left, right)) =
        case strict_tail_relation theorem of
          StrictAbsGt
            {theorem, left = factor, right = matching_factor} =>
            (strict_strict_pair
               (result, left, right, theorem, factor, matching_factor),
             arith_mult (left, factor),
             arith_mult (right, matching_factor))
        | StrictAbsEqNonzero
            {equality, nonzero, left = factor,
             right = matching_factor} =>
            (strict_equal_pair
               (result, left, right, equality, nonzero, factor,
                matching_factor),
             arith_mult (left, factor),
             arith_mult (right, matching_factor))
    in
      case prems of
        [] => raise ERR "arith_mult_abs_comparison"
          "expected at least one absolute-value factor premise"
      | first :: rest =>
          let
            val first_relation = direct_relation first
              handle Feedback.HOL_ERR _ =>
                raise ERR "arith_mult_abs_comparison"
                  "first premise must be |t1| = |s1| or |t1| > |s1|"
          in
            case first_relation of
              DirectAbsEq _ => finish (List.foldl equality_fold first rest)
            | DirectAbsGt {left, right, ...} =>
                finish (#1 (List.foldl strict_fold
                  (first, left, right) rest))
          end
    end

  fun arith_list_mk_plus terms =
    intSyntax.list_mk_plus terms
    handle Feedback.HOL_ERR _ => realSyntax.list_mk_plus terms

  fun arith_zero tm =
    let val _ = intSyntax.mk_geq (tm, intSyntax.zero_tm)
    in intSyntax.zero_tm end
    handle Feedback.HOL_ERR _ => realSyntax.zero_tm

  fun replay_arith_max_geq1 args =
    case args of
      [left, right] =>
        let
          val maximum = boolSyntax.mk_cond
            (arith_geq (left, right), left, right)
          val target = boolSyntax.mk_eq
            (arith_geq (maximum, left), boolSyntax.T)
        in
          arith_prove target
        end
    | _ => raise ERR "arith-max-geq1" "expected two arithmetic arguments"

  fun replay_arith_min_lt2 args =
    case args of
      [left, right] =>
        let
          val minimum = boolSyntax.mk_cond
            (boolSyntax.mk_neg (arith_geq (left, right)), left, right)
          val target = boolSyntax.mk_eq
            (arith_leq (minimum, right), boolSyntax.T)
        in
          arith_prove target
        end
    | _ => raise ERR "arith-min-lt2" "expected two arithmetic arguments"

  fun replay_arith_int_geq_tighten (integer, real_bound, rounded) =
    let
      fun real_of_int_leq (left, right) =
        let
          val target = boolSyntax.mk_eq
            (realSyntax.mk_leq (intrealSyntax.mk_real_of_int left,
              intrealSyntax.mk_real_of_int right),
             intSyntax.mk_leq (left, right))
        in
          Drule.INST_TY_TERM
            (Term.match_term (Thm.concl intrealTheory.real_of_int_le) target)
            intrealTheory.real_of_int_le
        end
      val left = realSyntax.mk_geq
        (intrealSyntax.mk_real_of_int integer, real_bound)
      val right = intSyntax.mk_geq (integer, rounded)
      val target = boolSyntax.mk_eq (left, right)
      val not_right = boolSyntax.mk_neg right
      val predecessor = intSyntax.mk_minus (rounded, intSyntax.one_tm)
      val integer_at_most_predecessor = Tactical.TAC_PROOF
        (([not_right], intSyntax.mk_leq (integer, predecessor)),
         intLib.ARITH_TAC)
      val real_at_most_predecessor = Thm.EQ_MP (Thm.SYM
        (real_of_int_leq (integer, predecessor)))
        integer_at_most_predecessor
      val left_normalization = Conv.REWR_CONV realTheory.real_ge left
      val bound_lt_real_predecessor = Tactical.TAC_PROOF
        (([], realSyntax.mk_less
          (intrealSyntax.mk_real_of_int predecessor, real_bound)),
         Tactical.THEN
           (bossLib.SIMP_TAC (bossLib.srw_ss()) [realTheory.real_div],
            Tactic.CONV_TAC RealField.REAL_RAT_REDUCE_CONV))
      val q_at_integer = Thm.EQ_MP left_normalization (Thm.ASSUME left)
      val q_at_most_predecessor = Drule.PROVE_HYP q_at_integer
        (Drule.PROVE_HYP real_at_most_predecessor
          (Tactical.TAC_PROOF
            (([Thm.concl q_at_integer, Thm.concl real_at_most_predecessor],
              realSyntax.mk_leq (real_bound,
                intrealSyntax.mk_real_of_int predecessor)),
             metisLib.METIS_TAC [realTheory.REAL_LE_TRANS])))
      val no_q_at_most_predecessor = Drule.PROVE_HYP
        bound_lt_real_predecessor
        (Tactical.TAC_PROOF
          (([Thm.concl bound_lt_real_predecessor],
            boolSyntax.mk_neg (Thm.concl q_at_most_predecessor)),
           metisLib.METIS_TAC [realTheory.REAL_NOT_LE]))
      val contradiction = Thm.MP (Thm.NOT_ELIM no_q_at_most_predecessor)
        q_at_most_predecessor
      val forward = Thm.DISCH left
        (Thm.MP (Thm.SPEC right HolSmtTheory.NOT_NOT_ELIM)
          (Thm.NOT_INTRO (Thm.DISCH not_right contradiction)))
      val right_normalization = Conv.REWR_CONV integerTheory.int_ge right
      val real_at_least_rounded = Thm.EQ_MP (Thm.SYM
        (real_of_int_leq (rounded, integer)))
        (Thm.EQ_MP right_normalization (Thm.ASSUME right))
      val bound_at_most_rounded = Tactical.TAC_PROOF
        (([], realSyntax.mk_leq
          (real_bound, intrealSyntax.mk_real_of_int rounded)),
         Tactical.THEN
           (bossLib.SIMP_TAC (bossLib.srw_ss()) [realTheory.real_div],
            Tactic.CONV_TAC RealField.REAL_RAT_REDUCE_CONV))
      val reverse = Thm.DISCH right
        (Thm.EQ_MP (Thm.SYM left_normalization)
          (Drule.PROVE_HYP bound_at_most_rounded
            (Drule.PROVE_HYP real_at_least_rounded
              (Tactical.TAC_PROOF
                (([Thm.concl bound_at_most_rounded,
                   Thm.concl real_at_least_rounded],
                  boolSyntax.rhs (Thm.concl left_normalization)),
                 metisLib.METIS_TAC [realTheory.REAL_LE_TRANS])))))
    in Drule.IMP_ANTISYM_RULE forward reverse end
    handle Feedback.HOL_ERR holerr =>
      raise ERR "arith-int-geq-tighten" (Feedback.message_of holerr)
    | exn => raise ERR "arith-int-geq-tighten" (General.exnMessage exn)

  fun replay_arith_rule name args =
    if name = "arith-int-geq-tighten" then
      (case args of
         [integer, real_bound, rounded] =>
           replay_arith_int_geq_tighten (integer, real_bound, rounded)
       | _ => raise ERR name "unsupported CPC arithmetic rule argument shape")
    else let
      val target =
        case (name, args) of
          ("arith_poly_norm", [eq]) => eq
        | ("arith-elim-lt", [left, right]) =>
            boolSyntax.mk_eq (arith_less (left, right),
              boolSyntax.mk_neg (arith_geq (left, right)))
        | ("arith-elim-leq", [left, right]) =>
            boolSyntax.mk_eq (arith_leq (left, right),
              arith_geq (right, left))
        | ("arith-elim-gt", [left, right]) =>
            boolSyntax.mk_eq (arith_greater (left, right),
              boolSyntax.mk_neg (arith_geq (right, left)))
        | ("arith-leq-norm", [left, right]) =>
            boolSyntax.mk_eq (intSyntax.mk_leq (left, right),
              boolSyntax.mk_neg (intSyntax.mk_geq
                (left, intSyntax.mk_plus (right, intSyntax.one_tm))))
        | ("arith-eq-elim-int", [left, right]) =>
            boolSyntax.mk_eq
              (boolSyntax.mk_eq (left, right),
               boolSyntax.mk_conj
                 (intSyntax.mk_geq (left, right), intSyntax.mk_leq (left, right)))
        | ("arith-geq-norm1-int", [left, right]) =>
            boolSyntax.mk_eq (intSyntax.mk_geq (left, right),
              intSyntax.mk_geq
                (intSyntax.mk_minus (left, right), intSyntax.zero_tm))
        | ("arith-geq-norm1-real", [left, right]) =>
            boolSyntax.mk_eq (realSyntax.mk_geq (left, right),
              realSyntax.mk_geq
                (realSyntax.mk_minus (left, right), realSyntax.zero_tm))
        | ("arith-geq-tighten", [left, right]) =>
            boolSyntax.mk_eq
              (boolSyntax.mk_neg (intSyntax.mk_geq (left, right)),
               intSyntax.mk_geq
                 (right, intSyntax.mk_plus (left, intSyntax.one_tm)))
        | _ => raise ERR name "unsupported CPC arithmetic rule argument shape"
    in
      if name = "arith-elim-lt" then
        (case args of
           [left, right] =>
             Thm.SYM (Drule.SPECL [right, left]
               (if Lib.equal (Term.type_of left) intSyntax.int_ty then
                  integerTheory.INT_NOT_LE
                else realTheory.REAL_NOT_LE))
         | _ => raise ERR name "unsupported CPC arithmetic rule argument shape")
      else if name = "arith_poly_norm" then
        profile "CPC(rung:arith/poly_norm_canonical)"
          SmtReplayCanon.arith_poly_norm_prove target
      else if name = "arith-leq-norm" then
        simpLib.SIMP_PROVE (bossLib.srw_ss())
          [integerTheory.int_ge, integerTheory.INT_NOT_LE,
           integerTheory.INT_NOT_LT, integerTheory.INT_LE_LT1] target
      else arith_prove target
    end

  (* Couple arithmetic relation rewrites to the exact syntax constructed by
     the successful semantic rule.  In particular, ARITH_EQ_ELIM_INT creates
     a binary conjunction here; recording that boundary is construction, not
     recovery from the erased HOL term or from a producer-name lookup. *)
  fun replay_arith_rule_result name
      (located_args : located_term list) =
    let
      val args = List.map (fn located => #term located) located_args
      val theorem = replay_arith_rule name args
      val provenance =
        case (name, located_args) of
          ("arith_poly_norm", [target]) => #provenance target
        | ("arith-eq-elim-int", [left, right]) =>
            let
              val left_provenance = #provenance left
              val right_provenance = #provenance right
            in
              EqualityProvenance
                (EqualityProvenance
                   (left_provenance, right_provenance),
                 ConjunctionProvenance
                   (ArithReductionConjunction,
                    [AtomicProvenance, AtomicProvenance]))
            end
        | _ => conjunction_free_semantic_provenance
            ("arithmetic relation rewrite contains an exact conjunction")
            (Thm.concl theorem)
    in
      exact_result provenance theorem
    end

  fun replay_arrays_select_const args =
    case args of
      [target] => Tactical.TAC_PROOF (([], target),
        bossLib.SIMP_TAC boolSimps.bool_ss [])
    | _ => raise ERR "arrays-select-const" "expected one equality"

  (* Compact CPC omits the conclusion of the read-over-write rules and gives
     only the selected update term.  Reconstruct the equality specified by
     the rule before handing it to the bounded, kernel-checked array prover. *)
  fun replay_arrays_read_over_write name prems conclusion args =
    let
      fun selected_update selected =
        let
          val (updated, selected_index) = Term.dest_comb selected
          val ((stored_index, stored_value), array) =
            combinSyntax.dest_update_comb updated
        in
          (selected_index, stored_index, stored_value, array)
        end
        handle Feedback.HOL_ERR _ =>
          raise ERR name "expected a select from a stored array"
      fun omitted_target () =
        case args of
          [selected] =>
            let
              val (selected_index, stored_index, stored_value, array) =
                selected_update selected
              val right =
                if name = "arrays_read_over_write_1" then
                  if Term.aconv selected_index stored_index then stored_value
                  else raise ERR name "select and store indices differ"
                else
                  Term.mk_comb (array, selected_index)
            in
              boolSyntax.mk_eq (selected, right)
            end
        | _ => raise ERR name "expected one selected update term"
      val target =
        case conclusion of SOME target => target | NONE => omitted_target ()
    in
      prove_from_prems SmtArrayProve.array_prove prems target
    end

  fun replay_ite_not_cond args =
    case args of
      [condition, then_tm, else_tm] =>
        let val target = boolSyntax.mk_eq
          (boolSyntax.mk_cond (boolSyntax.mk_neg condition, then_tm, else_tm),
           boolSyntax.mk_cond (condition, else_tm, then_tm))
        in
          Tactical.TAC_PROOF (([], target),
            Tactical.THEN (Tactic.BOOL_CASES_TAC condition,
              bossLib.ASM_SIMP_TAC boolSimps.bool_ss []))
        end
    | _ => raise ERR "ite-not-cond" "expected condition and two branches"

  fun replay_ite_true_cond args =
    case args of
      [then_tm, else_tm] =>
        let
          val target = boolSyntax.mk_eq
            (boolSyntax.mk_cond (boolSyntax.T, then_tm, else_tm), then_tm)
        in
          Tactical.TAC_PROOF (([], target),
            bossLib.SIMP_TAC boolSimps.bool_ss [])
        end
    | _ => raise ERR "ite-true-cond" "expected two branches"

  fun replay_ite_then_true args =
    case args of
      [condition, else_tm] =>
        let
          val target = boolSyntax.mk_eq
            (boolSyntax.mk_cond (condition, boolSyntax.T, else_tm),
             boolSyntax.mk_disj (condition, else_tm))
        in
          Tactical.TAC_PROOF (([], target),
            Tactical.THEN (Tactic.BOOL_CASES_TAC condition,
              bossLib.ASM_SIMP_TAC boolSimps.bool_ss []))
        end
    | _ => raise ERR "ite-then-true" "expected condition and else branch"

  fun replay_ite_then_false args =
    case args of
      [condition, else_tm] =>
        let
          val target = boolSyntax.mk_eq
            (boolSyntax.mk_cond (condition, boolSyntax.F, else_tm),
             boolSyntax.mk_conj (boolSyntax.mk_neg condition, else_tm))
        in
          Tactical.TAC_PROOF (([], target),
            Tactical.THEN (Tactic.BOOL_CASES_TAC condition,
              bossLib.ASM_SIMP_TAC boolSimps.bool_ss []))
        end
    | _ => raise ERR "ite-then-false" "expected condition and else branch"

  fun replay_ite_false_cond args =
    case args of
      [then_tm, else_tm] =>
        let
          val target = boolSyntax.mk_eq
            (boolSyntax.mk_cond (boolSyntax.F, then_tm, else_tm), else_tm)
        in
          Tactical.TAC_PROOF (([], target),
            bossLib.SIMP_TAC boolSimps.bool_ss [])
        end
    | _ => raise ERR "ite-false-cond" "expected two branches"

  (* cvc5 can emit a TRUST_THEORY_REWRITE equating its unconstrained
     division-by-zero term with HOL's total division.  That equality is not
     valid for smt_rdiv, so never assert it.  Return only a reflexive theorem
     for this exact shape; irrelevant congruence branches discard reflexive
     premises, while any proof that actually needs the rewrite still fails. *)
  val smtfp_eq_components_law =
    Library.prove
      (``!x y : ('t,'w) smtfp.
          smtfp_eq x y <=>
          (~smtfp_is_nan x /\ ~smtfp_is_nan y) /\
          (x = y \/ smtfp_is_zero x /\ smtfp_is_zero y)``,
       Tactical.THEN
         (bossLib.SIMP_TAC (bossLib.srw_ss())
            [smtfloatTheory.smtfp_eq_def,
             smtfloatTheory.float_equal_components,
             smtfloatTheory.smtfp_is_nan_def,
             smtfloatTheory.smtfp_is_zero_def],
          metisLib.METIS_TAC []))

  val fp_canonical_fact_laws = ref
    (Redblackmap.mkDict Type.compare :
      (Type.hol_type, Term.term * Thm.thm) Redblackmap.dict)
  val fp_atom_lowerings = ref
    (Redblackmap.mkDict Term.compare :
      (Term.term, Thm.thm) Redblackmap.dict)
  val fp_boolean_atom_normalizations = ref
    (Redblackmap.mkDict Term.compare :
      (Term.term, Thm.thm) Redblackmap.dict)
  val fp_atom_bridge_laws = ref ([] : Thm.thm list)

  val rounding_partition_law = Library.prove
    (``!mode : smt_rounding.
       (mode = RNE \/ mode = RNA \/ mode = RTP \/
        mode = RTN \/ mode = RTZ) /\
       ~(mode = RNE /\ mode = RNA) /\
       ~(mode = RNE /\ mode = RTP) /\
       ~(mode = RNE /\ mode = RTN) /\
       ~(mode = RNE /\ mode = RTZ) /\
       ~(mode = RNA /\ mode = RTP) /\
       ~(mode = RNA /\ mode = RTN) /\
       ~(mode = RNA /\ mode = RTZ) /\
       ~(mode = RTP /\ mode = RTN) /\
       ~(mode = RTP /\ mode = RTZ) /\
       ~(mode = RTN /\ mode = RTZ)``,
     metisLib.METIS_TAC
       [smtfloatTheory.smt_rounding_cases,
        smtfloatTheory.smt_rounding_distinctness])

  fun prove_boolean_circuit_tautology goal =
    if boolSyntax.is_eq goal andalso
       Term.type_of (#1 (boolSyntax.dest_eq goal)) = Type.bool then
      let
        val (left, right) = boolSyntax.dest_eq goal
        val forward = prove_boolean_circuit_tautology
          (boolSyntax.mk_imp (left, right))
        val backward = prove_boolean_circuit_tautology
          (boolSyntax.mk_imp (right, left))
      in Drule.IMP_ANTISYM_RULE forward backward end
    else if boolSyntax.is_imp goal andalso
            let val (_, consequent) = boolSyntax.dest_imp goal
            in boolSyntax.is_eq consequent andalso
               Term.type_of (#1 (boolSyntax.dest_eq consequent)) =
                 Type.bool end then
      let
        val (antecedent, consequent) = boolSyntax.dest_imp goal
        val (left, right) = boolSyntax.dest_eq consequent
        val forward = prove_boolean_circuit_tautology
          (boolSyntax.mk_imp
            (antecedent, boolSyntax.mk_imp (left, right)))
        val backward = prove_boolean_circuit_tautology
          (boolSyntax.mk_imp
            (antecedent, boolSyntax.mk_imp (right, left)))
        val assumption = Thm.ASSUME antecedent
        val equality = Drule.IMP_ANTISYM_RULE
          (Thm.MP forward assumption) (Thm.MP backward assumption)
      in Thm.DISCH antecedent equality end
    else
    let
      val circuit_started = Time.now ()
      val leaf_count = ref 0
      val memo = Array.array
        (boolean_dag_bucket_count,
         [] : (Term.term * Term.term) list)
      val leaves = Array.array
        (boolean_dag_bucket_count,
         [] : (Term.term * Term.term) list)
      val active = Array.array
        (boolean_dag_bucket_count,
         [] : (Term.term * unit) list)
      (* Shallow hashes cluster independently expanded word circuits with
         the same operator prefix.  Memoize a whole-DAG hash instead, so
         each physical application is visited once.  Abstractions stay
         opaque, making the hash independent of binder names without
         opening binders.  Hashes select buckets only: every structural
         reuse still requires exact alpha-equivalence. *)
      val hashes = Array.array
        (boolean_dag_bucket_count, [] : (Term.term * int) list)
      fun bucket_index term =
        let val index = boolean_dag_term_hash 4 term in
          case List.find (fn (saved, _) => Portable.pointer_eq (saved, term))
              (Array.sub (hashes, index)) of
            SOME (_, hash) => hash
          | NONE =>
              let
                val hash =
                  if Term.is_comb term then
                    (41 * bucket_index (Term.rator term) +
                     67 * bucket_index (Term.rand term) + 31) mod
                    boolean_dag_bucket_count
                  else boolean_dag_term_hash 0 term
                val _ = Array.update (hashes, index,
                  (term, hash) :: Array.sub (hashes, index))
              in hash end
        end
      fun pointer_lookup table term =
        case List.find (fn (saved, _) =>
            Portable.pointer_eq (saved, term))
            (Array.sub (table, bucket_index term)) of
          SOME (_, result) => SOME result
        | NONE => NONE
      fun alpha_lookup table term =
        case pointer_lookup table term of
          SOME result => SOME result
        | NONE =>
            (case List.find (fn (saved, _) =>
                shared_aconv saved term)
                (Array.sub (table, bucket_index term)) of
               SOME (_, result) => SOME result
             | NONE => NONE)
      fun insert table term result =
        let val index = bucket_index term in
          Array.update
            (table, index,
             (term, result) :: Array.sub (table, index))
        end
      val definitions = ref
        ([] : (Term.term * Term.term * Thm.thm option) list)
      val substitutions = ref
        ([] : {redex : Term.term, residue : Term.term} list)
      fun variable term =
        let
          val result = Term.genvar Type.bool
          val _ = substitutions :=
            {redex = result, residue = term} :: !substitutions
        in result end
      fun leaf term =
        case alpha_lookup leaves term of
          SOME result => result
        | NONE =>
            let
              val result = variable term
              val _ = insert leaves term result
              val _ = leaf_count := !leaf_count + 1
            in result end
      (* SMT Core XOR is a Boolean gate, not an opaque theory atom.  Both
         circuit paths use this checked definition before abstracting leaves. *)
      val circuit_leaf_rewrites =
        List.map Conv.REWR_CONV
          [HolSmtTheory.xor_def,
           fcpTheory.COND_COMPONENT,
           smtfloatReplayRoundingTheory.word_and_index0,
           smtfloatReplayRoundingTheory.word_or_index0,
           smtfloatReplayRoundingTheory.word_xor_index0,
           smtfloatReplayRoundingTheory.word_1comp_index0,
           smtfloatReplayRoundingTheory.word_compare_index,
           smtfloatReplayRoundingTheory.smtfp_pack_rounding_index,
           smtfloatReplayRoundingTheory.word1_eq_index,
           smtfloatReplayRoundingTheory.word1_cond_index,
           smtfloatReplayRoundingTheory.word_add_one_index0,
           smtfloatReplayRoundingTheory.word_add_one_twice_index0,
           smtfloatReplayRoundingTheory.word1_minus_index,
           smtfloatReplayRoundingTheory.word1_neg_minus_index]
      fun ground_leaf_conversion term =
        if SmtResource.dag_nodes_up_to 33 term > 32 orelse
           not (List.null (Term.free_vars term)) then NONE
        else
          (let
             val sizes = Conv.DEPTH_CONV
               wordsLib.SIZES_CONV term
               handle Conv.UNCHANGED => Thm.REFL term
             val sized = boolSyntax.rhs (Thm.concl sizes)
             val evaluated = SmtResource.with_bitblast_step_time
               "cpc-trust-fp-ground-leaf" bossLib.EVAL sized
               handle Conv.UNCHANGED => Thm.REFL sized
             val theorem = Thm.TRANS sizes evaluated
             val residue = boolSyntax.rhs (Thm.concl theorem)
           in if Term.aconv term residue then NONE
              else SOME theorem end)
          handle Feedback.HOL_ERR holerr =>
            if SmtResource.is_resource_gate holerr then
              raise Feedback.HOL_ERR holerr
            else NONE
      fun projection_index_conversion term =
        let
          val (_, index) = wordsSyntax.dest_index term
          val _ = SmtResource.dag_nodes_up_to 33 index <= 32 andalso
                  List.null (Term.free_vars index) orelse
            raise Conv.UNCHANGED
          val sizes = Conv.DEPTH_CONV wordsLib.SIZES_CONV index
            handle Conv.UNCHANGED => Thm.REFL index
          val sized = boolSyntax.rhs (Thm.concl sizes)
          val evaluated = SmtResource.with_bitblast_step_time
            "cpc-trust-fp-projection-index" bossLib.EVAL sized
            handle Conv.UNCHANGED => Thm.REFL sized
          val index_theorem = Thm.TRANS sizes evaluated
          val _ = not (Term.aconv index
            (boolSyntax.rhs (Thm.concl index_theorem))) orelse
            raise Conv.UNCHANGED
        in Thm.MK_COMB (Thm.REFL (Term.rator term),
             index_theorem) end
      fun packed_index_conversion term =
        let
          val (word, _) = wordsSyntax.dest_index term
          val (head, _) = boolSyntax.strip_comb word
          val {Thy, Name, ...} = Term.dest_thy_const head
          val _ = Thy = "smtfloat" andalso Name = "smtfp_pack_bv"
            orelse raise Conv.UNCHANGED
        in
          Conv.RATOR_CONV
            (Conv.RAND_CONV
              (Conv.REWR_CONV smtfloatTheory.smtfp_pack_bv_def)) term
        end
      val projection_laws = ref
        ([] : (Term.term * Term.term * Term.term list * Thm.thm) list)
      val structural_count = ref 0
      val multiplication_laws = ref ([] : (int * Thm.thm) list)
      val multiplication_words = ref
        ([] : (Term.term * Thm.thm) list)
      fun multiplication_law width =
        case List.find (fn (saved_width, _) => saved_width = width)
            (!multiplication_laws) of
          SOME (_, theorem) => theorem
        | NONE =>
            let
              val _ = if OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" =
                         SOME "full" then
                  (Feedback.HOL_MESG
                    ("CPC FP mul law begin width=" ^
                     Int.toString width);
                   TextIO.flushOut TextIO.stdOut)
                else ()
              val schema = Thm.INST_TYPE
                [{redex = Type.alpha,
                  residue = fcpSyntax.mk_int_numeric_type width}]
                blastTheory.BITWISE_MUL
              val evaluated = Conv.CONV_RULE
                (Conv.STRIP_QUANT_CONV
                  (Conv.RHS_CONV bossLib.EVAL)) schema
              val theorem = Conv.CONV_RULE
                (Conv.STRIP_QUANT_CONV
                  (Conv.RHS_CONV
                    (Rewrite.PURE_REWRITE_CONV
                      [wordsTheory.WORD_ADD_0]))) evaluated
              val _ = multiplication_laws :=
                (width, theorem) :: !multiplication_laws
              val _ = if OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" =
                         SOME "full" then
                  (Feedback.HOL_MESG
                    ("CPC FP mul law done width=" ^
                     Int.toString width);
                   TextIO.flushOut TextIO.stdOut)
                else ()
            in theorem end
      fun multiplication_word_law product =
        case List.find (fn (saved, _) =>
            Portable.pointer_eq (saved, product) orelse
            shared_aconv saved product) (!multiplication_words) of
          SOME (_, theorem) => theorem
        | NONE =>
            let
              val (left, _) = wordsSyntax.dest_word_mul product
              val width = fcpSyntax.dest_int_numeric_type
                (wordsSyntax.dim_of left)
              val _ = if OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" =
                         SOME "full" then
                  (Feedback.HOL_MESG
                    ("CPC FP mul word begin width=" ^
                     Int.toString width);
                   TextIO.flushOut TextIO.stdOut)
                else ()
              val theorem = Conv.REWR_CONV
                (multiplication_law width) product
              val _ = multiplication_words :=
                (product, theorem) :: !multiplication_words
              val _ = if OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" =
                         SOME "full" then
                  (Feedback.HOL_MESG
                    ("CPC FP mul word done width=" ^
                     Int.toString width);
                   TextIO.flushOut TextIO.stdOut)
                else ()
            in theorem end
      fun multiplication_index_conversion term =
        let
          val (product, _) = wordsSyntax.dest_index term
          val theorem = multiplication_word_law product
        in
          Conv.RATOR_CONV (Conv.RAND_CONV (fn _ => theorem)) term
        end
      val mod_bit_laws = ref
        ([] : (int * Arbnum.num * Term.term * Thm.thm) list)
      fun mod_bit_law width index =
        let val numeral = numSyntax.dest_numeral index in
          case List.find (fn (saved_width, saved_index, _, _) =>
              saved_width = width andalso saved_index = numeral)
              (!mod_bit_laws) of
            SOME (_, _, variable, theorem) => (variable, theorem)
          | NONE =>
              let
                val variable = Term.genvar numSyntax.num
                val specialized = Drule.SPECL
                  [index, numSyntax.term_of_int width, variable]
                  smtfloatReplayRoundingTheory.smtfp_bit_mod_pow2
                val (premise, _) = boolSyntax.dest_imp
                  (Thm.concl specialized)
                val proved = Thm.MP specialized
                  (Drule.EQT_ELIM (bossLib.EVAL premise))
                val theorem = Conv.CONV_RULE
                  (Conv.LHS_CONV
                    (Conv.RAND_CONV
                      (Conv.RAND_CONV bossLib.EVAL))) proved
                val _ = mod_bit_laws :=
                  (width, numeral, variable, theorem) :: !mod_bit_laws
              in (variable, theorem) end
        end
      val add_bit_laws = ref
        ([] : (Arbnum.num * Term.term * Term.term * Thm.thm) list)
      fun add_bit_law index =
        let val numeral = numSyntax.dest_numeral index in
          case List.find (fn (saved, _, _, _) => saved = numeral)
              (!add_bit_laws) of
            SOME (_, left, right, theorem) =>
              (left, right, theorem)
          | NONE =>
              let
                val _ = Arbnum.<
                  (numeral, Arbnum.fromInt
                    SmtResource.max_skeleton_replay_dag_nodes) orelse
                  raise Conv.UNCHANGED
                val left = Term.genvar numSyntax.num
                val right = Term.genvar numSyntax.num
                val law = Drule.SPECL [index, left, right]
                  smtfloatReplayRoundingTheory.smtfp_bit_add
                val (first, second, input) =
                  case boolSyntax.strip_comb
                      (boolSyntax.rhs (Thm.concl law)) of
                    (_, [_, first, second, input]) =>
                      (first, second, input)
                  | _ => raise Conv.UNCHANGED
                val base = Drule.SPECL [first, second, input]
                  (Thm.CONJUNCT1 blastTheory.BCARRY_def)
                fun next_carry position previous =
                  let
                    val recurrence = Drule.SPECL
                      [numSyntax.term_of_int position,
                       first, second, input]
                      (Thm.CONJUNCT2 blastTheory.BCARRY_def)
                    val indexed = Conv.CONV_RULE
                      (Conv.LHS_CONV
                        (Conv.RATOR_CONV
                          (Conv.RATOR_CONV
                            (Conv.RATOR_CONV
                              (Conv.RAND_CONV
                                numLib.REDUCE_CONV))))) recurrence
                    val carried = Conv.CONV_RULE
                      (Conv.RHS_CONV
                        (Conv.RAND_CONV
                          (Conv.REWR_CONV previous))) indexed
                    val simplified = Conv.CONV_RULE
                      (Conv.RHS_CONV
                        (Conv.REWR_CONV
                          blastTheory.bcarry_def)) carried
                  in
                    Conv.CONV_RULE
                      (Conv.RHS_CONV
                        (Conv.DEPTH_CONV Thm.BETA_CONV)) simplified
                  end
                val carry = List.foldl
                  (fn (position, previous) =>
                    next_carry position previous) base
                  (List.tabulate (Arbnum.toInt numeral, fn i => i))
                val expanded = Conv.CONV_RULE
                  (Conv.RHS_CONV
                    (Conv.REWR_CONV blastTheory.BSUM_def)) law
                val carried = Conv.CONV_RULE
                  (Conv.RHS_CONV
                    (Conv.RAND_CONV
                      (Conv.REWR_CONV carry))) expanded
                val simplified = Conv.CONV_RULE
                  (Conv.RHS_CONV
                    (Conv.REWR_CONV blastTheory.bsum_def)) carried
                val theorem = Conv.CONV_RULE
                  (Conv.RHS_CONV
                    (Conv.DEPTH_CONV Thm.BETA_CONV)) simplified
                val _ = add_bit_laws :=
                  (numeral, left, right, theorem) :: !add_bit_laws
              in (left, right, theorem) end
        end
      fun arithmetic_bit_conversion term =
        let
          val (index, number) = bitSyntax.dest_bit term
          val _ = numSyntax.is_numeral index orelse
            raise Conv.UNCHANGED
        in
          case Lib.total numSyntax.dest_mod number of
            SOME (value, modulus) =>
              let
                val digits = Arbnum.toBinString
                  (numSyntax.dest_numeral modulus)
                val width = String.size digits - 1
                val _ = width > 0 andalso
                  String.sub (digits, 0) = #"1" andalso
                  List.all (fn digit => digit = #"0")
                    (String.explode
                      (String.extract (digits, 1, NONE))) orelse
                  raise Conv.UNCHANGED
                val (variable, law) = mod_bit_law width index
              in Thm.INST
                   [{redex = variable, residue = value}] law end
          | NONE =>
              (case Lib.total numSyntax.dest_plus number of
                 SOME (left, right) =>
                   let
                     val (left_var, right_var, law) =
                       add_bit_law index
                   in Thm.INST
                        [{redex = left_var, residue = left},
                         {redex = right_var, residue = right}] law
                   end
               | NONE =>
                   if boolSyntax.is_cond number then
                     Conv.REWR_CONV boolTheory.COND_RAND term
                   else raise Conv.UNCHANGED)
        end
      fun multiplication_projection_schema schematic =
        let
          val (product, index) = wordsSyntax.dest_index schematic
          val (left, _) = wordsSyntax.dest_word_mul product
          val width = fcpSyntax.dest_int_numeric_type
            (wordsSyntax.dim_of left)
          val bitwise = multiplication_law width
          val _ = if OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" =
                     SOME "full" then
              (Feedback.HOL_MESG
                ("CPC FP mul projection begin index=" ^
                 Library.term_to_string index);
               TextIO.flushOut TextIO.stdOut)
            else ()
          val projected = Conv.RATOR_CONV
            (Conv.RAND_CONV (Conv.REWR_CONV bitwise)) schematic
          val _ = if OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" =
                     SOME "full" then
              (Feedback.HOL_MESG
                ("CPC FP mul projection done index=" ^
                 Library.term_to_string index);
               TextIO.flushOut TextIO.stdOut)
            else ()
        in projected end
      fun word_projection_schema term =
        let
          val (word, index) = wordsSyntax.dest_index term
          val _ = numSyntax.is_numeral index orelse
            raise Conv.UNCHANGED
          val (head, arguments) = boolSyntax.strip_comb word
          val {Thy, ...} = Term.dest_thy_const head
          val _ = Thy = "words" orelse
            Thy = "smtfloatReplayWord" orelse
            raise Conv.UNCHANGED
          val (variables, law) =
            case List.find (fn (saved_head, saved_index, _, _) =>
                Term.aconv saved_head head andalso
                Term.aconv saved_index index) (!projection_laws) of
              SOME (_, _, saved_variables, saved_law) =>
                (saved_variables, saved_law)
            | NONE =>
                let
                  val variables =
                    List.map (Term.genvar o Term.type_of) arguments
                  val schematic = wordsSyntax.mk_index
                    (Term.list_mk_comb (head, variables), index)
                  val law =
                    (SmtResource.with_bitblast_step_time
                       "cpc-trust-fp-word-projection-schema"
                       (SmtWordGraph.normalize_with_node_conversion
                         SmtFpGraph.convert_word_projection) schematic
                     handle Conv.UNCHANGED =>
                       SmtResource.with_resource_step_time
                         "BitVector" "fp-word-mul-projection-schema"
                         multiplication_projection_schema schematic)
                  val _ = projection_laws :=
                    (head, index, variables, law) :: !projection_laws
                in (variables, law) end
          val theorem = Thm.INST
            (ListPair.mapEq (fn (variable, argument) =>
              {redex = variable, residue = argument})
              (variables, arguments)) law
          val _ = if wordsSyntax.is_word_mul word andalso
              OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" = SOME "full"
            then
              (Feedback.HOL_MESG
                ("CPC FP mul instantiated index=" ^
                 Library.term_to_string index);
               TextIO.flushOut TextIO.stdOut)
            else ()
          val _ = Term.aconv
            (boolSyntax.lhs (Thm.concl theorem)) term orelse
            raise Conv.UNCHANGED
        in theorem end
      val word_bit_laws = ref
        ([] : (Term.term * Term.term * Term.term list * Thm.thm) list)
      fun word_bit_schema term =
        let
          val (index, word) = wordsSyntax.dest_word_bit term
          val _ = numSyntax.is_numeral index orelse
            raise Conv.UNCHANGED
          val (head, arguments) = boolSyntax.strip_comb word
          (* Variable-word projections are primitive circuit atoms too.
             Their guarded word_bit spelling must normalize to the same
             FCP index in the structural path as in the ordinary path. *)
          val _ = Term.is_const head orelse Term.is_var head orelse
            raise Conv.UNCHANGED
          val (variables, law) =
            case List.find (fn (saved_head, saved_index, _, _) =>
                Term.aconv saved_head head andalso
                Term.aconv saved_index index) (!word_bit_laws) of
              SOME (_, _, saved_variables, saved_law) =>
                (saved_variables, saved_law)
            | NONE =>
                let
                  val variables =
                    List.map (Term.genvar o Term.type_of) arguments
                  val schematic = wordsSyntax.mk_word_bit
                    (index, Term.list_mk_comb (head, variables))
                  val law = SmtResource.with_bitblast_step_time
                    "cpc-trust-fp-word-bit-schema"
                    (SmtWordGraph.normalize_with_node_conversion
                      SmtFpGraph.convert_word_projection) schematic
                  val _ = word_bit_laws :=
                    (head, index, variables, law) :: !word_bit_laws
                in (variables, law) end
          val theorem = Thm.INST
            (ListPair.mapEq (fn (variable, argument) =>
              {redex = variable, residue = argument})
              (variables, arguments)) law
        in theorem end
      val word_relation_laws = ref
        ([] : (Term.term * Term.term list * Thm.thm) list)
      fun word_relation_schema term =
        let
          val (head, arguments) = boolSyntax.strip_comb term
          val _ = List.length arguments = 2 andalso
            wordsSyntax.is_word_type
              (Term.type_of (List.hd arguments)) orelse
            raise Conv.UNCHANGED
          val (variables, law) =
            case List.find (fn (saved_head, _, _) =>
                Term.aconv saved_head head) (!word_relation_laws) of
              SOME (_, saved_variables, saved_law) =>
                (saved_variables, saved_law)
            | NONE =>
                let
                  val variables =
                    List.map (Term.genvar o Term.type_of) arguments
                  val schematic =
                    Term.list_mk_comb (head, variables)
                  val law = SmtResource.with_bitblast_step_time
                    "cpc-trust-fp-word-relation-schema"
                    SmtWordGraph.normalize schematic
                  val _ = word_relation_laws :=
                    (head, variables, law) :: !word_relation_laws
                in (variables, law) end
          val theorem = Thm.INST
            (ListPair.mapEq (fn (variable, argument) =>
              {redex = variable, residue = argument})
              (variables, arguments)) law
        in theorem end
      fun structural_leaf_conversion term =
        case ground_leaf_conversion term of
          SOME theorem => SOME theorem
        | NONE =>
            (case if SmtFpGraph.lower_atom_domain term then
                SOME (SmtFpGraph.convert_atom term)
              else NONE of
               SOME theorem => SOME theorem
             | NONE => case Lib.total
                (Conv.FIRST_CONV circuit_leaf_rewrites) term of
               SOME theorem => SOME theorem
             | NONE =>
               let
                 fun attempt conversion =
                   SOME (Conv.CHANGED_CONV conversion term)
                   handle Conv.UNCHANGED => NONE
                        | Feedback.HOL_ERR holerr =>
                            if SmtResource.is_resource_gate holerr then
                              raise Feedback.HOL_ERR holerr
                            else NONE
               in
                 case attempt projection_index_conversion of
                   SOME theorem => SOME theorem
                 | NONE =>
                     (case attempt packed_index_conversion of
                        SOME theorem => SOME theorem
                      | NONE => case attempt
                          multiplication_index_conversion of
                        SOME theorem => SOME theorem
                      | NONE => case attempt
                          arithmetic_bit_conversion of
                        SOME theorem => SOME theorem
                      | NONE => case attempt word_projection_schema of
                        SOME theorem => SOME theorem
                      | NONE =>
                          (case attempt word_bit_schema of
                             SOME theorem => SOME theorem
                           | NONE => attempt word_relation_schema))
               end)
      fun structural_circuit term =
        case alpha_lookup memo term of
          SOME result => result
        | NONE =>
            let
              fun internal_with proof skeleton =
                let
                  val result = variable term
                  val definition = boolSyntax.mk_eq (result, skeleton)
                  val _ = definitions :=
                    (term, definition, proof) :: !definitions
                  val _ = structural_count := !structural_count + 1
                  val _ =
                    if !structural_count mod 20000 = 0 andalso
                       OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" =
                         SOME "1" then
                      (Feedback.HOL_MESG
                        ("CPC FP structural nodes=" ^
                         Int.toString (!structural_count));
                       TextIO.flushOut TextIO.stdOut)
                    else ()
                in result end
              fun internal skeleton = internal_with NONE skeleton
              val result =
                if Term.aconv term boolSyntax.T orelse
                   Term.aconv term boolSyntax.F then term
                else if boolSyntax.is_neg term then
                  internal (boolSyntax.mk_neg
                    (structural_circuit (boolSyntax.dest_neg term)))
                else if boolSyntax.is_conj term then
                  let val (left, right) = boolSyntax.dest_conj term
                  in internal (boolSyntax.mk_conj
                    (structural_circuit left,
                     structural_circuit right)) end
                else if boolSyntax.is_disj term then
                  let val (left, right) = boolSyntax.dest_disj term
                  in internal (boolSyntax.mk_disj
                    (structural_circuit left,
                     structural_circuit right)) end
                else if boolSyntax.is_imp term then
                  let val (left, right) = boolSyntax.dest_imp term
                  in internal (boolSyntax.mk_imp
                    (structural_circuit left,
                     structural_circuit right)) end
                else if boolSyntax.is_eq term andalso
                        Term.type_of (#1 (boolSyntax.dest_eq term)) =
                          Type.bool then
                  let val (left, right) = boolSyntax.dest_eq term
                  in internal (boolSyntax.mk_eq
                    (structural_circuit left,
                     structural_circuit right)) end
                else if boolSyntax.is_cond term andalso
                        Term.type_of (#2 (boolSyntax.dest_cond term)) =
                          Type.bool then
                  let
                    val (condition, then_term, else_term) =
                      boolSyntax.dest_cond term
                  in internal (boolSyntax.mk_cond
                    (structural_circuit condition,
                     structural_circuit then_term,
                     structural_circuit else_term)) end
                else
                  (case structural_leaf_conversion term of
                     SOME theorem =>
                       internal_with (SOME theorem)
                         (structural_circuit
                           (boolSyntax.rhs (Thm.concl theorem)))
                   | NONE => leaf term)
              val _ = insert memo term result
            in result end
      fun circuit term =
        case alpha_lookup memo term of
          SOME result => result
        | NONE =>
          if Option.isSome (pointer_lookup active term) then leaf term
          else
            let
              val _ = insert active term ()
              fun internal_with proof skeleton =
                let
                  val result = variable term
                  val definition = boolSyntax.mk_eq (result, skeleton)
                  val _ = definitions :=
                    (term, definition, proof) :: !definitions
                in result end
              fun internal skeleton = internal_with NONE skeleton
              val result =
                if Term.aconv term boolSyntax.T orelse
                   Term.aconv term boolSyntax.F then term
                else if boolSyntax.is_neg term then
                  internal (boolSyntax.mk_neg
                    (circuit (boolSyntax.dest_neg term)))
                else if boolSyntax.is_conj term then
                  let val (left, right) = boolSyntax.dest_conj term
                  in internal (boolSyntax.mk_conj
                    (circuit left, circuit right)) end
                else if boolSyntax.is_disj term then
                  let val (left, right) = boolSyntax.dest_disj term
                  in internal (boolSyntax.mk_disj
                    (circuit left, circuit right)) end
                else if boolSyntax.is_imp term then
                  let val (left, right) = boolSyntax.dest_imp term
                  in internal (boolSyntax.mk_imp
                    (circuit left, circuit right)) end
                else if boolSyntax.is_eq term andalso
                        Term.type_of (#1 (boolSyntax.dest_eq term)) =
                          Type.bool then
                  let val (left, right) = boolSyntax.dest_eq term
                  in internal (boolSyntax.mk_eq
                    (circuit left, circuit right)) end
                else if boolSyntax.is_cond term andalso
                        Term.type_of (#2 (boolSyntax.dest_cond term)) =
                          Type.bool then
                  let val (condition, then_term, else_term) =
                    boolSyntax.dest_cond term
                  in internal (boolSyntax.mk_cond
                    (circuit condition, circuit then_term,
                     circuit else_term)) end
                else
                  let
                    fun attempt conversion =
                      (* Reflexivity must not hide a later applicable rule. *)
                      SOME (Conv.CHANGED_CONV conversion term)
                      handle Conv.UNCHANGED => NONE
                           | Feedback.HOL_ERR holerr =>
                               if SmtResource.is_resource_gate holerr then
                                 raise Feedback.HOL_ERR holerr
                               else NONE
                    fun first_conversion [] = NONE
                      | first_conversion (conversion :: rest) =
                          (case attempt conversion of
                             SOME theorem => SOME theorem
                           | NONE => first_conversion rest)
                    fun fcp_shift_conversion current =
                      let
                        val (head, arguments) =
                          boolSyntax.strip_comb current
                        val {Thy, ...} = Term.dest_thy_const head
                        val _ = Thy = "fcp" andalso
                                not (List.null arguments) orelse
                          raise Conv.UNCHANGED
                        val (indexed_head, _) = boolSyntax.strip_comb
                          (List.hd arguments)
                        val {Thy = indexed_theory,
                             Name = indexed_name, ...} =
                          Term.dest_thy_const indexed_head
                        val _ = indexed_theory = "words" orelse
                          raise Conv.UNCHANGED
                        val bitblast = List.exists
                          (fn name => indexed_name = name)
                          ["word_add", "word_lsl_bv", "word_lsr_bv",
                           "word_asr_bv"]
                      in
                        if bitblast then
                          let
                            val _ = Option.isSome
                                (Term.term_size_bounded
                                  SmtResource.max_skeleton_replay_dag_nodes
                                  current) orelse
                              raise Conv.UNCHANGED
                          in
                            SmtResource.with_bitblast_step_time
                              "cpc-trust-fp-fcp-word-operation"
                              blastLib.BBLAST_CONV current
                          end
                        else
                          let
                            val law =
                              if indexed_name = "word_lsl" then
                                smtfloatReplayRoundingTheory.word_lsl_index
                              else if indexed_name = "word_lsr" then
                                smtfloatReplayRoundingTheory.word_lsr_index
                              else if indexed_name = "word_asr" then
                                smtfloatReplayRoundingTheory.word_asr_index
                              else raise Conv.UNCHANGED
                            val schema = Drule.SPEC_ALL law
                            val (_, equation) = boolSyntax.dest_imp
                              (Thm.concl schema)
                            val specialized = Drule.INST_TY_TERM
                              (Term.match_term
                                (boolSyntax.lhs equation) current) schema
                            val (bound, _) = boolSyntax.dest_imp
                              (Thm.concl specialized)
                            val width = fcpLib.index_to_num
                              (wordsSyntax.dest_word_type
                                (Term.type_of (List.hd arguments)))
                            val bound_proof = Drule.EQT_ELIM
                              (simpLib.SIMP_CONV bossLib.std_ss
                                [fcpLib.DIMINDEX width] bound)
                          in
                            Thm.MP specialized bound_proof
                          end
                      end
                    val normalized =
                      case first_conversion
                          circuit_leaf_rewrites of
                        SOME theorem => SOME theorem
                      | NONE =>
                      case if SmtFpGraph.lower_atom_domain term then
                          attempt SmtFpGraph.convert_atom
                        else NONE of
                        SOME theorem => SOME theorem
                      | NONE =>
                      case attempt projection_index_conversion of
                        SOME theorem => SOME theorem
                      | NONE =>
                      case attempt packed_index_conversion of
                        SOME theorem => SOME theorem
                      | NONE =>
                      case attempt multiplication_index_conversion of
                        SOME theorem => SOME theorem
                      | NONE =>
                      case attempt arithmetic_bit_conversion of
                        SOME theorem => SOME theorem
                      | NONE =>
                      (* Lower one operator with schematic operands, as in
                         the structural path; do not repeatedly normalize
                         the whole shared word below each projection. *)
                      case attempt word_projection_schema of
                        SOME theorem => SOME theorem
                      | NONE =>
                      case attempt word_relation_schema of
                        SOME theorem => SOME theorem
                      | NONE =>
                      case attempt word_bit_schema of
                        SOME theorem => SOME theorem
                      | NONE =>
                      case attempt
                          (SmtWordGraph.normalize_with_node_conversion
                            SmtFpGraph.convert_word_projection) of
                        SOME theorem => SOME theorem
                      | NONE =>
                      case attempt SmtWordGraph.normalize of
                        SOME theorem => SOME theorem
                      | NONE =>
                      case attempt fcp_shift_conversion of
                        SOME theorem => SOME theorem
                      | NONE =>
                          if SmtResource.dag_nodes_up_to 33 term <= 32 then
                            (case attempt
                                (simpLib.SIMP_CONV
                                  (bossLib.srw_ss()) []) of
                               SOME theorem => SOME theorem
                             | NONE => ground_leaf_conversion term)
                          else NONE
                  in
                    case normalized of
                      SOME theorem =>
                        let
                          val residue = boolSyntax.rhs (Thm.concl theorem)
                          val maximum =
                            SmtResource.max_skeleton_replay_dag_nodes
                          val bounded =
                            SmtResource.dag_nodes_up_to (maximum + 1)
                              residue <= maximum andalso
                            Option.isSome
                              (Term.term_size_bounded maximum residue)
                        in
                          if bounded then internal_with (SOME theorem)
                            (circuit residue)
                          else internal_with (SOME theorem)
                            (structural_circuit residue)
                        end
                    | NONE => leaf term
                  end
              val _ = insert memo term result
            in result end
      val root = SmtResource.with_resource_step_time
        "BitVector" "cpc-fp-circuit-lower" circuit goal
      val definitions = List.rev (!definitions)
      fun cnf_definition (_, definition, _) =
        SmtCircuitSat.definition_cnf definition
      val cnf_equivalence = SmtResource.with_resource_step_time
        "BitVector" "cpc-fp-circuit-cnf"
        (fn () => SmtCircuitSat.balanced_equivalences
          (List.map cnf_definition definitions)) ()
      val cnf_body = boolSyntax.rhs (Thm.concl cnf_equivalence)
      val template =
        if List.null definitions then root
        else boolSyntax.mk_imp (cnf_body, root)
      val large_circuit = List.length definitions > 256
      val _ =
        if OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" = SOME "1"
          orelse OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" =
            SOME "full" then
          let
            val leaf_count = Array.foldl
              (fn (bucket, count) => List.length bucket + count)
              0 leaves
            val add_summary =
              if OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" =
                 SOME "full" then
                let
                  val terms = Array.foldl
                    (fn (bucket, result) =>
                      List.map Lib.fst bucket @ result) [] leaves
                  fun projection term =
                    let val (word, index) =
                      wordsSyntax.dest_index term
                    in if wordsSyntax.is_word_add word then
                         SOME (term, index)
                       else NONE end
                    handle Feedback.HOL_ERR _ => NONE
                  val projections = List.mapPartial projection terms
                  val numeric = List.length
                    (List.filter (numSyntax.is_numeral o Lib.snd)
                      projections)
                  val bounded = List.length (List.filter
                    (fn (term, _) => Option.isSome
                      (Term.term_size_bounded
                        SmtResource.max_skeleton_replay_dag_nodes
                        term)) projections)
                  val closed = List.length (List.filter
                    (List.null o Term.free_vars o Lib.snd)
                    projections)
                  fun reduced_numeral (_, index) =
                    let
                      val sizes = Conv.DEPTH_CONV
                        wordsLib.SIZES_CONV index
                        handle Conv.UNCHANGED => Thm.REFL index
                      val sized = boolSyntax.rhs
                        (Thm.concl sizes)
                      val evaluated = bossLib.EVAL sized
                        handle Conv.UNCHANGED => Thm.REFL sized
                    in numSyntax.is_numeral
                      (boolSyntax.rhs (Thm.concl evaluated)) end
                    handle Feedback.HOL_ERR _ => false
                  val reducible = List.length
                    (List.filter reduced_numeral projections)
                  val index_nodes = List.foldl
                    (fn ((_, index), maximum) =>
                      Int.max (maximum,
                        SmtResource.dag_nodes_up_to 257 index))
                    0 projections
                  fun head_name term =
                    let val (head, _) =
                      boolSyntax.strip_comb term
                    in if Term.is_const head then
                         let val {Thy, Name, ...} =
                           Term.dest_thy_const head
                         in Thy ^ "$" ^ Name end
                       else if Term.is_var head then "variable"
                       else "other" end
                  fun label term =
                    let val (head, arguments) =
                      boolSyntax.strip_comb term
                    in if Term.is_const head andalso
                          #Thy (Term.dest_thy_const head) = "fcp"
                       then case arguments of
                          first :: _ => head_name term ^ "[" ^
                            head_name first ^ "]"
                        | _ => head_name term
                       else head_name term end
                  fun count (term, counts) =
                    let
                      val name = label term
                      val prior = case List.find
                          (fn (saved, _) => saved = name) counts of
                          SOME (_, n) => n
                        | NONE => 0
                    in (name, prior + 1) ::
                      List.filter (fn (saved, _) => saved <> name)
                        counts end
                  val classes = List.foldl count [] terms
                  fun multiplication_operands term =
                    let
                      val (word, _) = wordsSyntax.dest_index term
                      val (left, right) =
                        wordsSyntax.dest_word_mul word
                    in SOME (head_name left ^ "*" ^ head_name right)
                    end
                    handle Feedback.HOL_ERR _ => NONE
                  val mul_operands = List.foldl
                    (fn (term, classes) =>
                      case multiplication_operands term of
                        SOME name =>
                          if List.exists (fn saved => saved = name)
                              classes then classes else name :: classes
                      | NONE => classes) [] terms
                  val mul_widths = List.foldl
                    (fn (term, widths) =>
                      let
                        val (word, _) = wordsSyntax.dest_index term
                        val _ = wordsSyntax.is_word_mul word orelse
                          raise Conv.UNCHANGED
                        val width = fcpLib.index_to_num
                          (wordsSyntax.dest_word_type
                            (Term.type_of word))
                      in
                        if List.exists (fn saved => saved = width) widths
                          then widths else width :: widths
                      end
                      handle Feedback.HOL_ERR _ => widths
                           | Conv.UNCHANGED => widths) [] terms
                  val class_text = SmtResource.bounded_text 500
                    (String.concatWith ","
                      (List.map (fn (name, n) =>
                        name ^ "=" ^ Int.toString n) classes))
                  val word_bit_text = String.concatWith ","
                    (List.map (SmtResource.bounded_text 500 o
                      String.translate
                        (fn #"\n" => " " | c => str c) o
                      Library.term_to_string)
                      (List.filter (fn term =>
                        head_name term = "words$word_bit") terms))
                  val variable_bit_text = String.concatWith ","
                    (List.map (SmtResource.bounded_text 120 o
                      Library.term_to_string)
                      (List.filter (fn term =>
                        case boolSyntax.strip_comb term of
                          (head, first :: _) =>
                            head_name head = "fcp$fcp_index" andalso
                            Term.is_var first
                        | _ => false) terms))
                  in
                    " word-add=" ^
                    Int.toString (List.length projections) ^
                    "/" ^ Int.toString numeric ^
                    "/" ^ Int.toString bounded ^
                    "/" ^ Int.toString closed ^
                    "/" ^ Int.toString reducible ^
                    "/" ^ Int.toString index_nodes ^
                    " word-mul-widths=" ^
                    String.concatWith ","
                      (List.map Arbnum.toString mul_widths) ^
                    " word-mul-operands=" ^
                    String.concatWith "," mul_operands ^
                    " heads=" ^ class_text ^
                  " word-bit=" ^ word_bit_text ^
                  " variable-bit=" ^ variable_bit_text
                end
              else ""
          in
            Feedback.HOL_MESG
              ("CPC FP circuit: definitions=" ^
               Int.toString (List.length definitions) ^
               " leaves=" ^ Int.toString leaf_count ^
               " elapsed=" ^
               Real.toString
                 (Time.toReal
                   (Time.- (Time.now (), circuit_started))) ^
               add_summary);
            TextIO.flushOut TextIO.stdOut
          end
        else ()
      val law = SmtResource.with_resource_step_time
        (if large_circuit then "BitVector" else "Skeleton")
        "cpc-trust-fp-atom-circuit-sat"
        (fn () =>
          if List.null definitions then
            HolSatLib.SAT_PROVE_ONLY template
          else
            SmtCircuitSat.prove_cnf (cnf_body, root)) ()
        handle Feedback.HOL_ERR holerr =>
          (if OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" = SOME "1" orelse
              OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" = SOME "full" then
             (Feedback.HOL_MESG
               ("CPC FP circuit SAT declined: " ^
                SmtResource.bounded_text 200
                  (Feedback.message_of holerr));
              TextIO.flushOut TextIO.stdOut)
           else ();
           raise Feedback.HOL_ERR holerr)
      val _ = if OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" =
            SOME "full" orelse
            OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" =
              SOME "1" then
          (Feedback.HOL_MESG
            ("CPC FP circuit SAT elapsed=" ^
             Real.toString
               (Time.toReal
                 (Time.- (Time.now (), circuit_started))));
           TextIO.flushOut TextIO.stdOut)
        else ()
      val theorem = SmtResource.with_resource_step_time
        "BitVector" "cpc-fp-circuit-instantiation"
        (fn () => Thm.INST (!substitutions) law) ()
      val alignment_memo = Array.array
        (boolean_dag_bucket_count,
         [] : (Term.term * Term.term * Thm.thm) list)
      fun alignment_index left right =
        (boolean_dag_term_hash 3 left * 67 +
         boolean_dag_term_hash 3 right) mod
        boolean_dag_bucket_count
      fun alignment_peek left right =
        case List.find (fn (saved_left, saved_right, _) =>
            Portable.pointer_eq (saved_left, left) andalso
            Portable.pointer_eq (saved_right, right))
            (Array.sub
              (alignment_memo, alignment_index left right)) of
          SOME (_, _, theorem) => SOME theorem
        | NONE => NONE
      fun alignment_insert left right theorem =
        let val index = alignment_index left right in
          Array.update
            (alignment_memo, index,
             (left, right, theorem) ::
               Array.sub (alignment_memo, index))
        end
      fun align left right =
        case alignment_peek left right of
          SOME proof =>
            SmtSkeletonProve.anchor_right right
              (SmtSkeletonProve.anchor_left left proof)
        | NONE =>
            let
              val proof =
                if Portable.pointer_eq (left, right) then Thm.REFL left
                else if Term.is_comb left andalso Term.is_comb right then
                  Thm.MK_COMB
                    (align (Term.rator left) (Term.rator right),
                     align (Term.rand left) (Term.rand right))
                else if Term.aconv left right then Thm.REFL left
                else raise ERR "trust"
                  "FP atom circuit definition endpoints differ"
              val _ = alignment_insert left right proof
            in proof end
      val result = SmtResource.with_resource_step_time
        "BitVector" "cpc-fp-circuit-reconstruct"
        (fn () => if List.null definitions then theorem
        else
          let
            val instantiated_equivalence =
              Thm.INST (!substitutions) cnf_equivalence
            val antecedent = boolSyntax.lhs
              (Thm.concl instantiated_equivalence)
            fun prove_definition
                ((_, _, proof), instantiated_definition) =
              let
                val (left, _) =
                  boolSyntax.dest_eq instantiated_definition
                val base =
                  case proof of
                    SOME theorem =>
                      SmtSkeletonProve.anchor_left left theorem
                  | NONE => Thm.REFL left
              in
                Thm.EQ_MP (Thm.REFL instantiated_definition) base
              end
            fun prove_tree term remaining =
              if boolSyntax.is_conj term then
                let
                  val (left, right) = boolSyntax.dest_conj term
                  val (left_proof, after_left) =
                    prove_tree left remaining
                  val (right_proof, after_right) =
                    prove_tree right after_left
                in
                  (Thm.EQ_MP (Thm.REFL term)
                     (Thm.CONJ left_proof right_proof),
                   after_right)
                end
              else
                case remaining of
                  definition :: rest =>
                    (prove_definition (definition, term), rest)
                | [] => raise ERR "trust"
                    "FP atom circuit definition tree is too short"
            val (definition_theorem, remaining) =
              prove_tree antecedent definitions
            val _ = List.null remaining orelse raise ERR "trust"
              "FP atom circuit definition tree is too long"
            val cnf_theorem = Thm.EQ_MP instantiated_equivalence
              definition_theorem
          in Thm.MP theorem cnf_theorem end) ()
    in result
    end
  fun replay_trust force_fp state prems args =
    let
      val target = expect_one_arg "trust" args
      fun context_terms () =
        HOLset.listItems (#asserted_hyps state) @ #scope_hyps state @
        List.map Thm.concl prems
      fun discharge_prems thm =
        List.foldl (fn (premise, proved) => Drule.PROVE_HYP premise proved)
          thm prems
      fun prove_scoped_arithmetic () =
        discharge_prems (Tactical.TAC_PROOF ((context_terms (), target),
          Tactical.THEN
            (Tactical.REPEAT Tactic.COND_CASES_TAC,
             Tactical.THEN
               (bossLib.FULL_SIMP_TAC (bossLib.srw_ss()) [],
                intLib.ARITH_TAC))))
      fun replay_rdiv () =
        let
          val (left, right) = boolSyntax.dest_eq target
          val (f, operands) = boolSyntax.strip_comb left
          val smt_rdiv = Term.prim_mk_const
            {Thy = "HolSmt", Name = "smt_rdiv"}
          val (numerator, denominator) =
            case operands of [x, y] => (x, y)
            | _ => raise ERR "trust" "expected binary smt_rdiv term"
          val _ = Term.same_const f smt_rdiv orelse
            raise ERR "trust" "unsupported trusted operator"
          fun valid_nonzero_rewrite () =
            let
              val nonzero = Tactical.TAC_PROOF
                (([], boolSyntax.mk_neg
                    (boolSyntax.mk_eq (denominator, realSyntax.zero_tm))),
                 bossLib.SIMP_TAC (bossLib.srw_ss()) [])
              val to_div = Thm.MP
                (Drule.SPECL [numerator, denominator]
                  HolSmtTheory.smt_rdiv_eq_div) nonzero
              val div_to_right = Tactical.TAC_PROOF
                (([], boolSyntax.mk_eq
                    (realSyntax.mk_div (numerator, denominator), right)),
                 bossLib.SIMP_TAC (bossLib.srw_ss()) [realTheory.real_div])
            in
              Thm.TRANS to_div div_to_right
            end
          fun irrelevant_zero_rewrite () =
            let
              val _ = Term.aconv right
                (realSyntax.mk_div (numerator, denominator)) orelse
                raise ERR "trust" "trusted rewrite is not rdiv-to-division"
              val _ = Tactical.TAC_PROOF
                (([], boolSyntax.mk_eq (denominator, realSyntax.zero_tm)),
                 bossLib.SIMP_TAC (bossLib.srw_ss()) [])
            in
              Thm.REFL left
            end
        in
          profile "CPC(rung:trust/rdiv_nonzero)" valid_nonzero_rewrite ()
          handle Feedback.HOL_ERR _ =>
            profile "CPC(rung:trust/rdiv_zero_irrelevant)"
              irrelevant_zero_rewrite ()
        end
      fun replay_set () =
        let
          val context =
            HOLset.listItems (#asserted_hyps state) @ #scope_hyps state @
            List.map Thm.concl prems
          fun card_lower_bound () =
            let
              val (injected_card, lower) = intSyntax.dest_geq target
              val number = intSyntax.dest_injected injected_card
              val set = pred_setSyntax.dest_card number
            in
              if Term.aconv lower intSyntax.zero_tm then
                let
                  val n = Term.genvar numSyntax.num
                  val proof = Tactical.TAC_PROOF
                    (([], intSyntax.mk_geq
                       (Term.mk_comb (intSyntax.int_injection, n), lower)),
                     intLib.ARITH_TAC)
                in Thm.INST [{redex = n, residue = number}] proof end
              else
                let
                  val _ = Term.aconv lower intSyntax.one_tm orelse
                    raise ERR "trust" "expected cardinality lower bound one"
                  fun member_of_set tm =
                    case Lib.total pred_setSyntax.dest_in tm of
                      SOME (_, member_set) => Term.aconv member_set set
                    | NONE => false
                  val membership =
                    case List.find member_of_set context of
                      SOME tm => tm
                    | NONE => raise ERR "trust" "missing Set membership premise"
                  val (element, _) = pred_setSyntax.dest_in membership
                  val finite = Tactical.TAC_PROOF
                    ((context, pred_setSyntax.mk_finite set),
                     bossLib.ASM_SIMP_TAC (bossLib.srw_ss ()) [])
                  val s = Term.genvar (Term.type_of set)
                  val x = Term.genvar (Term.type_of element)
                  val member = pred_setSyntax.mk_in (x, s)
                  val nonzero = boolSyntax.mk_neg
                    (boolSyntax.mk_eq
                      (pred_setSyntax.mk_card s, numSyntax.zero_tm))
                  val nonzero_proof = Tactical.TAC_PROOF
                    (([member, pred_setSyntax.mk_finite s], nonzero),
                     bossLib.METIS_TAC
                       [pred_setTheory.CARD_EQ_0,
                        pred_setTheory.MEMBER_NOT_EMPTY])
                  val positive = Tactical.TAC_PROOF
                    (([nonzero], intSyntax.mk_geq
                       (Term.mk_comb (intSyntax.int_injection,
                          pred_setSyntax.mk_card s), intSyntax.one_tm)),
                     intLib.ARITH_TAC)
                  val instantiated = Thm.INST [{redex = s, residue = set},
                       {redex = x, residue = element}]
                    (Drule.PROVE_HYP nonzero_proof positive)
                in
                  Drule.PROVE_HYP finite instantiated
                end
            end
          fun contextual () =
            Tactical.TAC_PROOF ((context, target),
              bossLib.ASM_SIMP_TAC (bossLib.srw_ss ()) [])
            handle Feedback.HOL_ERR holerr =>
              if SmtResource.is_resource_gate holerr then
                raise Feedback.HOL_ERR holerr
              else card_lower_bound ()
          val thm = SmtResource.with_resource_step_time "Set" "contextual"
            (fn () =>
              (List.app (SmtResource.check_resource_goal "Set" "contextual")
                 (target :: context);
               contextual ())) ()
        in
          List.foldl (fn (premise, proved) => Drule.PROVE_HYP premise proved)
            thm prems
        end
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else
            SmtArrayProve.array_prove target
      fun unsupported_set () =
        raise ERR "trust"
          ("unsupported CPC Set step: rule=trust; theory=set; " ^
           "conclusion=" ^ Library.term_to_string target)
      fun replay_bag () =
        SmtBagProve.bag_prove_with_arith arith_prove target
      fun prove_scoped_bag () =
        let
          val context =
            HOLset.listItems (#asserted_hyps state) @ #scope_hyps state @
            List.map Thm.concl prems
          val thm = SmtResource.with_resource_step_time "Bag" "contextual"
            (fn () =>
              (SmtResource.check_resource_goal "Bag" "contextual" target;
               Tactical.TAC_PROOF ((context, target),
                 Tactical.THEN
                   (Tactical.REPEAT Tactic.COND_CASES_TAC,
                    Tactical.THEN
                      (bossLib.FULL_SIMP_TAC (bossLib.srw_ss()) [],
                       intLib.ARITH_TAC))))) ()
        in
          List.foldl (fn (premise, proved) => Drule.PROVE_HYP premise proved)
            thm prems
        end
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else
            raise ERR "trust"
              ("unsupported CPC Bag step: rule=trust; theory=bag; " ^
               "conclusion=" ^ Library.term_to_string target)
      fun replay_fp () =
        SmtFpProve.fp_prove_with_decompositions_and_arith
          arith_prove [] target
      fun replay_fp_word_bridge () =
        let
          fun is_fp_type ty =
            let val {Thy, Tyop, ...} = Type.dest_thy_type ty
            in Thy = "smtfloat" andalso Tyop = "smtfp" end
            handle Feedback.HOL_ERR _ => false
          fun source_value term =
            is_fp_type (Term.type_of term) andalso
            (Term.is_var term orelse boolSyntax.is_select term)
          val sources = ref ([] : Term.term list)
          val seen = ref (HOLset.empty Term.compare)
          fun collect term =
            if HOLset.member (!seen, term) then ()
            else
              (seen := HOLset.add (!seen, term);
               if source_value term then
                 if List.exists (fn saved => Term.aconv saved term)
                     (!sources) then ()
                 else sources := term :: !sources
               else List.app collect (SmtResource.term_children term))
          val _ = collect target
          val variables = List.map (Term.genvar o Term.type_of) (!sources)
          val pairs = ListPair.zip (!sources, variables)
          val memo = ref
            (Redblackmap.mkDict Term.compare :
              (Term.term, Term.term) Redblackmap.dict)
          fun abstract term =
            case Redblackmap.peek (!memo, term) of
              SOME result => result
            | NONE =>
                let
                  val result =
                    case List.find (fn (source, _) => Term.aconv source term)
                        pairs of
                      SOME (_, variable) => variable
                    | NONE =>
                        if Term.is_comb term then
                          Term.mk_comb
                            (abstract (Term.rator term),
                             abstract (Term.rand term))
                        else term
                  val _ = memo := Redblackmap.insert (!memo, term, result)
                in result end
          val schematic_target = abstract target
          val (left, right) = boolSyntax.dest_eq schematic_target
          fun fp_value_equality term =
            boolSyntax.is_eq term andalso
            let val (first, second) = boolSyntax.dest_eq term in
              Term.type_of first <> Type.bool andalso
              Term.type_of first = Term.type_of second andalso
              SmtFpGraph.lower_atom_domain term
            end
          val _ = Term.type_of left = Type.bool andalso
              (fp_value_equality left orelse fp_value_equality right) orelse
            raise ERR "trust"
              "not a Boolean bridge for floating-point value equality"
          val schematic_proof =
          (fn target =>
            let
              val (left, right) = boolSyntax.dest_eq target
              val left_theorem = SmtFpGraph.convert_atom left
              val equality_head = Term.rator (Term.rator target)
              val converted = Thm.MK_COMB
                (Thm.MK_COMB (Thm.REFL equality_head, left_theorem),
                 Thm.REFL right)
              val converted_residue =
                boolSyntax.rhs (Thm.concl converted)
              val bit_leaf_ss = simpLib.++
                (simpLib.empty_ss, fcpLib.FCP_ss)
              val arithmetic_leaf_ss = simpLib.++
                (bossLib.srw_ss(), wordsLib.WORD_BIT_EQ_ss)
              fun bridge_node_conversion term =
                (SmtFpGraph.convert_word_projection term
                 handle Conv.UNCHANGED =>
                   let
                     val (head, _) = boolSyntax.strip_comb term
                     val _ = Term.is_const head orelse raise Conv.UNCHANGED
                     val {Thy, ...} = Term.dest_thy_const head
                   in
                     if Thy = "fcp" then
                       let
                         val (_, arguments) = boolSyntax.strip_comb term
                         val indexed = List.hd arguments
                         val (indexed_head, _) =
                           boolSyntax.strip_comb indexed
                         val {Thy = indexed_theory,
                              Name = indexed_name, ...} =
                           Term.dest_thy_const indexed_head
                       in
                         if indexed_theory = "words" andalso
                            indexed_name = "word_compare" then
                           Conv.REWR_CONV
                             smtfloatReplayRoundingTheory.word_compare_index
                             term
                         else raise Conv.UNCHANGED
                       end
                     else if List.exists (fn name => Thy = name)
                         ["bit", "prim_rec", "arithmetic"] then
                       simpLib.SIMP_CONV arithmetic_leaf_ss [] term
                     else raise Conv.UNCHANGED
                   end)
                handle Empty => raise Conv.UNCHANGED
              fun normalize_words 0 current = current
                | normalize_words remaining current =
                    let
                      val residue = boolSyntax.rhs (Thm.concl current)
                      val next = SmtResource.with_bitblast_step_time
                        "cpc-trust-fp-word-normalize"
                        (SmtWordGraph.normalize_with_node_conversion
                          bridge_node_conversion) residue
                    in normalize_words (remaining - 1)
                      (Thm.TRANS current next) end
                    handle Conv.UNCHANGED => current
              val word_theorem =
                normalize_words 8 (Thm.REFL converted_residue)
              val normalized = Thm.TRANS converted word_theorem
              val residue = boolSyntax.rhs (Thm.concl normalized)
              (* The compact bridge input was admitted by SmtWordGraph.
                 Its checked conversion may generate a larger but shared
                 Boolean output, just as ordinary skeleton atom expansion
                 may; do not reclassify that generated graph as a fresh
                 untrusted input. *)
              fun leaf_theory atom =
                let val (head, _) = boolSyntax.strip_comb atom in
                  if Term.is_const head then
                    SOME (#Thy (Term.dest_thy_const head))
                  else NONE
                end
              fun fcp_conversion atom =
                let
                  val (_, arguments) = boolSyntax.strip_comb atom
                  val indexed = List.hd arguments
                  val (head, _) = boolSyntax.strip_comb indexed
                  val {Thy, Name, ...} = Term.dest_thy_const head
                in
                  if Thy = "words" andalso Name = "word_compare" then
                    Conv.REWR_CONV
                      smtfloatReplayRoundingTheory.word_compare_index atom
                  else if Thy = "words" andalso Name = "n2w" then
                    Conv.REWR_CONV wordsTheory.word_index_n2w atom
                  else if Thy = "bool" andalso Name = "COND" then
                    simpLib.SIMP_CONV bit_leaf_ss
                      [boolTheory.COND_RAND] atom
                  else raise Conv.UNCHANGED
                end
                handle Empty => raise Conv.UNCHANGED
              fun primitive_leaf_conversion atom =
                let
                  fun attempt () =
                    case leaf_theory atom of
                      SOME "fcp" => SOME (fcp_conversion atom)
                    | SOME theory =>
                        if List.exists (fn name => theory = name)
                            ["bit", "prim_rec", "arithmetic"] then
                          SOME
                            (simpLib.SIMP_CONV arithmetic_leaf_ss [] atom)
                        else NONE
                    | NONE => NONE
                in
                  attempt ()
                  handle Conv.UNCHANGED => NONE
                       | Feedback.HOL_ERR holerr =>
                           if SmtResource.is_resource_gate holerr then
                             raise Feedback.HOL_ERR holerr
                           else NONE
                end
              val leaf_proofs = ref (Redblackmap.mkDict Term.compare)
              val owners = ref (Redblackmap.mkDict Term.compare)
              val seen = ref (HOLset.empty Term.compare)
              fun collect term =
                if HOLset.member (!seen, term) then ()
                else
                  (seen := HOLset.add (!seen, term);
                   case SmtSkeletonProve.skeleton_children term of
                     SOME children => List.app collect children
                   | NONE =>
                       (case primitive_leaf_conversion term of
                          SOME theorem =>
                            (leaf_proofs := Redblackmap.insert
                               (!leaf_proofs, term, theorem);
                             owners := Redblackmap.insert
                               (!owners, term, "leaf-normalization"))
                        | NONE => ()))
              val _ = collect residue
              fun expand_leaf atom =
                case Redblackmap.peek (!leaf_proofs, atom) of
                  SOME theorem => SmtSkeletonProve.Expanded theorem
                | NONE => SmtSkeletonProve.Unable
              val measure = SmtResource.term_measure residue
              val context = SmtSkeletonProve.new_context
                [{name = "leaf-normalization", expand = expand_leaf}]
              val {theorem = proof, ...} =
                SmtResource.with_bitblast_step_time
                  "cpc-trust-fp-word-circuit"
                  (fn () => SmtSkeletonProve.prove_with_owners
                    context (!owners) measure residue) ()
            in
              Thm.EQ_MP (Thm.SYM normalized) proof
            end) schematic_target
          val substitutions = ListPair.mapEq
            (fn (source, variable) =>
              {redex = variable, residue = source})
            (!sources, variables)
        in Thm.INST substitutions schematic_proof end
        handle HolSatLib.SAT_cex _ =>
          raise ERR "trust" "FP/word bridge residue is not valid"
             | Conv.UNCHANGED =>
          raise ERR "trust" "FP/word bridge made no progress"
      fun replay_fp_word_circuit () =
        let
          fun fp_source term =
            let val {Thy, Tyop, ...} =
              Type.dest_thy_type (Term.type_of term)
            in
              Thy = "smtfloat" andalso Tyop = "smtfp" andalso
              (Term.is_var term orelse boolSyntax.is_select term)
            end
            handle Feedback.HOL_ERR _ => false
          val seen = ref (HOLset.empty Term.compare)
          val sources = ref ([] : Term.term list)
          fun collect term =
            if HOLset.member (!seen, term) then ()
            else
              (seen := HOLset.add (!seen, term);
               if fp_source term then
                 if List.exists (Term.aconv term) (!sources) then ()
                 else sources := term :: !sources
               else List.app collect (SmtResource.term_children term))
          val _ = collect target
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
                    case List.find (fn (source, _) =>
                        Portable.pointer_eq (source, term) orelse
                        Term.aconv source term) source_pairs of
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
          val (left, right) = boolSyntax.dest_eq schematic_target
          val word_type = Term.type_of left
          val first = Term.genvar word_type
          val second = Term.genvar word_type
          val schema_goal = boolSyntax.mk_eq (first, second)
          val schema = SmtWordGraph.normalize schema_goal
          val normalized = Thm.INST
            [{redex = first, residue = left},
             {redex = second, residue = right}] schema
          val _ = Term.aconv (boolSyntax.lhs (Thm.concl normalized))
            schematic_target orelse raise ERR "trust"
              "word equality schema endpoint mismatch"
          val residue = boolSyntax.rhs (Thm.concl normalized)
          fun canonical_fact source =
            let
              val base = Drule.ISPECL [source]
                (Drule.GEN_ALL
                  smtfloatReplayRoundingTheory.smtfp_rep_canonical_fields)
              val formula = Thm.concl base
              val beta = Conv.TOP_DEPTH_CONV Thm.BETA_CONV formula
                handle Conv.UNCHANGED => Thm.REFL formula
            in Thm.EQ_MP beta base end
          val facts = List.map canonical_fact source_variables
          val implication = List.foldr boolSyntax.mk_imp residue
            (List.map Thm.concl facts)
          val circuit_proof =
            prove_boolean_circuit_tautology implication
          val proof = List.foldl
            (fn (fact, theorem) => Thm.MP theorem fact)
            circuit_proof facts
          val schematic = Thm.EQ_MP (Thm.SYM normalized) proof
          val substitutions = ListPair.mapEq
            (fn (source, variable) =>
              {redex = variable, residue = source})
            (!sources, source_variables)
        in Thm.INST substitutions schematic end
        handle HolSatLib.SAT_cex _ =>
          raise ERR "trust" "FP word circuit is not valid"
      fun replay_fp_atom_bridge_uncached () =
            let
              fun trace_start stage =
                if OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" = SOME "1"
                   orelse OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" =
                     SOME "full" then
                  (Feedback.HOL_MESG ("CPC FP bridge: " ^ stage);
                   TextIO.flushOut TextIO.stdOut)
                else ()
              val _ = trace_start "source collection begin"
              fun is_fp_type ty =
                let val {Thy, Tyop, ...} = Type.dest_thy_type ty
                in Thy = "smtfloat" andalso Tyop = "smtfp" end
                handle Feedback.HOL_ERR _ => false
              fun is_rounding_type ty =
                let val {Thy, Tyop, ...} = Type.dest_thy_type ty
                in Thy = "smtfloat" andalso Tyop = "smt_rounding" end
                handle Feedback.HOL_ERR _ => false
              fun source_value term =
                (is_fp_type (Term.type_of term) orelse
                 is_rounding_type (Term.type_of term)) andalso
                (Term.is_var term orelse boolSyntax.is_select term)
              val source_seen = ref (HOLset.empty Term.compare)
              val sources = ref ([] : Term.term list)
              fun collect_sources term =
                if HOLset.member (!source_seen, term) then ()
                else
                  (source_seen := HOLset.add (!source_seen, term);
                   if source_value term then
                     if List.exists (fn saved => Term.aconv saved term)
                         (!sources) then ()
                     else sources := term :: !sources
                   else List.app collect_sources
                     (SmtResource.term_children term))
              val source_roots =
                let
                  val (left, right) = boolSyntax.dest_eq target
                  val roots = List.filter SmtFpGraph.lower_atom_domain
                    [left, right]
                in if List.null roots then [target] else roots end
                handle Feedback.HOL_ERR _ => [target]
              val _ = List.app collect_sources source_roots
              val _ = trace_start "source collection complete"
              (* The bridge is parametric in FP operands.  Schematic
                 sources keep a large Hilbert-choice/Skolem operand opaque
                 while its checked canonical-field law is proved once for
                 a variable and then instantiated by the kernel. *)
              val abstract_large =
                SmtResource.dag_nodes_up_to
                  (max_cached_theorem_dag_nodes + 1) target >
                  max_cached_theorem_dag_nodes orelse
                (let val (left, _) = boolSyntax.dest_eq target
                 in Term.type_of left <> Type.bool end
                 handle Feedback.HOL_ERR _ => false)
              fun trace_bridge stage =
                if abstract_large andalso
                   (OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" = SOME "1"
                    orelse OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" =
                      SOME "full") then
                  (Feedback.HOL_MESG ("CPC FP bridge: " ^ stage);
                   TextIO.flushOut TextIO.stdOut)
                else ()
              val _ = trace_bridge
                ("sources=" ^ Int.toString (List.length (!sources)))
              val source_variables =
                List.map (Term.genvar o Term.type_of) (!sources)
              val source_pairs = ListPair.zip (!sources, source_variables)
              (* The source may be a large choice term occurring inside many
                 circuit nodes.  A shallow, alpha-invariant fingerprint
                 avoids repeatedly alpha-comparing it with unrelated nodes;
                 equal fingerprints are only a prefilter, never a proof of
                 equality. *)
              fun source_hash 0 term =
                    if Term.is_const term then
                      let val {Thy, Name, ...} = Term.dest_thy_const term
                      in (boolean_dag_string_hash Thy * 37 +
                          boolean_dag_string_hash Name) mod
                         boolean_dag_bucket_count end
                    else if Term.is_var term then 3
                    else if Term.is_abs term then 5
                    else 7
                | source_hash depth term =
                    if Term.is_comb term then
                      (source_hash (depth - 1) (Term.rator term) * 41 +
                       source_hash (depth - 1) (Term.rand term) * 67 + 11)
                      mod boolean_dag_bucket_count
                    else if Term.is_abs term then
                      (source_hash (depth - 1) (Term.body term) * 73 + 13)
                      mod boolean_dag_bucket_count
                    else source_hash 0 term
              val source_fingerprints = List.map
                (fn (source, variable) =>
                  (source, variable, source_hash 5 source)) source_pairs
              fun source_replacement term =
                case if abstract_large then
                    let val fingerprint = source_hash 5 term
                    in List.find (fn (source, _, saved) =>
                      Portable.pointer_eq (source, term) orelse
                      (fingerprint = saved andalso
                       Term.aconv source term)) source_fingerprints end
                  else NONE of
                  SOME (_, variable, _) => SOME variable
                | NONE => NONE
              val abstraction_memo = ref
                (Redblackmap.mkDict Term.compare :
                  (Term.term, Term.term) Redblackmap.dict)
              fun abstract_sources term =
                case Redblackmap.peek (!abstraction_memo, term) of
                  SOME result => result
                | NONE =>
                    let
                      val result =
                        case source_replacement term of
                          SOME variable => variable
                        | NONE =>
                            if Term.is_comb term then
                              Term.mk_comb
                                (abstract_sources (Term.rator term),
                                 abstract_sources (Term.rand term))
                            else term
                      val _ = abstraction_memo :=
                        Redblackmap.insert (!abstraction_memo, term, result)
                    in result end
              val schematic_target = abstract_sources target
              val _ = trace_bridge "sources abstracted"
              val schematic_sources =
                if abstract_large then source_variables else !sources
              val arithmetic_leaf_ss = simpLib.++
                (bossLib.srw_ss(), wordsLib.WORD_BIT_EQ_ss)
              fun convert_word_node term =
                (SmtFpGraph.convert_word_projection term
                 handle Conv.UNCHANGED =>
                   let
                     val (head, _) = boolSyntax.strip_comb term
                     val _ = Term.is_const head orelse raise Conv.UNCHANGED
                     val {Thy, Name, ...} = Term.dest_thy_const head
                   in
                     if Thy = "smtfloatReplayWord" andalso
                        Name = "smtfp_cvc_unpacked_exponent" then
                       Conv.REWR_CONV
                         smtfloatReplayWordTheory.smtfp_cvc_unpacked_exponent_def
                         term
                     else if Thy = "smtfloatReplayWord" andalso
                             Name = "smtfp_cvc_unpacked_significand" then
                       Conv.REWR_CONV
                         smtfloatReplayWordTheory.smtfp_cvc_unpacked_significand_def
                         term
                     else if Thy = "words" andalso
                             Name = "word_compare" then
                       Conv.REWR_CONV
                         wordsTheory.word_compare_def term
                     else if Thy = "words" andalso
                             Name = "word_2comp" andalso
                             Term.type_of term =
                               wordsSyntax.mk_word_type
                                 (fcpSyntax.mk_int_numeric_type 1)
                          then
                       Conv.REWR_CONV
                         smtfloatReplayRoundingTheory.word1_neg term
                     else if Thy = "fcp" then
                       let
                         val (_, arguments) = boolSyntax.strip_comb term
                         val indexed = List.hd arguments
                         val (indexed_head, _) =
                           boolSyntax.strip_comb indexed
                         val {Thy = indexed_theory,
                              Name = indexed_name, ...} =
                           Term.dest_thy_const indexed_head
                       in
                         if indexed_theory = "words" andalso
                            indexed_name = "word_compare" then
                           Conv.REWR_CONV
                             smtfloatReplayRoundingTheory.word_compare_index
                             term
                         else if indexed_theory = "words" andalso
                                 indexed_name = "word_add" then
                           (Conv.REWR_CONV
                              smtfloatReplayRoundingTheory.word_add_one_twice_index0
                              term
                            handle Feedback.HOL_ERR _ =>
                              blastLib.BIT_BLAST_CONV term)
                         else if indexed_theory = "words" andalso
                                 List.exists (fn name =>
                                   indexed_name = name)
                                   ["word_and", "word_or", "word_xor",
                                    "word_1comp", "word_2comp"] then
                           blastLib.BIT_BLAST_CONV term
                         else raise Conv.UNCHANGED
                       end
                     else if List.exists (fn name => Thy = name)
                         ["bit", "prim_rec", "arithmetic"] then
                       simpLib.SIMP_CONV arithmetic_leaf_ss [] term
                     else raise Conv.UNCHANGED
                   end)
                handle Empty => raise Conv.UNCHANGED
              (* A single proof-local DAG walk determines whether a subtree
                 changes while building its checked equality.  NONE means
                 reflexivity suffices; only changed branches need MK_COMB.
                 This avoids a separate occurrence scan of large word
                 circuits before lowering their FP atoms. *)
              val fp_memo = Array.array
                (boolean_dag_bucket_count,
                 [] : (Term.term * Thm.thm option) list)
              val fp_lower_nodes = ref 0
              fun fp_memo_index term =
                boolean_dag_term_hash 4 term
              fun fp_memo_peek term =
                case List.find (fn (saved, _) =>
                    Portable.pointer_eq (saved, term))
                    (Array.sub (fp_memo, fp_memo_index term)) of
                  SOME (_, result) => SOME result
                | NONE => NONE
              fun fp_memo_insert term result =
                let val index = fp_memo_index term in
                  Array.update (fp_memo, index,
                    (term, result) :: Array.sub (fp_memo, index))
                end
              fun proof_or_refl term result =
                case result of
                  SOME theorem => theorem
                | NONE => Thm.REFL term
              (* The instantiated equality constant carries the operand
                 type; no traversal of either potentially large operand is
                 needed to inspect it. *)
              fun equality_operand_type term =
                let
                  val equality = Term.rator (Term.rator term)
                  val (operand_type, _) =
                    Type.dom_rng (Term.type_of equality)
                in operand_type end
              fun lower_fp_atoms term =
                case fp_memo_peek term of
                  SOME (SOME theorem) =>
                    SOME (SmtSkeletonProve.anchor_left term theorem)
                | SOME NONE => NONE
                | NONE =>
                    let
                      val _ = fp_lower_nodes := !fp_lower_nodes + 1
                      val _ = if !fp_lower_nodes mod 1000 = 0 then
                          trace_bridge ("FP lowering nodes=" ^
                            Int.toString (!fp_lower_nodes))
                        else ()
                      val atom = SmtFpGraph.lower_atom_domain term
                      val cached = if atom then
                          Redblackmap.peek (!fp_atom_lowerings, term)
                        else NONE
                      val result =
                        case cached of
                          SOME proof => SOME
                            (SmtSkeletonProve.anchor_left term proof)
                        | NONE =>
                            if atom then
                              let
                                val _ = trace_bridge
                                  "FP atom lowering begin"
                                val proof =
                                  SmtFpGraph.convert_atom term
                                val _ = trace_bridge
                                  "FP atom lowering complete"
                              in SOME proof end
                            else if Term.is_comb term then
                              let
                                val operator = Term.rator term
                                val operand = Term.rand term
                                val operator_proof =
                                  lower_fp_atoms operator
                                val operand_proof =
                                  lower_fp_atoms operand
                              in
                                case (operator_proof, operand_proof) of
                                  (NONE, NONE) => NONE
                                | _ => SOME (Thm.MK_COMB
                                    (proof_or_refl operator operator_proof,
                                     proof_or_refl operand operand_proof))
                              end
                            else NONE
                      val _ = fp_memo_insert term result
                      val _ = if atom then
                          (case result of
                             SOME theorem =>
                               fp_atom_lowerings := Redblackmap.insert
                                 (!fp_atom_lowerings, term, theorem)
                           | NONE => ())
                        else ()
                    in result end
              (* A deferred CPC obligation may be a Boolean FP clause as
                 well as an equality.  In the clause case the same checked
                 atom conversion transports the proposition directly. *)
              val equality_target = boolSyntax.is_eq schematic_target
              val (left, right) =
                if equality_target then
                  boolSyntax.dest_eq schematic_target
                else (schematic_target, boolSyntax.T)
              val _ = trace_bridge "FP lowering setup complete"
              val direct_fp_equality =
                equality_target andalso
                equality_operand_type schematic_target <> Type.bool
              val _ = trace_bridge "FP equality type classified"
              val left_conversion =
                if direct_fp_equality then Thm.REFL left
                else proof_or_refl left (lower_fp_atoms left)
              val _ = trace_bridge "left FP atoms lowered"
              val right_conversion =
                if direct_fp_equality then Thm.REFL right
                else proof_or_refl right (lower_fp_atoms right)
              val _ = trace_bridge "right FP atoms lowered"
              val left_residue = boolSyntax.rhs
                (Thm.concl left_conversion)
              val right_residue = boolSyntax.rhs
                (Thm.concl right_conversion)
              fun boolean_children term =
                case SmtSkeletonProve.skeleton_children term of
                  SOME children => SOME children
                | NONE =>
                    let
                      val (head, arguments) = boolSyntax.strip_comb term
                      val {Thy, Name, ...} = Term.dest_thy_const head
                    in
                      if Thy = "bool" andalso
                         List.exists (fn saved => Name = saved)
                           ["/\\", "\\/", "==>", "~"] then
                        SOME arguments
                      else NONE
                    end
                    handle Feedback.HOL_ERR _ => NONE
              fun normalize_words label passes term =
                let
                  fun loop 0 current = current
                    | loop remaining current =
                        let
                          val residue = boolSyntax.rhs (Thm.concl current)
                          val direct = convert_word_node residue
                            handle Conv.UNCHANGED => Thm.REFL residue
                          val direct_residue = boolSyntax.rhs
                            (Thm.concl direct)
                          val generated_skeleton = Option.isSome
                            (boolean_children direct_residue)
                          val graph =
                            if generated_skeleton then Thm.REFL direct_residue
                            else SmtResource.with_bitblast_step_time label
                              (SmtWordGraph.normalize_with_node_conversion
                                convert_word_node) direct_residue
                              handle Conv.UNCHANGED => Thm.REFL direct_residue
                          val next = Thm.TRANS direct graph
                          val next_residue = boolSyntax.rhs (Thm.concl next)
                        in
                          if Term.aconv residue next_residue then current
                          else if generated_skeleton then
                            Thm.TRANS current next
                          else loop (remaining - 1)
                            (Thm.TRANS current next)
                        end
                in loop passes (Thm.REFL term) end
              fun normalize_boolean_atoms term =
                let
                  val memo = ref
                    (Redblackmap.mkDict Term.compare :
                      (Term.term, Thm.thm) Redblackmap.dict)
                  val word_equality_laws = ref
                    ([] : (Type.hol_type * Term.term * Term.term *
                            Thm.thm) list)
                  fun word_equality_schema current =
                    let
                      val (left, right) = boolSyntax.dest_eq current
                      val ty = equality_operand_type current
                      val _ = wordsSyntax.is_word_type ty orelse
                        raise ERR "trust" "not a word equality"
                      val width = Arbnum.toInt
                        (fcpLib.index_to_num
                          (wordsSyntax.dest_word_type ty))
                      val _ = width <= 256 orelse raise ERR "trust"
                        "word equality exceeds decomposition width"
                      val (left_var, right_var, law) =
                        case List.find (fn (saved_type, _, _, _) =>
                            Type.compare (saved_type, ty) = EQUAL)
                            (!word_equality_laws) of
                          SOME (_, saved_left, saved_right, saved_law) =>
                            (saved_left, saved_right, saved_law)
                        | NONE =>
                            let
                              val generic_left = Term.genvar ty
                              val generic_right = Term.genvar ty
                              fun bit word index = wordsSyntax.mk_word_bit
                                (numSyntax.mk_numeral
                                   (Arbnum.fromInt index), word)
                              val bit_equalities = List.tabulate (width,
                                fn index => boolSyntax.mk_eq
                                  (bit generic_left index,
                                   bit generic_right index))
                              fun conjunction [] = boolSyntax.T
                                | conjunction [term] = term
                                | conjunction (term :: rest) =
                                    boolSyntax.mk_conj
                                      (term, conjunction rest)
                              val schema_goal = boolSyntax.mk_eq
                                (boolSyntax.mk_eq
                                   (generic_left, generic_right),
                                 conjunction bit_equalities)
                              val generic_law =
                                wordsLib.WORD_DECIDE schema_goal
                              val _ = word_equality_laws :=
                                (ty, generic_left, generic_right,
                                 generic_law) :: !word_equality_laws
                            in
                              (generic_left, generic_right, generic_law)
                            end
                    in
                      SOME (Thm.INST
                        [{redex = left_var, residue = left},
                         {redex = right_var, residue = right}] law)
                    end
                    handle Feedback.HOL_ERR holerr =>
                      if SmtResource.is_resource_gate holerr then
                        raise Feedback.HOL_ERR holerr
                      else NONE
                  fun walk current =
                    case Redblackmap.peek (!memo, current) of
                      SOME theorem =>
                        SmtSkeletonProve.anchor_left current theorem
                    | NONE =>
                        (case Redblackmap.peek
                            (!fp_boolean_atom_normalizations, current) of
                           SOME theorem =>
                             SmtSkeletonProve.anchor_left current theorem
                         | NONE =>
                        let
                          val theorem =
                            case boolean_children current of
                              SOME _ =>
                                let
                                  val (head, arguments) =
                                    boolSyntax.strip_comb current
                                in List.foldl
                                  (fn (argument, function) =>
                                    Thm.MK_COMB (function, walk argument))
                                  (Thm.REFL head) arguments
                                end
                            | NONE =>
                                if Term.type_of current = Type.bool then
                                  (case word_equality_schema current of
                                     SOME schema =>
                                       let
                                         val residue = boolSyntax.rhs
                                           (Thm.concl schema)
                                       in Thm.TRANS schema (walk residue) end
                                   | NONE =>
                                       let
                                         val base = normalize_words
                                           "cpc-trust-fp-equality-atom" 32
                                           current
                                         val residue = boolSyntax.rhs
                                           (Thm.concl base)
                                       in
                                         case boolean_children residue of
                                           SOME _ => Thm.TRANS base
                                             (walk residue)
                                         | NONE => base
                                       end)
                                else Thm.REFL current
                          val _ = memo := Redblackmap.insert
                            (!memo, current, theorem)
                          val _ = fp_boolean_atom_normalizations :=
                            Redblackmap.insert
                              (!fp_boolean_atom_normalizations,
                               current, theorem)
                        in theorem end)
                in walk term end
              val left_word =
                if direct_fp_equality then Thm.REFL left_residue
                else if abstract_large then
                  normalize_boolean_atoms left_residue
                else normalize_words
                  "cpc-trust-fp-atom-normalize-left" 1 left_residue
              val _ = trace_bridge "left word atoms normalized"
              val right_word =
                if not equality_target orelse direct_fp_equality then
                  Thm.REFL right_residue
                else if abstract_large then
                  normalize_boolean_atoms right_residue
                else normalize_words
                  "cpc-trust-fp-atom-normalize-right" 32 right_residue
              val _ = trace_bridge "right word atoms normalized"
              val left_theorem = Thm.TRANS left_conversion left_word
              val right_theorem = Thm.TRANS right_conversion right_word
              val normalized =
                if direct_fp_equality then
                  let
                    val atom = SmtFpGraph.convert_atom schematic_target
                    val atom_residue = boolSyntax.rhs (Thm.concl atom)
                    val word = normalize_boolean_atoms atom_residue
                  in Thm.TRANS atom word end
                else if equality_target then
                  let
                    val equality =
                      Term.rator (Term.rator schematic_target)
                  in Thm.MK_COMB
                    (Thm.MK_COMB (Thm.REFL equality, left_theorem),
                     right_theorem) end
                else left_theorem
              val residue = boolSyntax.rhs (Thm.concl normalized)
              val _ = trace_bridge "FP bridge normalized"
              fun canonical_fact source =
                case if Term.is_var source then
                    Redblackmap.peek
                      (!fp_canonical_fact_laws, Term.type_of source)
                  else NONE of
                  SOME (generic_source, theorem) =>
                    Thm.INST
                      [{redex = generic_source, residue = source}] theorem
                | NONE => let
                  val base = Drule.ISPECL [source]
                    (Drule.GEN_ALL
                      smtfloatReplayRoundingTheory.smtfp_rep_canonical_fields)
                  val formula = Thm.concl base
                  val beta = Conv.TOP_DEPTH_CONV Thm.BETA_CONV formula
                    handle Conv.UNCHANGED => Thm.REFL formula
                  val beta_residue = boolSyntax.rhs (Thm.concl beta)
                  val lowered = proof_or_refl beta_residue
                    (lower_fp_atoms beta_residue)
                  val lowered_residue = boolSyntax.rhs (Thm.concl lowered)
                  val word = normalize_boolean_atoms lowered_residue
                  val theorem = Thm.EQ_MP word
                    (Thm.EQ_MP lowered (Thm.EQ_MP beta base))
                  val _ =
                    if Term.is_var source then
                      fp_canonical_fact_laws := Redblackmap.insert
                        (!fp_canonical_fact_laws, Term.type_of source,
                         (source, theorem))
                    else ()
                in theorem end
              fun rounding_fact source =
                Drule.SPECL [source] rounding_partition_law
              val canonical_facts = List.map
                (fn source =>
                  if is_rounding_type (Term.type_of source) then
                    rounding_fact source
                  else canonical_fact source) schematic_sources
              val _ = trace_bridge "canonical facts proved"
              fun prove_from assumptions proofs =
                let
                  val implication = List.foldr boolSyntax.mk_imp
                    residue assumptions
                  val theorem = prove_boolean_circuit_tautology implication
                in List.foldl
                  (fn (proof, result) => Thm.MP result proof)
                  theorem proofs
                end
              val proof = prove_from
                (List.map Thm.concl canonical_facts) canonical_facts
              val _ = trace_bridge "Boolean circuit proved"
              val schematic = Thm.EQ_MP (Thm.SYM normalized) proof
              val substitutions = ListPair.mapEq
                (fn (source, variable) =>
                  {redex = variable, residue = source})
                (!sources, source_variables)
            in Thm.INST substitutions schematic end
        handle HolSatLib.SAT_cex _ => raise ERR "trust"
          "normalized FP atom bridge is not valid"
             | HolSatLib.SAT_satisfiable _ => raise ERR "trust"
          "normalized FP atom bridge is not valid"
      fun replay_fp_atom_bridge () =
        let
          (* Matching a concrete cached bridge against a large FP circuit
             may traverse its unfolded tree.  This bounded rigid-skeleton
             check only rejects impossible matches; variables remain
             wildcards and every survivor still goes through match_term. *)
          fun compatible 0 _ _ = true
            | compatible depth pattern actual =
                if Term.is_var pattern then true
                else if Term.is_const pattern then
                  Term.is_const actual andalso
                  let
                    val left = Term.dest_thy_const pattern
                    val right = Term.dest_thy_const actual
                  in #Thy left = #Thy right andalso
                     #Name left = #Name right end
                else if Term.is_comb pattern then
                  Term.is_comb actual andalso
                  compatible (depth - 1)
                    (Term.rator pattern) (Term.rator actual) andalso
                  compatible (depth - 1)
                    (Term.rand pattern) (Term.rand actual)
                else if Term.is_abs pattern then
                  Term.is_abs actual andalso
                  compatible (depth - 1)
                    (Term.body pattern) (Term.body actual)
                else false
          val trace =
            OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" = SOME "1" orelse
            OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" = SOME "full"
          fun report message =
            if trace then
              (Feedback.HOL_MESG ("CPC FP bridge: " ^ message);
               TextIO.flushOut TextIO.stdOut)
            else ()
          fun instantiate theorem =
            SmtResource.with_resource_step_time "Skeleton"
              "cpc-fp-bridge-cache-match"
              (fn theorem =>
                let
                  val proof = Drule.INST_TY_TERM
                    (Term.match_term (Thm.concl theorem) target) theorem
                in
                  if Term.aconv (Thm.concl proof) target then SOME proof
                  else NONE
                end) theorem
            handle Feedback.HOL_ERR _ => NONE
          fun cached [] = NONE
            | cached (theorem :: rest) =
                (case instantiate theorem of
                   SOME proof => SOME proof
                 | NONE => cached rest)
          val candidates = List.filter
            (fn theorem => compatible 8 (Thm.concl theorem) target)
            (!fp_atom_bridge_laws)
          val _ = report ("cache candidates=" ^
            Int.toString (List.length candidates) ^ "/" ^
            Int.toString (List.length (!fp_atom_bridge_laws)))
        in
          case cached candidates of
            SOME proof => (report "cache hit"; proof)
          | NONE =>
              let
                val _ = report "cache miss; reconstructing bridge"
                val proof = replay_fp_atom_bridge_uncached ()
                val symmetric =
                  if boolSyntax.is_eq (Thm.concl proof) then
                    [Thm.SYM proof]
                  else []
                val _ = fp_atom_bridge_laws :=
                  proof :: (symmetric @ !fp_atom_bridge_laws)
              in proof end
        end
      fun replay_fp_contextual () =
        let
          val context = SmtSkeletonDispatch.new_context arith_prove
          fun without_hypotheses () =
            #theorem (SmtSkeletonDispatch.prove context target)
          fun with_hypotheses () =
            let
              val hypotheses = context_terms ()
              val implication =
                List.foldr boolSyntax.mk_imp target hypotheses
              val {theorem, ...} =
                SmtSkeletonDispatch.prove context implication
            in
              List.foldl
                (fn (hypothesis, result) =>
                  Thm.MP result (Thm.ASSUME hypothesis))
                theorem hypotheses
            end
          val theorem = without_hypotheses ()
            handle Feedback.HOL_ERR _ => with_hypotheses ()
        in
          discharge_prems theorem
        end
      (* A CPC TRUST step is never accepted as a theorem.  Retain its exact
         proposition only as a deferred hypothesis; [check_proof_impl]
         removes it solely when another checked certificate step proves the
         same proposition independently. *)
      fun deferred_fp_trust () =
        let
          (* Deferral is only for the first certificate pass.  During
             closure the caller requires an independent checked proof;
             recreating ASSUME here cannot discharge the obligation and
             can traverse an enormous instantiated witness unnecessarily. *)
          val _ = force_fp andalso raise ERR "trust"
            "forced FP checking could not prove the deferred obligation"
          val seen = ref ([] : Term.term list)
          val variables = ref ([] : Term.term list)
          fun visited term =
            List.exists (fn saved => Portable.pointer_eq (saved, term))
              (!seen)
          fun visit term =
            if visited term then ()
            else
              (seen := term :: !seen;
               if Term.is_var term then
                 if List.exists (fn variable => Term.aconv variable term)
                     (!variables) then ()
                 else variables := term :: !variables
               else List.app visit (SmtResource.term_children term))
          val target_dag = SmtResource.dag_nodes_up_to 257 target
          val _ = if target_dag <= 256 then visit target else ()
          val variables = List.rev (!variables)
          fun private_marker variable =
            let val (name, _) = Term.dest_var variable in
              String.isPrefix "@fp." name
            end handle Feedback.HOL_ERR _ => false
        in
          if target_dag > 256 orelse List.null variables orelse
             List.exists private_marker variables then
            Thm.ASSUME target
          else
            let val closed =
              boolSyntax.list_mk_forall (variables, target)
            in Drule.SPECL variables (Thm.ASSUME closed) end
        end
      fun next prover continuation =
        prover ()
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else continuation ()
      fun next_fp prover continuation =
        prover () handle SmtFpGraph.Declined _ => continuation ()
          | Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            (continuation ()
             handle Feedback.HOL_ERR fallback_error =>
               if SmtResource.is_resource_gate fallback_error then
                 raise Feedback.HOL_ERR fallback_error
               else raise Feedback.HOL_ERR holerr)
          else continuation ()
      fun replay_seq () =
        let
          val context =
            HOLset.listItems (#asserted_hyps state) @ #scope_hyps state @
            List.map Thm.concl prems
          val thm =
            SmtSeqProve.seq_prove target
            handle Feedback.HOL_ERR holerr =>
              if SmtResource.is_resource_gate holerr then
                raise Feedback.HOL_ERR holerr
              else
                SmtSeqProve.seq_contextual_prove context target
        in
          List.foldl (fn (premise, proved) => Drule.PROVE_HYP premise proved)
            thm prems
        end
      fun string_context () =
        List.exists SmtStringProve.has_string_theory_term
          (target :: context_terms ())
      fun replay_string () =
        let
          val context =
            HOLset.listItems (#asserted_hyps state) @ #scope_hyps state @
            List.map Thm.concl prems
          val thm =
            SmtStringProve.string_rewrite_prove target
            handle Feedback.HOL_ERR _ =>
              SmtStringProve.string_prove arith_prove target
            handle Feedback.HOL_ERR _ =>
              SmtStringProve.string_contextual_prove context target
        in
          List.foldl (fn (premise, proved) => Drule.PROVE_HYP premise proved)
            thm prems
        end
      fun set_context () =
        List.exists SmtArrayProve.has_set_term (target :: context_terms ())
      fun bag_context () =
        List.exists SmtBagProve.has_native_bag_encoding
          (target :: context_terms ())
      fun fp_term_dag root =
        Lib.can (HolKernel.find_term (fn term =>
          Term.is_const term andalso
          let val {Thy, ...} = Term.dest_thy_const term
          in Thy = "smtfloat" orelse Thy = "binary_ieee" end)) root
      fun fp_context () =
        List.exists fp_term_dag (target :: context_terms ())
      fun has_private_fp_marker root =
        let
          val seen = ref (HOLset.empty Term.compare)
          fun visit term =
            if HOLset.member (!seen, term) then false
            else
              let
                val _ = seen := HOLset.add (!seen, term)
              in
                if Term.is_var term then
                  String.isPrefix "@fp." (#1 (Term.dest_var term))
                else List.exists visit (SmtResource.term_children term)
              end
        in visit root end
      fun replay_boolean_case_rewrite () =
        let
          val (left, right) = boolSyntax.dest_eq target
          val _ = Term.type_of left = Type.bool andalso
                  Term.type_of right = Type.bool orelse
            raise ERR "trust" "not a Boolean equality"
          fun condition_matches pivot encoding =
            let
              val (first, second) = boolSyntax.dest_eq encoding
              fun conditional term =
                let val (condition, _, _) = boolSyntax.dest_cond term
                in Term.aconv condition pivot end
                handle Feedback.HOL_ERR _ => false
            in conditional first orelse conditional second end
            handle Feedback.HOL_ERR _ => false
          fun prove pivot encoding =
            let
              val _ = condition_matches pivot encoding orelse
                raise ERR "trust"
                  "Boolean equality is not a direct conditional encoding"
              val trace =
                (OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" = SOME "1" orelse
                 OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" = SOME "full")
                andalso SmtResource.dag_nodes_up_to 257 target > 256
              fun report stage =
                if trace then
                  (Feedback.HOL_MESG
                    ("CPC Boolean case bridge: " ^ stage);
                   TextIO.flushOut TextIO.stdOut)
                else ()
              fun case_proof condition goal =
                Tactical.TAC_PROOF (([], goal),
                  Tactical.THEN (Tactic.BOOL_CASES_TAC condition,
                    bossLib.ASM_SIMP_TAC (bossLib.srw_ss()) []))
              fun schematic () =
                let
                  val variable = Term.genvar Type.bool
                  val goal = Term.subst
                    [{redex = pivot, residue = variable}] target
                  val _ = report "schematic goal ready"
                  val theorem = case_proof variable goal
                in Thm.INST
                  [{redex = variable, residue = pivot}] theorem end
              val _ = report "schematic attempt"
            in
              (SmtResource.with_resource_step_time "Skeleton"
                "cpc-trust-boolean-case-schema" schematic ()
               handle Feedback.HOL_ERR _ =>
                 (report "bounded concrete fallback";
                  SmtResource.with_resource_step_time "BitVector"
                    "cpc-trust-boolean-case-concrete"
                    (fn () => case_proof pivot target) ()))
            end
        in
          prove left right handle Feedback.HOL_ERR _ => prove right left
        end
      fun replay_fp_eq_components () =
        let
          val (variables, body) =
            if boolSyntax.is_forall target then
              boolSyntax.strip_forall target
            else ([], target)
          val (left, _) = boolSyntax.dest_eq body
          val (head, arguments) = boolSyntax.strip_comb left
          val {Thy, Name, ...} = Term.dest_thy_const head
          val _ = Thy = "smtfloat" andalso Name = "smtfp_eq" orelse
            raise ERR "trust" "not an smtfp_eq component rewrite"
          val theorem = Drule.ISPECL arguments smtfp_eq_components_law
          val _ = Term.aconv (Thm.concl theorem) body orelse
            raise ERR "trust" "smtfp_eq component endpoint mismatch"
        in List.foldr
          (fn (variable, result) => Thm.GEN variable result)
          theorem variables
        end
      fun fp_atom_rewrite_target () =
        let
          val body =
            if boolSyntax.is_forall target then
              #2 (boolSyntax.strip_forall target)
            else target
          val (left, right) = boolSyntax.dest_eq body
        in
          if SmtFpGraph.lower_atom_domain left then true
          else if SmtFpGraph.lower_atom_domain right then true
          else Term.type_of left <> Type.bool andalso
            SmtFpGraph.lower_atom_domain body
        end
        handle Feedback.HOL_ERR _ => false
      fun direct_fp_equality_target () =
        let
          val (left, right) = boolSyntax.dest_eq target
          val (left_head, _) = boolSyntax.strip_comb left
          val (right_head, _) = boolSyntax.strip_comb right
          fun fp_head head =
            let val {Thy, ...} = Term.dest_thy_const head
            in Thy = "smtfloat" orelse Thy = "binary_ieee" end
            handle Feedback.HOL_ERR _ => false
        in
          Term.type_of left <> Type.bool andalso
          Term.type_of left = Term.type_of right andalso
          (fp_head left_head orelse fp_head right_head) andalso
          SmtFpGraph.lower_atom_domain target
        end
        handle Feedback.HOL_ERR _ => false
      fun fp_word_bridge_target () =
        let
          val (left, _) = boolSyntax.dest_eq target
          fun fp_head term =
            let
              val (head, _) = boolSyntax.strip_comb term
              val {Thy, ...} = Term.dest_thy_const head
            in Thy = "smtfloat" orelse Thy = "binary_ieee" end
            handle Feedback.HOL_ERR _ => false
          fun fp_value_equality term =
            boolSyntax.is_eq term andalso
            let val (first, second) = boolSyntax.dest_eq term in
              Term.type_of first <> Type.bool andalso
              Term.type_of first = Term.type_of second andalso
              (fp_head first orelse fp_head second)
            end
        in Term.type_of left = Type.bool andalso fp_value_equality left end
        handle Feedback.HOL_ERR _ => false
      fun word_equality_target () =
        let val (left, right) = boolSyntax.dest_eq target
        in
          wordsSyntax.is_word_type (Term.type_of left) andalso
          Term.type_of left = Term.type_of right
        end
        handle Feedback.HOL_ERR _ => false
    in
      (* Native Seq, Set, and Bag trusts have no unchecked fallback.  Bag's
         second rung is the checked contextual simplifier used by its shared
         D2 prover; failure records a theory-specific CPC obligation. *)
      if not force_fp andalso has_private_fp_marker target then
        profile "CPC(rung:trust/fp_deferred)" deferred_fp_trust ()
      else if force_fp andalso word_equality_target () then
        next_fp
          (fn () => profile "CPC(rung:trust/fp-word-circuit)"
            replay_fp_word_circuit ())
          (fn () => profile "CPC(rung:trust/fp_deferred)"
            deferred_fp_trust ())
      else if force_fp orelse fp_term_dag target then
        if direct_fp_equality_target () then
          next_fp
            (fn () => profile "CPC(rung:trust/fp)" replay_fp ())
            (fn () => next_fp
              (fn () => profile "CPC(rung:trust/fp-atom-bridge)"
                replay_fp_atom_bridge ())
              (fn () => profile "CPC(rung:trust/fp_deferred)"
                deferred_fp_trust ()))
        else if fp_word_bridge_target () then
          if force_fp then
            next_fp
              (fn () => profile "CPC(rung:trust/fp-atom-bridge)"
                replay_fp_atom_bridge ())
              (fn () => profile "CPC(rung:trust/fp_deferred)"
                deferred_fp_trust ())
          else profile "CPC(rung:trust/fp_deferred)" deferred_fp_trust ()
        else if fp_atom_rewrite_target () then
          if not force_fp andalso
             (has_private_fp_marker target orelse
              SmtResource.dag_nodes_up_to 2001 target > 2000) then
            profile "CPC(rung:trust/fp_deferred)" deferred_fp_trust ()
          else
            next_fp
              (fn () => profile "CPC(rung:trust/boolean-case-rewrite)"
                replay_boolean_case_rewrite ())
              (fn () => next_fp
                (fn () => profile "CPC(rung:trust/fp-eq-components)"
                  replay_fp_eq_components ())
                (fn () =>
                  let
                    fun native () = profile "CPC(rung:trust/fp)"
                      replay_fp ()
                    fun bridge () =
                      profile "CPC(rung:trust/fp-atom-bridge)"
                        replay_fp_atom_bridge ()
                    fun defer () =
                      profile "CPC(rung:trust/fp_deferred)"
                        deferred_fp_trust ()
                    val large = SmtResource.dag_nodes_up_to
                      (max_cached_theorem_dag_nodes + 1) target >
                      max_cached_theorem_dag_nodes
                  in
                    (* A large FP operand is schematic in the checked atom
                       bridge.  Try that bounded route before asking the
                       native prover to expand its full bit circuit. *)
                    if large then next_fp bridge
                      (fn () => next_fp native defer)
                    else next_fp native
                      (fn () => next_fp bridge defer)
                  end))
        else if SmtResource.dag_nodes_up_to 257 target > 256 then
          if force_fp then
            next_fp
              (fn () => profile "CPC(rung:trust/fp-atom-bridge)"
                replay_fp_atom_bridge ())
              (fn () => profile "CPC(rung:trust/fp_deferred)"
                deferred_fp_trust ())
          else profile "CPC(rung:trust/fp_deferred)" deferred_fp_trust ()
        else
          next_fp
            (fn () => profile "CPC(rung:trust/fp-word-bridge)"
              replay_fp_word_bridge ())
            (fn () => next_fp
              (fn () => profile "CPC(rung:trust/fp_contextual)"
                replay_fp_contextual ())
              (fn () => next_fp
                (fn () => profile "CPC(rung:trust/fp)" replay_fp ())
                (fn () => profile "CPC(rung:trust/fp_deferred)"
                  deferred_fp_trust ())))
      else if SmtSeqProve.has_seq_type target then
        profile "CPC(rung:trust/seq)" replay_seq ()
      else if string_context () then
        profile "CPC(rung:trust/string)" replay_string ()
      else if bag_context () then
        next (fn () => profile "CPC(rung:trust/bag)" replay_bag ())
          (fn () => profile "CPC(rung:trust/bag_context)"
            prove_scoped_bag ())
      else if set_context () then
        next (fn () => profile "CPC(rung:trust/set)" replay_set ())
          unsupported_set
      else if fp_context () then
        profile "CPC(rung:trust/fp_deferred)" deferred_fp_trust ()
      else
        next (fn () => profile "CPC(rung:trust/scoped_arithmetic)"
          prove_scoped_arithmetic ())
          (fn () => profile "CPC(rung:trust/rdiv)" replay_rdiv ())
    end

  fun replay_ite_eq args =
    let
      val ite_tm = expect_one_arg "ite_eq" args
      val (condition, then_tm, else_tm) = boolSyntax.dest_cond ite_tm
      val target = boolSyntax.mk_cond
        (condition, boolSyntax.mk_eq (ite_tm, then_tm),
         boolSyntax.mk_eq (ite_tm, else_tm))
    in
      Tactical.TAC_PROOF (([], target),
        Tactical.THEN (Tactic.COND_CASES_TAC,
          bossLib.ASM_SIMP_TAC boolSimps.bool_ss []))
    end

  fun replay_ite_elim1 prems =
    let
      val premise = expect_one_premise "ite_elim1" prems
    in
      if Term.aconv (Thm.concl premise) boolSyntax.T then premise
      else
        let
          val (condition, then_tm, _) =
            boolSyntax.dest_cond (Thm.concl premise)
            handle Feedback.HOL_ERR _ => raise ERR "ite_elim1"
              ("premise is not a conditional: " ^
               Library.term_to_string (Thm.concl premise))
        in tautological_consequence premise
          (mk_disj_terms [boolSyntax.mk_neg condition, then_tm]) end
    end

  fun replay_ite_elim2 prems =
    let
      val premise = expect_one_premise "ite_elim2" prems
    in
      if Term.aconv (Thm.concl premise) boolSyntax.T then premise
      else
        let
          val (condition, _, else_tm) =
            boolSyntax.dest_cond (Thm.concl premise)
            handle Feedback.HOL_ERR _ => raise ERR "ite_elim2"
              ("premise is not a conditional: " ^
               Library.term_to_string (Thm.concl premise))
        in tautological_consequence premise
          (mk_disj_terms [condition, else_tm]) end
    end

  fun replay_scope state prems =
    let
      val premise = expect_one_premise "scope" prems
      (* Canonical replay can retain [T] as support when a syntactically
         nontrivial equality reduces to truth inside a TRANS or resolution
         chain.  It is not a CPC scope assumption: discharge it with the
         kernel theorem [|- T] before auditing the hypotheses that survive
         the pop. *)
      val premise =
        if HOLset.member (Thm.hypset premise, boolSyntax.T) then
          Drule.PROVE_HYP boolTheory.TRUTH premise
        else premise
      val (hyp, state) = pop_scope_hyp state
      val thm = Thm.DISCH hyp premise
      val allowed = HOLset.addList (#asserted_hyps state, #scope_hyps state)
      val _ = HOLset.isSubset (Thm.hypset thm, allowed) orelse
        raise ERR "scope"
          ("CPC scope pop did not close all of its local assumptions; " ^
           "popped=" ^ Library.term_to_string hyp ^ "; residual=" ^
           String.concatWith ", " (List.map Library.term_to_string
             (HOLset.listItems (HOLset.difference (Thm.hypset thm, allowed)))))
    in
      (state, thm)
    end

  fun replay_process_scope strong_canon args prems =
    let
      val process_scope_timer = Timer.startRealTimer ()
      fun process_scope_mark phase =
        if OS.Process.getEnv "HOL4_CPC_REPLAY_SHAPE" = SOME "1" then
          Feedback.HOL_MESG
            ("CPCPROCESSSCOPE phase=" ^ phase ^ " time=" ^
             Time.toString (Timer.checkRealTimer process_scope_timer))
        else ()
      val premise = expect_one_premise "process_scope" prems
      (* The CPC printer records the original body conclusion as its sole
         argument.  Stop uncurrying at that exact term: the body itself may
         be an implication, which is not an additional scoped assumption. *)
      val scope_result = case args of [tm] => tm
        | _ => raise ERR "process_scope" "expected one CPC :args term"
      fun dest_scope tm acc =
        if shared_aconv tm scope_result then (List.rev acc, NONE)
        else if boolSyntax.is_imp_only tm andalso
                not (boolSyntax.is_imp_only scope_result) then
          let val (antecedent, consequent) = boolSyntax.dest_imp tm
          in dest_scope consequent (antecedent :: acc) end
        else if shared_aconv
          (canonical_term tm) (canonical_term scope_result)
        then (List.rev acc, SOME tm)
        else if boolSyntax.is_imp_only tm then
          let val (antecedent, consequent) = boolSyntax.dest_imp tm
          in dest_scope consequent (antecedent :: acc) end
        else (List.rev acc, SOME tm)
      fun mk_conj [tm] = tm
        | mk_conj (tm :: rest) = boolSyntax.mk_conj (tm, mk_conj rest)
        | mk_conj [] = raise ERR "process_scope" "empty scope implication"
      val (antecedents, normalized_result) =
        dest_scope (Thm.concl premise) []
      val _ = process_scope_mark "dest"
      val conjunction = mk_conj antecedents
      val target = if Term.aconv scope_result boolSyntax.F then
        boolSyntax.mk_neg conjunction
      else boolSyntax.mk_imp (conjunction, scope_result)
      val conjunction_thm = Thm.ASSUME conjunction
      fun conjunct_theorems expected theorem =
        case expected of
          [] => raise ERR "process_scope" "empty conjunction proof"
        | [_] => [theorem]
        | _ :: rest =>
            Thm.CONJUNCT1 theorem ::
            conjunct_theorems rest (Thm.CONJUNCT2 theorem)
      val antecedent_theorems =
        conjunct_theorems antecedents conjunction_thm
      val applied = List.foldl
        (fn (antecedent, implication) => Thm.MP implication antecedent)
        premise antecedent_theorems
      val _ = process_scope_mark "apply"
      val normalized = case normalized_result of
          NONE => applied
        | SOME tm =>
            let
              fun bridge canon =
                let
                  val tm_norm = canon tm
                  val result_norm = canon scope_result
                in Thm.TRANS tm_norm (Thm.SYM result_norm) end
              fun arithmetic_bridge () =
                let
                  val tm_norm = SmtReplayCanon.cpc_canon_conv tm
                  val result_norm =
                    SmtReplayCanon.cpc_canon_conv scope_result
                  val normalized_tm = boolSyntax.rhs (Thm.concl tm_norm)
                  val normalized_result =
                    boolSyntax.rhs (Thm.concl result_norm)
                  val middle = arith_prove
                    (boolSyntax.mk_eq (normalized_tm, normalized_result))
                in
                  Thm.TRANS tm_norm
                    (Thm.TRANS middle (Thm.SYM result_norm))
                end
              val bridge =
                bridge SmtReplayCanon.cpc_canon_conv
                handle Feedback.HOL_ERR _ =>
                  (arithmetic_bridge ()
                   handle Feedback.HOL_ERR _ =>
                     (bridge strong_canon
                      handle Feedback.HOL_ERR holerr =>
                        raise ERR "process_scope"
                          ("scope result canonicalization failed; local=" ^
                           Library.term_to_string tm ^ "; expected=" ^
                           Library.term_to_string scope_result ^ "; " ^
                           Feedback.message_of holerr)))
            in Thm.EQ_MP bridge applied end
      val _ = process_scope_mark "normalize"
      val discharged = Thm.DISCH conjunction normalized
      val result =
        if Term.aconv scope_result boolSyntax.F then Thm.NOT_INTRO discharged
        else discharged
    in
      if Term.aconv (Thm.concl result) target then result
      else raise ERR "process_scope" "direct scope normalization shape mismatch"
    end

  fun replay_not_and prems =
    let
      val premise = expect_one_premise "not_and" prems
      val conjunction =
        (boolSyntax.dest_neg (Thm.concl premise)
         handle Feedback.HOL_ERR _ =>
           let
             val (antecedent, consequent) =
               boolSyntax.dest_imp (Thm.concl premise)
             val _ = Term.aconv consequent boolSyntax.F orelse
               raise ERR "not_and" "implication consequent is not false"
           in antecedent end)
        handle Feedback.HOL_ERR _ => raise ERR "not_and"
          ("premise is neither a negation nor an implication to false: " ^
           Library.term_to_string (Thm.concl premise))
      val target = mk_disj_terms
        (List.map boolSyntax.mk_neg (boolSyntax.strip_conj conjunction))
    in tautological_consequence premise target end

  fun replay_not_or_elim args prems =
    let
      val premise = expect_one_premise "not_or_elim" prems
      val index_term = expect_one_arg "not_or_elim" args
      val index = Arbnum.toInt
        (numSyntax.dest_numeral index_term
         handle Feedback.HOL_ERR _ =>
           numSyntax.dest_numeral (intSyntax.dest_injected index_term))
      val disjunction = boolSyntax.dest_neg (Thm.concl premise)
      val selected = List.nth (boolSyntax.strip_disj disjunction, index)
        handle Subscript => raise ERR "not_or_elim"
          "CPC disjunction index is outside the premise"
    in
      tautological_consequence premise (boolSyntax.mk_neg selected)
    end

  fun replay_not_not_elim prems =
    let
      val premise = expect_one_premise "not_not_elim" prems
      val result = boolSyntax.dest_neg (boolSyntax.dest_neg (Thm.concl premise))
    in
      tautological_consequence premise result
    end

  fun replay_and_intro (premise_steps : replayed_step list) =
    let
      val prems = List.map
        step_theorem premise_steps
      fun construct theorems =
        case theorems of
          [] => raise ERR "and_intro" "expected CPC premises"
        | [premise] => premise
        | premise :: rest => Thm.CONJ premise (construct rest)
    in
      case premise_steps of
        [] => raise ERR "and_intro" "expected CPC premises"
      | [premise] => (step_theorem premise, step_provenance premise)
      | _ => (construct prems,
          ConjunctionProvenance (AndIntroConjunction,
            List.map step_provenance premise_steps))
    end

  (* Unlike ordinary replay handlers, SKOLEMIZE has a source-syntax
     contract which a theorem with the same declared conclusion cannot
     establish.  This complete check is therefore run before the generic
     theorem-cache probe. *)
  fun skolemize_preflight conclusion located_args premise_steps =
    let
      val _ = if List.null located_args then ()
        else raise ERR "skolemize"
          "skolemize expects no explicit CPC :args terms"
      val premise_step =
        case premise_steps of
          [premise_step] => premise_step
        | _ => raise ERR "skolemize" "expected exactly one CPC premise"
      val (immediate_count, body_provenance) =
        case step_provenance premise_step of
          ApplicationProvenance
              ("not", [BinderBlockProvenance
                ("forall", size, body)]) => (size, body)
        | AmbiguousProvenance reason => raise ERR "skolemize"
            ("premise binder-block provenance is ambiguous: " ^ reason)
        | UnavailableProvenance reason => raise ERR "skolemize"
            ("premise binder-block provenance is unavailable: " ^ reason)
        | provenance => raise ERR "skolemize"
            ("premise lacks exact negated FORALL binder-block provenance: " ^
             provenance_shape provenance)
      val _ = if immediate_count > 0 then ()
        else raise ERR "skolemize"
          "expected an unambiguous positive immediate FORALL binder count"
      (* The shared builder checks that the recorded immediate boundary fits
         the semantic ~FORALL theorem and consumes exactly that boundary. *)
      val {theorem, witnesses} = CPC_Proof.cpc_skolem_witnesses
        immediate_count (step_theorem premise_step)
      val _ = if List.length witnesses = immediate_count then ()
        else raise ERR "skolemize"
          "shared witness builder crossed the immediate FORALL boundary"
      val _ =
        case conclusion of
          NONE => ()
        | SOME target => if Term.aconv (Thm.concl theorem) target then ()
            else raise ERR "skolemize"
              ("declared conclusion differs from the shared witness " ^
               "builder boundary result")
      (* SELECT substitutes choice terms for the consumed source variables.
         Preserve every unaffected source constructor and binder boundary,
         but mark atomic leaves unavailable because provenance does not label
         which atoms were substituted.  In particular, a nested source
         forall remains available as the immediate block of a later premise. *)
      fun substituted provenance =
        case provenance of
          AtomicProvenance => UnavailableProvenance
            "atomic occurrence may contain a skolem choice substitution"
        | ApplicationProvenance (head, operands) =>
            ApplicationProvenance (head, List.map substituted operands)
        | BinderProvenance (head, body) =>
            BinderProvenance (head, substituted body)
        | BinderBlockProvenance (head, size, body) =>
            BinderBlockProvenance (head, size, substituted body)
        | EqualityProvenance (left, right) =>
            EqualityProvenance (substituted left, substituted right)
        | ConjunctionProvenance (source, operands) =>
            ConjunctionProvenance (source, List.map substituted operands)
        | UnavailableProvenance reason => UnavailableProvenance reason
        | AmbiguousProvenance reason => AmbiguousProvenance reason
      val provenance = ApplicationProvenance
        ("not", [substituted body_provenance])
    in
      exact_result provenance theorem
    end

  fun replay_arith_mult_neg args =
    case args of
      [coefficient, equality] =>
        let
          datatype relation = Eq | Lt | Le | Gt | Ge
          val (relation, left, right) =
            (let val (left, right) = boolSyntax.dest_eq equality
             in (Eq, left, right) end
             handle Feedback.HOL_ERR _ =>
            let val (left, right) = arith_dest_less equality
             in (Lt, left, right) end
             handle Feedback.HOL_ERR _ =>
            let val (left, right) = arith_dest_leq equality
             in (Le, left, right) end
             handle Feedback.HOL_ERR _ =>
            let val (left, right) = arith_dest_greater equality
             in (Gt, left, right) end
             handle Feedback.HOL_ERR _ =>
            let val (left, right) = arith_dest_geq equality
             in (Ge, left, right) end
             handle Feedback.HOL_ERR _ =>
            raise ERR "arith_mult_neg"
              "expected relation (=, <, <=, >, or >=)")
          val product_left = arith_mult (coefficient, left)
          val product_right = arith_mult (coefficient, right)
          val result =
            case relation of
              Eq => boolSyntax.mk_eq (product_left, product_right)
            | Lt => arith_greater (product_left, product_right)
            | Le => arith_geq (product_left, product_right)
            | Gt => arith_less (product_left, product_right)
            | Ge => arith_leq (product_left, product_right)
          val target = boolSyntax.mk_imp
            (boolSyntax.mk_conj
             (arith_less (coefficient, arith_zero coefficient), equality),
             result)
        in arith_prove target end
    | _ => raise ERR "arith_mult_neg"
      "expected a coefficient and an arithmetic relation"

  fun replay_arith_mult_pos args =
    case args of
      [coefficient, equality] =>
        let
          datatype relation = Eq | Lt | Le | Gt | Ge
          val (relation, left, right) =
            (let val (left, right) = boolSyntax.dest_eq equality
             in (Eq, left, right) end
             handle Feedback.HOL_ERR _ =>
            let val (left, right) = arith_dest_less equality
             in (Lt, left, right) end
             handle Feedback.HOL_ERR _ =>
            let val (left, right) = arith_dest_leq equality
             in (Le, left, right) end
             handle Feedback.HOL_ERR _ =>
            let val (left, right) = arith_dest_greater equality
             in (Gt, left, right) end
             handle Feedback.HOL_ERR _ =>
            let val (left, right) = arith_dest_geq equality
             in (Ge, left, right) end)
          val product_left = arith_mult (coefficient, left)
          val product_right = arith_mult (coefficient, right)
          val result =
            case relation of
              Eq => boolSyntax.mk_eq (product_left, product_right)
            | Lt => arith_less (product_left, product_right)
            | Le => arith_leq (product_left, product_right)
            | Gt => arith_greater (product_left, product_right)
            | Ge => arith_geq (product_left, product_right)
          val target = boolSyntax.mk_imp
            (boolSyntax.mk_conj
             (arith_greater (coefficient, arith_zero coefficient), equality),
             result)
        in arith_prove target end
    | _ => raise ERR "arith_mult_pos"
      "expected a coefficient and a non-negative arithmetic literal"

  (* CPC uses this rule to establish that two strictly positive factors have
     a strictly positive product. *)
  fun replay_arith_mult_sign args =
    case args of
      [positive_factors, product] =>
        arith_prove (boolSyntax.mk_imp
          (positive_factors,
           arith_greater (product, arith_zero product)))
    | _ => raise ERR "arith_mult_sign"
      "expected a conjunction of positive factors and their product"

  fun replay_arith_trichotomy declared prems =
    let
      datatype relation = Eq | Lt | Le | Gt | Ge
      fun dest_relation tm =
        let val (left, right) = boolSyntax.dest_eq tm in (Eq, left, right) end
        handle Feedback.HOL_ERR _ =>
        let val (left, right) = arith_dest_less tm in (Lt, left, right) end
        handle Feedback.HOL_ERR _ =>
        let val (left, right) = arith_dest_leq tm in (Le, left, right) end
        handle Feedback.HOL_ERR _ =>
        let val (left, right) = arith_dest_greater tm in (Gt, left, right) end
        handle Feedback.HOL_ERR _ =>
        let val (left, right) = arith_dest_geq tm in (Ge, left, right) end
      fun negate_relation (Lt, left, right) = (Ge, left, right)
        | negate_relation (Le, left, right) = (Gt, left, right)
        | negate_relation (Gt, left, right) = (Le, left, right)
        | negate_relation (Ge, left, right) = (Lt, left, right)
        | negate_relation (Eq, _, _) =
            raise ERR "arith_trichotomy"
              "CPC arithmetic trichotomy does not accept a disequality literal"
      fun normalize_not tm =
        let
          fun strip parity term =
            (strip (not parity) (boolSyntax.dest_neg term)
             handle Feedback.HOL_ERR _ => (parity, term))
          val (negated, atom) = strip true tm
          val result = dest_relation atom
        in if negated then negate_relation result else result end
      fun relation_name Eq = "="
        | relation_name Lt = "<"
        | relation_name Le = "<="
        | relation_name Gt = ">"
        | relation_name Ge = ">="
      fun reverse_relation Eq = Eq
        | reverse_relation Lt = Gt
        | reverse_relation Le = Ge
        | reverse_relation Gt = Lt
        | reverse_relation Ge = Le
      fun conclusion (Eq, Lt, left, right) = arith_greater (left, right)
        | conclusion (Eq, Gt, left, right) = arith_less (left, right)
        | conclusion (Gt, Eq, left, right) = arith_less (left, right)
        | conclusion (Lt, Eq, left, right) = arith_greater (left, right)
        | conclusion (Ge, Le, left, right) = boolSyntax.mk_eq (left, right)
        | conclusion (Le, Ge, left, right) = boolSyntax.mk_eq (left, right)
        | conclusion (Gt, Lt, left, right) = boolSyntax.mk_eq (left, right)
        | conclusion (Lt, Gt, left, right) = boolSyntax.mk_eq (left, right)
        | conclusion (relation1, relation2, _, _) =
            raise ERR "arith_trichotomy"
              ("normalized CPC relations " ^ relation_name relation1 ^
               " and " ^ relation_name relation2 ^
               " do not form a supported trichotomy")
      val alias_rewrites = [integerTheory.INT_GE, realTheory.real_ge]
      fun normalize_aliases tm =
        boolSyntax.rhs (Thm.concl
          (Rewrite.PURE_REWRITE_CONV alias_rewrites tm))
        handle Conv.UNCHANGED => tm
      fun normalize_operand tm =
        let
          val aliased = boolSyntax.rhs
            (Thm.concl (SmtReplayCanon.cpc_term_canon_conv
              (normalize_aliases tm)))
        in
          boolSyntax.rhs (Thm.concl
            (SmtReplayCanon.arith_poly_norm_conversion aliased))
          handle Conv.UNCHANGED => aliased
               | Feedback.HOL_ERR _ => aliased
        end
      fun antisym left right left_le_right right_le_left =
        let
          val rule =
            if Lib.equal (Term.type_of left) intSyntax.int_ty then
              integerTheory.INT_LE_ANTISYM
            else realTheory.REAL_LE_ANTISYM
        in
          Thm.MP (Drule.SPECL [left, right] rule)
            (Thm.CONJ left_le_right right_le_left)
        end
      fun prove_declared fallback =
        case declared of
          SOME target => arith_prove_from_prems prems target
        | NONE => arith_prove_from_prems prems fallback
    in
      case prems of
        [premise1, premise2] =>
          let
            val (relation1, left, right) = normalize_not (Thm.concl premise1)
            val (relation2_raw, a, b) =
              normalize_not (Thm.concl premise2)
            val normalized_left = normalize_operand left
            val normalized_right = normalize_operand right
            val normalized_a = normalize_operand a
            val normalized_b = normalize_operand b
            val same_operands =
              Term.aconv normalized_left normalized_a andalso
              Term.aconv normalized_right normalized_b
            val reversed_operands =
              Term.aconv normalized_left normalized_b andalso
              Term.aconv normalized_right normalized_a
            val relation2 =
              if reversed_operands then reverse_relation relation2_raw
              else relation2_raw
            val premise1' = Rewrite.PURE_REWRITE_RULE alias_rewrites premise1
            val premise2' = Rewrite.PURE_REWRITE_RULE alias_rewrites premise2
          in
          if same_operands orelse reversed_operands then
            ((case (relation1, relation2) of
               (Ge, Le) => antisym (normalize_aliases left)
                 (normalize_aliases right) premise2' premise1'
             | (Le, Ge) => antisym (normalize_aliases left)
                 (normalize_aliases right) premise1' premise2'
             | _ => arith_prove_from_prems prems
                 (conclusion (relation1, relation2, left, right)))
             handle Feedback.HOL_ERR _ =>
               prove_declared
                 (conclusion (relation1, relation2, left, right)))
          else prove_declared
            (conclusion (relation1, relation2, left, right))
          end
      | _ => raise ERR "arith_trichotomy" "expected two CPC premises"
    end

  (* Over integer terms, a strict integral upper bound can be tightened by
     one.  CPC emits this after arith-elim-lt has exposed an Int '<' atom. *)
  fun replay_int_tight_ub prems =
    let
      val premise = expect_one_premise "int_tight_ub" prems
      val (left, right) =
        intSyntax.dest_less (Thm.concl premise)
        handle Feedback.HOL_ERR _ =>
          Lib.swap (intSyntax.dest_greater (Thm.concl premise))
      val target = intSyntax.mk_leq
        (left, if Term.aconv right intSyntax.one_tm then intSyntax.zero_tm
               else intSyntax.mk_minus (right, intSyntax.one_tm))
    in arith_prove_from_prems [premise] target end

  (* Over integer terms, a strict integral lower bound can be tightened by
     one, while a non-strict bound is left unchanged. *)
  fun replay_int_tight_lb prems =
    let
      val premise = expect_one_premise "int_tight_lb" prems
      val (left, right, strict) =
        (let val (left, right) = intSyntax.dest_greater (Thm.concl premise)
         in (left, right, true) end
         handle Feedback.HOL_ERR _ =>
           (let val (left, right) = intSyntax.dest_geq (Thm.concl premise)
            in (left, right, false) end
            handle Feedback.HOL_ERR _ =>
              (let val (right, left) =
                 intSyntax.dest_less (Thm.concl premise)
               in (left, right, true) end
               handle Feedback.HOL_ERR _ =>
                 let val (right, left) =
                   intSyntax.dest_leq (Thm.concl premise)
                 in (left, right, false) end)))
      val target = intSyntax.mk_geq
        (left, if strict then intSyntax.mk_plus (right, intSyntax.one_tm)
               else right)
    in arith_prove_from_prems [premise] target end

  fun replay_arith_reduction args =
    let
      val reduction = expect_one_arg "arith_reduction" args
      val (head, operands) = boolSyntax.strip_comb reduction
      val int_ediv_tm = Term.prim_mk_const
        {Thy = "integer", Name = "ediv"}
      val int_emod_tm = Term.prim_mk_const
        {Thy = "integer", Name = "emod"}
      val smt_ediv_total_tm = Term.prim_mk_const
        {Thy = "HolSmt", Name = "smt_ediv_total"}
      val smt_emod_total_tm = Term.prim_mk_const
        {Thy = "HolSmt", Name = "smt_emod_total"}
      val smt_rdiv_tm = Term.prim_mk_const
        {Thy = "HolSmt", Name = "smt_rdiv"}
      fun total (constant, a, b) = Term.list_mk_comb
        (constant, [a, b])
      fun exact_nonconjunction detail term =
        conjunction_free_semantic_provenance
          ("arith_reduction " ^ detail ^ " unexpectedly contains a conjunction")
          term
      fun exact_theorem detail theorem =
        exact_nonconjunction detail (Thm.concl theorem)
      fun exact_binary_conjunction detail theorem =
        let
          val (left, right) = boolSyntax.dest_conj (Thm.concl theorem)
        in
          ConjunctionProvenance (ArithReductionConjunction,
            [exact_nonconjunction (detail ^ " left conjunct") left,
             exact_nonconjunction (detail ^ " right conjunct") right])
        end
      fun nonconjunction theorem =
        (theorem, conjunction_free_semantic_provenance
          "arith_reduction unexpectedly produced a conjunction"
          (Thm.concl theorem))
      fun guarded_conditional (a, b, total_term, equality) =
        let
          val condition = boolSyntax.mk_eq (b, intSyntax.zero_tm)
          val target = boolSyntax.mk_eq
            (reduction, boolSyntax.mk_cond
              (condition, equality, total_term))
        in
          nonconjunction (Tactical.TAC_PROOF (([], target),
             Tactical.THEN (Tactic.COND_CASES_TAC,
               bossLib.ASM_SIMP_TAC bossLib.arith_ss
                 [HolSmtTheory.smt_ediv_total_def,
                  HolSmtTheory.smt_emod_total_def])))
        end
      fun div_reduction () =
        (case operands of
           [a, b] => guarded_conditional (a, b,
             total (smt_ediv_total_tm, a, b),
             SmtLib_Theories.mk_int_ediv (a, intSyntax.zero_tm))
         | _ => raise ERR "arith_reduction"
             "ediv reduction expects two operands")
      fun mod_reduction () =
        (case operands of
           [a, b] =>
             let
               val condition = boolSyntax.mk_eq (b, intSyntax.zero_tm)
               val target = boolSyntax.mk_eq
                 (reduction, boolSyntax.mk_cond
                   (condition,
                    SmtLib_Theories.mk_int_emod
                      (a, intSyntax.zero_tm),
                    total (smt_emod_total_tm, a, b)))
             in
               nonconjunction (Tactical.TAC_PROOF (([], target),
                  Tactical.THEN (Tactic.COND_CASES_TAC,
                    bossLib.ASM_SIMP_TAC bossLib.arith_ss
                      [HolSmtTheory.smt_emod_total_def])))
             end
         | _ => raise ERR "arith_reduction"
             "emod reduction expects two operands")
      fun real_div_reduction () =
        (case operands of
           [a, b] =>
             let
               val condition = boolSyntax.mk_eq (b, realSyntax.zero_tm)
               val target = boolSyntax.mk_eq
                 (reduction, boolSyntax.mk_cond
                   (condition,
                    total (smt_rdiv_tm, a, realSyntax.zero_tm),
                    realSyntax.mk_div (a, b)))
             in
               nonconjunction (Tactical.TAC_PROOF (([], target),
                  Tactical.THEN (Tactic.COND_CASES_TAC,
                    bossLib.ASM_SIMP_TAC bossLib.arith_ss
                      [HolSmtTheory.smt_rdiv_eq_div])))
             end
         | _ => raise ERR "arith_reduction"
             "real division reduction expects two operands")
      fun total_div_reduction () =
        (case operands of
           [a, b] => let
             val equality = Thm.REFL reduction
             val bounds = Drule.SPECL [a, b]
               HolSmtTheory.smt_ediv_total_bounds
           in
             (Thm.CONJ equality bounds,
              ConjunctionProvenance (ArithReductionConjunction,
                [exact_theorem "equality conjunct" equality,
                 exact_binary_conjunction "bounds" bounds]))
           end
         | _ => raise ERR "arith_reduction"
             "div_total reduction expects two operands")
      fun total_mod_reduction () =
        (case operands of
           [a, b] =>
             let
               val equality = Drule.SPECL [a, b]
                 HolSmtTheory.smt_emod_total_ediv
               val target = boolSyntax.mk_eq (reduction,
                 intSyntax.mk_plus
                   (a, intSyntax.mk_negated
                     (intSyntax.mk_mult
                       (b, total (smt_ediv_total_tm, a, b)))))
             in
               (Thm.CONJ equality
                  (Drule.SPECL [a, b] HolSmtTheory.smt_ediv_total_bounds),
                ConjunctionProvenance (ArithReductionConjunction,
                  [exact_theorem "equality conjunct" equality,
                   exact_binary_conjunction "bounds"
                     (Drule.SPECL [a, b]
                       HolSmtTheory.smt_ediv_total_bounds)]))
             end
         | _ => raise ERR "arith_reduction"
             "mod_total reduction expects two operands")
      fun total_real_div_reduction () =
        (case operands of
           [a, b] =>
             let
               val side = boolSyntax.mk_imp
                 (boolSyntax.mk_neg
                   (boolSyntax.mk_eq (b, realSyntax.zero_tm)),
                  boolSyntax.mk_eq
                    (realSyntax.mk_mult
                       (b, realSyntax.mk_div (a, b)), a))
               val side_thm = Tactical.TAC_PROOF (([], side),
                 metisLib.METIS_TAC [realTheory.REAL_DIV_LMUL])
             in
               (Thm.CONJ (Thm.REFL reduction) side_thm,
                ConjunctionProvenance (ArithReductionConjunction,
                  [exact_theorem "equality conjunct"
                     (Thm.REFL reduction),
                   exact_theorem "nonzero-side conjunct" side_thm]))
             end
         | _ => raise ERR "arith_reduction"
             "/_total reduction expects two operands")
      fun floor_reduction () =
        let
          val real = intrealSyntax.dest_INT_FLOOR reduction
          val bounds = Thm.SPEC real HolSmtTheory.int_floor_remainder_bounds
        in
          (Thm.CONJ (Thm.REFL reduction) bounds,
           ConjunctionProvenance (ArithReductionConjunction,
             [exact_theorem "equality conjunct" (Thm.REFL reduction),
              exact_binary_conjunction "bounds" bounds]))
        end
      fun abs_reduction () =
        let
          val value = intSyntax.dest_absval reduction
          val target = boolSyntax.mk_eq (reduction,
            boolSyntax.mk_cond (intSyntax.mk_less (value, intSyntax.zero_tm),
              intSyntax.mk_negated value, value))
        in
          nonconjunction (Tactical.TAC_PROOF (([], target),
             Tactical.THEN (Tactic.COND_CASES_TAC,
               bossLib.ASM_SIMP_TAC bossLib.arith_ss
                 [integerTheory.INT_ABS])))
        end
    in
      if Term.aconv head intrealSyntax.INT_FLOOR_tm then floor_reduction ()
      else if Term.aconv head intSyntax.absval_tm then abs_reduction ()
      else if Term.aconv head int_ediv_tm then div_reduction ()
      else if Term.aconv head int_emod_tm then mod_reduction ()
      else if Term.aconv head smt_rdiv_tm then real_div_reduction ()
      else if Term.aconv head smt_ediv_total_tm then total_div_reduction ()
      else if Term.aconv head smt_emod_total_tm then total_mod_reduction ()
      else if Term.aconv head realSyntax.div_tm then total_real_div_reduction ()
      else raise ERR "arith_reduction"
        ("unsupported arithmetic reduction head " ^
         Library.term_to_string head)
    end

  fun replay_modus_ponens prems =
    case prems of
      [left, right] =>
        (Thm.MP right left
         handle Feedback.HOL_ERR _ =>
           (Thm.MP left right
            handle Feedback.HOL_ERR _ =>
              raise ERR "modus_ponens"
                ("canonical premises are not applicable; left=" ^
                 Library.term_to_string (Thm.concl left) ^ "; right=" ^
                 Library.term_to_string (Thm.concl right))))
    | _ => raise ERR "modus_ponens" "expected two CPC premises"

  (* Canonical matching must not replace an implication by its normalized
     consequence: omitted CPC conclusions are inferred from the original
     implication and later steps depend on that exact endpoint.  Normalize
     only to establish that the proposition proves the antecedent, transport
     it back, and apply the untouched implication. *)
  fun replay_canonical_modus_ponens strong_canon prems =
    let
      fun apply canon proposition implication =
        let
          val (antecedent, _) = boolSyntax.dest_imp (Thm.concl implication)
          val proposition_norm = canon (Thm.concl proposition)
          val antecedent_norm = canon antecedent
          val normalized_proposition =
            boolSyntax.rhs (Thm.concl proposition_norm)
          val normalized_antecedent =
            boolSyntax.rhs (Thm.concl antecedent_norm)
          val _ = Term.aconv normalized_proposition normalized_antecedent orelse
            raise ERR "modus_ponens"
              "canonical proposition does not match the exact antecedent"
          val proposition' = Thm.EQ_MP proposition_norm proposition
          val antecedent' = Thm.EQ_MP (Thm.SYM antecedent_norm) proposition'
        in
          Thm.MP implication antecedent'
        end
      fun oriented canon left right =
        apply canon left right
        handle Feedback.HOL_ERR _ => apply canon right left
    in
      case prems of
        [left, right] =>
          (oriented SmtReplayCanon.cpc_operand_canon_conv left right
           handle Feedback.HOL_ERR _ =>
             oriented strong_canon left right)
      | _ => raise ERR "modus_ponens" "expected two CPC premises"
    end

  (* Some arithmetic CPC certificates state an antecedent in an algebraically
     equivalent, rather than canonically identical, form.  Derive only that
     antecedent from the recorded proposition and then apply the untouched
     implication.  The arithmetic prover and MP remain kernel checked, and
     both premise hypothesis sets are retained. *)
  fun replay_arithmetic_modus_ponens prems =
    let
      fun apply proposition implication =
        let
          val (antecedent, _) = boolSyntax.dest_imp (Thm.concl implication)
          val antecedent_theorem =
            arith_prove_from_prems [proposition] antecedent
        in
          Thm.MP implication antecedent_theorem
        end
      fun oriented left right =
        apply left right
        handle Feedback.HOL_ERR _ => apply right left
    in
      case prems of
        [left, right] => oriented left right
      | _ => raise ERR "modus_ponens" "expected two CPC premises"
    end

  fun replay_arith_sum_ub prems =
    let
      fun equality_as_leq premise left right =
        let
          val reflexive_target = arith_leq (left, left)
          val (leq_const, _) = boolSyntax.strip_comb reflexive_target
          val reflexive =
            Drule.ISPEC left integerTheory.INT_LE_REFL
            handle Feedback.HOL_ERR _ =>
              Drule.ISPEC left realTheory.REAL_LE_REFL
          val transported = Thm.AP_TERM
            (Term.mk_comb (leq_const, left)) premise
        in
          Thm.EQ_MP transported reflexive
        end
      fun dest_bound premise =
        (let val (left, right) = arith_dest_less (Thm.concl premise)
         in (true, left, right, premise) end
        handle Feedback.HOL_ERR _ =>
          let val (left, right) = arith_dest_leq (Thm.concl premise)
           in (false, left, right, premise) end
           handle Feedback.HOL_ERR _ =>
             let val (left, right) = boolSyntax.dest_eq (Thm.concl premise)
             in (false, left, right,
               equality_as_leq premise left right) end)
      fun add_bounds ((left_strict, left_lhs, left_rhs, left_thm),
                      (right_strict, right_lhs, right_rhs, right_thm)) =
        let
          val int_rule =
            case (left_strict, right_strict) of
              (true, true) => integerTheory.INT_LT_ADD2
            | (false, true) => integerTheory.INT_LET_ADD2
            | (true, false) => integerTheory.INT_LTE_ADD2
            | (false, false) => integerTheory.INT_LE_ADD2
          val real_rule =
            case (left_strict, right_strict) of
              (true, true) => realTheory.REAL_LT_ADD2
            | (false, true) => realTheory.REAL_LET_ADD2
            | (true, false) => realTheory.REAL_LTE_ADD2
            | (false, false) => realTheory.REAL_LE_ADD2
          val rule =
            if Lib.equal (Term.type_of left_lhs) intSyntax.int_ty then int_rule
            else real_rule
          val combined = Thm.MP
            (Drule.SPECL [left_lhs, left_rhs, right_lhs, right_rhs] rule)
            (Thm.CONJ left_thm right_thm)
          (* Normalize each partial sum before adding the next bound.  CPC
             certificates use the polynomial normal form of the combined
             relation; retaining the unreduced expression here duplicates
             shared conditional terms exponentially and forces the following
             EQ_RESOLVE to rediscover the same linear cancellation. *)
          val combined = Conv.CONV_RULE
            (SmtReplayCanon.compose
              [SmtReplayCanon.cpc_operand_canon_conv,
               Conv.BINOP_CONV
                 (Conv.QCONV
                   SmtReplayCanon.arith_poly_norm_conversion)]) combined
          val (combined_lhs, combined_rhs) =
            if left_strict orelse right_strict then
              arith_dest_less (Thm.concl combined)
            else arith_dest_leq (Thm.concl combined)
        in
          (left_strict orelse right_strict,
           combined_lhs, combined_rhs, combined)
        end
      val bounds = List.map dest_bound prems
      val (_, _, _, result) =
        case bounds of
          first :: rest => List.foldl
            (fn (next, accumulated) => add_bounds (accumulated, next))
            first rest
        | [] => raise ERR "arith_sum_ub" "expected CPC premises"
    in result end

  fun replay_arith_rel prems args =
    let
      val target = expect_one_arg "arith_poly_norm_rel" args
      fun has_real_of_int tm =
        intrealSyntax.is_real_of_int tm orelse
        ((let val (f, x) = Term.dest_comb tm in
            has_real_of_int f orelse has_real_of_int x
          end) handle _ =>
          ((let val (_, body) = Term.dest_abs tm in has_real_of_int body end)
           handle _ => false))
      val needs_real_normalization = has_real_of_int target orelse
        List.exists (has_real_of_int o Thm.concl) prems
      (* E1(a): one coverage terminal for the complete linear Int/Real
         fragment of arith_poly_norm_rel.  Mixed formulas first use the
         canonical cast-abstraction procedure; formulas without casts use
         the general arithmetic prover directly.  This is semantic fragment
         dispatch, not an optional cache, so it remains enabled in D-mode. *)
      fun general () =
        if needs_real_normalization then
          profile "CPC(arith_rel:fragment/cast)"
            (prove_cast_arithmetic prems) target
        else
          profile "CPC(arith_rel:fragment/plain)"
            (arith_prove_from_prems prems) target
      val () = profile_event
        ("CPC(arith_rel:premises=" ^ Int.toString (List.length prems) ^ ")")
    in
      profile "CPC(rung:arith_rel/general)" general ()
      handle Feedback.HOL_ERR general_error =>
        raise ERR "arith_poly_norm_rel"
          ("general linear arithmetic reconstruction failed for target " ^
           Library.term_to_string target ^ "; premises=" ^
           String.concatWith ", "
             (List.map (Library.term_to_string o Thm.concl) prems) ^
           "; underlying error=" ^ Feedback.message_of general_error)
    end

  fun replay_datatype args =
    case args of
      [left, right] =>
        profile "CPC(rung:datatype/prove)" SmtDatatypeProve.datatype_prove
          (boolSyntax.mk_neg (boolSyntax.mk_eq (left, right)))
    | _ => raise ERR "datatype" "expected two constructor values"

  fun replay_dt_split args =
    case args of
      [scrutinee] =>
        let
          val ty = Term.type_of scrutinee
          val constructors = SmtDatatypeProve.constructors_of ty
          val testers = List.map
            (fn constructor =>
              SmtDatatypeProve.datatype_tester_term
                ty constructor scrutinee)
            constructors
          val target = mk_disj_terms testers
        in
          profile "CPC(rung:datatype/split)"
            SmtDatatypeProve.datatype_prove target
        end
    | _ => raise ERR "dt_split" "expected one datatype scrutinee"

  fun replay_datatype_eq args =
    profile "CPC(rung:datatype/prove_eq)" SmtDatatypeProve.datatype_prove
      (expect_one_arg "datatype_eq" args)

  val resolution_literal_normalizations = ref
    (Redblackmap.mkDict Term.compare :
      (Term.term, Thm.thm) Redblackmap.dict)

  (* Recognition retains checked leaf bridges but does not construct the
     recursive implication proof.  All tables belong to this one target and
     conversion context.  Hashes only select buckets; typed alpha-equality
     decides every hit.  Target paths include internal disjunctions, since
     those can themselves be literal occurrences. *)
  fun disjunction_alignment_plan
      {target, hash, equivalence, conversion, count} source =
    let
      datatype insertion = Left of Term.term | Right of Term.term
      datatype plan =
          Member of Term.term * insertion list * Thm.thm option
        | Disjunction of Term.term * plan * plan
        | Conjunction of Term.term * bool * plan
        | Conversion of Term.term * Thm.thm * plan
      datatype decision = Visiting | Declined | Planned of plan
      val buckets = 1021
      val targets = Array.array
        (buckets, [] : (Term.term * insertion list) list)
      val memo = Array.array
        (buckets, [] : (Term.term * decision) list)
      val occurrences = ref ([] : (Term.term * insertion list) list)
      fun index term = hash term mod buckets
      fun same left right = Portable.pointer_eq (left, right) orelse
        Term.aconv left right
      fun target_index term path =
        let val key = index term
            val bucket = Array.sub (targets, key)
        in
          if List.exists (fn (saved, _) => same saved term) bucket then ()
          else
            (count "target-nodes" 1;
             Array.update (targets, key, (term, path) :: bucket);
             occurrences := (term, path) :: !occurrences;
             case Lib.total boolSyntax.dest_disj term of
               SOME (left, right) =>
                 (target_index left (Left right :: path);
                  target_index right (Right left :: path))
             | NONE => ())
        end
      val _ = target_index target []
      val target_occurrences = List.rev (!occurrences)
      fun checked_equality left right theorem =
        let
          val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl theorem)
          val _ = Library.check_oracle_tags
            "CPC_ProofReplay" "disjunction plan bridge" theorem
        in
          if same lhs left andalso same rhs right andalso
             List.null (Thm.hyp theorem) then theorem
          else raise ERR "disjunction_alignment_plan"
            "leaf bridge has incorrect endpoints or hypotheses"
        end
      fun membership term =
        let
          val _ = count "membership" 1
          val exact = List.find (fn (saved, _) => same saved term)
            (Array.sub (targets, index term))
          fun semantic [] = NONE
            | semantic ((literal, path) :: rest) =
                case equivalence term literal of
                  SOME theorem => SOME (Member (term, path,
                    SOME (checked_equality term literal theorem)))
                | NONE => semantic rest
        in
          case exact of
            SOME (_, path) => SOME (Member (term, path, NONE))
          | NONE => semantic target_occurrences
        end
      fun save term value =
        let val key = index term
        in Array.update (memo, key, (term, value) ::
          List.filter (fn (saved, _) => not (same saved term))
            (Array.sub (memo, key))) end
      fun recognize term =
        let
          val _ = count "visits" 1
        in
          case List.find (fn (saved, _) => same saved term)
              (Array.sub (memo, index term)) of
            SOME (_, Planned result) =>
              (count "repeated" 1; SOME result)
          | SOME (_, _) => (count "repeated-decline" 1; NONE)
          | NONE =>
              let
                val _ = count "nodes" 1
                val _ = save term Visiting
                val result =
                  if boolSyntax.is_disj term then
                    let val (left, right) = boolSyntax.dest_disj term
                    in case recognize left of
                         NONE => NONE
                       | SOME l => Option.map
                           (fn r => Disjunction (term, l, r))
                           (recognize right)
                    end
                  else if boolSyntax.is_conj term then
                    let val (left, right) = boolSyntax.dest_conj term
                    in case recognize left of
                         SOME l => SOME (Conjunction (term, true, l))
                       | NONE => Option.map
                           (fn r => Conjunction (term, false, r))
                           (recognize right)
                    end
                  else case membership term of
                    SOME member => SOME member
                  | NONE =>
                      (case conversion term of
                         NONE => NONE
                       | SOME bridge =>
                           let
                             val residue = boolSyntax.rhs (Thm.concl bridge)
                             val bridge = checked_equality term residue bridge
                           in Option.map
                             (fn sub => Conversion (term, bridge, sub))
                             (recognize residue) end)
                val _ = save term (case result of
                    NONE => Declined | SOME p => Planned p)
                val _ = if Option.isSome result then () else count "declines" 1
              in result end
        end
      val realized = Array.array
        (buckets, [] : (Term.term * Thm.thm) list)
      fun source_of (Member (term, _, _)) = term
        | source_of (Disjunction (term, _, _)) = term
        | source_of (Conjunction (term, _, _)) = term
        | source_of (Conversion (term, _, _)) = term
      fun realize p =
        let val term = source_of p
            val key = index term
        in
          case List.find (fn (saved, _) => same saved term)
              (Array.sub (realized, key)) of
            SOME (_, theorem) => theorem
          | NONE =>
              let
                val _ = count "proof-nodes" 1
                val _ = count "proof-edges" (case p of
                    Member _ => 0 | Disjunction _ => 2 | _ => 1)
                val assumption = Thm.ASSUME term
                val result = case p of
                    Member (_, path, bridge) =>
                      List.foldl
                        (fn (Left right, th) => Thm.DISJ1 th right
                          | (Right left, th) => Thm.DISJ2 left th)
                        (case bridge of NONE => assumption
                         | SOME eq => Thm.EQ_MP eq assumption) path
                  | Disjunction (_, l, r) =>
                      let val (left, right) = boolSyntax.dest_disj term
                      in Thm.DISJ_CASES assumption
                        (Thm.MP (realize l) (Thm.ASSUME left))
                        (Thm.MP (realize r) (Thm.ASSUME right)) end
                  | Conjunction (_, first, sub) =>
                      Thm.MP (realize sub)
                        ((if first then Thm.CONJUNCT1 else Thm.CONJUNCT2)
                          assumption)
                  | Conversion (_, bridge, sub) =>
                      Thm.MP (realize sub) (Thm.EQ_MP bridge assumption)
                val theorem = Thm.DISCH term result
                val _ = same (Thm.concl theorem)
                    (boolSyntax.mk_imp (term, target)) andalso
                    List.null (Thm.hyp theorem) orelse
                  raise ERR "disjunction_alignment_plan"
                    "realized plan has incorrect endpoints or hypotheses"
                val _ = Array.update (realized, key,
                  (term, theorem) :: Array.sub (realized, key))
              in theorem end
        end
    in Option.map (fn p => fn () => realize p) (recognize source) end

  fun semantic_tseitin_law source destination =
    resolution_profile "tseitin/total" (fn () =>
    let
      fun unfold_xor term =
        let
          val (head, arguments) = boolSyntax.strip_comb term
          val {Thy, Name, ...} = Term.dest_thy_const head
        in
          if Thy = "HolSmt" andalso Name = "xor" andalso
              List.length arguments = 2 then
            SOME (Conv.REWR_CONV HolSmtTheory.xor_def term)
          else NONE
        end
        handle Feedback.HOL_ERR _ => NONE
      (* This caller has no definition-count admission limit.  The
         bounded Boolean DAG caller checks its own unchanged cap. *)
      val graph = SmtBooleanGraph.new
        {chunk_depth = NONE, stops = [],
         stop_conversion = fn _ => NONE,
         leaf = CPC_ProofParser.intern_cpc_term, unfold = unfold_xor}
      val _ = resolution_profile "tseitin/source-circuit"
        (#circuit graph) source
      val _ = resolution_profile "tseitin/target-circuit"
        (#circuit graph) destination
      val root = #circuit graph
        (boolSyntax.mk_imp (source, destination))
      val definitions = #definitions graph ()
      val _ = if not (!resolution_profile_enabled) then () else
        let val {nodes, leaves} = #counts graph () in
          resolution_count "tseitin/nodes" nodes;
          resolution_count "tseitin/leaves" leaves;
          resolution_count "tseitin/definitions"
            (List.length definitions)
        end
      val law = SmtBooleanGraph.prove_cnf_using
        (fn stage => fn action =>
          resolution_profile ("tseitin/" ^ stage) action ())
        {definitions = definitions,
         substitutions = #substitutions graph (), root = root}
      val _ = Term.aconv (Thm.concl law)
          (boolSyntax.mk_imp (source, destination)) andalso
          List.null (Thm.hyp law) orelse
        raise ERR "resolution" "Boolean graph endpoint mismatch"
    in law end) ()

  fun replay_resolution prems conclusion args =
    let
      (* A proof of T is a neutral resolution premise regardless of which
         irrelevant assumptions were retained while producing it.  Rebuild
         it as kernel TRUTH so the general route does not depend on a cache
         hit to discard those assumptions. *)
      val prems = List.map (fn theorem =>
        if Term.aconv (Thm.concl theorem) boolSyntax.T then boolTheory.TRUTH
        else theorem) prems
      (* Most CPC literals are pointer-shared.  One-bit word propositions can
         nevertheless enter through either Boolean extraction or equality
         with 1w; compare those through checked word normalization. *)
      fun word_bridge_literal term =
        let
          val atom = boolSyntax.dest_neg term
            handle Feedback.HOL_ERR _ => term
        in
          wordsSyntax.is_word_bit atom orelse
          (case Lib.total boolSyntax.dest_eq atom of
             SOME (left, right) =>
               wordsSyntax.is_word_type (Term.type_of left) orelse
               wordsSyntax.is_word_type (Term.type_of right)
           | NONE => false)
        end
      fun literal_kind term =
        let
          val atom = case Lib.total boolSyntax.dest_neg term of
              SOME body => body
            | NONE => term
          val (head, arguments) = boolSyntax.strip_comb atom
          val name =
            (let val {Thy, Name, ...} = Term.dest_thy_const head
             in Thy ^ "$" ^ Name end)
            handle Feedback.HOL_ERR _ =>
              if Term.is_var head then "variable" else "compound"
        in name ^ "/" ^ Int.toString (List.length arguments) end
      fun resolution_node_conversion term =
        SmtFpGraph.convert_word_projection term
        handle Conv.UNCHANGED =>
          (Conv.REWR_CONV
             smtfloatReplayRoundingTheory.word_compare_index term
           handle Feedback.HOL_ERR _ => raise Conv.UNCHANGED)
             | Empty => raise Conv.UNCHANGED
             | Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else raise Conv.UNCHANGED
      fun normalize_literal term =
        case Redblackmap.peek (!resolution_literal_normalizations, term) of
          SOME theorem => theorem
        | NONE =>
            let
              val theorem =
                (SmtWordGraph.normalize_with_node_conversion
                   resolution_node_conversion term
                 handle Conv.UNCHANGED =>
                   (SmtWordGraph.normalize term
                    handle Conv.UNCHANGED => Thm.REFL term))
              val _ = resolution_literal_normalizations :=
                Redblackmap.insert
                  (!resolution_literal_normalizations, term, theorem)
            in theorem end
      fun literal_hash_string string =
        CharVector.foldl
          (fn (character, hash) =>
            (hash * 33 + Char.ord character) mod 1000003) 17 string
      fun literal_hash 0 term =
            if Term.is_const term then
              let val {Thy, Name, ...} = Term.dest_thy_const term
              in (literal_hash_string Thy * 37 +
                  literal_hash_string Name) mod 1000003 end
            else if Term.is_var term then 3
            else if Term.is_abs term then 5
            else 7
        | literal_hash depth term =
            if Term.is_comb term then
              (literal_hash (depth - 1) (Term.rator term) * 41 +
               literal_hash (depth - 1) (Term.rand term) * 67 + 11) mod
                1000003
            else if Term.is_abs term then
              (literal_hash (depth - 1) (Term.body term) * 73 + 13) mod
                1000003
            else literal_hash 0 term
      fun normalized_literal_equal left right =
        let
          val left_theorem = normalize_literal left
          val right_theorem = normalize_literal right
          val left_residue = boolSyntax.rhs (Thm.concl left_theorem)
          val right_residue = boolSyntax.rhs (Thm.concl right_theorem)
        in
          Portable.pointer_eq (left_residue, right_residue) orelse
          (literal_hash 6 left_residue = literal_hash 6 right_residue andalso
           shared_aconv left_residue right_residue)
        end
      val literal_equivalences = ref
        ([] : (Term.term * Term.term * Thm.thm option) list)
      fun decided_literal_equivalence left right =
        case List.find (fn (saved_left, saved_right, _) =>
            Portable.pointer_eq (saved_left, left) andalso
            Portable.pointer_eq (saved_right, right))
            (!literal_equivalences) of
          SOME (_, _, result) => result
        | NONE =>
            let
              val result =
                SOME (Drule.EQT_ELIM (wordsLib.WORD_DECIDE
                  (boolSyntax.mk_eq (left, right))))
                handle Conv.UNCHANGED => NONE
                     | Feedback.HOL_ERR _ => NONE
              val _ = literal_equivalences :=
                (left, right, result) :: !literal_equivalences
            in result end
      fun strip_literal_negation term =
        case Lib.total boolSyntax.dest_neg term of
          SOME atom => (true, atom)
        | NONE => (false, term)
      fun one_bit_equality atom =
        let
          val (left, right) = boolSyntax.dest_eq atom
          val (word, literal) =
            if wordsSyntax.is_word_literal right then (left, right)
            else (right, left)
          val _ = Arbnum.compare
              (wordsSyntax.dest_word_literal literal, Arbnum.one) = EQUAL orelse
            raise ERR "resolution" "not equality with 1w"
          val _ = Arbnum.compare
              (fcpSyntax.dest_numeric_type
                 (wordsSyntax.dest_word_type (Term.type_of word)),
               Arbnum.one) = EQUAL orelse
            raise ERR "resolution" "not a one-bit word"
        in word end
      fun bridge_shape left right =
        let
          val (left_negated, left_atom) = strip_literal_negation left
          val (right_negated, right_atom) = strip_literal_negation right
          val _ = left_negated = right_negated orelse
            raise ERR "resolution" "different literal polarities"
          val (bit_atom, equality_atom) =
            if wordsSyntax.is_word_bit left_atom then
              (left_atom, right_atom)
            else (right_atom, left_atom)
          val (index, bit_word) = wordsSyntax.dest_word_bit bit_atom
          val _ = Arbnum.compare
              (numSyntax.dest_numeral index, Arbnum.zero) = EQUAL orelse
            raise ERR "resolution" "not bit zero"
          val equality_word = one_bit_equality equality_atom
        in shared_aconv bit_word equality_word end
        handle Feedback.HOL_ERR _ => false
      fun literal_equivalence left right =
        let
          val (left_negated, _) = strip_literal_negation left
          val (right_negated, _) = strip_literal_negation right
        in
          if left_negated <> right_negated orelse
             not (word_bridge_literal left andalso
                  word_bridge_literal right) then NONE
          else if normalized_literal_equal left right then
            let
              val left_conversion = normalize_literal left
              val right_conversion = normalize_literal right
            in SOME (Thm.TRANS left_conversion
              (Thm.SYM right_conversion)) end
          else if bridge_shape left right then
            decided_literal_equivalence left right
          else NONE
        end
      fun structural_literal_equal left right =
        Portable.pointer_eq (left, right) orelse
        (literal_hash 6 left = literal_hash 6 right andalso
         shared_aconv left right)
      fun literal_equal left right =
        structural_literal_equal left right orelse
        Option.isSome (literal_equivalence left right)
      fun convert_literal theorem target =
        let val source = Thm.concl theorem in
          if Term.aconv source target then theorem
          else
            (case literal_equivalence source target of
               SOME equivalence => Thm.EQ_MP equivalence theorem
             | NONE => raise ERR "resolution"
                 "incompatible canonical CPC literals")
        end
      fun strip_clause term =
        (let val (left, right) = boolSyntax.dest_disj term in
           left :: strip_clause right
         end)
        handle Feedback.HOL_ERR _ => [term]
      fun remove_first_using _ _ [] = NONE
        | remove_first_using equal literal (candidate :: rest) =
            if equal literal candidate then SOME rest
            else Option.map (fn rest' => candidate :: rest')
              (remove_first_using equal literal rest)
      fun remove_first literal literals =
        case remove_first_using structural_literal_equal literal literals of
          SOME rest => SOME rest
        | NONE => remove_first_using literal_equal literal literals
      fun complement literal =
        boolSyntax.dest_neg literal
        handle Feedback.HOL_ERR _ => boolSyntax.mk_neg literal
      val recent_semantic_aliases = ref ([] : Term.term list)
      fun resolve_pair_on_with_hashed_stop_match require_both stop_match
          use_structural_equality hashed_stops first_pivot first second =
        let
          val second_pivot = complement first_pivot
          val equal = if use_structural_equality then
            structural_literal_equal else literal_equal
          fun is_stop term =
            let val hash = literal_hash 6 term in
              List.exists (fn (saved_hash, stop) =>
                hash = saved_hash andalso stop_match term stop) hashed_stops
            end
          fun strip_resolution_clause required term =
            let
              val required_hash = literal_hash 6 required
              fun required_match candidate =
                Portable.pointer_eq (candidate, required) orelse
                (literal_hash 6 candidate = required_hash andalso
                 shared_aconv candidate required)
              fun strip pending accumulated =
                case pending of
                  [] => List.rev accumulated
                | current :: rest =>
                    if required_match current orelse is_stop current then
                      strip rest (current :: accumulated)
                    else
                      case Lib.total boolSyntax.dest_disj current of
                        SOME (left, right) =>
                          strip (left :: right :: rest) accumulated
                      | NONE => strip rest (current :: accumulated)
            in strip [term] [] end
          val first_lits = strip_resolution_clause
            first_pivot (Thm.concl first)
          val second_lits = strip_resolution_clause
            second_pivot (Thm.concl second)
          val first_removed =
            remove_first_using equal first_pivot first_lits
          val second_removed =
            remove_first_using equal second_pivot second_lits
          val first_rest = case first_removed of
              SOME rest => List.filter
                (fn literal =>
                  not (equal first_pivot literal))
                rest
            | NONE => first_lits
          val second_rest = case second_removed of
              SOME rest => List.filter
                (fn literal =>
                  not (equal second_pivot literal))
                rest
            | NONE => second_lits
          fun unique literals =
            if use_structural_equality then
              let
                val buckets = ref (Redblackmap.mkDict Int.compare)
                fun keep (literal, kept) =
                  let
                    val hash = literal_hash 6 literal
                    val bucket =
                      case Redblackmap.peek (!buckets, hash) of
                        SOME saved => saved
                      | NONE => []
                  in
                    if List.exists
                        (structural_literal_equal literal) bucket then
                      kept
                    else
                      (buckets := Redblackmap.insert
                        (!buckets, hash, literal :: bucket);
                       literal :: kept)
                  end
              in List.rev (List.foldl keep [] literals) end
            else
              List.rev (List.foldl
                (fn (literal, kept) =>
                  if List.exists (literal_equal literal) kept then
                    kept
                  else literal :: kept)
                [] literals)
          val first_tail = mk_disj_terms first_rest
          val second_tail = mk_disj_terms second_rest
          val result_literals = unique (first_rest @ second_rest)
          val result = mk_disj_terms result_literals
          val semantic_aliases = List.filter
            (fn literal => literal_equal first_pivot literal andalso
              not (structural_literal_equal first_pivot literal))
            (first_lits @ second_lits)
          val _ = recent_semantic_aliases := semantic_aliases
          val _ = ()
          fun prove_member literal target =
            if equal literal target then
              convert_literal (Thm.ASSUME literal) target
            else
              let val (left, right) = boolSyntax.dest_disj target in
                if equal literal left then
                  Thm.DISJ1 (convert_literal (Thm.ASSUME literal) left) right
                else Thm.DISJ2 left (prove_member literal right)
              end
          fun reorder_clause theorem pivot tail =
            let
              val target = boolSyntax.mk_disj (pivot, tail)
              fun branch theorem =
                if equal (Thm.concl theorem) pivot then
                  Thm.DISJ1 (convert_literal theorem pivot) tail
                else
                  (Thm.DISJ2 pivot
                     (prove_member (Thm.concl theorem) tail)
                   handle Feedback.HOL_ERR _ =>
                     let
                       val (left, right) =
                         boolSyntax.dest_disj (Thm.concl theorem)
                     in
                       Thm.DISJ_CASES theorem (branch (Thm.ASSUME left))
                         (branch (Thm.ASSUME right))
                     end)
            in branch theorem end
          fun inject_clause theorem target =
            let
              fun branch theorem =
                (prove_member (Thm.concl theorem) target
                 handle Feedback.HOL_ERR _ =>
                   let
                     val (left, right) =
                       boolSyntax.dest_disj (Thm.concl theorem)
                   in
                     Thm.DISJ_CASES theorem (branch (Thm.ASSUME left))
                       (branch (Thm.ASSUME right))
                   end)
            in branch theorem end
          fun first_normal () = reorder_clause first first_pivot first_tail
            handle Feedback.HOL_ERR _ => raise ERR "resolution"
              "could not normalize the first resolution clause"
          fun second_normal () = reorder_clause second second_pivot second_tail
            handle Feedback.HOL_ERR _ => raise ERR "resolution"
              "could not normalize the second resolution clause"
          val from_false = fn contradiction => Thm.MP
            (Thm.SPEC result boolTheory.FALSITY) contradiction
          fun inject_or_false theorem =
            if Term.aconv (Thm.concl theorem) boolSyntax.F then from_false theorem
            else inject_clause theorem result
          val first_case = Thm.ASSUME first_pivot
          val second_case = Thm.ASSUME second_pivot
          val contradiction =
            (boolSyntax.dest_neg first_pivot;
             Thm.MP first_case second_case)
            handle Feedback.HOL_ERR _ => Thm.MP second_case first_case
          val second_false_branch = from_false contradiction
          val second_tail_branch = inject_or_false (Thm.ASSUME second_tail)
          fun resolve_pivot () = Thm.DISJ_CASES (second_normal ()) second_false_branch
            second_tail_branch
            handle Feedback.HOL_ERR _ => raise ERR "resolution"
              ("could not discharge the second resolution clause; false branch=" ^
               Library.term_to_string (Thm.concl second_false_branch) ^
               "; tail branch=" ^
               Library.term_to_string (Thm.concl second_tail_branch))
          fun resolve_rest () = inject_or_false (Thm.ASSUME first_tail)
        in
          case (first_removed, second_removed) of
            (SOME _, SOME _) =>
              (let
                 val first_normalized = first_normal ()
                 val pivot_result = resolve_pivot ()
                 val rest_result = resolve_rest ()
               in
                 Thm.DISJ_CASES first_normalized pivot_result rest_result
               end
               handle Feedback.HOL_ERR _ => raise ERR "resolution"
                 "could not discharge the first resolution clause")
          (* cvc5 permits a missing pivot as a weakening: retain that
             uneliminated premise and inject it into the result clause. *)
          | (NONE, _) =>
              if require_both then
                raise ERR "resolution" "first pivot is absent"
              else inject_clause first result
          | (_, NONE) =>
              if require_both then
                raise ERR "resolution" "second pivot is absent"
              else inject_clause second result
        end
        handle Feedback.HOL_ERR holerr =>
          raise ERR "resolution"
            ("kernel resolution failed on pivot " ^
             Library.term_to_string first_pivot ^ ": " ^
             Feedback.message_of holerr)
      fun resolve_pair_on_with_stop_match require_both stop_match stops =
        resolve_pair_on_with_hashed_stop_match require_both stop_match false
          (List.map (fn stop => (literal_hash 6 stop, stop)) stops)
      fun resolve_pair_on stops = resolve_pair_on_with_stop_match false
        (fn left => fn right => Portable.pointer_eq (left, right)) stops
      fun resolve_pair_on_structural stops = resolve_pair_on_with_stop_match
        false structural_literal_equal stops
      fun resolve_pair_on_structural_strict_hashed stops =
        resolve_pair_on_with_hashed_stop_match true
          structural_literal_equal true stops
      fun replay_chain target polarities pivots =
        let
          val expected = List.length prems - 1
          val _ = List.length polarities = expected andalso
                  List.length pivots = expected orelse
            raise ERR "resolution" "resolution-chain annotation arity mismatch"
          fun signed_pivot polarity pivot =
            if Term.aconv polarity boolSyntax.T then pivot
            else if Term.aconv polarity boolSyntax.F then complement pivot
            else raise ERR "resolution" "resolution-chain polarity is not Boolean"
          fun prove_member literal target =
            if literal_equal literal target then
              convert_literal (Thm.ASSUME literal) target
            else
              let val (left, right) = boolSyntax.dest_disj target in
                if literal_equal literal left then
                  Thm.DISJ1 (convert_literal (Thm.ASSUME literal) left) right
                else Thm.DISJ2 left (prove_member literal right)
              end
          fun factor theorem =
            let
              fun seen literal literals =
                List.exists (literal_equal literal) literals
              fun unique literals =
                List.rev (List.foldl (fn (literal, kept) =>
                  if seen literal kept then kept else literal :: kept) [] literals)
              val factored = mk_disj_terms (unique
                (strip_clause (Thm.concl theorem)))
            in
              if Term.aconv (Thm.concl theorem) factored then theorem
              else
                let
                  fun branch theorem =
                    case (SOME (boolSyntax.dest_disj (Thm.concl theorem))
                          handle Feedback.HOL_ERR _ => NONE) of
                      SOME (left, right) =>
                        Thm.DISJ_CASES theorem (branch (Thm.ASSUME left))
                          (branch (Thm.ASSUME right))
                    | NONE => prove_member (Thm.concl theorem) factored
                in branch theorem end
            end
          val chain_stops = strip_clause target @ pivots @
            List.map complement pivots
          val hash_modulus = 1000003
          fun hash_string string =
            CharVector.foldl
              (fn (character, hash) =>
                (hash * 33 + Char.ord character) mod hash_modulus)
              17 string
          fun stop_hash 0 term =
                if Term.is_var term then 3
                else if Term.is_const term then
                  let val {Thy, Name, ...} = Term.dest_thy_const term
                  in (hash_string Thy + 37 * hash_string Name) mod
                    hash_modulus
                  end
                else if Term.is_comb term then 5 else 7
            | stop_hash depth term =
                if Term.is_comb term then
                  let val (operator, operand) = Term.dest_comb term
                  in (19 * stop_hash (depth - 1) operator +
                      41 * stop_hash (depth - 1) operand) mod hash_modulus
                  end
                else if Term.is_abs term then
                  (43 * stop_hash (depth - 1)
                    (#2 (Term.dest_abs term))) mod hash_modulus
                else stop_hash 0 term
          val hashed_stops = List.map (fn stop =>
            (stop_hash 6 stop, stop)) chain_stops
          fun is_chain_stop term =
            let val hash = stop_hash 6 term in
              List.exists (fn (stop_hash, stop) =>
                hash = stop_hash andalso
                (Portable.pointer_eq (term, stop) orelse
                 shared_aconv term stop)) hashed_stops
            end
          fun clause_pair term =
            if is_chain_stop term then NONE
            else Lib.total boolSyntax.dest_disj term
          fun reorder_to_target theorem =
            let
              val exact_modulus = 1000000007
              fun exact_hash root =
                let
                  type environment = Term.term list
                  val memo = ref
                    ([] : (Term.term * environment * int) list)
                  fun same_environment [] [] = true
                    | same_environment (left :: rest)
                        (right :: saved_rest) =
                        Portable.pointer_eq (left, right) andalso
                        same_environment rest saved_rest
                    | same_environment _ _ = false
                  fun bound_index variable environment =
                    let
                      fun seek _ [] = NONE
                        | seek index (bound :: rest) =
                            if Term.compare (variable, bound) = EQUAL then
                              SOME index
                            else seek (index + 1) rest
                    in seek 0 environment end
                  fun hash environment term =
                    case List.find (fn (saved, saved_environment, _) =>
                        Portable.pointer_eq (saved, term) andalso
                        same_environment environment saved_environment)
                        (!memo) of
                      SOME (_, _, value) => value
                    | NONE =>
                        let
                          val value =
                            if Term.is_comb term then
                              (97 * hash environment (Term.rator term) +
                               193 * hash environment (Term.rand term) + 11)
                              mod exact_modulus
                            else if Term.is_abs term then
                              (389 * hash (Term.bvar term :: environment)
                                (Term.body term) + 17) mod exact_modulus
                            else if Term.is_const term then
                              let
                                val {Thy, Name, ...} =
                                  Term.dest_thy_const term
                              in (hash_string Thy * 769 +
                                  hash_string Name * 1543 + 23) mod
                                exact_modulus
                              end
                            else if Term.is_var term then
                              (case bound_index term environment of
                                 SOME index =>
                                   (index * 3079 + 31) mod exact_modulus
                               | NONE =>
                                   let val (name, _) = Term.dest_var term in
                                     (hash_string name * 6151 + 29) mod
                                       exact_modulus
                                   end)
                            else 37
                          val _ = memo :=
                            (term, environment, value) :: !memo
                        in value end
                in hash [] root end
              fun has_abstraction root =
                let
                  val seen = ref ([] : Term.term list)
                  fun search term =
                    if List.exists (fn saved =>
                         Portable.pointer_eq (saved, term)) (!seen) then false
                    else
                      (seen := term :: !seen;
                       Term.is_abs term orelse
                       if Term.is_comb term then
                         search (Term.rator term) orelse
                         search (Term.rand term)
                       else false)
                in search root end
              fun dag_same left_root right_root =
                let
                  val bucket_count = 4093
                  type environment = (Term.term * Term.term) list
                  val buckets = Array.array (bucket_count,
                    [] : (Term.term * Term.term * environment * bool) list)
                  val ids = ref ([] : (Term.term * int) list)
                  val next_id = ref 0
                  fun pointer_id term =
                    case List.find (fn (saved, _) =>
                        Portable.pointer_eq (saved, term)) (!ids) of
                      SOME (_, id) => id
                    | NONE =>
                        let
                          val id = !next_id
                          val _ = next_id := id + 1
                          val _ = ids := (term, id) :: !ids
                        in id end
                  fun index left right =
                    (pointer_id left * 67 + pointer_id right) mod bucket_count
                  fun same_environment [] [] = true
                    | same_environment
                        ((left, right) :: rest)
                        ((saved_left, saved_right) :: saved_rest) =
                        Portable.pointer_eq (left, saved_left) andalso
                        Portable.pointer_eq (right, saved_right) andalso
                        same_environment rest saved_rest
                    | same_environment _ _ = false
                  fun find [] _ _ _ = NONE
                    | find ((saved_left, saved_right, saved_environment,
                            result) :: rest) left right environment =
                        if Portable.pointer_eq (saved_left, left) andalso
                           Portable.pointer_eq (saved_right, right) andalso
                           same_environment environment saved_environment then
                          SOME result
                        else find rest left right environment
                  fun bound_partner variable environment =
                    case List.find (fn (left, _) =>
                        Term.compare (left, variable) = EQUAL) environment of
                      SOME (_, right) => SOME right
                    | NONE => NONE
                  fun is_right_bound variable environment =
                    List.exists (fn (_, right) =>
                      Term.compare (right, variable) = EQUAL) environment
                  fun same environment left right =
                    if Portable.pointer_eq (left, right) then true
                    else
                      let val bucket = index left right in
                        case find (Array.sub (buckets, bucket)) left right
                            environment of
                          SOME result => result
                        | NONE =>
                            let
                              val result =
                                if Term.is_comb left andalso
                                   Term.is_comb right then
                                  same environment (Term.rator left)
                                    (Term.rator right) andalso
                                  same environment (Term.rand left)
                                    (Term.rand right)
                                else if Term.is_const left andalso
                                        Term.is_const right then
                                  Term.same_const left right
                                else if Term.is_var left andalso
                                        Term.is_var right then
                                  (case bound_partner left environment of
                                     SOME partner =>
                                       Term.compare (partner, right) = EQUAL
                                   | NONE =>
                                       not (is_right_bound right environment)
                                       andalso
                                       Term.compare (left, right) = EQUAL)
                                else if Term.is_abs left andalso
                                        Term.is_abs right then
                                  Term.type_of (Term.bvar left) =
                                    Term.type_of (Term.bvar right) andalso
                                  same ((Term.bvar left, Term.bvar right) ::
                                    environment)
                                    (Term.body left) (Term.body right)
                                else false
                              val entries = Array.sub (buckets, bucket)
                              val _ = Array.update (buckets, bucket,
                                (left, right, environment, result) :: entries)
                            in result end
                      end
                in same [] left_root right_root end
              fun dag_equality left_root right_root =
                let
                  val memo = ref
                    ([] : (Term.term * Term.term * Thm.thm) list)
                  fun prove left right =
                    if Portable.pointer_eq (left, right) then Thm.REFL left
                    else
                      case List.find (fn (saved_left, saved_right, _) =>
                          Portable.pointer_eq (saved_left, left) andalso
                          Portable.pointer_eq (saved_right, right)) (!memo) of
                        SOME (_, _, theorem) => theorem
                      | NONE =>
                          let
                            val theorem =
                              if Term.is_comb left andalso
                                 Term.is_comb right then
                                Thm.MK_COMB
                                  (prove (Term.rator left) (Term.rator right),
                                   prove (Term.rand left) (Term.rand right))
                              else if Term.is_abs left andalso
                                      Term.is_abs right then
                                let
                                  val variable = Term.genvar
                                    (Term.type_of (Term.bvar left))
                                  val left_beta = Thm.BETA_CONV
                                    (Term.mk_comb (left, variable))
                                  val right_beta = Thm.BETA_CONV
                                    (Term.mk_comb (right, variable))
                                  val middle = prove
                                    (boolSyntax.rhs (Thm.concl left_beta))
                                    (boolSyntax.rhs (Thm.concl right_beta))
                                  val pointwise = Thm.TRANS left_beta
                                    (Thm.TRANS middle (Thm.SYM right_beta))
                                in Drule.EXT (Thm.GEN variable pointwise) end
                              else if Term.is_const left andalso
                                      Term.is_const right andalso
                                      Term.same_const left right then
                                Thm.ALPHA left right
                              else if Term.is_var left andalso
                                      Term.is_var right andalso
                                      Term.compare (left, right) = EQUAL then
                                Thm.ALPHA left right
                              else raise ERR "resolution"
                                "hashed literals differ structurally"
                            val _ = memo :=
                              (left, right, theorem) :: !memo
                          in theorem end
                in prove left_root right_root end
              datatype clause_path =
                  ClauseLeft of Term.term
                | ClauseRight of Term.term
              val target_paths = ref
                ([] : (int * int * Term.term * clause_path list) list)
              val target_seen = ref ([] : Term.term list)
              fun collect term path =
                if List.exists (fn saved =>
                     Portable.pointer_eq (saved, term)) (!target_seen) then ()
                else
                  (target_seen := term :: !target_seen;
                   case clause_pair term of
                     SOME (left, right) =>
                       (collect left (ClauseLeft right :: path);
                        collect right (ClauseRight left :: path))
                   | NONE => target_paths :=
                       (stop_hash 12 term, exact_hash term, term, path) ::
                       !target_paths)
              val _ = collect target []
              fun lift_path theorem path =
                let
                  fun lift (step, result) =
                    case step of
                      ClauseLeft right => Thm.DISJ1 result right
                    | ClauseRight left => Thm.DISJ2 left result
                in List.foldl lift theorem path end
              fun conjunction_consequence source_theorem destination =
                let
                  val leaves = ref ([] : (int * Term.term * Thm.thm) list)
                  val seen = ref ([] : Term.term list)
                  fun collect_conj theorem =
                    let val term = Thm.concl theorem in
                      if List.exists (fn saved =>
                           Portable.pointer_eq (saved, term)) (!seen) then ()
                      else
                        (seen := term :: !seen;
                         case Lib.total boolSyntax.dest_conj term of
                           SOME _ =>
                             (collect_conj (Thm.CONJUNCT1 theorem);
                              collect_conj (Thm.CONJUNCT2 theorem))
                         | NONE => leaves :=
                             (exact_hash term, term, theorem) :: !leaves)
                    end
                  val _ = collect_conj source_theorem
                  val derived = ref ([] : (Term.term * Thm.thm) list)
                  fun derive term =
                    case List.find (fn (saved, _) =>
                        Portable.pointer_eq (saved, term)) (!derived) of
                      SOME (_, theorem) => theorem
                    | NONE =>
                        let
                          val theorem =
                            case Lib.total boolSyntax.dest_conj term of
                              SOME (left, right) =>
                                Thm.CONJ (derive left) (derive right)
                            | NONE =>
                                let
                                  val hash = exact_hash term
                                  fun find [] = raise ERR "resolution"
                                        "conjunction has no target leaf"
                                    | find ((saved_hash, saved, theorem) ::
                                        rest) =
                                        if hash <> saved_hash then find rest
                                        else
                                          (Thm.EQ_MP
                                            (dag_equality saved term) theorem
                                           handle Feedback.HOL_ERR _ =>
                                             find rest)
                                in find (!leaves) end
                          val _ = derived := (term, theorem) :: !derived
                        in theorem end
                in derive destination end
              fun introduce theorem =
                let
                  val literal = Thm.concl theorem
                  val hash = stop_hash 12 literal
                  val deep_hash = exact_hash literal
                  fun match [] =
                        raise ERR "resolution"
                          "chain result contains literal outside declared target"
                    | match ((saved_hash, saved_deep_hash, saved, path) ::
                        rest) =
                        if hash <> saved_hash orelse
                           deep_hash <> saved_deep_hash then match rest
                        else
                          (let
                             val anchored =
                               if boolSyntax.is_conj literal andalso
                                  boolSyntax.is_conj saved then
                                 conjunction_consequence theorem saved
                               else Thm.EQ_MP
                                 (dag_equality literal saved) theorem
                           in (anchored, path) end
                           handle Feedback.HOL_ERR _ => match rest)
                  val (theorem, path) = match (!target_paths)
                in lift_path theorem path end
              fun introduce_conjunction theorem =
                let
                  fun search [] = raise ERR "resolution"
                        "conjunction has no target consequence"
                    | search ((_, _, saved, path) :: rest) =
                        if not (boolSyntax.is_conj saved) then search rest
                        else
                          (lift_path
                            (conjunction_consequence theorem saved) path
                           handle Feedback.HOL_ERR _ => search rest)
                in search (!target_paths) end
              val failed_weakening = ref ([] : Term.term list)
              fun weaken theorem =
                let
                  val source = Thm.concl theorem
                  val _ = List.exists (fn failed =>
                      Portable.pointer_eq (failed, source))
                      (!failed_weakening) andalso
                    raise ERR "resolution"
                      "clause literal has no target consequence"
                  val result =
                    (introduce theorem
                     handle Feedback.HOL_ERR _ =>
                       case Lib.total boolSyntax.dest_conj source of
                         SOME _ =>
                           (introduce_conjunction theorem
                            handle Feedback.HOL_ERR _ =>
                              let
                                val left = Thm.CONJUNCT1 theorem
                                val right = Thm.CONJUNCT2 theorem
                              in
                                weaken left
                                handle Feedback.HOL_ERR _ => weaken right
                              end)
                       | NONE => raise ERR "resolution"
                           "atomic clause literal has no target consequence")
                    handle Feedback.HOL_ERR holerr =>
                      (failed_weakening := source :: !failed_weakening;
                       raise Feedback.HOL_ERR holerr)
                in result end
              fun branch theorem =
                case clause_pair (Thm.concl theorem) of
                  SOME (left, right) =>
                    Thm.DISJ_CASES theorem (branch (Thm.ASSUME left))
                      (branch (Thm.ASSUME right))
                | NONE => weaken theorem
            in branch theorem end
          fun contextual_target theorem =
            Tactical.TAC_PROOF ((Thm.hyp theorem, target),
              bossLib.FULL_SIMP_TAC boolSimps.bool_ss [theorem])
          fun schematic_reorder theorem =
            let
              val modulus = 1000003
              fun string_hash string =
                CharVector.foldl
                  (fn (character, hash) =>
                    (hash * 33 + Char.ord character) mod modulus)
                  17 string
              fun shallow_hash 0 term =
                    if Term.is_var term then 3
                    else if Term.is_const term then
                      let val {Thy, Name, ...} = Term.dest_thy_const term
                      in (string_hash Thy + 37 * string_hash Name) mod modulus
                      end
                    else if Term.is_comb term then 5 else 7
                | shallow_hash depth term =
                    if Term.is_comb term then
                      let val (operator, operand) = Term.dest_comb term
                      in (19 * shallow_hash (depth - 1) operator +
                          41 * shallow_hash (depth - 1) operand) mod modulus
                      end
                    else if Term.is_abs term then
                      (43 * shallow_hash (depth - 1)
                        (#2 (Term.dest_abs term))) mod modulus
                    else shallow_hash 0 term
              val atoms = ref
                ([] : (int * Term.term * Term.term) list)
              val substitutions = ref
                ([] : {redex : Term.term, residue : Term.term} list)
              fun atom term =
                let val hash = shallow_hash 8 term in
                case List.find (fn (saved_hash, saved, _) =>
                    hash = saved_hash andalso
                    (Portable.pointer_eq (saved, term) orelse
                     shared_aconv saved term)) (!atoms) of
                  SOME (_, _, variable) => variable
                | NONE =>
                    let
                      val variable = Term.genvar Type.bool
                      val _ = atoms := (hash, term, variable) :: !atoms
                      val _ = substitutions :=
                        {redex = variable, residue = term} :: !substitutions
                    in variable end
                end
              fun abstract clause =
                case clause_pair clause of
                  SOME (left, right) => boolSyntax.mk_disj
                    (abstract left, abstract right)
                | NONE => atom clause
              val source_schema = abstract (Thm.concl theorem)
              val target_schema = abstract target
              datatype schema_path =
                  SchemaLeft of Term.term
                | SchemaRight of Term.term
              val target_paths = ref
                ([] : (Term.term * schema_path list) list)
              val target_seen = ref ([] : Term.term list)
              fun collect_paths term path =
                if List.exists (fn saved =>
                     Portable.pointer_eq (saved, term)) (!target_seen) then ()
                else
                  (target_seen := term :: !target_seen;
                   if Term.is_var term then
                     target_paths := (term, path) :: !target_paths
                   else
                     let val (left, right) = boolSyntax.dest_disj term in
                       collect_paths left (SchemaLeft right :: path);
                       collect_paths right (SchemaRight left :: path)
                     end)
              val _ = collect_paths target_schema []
              fun schema_member theorem _ =
                let
                  val literal = Thm.concl theorem
                  val path =
                    case List.find (fn (saved, _) =>
                        Portable.pointer_eq (saved, literal))
                        (!target_paths) of
                      SOME (_, path) => path
                    | NONE => raise ERR "resolution"
                        "schema literal absent"
                  fun lift (step, result) =
                    case step of
                      SchemaLeft right => Thm.DISJ1 result right
                    | SchemaRight left => Thm.DISJ2 left result
                in List.foldl lift theorem path end
              val circuit_memo = ref
                ([] : (Term.term * Term.term) list)
              val circuit_substitutions = ref
                ([] : {redex : Term.term, residue : Term.term} list)
              val circuit_definitions = ref
                ([] : (Term.term * Term.term) list)
              fun circuit term =
                if Term.is_var term then term
                else
                  case List.find (fn (saved, _) =>
                      Portable.pointer_eq (saved, term)) (!circuit_memo) of
                    SOME (_, variable) => variable
                  | NONE =>
                      let
                        val (left, right) = boolSyntax.dest_disj term
                        val skeleton = boolSyntax.mk_disj
                          (circuit left, circuit right)
                        val variable = Term.genvar Type.bool
                        val definition = boolSyntax.mk_eq
                          (variable, skeleton)
                        val _ = circuit_memo :=
                          (term, variable) :: !circuit_memo
                        val _ = circuit_substitutions :=
                          {redex = variable, residue = term} ::
                          !circuit_substitutions
                        val _ = circuit_definitions :=
                          (term, definition) :: !circuit_definitions
                      in variable end
              val source_root = circuit source_schema
              val target_root = circuit target_schema
              val definitions = List.rev (!circuit_definitions)
              val circuit_goal = List.foldr
                (fn ((_, definition), body) =>
                  boolSyntax.mk_imp (definition, body))
                (boolSyntax.mk_imp (source_root, target_root)) definitions
              val schema_memo = ref
                ([] : (Term.term * Thm.thm) list)
              fun schema_lemma source =
                case List.find (fn (saved, _) =>
                    Portable.pointer_eq (saved, source)) (!schema_memo) of
                  SOME (_, saved_theorem) => saved_theorem
                | NONE =>
                    let
                      val result =
                        if Term.is_var source then
                          Thm.DISCH source
                            (schema_member (Thm.ASSUME source) target_schema)
                        else
                          let
                            val (left, right) = boolSyntax.dest_disj source
                            val left_result = Thm.MP (schema_lemma left)
                              (Thm.ASSUME left)
                            val right_result = Thm.MP (schema_lemma right)
                              (Thm.ASSUME right)
                          in Thm.DISCH source
                            (Thm.DISJ_CASES (Thm.ASSUME source)
                              left_result right_result)
                          end
                      val _ = schema_memo :=
                        (source, result) :: !schema_memo
                    in result end
              val law = schema_lemma source_schema
              val instantiated = Thm.INST (!substitutions) law
            in Thm.MP instantiated theorem end
          fun semantic_taut_reorder theorem =
            let
              fun is_xor term =
                let
                  val (head, arguments) = boolSyntax.strip_comb term
                  val {Thy, Name, ...} = Term.dest_thy_const head
                in Thy = "HolSmt" andalso Name = "xor" andalso
                   List.length arguments = 2 end
                handle Feedback.HOL_ERR _ => false
              val one_bit_laws = ref
                ([] : (Type.hol_type * bool * Term.term * Thm.thm) list)
              fun one_bit_conversion atom =
                let
                  val word = one_bit_equality atom
                  val (left, _) = boolSyntax.dest_eq atom
                  val left_word = shared_aconv left word
                  val word_type = Term.type_of word
                  fun same (saved_type, saved_left, _, _) =
                    Type.compare (saved_type, word_type) = EQUAL andalso
                    saved_left = left_word
                in
                  case List.find same (!one_bit_laws) of
                    SOME (_, _, saved_word, law) =>
                      Thm.INST [{redex = saved_word, residue = word}] law
                  | NONE =>
                      let
                        val bit = wordsSyntax.mk_word_bit
                          (numSyntax.zero_tm, word)
                        val law = Drule.EQT_ELIM (wordsLib.WORD_DECIDE
                          (boolSyntax.mk_eq (atom, bit)))
                        val _ = one_bit_laws :=
                          (word_type, left_word, word, law) :: !one_bit_laws
                      in law end
                end
              val conversion_memo = ref
                ([] : (Term.term * Thm.thm) list)
              fun expand term =
                case List.find (fn (saved, _) =>
                    Portable.pointer_eq (saved, term)) (!conversion_memo) of
                  SOME (_, theorem) => theorem
                | NONE =>
                    let
                      val congruence =
                        if Term.is_comb term then
                          let
                            val (operator, operand) = Term.dest_comb term
                          in Thm.MK_COMB (expand operator, expand operand) end
                        else Thm.REFL term
                      val residue = boolSyntax.rhs (Thm.concl congruence)
                      val local_conversion =
                        if is_xor residue then
                          Conv.REWR_CONV HolSmtTheory.xor_def residue
                        else
                          (one_bit_conversion residue
                           handle Feedback.HOL_ERR holerr =>
                             if SmtResource.is_resource_gate holerr then
                               raise Feedback.HOL_ERR holerr
                             else if word_bridge_literal residue then
                               normalize_literal residue
                             else Thm.REFL residue
                                | Conv.UNCHANGED =>
                                    if word_bridge_literal residue then
                                      normalize_literal residue
                                    else Thm.REFL residue)
                      val result = Thm.TRANS congruence local_conversion
                      val _ = conversion_memo :=
                        (term, result) :: !conversion_memo
                    in result end
              val source = Thm.concl theorem
              val source_conversion = expand source
              val target_conversion = expand target
              val source_expanded = boolSyntax.rhs
                (Thm.concl source_conversion)
              val target_expanded = boolSyntax.rhs
                (Thm.concl target_conversion)
              val abstraction_memo = ref
                ([] : (Term.term * Term.term) list)
              val leaves = ref ([] : (Term.term * Term.term) list)
              val substitutions = ref
                ([] : {redex : Term.term, residue : Term.term} list)
              fun bool_structure term =
                boolSyntax.is_neg term orelse boolSyntax.is_conj term orelse
                boolSyntax.is_disj term orelse boolSyntax.is_imp term orelse
                (boolSyntax.is_eq term andalso
                 Term.type_of (#1 (boolSyntax.dest_eq term)) = Type.bool) orelse
                (boolSyntax.is_cond term andalso
                 Term.type_of (#2 (boolSyntax.dest_cond term)) = Type.bool)
              fun leaf term =
                let
                  val canonical = CPC_ProofParser.intern_cpc_term term
                in
                  case List.find (fn (saved, _) =>
                      Portable.pointer_eq (saved, canonical)) (!leaves) of
                    SOME (_, result) => result
                  | NONE =>
                      let
                        val result = Term.genvar Type.bool
                        val _ = leaves := (canonical, result) :: !leaves
                        val _ = substitutions :=
                          {redex = result, residue = canonical} ::
                          !substitutions
                      in result end
                end
              fun abstract term =
                case List.find (fn (saved, _) =>
                    Portable.pointer_eq (saved, term)) (!abstraction_memo) of
                  SOME (_, result) => result
                | NONE =>
                    let
                      val result =
                        if Term.aconv term boolSyntax.T orelse
                           Term.aconv term boolSyntax.F then term
                        else if Term.type_of term = Type.bool andalso
                           not (bool_structure term) then leaf term
                        else if Term.is_comb term then
                          let val (operator, operand) = Term.dest_comb term
                          in Term.mk_comb
                            (abstract operator, abstract operand) end
                        else term
                      val _ = abstraction_memo :=
                        (term, result) :: !abstraction_memo
                    in result end
              val template = boolSyntax.mk_imp
                (abstract source_expanded, abstract target_expanded)
              val leaf_count = List.length (!leaves)
              val _ = leaf_count <= 25 orelse raise ERR "resolution"
                "direct Boolean SAT alignment has too many leaves"
              val proposition = Term.genvar Type.bool
              val semantic_rules = List.map tautLib.TAUT_PROVE
                [boolSyntax.mk_eq
                   (boolSyntax.mk_eq (proposition, proposition),
                    boolSyntax.T),
                 boolSyntax.mk_eq
                   (boolSyntax.mk_conj (proposition, proposition),
                    proposition),
                 boolSyntax.mk_eq
                   (boolSyntax.mk_disj (proposition, proposition),
                    proposition),
                 boolSyntax.mk_eq
                   (boolSyntax.mk_conj
                      (proposition, boolSyntax.mk_neg proposition),
                    boolSyntax.F),
                 boolSyntax.mk_eq
                   (boolSyntax.mk_conj
                      (boolSyntax.mk_neg proposition, proposition),
                    boolSyntax.F),
                 boolSyntax.mk_eq
                   (boolSyntax.mk_disj
                      (proposition, boolSyntax.mk_neg proposition),
                    boolSyntax.T),
                 boolSyntax.mk_eq
                   (boolSyntax.mk_disj
                      (boolSyntax.mk_neg proposition, proposition),
                    boolSyntax.T),
                 boolSyntax.mk_eq
                   (boolSyntax.mk_neg (boolSyntax.mk_neg proposition),
                    proposition)]
              val boolean_values =
                [(boolSyntax.T, true), (boolSyntax.F, false)]
              fun truth_term true = boolSyntax.T
                | truth_term false = boolSyntax.F
              fun binary_rules constructor operation =
                List.concat (List.map (fn (left, left_value) =>
                  List.map (fn (right, right_value) =>
                    tautLib.TAUT_PROVE (boolSyntax.mk_eq
                      (constructor (left, right),
                       truth_term (operation (left_value, right_value)))))
                    boolean_values) boolean_values)
              val ground_rules =
                [tautLib.TAUT_PROVE (boolSyntax.mk_eq
                   (boolSyntax.mk_neg boolSyntax.T, boolSyntax.F)),
                 tautLib.TAUT_PROVE (boolSyntax.mk_eq
                   (boolSyntax.mk_neg boolSyntax.F, boolSyntax.T))] @
                binary_rules boolSyntax.mk_conj
                  (fn (left, right) => left andalso right) @
                binary_rules boolSyntax.mk_disj
                  (fn (left, right) => left orelse right) @
                binary_rules boolSyntax.mk_imp
                  (fn (left, right) => not left orelse right) @
                binary_rules boolSyntax.mk_eq (op =)
              val local_rules = semantic_rules @ ground_rules @ List.filter
                (boolSyntax.is_eq o Thm.concl)
                (List.concat (List.map Drule.CONJUNCTS
                  [boolTheory.AND_CLAUSES, boolTheory.OR_CLAUSES,
                   boolTheory.NOT_CLAUSES, boolTheory.EQ_CLAUSES,
                   boolTheory.IMP_CLAUSES, boolTheory.COND_CLAUSES]))
              fun safe_rewrite theorem term =
                Conv.REWR_CONV theorem term
                handle Feedback.HOL_ERR _ => raise Conv.UNCHANGED
              fun root_reduce 0 term = Thm.REFL term
                | root_reduce count term =
                    let
                      val step = Conv.FIRST_CONV
                        (List.map safe_rewrite local_rules) term
                      val residue = boolSyntax.rhs (Thm.concl step)
                    in Thm.TRANS step
                      (root_reduce (count - 1) residue) end
                    handle Conv.UNCHANGED => Thm.REFL term
              val simplification_memo = ref
                ([] : (Term.term * Thm.thm) list)
              fun simplify term =
                case List.find (fn (saved, _) =>
                    Portable.pointer_eq (saved, term))
                    (!simplification_memo) of
                  SOME (_, theorem) => theorem
                | NONE =>
                    let
                      val congruence =
                        if Term.is_comb term then
                          let
                            val (operator, operand) = Term.dest_comb term
                          in Thm.MK_COMB
                            (simplify operator, simplify operand) end
                        else Thm.REFL term
                      val residue = boolSyntax.rhs (Thm.concl congruence)
                      val result = Thm.TRANS congruence
                        (root_reduce 20 residue)
                      val _ = simplification_memo :=
                        (term, result) :: !simplification_memo
                    in result end
              val simplified = simplify template
              val residue = boolSyntax.rhs (Thm.concl simplified)
              val variables = List.map #2 (!leaves)
              fun evaluate assignments root =
                let
                  val memo = ref ([] : (Term.term * Thm.thm) list)
                  fun visit term =
                    case List.find (fn (saved, _) =>
                        Portable.pointer_eq (saved, term)) (!memo) of
                      SOME (_, theorem) => theorem
                    | NONE =>
                        let
                          val result =
                            case List.find (fn (variable, _) =>
                                Portable.pointer_eq (variable, term))
                                assignments of
                              SOME (_, theorem) => theorem
                            | NONE =>
                                let
                                  val congruence =
                                    if Term.is_comb term then
                                      let
                                        val (operator, operand) =
                                          Term.dest_comb term
                                      in Thm.MK_COMB
                                        (visit operator, visit operand) end
                                    else Thm.REFL term
                                  val current = boolSyntax.rhs
                                    (Thm.concl congruence)
                                  val reduced = bossLib.SIMP_CONV
                                    (bossLib.srw_ss ()) [] current
                                    handle Conv.UNCHANGED =>
                                      Thm.REFL current
                                in Thm.TRANS congruence reduced end
                          val _ = memo := (term, result) :: !memo
                        in result end
                in visit root end
              fun truth_table [] assignments =
                    let
                      val evaluation = evaluate assignments residue
                      val evaluated = boolSyntax.rhs
                        (Thm.concl evaluation)
                      val _ = Term.aconv evaluated boolSyntax.T orelse
                        raise ERR "resolution"
                          "truth-table branch is false"
                    in Drule.EQT_ELIM evaluation end
                | truth_table (variable :: rest) assignments =
                    let
                      val true_case = boolSyntax.mk_eq
                        (variable, boolSyntax.T)
                      val false_case = boolSyntax.mk_eq
                        (variable, boolSyntax.F)
                      val true_theorem = truth_table rest
                        ((variable, Thm.ASSUME true_case) :: assignments)
                      val false_theorem = truth_table rest
                        ((variable, Thm.ASSUME false_case) :: assignments)
                    in Thm.DISJ_CASES
                      (Drule.ISPEC variable boolTheory.BOOL_CASES_AX)
                      true_theorem false_theorem end
              (* Use the checked SAT replay for nontrivial Boolean DAGs.
                 Enumerating all valuations is complete but exponential and
                 made medium-sized resolution alignments impractical. *)
              val truth_theorem =
                HolSatLib.SAT_PROVE residue
                handle HolSatLib.SAT_cex _ => raise ERR "resolution"
                  "abstract Boolean implication is not valid"
              val abstract_law = Thm.EQ_MP (Thm.SYM simplified)
                truth_theorem
              val law = Thm.INST (!substitutions) abstract_law
              fun align left right =
                Thm.TRANS (canonical_term_conv left)
                  (Thm.SYM (canonical_term_conv right))
              val (law_source, law_target) =
                boolSyntax.dest_imp (Thm.concl law)
              val source_theorem = Thm.EQ_MP
                (align source law_source) theorem
              val expanded_result = Thm.MP law source_theorem
              val target_alignment = Thm.TRANS
                (align law_target target_expanded)
                (Thm.SYM target_conversion)
            in Thm.EQ_MP target_alignment expanded_result end
          val previous_tseitin = ref
            (NONE : (Term.term * Term.term) option)
          val tseitin_attempts = SmtReplayAttempt.new
            {enabled = not (Library.no_fastpath ()), capacity = 16,
             hash = SmtBooleanGraph.hash 4}
          fun semantic_tseitin_with procedure destination theorem =
            let
              val source = Thm.concl theorem
              val _ = if not (!resolution_profile_enabled) then ()
                else
                  let val source = Thm.concl theorem in
                    resolution_count "tseitin/attempts" 1;
                    (case !previous_tseitin of
                       SOME (prior_source, prior_target) =>
                         if Portable.pointer_eq (source, prior_source) andalso
                            Portable.pointer_eq (destination, prior_target)
                         then resolution_count
                           "tseitin/consecutive-duplicates" 1 else ()
                     | NONE => ());
                    previous_tseitin := SOME (source, destination)
                  end
              val prior = #statistics tseitin_attempts ()
              val result = Exn.capture (#run tseitin_attempts)
                {procedure = procedure, source = source, target = destination,
                 prove = fn () => semantic_tseitin_law source destination}
              val current = #statistics tseitin_attempts ()
              val _ = resolution_count "tseitin/cache-hits"
                (#hits current - #hits prior)
              val _ = resolution_count "tseitin/cache-misses"
                (#misses current - #misses prior)
              val law = Exn.release result
                handle HolSatLib.SAT_satisfiable _ =>
                  raise ERR "resolution"
                    "abstract Boolean implication is not valid"
            in resolution_profile "tseitin/apply" (Thm.MP law) theorem end
          val semantic_tseitin_atom = semantic_tseitin_with "raw"
          fun semantic_word_tseitin destination theorem =
            let
              val memo = ref ([] : (Term.term * Thm.thm) list)
              fun convert term =
                case List.find (fn (saved, _) =>
                    Portable.pointer_eq (saved, term)) (!memo) of
                  SOME (_, result) => result
                | NONE =>
                    let
                      val congruence =
                        if Term.is_comb term then
                          Thm.MK_COMB
                            (convert (Term.rator term),
                             convert (Term.rand term))
                        else Thm.REFL term
                      val residue = boolSyntax.rhs
                        (Thm.concl congruence)
                      val local_conversion =
                        if word_bridge_literal residue then
                          (SmtWordGraph.normalize residue
                           handle Conv.UNCHANGED => Thm.REFL residue)
                        else Thm.REFL residue
                      val result = Thm.TRANS congruence local_conversion
                      val _ = memo := (term, result) :: !memo
                    in result end
              val source_conversion = convert (Thm.concl theorem)
              val target_conversion = convert destination
              val source_normalized = boolSyntax.rhs
                (Thm.concl source_conversion)
              val target_normalized = boolSyntax.rhs
                (Thm.concl target_conversion)
              val source_theorem = Thm.EQ_MP source_conversion theorem
              val result = semantic_tseitin_with "word-normalized" target_normalized
                source_theorem
            in
              Thm.EQ_MP (Thm.SYM target_conversion) result
            end
          fun semantic_direct_atom destination theorem =
            let
              val memo = ref ([] : (Term.term * Term.term) list)
              val leaves = ref ([] : (Term.term * Term.term) list)
              val substitutions = ref
                ([] : {redex : Term.term, residue : Term.term} list)
              fun bool_structure term =
                boolSyntax.is_neg term orelse boolSyntax.is_conj term orelse
                boolSyntax.is_disj term orelse boolSyntax.is_imp term orelse
                (boolSyntax.is_eq term andalso
                 Term.type_of (#1 (boolSyntax.dest_eq term)) = Type.bool) orelse
                (boolSyntax.is_cond term andalso
                 Term.type_of (#2 (boolSyntax.dest_cond term)) = Type.bool)
              fun leaf term =
                let
                  val canonical = CPC_ProofParser.intern_cpc_term term
                in
                  case List.find (fn (saved, _) =>
                      Portable.pointer_eq (saved, canonical)) (!leaves) of
                    SOME (_, variable) => variable
                  | NONE =>
                      let
                        val variable = Term.genvar Type.bool
                        val _ = leaves := (canonical, variable) :: !leaves
                        val _ = substitutions :=
                          {redex = variable, residue = canonical} ::
                          !substitutions
                      in variable end
                end
              fun abstract term =
                case List.find (fn (saved, _) =>
                    Portable.pointer_eq (saved, term)) (!memo) of
                  SOME (_, result) => result
                | NONE =>
                    let
                      val result =
                        if Term.aconv term boolSyntax.T orelse
                           Term.aconv term boolSyntax.F then term
                        else if Term.type_of term = Type.bool andalso
                                not (bool_structure term) then leaf term
                        else if Term.is_comb term then
                          Term.mk_comb
                            (abstract (Term.rator term),
                             abstract (Term.rand term))
                        else term
                      val _ = memo := (term, result) :: !memo
                    in result end
              val source = Thm.concl theorem
              val template = boolSyntax.mk_imp
                (abstract source, abstract destination)
              val leaf_count = List.length (!leaves)
              val _ = leaf_count <= 25 orelse raise ERR "resolution"
                "direct Boolean alignment has too many leaves"
              val law = HolSatLib.SAT_PROVE template
              val law = Thm.INST (!substitutions) law
              val align = Thm.ALPHA
              val (law_source, law_target) =
                boolSyntax.dest_imp (Thm.concl law)
              val source_theorem = Thm.EQ_MP
                (align source law_source) theorem
              val result = Thm.MP law source_theorem
              val result = Thm.EQ_MP
                (align law_target destination) result
            in result end
          fun semantic_circuit_atom destination theorem =
            semantic_tseitin_atom destination theorem
          fun semantic_circuit_reorder theorem =
            let
              val target_literals = ref ([] : Term.term list)
              val target_seen = ref ([] : Term.term list)
              fun collect_target term =
                if List.exists (fn saved =>
                     Portable.pointer_eq (saved, term)) (!target_seen) then ()
                else
                  (target_seen := term :: !target_seen;
                   case clause_pair term of
                     SOME (left, right) =>
                       (collect_target left; collect_target right)
                   | NONE => target_literals := term :: !target_literals)
              val _ = collect_target target
              val literals = !target_literals
              fun pairs [] = []
                | pairs (first :: rest) =
                    List.map (fn second =>
                      boolSyntax.mk_disj (first, second)) rest @ pairs rest
              fun triples [] = []
                | triples (first :: rest) =
                    List.map (fn pair =>
                      boolSyntax.mk_disj (first, pair)) (pairs rest) @
                    triples rest
              val destinations =
                target :: (literals @ pairs literals @ triples literals)
              fun prove_atom theorem =
                (semantic_taut_reorder theorem
                 handle Feedback.HOL_ERR holerr =>
                   if SmtResource.is_resource_gate holerr then
                     raise Feedback.HOL_ERR holerr
                   else
                let
                  fun try [] = raise ERR "resolution"
                        "no semantic target clause follows"
                    | try (destination :: rest) =
                        (reorder_to_target
                          (semantic_circuit_atom destination theorem)
                         handle HolSatLib.SAT_cex _ => try rest
                              | Feedback.HOL_ERR holerr =>
                                  if SmtResource.is_resource_gate holerr then
                                    raise Feedback.HOL_ERR holerr
                                  else try rest)
                in try destinations end)
              fun prove theorem =
                case clause_pair (Thm.concl theorem) of
                  SOME (left, right) =>
                    Thm.DISJ_CASES theorem
                      (prove (Thm.ASSUME left))
                      (prove (Thm.ASSUME right))
                | NONE =>
                    (reorder_to_target theorem
                     handle Feedback.HOL_ERR _ => prove_atom theorem)
            in
              semantic_circuit_atom target theorem
              handle HolSatLib.SAT_cex _ => prove theorem
                   | Feedback.HOL_ERR holerr =>
                       if SmtResource.is_resource_gate holerr then
                         raise Feedback.HOL_ERR holerr
                       else prove theorem
            end
          fun strip_chain_clause term =
            if is_chain_stop term then [term]
            else
              (case Lib.total boolSyntax.dest_disj term of
                 SOME (left, right) =>
                   strip_chain_clause left @ strip_chain_clause right
               | NONE => [term])
          fun sat_chain_consequence () =
            let
              val atoms = ref ([] : (Term.term * Term.term) list)
              fun is_stop term = List.exists
                (fn stop => shared_aconv stop term) chain_stops
              fun atom term =
                case List.find (fn (saved, _) =>
                    Portable.pointer_eq (saved, term) orelse
                    shared_aconv saved term) (!atoms) of
                  SOME (_, variable) => variable
                | NONE =>
                    let
                      val variable = Term.genvar Type.bool
                      val _ = atoms := (term, variable) :: !atoms
                    in variable end
              fun abstract_literal term =
                if Term.aconv term boolSyntax.T orelse
                   Term.aconv term boolSyntax.F then term
                else
                  case Lib.total boolSyntax.dest_neg term of
                    SOME body => boolSyntax.mk_neg (atom body)
                  | NONE => atom term
              fun abstract_clause term =
                if is_stop term then abstract_literal term
                else
                  case Lib.total boolSyntax.dest_disj term of
                    SOME (left, right) => boolSyntax.mk_disj
                      (abstract_literal left, abstract_clause right)
                  | NONE => abstract_literal term
              val abstract_prems = List.map
                (abstract_clause o Thm.concl) prems
              val abstract_target = abstract_clause target
              fun contains literal clause =
                Term.aconv literal clause orelse
                case Lib.total boolSyntax.dest_disj clause of
                  SOME (left, right) =>
                    Term.aconv literal left orelse contains literal right
                | NONE => false
              fun selected_pivot accumulated next polarity pivot =
                let
                  val annotated = abstract_literal
                    (signed_pivot polarity pivot)
                  fun usable candidate =
                    contains candidate (Thm.concl accumulated) andalso
                    contains (complement candidate) (Thm.concl next)
                in
                  if usable annotated then SOME annotated
                  else if usable (complement annotated) then
                    SOME (complement annotated)
                  else NONE
                end
              fun clause_literals clause =
                case Lib.total boolSyntax.dest_disj clause of
                  SOME (left, right) => left :: clause_literals right
                | NONE => [clause]
              fun unique_clause_literals literals =
                List.rev (List.foldl (fn (literal, kept) =>
                  if List.exists (Term.aconv literal) kept then kept
                  else literal :: kept) [] literals)
              fun same_clause left right =
                let
                  val left_literals = unique_clause_literals
                    (clause_literals (Thm.concl left))
                  val right_literals = unique_clause_literals
                    (clause_literals (Thm.concl right))
                in
                  List.length left_literals = List.length right_literals andalso
                  List.all (fn literal =>
                    List.exists (Term.aconv literal) right_literals)
                    left_literals
                end
              fun deduplicate states = List.foldl
                (fn (theorem, kept) =>
                  if List.exists (same_clause theorem) kept then kept
                  else theorem :: kept) [] states
              fun advance next polarity pivot accumulated =
                case selected_pivot accumulated next polarity pivot of
                  SOME selected =>
                    [resolve_pair_on [] selected accumulated next]
                | NONE => [accumulated, next]
              val abstract_theorems = List.map Thm.ASSUME abstract_prems
              val states =
                case abstract_theorems of
                  first :: rest => List.foldl
                    (fn ((next, (polarity, pivot)), current) =>
                      deduplicate (List.concat (List.map
                        (advance next polarity pivot) current)))
                    [first]
                    (ListPair.zip
                      (rest, ListPair.zip (polarities, pivots)))
                | [] => raise ERR "resolution" "empty abstract chain"
              fun align_state [] = raise ERR "resolution"
                    "no abstract chain branch implies the target"
                | align_state (theorem :: rest) =
                    let
                      val goal = boolSyntax.mk_imp
                        (Thm.concl theorem, abstract_target)
                    in Thm.MP (HolSatLib.SAT_PROVE goal) theorem end
                    handle HolSatLib.SAT_cex _ => align_state rest
              val aligned = align_state states
              val law = List.foldr
                (fn (premise, theorem) => Thm.DISCH premise theorem)
                aligned abstract_prems
              val law = Thm.INST (List.map
                (fn (term, variable) =>
                  {redex = variable, residue = term}) (!atoms)) law
              val result = List.foldl
                (fn (premise, theorem) => Thm.MP theorem premise)
                law prems
            in result end
          val unused_prems = ref ([] : Thm.thm list)
          val unused_annotations = ref
            ([] : (Thm.thm * Term.term) list)
          fun annotated_chain_using premises destination pivot_terms
              strict_resolver resolver record_unused () =
            let
              val annotation_index = ref 0
              fun hashed stop = (literal_hash 6 stop, stop)
              val target_clause_stops = List.map hashed
                (List.filter boolSyntax.is_disj (strip_clause destination))
              val remaining_pivot_stops = ref
                (List.map hashed (List.filter boolSyntax.is_disj
                  (pivot_terms @ List.map complement pivot_terms)))
              fun retire_stop stop =
                if not (boolSyntax.is_disj stop) then ()
                else
                  case remove_first_using
                      (fn sought => fn (_, candidate) =>
                        structural_literal_equal sought candidate)
                      stop (!remaining_pivot_stops) of
                    SOME remaining => remaining_pivot_stops := remaining
                  | NONE => ()
              fun describe_literal term =
                let
                  val base = case Lib.total boolSyntax.dest_neg term of
                      SOME body => body
                    | NONE => term
                  val (head, arguments) = boolSyntax.strip_comb base
                  val name =
                    (let val {Thy, Name, ...} = Term.dest_thy_const head
                     in Thy ^ "$" ^ Name end)
                    handle Feedback.HOL_ERR _ =>
                      if Term.is_var head then "variable" else "compound"
                in name ^ "/" ^ Int.toString (List.length arguments) end
            in case premises of
              first :: rest => List.foldl
                (fn ((next, (polarity, pivot)), accumulated) =>
                  let
                    val _ = annotation_index := !annotation_index + 1
                    val _ = if OS.Process.getEnv
                        "HOL4_CPC_REPLAY_TRACE" = SOME "full" andalso
                        !annotation_index mod 16 = 0 then
                      (Feedback.HOL_MESG
                        ("CPC chain annotated pivot " ^
                         Int.toString (!annotation_index) ^ "/" ^
                         Int.toString (List.length rest));
                       TextIO.flushOut TextIO.stdOut)
                    else ()
                    val _ = if OS.Process.getEnv
                        "HOL4_CPC_REPLAY_TRACE" = SOME "full" andalso
                        List.length premises >= 128 andalso
                        List.length premises < 256 andalso
                        !annotation_index >= 160 then
                      (Feedback.HOL_MESG
                        ("CPC chain annotated detail " ^
                         Int.toString (!annotation_index) ^
                         " accumulated=" ^
                         Int.toString (List.length
                           (strip_clause (Thm.concl accumulated))) ^
                         " next=" ^
                         Int.toString (List.length
                           (strip_clause (Thm.concl next))));
                       TextIO.flushOut TextIO.stdOut)
                    else ()
                    val annotated = signed_pivot polarity pivot
                    val active_stops =
                      target_clause_stops @ !remaining_pivot_stops
                    fun strict candidate =
                      SOME (candidate, strict_resolver active_stops candidate
                        accumulated next)
                      handle Feedback.HOL_ERR holerr =>
                        if SmtResource.is_resource_gate holerr then
                          raise Feedback.HOL_ERR holerr
                        else NONE
                    val strict_result =
                      case strict annotated of
                        SOME result => SOME result
                      | NONE => strict (complement annotated)
                    val _ = if OS.Process.getEnv
                        "HOL4_CPC_REPLAY_TRACE" = SOME "full" andalso
                        List.length premises >= 128 andalso
                        List.length premises < 256 andalso
                        !annotation_index >= 160 then
                      (Feedback.HOL_MESG
                        ("CPC chain annotated strict " ^
                         Int.toString (!annotation_index) ^ " " ^
                         Bool.toString (Option.isSome strict_result));
                       TextIO.flushOut TextIO.stdOut)
                    else ()
                    val (selected, resolved, used) =
                      case strict_result of
                        SOME (selected, resolved) =>
                          (selected, resolved, true)
                      | NONE =>
                          (annotated, resolver (List.map #2 active_stops)
                            annotated accumulated next, false)
                    val _ = if not used andalso record_unused then
                        (unused_prems := next :: !unused_prems;
                         unused_annotations :=
                           (next, selected) :: !unused_annotations)
                      else ()
                    val _ = retire_stop pivot
                    val _ = retire_stop (complement pivot)
                    val _ = if OS.Process.getEnv
                        "HOL4_CPC_REPLAY_TRACE" = SOME "full" andalso
                        List.length premises >= 128 andalso
                        List.length premises < 256 andalso
                        !annotation_index >= 160 then
                      (Feedback.HOL_MESG
                        ("CPC chain annotated done " ^
                         Int.toString (!annotation_index) ^
                         " result=" ^
                         Int.toString (List.length
                           (strip_clause (Thm.concl resolved))) ^
                         " strict=" ^ Bool.toString used);
                       TextIO.flushOut TextIO.stdOut)
                    else ()
                  in resolved end)
                first (ListPair.zip
                  (rest, ListPair.zip (polarities, pivot_terms)))
            | [] => raise ERR "resolution" "empty resolution chain"
            end
          fun annotated_chain () =
            annotated_chain_using prems target pivots
              resolve_pair_on_structural_strict_hashed
              resolve_pair_on_structural true ()
          fun structural_annotated_chain () =
            annotated_chain_using prems target pivots
              resolve_pair_on_structural_strict_hashed
              resolve_pair_on false ()
          fun abstract_structural_annotated_chain () =
            let
              val bucket_count = 16381
              val atoms = Array.array
                (bucket_count, [] : (int * Term.term * Term.term) list)
              val substitutions = ref
                ([] : {redex : Term.term, residue : Term.term} list)
              fun atom term =
                let
                  val hash = literal_hash 6 term
                  val index = hash mod bucket_count
                in
                  case List.find (fn (saved_hash, saved, _) =>
                      hash = saved_hash andalso
                      structural_literal_equal saved term)
                      (Array.sub (atoms, index)) of
                    SOME (_, _, variable) => variable
                  | NONE =>
                      let
                        val variable = Term.genvar Type.bool
                        val _ = Array.update
                          (atoms, index,
                           (hash, term, variable) ::
                           Array.sub (atoms, index))
                        val _ = substitutions :=
                          {redex = variable, residue = term} ::
                          !substitutions
                      in variable end
                end
              val memo = ref (Redblackmap.mkDict Term.compare :
                (Term.term, Term.term) Redblackmap.dict)
              fun abstract_term term =
                case Redblackmap.peek (!memo, term) of
                  SOME result => result
                | NONE =>
                    let
                      val result =
                        if Term.aconv term boolSyntax.T orelse
                           Term.aconv term boolSyntax.F then term
                        else
                          case Lib.total boolSyntax.dest_disj term of
                            SOME (left, right) => boolSyntax.mk_disj
                              (abstract_term left, abstract_term right)
                          | NONE =>
                              (case Lib.total boolSyntax.dest_neg term of
                                 SOME body =>
                                   boolSyntax.mk_neg (abstract_term body)
                               | NONE => atom term)
                      val _ = memo := Redblackmap.insert
                        (!memo, term, result)
                    in result end
              val abstract_prems = List.map
                (abstract_term o Thm.concl) prems
              val abstract_target = abstract_term target
              val abstract_pivots = List.map abstract_term pivots
              val abstract_result = annotated_chain_using
                (List.map Thm.ASSUME abstract_prems)
                abstract_target abstract_pivots
                resolve_pair_on_structural_strict_hashed
                resolve_pair_on_structural false ()
              val law = List.foldr
                (fn (premise, theorem) => Thm.DISCH premise theorem)
                abstract_result abstract_prems
              val instantiated = Thm.INST (!substitutions) law
            in List.foldl
              (fn (premise, theorem) => Thm.MP theorem premise)
              instantiated prems end
          fun dynamic_schema_consequence () =
            let
              val bucket_count = 16381
              fun bucket hash = hash mod bucket_count
              val atoms = Array.array
                (bucket_count,
                 [] : (int * Term.term * Term.term) list)
              val substitutions = ref
                ([] : {redex : Term.term, residue : Term.term} list)
              fun atom term =
                let val hash = literal_hash 6 term in
                  case List.find (fn (saved_hash, saved, _) =>
                      hash = saved_hash andalso
                      structural_literal_equal saved term)
                      (Array.sub (atoms, bucket hash)) of
                    SOME (_, _, variable) => variable
                  | NONE =>
                      let
                        val variable = Term.genvar Type.bool
                        val index = bucket hash
                        val _ = Array.update
                          (atoms, index,
                           (hash, term, variable) ::
                           Array.sub (atoms, index))
                        val _ = substitutions :=
                          {redex = variable, residue = term} :: !substitutions
                      in variable end
                end
              fun abstract_literal term =
                if Term.aconv term boolSyntax.T orelse
                   Term.aconv term boolSyntax.F then term
                else
                  case Lib.total boolSyntax.dest_neg term of
                    SOME body => boolSyntax.mk_neg (atom body)
                  | NONE => atom term
              val stops = Array.array
                (bucket_count, [] : (int * Term.term) list)
              fun add_stop term =
                let
                  val hash = literal_hash 6 term
                  val index = bucket hash
                in Array.update
                  (stops, index,
                   (hash, term) :: Array.sub (stops, index)) end
              val _ = List.app add_stop
                (List.filter boolSyntax.is_disj
                  (strip_clause target @ pivots @
                   List.map complement pivots))
              fun abstract_clause term =
                let
                  val hash = literal_hash 6 term
                  val stopped = List.exists (fn (saved_hash, stop) =>
                    hash = saved_hash andalso
                    structural_literal_equal term stop)
                    (Array.sub (stops, bucket hash))
                in
                  if stopped then abstract_literal term
                  else
                    case Lib.total boolSyntax.dest_disj term of
                      SOME (left, right) => boolSyntax.mk_disj
                        (abstract_clause left, abstract_clause right)
                    | NONE => abstract_literal term
                end
              val _ = List.null prems andalso
                raise ERR "resolution" "empty resolution chain"
              val abstract_prems = List.map
                (abstract_clause o Thm.concl) prems
              val abstract_target = abstract_clause target
              val goal = List.foldr boolSyntax.mk_imp abstract_target
                abstract_prems
              val law = SmtResource.with_bitblast_step_time
                "cpc-resolution-dynamic-schema" HolSatLib.SAT_PROVE goal
              val instantiated = Thm.INST (!substitutions) law
              val result = List.foldl (fn (premise, theorem) =>
                Thm.MP theorem premise) instantiated prems
            in
              if Portable.pointer_eq (Thm.concl result, target) then result
              else
                let
                  val source_conversion =
                    canonical_term_conv (Thm.concl result)
                  val target_conversion = canonical_term_conv target
                  val source_canonical = boolSyntax.rhs
                    (Thm.concl source_conversion)
                  val target_canonical = boolSyntax.rhs
                    (Thm.concl target_conversion)
                  val _ = Portable.pointer_eq
                      (source_canonical, target_canonical) orelse
                    raise ERR "resolution"
                      "dynamic schema endpoint is not canonical"
                in
                  Thm.EQ_MP (Thm.TRANS source_conversion
                    (Thm.SYM target_conversion)) result
                end
            end
          fun schematic_chain_consequence () =
            let
              val atoms = ref
                ([] : (Term.term * Term.term * Term.term) list)
              val structural_atoms = ref
                (Redblackmap.mkDict Term.compare :
                  (Term.term, Term.term) Redblackmap.dict)
              val normalized_atoms = ref
                (Redblackmap.mkDict Term.compare :
                  (Term.term, Term.term) Redblackmap.dict)
              val substitutions = ref
                ([] : {redex : Term.term, residue : Term.term} list)
              val substitution_map = ref
                (Redblackmap.mkDict Term.compare :
                  (Term.term, Term.term) Redblackmap.dict)
              fun atom term =
                let
                  val canonical = term
                  fun normalized_key () =
                    if word_bridge_literal canonical then
                      SOME (boolSyntax.rhs
                        (Thm.concl (normalize_literal canonical)))
                    else NONE
                  fun remember variable normalized =
                    (structural_atoms := Redblackmap.insert
                       (!structural_atoms, canonical, variable);
                     case normalized of
                       SOME key => normalized_atoms := Redblackmap.insert
                         (!normalized_atoms, key, variable)
                     | NONE => ();
                     variable)
                in
                  case Redblackmap.peek (!structural_atoms, canonical) of
                    SOME variable => variable
                  | NONE =>
                      let val normalized = normalized_key () in
                        case (case normalized of
                                SOME key =>
                                  Redblackmap.peek (!normalized_atoms, key)
                              | NONE => NONE) of
                          SOME variable => remember variable normalized
                        | NONE =>
                            let
                              val variable = Term.genvar Type.bool
                              val _ = atoms :=
                                (canonical, term, variable) :: !atoms
                              val _ = substitutions :=
                                {redex = variable, residue = term} ::
                                !substitutions
                              val _ = substitution_map :=
                                Redblackmap.insert
                                  (!substitution_map, variable, term)
                            in remember variable normalized end
                      end
                end
              fun substitutions_for terms =
                let
                  val variables = List.concat
                    (List.map Term.free_vars terms)
                  val unique = List.foldl
                    (fn (variable, kept) =>
                      if List.exists (Term.aconv variable) kept then kept
                      else variable :: kept) [] variables
                in List.mapPartial (fn variable =>
                  Option.map (fn term =>
                    {redex = variable, residue = term})
                    (Redblackmap.peek (!substitution_map, variable))) unique
                end
              fun align_clause theorem destination =
                let
                  fun branch theorem =
                    case Lib.total boolSyntax.dest_disj
                        (Thm.concl theorem) of
                      SOME (left, right) =>
                        Thm.DISJ_CASES theorem
                          (branch (Thm.ASSUME left))
                          (branch (Thm.ASSUME right))
                    | NONE => prove_member (Thm.concl theorem) destination
                in
                  if Term.aconv (Thm.concl theorem) destination then theorem
                  else branch theorem
                end
              fun abstract_literal literal =
                case Lib.total boolSyntax.dest_neg literal of
                  SOME base => boolSyntax.mk_neg (atom base)
                | NONE => atom literal
              fun abstract_clause term =
                if is_chain_stop term then abstract_literal term
                else
                  case Lib.total boolSyntax.dest_disj term of
                    SOME (left, right) => boolSyntax.mk_disj
                      (abstract_clause left, abstract_clause right)
                  | NONE => abstract_literal term
              val abstracted_premises = List.map
                (abstract_clause o Thm.concl) prems
              val consequent = abstract_clause target
              fun pivot_schema_consequence () =
                let
              val generic_pivots = ListPair.mapEq
                (fn (polarity, pivot) =>
                  abstract_literal (signed_pivot polarity pivot))
                (polarities, pivots)
              val max_pending_duplicates = 32
              fun bounded_factor theorem =
                let
                  val literals = strip_clause (Thm.concl theorem)
                  val unique = List.foldl
                    (fn (literal, kept) =>
                      if List.exists (Term.aconv literal) kept then kept
                      else literal :: kept) [] literals
                in
                  if List.length literals - List.length unique >=
                      max_pending_duplicates then factor theorem
                  else theorem
                end
              fun resolve_step accumulated next pivot =
                let
                  val accumulated_assumption = Thm.ASSUME accumulated
                  val next_assumption = Thm.ASSUME next
                  fun strict candidate =
                    SOME (resolve_pair_on_structural_strict_hashed []
                      candidate accumulated_assumption next_assumption)
                    handle Feedback.HOL_ERR holerr =>
                      if SmtResource.is_resource_gate holerr then
                        raise Feedback.HOL_ERR holerr
                      else NONE
                  val resolved =
                    case strict pivot of
                      SOME theorem => theorem
                    | NONE =>
                        (case strict (complement pivot) of
                           SOME theorem => theorem
                         | NONE => resolve_pair_on_structural [] pivot
                             accumulated_assumption next_assumption)
                in bounded_factor resolved end
              val (resolved, concrete_result) =
                case (abstracted_premises, prems) of
                  (first :: rest, concrete_first :: concrete_rest) =>
                    List.foldl
                      (fn ((next, (concrete_next, pivot)),
                           (accumulated, concrete_accumulated)) =>
                        let
                          val step = resolve_step accumulated next pivot
                          val step_substitutions = substitutions_for
                            [accumulated, next, Thm.concl step]
                          val concrete_step = Thm.INST
                            step_substitutions step
                          fun discharge premise expected theorem =
                            (Drule.PROVE_HYP premise theorem
                             handle Feedback.HOL_ERR _ =>
                               Drule.PROVE_HYP
                                 (align_clause premise expected) theorem)
                          val concrete_step = discharge
                            concrete_accumulated
                            (Term.subst step_substitutions accumulated)
                            concrete_step
                          val concrete_step = discharge concrete_next
                            (Term.subst step_substitutions next)
                            concrete_step
                        in (Thm.concl step, concrete_step) end)
                      (first, concrete_first)
                      (ListPair.zip
                        (rest, ListPair.zip
                          (concrete_rest, generic_pivots)))
                | _ => raise ERR "resolution"
                    "empty schematic resolution chain"
              fun reorder theorem =
                case Lib.total boolSyntax.dest_disj (Thm.concl theorem) of
                  SOME (left, right) =>
                    Thm.DISJ_CASES theorem
                      (reorder (Thm.ASSUME left))
                      (reorder (Thm.ASSUME right))
                | NONE => prove_member (Thm.concl theorem) consequent
              val alignment =
                if shared_aconv resolved consequent then
                  Thm.DISCH resolved (Thm.ASSUME resolved)
                else
                  (let
                     val theorem = reorder (Thm.ASSUME resolved)
                   in Thm.DISCH resolved theorem end
                   handle Feedback.HOL_ERR holerr =>
                     if SmtResource.is_resource_gate holerr then
                       raise Feedback.HOL_ERR holerr
                     else
                       SmtResource.with_bitblast_step_time
                         "cpc-resolution-schematic-alignment"
                         HolSatLib.SAT_PROVE
                         (boolSyntax.mk_imp (resolved, consequent)))
              val alignment_substitutions =
                substitutions_for [resolved, consequent]
              val concrete_alignment = Thm.INST
                alignment_substitutions alignment
              val concrete_antecedent =
                Term.subst alignment_substitutions resolved
              val concrete_result =
                if Term.aconv (Thm.concl concrete_result)
                    concrete_antecedent then concrete_result
                else align_clause concrete_result concrete_antecedent
                in Thm.MP concrete_alignment concrete_result
                end
              fun normalized_schema_consequence () =
                let
                  val goal = List.foldr boolSyntax.mk_imp consequent
                    abstracted_premises
                  val law = HolSatLib.SAT_PROVE goal
                  val instantiated = Thm.INST (!substitutions) law
                  fun apply ((abstracted, premise), theorem) =
                    let
                      val expected = Term.subst (!substitutions) abstracted
                      val premise =
                        if Term.aconv (Thm.concl premise) expected then premise
                        else align_clause premise expected
                    in Thm.MP theorem premise end
                in List.foldl apply instantiated
                  (ListPair.zip (abstracted_premises, prems))
                end
            in
              normalized_schema_consequence ()
              handle HolSatLib.SAT_cex _ => pivot_schema_consequence ()
                   | Feedback.HOL_ERR holerr =>
                  if SmtResource.is_resource_gate holerr then
                    raise Feedback.HOL_ERR holerr
                  else pivot_schema_consequence ()
            end
          fun trace_chain name =
            if OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" = SOME "full"
               orelse
               (OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" = SOME "1"
                andalso List.length prems >= 128)
            then Feedback.HOL_MESG ("CPC chain " ^ name ^ " begin")
            else ()
          (* Reconstruct a long pivot chain in a propositional schema.
             The kernel checks every abstract resolution step, but the
             potentially large concrete FP/word literals are substituted
             only once, after the entire chain has been established. *)
          fun structural_schema_chain_consequence () =
            let
              val bucket_count = 16381
              val atoms = Array.array
                (bucket_count,
                 [] : (int * Term.term * Term.term) list)
              val substitutions = ref
                ([] : {redex : Term.term, residue : Term.term} list)
              fun atom term =
                let
                  val hash = literal_hash 6 term
                  val index = hash mod bucket_count
                in
                  case List.find (fn (saved_hash, saved, _) =>
                      hash = saved_hash andalso
                      structural_literal_equal saved term)
                      (Array.sub (atoms, index)) of
                    SOME (_, _, variable) => variable
                  | NONE =>
                      let
                        val variable = Term.genvar Type.bool
                        val _ = Array.update
                          (atoms, index,
                           (hash, term, variable) ::
                           Array.sub (atoms, index))
                        val _ = substitutions :=
                          {redex = variable, residue = term} ::
                          !substitutions
                      in variable end
                end
              fun abstract_literal term =
                if Term.aconv term boolSyntax.T orelse
                   Term.aconv term boolSyntax.F then term
                else
                  case Lib.total boolSyntax.dest_neg term of
                    SOME body => boolSyntax.mk_neg (atom body)
                  | NONE => atom term
              fun abstract_clause term =
                if is_chain_stop term then abstract_literal term
                else
                  case Lib.total boolSyntax.dest_disj term of
                    SOME (left, right) => boolSyntax.mk_disj
                      (abstract_clause left, abstract_clause right)
                  | NONE => abstract_literal term
              val abstract_prems = List.map
                (abstract_clause o Thm.concl) prems
              val abstract_pivots = ListPair.mapEq
                (fn (polarity, pivot) =>
                  abstract_literal (signed_pivot polarity pivot))
                (polarities, pivots)
              fun refutation_resolved () =
                let
                  fun clause_literals term =
                    case Lib.total boolSyntax.dest_disj term of
                      SOME (left, right) =>
                        clause_literals left @ clause_literals right
                    | NONE =>
                        if Term.aconv term boolSyntax.F then []
                        else [term]
                  fun refute_literal literal =
                    if Term.aconv literal boolSyntax.F then
                      Thm.ASSUME boolSyntax.F
                    else
                      case Lib.total boolSyntax.dest_neg literal of
                        SOME _ => Thm.MP (Thm.ASSUME literal)
                          (Thm.ASSUME (complement literal))
                      | NONE => Thm.MP
                          (Thm.ASSUME (complement literal))
                          (Thm.ASSUME literal)
                  fun refute_clause clause =
                    case Lib.total boolSyntax.dest_disj clause of
                      SOME (left, right) =>
                        Thm.DISJ_CASES (Thm.ASSUME clause)
                          (refute_clause left) (refute_clause right)
                    | NONE => refute_literal clause
                  fun contains literal literals =
                    List.exists (structural_literal_equal literal) literals
                  fun without literal literals =
                    List.filter
                      (fn candidate =>
                        not (structural_literal_equal literal candidate))
                      literals
                  fun unique literals =
                    let
                      val buckets = ref (Redblackmap.mkDict Int.compare)
                      fun keep (literal, kept) =
                        let
                          val hash = literal_hash 6 literal
                          val bucket =
                            case Redblackmap.peek (!buckets, hash) of
                              SOME saved => saved
                            | NONE => []
                        in
                          if List.exists
                              (structural_literal_equal literal) bucket then
                            kept
                          else
                            (buckets := Redblackmap.insert
                              (!buckets, hash, literal :: bucket);
                             literal :: kept)
                        end
                    in List.rev (List.foldl keep [] literals) end
                  fun advance ((next_literals, next_refutation), pivot)
                      (literals, refutation) =
                    let
                      val selected =
                        if contains pivot literals andalso
                           contains (complement pivot) next_literals then
                          SOME pivot
                        else if contains (complement pivot) literals andalso
                                contains pivot next_literals then
                          SOME (complement pivot)
                        else NONE
                    in
                      case selected of
                        SOME chosen =>
                          let
                            val opposite = complement chosen
                            val survivors = unique
                              (without chosen literals @
                               without opposite next_literals)
                            val contradiction =
                              case Lib.total boolSyntax.dest_neg chosen of
                                SOME atom => Thm.DISJ_CASES
                                  (Thm.SPEC atom
                                    boolTheory.EXCLUDED_MIDDLE)
                                  refutation next_refutation
                              | NONE => Thm.DISJ_CASES
                                  (Thm.SPEC chosen
                                    boolTheory.EXCLUDED_MIDDLE)
                                  next_refutation refutation
                          in (survivors, contradiction) end
                      | NONE =>
                          let
                            val opposite = complement pivot
                            val first_present = contains pivot literals
                            val second_present =
                              contains opposite next_literals
                            val survivors = unique
                              ((if first_present then
                                  without pivot literals else literals) @
                               (if second_present then
                                  without opposite next_literals
                                else next_literals))
                          in
                            (survivors,
                             if first_present then next_refutation
                             else refutation)
                          end
                    end
                  val states = List.map
                    (fn clause =>
                      (clause_literals clause, refute_clause clause))
                    abstract_prems
                  val (literals, contradiction) =
                    case states of
                      first :: rest => List.foldl
                        (fn ((next, pivot), accumulated) =>
                          advance (next, pivot) accumulated)
                        first (ListPair.zip (rest, abstract_pivots))
                    | [] => raise ERR "resolution"
                        "empty abstract refutation chain"
                  val clause = mk_disj_terms literals
                  fun deny literal =
                    let
                      val contradiction = Thm.MP
                        (Thm.ASSUME (boolSyntax.mk_neg clause))
                        (Library.disj_intro
                          (Thm.ASSUME literal, clause))
                    in
                      case Lib.total boolSyntax.dest_neg literal of
                        SOME atom => Thm.CCONTR atom contradiction
                      | NONE => Thm.NOT_INTRO
                          (Thm.DISCH literal contradiction)
                    end
                  val resolved =
                    if List.null literals then contradiction
                    else
                      Thm.CCONTR clause
                        (List.foldl
                          (fn (literal, theorem) =>
                            Drule.PROVE_HYP (deny literal) theorem)
                          contradiction literals)
                  val residual = List.filter (fn hyp => not (List.exists
                      (structural_literal_equal hyp) abstract_prems))
                      (Thm.hyp resolved)
                  val _ = List.null residual orelse
                    raise ERR "resolution"
                      ("abstract refutation has an undischarged literal " ^
                       Library.term_to_string
                         (Term.subst (!substitutions)
                           (List.hd residual)))
                in resolved end
              fun resolve accumulated next pivot =
                let
                  fun strict candidate =
                    SOME (resolve_pair_on_structural_strict_hashed []
                      candidate accumulated next)
                    handle Feedback.HOL_ERR holerr =>
                      if SmtResource.is_resource_gate holerr then
                        raise Feedback.HOL_ERR holerr
                      else NONE
                in
                  case strict pivot of
                    SOME theorem => theorem
                  | NONE =>
                      (case strict (complement pivot) of
                         SOME theorem => theorem
                       | NONE => resolve_pair_on_structural [] pivot
                           accumulated next)
                end
              fun explicit_resolved () =
                case List.map Thm.ASSUME abstract_prems of
                  first :: rest => List.foldl
                    (fn ((next, pivot), accumulated) =>
                      resolve accumulated next pivot)
                    first (ListPair.zip (rest, abstract_pivots))
                | [] => raise ERR "resolution" "empty abstract chain"
              val resolved =
                (trace_chain "refutation schema";
                 let val theorem = refutation_resolved ()
                 in trace_chain "refutation schema complete";
                    theorem end)
                handle Feedback.HOL_ERR holerr =>
                  if SmtResource.is_resource_gate holerr then
                    raise Feedback.HOL_ERR holerr
                  else
                    (trace_chain ("refutation schema error " ^
                      Feedback.message_of holerr);
                     explicit_resolved ())
              val law = List.foldr
                (fn (premise, theorem) => Thm.DISCH premise theorem)
                resolved abstract_prems
              val instantiated = Thm.INST (!substitutions) law
            in List.foldl
              (fn (premise, theorem) => Thm.MP theorem premise)
              instantiated prems end
          fun annotated_then_schematic () =
            let val _ = trace_chain "annotated" in
              profile "CPC(chain:annotated)" annotated_chain ()
              handle Feedback.HOL_ERR holerr =>
                if SmtResource.is_resource_gate holerr then
                  raise Feedback.HOL_ERR holerr
                else (trace_chain "schematic";
                      profile "CPC(chain:schematic)"
                        schematic_chain_consequence ())
            end
          fun dynamic_then_annotated () =
            let val _ = trace_chain "dynamic" in
              profile "CPC(chain:dynamic)" dynamic_schema_consequence ()
              handle HolSatLib.SAT_cex _ =>
                (trace_chain "dynamic counterexample";
                 annotated_then_schematic ())
                   | Feedback.HOL_ERR holerr =>
                  if SmtResource.is_resource_gate holerr then
                    raise Feedback.HOL_ERR holerr
                  else (trace_chain
                          ("dynamic error " ^
                           Feedback.message_of holerr);
                        annotated_then_schematic ())
            end
          fun annotated_then_dynamic () =
            (trace_chain "annotated";
             profile "CPC(chain:annotated)"
               annotated_chain ()
             handle Feedback.HOL_ERR holerr =>
               if SmtResource.is_resource_gate holerr then
                 raise Feedback.HOL_ERR holerr
               else dynamic_then_annotated ())
          fun structural_then fallback () =
            (trace_chain "structural schema";
             profile "CPC(chain:structural-schema)"
               structural_schema_chain_consequence ()
             handle Feedback.HOL_ERR holerr =>
               (trace_chain
                 ("structural schema error " ^
                  Feedback.message_of holerr);
                fallback ()))
          fun schematic_then_dynamic () =
            (trace_chain "schematic";
             profile "CPC(chain:schematic)"
               schematic_chain_consequence ()
             handle HolSatLib.SAT_cex _ => dynamic_then_annotated ()
                  | Feedback.HOL_ERR holerr =>
               if SmtResource.is_resource_gate holerr then
                 raise Feedback.HOL_ERR holerr
               else dynamic_then_annotated ())
          val result = profile "CPC(chain:initial)" (fn () =>
            (* Large explicit pivot chains replay directly; medium chains
               use the pivot schema before the all-premise SAT abstraction.
               Every route constructs a checked theorem. *)
            (if List.length prems = 2 then annotated_then_dynamic ()
             else if List.length prems >= 256 then
               structural_then annotated_then_dynamic ()
             else if List.length prems >= 128 then
               structural_then schematic_then_dynamic ()
             else dynamic_then_annotated ())
            handle Feedback.HOL_ERR holerr =>
              if SmtResource.is_resource_gate holerr then
                raise Feedback.HOL_ERR holerr
              else (trace_chain "sat";
                    profile "CPC(chain:sat)" sat_chain_consequence ())) ()
          val _ = trace_chain "initial complete"
          val target_literals = strip_chain_clause target
          fun is_target_literal literal = List.exists
            (fn target_literal => literal_equal literal target_literal)
            target_literals
          fun extras theorem = List.filter
            (fn literal => not (is_target_literal literal))
            (List.filter (fn literal => not (List.exists
              (structural_literal_equal literal) target_literals))
              (strip_chain_clause (Thm.concl theorem)))
          fun cleanup theorem [] = theorem
            | cleanup theorem remaining =
                let
                  fun candidate [] = NONE
                    | candidate (premise :: rest) =
                        (case List.find (fn literal => List.exists
                            (fn premise_literal => literal_equal
                              (complement literal) premise_literal)
                            (strip_chain_clause (Thm.concl premise)))
                            (extras theorem) of
                           SOME literal => SOME (literal, premise, rest)
                         | NONE => Option.map
                             (fn (literal, selected, tail) =>
                               (literal, selected, premise :: tail))
                             (candidate rest))
                in
                  case candidate remaining of
                    SOME (literal, premise, rest) =>
                      cleanup
                        (resolve_pair_on chain_stops literal theorem premise)
                        rest
                  | NONE => theorem
                end
          fun contains_literal literal theorem =
            List.exists (literal_equal literal)
              (strip_chain_clause (Thm.concl theorem))
          fun annotated_cleanup theorem [] remaining =
                (theorem, List.rev remaining)
            | annotated_cleanup theorem ((premise, pivot) :: rest)
                remaining =
                if contains_literal pivot theorem andalso
                   contains_literal (complement pivot) premise then
                  annotated_cleanup
                    (resolve_pair_on chain_stops pivot theorem premise)
                    rest remaining
                else annotated_cleanup theorem rest (premise :: remaining)
          val (annotated_cleaned, annotated_remaining) =
            profile "CPC(chain:annotated_cleanup)"
              (fn () => annotated_cleanup result
                (List.rev (!unused_annotations)) []) ()
          val _ = trace_chain "annotated cleanup complete"
          val cleaned_result = profile "CPC(chain:cleanup)"
            (fn () => cleanup annotated_cleaned annotated_remaining) ()
          val _ = trace_chain "cleanup complete"
          val structural_extras = List.filter
            (fn literal => not (List.exists
              (structural_literal_equal literal) target_literals))
            (strip_chain_clause (Thm.concl cleaned_result))
          val _ = if OS.Process.getEnv
              "HOL4_CPC_REPLAY_TRACE" = SOME "full" then
            trace_chain ("structural extras " ^
              Int.toString (List.length structural_extras))
          else ()
          fun structural_deep_literals term =
            if boolSyntax.is_disj term then
              let val (left, right) = boolSyntax.dest_disj term
              in structural_deep_literals left @
                 structural_deep_literals right end
            else
              case Lib.total boolSyntax.dest_neg term of
                SOME body =>
                  if boolSyntax.is_disj body then
                    let val (left, right) = boolSyntax.dest_disj body
                    in structural_deep_literals
                         (boolSyntax.mk_neg left) @
                       structural_deep_literals
                         (boolSyntax.mk_neg right) end
                  else if boolSyntax.is_conj body then
                    let val (left, right) = boolSyntax.dest_conj body
                    in structural_deep_literals
                         (boolSyntax.mk_neg left) @
                       structural_deep_literals
                         (boolSyntax.mk_neg right) end
                  else [term]
              | NONE => [term]
          val structural_deep_extras = List.filter
            (fn literal => not (List.exists
              (structural_literal_equal literal) target_literals))
            (List.concat (List.map structural_deep_literals
              structural_extras))
          val _ = trace_chain "deep extras complete"
          fun atomic_boolean_literal term =
            if boolSyntax.is_disj term orelse boolSyntax.is_conj term then false
            else case Lib.total boolSyntax.dest_neg term of
                SOME body => not (boolSyntax.is_disj body orelse
                  boolSyntax.is_conj body orelse boolSyntax.is_neg body)
              | NONE => true
          fun supported_deep_literal term =
            word_bridge_literal term orelse
            (let
               val atom = case Lib.total boolSyntax.dest_neg term of
                   SOME body => body
                 | NONE => term
               val (head, _) = boolSyntax.strip_comb atom
               val {Thy, Name, ...} = Term.dest_thy_const head
             in Thy = "smtfloat" andalso
                String.isPrefix "smtfp_" Name end
             handle Feedback.HOL_ERR _ => false) orelse
            (case Lib.total boolSyntax.dest_neg term of
               SOME body => boolSyntax.is_disj body orelse
                 boolSyntax.is_conj body orelse boolSyntax.is_neg body
             | NONE => boolSyntax.is_disj term orelse
                 boolSyntax.is_conj term)
          val _ = unused_prems := annotated_remaining
          val supported_result = List.foldl
            (fn (theorem, accumulated) =>
              Thm.CONJ accumulated theorem) cleaned_result (!unused_prems)
          val alignment_source =
            case prems of
              first :: rest => List.foldl
                (fn (theorem, accumulated) =>
                  Thm.CONJ accumulated theorem) first rest
            | [] => cleaned_result
          val complete_source = SmtCircuitSat.balanced_conjunction prems
          fun complete_alignment_then fallback () =
            (* A weakened chain result can omit Boolean relationships that
               are still present in the certificate's original premises.
               Check their complete implication before converting literals
               in speculative strengthening attempts.  Ordinary Boolean
               decline leaves the existing theory-aware routes available. *)
            (resolution_profile "complete/raw"
               (semantic_tseitin_atom target) complete_source
             handle HolSatLib.SAT_cex _ => fallback ()
                  | Conv.UNCHANGED => fallback ()
                  | Feedback.HOL_ERR holerr =>
                      if SmtResource.is_resource_gate holerr then
                        raise Feedback.HOL_ERR holerr
                      else fallback ())
          fun chain_atom literal =
            boolSyntax.dest_neg literal
            handle Feedback.HOL_ERR _ => literal
          fun deep_disjunction_alignment () =
            let
              val _ = trace_chain "deep disjunction alignment"
              fun deep_literals term =
                if boolSyntax.is_disj term then
                  let val (left, right) = boolSyntax.dest_disj term
                  in deep_literals left @ deep_literals right end
                else [term]
              fun find_pivot theorem premise =
                let val premise_literals =
                  deep_literals (Thm.concl premise)
                in List.find
                  (fn literal => List.exists
                    (literal_equal (complement literal)) premise_literals)
                  (deep_literals (Thm.concl theorem))
                end
              fun resolve_remaining theorem [] kept =
                    (theorem, List.rev kept)
                | resolve_remaining theorem (premise :: rest) kept =
                    (case resolution_profile "deep/pivot-search"
                        (find_pivot theorem) premise of
                       SOME pivot => resolve_remaining
                         (resolve_pair_on [] pivot theorem premise)
                         (List.revAppend (kept, rest)) []
                     | NONE => resolve_remaining theorem rest
                         (premise :: kept))
              val (deep_cleaned, deep_remaining) =
                resolution_profile "deep/resolve-remaining"
                  (fn () => resolve_remaining
                    cleaned_result (!unused_prems) []) ()
              val _ = resolution_count "deep/unused-premises"
                (List.length (!unused_prems))
              val _ = trace_chain ("deep remaining " ^
                Int.toString (List.length deep_remaining))
              fun fp_literal_conversion term =
                let
                  val negated = Lib.total boolSyntax.dest_neg term
                  val atom = case negated of SOME body => body | NONE => term
                  val (head, _) = boolSyntax.strip_comb atom
                  val {Thy, Name, ...} = Term.dest_thy_const head
                  val _ = Thy = "smtfloat" andalso
                    String.isPrefix "smtfp_" Name orelse
                    raise Conv.UNCHANGED
                in
                  case negated of
                    SOME _ => Conv.RAND_CONV SmtFpGraph.convert_atom term
                  | NONE => SmtFpGraph.convert_atom term
                end
                handle Feedback.HOL_ERR holerr =>
                  if SmtResource.is_resource_gate holerr then
                    raise Feedback.HOL_ERR holerr
                  else raise Conv.UNCHANGED
              fun boolean_negation_conversion term =
                let
                  val body = boolSyntax.dest_neg term
                  val theorem =
                    if boolSyntax.is_disj body then
                      let val (left, right) = boolSyntax.dest_disj body
                      in Thm.CONJUNCT2
                        (Drule.SPECL [left, right]
                          boolTheory.DE_MORGAN_THM) end
                    else if boolSyntax.is_conj body then
                      let val (left, right) = boolSyntax.dest_conj body
                      in Thm.CONJUNCT1
                        (Drule.SPECL [left, right]
                          boolTheory.DE_MORGAN_THM) end
                    else
                      Thm.SPEC (boolSyntax.dest_neg body)
                        (Thm.CONJUNCT1 boolTheory.NOT_CLAUSES)
                in Conv.REWR_CONV theorem term end
              fun checked_conversion source =
                resolution_profile "deep/leaf-conversion" (fn () =>
                  SOME (boolean_negation_conversion source
                    handle Feedback.HOL_ERR holerr =>
                      if SmtResource.is_resource_gate holerr then
                        raise Feedback.HOL_ERR holerr
                      else fp_literal_conversion source)
                  handle Conv.UNCHANGED => NONE) ()
              fun checked_equivalence source destination =
                resolution_profile "deep/membership" (fn () =>
                  literal_equivalence source destination) ()
              fun work () =
                let
                  val planned = resolution_profile "deep/recognition"
                    (fn () => disjunction_alignment_plan
                      {target = target, hash = literal_hash 6,
                       equivalence = checked_equivalence,
                       conversion = checked_conversion,
                       count = fn name => resolution_count ("deep/" ^ name)}
                      (Thm.concl deep_cleaned)) ()
                in
                  case planned of
                    NONE => raise Conv.UNCHANGED
                  | SOME realize => Thm.MP
                      (resolution_profile "deep/realization" realize ())
                      deep_cleaned
                end
              val _ = trace_chain "deep recognition begin"
            in SmtResource.with_bitblast_step_time
              "cpc-resolution-deep-disjunction-alignment" work () end
          fun schematic_supported_alignment () =
            let
              val _ = trace_chain "schematic supported alignment"
              val atoms = ref ([] : (Term.term * Term.term) list)
              val substitutions = ref
                ([] : {redex : Term.term, residue : Term.term} list)
              fun atom term =
                case List.find (fn (saved, _) =>
                    literal_equal saved term) (!atoms) of
                  SOME (_, variable) => variable
                | NONE =>
                    let
                      val variable = Term.genvar Type.bool
                      val _ = atoms := (term, variable) :: !atoms
                      val _ = substitutions :=
                        {redex = variable, residue = term} :: !substitutions
                    in variable end
              fun literal term =
                case Lib.total boolSyntax.dest_neg term of
                  SOME base => boolSyntax.mk_neg (atom base)
                | NONE => atom term
              val normalize_memo = ref
                ([] : (Term.term * Thm.thm) list)
              fun direct_fp_atom term =
                let
                  val (head, _) = boolSyntax.strip_comb term
                  val {Thy, Name, ...} = Term.dest_thy_const head
                in Thy = "smtfloat" andalso
                  String.isPrefix "smtfp_" Name
                end
                handle Feedback.HOL_ERR _ => false
              fun normalize_clause term =
                case List.find (fn (saved, _) =>
                    Portable.pointer_eq (saved, term)) (!normalize_memo) of
                  SOME (_, theorem) => theorem
                | NONE =>
                    let
                      val theorem =
                        if boolSyntax.is_disj term orelse
                           boolSyntax.is_conj term orelse
                           boolSyntax.is_imp term then
                          Conv.BINOP_CONV normalize_clause term
                        else if boolSyntax.is_neg term then
                          Conv.RAND_CONV normalize_clause term
                        else if word_bridge_literal term then
                          normalize_literal term
                        else if direct_fp_atom term then
                          SmtFpGraph.convert_atom term
                        else Thm.REFL term
                      val _ = normalize_memo :=
                        (term, theorem) :: !normalize_memo
                    in theorem end
              fun normalize_inputs () =
                let
                  val cleaned = Conv.CONV_RULE normalize_clause cleaned_result
                  val unused = List.map
                    (Conv.CONV_RULE normalize_clause) (!unused_prems)
                  val supported = List.foldl
                    (fn (theorem, accumulated) =>
                      Thm.CONJ accumulated theorem) cleaned unused
                  val target_conversion = normalize_clause target
                in (supported, target_conversion) end
              val (normalized_supported, target_conversion) =
                SmtResource.with_bitblast_step_time
                  "cpc-resolution-supported-normalize"
                  normalize_inputs ()
              val normalized_target = boolSyntax.rhs
                (Thm.concl target_conversion)
              val abstract_memo = ref
                (Redblackmap.mkDict Term.compare :
                  (Term.term, Term.term) Redblackmap.dict)
              fun abstract_formula term =
                case Redblackmap.peek (!abstract_memo, term) of
                  SOME result => result
                | NONE =>
                    let
                      val result =
                        if boolSyntax.is_conj term then
                          let val (left, right) = boolSyntax.dest_conj term
                          in boolSyntax.mk_conj
                            (abstract_formula left,
                             abstract_formula right) end
                        else if boolSyntax.is_disj term then
                          let val (left, right) = boolSyntax.dest_disj term
                          in boolSyntax.mk_disj
                            (abstract_formula left,
                             abstract_formula right) end
                        else
                          case Lib.total boolSyntax.dest_neg term of
                            SOME inner =>
                              boolSyntax.mk_neg (abstract_formula inner)
                          | NONE => atom term
                      val _ = abstract_memo := Redblackmap.insert
                        (!abstract_memo, term, result)
                    in result end
              val implication = boolSyntax.mk_imp
                (abstract_formula (Thm.concl normalized_supported),
                 abstract_formula normalized_target)
              val law = prove_boolean_dag_tautology_compact
                "cpc-resolution-supported-schema" implication
              val theorem = Thm.INST (!substitutions) law
              val normalized_result = Thm.MP theorem normalized_supported
            in Thm.EQ_MP (Thm.SYM target_conversion) normalized_result end
          fun boolean_dag_convert_leaf term =
            if word_bridge_literal term then
              let
                val conversion = normalize_literal term
                val residue = boolSyntax.rhs (Thm.concl conversion)
              in if Term.aconv term residue then NONE
                 else SOME conversion end
            else
              let
                val negated = Lib.total boolSyntax.dest_neg term
                val atom = case negated of
                    SOME body => body
                  | NONE => term
                val (head, _) = boolSyntax.strip_comb atom
                val {Thy, Name, ...} = Term.dest_thy_const head
                val _ = Thy = "smtfloat" andalso
                  String.isPrefix "smtfp_" Name orelse
                  raise Conv.UNCHANGED
                val conversion = case negated of
                    SOME _ => Conv.RAND_CONV SmtFpGraph.convert_atom term
                  | NONE => SmtFpGraph.convert_atom term
              in SOME conversion end
              handle Conv.UNCHANGED => NONE
                   | Feedback.HOL_ERR holerr =>
                if SmtResource.is_resource_gate holerr then
                  raise Feedback.HOL_ERR holerr
                else NONE
          fun boolean_dag_prove_from theorem =
            let
              val implication = boolSyntax.mk_imp
                (Thm.concl theorem, target)
              val law =
                prove_boolean_dag_tautology_with_leaf_conversion_using
                  (SOME 3) HolSatLib.SAT_PROVE []
                  boolean_dag_convert_leaf
                  "cpc-resolution-boolean-dag-alignment" implication
            in Thm.MP law theorem end
          fun boolean_dag_cleaned_alignment () =
            (trace_chain "boolean DAG cleaned first";
             boolean_dag_prove_from cleaned_result)
          fun boolean_dag_combined_alignment () =
            let
              val _ = trace_chain "boolean DAG combined fallback"
              fun align theorem = boolean_dag_prove_from
                (Thm.CONJ cleaned_result theorem)
            in
              align (abstract_structural_annotated_chain ())
              handle HolSatLib.SAT_cex _ =>
                       align (structural_annotated_chain ())
                   | Feedback.HOL_ERR holerr =>
                       if SmtResource.is_resource_gate holerr then
                         raise Feedback.HOL_ERR holerr
                       else align (structural_annotated_chain ())
            end
          fun direct_chain_alignment () =
            let
              val _ = trace_chain "direct alignment"
              val implication = boolSyntax.mk_imp
                (Thm.concl alignment_source, target)
              fun node_conversion term =
                SmtFpGraph.convert_word_projection term
                handle Conv.UNCHANGED =>
                  (Conv.REWR_CONV
                     smtfloatReplayRoundingTheory.word_compare_index term
                   handle Feedback.HOL_ERR _ => raise Conv.UNCHANGED)
                     | Empty => raise Conv.UNCHANGED
                     | Feedback.HOL_ERR holerr =>
                  if SmtResource.is_resource_gate holerr then
                    raise Feedback.HOL_ERR holerr
                  else raise Conv.UNCHANGED
              fun convert_leaf term =
                if word_bridge_literal term then
                  let
                    val theorem =
                      (SmtWordGraph.normalize_with_node_conversion
                         node_conversion term
                       handle Conv.UNCHANGED => normalize_literal term)
                    val residue = boolSyntax.rhs (Thm.concl theorem)
                  in
                    if Term.aconv term residue then NONE
                    else SOME theorem
                  end
                else if SmtFpGraph.lower_atom_domain term then
                  SOME (SmtFpGraph.convert_atom term)
                else NONE
              val law =
                prove_boolean_dag_tautology_with_leaf_conversion_using
                  (SOME 3) HolSatLib.SAT_PROVE [] convert_leaf
                  "cpc-resolution-result-alignment" implication
            in Thm.MP law alignment_source end
          fun circuit_alignment [] =
                (trace_chain "circuit alignment final";
                if List.length target_literals <= 3 then
                  semantic_word_tseitin target alignment_source
                else semantic_tseitin_atom target alignment_source)
            | circuit_alignment ((label, source) :: rest) =
                (trace_chain "circuit alignment candidate";
                 resolution_profile ("candidate/" ^ label)
                   (semantic_tseitin_atom target) source
                 handle HolSatLib.SAT_cex _ => circuit_alignment rest
                      | Feedback.HOL_ERR holerr =>
                          if SmtResource.is_resource_gate holerr then
                            raise Feedback.HOL_ERR holerr
                          else circuit_alignment rest)
          fun original_alignment () =
            (trace_chain "original alignment";
             (if List.length prems > 32 then
                circuit_alignment
                  [("cleaned", cleaned_result),
                   ("supported", supported_result),
                   ("premises", alignment_source)]
              else semantic_taut_reorder supported_result)
             handle Feedback.HOL_ERR holerr =>
               if SmtResource.is_resource_gate holerr then
                 raise Feedback.HOL_ERR holerr
               else schematic_reorder cleaned_result
             handle HolSatLib.SAT_cex _ =>
                      reorder_to_target cleaned_result
                  | Feedback.HOL_ERR _ =>
                      (resolution_profile "circuit-reorder"
                         semantic_circuit_reorder alignment_source
                       handle HolSatLib.SAT_cex _ =>
                              reorder_to_target cleaned_result
                            | Feedback.HOL_ERR _ =>
                              reorder_to_target cleaned_result)
             handle Feedback.HOL_ERR _ => contextual_target cleaned_result
             handle Feedback.HOL_ERR _ =>
               tautological_consequences prems target)
          fun boolean_dag_later_alignment () =
            let
              fun original_then_combined () =
                original_alignment ()
                handle HolSatLib.SAT_cex _ =>
                         boolean_dag_combined_alignment ()
                     | Conv.UNCHANGED =>
                         boolean_dag_combined_alignment ()
                     | Feedback.HOL_ERR holerr =>
                         if SmtResource.is_resource_gate holerr then
                           raise Feedback.HOL_ERR holerr
                         else boolean_dag_combined_alignment ()
            in
              resolution_profile "deep-disjunction"
                deep_disjunction_alignment ()
              handle HolSatLib.SAT_cex _ => original_then_combined ()
                   | Conv.UNCHANGED => original_then_combined ()
                   | Feedback.HOL_ERR holerr =>
                       if SmtResource.is_resource_gate holerr then
                         raise Feedback.HOL_ERR holerr
                       else original_then_combined ()
            end
          val use_supported_schema =
            List.length prems > 150 andalso
            List.length prems <= 250 andalso
            not (List.null (!unused_prems)) andalso
            List.length target_literals <= 16 andalso
              List.length (strip_chain_clause
              (Thm.concl cleaned_result)) -
              List.length target_literals > 0
          val _ = trace_chain ("supported schema " ^
            Bool.toString use_supported_schema ^ " unused=" ^
            Int.toString (List.length (!unused_prems)) ^ " target=" ^
            Int.toString (List.length target_literals))
          val _ = trace_chain "checking Boolean DAG eligibility"
          val boolean_dag_eligible =
            List.null (!unused_prems) andalso
            not (List.null structural_extras) andalso
            List.all atomic_boolean_literal target_literals andalso
            List.length structural_deep_extras <= 64 andalso
            List.all supported_deep_literal structural_deep_extras
          val _ = trace_chain ("Boolean DAG eligible " ^
            Bool.toString boolean_dag_eligible)
          fun semantic_extras_empty () =
            let
              val _ = trace_chain "checking semantic extras"
              val result = List.null (extras cleaned_result)
              val _ = trace_chain ("semantic extras empty " ^
                Bool.toString result)
            in result end
          val _ = trace_chain "alignment setup complete"
        in
          resolution_profile "alignment" (fn () =>
          profile "CPC(chain:alignment)" (fn () =>
          if List.null structural_extras andalso
             shared_aconv (Thm.concl cleaned_result) target then
            cleaned_result
          else if List.null structural_extras then
            resolution_profile "reorder" reorder_to_target cleaned_result
          else complete_alignment_then (fn () =>
          if List.length prems = 2 then
            (* Binary resolution has a compact Boolean consequence from its
               two exact premise theorems.  Check that DAG directly before
               trying the broader semantic alignment ladder, whose generic
               term abstraction is needlessly expensive on bit-blasted FP
               literals. *)
            (resolution_profile "direct" direct_chain_alignment ()
             handle HolSatLib.SAT_cex _ => original_alignment ()
                  | Feedback.HOL_ERR holerr =>
                      if SmtResource.is_resource_gate holerr then
                        raise Feedback.HOL_ERR holerr
                      else original_alignment ())
          else if boolean_dag_eligible then
            (resolution_profile "boolean-dag/cleaned"
               boolean_dag_cleaned_alignment ()
             handle HolSatLib.SAT_cex _ =>
                      boolean_dag_later_alignment ()
                  | Feedback.HOL_ERR holerr =>
               if SmtResource.is_resource_gate holerr then
                 raise Feedback.HOL_ERR holerr
               else boolean_dag_later_alignment ())
          else if semantic_extras_empty () then
            resolution_profile "reorder" reorder_to_target cleaned_result
          else if use_supported_schema then
            (resolution_profile "supported-schema"
               schematic_supported_alignment ()
             handle HolSatLib.SAT_cex _ => original_alignment ()
                  | Conv.UNCHANGED => original_alignment ()
                  | Feedback.HOL_ERR holerr =>
               (trace_chain
                  ("schematic supported error " ^
                   Feedback.message_of holerr);
                direct_chain_alignment ()
                handle HolSatLib.SAT_cex _ => original_alignment ()
                     | Feedback.HOL_ERR _ => original_alignment ()))
          else original_alignment ()) ()) ()) ()
        end
      fun has_non_arithmetic_equality tm =
        let
          fun arithmetic_type ty =
            Type.compare (ty, Type.bool) = EQUAL orelse
            Type.compare (ty, numSyntax.num) = EQUAL orelse
            Type.compare (ty, intSyntax.int_ty) = EQUAL orelse
            Type.compare (ty, realSyntax.real_ty) = EQUAL orelse
            wordsSyntax.is_word_type ty
          fun search term =
            case Lib.total boolSyntax.dest_eq term of
              SOME (left, right) =>
                not (arithmetic_type (Term.type_of left)) orelse
                search left orelse search right
            | NONE =>
                (case Lib.total Term.dest_comb term of
                   SOME (operator, operand) =>
                     search operator orelse search operand
                 | NONE =>
                     (case Lib.total Term.dest_abs term of
                        SOME (_, body) => search body
                      | NONE => false))
        in search tm end
      fun resolution_result polarity pivot =
        case prems of
          [first, second] =>
            let
              val first_lits = strip_clause (Thm.concl first)
              val second_lits = strip_clause (Thm.concl second)
              val first_pivot =
                if Term.aconv polarity boolSyntax.T then pivot
                else if Term.aconv polarity boolSyntax.F then
                  boolSyntax.mk_neg pivot
                else raise ERR "resolution"
                  "CPC resolution polarity is not Boolean"
              val second_pivot = boolSyntax.mk_neg first_pivot
              val first_rest =
                case remove_first first_pivot first_lits of
                  SOME rest => rest
                | NONE => raise ERR "resolution"
                  "CPC resolution pivot is absent from its first clause"
              val second_rest =
                case remove_first second_pivot second_lits of
                  SOME rest => rest
                | NONE => raise ERR "resolution"
                  ("CPC resolution pivot is absent from its second clause; pivot=" ^
                   Library.term_to_string second_pivot ^ "; second clause=" ^
                   Library.term_to_string (Thm.concl second))
            in mk_disj_terms (first_rest @ second_rest) end
        | _ => raise ERR "resolution" "expected two CPC resolution premises"
      fun tautological_checked target =
        (if List.length prems > 2 then
           (sat_clause_consequences prems target
            handle Feedback.HOL_ERR holerr =>
              if SmtResource.is_resource_gate holerr then
                raise Feedback.HOL_ERR holerr
              else tautological_consequences prems target)
         else tautological_consequences prems target)
        handle HolSatLib.SAT_cex _ =>
          raise ERR "resolution" "propositional consequence is invalid"
      (* Macro/chain resolution records its resolvent as the first argument,
         followed by one polarity and one pivot for every premise after the
         first.  This annotation is the general rule contract, including the
         two-premise case.  Replaying it directly avoids handing a large
         bit-blasted clause to a blind propositional tautology procedure. *)
      fun annotated_macro_chain target =
        let
          val pivot_count = List.length prems - 1
        in
          case args of
            recorded_target :: annotation =>
              if pivot_count > 0 andalso
                 List.length annotation = 2 * pivot_count then
                (replay_chain recorded_target
                   (List.take (annotation, pivot_count))
                   (List.drop (annotation, pivot_count))
                 handle HolSatLib.SAT_cex _ =>
                   tautological_checked target
                      | Feedback.HOL_ERR replay_error =>
                   if SmtResource.is_resource_gate replay_error then
                     raise Feedback.HOL_ERR replay_error
                   else tautological_checked target)
              else tautological_checked target
          | [] => tautological_checked target
        end
      fun prove target =
        (profile "CPC(rung:resolution/annotated_macro)"
           annotated_macro_chain target
         handle Feedback.HOL_ERR _ =>
           (case profile "CPC(rung:resolution/complementary)"
             (fn () => resolve_complementary_literals prems target) () of
              SOME thm => thm
            | NONE =>
                (case profile "CPC(rung:resolution/binary)"
                  (fn () => resolve_binary_disjunction prems target) () of
                   SOME thm => thm
                 | NONE =>
                     (* HOL reconstruction can expose equality congruences
                        between certificate literals (notably datatype and
                        record constructor/selector terms).  These are beyond
                        propositional TAUT but remain the semantics of
                        resolution from the exact premise theorems. *)
                     if List.exists has_non_arithmetic_equality
                          (target :: List.map Thm.concl prems) then
                       metis_prove prems target
                     else raise ERR "resolution"
                       "resolution requires no equality-congruence fallback")))
    in
      case (conclusion, args) of
        (SOME target, _) => prove target
      | (NONE, [target, polarity, pivot]) =>
          replay_chain target [polarity] [pivot]
      | (NONE, [polarity, pivot]) => prove (resolution_result polarity pivot)
      | (NONE, [target]) => prove target
      | (NONE, target :: _) => prove target
      | (NONE, _) => raise ERR "resolution"
          "CPC resolution omitted its conclusion or pivot annotation"
    end

  fun replay_bool prems conclusion =
    case conclusion of
      SOME target => metis_prove prems target
    | NONE => raise ERR "bool" "CPC boolean step omitted its conclusion"

  fun replay_arith prems conclusion =
    case conclusion of
      SOME target => arith_prove_from_prems prems target
    | NONE => raise ERR "arith" "CPC arithmetic step omitted its conclusion"

  fun replay_string state name prems conclusion args =
    let
      fun same_const thy name tm =
        case Lib.total Term.dest_thy_const tm of
          SOME {Thy, Name, ...} => Thy = thy andalso Name = name
        | NONE => false
      fun binary_app thy name left right = Term.list_mk_comb
        (Term.prim_mk_const {Thy = thy, Name = name}, [left, right])
      fun smt_in_re string regex =
        binary_app "smtstring" "smt_in_re" string regex
      fun concat_strings [] = raise ERR "string"
            "re_unfold_pos produced no components"
        | concat_strings [only] = only
        | concat_strings (first :: rest) =
            binary_app "smtstring" "smtstr_concat" first
              (concat_strings rest)
      fun concat_regexps [] = raise ERR "string"
            "re_unfold_pos produced no regular expressions"
        | concat_regexps [only] = only
        | concat_regexps (first :: rest) =
            binary_app "smtstring" "reglan_concat" first
              (concat_regexps rest)
      fun binary_congruence operator left right =
        Thm.MK_COMB (Thm.MK_COMB (Thm.REFL operator, left), right)
      (* Expose only the selected edge of an outer associative spine.  The
         selected term is an explicit stopping point, even when it is itself
         headed by the same operator, so opaque nested operands are never
         rewritten. *)
      fun outer_edge_decomposition operator dest mk assoc empty
          nil_left nil_right from_end whole selected =
        let
          fun root_rewrite label theorem term =
            Conv.REWR_CONV theorem term
            handle Feedback.HOL_ERR holerr => raise ERR "string"
              ("outer concat " ^ label ^ " failed on " ^
               Library.term_to_string term ^ ": " ^
               Feedback.message_of holerr)
          fun descend term =
            if Term.aconv term selected then
              if from_end then
                let
                  val theorem = root_rewrite "left identity" nil_left
                    (mk (empty, selected))
                in
                  {theorem = Thm.SYM theorem, other = empty}
                end
              else
                let
                  val theorem = root_rewrite "right identity" nil_right
                    (mk (selected, empty))
                in
                  {theorem = Thm.SYM theorem, other = empty}
                end
            else
              case Lib.total dest term of
                NONE => raise ERR "string"
                  "concat_unify selected term is not on the outer edge"
              | SOME (left, right) =>
                  if from_end andalso Term.aconv right selected then
                    {theorem = Thm.REFL term, other = left}
                  else if not from_end andalso
                          Term.aconv left selected then
                    {theorem = Thm.REFL term, other = right}
                  else if from_end then
                    let
                      val {theorem, other} = descend right
                      val congruence = binary_congruence operator
                        (Thm.REFL left) theorem
                      val reassociate = Thm.SYM
                        (root_rewrite "reverse associativity" assoc
                          (mk (mk (left, other), selected)))
                    in
                      {theorem = Thm.TRANS congruence reassociate,
                       other = mk (left, other)}
                    end
                  else
                    let
                      val {theorem, other} = descend left
                      val congruence = binary_congruence operator theorem
                        (Thm.REFL right)
                      val reassociate = root_rewrite "front associativity"
                        assoc
                        (mk (mk (selected, other), right))
                    in
                      {theorem = Thm.TRANS congruence reassociate,
                       other = mk (other, right)}
                    end
        in
          descend whole
        end
      (* Prove semantic right-canonicalization against the parser's exact
         desired component list.  A singleton alpha-match is an opaque stop,
         even when that component is concat-headed.  Otherwise, backtrack
         over nonempty desired-list partitions matching the original root. *)
      fun regex_components_right_canonical dest mk whole desired =
        let
          val smtstr_type = Type.mk_thy_type
            {Thy = "smtstring", Tyop = "smtstr", Args = []}
          fun fold [term] = term
            | fold (term :: rest) = mk (term, fold rest)
            | fold [] = raise ERR "string" "empty outer concat spine"
          fun language_refl regex =
            let
              val string = Term.variant (Term.free_vars regex)
                (Term.mk_var ("outer_regex_string", smtstr_type))
            in
              Thm.GEN string (Thm.REFL (smt_in_re string regex))
            end
          fun language_trans first second =
            let
              val string = Term.variant
                (Term.free_vars (Thm.concl first) @
                 Term.free_vars (Thm.concl second))
                (Term.mk_var ("outer_regex_string", smtstr_type))
            in
              Thm.GEN string (Thm.TRANS
                (Thm.SPEC string first) (Thm.SPEC string second))
            end
          fun language_congruence left left' right right'
              left_theorem right_theorem =
            Thm.MP (Drule.SPECL [left, left', right, right']
              smtstringTheory.smt_in_re_concat_language_cong)
              (Thm.CONJ left_theorem right_theorem)
          fun merge (left :: []) right =
                language_refl (mk (left, fold right))
            | merge (left :: rest) right =
                let
                  val tail = merge rest right
                  val reassociate = Drule.SPECL
                    [left, fold rest, fold right]
                    smtstringTheory.smt_in_re_concat_assoc_all
                  val congruence = language_congruence
                    left left (mk (fold rest, fold right))
                    (fold (rest @ right)) (language_refl left) tail
                in
                  language_trans reassociate congruence
                end
            | merge [] _ = raise ERR "string" "empty outer concat spine"
          fun prove term [only] =
                if Term.aconv term only then SOME (language_refl term)
                else NONE
            | prove _ [] = NONE
            | prove term components =
                (case Lib.total dest term of
                   NONE => NONE
                 | SOME (left, right) =>
                     let
                       fun try [] = NONE
                         | try (position :: positions) =
                             let
                               val lefts = List.take
                                 (components, position)
                               val rights = List.drop
                                 (components, position)
                             in
                               case (prove left lefts,
                                     prove right rights) of
                                 (SOME left_theorem,
                                  SOME right_theorem) =>
                                   let
                                     val congruence = language_congruence
                                       left (fold lefts) right (fold rights)
                                       left_theorem right_theorem
                                     val merged = merge lefts rights
                                   in
                                     SOME (language_trans congruence merged)
                                   end
                               | _ => try positions
                             end
                       val positions = List.tabulate
                         (List.length components - 1, fn index => index + 1)
                     in
                       try positions
                     end)
        in
          case prove whole desired of
            SOME theorem => theorem
          | NONE => raise ERR "string"
              "re_unfold_pos regex does not match parser component spine"
        end
      fun empty_string () = Term.mk_comb
        (Term.prim_mk_const {Thy = "smtstring", Name = "SmtStr"},
         listSyntax.mk_nil numSyntax.num)
      fun concat_unify_target () =
        case prems of
          [_, length_equality] =>
            let
              fun length_argument side tm =
                case boolSyntax.strip_comb tm of
                  (head, [argument]) =>
                    if same_const "smtstring" "smtstr_len" head then
                      argument
                    else if Term.aconv head intSyntax.int_injection then
                      (case Lib.total listSyntax.dest_length argument of
                         SOME sequence => sequence
                       | NONE => raise ERR "string"
                           ("concat_unify " ^ side ^
                            " term is not a sequence length"))
                    else raise ERR "string"
                      ("concat_unify " ^ side ^ " term is not a length")
                | _ => raise ERR "string"
                    ("concat_unify " ^ side ^ " length is not unary")
              val (left_length, right_length) =
                boolSyntax.dest_eq (Thm.concl length_equality)
              val left = length_argument "left" left_length
              val right = length_argument "right" right_length
            in
              boolSyntax.mk_eq (left, right)
            end
        | _ => raise ERR "string"
            "concat_unify expects equality and length premises"
      fun re_unfold_pos_target () =
        case prems of
          [membership] =>
            let
              val (head, membership_args) =
                boolSyntax.strip_comb (Thm.concl membership)
              val (string, regex) =
                case membership_args of
                  [string, regex] =>
                    if same_const "smtstring" "smt_in_re" head then
                      (string, regex)
                    else raise ERR "string"
                      "re_unfold_pos premise is not membership"
                | _ => raise ERR "string"
                    "re_unfold_pos premise is not binary membership"
              fun decomposition decomposition_regex =
                let
                  val components =
                    CPC_ProofParser.cpc_re_unfold_pos_regexps
                      decomposition_regex
                  fun component (component_regex, index) =
                    case boolSyntax.strip_comb component_regex of
                      (to_re, [literal]) =>
                        if same_const "smtstring" "reglan_to_re" to_re then
                          (literal, NONE)
                        else
                          let
                            val index = intSyntax.term_of_int
                              (Arbint.fromInt index)
                            val skolem =
                              CPC_ProofParser.cpc_re_unfold_pos_component
                                string decomposition_regex index
                          in
                            (skolem, SOME
                              (smt_in_re skolem component_regex))
                          end
                    | _ =>
                        let
                          val index = intSyntax.term_of_int
                            (Arbint.fromInt index)
                          val skolem =
                            CPC_ProofParser.cpc_re_unfold_pos_component
                              string decomposition_regex index
                        in
                          (skolem, SOME
                            (smt_in_re skolem component_regex))
                        end
                  val indexed = ListPair.zip
                    (components, List.tabulate
                      (List.length components, Lib.I))
                  val decomposed = List.map component indexed
                  val strings = List.map Lib.fst decomposed
                  val equality = boolSyntax.mk_eq
                    (string, concat_strings strings)
                in
                  (strings, equality, List.mapPartial Lib.snd decomposed)
                end
            in
              case boolSyntax.strip_comb regex of
                (star, [body]) =>
                  if same_const "smtstring" "reglan_star" star then
                    let
                      val expanded = concat_regexps [body, regex, body]
                      val (strings, equality, memberships) =
                        decomposition expanded
                      val decomposition = boolSyntax.list_mk_conj
                        (equality :: memberships)
                      val first = List.hd strings
                      val last = List.last strings
                      val nonempty = fn component => boolSyntax.mk_neg
                        (boolSyntax.mk_eq (component, empty_string ()))
                    in
                      boolSyntax.list_mk_disj
                        [boolSyntax.mk_eq (string, empty_string ()),
                         smt_in_re string body,
                         boolSyntax.list_mk_conj
                           [decomposition, nonempty first, nonempty last]]
                    end
                  else raise ERR "string"
                    "re_unfold_pos expects star or concatenation membership"
              | (concat, [_, _]) =>
                  if same_const "smtstring" "reglan_concat" concat then
                    let
                      val (_, equality, memberships) = decomposition regex
                    in
                      boolSyntax.list_mk_conj (equality :: memberships)
                    end
                  else raise ERR "string"
                    "re_unfold_pos expects star or concatenation membership"
              | _ => raise ERR "string"
                  "re_unfold_pos expects star or concatenation membership"
            end
        | _ => raise ERR "string" "re_unfold_pos expects one premise"
      fun is_empty_string tm =
        case boolSyntax.strip_comb tm of
          (head, [chars]) =>
            (case Lib.total Term.dest_thy_const head of
               SOME {Thy, Name, ...} =>
                 Thy = "smtstring" andalso Name = "SmtStr" andalso
                 listSyntax.is_nil chars
             | NONE => false)
        | _ => false
      fun substring_reduction_theorem substring =
        case boolSyntax.strip_comb substring of
          (head, [string, start, count]) =>
            if same_const "smtstring" "smtstr_substr" head then
              Thm.INST
                [{redex = ``s : smtstr``, residue = string},
                 {redex = ``i : int``, residue = start},
                 {redex = ``n : int``, residue = count}]
                smtstringTheory.smtstr_substr_reduction
            else raise ERR "string_reduction"
              "expected a substring argument"
        | _ => raise ERR "string_reduction"
            "expected a substring argument"
      fun instantiate_exact theorem target =
        let val generic = Drule.SPEC_ALL theorem in
          Drule.INST_TY_TERM
            (Term.match_term (Thm.concl generic) target) generic
        end
      fun fixed_regex_length_theorem string regex =
        let
          fun membership string regex = smt_in_re string regex
          fun implication length = boolSyntax.mk_imp
            (membership string regex,
             boolSyntax.mk_eq
               (Term.mk_comb
                  (Term.prim_mk_const
                    {Thy = "smtstring", Name = "smtstr_len"}, string),
                length))
          val (head, operands) = boolSyntax.strip_comb regex
        in
          if same_const "smtstring" "reglan_range" head then
            instantiate_exact smtstringTheory.smt_in_re_range_length
              (implication (intSyntax.mk_injected
                (numSyntax.mk_numeral Arbnum.one)))
          else if same_const "smtstring" "reglan_allchar" head andalso
                  List.null operands then
            instantiate_exact
              (Drule.iffLR smtstringTheory.smt_in_re_allchar_len)
              (implication (intSyntax.mk_injected
                (numSyntax.mk_numeral Arbnum.one)))
          else if same_const "smtstring" "reglan_to_re" head then
            (case operands of
               [literal] => instantiate_exact
                 smtstringTheory.smt_in_re_to_re_length
                 (implication (Term.mk_comb
                   (Term.prim_mk_const
                     {Thy = "smtstring", Name = "smtstr_len"}, literal)))
             | _ => raise ERR "string_eager_reduction"
                 "str.to_re has wrong arity")
          else if same_const "smtstring" "reglan_concat" head then
            (case operands of
               [left, right] =>
                 let
                   val smtstr_type = Type.mk_thy_type
                     {Thy = "smtstring", Tyop = "smtstr", Args = []}
                   val left_string = Term.variant
                     (Term.free_vars regex @ Term.free_vars string)
                     (Term.mk_var ("fixed_left", smtstr_type))
                   val right_string = Term.variant
                     (left_string :: Term.free_vars regex @
                      Term.free_vars string)
                     (Term.mk_var ("fixed_right", smtstr_type))
                   val left_theorem = Thm.GEN left_string
                     (fixed_regex_length_theorem left_string left)
                   val right_theorem = Thm.GEN right_string
                     (fixed_regex_length_theorem right_string right)
                   val (_, left_result) = boolSyntax.dest_imp
                     (Thm.concl (Thm.SPEC left_string left_theorem))
                   val (_, left_length) = boolSyntax.dest_eq left_result
                   val (_, right_result) = boolSyntax.dest_imp
                     (Thm.concl (Thm.SPEC right_string right_theorem))
                   val (_, right_length) = boolSyntax.dest_eq right_result
                   val target = implication
                     (intSyntax.mk_plus (left_length, right_length))
                   val premise = Thm.CONJ left_theorem right_theorem
                   val generic = Drule.SPEC_ALL
                     smtstringTheory.smt_in_re_concat_fixed_length
                   val specialized = Drule.INST_TY_TERM
                     (Term.match_term (Thm.concl generic)
                       (boolSyntax.mk_imp (Thm.concl premise, target)))
                     generic
                 in Thm.MP specialized premise end
             | _ => raise ERR "string_eager_reduction"
                 "re.++ has wrong arity")
          else raise ERR "string_eager_reduction"
            "regular expression has no checked fixed-length schema"
        end
      fun string_eager_reduction_theorem argument =
        case boolSyntax.strip_comb argument of
          (head, [string, regex]) =>
            if same_const "smtstring" "smt_in_re" head then
              fixed_regex_length_theorem string regex
            else raise ERR "string_eager_reduction"
              "argument is not regular-expression membership"
        | (head, [string]) =>
            if same_const "smtstring" "smtstr_to_code" head then
              let
                val generic = Drule.SPEC_ALL
                  smtstringTheory.smtstr_to_code_eager_reduction
                val variable = Lib.singleton_of_list
                  (Term.free_vars (Thm.concl generic))
              in
                Thm.INST [{redex = variable, residue = string}] generic
              end
            else raise ERR "string_eager_reduction"
              "unary argument has no checked eager-reduction schema"
        | _ => raise ERR "string_eager_reduction"
            "argument has no checked eager-reduction schema"
      fun string_length_pos_theorem string =
        let
          val generic = Drule.SPEC_ALL
            smtstringTheory.smtstr_length_positive_split
          val variable = Lib.singleton_of_list (Term.free_vars
            (Thm.concl generic))
        in
          Thm.INST [{redex = variable, residue = string}] generic
        end
      fun inferred_target () =
        case (name, args) of
          ("concat_unify", [_]) => concat_unify_target ()
        | ("re_unfold_pos", []) => re_unfold_pos_target ()
        | ("string_reduction", [substring]) =>
            Thm.concl (substring_reduction_theorem substring)
        | ("string_eager_reduction", [argument]) =>
            Thm.concl (string_eager_reduction_theorem argument)
        | ("string_length_pos", [string]) =>
            Thm.concl (string_length_pos_theorem string)
        | ("str-len-concat-rec", [left, right, empty]) =>
            if listSyntax.is_nil empty orelse is_empty_string empty then
              if is_smtstr_type (Term.type_of left) then
                Thm.concl (Drule.SPECL [left, right]
                  smtstringTheory.smtstr_len_concat)
              else
                let
                  fun length sequence = Term.mk_comb
                    (intSyntax.int_injection, listSyntax.mk_length sequence)
                in
                  boolSyntax.mk_eq
                    (length (listSyntax.mk_append (left, right)),
                     intSyntax.mk_plus (length left, length right))
                end
            else raise ERR "string" "expected an empty sequence argument"
        | (_, [target]) =>
            if Type.compare (Term.type_of target, Type.bool) = EQUAL then
              target
            else raise ERR "string"
              ("CPC string step " ^ name ^
               " omitted its conclusion; tracked replay obligation")
        | _ => raise ERR "string"
            ("CPC string step " ^ name ^
             " omitted its conclusion; tracked replay obligation")
      val target =
        let
          val _ =
            if name = "re_unfold_pos" andalso not (List.null args) then
              raise ERR "string"
                "re_unfold_pos expects no explicit arguments"
            else ()
        in
        case conclusion of
          SOME target => target
        | NONE => inferred_target ()
        end
      (* Only this rung needs the assertion set, and it is reached only after
         the cheaper string rungs have failed, so the flattening stays behind
         a thunk.  ASM_SIMP_TAC turns every context assumption it uses into a
         hypothesis, so the premise conclusions are discharged again against
         the premises themselves; only the tracked assertion and scope
         hypotheses may survive into the replayed theorem. *)
      fun contextual_prove () =
        let
          val context =
            HOLset.listItems (#asserted_hyps state) @ #scope_hyps state @
            List.map Thm.concl prems
        in
          List.foldl (fn (premise, proved) => Drule.PROVE_HYP premise proved)
            (SmtStringProve.string_contextual_prove context target) prems
        end
      fun fail () =
        raise ERR "string"
          ("unsupported CPC string step: rule=" ^ name ^
           "; conclusion=" ^ Library.term_to_string target ^
           "; attempted rungs=[rewrite, theory, contextual]")
      fun concat_unify_prove rev =
        case prems of
          [concat_equality, length_equality] =>
            let
              fun stage label work = work ()
                handle Feedback.HOL_ERR holerr => raise ERR "string"
                  ("concat_unify " ^ label ^ ": " ^
                   Feedback.message_of holerr)
              val from_end =
                if Term.aconv rev boolSyntax.T then true
                else if Term.aconv rev boolSyntax.F then false
                else raise ERR "string"
                  "concat_unify direction argument is not Boolean"
              val (left_string, right_string) =
                boolSyntax.dest_eq (Thm.concl concat_equality)
              val (left_selected, right_selected) = boolSyntax.dest_eq target
              val string_carrier =
                is_smtstr_type (Term.type_of left_string) andalso
                is_smtstr_type (Term.type_of right_string)
              val sequence_carrier =
                Lib.can listSyntax.dest_list_type (Term.type_of left_string)
                andalso Type.compare
                  (Term.type_of left_string, Term.type_of right_string) = EQUAL
              val _ = string_carrier orelse sequence_carrier orelse
                raise ERR "string"
                  "concat_unify expects String or same-element Seq operands"
              val direct =
                if Term.aconv (Thm.concl concat_equality) target then
                  SOME concat_equality
                else if Term.aconv
                    (Thm.concl (Thm.SYM concat_equality)) target then
                  SOME (Thm.SYM concat_equality)
                else NONE
            in
              case direct of
                SOME theorem => theorem
              | NONE =>
                  let
                    val (operator, dest, mk, assoc, empty,
                         nil_left, nil_right) =
                      if string_carrier then
                        let
                          val operator = Term.prim_mk_const
                            {Thy = "smtstring", Name = "smtstr_concat"}
                          fun dest term =
                            case boolSyntax.strip_comb term of
                              (head, [left, right]) =>
                                if Term.aconv head operator then (left, right)
                                else raise ERR "string" "not a String concat"
                            | _ => raise ERR "string" "not a String concat"
                        in
                          (operator, dest,
                           fn (left, right) =>
                             Term.list_mk_comb (operator, [left, right]),
                           smtstringTheory.smtstr_concat_assoc,
                           empty_string (),
                           smtstringTheory.smtstr_concat_nil_left,
                           smtstringTheory.smtstr_concat_nil_right)
                        end
                      else
                        let
                          val element = listSyntax.dest_list_type
                            (Term.type_of left_string)
                          val empty = listSyntax.mk_nil element
                          val operator = Lib.fst (boolSyntax.strip_comb
                            (listSyntax.mk_append (empty, empty)))
                        in
                          (operator, listSyntax.dest_append,
                           listSyntax.mk_append,
                           Thm.SYM
                             (Drule.SPEC_ALL listTheory.APPEND_ASSOC),
                           empty,
                           Thm.CONJUNCT1 listTheory.APPEND,
                           listTheory.APPEND_NIL)
                        end
                    val left_decomposition = stage
                      "left outer-spine decomposition" (fn () =>
                        outer_edge_decomposition operator dest mk assoc
                          empty nil_left nil_right from_end left_string
                          left_selected)
                    val right_decomposition = stage
                      "right outer-spine decomposition" (fn () =>
                        outer_edge_decomposition operator dest mk assoc
                          empty nil_left nil_right from_end right_string
                          right_selected)
                    val canonical_equality = Thm.TRANS
                      (Thm.SYM (#theorem left_decomposition))
                      (Thm.TRANS concat_equality
                        (#theorem right_decomposition))
                    val represented_equality = stage
                      "representation lowering" (fn () =>
                        if string_carrier then
                          Conv.CONV_RULE
                            (Conv.BINOP_CONV (Conv.REWR_CONV
                              smtstringTheory.smtstr_rep_concat))
                            (Thm.AP_TERM
                              (Term.prim_mk_const
                                {Thy = "smtstring", Name = "smtstr_rep"})
                              canonical_equality)
                        else canonical_equality)
                    val represented_length = stage
                      "length normalization" (fn () => Rewrite.REWRITE_RULE
                        [smtstringTheory.smtstr_len_def,
                         integerTheory.INT_OF_NUM_EQ] length_equality)
                    val (left_append, right_append) =
                      boolSyntax.dest_eq (Thm.concl represented_equality)
                    val (left_prefix, left_suffix) = stage
                      "left concat decomposition" (fn () =>
                        listSyntax.dest_append left_append)
                    val (right_prefix, right_suffix) = stage
                      "right concat decomposition" (fn () =>
                        listSyntax.dest_append right_append)
                    val cancellation_schema =
                      if from_end then
                        Thm.CONJUNCT2 listTheory.APPEND_11_LENGTH
                      else Thm.CONJUNCT1 listTheory.APPEND_11_LENGTH
                    val cancellation = stage "cancellation specialization"
                      (fn () => Drule.ISPECL
                        [left_prefix, left_suffix,
                         right_prefix, right_suffix]
                        cancellation_schema)
                    val equivalence = stage "length discharge" (fn () =>
                      let
                        val expected = Lib.fst
                          (boolSyntax.dest_imp (Thm.concl cancellation))
                        val received = Thm.concl represented_length
                        val _ = Term.aconv expected received orelse
                          raise ERR "string"
                            ("expected " ^ Library.term_to_string expected ^
                             "; received " ^
                             Library.term_to_string received)
                      in
                        Thm.MP cancellation represented_length
                      end)
                    val components = stage "append cancellation" (fn () =>
                      Thm.EQ_MP equivalence represented_equality)
                    val represented_result =
                      if from_end then Thm.CONJUNCT2 components
                      else Thm.CONJUNCT1 components
                  in
                    if string_carrier then
                      let
                        val constructor = Term.mk_thy_const
                          {Thy = "smtstring", Name = "SmtStr",
                           Ty = Type.--> (Term.type_of left_prefix,
                             Term.type_of left_selected)}
                      in
                        stage "representation injectivity" (fn () =>
                          Conv.CONV_RULE
                            (Conv.BINOP_CONV (Conv.REWR_CONV
                              smtstringTheory.SmtStr_smtstr_rep))
                            (Thm.AP_TERM constructor represented_result))
                      end
                    else represented_result
                  end
            end
        | _ => raise ERR "string"
            "concat_unify expects equality and length premises"
      fun re_unfold_pos_prove () =
        case prems of
          [membership] =>
            let
              val (membership_head, membership_args) =
                boolSyntax.strip_comb (Thm.concl membership)
              val (string, regex) =
                case membership_args of
                  [string, regex] =>
                    if same_const "smtstring" "smt_in_re" membership_head
                    then (string, regex)
                    else raise ERR "string"
                      "re_unfold_pos premise is not membership"
                | _ => raise ERR "string"
                    "re_unfold_pos premise is not binary membership"
              fun adapt_decomposition source_theorem target =
                let
                  val source_atoms = Drule.CONJUNCTS source_theorem
                  fun literal_equality theorem =
                    let
                      val (head, operands) = boolSyntax.strip_comb
                        (Thm.concl theorem)
                      val regex =
                        case operands of
                          [_, regex] => regex
                        | _ => raise ERR "string"
                            "not a binary membership atom"
                      val to_re =
                        case boolSyntax.strip_comb regex of
                          (to_re, [_]) => to_re
                        | _ => raise ERR "string"
                            "not a literal membership atom"
                      val _ = same_const "smtstring" "smt_in_re" head
                        andalso same_const "smtstring" "reglan_to_re" to_re
                        orelse raise ERR "string"
                          "not a literal membership atom"
                    in
                      Thm.EQ_MP
                        (Conv.REWR_CONV smtstringTheory.smt_in_re_to_re
                          (Thm.concl theorem)) theorem
                    end
                  val literal_equalities = List.mapPartial
                    (Lib.total literal_equality) source_atoms
                  fun exact_literal_rewrite [] _ =
                        raise Conv.UNCHANGED
                    | exact_literal_rewrite (theorem :: rest) term =
                        let
                          val (left, _) = boolSyntax.dest_eq
                            (Thm.concl theorem)
                        in
                          if Term.aconv left term then theorem
                          else exact_literal_rewrite rest term
                        end
                  val rewrite_literals = Conv.DEPTH_CONV
                    (exact_literal_rewrite literal_equalities)
                  val candidates = List.map
                    (Conv.CONV_RULE rewrite_literals)
                    (source_atoms @ literal_equalities)
                  fun prove_atom atom =
                    case List.find
                        (fn theorem => Term.aconv
                          (Thm.concl theorem) atom) candidates of
                      SOME theorem => theorem
                    | NONE => raise ERR "string"
                        ("re_unfold_pos component did not match: " ^
                         Library.term_to_string atom ^ "; available: " ^
                         String.concatWith "; "
                           (List.map (Library.term_to_string o Thm.concl)
                             candidates))
                  val assembled = Drule.LIST_CONJ
                    (List.map prove_atom (boolSyntax.strip_conj target))
                  val reassociate = Drule.CONJUNCTS_AC
                    (Thm.concl assembled, target)
                in
                  Thm.EQ_MP reassociate assembled
                end
              fun expose_preferred theorem = Conv.BETA_RULE
                (Rewrite.PURE_REWRITE_RULE
                  [boolTheory.LET_THM,
                   smtstringTheory.cpc_re_unfold_pos_preferred_def,
                   smtstringTheory.cpc_re_unfold_pos_ordinary_def,
                   smtstringTheory.cpc_re_unfold_pos_endpoints_def]
                  theorem)
              fun normalize_preferred decomposition_regex theorem =
                let
                  val {witness = selector, ...} =
                    CPC_ProofParser.cpc_re_unfold_pos_decomposition
                      string decomposition_regex
                  val selectors = HolKernel.find_terms
                    boolSyntax.is_select (Thm.concl theorem)
                  val _ = List.exists (Term.aconv selector) selectors
                    orelse raise ERR "string"
                      ("re_unfold_pos authoritative selector is absent; " ^
                       "expected " ^ Library.term_to_string selector ^
                       "; found " ^ String.concatWith "; "
                         (List.map Library.term_to_string selectors))
                  val frozen = Term.variant
                    (Term.free_vars (Thm.concl theorem))
                    (Term.mk_var
                      ("re_unfold_pos_frozen_pieces",
                       Term.type_of selector))
                  val protected_string = Term.variant
                    (frozen :: Term.free_vars (Thm.concl theorem))
                    (Term.mk_var
                      ("re_unfold_pos_input", Term.type_of string))
                  val frozen_conclusion = Term.subst
                    [{redex = selector, residue = frozen},
                     {redex = string, residue = protected_string}]
                    (Thm.concl theorem)
                  val string_list_rewrites = Drule.CONJUNCTS
                    smtstringTheory.smtstr_concat_list_def
                  val normalized_frozen = Conv.BETA_RULE
                    (simpLib.SIMP_CONV
                      (simpLib.++
                        (simpLib.++ (boolSimps.bool_ss,
                           numSimps.REDUCE_ss),
                         listSimps.LIST_ss))
                      ([boolTheory.LET_THM,
                        listTheory.GENLIST_NUMERALS,
                        listTheory.GENLIST_AUX,
                        listTheory.LIST_REL_def] @
                       string_list_rewrites)
                      frozen_conclusion)
                  (* LIST simplification exposes the head of a nonempty
                     GENLIST as HD.  CPC's component dictionary names that
                     same projection uniformly as EL 0; restore precisely
                     that surface form while the authoritative SELECT is
                     still protected by [frozen]. *)
                  val hd_to_el0 = Thm.SYM
                    (Drule.SPEC_ALL
                      (Thm.CONJUNCT1 listTheory.EL))
                  val normalized_frozen =
                    Rewrite.PURE_REWRITE_RULE [hd_to_el0]
                      normalized_frozen
                  val normalized = Thm.INST
                    [{redex = frozen, residue = selector},
                     {redex = protected_string, residue = string}]
                    normalized_frozen
                in
                  Thm.EQ_MP normalized theorem
                end
            in
              case boolSyntax.strip_comb regex of
                (star, [body]) =>
                  if same_const "smtstring" "reglan_star" star then
                    let
                      val expanded = concat_regexps [body, regex, body]
                      val expansion = normalize_preferred expanded
                        (expose_preferred (Drule.MATCH_MP
                          smtstringTheory.smt_in_re_star_cpc_preferred
                          membership))
                    in
                      if Term.aconv (Thm.concl expansion) target then expansion
                      else
                        let
                          val normalized_expansion =
                            Rewrite.REWRITE_RULE
                              [smtstringTheory.smtstr_concat_assoc]
                              expansion
                          val (source_empty, source_rest) =
                            boolSyntax.dest_disj
                              (Thm.concl normalized_expansion)
                          val (source_single, source_decomposition) =
                            boolSyntax.dest_disj source_rest
                          val (target_empty, target_rest) =
                            boolSyntax.dest_disj target
                          val (target_single, target_decomposition) =
                            boolSyntax.dest_disj target_rest
                          val _ = Term.aconv source_empty target_empty orelse
                            raise ERR "string"
                              "re_unfold_pos empty arm mismatch"
                          val _ = Term.aconv source_single target_single orelse
                            raise ERR "string"
                              "re_unfold_pos single-match arm mismatch"
                          val decomposition = adapt_decomposition
                            (Thm.ASSUME source_decomposition)
                            target_decomposition
                          val empty_case = Thm.DISJ1
                            (Thm.ASSUME source_empty) target_rest
                          val single_case = Thm.DISJ2 target_empty
                            (Thm.DISJ1 (Thm.ASSUME source_single)
                              target_decomposition)
                          val decomposition_case = Thm.DISJ2 target_empty
                            (Thm.DISJ2 target_single decomposition)
                          val rest_case = Thm.DISJ_CASES
                            (Thm.ASSUME source_rest) single_case
                            decomposition_case
                        in
                          Thm.DISJ_CASES normalized_expansion empty_case
                            rest_case
                        end
                    end
                  else raise ERR "string"
                    "re_unfold_pos expects star or concatenation membership"
              | (concat, [_, _]) =>
                  if same_const "smtstring" "reglan_concat" concat then
                    let
                      val regex_operator = Term.prim_mk_const
                        {Thy = "smtstring", Name = "reglan_concat"}
                      fun dest_regex term =
                        case boolSyntax.strip_comb term of
                          (head, [left, right]) =>
                            if Term.aconv head regex_operator then
                              (left, right)
                            else raise ERR "string" "not a regex concat"
                        | _ => raise ERR "string" "not a regex concat"
                      val regexps =
                        CPC_ProofParser.cpc_re_unfold_pos_regexps regex
                      fun mk_regex (left, right) = Term.list_mk_comb
                        (regex_operator, [left, right])
                      val regex_canonical =
                        regex_components_right_canonical dest_regex
                          mk_regex regex regexps
                      val regex_list = listSyntax.mk_list
                        (regexps, Term.type_of (List.hd regexps))
                      val nonempty = boolSyntax.mk_neg
                        (boolSyntax.mk_eq (regex_list,
                          listSyntax.mk_nil (Term.type_of
                            (List.hd regexps))))
                      val nonempty = Drule.EQT_ELIM
                        (computeLib.EVAL_CONV nonempty)
                      val normalized_membership = Thm.EQ_MP
                        (Thm.SPEC string regex_canonical) membership
                      val choice_theorem =
                        smtstringTheory.smt_in_re_concat_list_cpc_preferred
                      val free_variables =
                        Term.free_vars (Thm.concl choice_theorem)
                      val regex_list_variable = valOf (List.find
                        (fn variable => Type.compare
                          (Term.type_of variable,
                           Term.type_of regex_list) = EQUAL)
                        free_variables)
                      val string_variable = valOf (List.find
                        (fn variable => Type.compare
                          (Term.type_of variable,
                           Term.type_of string) = EQUAL)
                        free_variables)
                      (* [string] may itself contain an unrelated component
                         selector.  Protect it before simplifying the outer
                         regex-list premise, so the inner selector remains
                         byte-for-byte unchanged. *)
                      val protected_string = Term.variant
                        (Term.free_vars string @ free_variables)
                        (Term.mk_var
                          ("re_unfold_pos_input", Term.type_of string))
                      val choice_theorem = Thm.INST
                        [{redex = regex_list_variable,
                          residue = regex_list},
                         {redex = string_variable,
                          residue = protected_string}]
                        choice_theorem
                      val reglan_list_rewrites = Drule.CONJUNCTS
                        smtstringTheory.reglan_concat_list_def
                      val choice_theorem = Conv.BETA_RULE
                        (Rewrite.PURE_REWRITE_RULE
                          (reglan_list_rewrites @
                           [listTheory.list_case_def,
                            listTheory.LENGTH]) choice_theorem)
                      val choice_theorem = simpLib.SIMP_RULE
                        (simpLib.++
                          (boolSimps.bool_ss, numSimps.REDUCE_ss))
                        [] choice_theorem
                      val choice_theorem = Thm.INST
                        [{redex = protected_string, residue = string}]
                        choice_theorem
                      val expected_premise = Lib.fst
                        (boolSyntax.dest_imp (Thm.concl choice_theorem))
                      val choice_premise =
                        if Term.aconv expected_premise
                            (Thm.concl normalized_membership) then
                          normalized_membership
                        else Thm.CONJ nonempty normalized_membership
                      val _ = Term.aconv expected_premise
                        (Thm.concl choice_premise) orelse
                        raise ERR "string"
                          ("re_unfold_pos n-ary premise mismatch: expected " ^
                           Library.term_to_string expected_premise ^
                           "; received " ^ Library.term_to_string
                             (Thm.concl choice_premise))
                      val raw_expansion = Drule.MATCH_MP
                        choice_theorem choice_premise
                      (* Expose the one preferred selector, then freeze it
                         while normalizing only the decomposition it carries. *)
                      val expansion = normalize_preferred regex
                        (expose_preferred raw_expansion)
                    in
                      if Term.aconv (Thm.concl expansion) target then expansion
                      else adapt_decomposition expansion target
                    end
                  else raise ERR "string"
                    "re_unfold_pos expects star or concatenation membership"
              | _ => raise ERR "string"
                  "re_unfold_pos expects star or concatenation membership"
            end
        | _ => raise ERR "string" "re_unfold_pos expects one premise"
      fun string_reduction_prove () =
        case args of
          [substring] =>
            let
              val theorem = substring_reduction_theorem substring
              val normalized_theorem = Rewrite.PURE_REWRITE_RULE
                [integerTheory.int_ge, integerTheory.int_gt] theorem
              val normalization = Rewrite.PURE_REWRITE_CONV
                [integerTheory.int_ge, integerTheory.int_gt] target
              val normalized = boolSyntax.rhs (Thm.concl normalization)
            in
              if Term.aconv (Thm.concl normalized_theorem) normalized then
                Thm.EQ_MP (Thm.SYM normalization) normalized_theorem
              else raise ERR "string_reduction"
                ("certificate conclusion differs from the checked schema: " ^
                 Library.term_to_string target ^ "; normalized to: " ^
                 Library.term_to_string normalized ^ "; expected: " ^
                 Library.term_to_string (Thm.concl normalized_theorem))
            end
        | _ => raise ERR "string_reduction"
            "expected exactly one substring argument"
      fun re_loop_elim_prove () =
        let
          val _ = List.null prems orelse raise ERR "re-loop-elim"
            "expected no premises"
          val (source, destination) = dest_reglan_equiv target
          val (loop_head, loop_args) = boolSyntax.strip_comb source
          val (regex, lower, upper) =
            if same_const "smtstring" "reglan_loop" loop_head then
              case loop_args of
                [regex, lower, upper] => (regex, lower, upper)
              | _ => raise ERR "re-loop-elim" "re.loop has wrong arity"
            else raise ERR "re-loop-elim"
              "source is not a regular-expression loop"
          val _ = Term.aconv lower upper orelse raise ERR "re-loop-elim"
            "only exact finite loops have a concatenation expansion"
          val count = numSyntax.dest_numeral upper
            handle Feedback.HOL_ERR _ => raise ERR "re-loop-elim"
              "loop bound is not a numeral"
          val count_int = Arbnum.toInt count
            handle Overflow => raise ERR "re-loop-elim"
              "loop bound is too large to replay"
          fun exact theorem expected =
            if Term.aconv (Thm.concl theorem) expected then theorem
            else raise ERR "re-loop-elim"
              ("derived theorem does not match the certificate target: " ^
               Library.term_to_string (Thm.concl theorem) ^ "; expected " ^
               Library.term_to_string expected)
          fun instantiate theorem expected =
            let
              val generic = Drule.SPEC_ALL theorem
            in
              Drule.INST_TY_TERM
                (Term.match_term (Thm.concl generic) expected) generic
            end
          fun equivalent left right =
            Term.list_mk_comb (reglan_equiv_tm, [left, right])
          fun power n = Term.list_mk_comb
            (``reglan_power``, [regex, numSyntax.mk_numeral
              (Arbnum.fromInt n)])
          fun concat left right =
            binary_app "smtstring" "reglan_concat" left right
          fun power_expansion 0 result =
                let
                  val theorem = instantiate
                    smtstringTheory.reglan_equiv_power_zero
                    (equivalent (power 0) result)
                in exact theorem (equivalent (power 0) result) end
            | power_expansion 1 result =
                let
                  val theorem = instantiate
                    smtstringTheory.reglan_equiv_power_one
                    (equivalent (power 1) result)
                in exact theorem (equivalent (power 1) result) end
            | power_expansion n result =
                let
                  val (head, operands) = boolSyntax.strip_comb result
                  val (first, rest) =
                    if same_const "smtstring" "reglan_concat" head then
                      case operands of
                        [first, rest] => (first, rest)
                      | _ => raise ERR "re-loop-elim"
                          "expanded concatenation has wrong arity"
                    else raise ERR "re-loop-elim"
                      "expanded loop is not a concatenation"
                  val _ = Term.aconv first regex orelse
                    raise ERR "re-loop-elim"
                      "expanded loop changes its repeated expression"
                  val tail = power_expansion (n - 1) rest
                  val lifted = Drule.MATCH_MP
                    smtstringTheory.reglan_concat_equiv
                    (Thm.CONJ (replay_reglan_refl regex) tail)
                  val predecessor = numSyntax.mk_numeral
                    (Arbnum.fromInt (n - 1))
                  val raw_step_target = equivalent
                    (Term.list_mk_comb
                      (``reglan_power``,
                       [regex, numSyntax.mk_suc predecessor]))
                    (concat regex (power (n - 1)))
                  val step = reduceLib.REDUCE_RULE (instantiate
                    smtstringTheory.reglan_equiv_power_suc raw_step_target)
                  val theorem = replay_reglan_trans step lifted
                in exact theorem (equivalent (power n) result) end
          val loop_to_power = replay_reglan_sym (instantiate
            smtstringTheory.reglan_equiv_power_loop
            (equivalent (power count_int) source))
          val theorem = replay_reglan_trans loop_to_power
            (power_expansion count_int destination)
        in exact theorem target end
      val is_substring_reduction =
        name = "string_reduction" andalso
        (case args of
           [substring] => Lib.can substring_reduction_theorem substring
         | _ => false)
      val is_string_eager_reduction =
        name = "string_eager_reduction" andalso
        (case args of
           [argument] => Lib.can string_eager_reduction_theorem argument
         | _ => false)
    in
      (* `str` is cvc5's macro name for both String and Seq theory steps.
         Dispatch on HOL's carrier, rather than the macro spelling, so the
         Phase-4 String route remains unchanged. *)
      if name = "concat_unify" then
        profile "CPC(rung:string/concat_unify)" concat_unify_prove
          (Lib.singleton_of_list args handle Feedback.HOL_ERR _ =>
            raise ERR "string"
              "concat_unify expects one direction argument")
      else if name = "re_unfold_pos" then
        profile "CPC(rung:string/re_unfold_pos)"
          re_unfold_pos_prove ()
      else if is_substring_reduction then
        profile "CPC(rung:string/string_reduction)"
          string_reduction_prove ()
      else if is_string_eager_reduction then
        profile "CPC(rung:string/string_eager_reduction)"
          string_eager_reduction_theorem (List.hd args)
      else if name = "string_length_pos" then
        profile "CPC(rung:string/string_length_pos)"
          (fn string => string_length_pos_theorem string)
          (expect_one_arg "string_length_pos" args)
      else if name = "re-loop-elim" then
        profile "CPC(rung:string/re-loop-elim)"
          re_loop_elim_prove ()
      else if SmtSeqProve.has_seq_type target then
        let
          val context =
            HOLset.listItems (#asserted_hyps state) @ #scope_hyps state @
            List.map Thm.concl prems
          val thm = profile "CPC(rung:string/seq_contextual)"
            (fn target =>
              SmtSeqProve.seq_prove target
              handle Feedback.HOL_ERR holerr =>
                if SmtResource.is_resource_gate holerr then
                  raise Feedback.HOL_ERR holerr
                else
                  SmtSeqProve.seq_contextual_prove context target) target
        in
          List.foldl (fn (premise, proved) => Drule.PROVE_HYP premise proved)
            thm prems
        end
      else
        profile "CPC(rung:string/rewrite)"
          SmtStringProve.string_rewrite_prove target
        handle Feedback.HOL_ERR _ =>
        profile "CPC(rung:string/theory)"
          (SmtStringProve.string_prove arith_prove) target
        handle Feedback.HOL_ERR _ =>
        profile "CPC(rung:string/contextual)" contextual_prove ()
        handle Feedback.HOL_ERR _ =>
        profile "CPC(rung:string/unsupported)" fail ()
    end

  fun apply_native_const const args =
    let
      fun apply_one (arg, rator) =
        let
          val (domain, _) = Type.dom_rng (Term.type_of rator)
        in
          Term.mk_comb (Term.inst
            (Type.match_type domain (Term.type_of arg)) rator, arg)
        end
    in
      List.foldl apply_one const args
    end

  fun rare_string_expected_target name args =
    let
      fun app thy constant arguments = apply_native_const
        (Term.prim_mk_const {Thy = thy, Name = constant}) arguments
      fun is_empty_string tm =
        case boolSyntax.strip_comb tm of
          (head, [chars]) =>
            (case Lib.total Term.dest_thy_const head of
               SOME {Thy = "smtstring", Name = "SmtStr", ...} =>
                 listSyntax.is_nil chars
             | _ => false)
        | _ => false
      fun is_string tm = is_smtstr_type (Term.type_of tm)
      fun concat_two (left, right) =
        if is_string left then app "smtstring" "smtstr_concat" [left, right]
        else listSyntax.mk_append (left, right)
      fun concat [] = raise ERR name "expected a nonempty concat operand list"
        | concat (first :: rest) = List.foldl
            (fn (right, left) => concat_two (left, right)) first rest
      fun list_arg tm =
        case Lib.total listSyntax.dest_list tm of
          SOME (terms, _) => terms
        | NONE => if is_empty_string tm then [] else [tm]
      fun length sequence =
        if is_string sequence then app "smtstring" "smtstr_len" [sequence]
        else Term.mk_comb
          (intSyntax.int_injection, listSyntax.mk_length sequence)
      fun contains (sequence, sub) =
        if is_string sequence then
          app "smtstring" "smtstr_contains" [sequence, sub]
        else app "rich_list" "IS_SUBLIST" [sequence, sub]
      fun prefixof (prefix, sequence) =
        if is_string prefix then
          app "smtstring" "smtstr_prefixof" [prefix, sequence]
        else app "rich_list" "IS_PREFIX" [sequence, prefix]
      fun substr (sequence, start, count) =
        if is_string sequence then
          app "smtstring" "smtstr_substr" [sequence, start, count]
        else app "HolSmt" "smt_seq_extract" [sequence, start, count]
      fun replace (sequence, pattern, replacement) =
        if is_string sequence then app "smtstring" "smtstr_replace"
          [sequence, pattern, replacement]
        else app "HolSmt" "smt_seq_replace"
          [sequence, pattern, replacement]
      fun replace_all (sequence, pattern, replacement) =
        if is_string sequence then app "smtstring" "smtstr_replace_all"
          [sequence, pattern, replacement]
        else app "HolSmt" "smt_seq_replace_all"
          [sequence, pattern, replacement]
      fun update (sequence, index, replacement) =
        if is_string sequence then app "smtstring" "smtstr_update"
          [sequence, index, replacement]
        else app "HolSmt" "smt_seq_update" [sequence, index, replacement]
      fun empty sequence =
        if is_string sequence then app "smtstring" "SmtStr"
          [listSyntax.mk_nil numSyntax.num]
        else listSyntax.mk_nil (listSyntax.eltype sequence)
      fun eq (left, right) = boolSyntax.mk_eq (left, right)
      fun checked label action = action ()
        handle Feedback.HOL_ERR holerr =>
          raise ERR name (label ^ ": " ^ Feedback.message_of holerr)
      fun concat_context xs z zs = concat (list_arg xs @ z :: list_arg zs)
      fun bad_shape () = raise ERR name
        ("cvc5-1.3.4 RARE rule " ^ name ^
         " received the wrong argument shape")
    in
      case (name, args) of
        ("str-contains-split-char", [x, y, zs, w]) =>
          let
            val tail = y :: list_arg zs
            val suffix = checked "split suffix" (fn () => concat tail)
            val whole = checked "split whole" (fn () => concat (x :: tail))
            val whole_contains = checked "split whole contains"
              (fn () => contains (whole, w))
            val left_contains = checked "split left contains"
              (fn () => contains (x, w))
            val right_contains = checked "split right contains"
              (fn () => contains (suffix, w))
          in
            checked "split equality" (fn () => eq (whole_contains,
              boolSyntax.mk_disj (left_contains, right_contains)))
          end
      | ("str-contains-concat-find", [xs, z, y, zs]) =>
          eq (contains (concat_context xs z zs, y), boolSyntax.T)
      | ("str-contains-concat-find-contra", [xs, z, y, zs]) =>
          eq (contains (y, concat_context xs z zs), boolSyntax.F)
      | ("str-contains-leq-len-eq", [x, y]) =>
          eq (contains (x, y), eq (x, y))
      | ("str-contains-emp", [x, y]) =>
          eq (contains (x, y), boolSyntax.T)
      | ("str-contains-char", [x, y]) =>
          eq (contains (x, y),
            boolSyntax.mk_disj (eq (empty x, y), eq (x, y)))
      | ("str-contains-char", [x, y, _]) =>
          rare_string_expected_target name [x, y]
      | ("str-len-replace-inv", [t, s, r]) =>
          eq (length (replace (t, s, r)), length t)
      | ("str-len-replace-all-inv", [t, s, r]) =>
          eq (length (replace_all (t, s, r)), length t)
      | ("str-len-update-inv", [t, n, r]) =>
          eq (length (update (t, n, r)), length t)
      | ("str-len-substr-in-range", [s, n, m]) =>
          eq (length (substr (s, n, m)), m)
      | ("str-len-concat-rec", [s1, s2, s3]) =>
          let val tail = s2 :: list_arg s3 in
            eq (length (concat (s1 :: tail)),
              intSyntax.mk_plus (length s1, length (concat tail)))
          end
      | ("str-len-eq-zero-concat-rec", [s1, s2, s3]) =>
          let val tail = s2 :: list_arg s3 in
            eq (eq (length (concat (s1 :: tail)), intSyntax.zero_tm),
              boolSyntax.mk_conj (eq (s1, empty s1),
                eq (length (concat tail), intSyntax.zero_tm)))
          end
      | ("str-len-eq-zero-concat-rec", [s1, s2, s3, _]) =>
          rare_string_expected_target name [s1, s2, s3]
      | ("str-len-eq-zero-base", [s]) =>
          eq (eq (length s, intSyntax.zero_tm), eq (s, empty s))
      | ("str-len-eq-zero-base", [s, _]) =>
          rare_string_expected_target name [s]
      | ("str-prefixof-elim", [s, t]) =>
          eq (prefixof (s, t),
            eq (s, substr (t, intSyntax.zero_tm, length s)))
      | ("str-prefixof-eq", [s, t]) =>
          eq (prefixof (s, t), eq (s, t))
      | ("str-prefixof-one", [s, t]) =>
          eq (prefixof (s, t), contains (t, s))
      | _ => bad_shape ()
    end

  fun replay_contains_split_char prems conclusion args =
    case prems of
      [length_one] =>
        let
          fun phase label action = action ()
            handle Feedback.HOL_ERR holerr =>
              raise ERR "str-contains-split-char"
                (label ^ ": " ^ Feedback.message_of holerr)
          fun typed tm = Library.term_to_string tm ^ " : " ^
            Parse.type_to_string (Term.type_of tm)
          val expected = phase "could not derive the exact conclusion"
            (fn () => rare_string_expected_target
              "str-contains-split-char" args)
            handle Feedback.HOL_ERR holerr =>
              raise ERR "str-contains-split-char"
                (Feedback.message_of holerr ^ "; args=[" ^
                 String.concatWith ", " (List.map typed args) ^ "]")
          fun length sequence =
            if is_smtstr_type (Term.type_of sequence) then
              Term.mk_comb
                (Term.prim_mk_const
                  {Thy = "smtstring", Name = "smtstr_len"}, sequence)
            else Term.mk_comb
              (intSyntax.int_injection, listSyntax.mk_length sequence)
          val expected_premise = phase "could not derive the length premise"
            (fn () =>
            case args of
              [_, _, _, needle] => boolSyntax.mk_eq
                (length needle, intSyntax.one_tm)
            | _ => raise ERR "str-contains-split-char"
                "received the wrong argument shape")
          val _ = Term.aconv (Thm.concl length_one) expected_premise orelse
            raise ERR "str-contains-split-char"
              "length premise does not match the needle argument"
          val target = case conclusion of
              NONE => expected
            | SOME target =>
                if Term.aconv target expected then target
                else raise ERR "str-contains-split-char"
                  "conclusion does not match its exact argument recipe"
          val theorem = phase "could not prove the exact conclusion" (fn () =>
            if SmtSeqProve.has_seq_type target then
              Tactical.TAC_PROOF
                (([Thm.concl length_one], target),
                 bossLib.ASM_SIMP_TAC (bossLib.srw_ss ())
                   [smtstringTheory.IS_SUBLIST_APPEND_len_one,
                    listTheory.APPEND_ASSOC])
            else Tactical.TAC_PROOF
              (([Thm.concl length_one], target),
               bossLib.ASM_SIMP_TAC (bossLib.srw_ss ())
                 [smtstringTheory.smtstr_contains_concat_len_one,
                  smtstringTheory.smtstr_concat_assoc]))
        in
          Drule.PROVE_HYP length_one theorem
        end
    | _ => raise ERR "str-contains-split-char"
        "expected exactly one length-one premise"

  fun rare_string_expected_premises name args =
    let
      fun app thy constant arguments = apply_native_const
        (Term.prim_mk_const {Thy = thy, Name = constant}) arguments
      fun is_string tm = is_smtstr_type (Term.type_of tm)
      fun length sequence =
        if is_string sequence then app "smtstring" "smtstr_len" [sequence]
        else Term.mk_comb
          (intSyntax.int_injection, listSyntax.mk_length sequence)
      fun contains (sequence, sub) =
        if is_string sequence then
          app "smtstring" "smtstr_contains" [sequence, sub]
        else app "rich_list" "IS_SUBLIST" [sequence, sub]
      fun eq (left, right) = boolSyntax.mk_eq (left, right)
      fun true_eq proposition = eq (proposition, boolSyntax.T)
      fun geq (left, right) = intSyntax.mk_geq (left, right)
      fun bad_shape () = raise ERR name
        ("cvc5-1.3.4 RARE rule " ^ name ^
         " received the wrong argument shape")
    in
      case (name, args) of
        ("str-contains-concat-find", [_, z, y, _]) =>
          [true_eq (contains (z, y))]
      | ("str-contains-concat-find-contra", [_, z, y, _]) =>
          [eq (contains (y, z), boolSyntax.F)]
      | ("str-contains-leq-len-eq", [x, y]) =>
          [true_eq (geq (length y, length x))]
      | ("str-contains-emp", [_, y]) =>
          [eq (length y, intSyntax.zero_tm)]
      | ("str-contains-char", [x, _]) =>
          [eq (length x, intSyntax.one_tm)]
      | ("str-contains-char", [x, y, _]) =>
          rare_string_expected_premises name [x, y]
      | ("str-len-replace-inv", [_, s, r]) =>
          [eq (length s, length r)]
      | ("str-len-replace-all-inv", [_, s, r]) =>
          [eq (length s, length r)]
      | ("str-len-substr-in-range", [s, n, m]) =>
          [true_eq (geq (n, intSyntax.zero_tm)),
           true_eq (geq (m, intSyntax.zero_tm)),
           true_eq (geq (length s, intSyntax.mk_plus (n, m)))]
      | ("str-prefixof-eq", [s, t]) =>
          [true_eq (geq (length s, length t))]
      | ("str-prefixof-one", [_, t]) =>
          [eq (length t, intSyntax.one_tm)]
      | ("str-len-update-inv", [_, _, _]) => []
      | ("str-len-concat-rec", [_, _, _]) => []
      | ("str-len-eq-zero-concat-rec", [_, _, _]) => []
      | ("str-len-eq-zero-concat-rec", [_, _, _, _]) => []
      | ("str-len-eq-zero-base", [_]) => []
      | ("str-len-eq-zero-base", [_, _]) => []
      | ("str-prefixof-elim", [_, _]) => []
      | _ => bad_shape ()
    end

  fun replay_inventory_string_rule name prems conclusion args =
    let
      val expected = rare_string_expected_target name args
        handle Feedback.HOL_ERR holerr =>
          let val message = Feedback.message_of holerr in
            if String.isSubstring "received the wrong argument shape" message
            then raise Feedback.HOL_ERR holerr
            else raise ERR name
              ("cvc5-1.3.4 RARE rule " ^ name ^
               " received type-incompatible arguments")
          end
      val target = case conclusion of
          SOME target =>
            if Term.aconv target expected then target
            else raise ERR name
              ("cvc5-1.3.4 RARE rule " ^ name ^
               " conclusion does not match its exact argument recipe")
        | NONE => expected
      val expected_premises = rare_string_expected_premises name args
      val actual_premises = List.map Thm.concl prems
      val _ = ListPair.allEq (fn (actual, expected) =>
          Term.aconv actual expected)
        (actual_premises, expected_premises) orelse raise ERR name
          ("cvc5-1.3.4 RARE rule " ^ name ^
           " premises do not match its exact argument recipe")
      val context = List.map Thm.concl prems
      val theorem =
        if SmtSeqProve.has_seq_type target then
          (SmtSeqProve.seq_prove target
           handle Feedback.HOL_ERR holerr =>
             if SmtResource.is_resource_gate holerr then
               raise Feedback.HOL_ERR holerr
             else SmtSeqProve.seq_contextual_prove context target)
        else
          (SmtStringProve.string_rewrite_prove target
           handle Feedback.HOL_ERR holerr =>
             if SmtResource.is_resource_gate holerr then
               raise Feedback.HOL_ERR holerr
             else SmtStringProve.string_contextual_prove context target)
    in
      List.foldl
        (fn (premise, proved) => Drule.PROVE_HYP premise proved)
        theorem prems
    end

  (* A theorem's hypotheses are a set, so HOL does not retain their source
     order.  Compare them as an exact alpha-equivalence multiset: counts are
     preserved, and removal follows HOL's deterministic hypothesis order. *)
  fun same_alpha_hypotheses expected actual =
    let
      fun remove _ [] = NONE
        | remove target (candidate :: rest) =
            if Term.aconv target candidate then SOME rest
            else Option.map (fn remaining => candidate :: remaining)
              (remove target rest)
      fun consume [] remaining = List.null remaining
        | consume (target :: rest) remaining =
            (case remove target remaining of
               SOME remaining => consume rest remaining
             | NONE => false)
    in
      List.length expected = List.length actual andalso
      consume expected actual
    end

  fun alpha_union terms =
    List.foldl (fn (term, accumulated) =>
      if List.exists (Term.aconv term) accumulated then accumulated
      else term :: accumulated) [] terms

  fun discharge_rare_inventory_contract name prems synthesized =
    let
      val expected_premises = Thm.hyp synthesized
      val supplied_premises = List.map Thm.concl prems
      val _ = same_alpha_hypotheses expected_premises supplied_premises
        orelse raise ERR name
          ("cvc5-1.3.4 RARE rule " ^ name ^
           " premises do not match its synthesized theorem hypotheses")
      val discharged = List.foldl
        (fn (premise, theorem) => Drule.PROVE_HYP premise theorem)
        synthesized prems
      val expected_final_hypotheses = alpha_union
        (List.concat (List.map Thm.hyp prems))
      val _ = same_alpha_hypotheses expected_final_hypotheses
          (Thm.hyp discharged) orelse
        raise ERR name
          ("cvc5-1.3.4 RARE rule " ^ name ^
           " violated its final hypothesis contract")
    in
      discharged
    end

  datatype rare_source_sexp =
      RareAtom of string
    | RareList of rare_source_sexp list

  fun parse_rare_source_sexp source =
    let
      fun space #"(" = " ( "
        | space #")" = " ) "
        | space character = String.str character
      val tokens = String.tokens Char.isSpace (String.translate space source)
      fun parse ("(" :: rest) =
            let
              fun items accumulated (")" :: rest) =
                    (RareList (List.rev accumulated), rest)
                | items _ [] = raise ERR "parse_rare_source_sexp"
                    "unterminated declarative RARE expression"
                | items accumulated tokens =
                    let val (item, rest) = parse tokens in
                      items (item :: accumulated) rest
                    end
              val (items, rest) = items [] rest
            in
              (items, rest)
            end
        | parse (")" :: _) = raise ERR "parse_rare_source_sexp"
            "unexpected ')' in declarative RARE expression"
        | parse (token :: rest) = (RareAtom token, rest)
        | parse [] = raise ERR "parse_rare_source_sexp"
            "empty declarative RARE expression"
      val (result, rest) = parse tokens
    in
      if List.null rest then result
      else raise ERR "parse_rare_source_sexp"
        "trailing tokens in declarative RARE expression"
    end

  val (_, rare_source_base_tmdict) =
    SmtLib_Logics.parsedicts_of_logic "ALL"
  val rare_source_tmdict = Library.union_dict rare_source_base_tmdict
    SmtLib_Theories.CVC5_Seq.tmdict

  fun rare_source_empty carrier =
    if is_smtstr_type (Term.type_of carrier) then
      Term.mk_comb
        (Term.prim_mk_const {Thy = "smtstring", Name = "SmtStr"},
         listSyntax.mk_nil numSyntax.num)
    else if listSyntax.is_list_type (Term.type_of carrier) then
      listSyntax.mk_nil (listSyntax.eltype carrier)
    else raise ERR "rare_source_empty"
      "expected a String or Seq carrier"

  fun rare_source_is_empty carrier =
    if is_smtstr_type (Term.type_of carrier) then
      (case boolSyntax.strip_comb carrier of
         (head, [characters]) =>
           (case Lib.total Term.dest_thy_const head of
              SOME {Thy = "smtstring", Name = "SmtStr", ...} =>
                listSyntax.is_nil characters
            | _ => false)
       | _ => false)
    else listSyntax.is_list_type (Term.type_of carrier) andalso
      listSyntax.is_nil carrier

  fun rare_source_structured_wrapper
      ({provenance, ...} : located_term) =
    case provenance of
      UnavailableProvenance "CPC structured-list metadata" => true
    | UnavailableProvenance "CPC structured-list alias" => true
    | _ => false

  fun rare_source_fixed_type source =
    case source of
      RareSourceString => SOME (Term.type_of ``SmtStr []``)
    | RareSourceRegex => SOME (reglan_ty)
    | RareSourceInt => SOME intSyntax.int_ty
    | RareSourceSeq => NONE
    | RareSourceElement => NONE

  fun rare_source_aggregate_name aggregate carrier_ty =
    case aggregate of
      RareSourceSeqConcat =>
        if is_smtstr_type carrier_ty then "str.++"
        else if listSyntax.is_list_type carrier_ty then "seq.++"
        else raise ERR "rare_source_aggregate_name"
          "sequence concatenation has a non-String/non-Seq carrier"
    | RareSourceRegexConcat => "re.++"
    | RareSourceRegexUnion => "re.union"
    | RareSourceRegexInter => "re.inter"

  fun rare_source_aggregate_head provenance =
    case provenance of
      ApplicationProvenance (head, operands) =>
        if List.exists (Lib.equal head)
             ["str.++", "seq.++", "re.++", "re.union", "re.inter"]
        then SOME (head, List.length operands)
        else NONE
    | _ => NONE

  fun rare_source_identity aggregate carrier =
    let
      fun constant symbol =
        SmtLib_Parser.apply_term rare_source_tmdict symbol [] []
      fun empty_string () =
        Term.mk_comb
          (Term.prim_mk_const {Thy = "smtstring", Name = "SmtStr"},
           listSyntax.mk_nil numSyntax.num)
    in
      case aggregate of
        RareSourceSeqConcat => rare_source_is_empty carrier
      | RareSourceRegexConcat => Term.aconv carrier
          (SmtLib_Parser.apply_term rare_source_tmdict "str.to_re" []
            [empty_string ()])
      | RareSourceRegexUnion => Term.aconv carrier (constant "re.none")
      | RareSourceRegexInter => Term.aconv carrier (constant "re.all")
    end

  fun rare_source_binary_head aggregate carrier_ty term =
    let
      val (head, operands) = boolSyntax.strip_comb term
      val expected =
        case aggregate of
          RareSourceSeqConcat =>
            if is_smtstr_type carrier_ty then
              {Thy = "smtstring", Name = "smtstr_concat"}
            else {Thy = "list", Name = "APPEND"}
        | RareSourceRegexConcat =>
            {Thy = "smtstring", Name = "reglan_concat"}
        | RareSourceRegexUnion =>
            {Thy = "smtstring", Name = "reglan_union"}
        | RareSourceRegexInter =>
            {Thy = "smtstring", Name = "reglan_inter"}
    in
      case (Lib.total Term.dest_thy_const head, operands) of
        (SOME {Thy, Name, ...}, [left, right]) =>
          if Thy = #Thy expected andalso Name = #Name expected
          then SOME (left, right)
          else NONE
      | _ => NONE
    end

  (* cvc5 serializes a :list substitution as its aggregate term, not as a
     synthetic @list.  The source metadata names that aggregate explicitly.
     Its outer variadic application denotes the exact lexical operands, a
     bare identity denotes [], and every other carrier term is a singleton.
     Application provenance is authoritative for the outer boundary because
     HOL elaboration left-folds variadic operators and erases unary
     wrappers. *)
  fun rare_source_native_list name formal aggregate
      ({term, provenance} : located_term) =
    let
      val carrier_ty = Term.type_of term
      val expected_head = rare_source_aggregate_name aggregate carrier_ty
      fun wrong message = raise ERR name
        ("cvc5-1.3.4 RARE rule " ^ name ^ " formal " ^ formal ^ " " ^
         message)
      fun split width aggregate_term =
        if width = 1 then [aggregate_term]
        else if width > 1 then
          (case rare_source_binary_head aggregate carrier_ty aggregate_term of
             SOME (left, right) => split (width - 1) left @ [right]
           | NONE => wrong
               "has aggregate syntax inconsistent with its operands")
        else wrong "has an empty aggregate application"
    in
      case rare_source_aggregate_head provenance of
        SOME (actual_head, width) =>
          if actual_head <> expected_head then
            wrong ("uses mismatched aggregate " ^ actual_head ^
              " instead of " ^ expected_head)
          else split width term
      | NONE => if rare_source_identity aggregate term then [] else [term]
    end

  fun normalize_rare_source_arguments name formals located_args =
    let
      fun is_string_sort_marker ({term, ...} : located_term) =
        case Lib.total Term.dest_var term of
          SOME (marker, ty) => marker = "@cpc.String" andalso
            is_smtstr_type ty
        | NONE => false
      val has_sequence_formal = List.exists
        (fn (_, _, source) => source = RareSourceSeq) formals
      val located_args =
        if has_sequence_formal andalso
           List.length located_args = List.length formals + 1 andalso
           is_string_sort_marker (List.last located_args)
        then List.take (located_args, List.length formals)
        else located_args
      val _ = List.length formals = List.length located_args orelse
        raise ERR name
          ("cvc5-1.3.4 RARE rule " ^ name ^
           " received the wrong argument count")
      fun wrong formal message = raise ERR name
        ("cvc5-1.3.4 RARE rule " ^ name ^ " formal " ^ formal ^ " " ^
         message)
      fun list_parts formal aggregate (located : located_term) =
        if rare_source_structured_wrapper located then
          (case Lib.total listSyntax.dest_list (#term located) of
             SOME parts => parts
           | NONE => wrong formal "has malformed CPC list metadata")
        else
          (rare_source_native_list name formal aggregate located,
           Term.type_of (#term located))
      fun seq_candidate ((formal, kind, source), located : located_term) =
        if source <> RareSourceSeq then NONE
        else case kind of
          RareSourceTerm =>
            if rare_source_structured_wrapper located then NONE
            else SOME (Term.type_of (#term located))
        | RareSourceList aggregate =>
            let val (elements, element_ty) =
              list_parts formal aggregate located
            in
              if List.null elements andalso Type.is_vartype element_ty
              then NONE
              else if List.null elements then SOME element_ty
              else SOME (Term.type_of (List.hd elements))
            end
        | RareSourceIndex => NONE
      val seq_candidates = List.mapPartial seq_candidate
        (ListPair.zip (formals, located_args))
      val seq_type = case seq_candidates of
          [] => NONE
        | first :: rest =>
            if List.all (fn candidate =>
                 Type.compare (first, candidate) = EQUAL) rest
            then SOME first
            else raise ERR name
              ("cvc5-1.3.4 RARE rule " ^ name ^
               " has inconsistent Seq carriers")
      fun expected_type source =
        case rare_source_fixed_type source of
          SOME ty => SOME ty
        | NONE => if source = RareSourceSeq then seq_type else NONE
      fun check_type formal source term =
        case expected_type source of
          NONE => ()
        | SOME expected =>
            if Type.compare (Term.type_of term, expected) = EQUAL then ()
            else wrong formal "has the wrong declared carrier"
      fun normalize ((formal, kind, source), located : located_term) =
        let
          val term = #term located
          val wrapper = rare_source_structured_wrapper located
        in
          case kind of
            RareSourceList aggregate =>
              let
                val (elements, element_ty) =
                  list_parts formal aggregate located
                val carrier_ty = case expected_type source of
                    SOME ty => ty
                  | NONE =>
                      if Type.is_vartype element_ty then
                        wrong formal "has an untyped empty CPC list wrapper"
                      else element_ty
                val _ = List.all (fn element =>
                    Type.compare (Term.type_of element, carrier_ty) = EQUAL)
                    elements orelse
                  wrong formal "has mixed or wrong-carrier list elements"
                val _ = if Type.is_vartype element_ty orelse
                    Type.compare (element_ty, carrier_ty) = EQUAL then ()
                  else wrong formal
                    "has mixed or wrong-carrier list elements"
              in
                listSyntax.mk_list (elements, carrier_ty)
              end
          | RareSourceTerm =>
              if wrapper then
                wrong formal "must not be a CPC list wrapper"
              else (check_type formal source term; term)
          | RareSourceIndex =>
              if wrapper then
                wrong formal "must not be a CPC list wrapper"
              else (check_type formal source term; term)
        end
    in
      ListPair.map normalize (formals, located_args)
    end

  fun eval_rare_source_recipe name formals args expression =
    let
      val _ = List.length formals = List.length args orelse
        raise ERR name
          ("cvc5-1.3.4 RARE rule " ^ name ^
           " received the wrong argument count")
      val environment = ListPair.map
        (fn ((formal, kind, _), argument) => (formal, kind, argument))
        (formals, args)
      fun lookup formal =
        case List.find (fn (name, _, _) => name = formal) environment of
          SOME binding => binding
        | NONE => raise ERR name
            ("unknown formal " ^ formal ^ " in its declarative recipe")
      fun numeral token = intSyntax.mk_injected
        (numSyntax.mk_numeral (Library.parse_arbnum token))
      fun is_digits token =
        String.size token > 0 andalso
        List.all Char.isDigit (String.explode token)
      fun is_simple_string_literal token =
        String.size token >= 2 andalso String.sub (token, 0) = #"\"" andalso
        String.sub (token, String.size token - 1) = #"\""
      fun simple_string_literal token =
        SmtLib_String_Literal.mk_string_term
          (String.substring (token, 1, String.size token - 2))
      fun source_name operator operands =
        let
          val seq = List.exists
            (listSyntax.is_list_type o Term.type_of) operands
        in
          if not seq then operator
          else case operator of
            "str.++" => "seq.++"
          | "str.len" => "seq.len"
          | "str.contains" => "seq.contains"
          | "str.substr" => "seq.extract"
          | "str.at" => "seq.at"
          | "str.indexof" => "seq.indexof"
          | "str.replace" => "seq.replace"
          | "str.replace_all" => "seq.replace_all"
          | "str.update" => "seq.update"
          | "str.prefixof" => "seq.prefixof"
          | "str.suffixof" => "seq.suffixof"
          | "str.rev" => "seq.rev"
          | other => other
        end
      fun list_parts formal =
        let val (_, _, argument) = lookup formal in
          #1 (listSyntax.dest_list argument)
          handle Feedback.HOL_ERR _ => raise ERR name
            ("cvc5-1.3.4 RARE rule " ^ name ^ " list formal " ^ formal ^
             " lost its explicit CPC list wrapper")
        end
      fun identity operator expressions operands =
        let
          fun constant symbol =
            SmtLib_Parser.apply_term rare_source_tmdict symbol [] []
          fun binary_fold symbol first rest =
            List.foldl
              (fn (operand, accumulated) =>
                SmtLib_Parser.apply_term rare_source_tmdict symbol []
                  [accumulated, operand])
              first rest
          fun indexed_natural tm =
            numSyntax.dest_numeral (intSyntax.dest_injected tm)
            handle Feedback.HOL_ERR _ => raise ERR name
              ("cvc5-1.3.4 RARE rule " ^ name ^
               " requires literal natural re.loop indices")
          fun adjacent _ [_] = []
            | adjacent relation (left :: (rest as right :: _)) =
                relation left right :: adjacent relation rest
            | adjacent _ [] = []
          fun equality operands =
            if List.length operands < 2 then raise ERR name
              "declarative equality requires at least two operands"
            else if Type.compare
                (Term.type_of (List.hd operands), reglan_ty) =
                EQUAL then
              boolSyntax.list_mk_conj
                (adjacent (fn left => fn right =>
                   Term.list_mk_comb (reglan_equiv_tm, [left, right]))
                 operands)
            else SmtLib_Parser.apply_term rare_source_tmdict "=" [] operands
        in
        case (operator, operands) of
          ("=", operands) => equality operands
        | ("str.++", []) =>
            let
              fun carrier (RareAtom formal :: _) = #3 (lookup formal)
                | carrier (_ :: rest) = carrier rest
                | carrier [] = raise ERR name
                    "empty concat recipe has no carrier witness"
            in
              rare_source_empty (carrier expressions)
            end
        | ("seq.++", []) => raise ERR name
            "internal unnormalized Seq concat recipe"
        | ("and", []) => boolSyntax.T
        | ("or", []) => boolSyntax.F
        | ("str.++", [operand]) => operand
        | ("seq.++", [operand]) => operand
        | ("re.++", [operand]) => operand
        | ("re.union", [operand]) => operand
        | ("re.inter", [operand]) => operand
        | ("re.++", []) =>
            SmtLib_Parser.apply_term rare_source_tmdict "str.to_re" []
              [rare_source_empty
                (Term.mk_comb
                  (Term.prim_mk_const
                    {Thy = "smtstring", Name = "SmtStr"},
                   listSyntax.mk_nil numSyntax.num))]
        | ("re.union", []) => constant "re.none"
        | ("re.inter", []) => constant "re.all"
        | ("re.++", first :: rest) => binary_fold "re.++" first rest
        | ("re.union", first :: rest) =>
            binary_fold "re.union" first rest
        | ("re.inter", first :: rest) =>
            binary_fold "re.inter" first rest
        | ("re.loop", [lo, hi, re]) =>
            SmtLib_Parser.apply_term rare_source_tmdict "re.loop"
              [numSyntax.mk_numeral (indexed_natural lo),
               numSyntax.mk_numeral (indexed_natural hi)] [re]
        | ("re.^", [power, re]) =>
            SmtLib_Parser.apply_term rare_source_tmdict "re.^"
              [numSyntax.mk_numeral (indexed_natural power)] [re]
        | ("and", [operand]) => operand
        | ("or", [operand]) => operand
        | _ => SmtLib_Parser.apply_term rare_source_tmdict
            (source_name operator operands) [] operands
        end
      fun eval (RareAtom formal) =
            (case List.find (fn (candidate, _, _) => candidate = formal)
                 environment of
               SOME (_, RareSourceTerm, argument) => argument
             | SOME (_, RareSourceList _, _) => raise ERR name
                 ("list formal " ^ formal ^ " used outside a variadic head")
             | SOME (_, RareSourceIndex, argument) => argument
             | NONE =>
                 if formal = "true" then boolSyntax.T
                 else if formal = "false" then boolSyntax.F
                 else if is_simple_string_literal formal then
                   simple_string_literal formal
                 else if is_digits formal then numeral formal
                 else SmtLib_Parser.apply_term rare_source_tmdict
                   formal [] [])
        | eval (RareList
            [RareAtom "@seq.empty_of_type",
             RareList [RareAtom "@type_of", RareAtom formal]]) =
            rare_source_empty (#3 (lookup formal))
        | eval (RareList (RareAtom operator :: expressions)) =
            let
              fun operands [] = []
                | operands (RareAtom formal :: rest) =
                    (case List.find
                       (fn (candidate, _, _) => candidate = formal)
                       environment of
                       SOME (_, RareSourceList _, _) =>
                         list_parts formal @ operands rest
                     | _ => eval (RareAtom formal) :: operands rest)
                | operands (expression :: rest) =
                    eval expression :: operands rest
              val arguments = operands expressions
            in
              identity operator expressions arguments
            end
        | eval (RareList []) = raise ERR name
            "empty application in its declarative recipe"
        | eval _ = raise ERR name
            "non-atomic application head in its declarative recipe"
    in
      eval (parse_rare_source_sexp expression)
    end

  fun validate_rare_source_premises name
      ({formals, premises, ...} : rare_source_recipe) prems args =
    let
      val expected_premises = List.map
        (eval_rare_source_recipe name formals args) premises
      val supplied_premises = List.map Thm.concl prems
      val _ = ListPair.allEq (fn (expected, supplied) =>
          Term.aconv expected supplied)
          (expected_premises, supplied_premises) orelse
        raise ERR name
          ("cvc5-1.3.4 RARE rule " ^ name ^
           " premises do not match its declarative source recipe")
    in
      expected_premises
    end

  fun validate_rare_source_contract name
      (recipe as {formals, target, ...} : rare_source_recipe)
      prems conclusion args =
    let
      val expected_premises =
        validate_rare_source_premises name recipe prems args
      val expected = eval_rare_source_recipe name formals args target
      val _ = case conclusion of
          NONE => ()
        | SOME declared =>
            if Term.aconv expected declared then ()
            else raise ERR name
              ("cvc5-1.3.4 RARE rule " ^ name ^
               " conclusion does not match its declarative source recipe")
    in
      {expected_premises = expected_premises, expected = expected}
    end

  fun replay_rare_source_recipe family name
      (recipe : rare_source_recipe) prems conclusion args =
    let
      val {expected_premises, expected} =
        validate_rare_source_contract name recipe prems conclusion args
      fun implication_target () =
        List.foldr boolSyntax.mk_imp expected expected_premises
      fun apply_implication theorem =
        List.foldl
          (fn (premise, theorem) =>
            Thm.MP theorem (Thm.ASSUME premise))
          theorem expected_premises
      fun prove_implication tactic =
        let
          val implication = implication_target ()
          val theorem = Tactical.TAC_PROOF (([], implication), tactic)
        in
          apply_implication theorem
        end
      fun owning_procedure () =
        let val implication = implication_target () in
          apply_implication
            (if SmtSeqProve.has_seq_type implication then
               SmtSeqProve.seq_prove implication
            else SmtStringProve.string_prove intLib.ARITH_PROVE implication)
        end
      fun missing_recipe () = raise ERR name
        ("cvc5-1.3.4 RARE rule " ^ name ^
         " has no fixed typed family proof recipe")
      val regex_context_theorems =
        [smtstringTheory.reglan_equiv_refl,
         smtstringTheory.reglan_equiv_sym,
         smtstringTheory.reglan_equiv_trans,
         smtstringTheory.reglan_concat_equiv,
         smtstringTheory.reglan_union_equiv,
         smtstringTheory.reglan_inter_equiv,
         smtstringTheory.reglan_star_equiv]
      fun regex_metis theorems =
        prove_implication (Tactical.THEN
          (bossLib.SIMP_TAC (bossLib.srw_ss())
             [boolTheory.EQ_CLAUSES, integerTheory.int_gt,
              integerTheory.int_ge],
           metisLib.METIS_TAC (regex_context_theorems @ theorems)))
      fun instantiate_exact theorem target =
        let val generic = Drule.SPEC_ALL theorem in
          Drule.INST_TY_TERM
            (Term.match_term (Thm.concl generic) target) generic
        end
      fun regex_concat_context base_theorems target =
        let
          fun base target =
            Lib.tryfind (fn theorem =>
              instantiate_exact theorem target
              handle Feedback.HOL_ERR _ =>
                instantiate_exact (Thm.SYM theorem) target)
              base_theorems
          fun prove left right =
            if Term.aconv left right then replay_reglan_refl left
            else
              let val target = Term.list_mk_comb
                (reglan_equiv_tm, [left, right])
              in
                base target
                handle Feedback.HOL_ERR _ =>
                  let
                    val (left_head, left_args) = boolSyntax.strip_comb left
                    val (right_head, right_args) = boolSyntax.strip_comb right
                    val _ = Term.same_const left_head right_head andalso
                      Term.same_const left_head ``reglan_concat`` orelse
                      raise ERR name
                        "semantic regex context is not respectful"
                    val (left_first, left_rest, right_first, right_rest) =
                      case (left_args, right_args) of
                        ([a, b], [c, d]) => (a, b, c, d)
                      | _ => raise ERR name
                          "semantic regex concat context has wrong arity"
                  in
                    Drule.MATCH_MP smtstringTheory.reglan_concat_equiv
                      (Thm.CONJ
                        (prove left_first right_first)
                        (prove left_rest right_rest))
                  end
              end
          val (left, right) = dest_reglan_equiv target
        in prove left right end
      fun regex_union_all target =
        let
          val (source, universal) = dest_reglan_equiv target
          fun prove tm =
            if Term.aconv tm universal then replay_reglan_refl universal
            else
              let
                val (head, operands) = boolSyntax.strip_comb tm
                val (left, right) =
                  if Term.same_const head ``reglan_union`` then
                    case operands of
                      [left, right] => (left, right)
                    | _ => raise ERR name
                        "semantic regex union context has wrong arity"
                  else raise ERR name
                    "semantic regex union context does not contain re.all"
                fun through_left () =
                  let
                    val lifted = Drule.MATCH_MP
                      smtstringTheory.reglan_union_equiv
                      (Thm.CONJ (prove left) (replay_reglan_refl right))
                    val middle = Term.list_mk_comb
                      (``reglan_union``, [universal, right])
                    val collapse_target = Term.list_mk_comb
                      (reglan_equiv_tm, [middle, universal])
                    val collapse = instantiate_exact
                      smtstringTheory.reglan_equiv_union_star_all_left
                      collapse_target
                  in replay_reglan_trans lifted collapse end
                fun through_right () =
                  let
                    val lifted = Drule.MATCH_MP
                      smtstringTheory.reglan_union_equiv
                      (Thm.CONJ (replay_reglan_refl left) (prove right))
                    val middle = Term.list_mk_comb
                      (``reglan_union``, [left, universal])
                    val collapse_target = Term.list_mk_comb
                      (reglan_equiv_tm, [middle, universal])
                    val collapse = instantiate_exact
                      smtstringTheory.reglan_equiv_union_star_all
                      collapse_target
                  in replay_reglan_trans lifted collapse end
              in
                through_left () handle Feedback.HOL_ERR _ => through_right ()
              end
        in prove source end
      fun regex_remove_identity operator identity congruence left_identity
          right_identity target =
        let
          fun normalize tm =
            if Term.aconv tm identity then (identity,
              replay_reglan_refl identity)
            else
              let
                val (head, operands) = boolSyntax.strip_comb tm
              in
                if Term.same_const head operator then
                  let
                    val (left, right) =
                      case operands of
                        [left, right] => (left, right)
                      | _ => raise ERR name
                          "semantic regex identity context has wrong arity"
                    val (left', left_thm) = normalize left
                    val (right', right_thm) = normalize right
                    val combined = Term.list_mk_comb
                      (operator, [left', right'])
                    val lifted = Drule.MATCH_MP congruence
                      (Thm.CONJ left_thm right_thm)
                    fun collapse theorem result =
                      let
                        val collapse_target = Term.list_mk_comb
                          (reglan_equiv_tm, [combined, result])
                        val collapse = instantiate_exact theorem
                          collapse_target
                      in (result, replay_reglan_trans lifted collapse) end
                  in
                    if Term.aconv left' identity then
                      collapse left_identity right'
                    else if Term.aconv right' identity then
                      collapse right_identity left'
                    else (combined, lifted)
                  end
                else (tm, replay_reglan_refl tm)
              end
          val (source, destination) = dest_reglan_equiv target
          val (source', source_thm) = normalize source
          val (destination', destination_thm) = normalize destination
          val _ = Term.aconv source' destination' orelse raise ERR name
            ("semantic regex identity normalization changed the target: " ^
             "source=" ^ Library.term_to_string source' ^
             "; destination=" ^ Library.term_to_string destination')
        in
          replay_reglan_trans source_thm
            (replay_reglan_sym destination_thm)
        end
      fun regex_inter_cstring () =
        let
          val premise = expose_true_equality
            (expect_one_premise name prems)
          val (string, source) =
            case boolSyntax.strip_comb (Thm.concl premise) of
              (head, [string, regex]) =>
                if Term.same_const head ``smt_in_re`` then (string, regex)
                else raise ERR name
                  "expected a regex-membership premise"
            | _ => raise ERR name "expected a regex-membership premise"
          val (target_source, singleton) = dest_reglan_equiv expected
          val _ = Term.aconv source target_source orelse raise ERR name
            "membership premise and regex equality use different languages"
          val expected_singleton = Term.mk_comb (``reglan_to_re``, string)
          val _ = Term.aconv singleton expected_singleton orelse raise ERR name
            "regex intersection target is not its singleton member"
          fun prove regex membership =
            if Term.aconv regex singleton then replay_reglan_refl singleton
            else
              let
                val (head, operands) = boolSyntax.strip_comb regex
                val (left, _) =
                  if Term.same_const head ``reglan_inter`` then
                    case operands of
                      [left, right] => (left, right)
                    | _ => raise ERR name
                        "regex intersection has wrong arity"
                  else raise ERR name
                    "regex intersection does not start with its singleton"
                val left_membership = Drule.MATCH_MP
                  smtstringTheory.smt_in_re_inter_left membership
                val left_equiv = prove left left_membership
              in
                Drule.MATCH_MP
                  smtstringTheory.reglan_equiv_inter_cstring_step
                  (Thm.CONJ membership left_equiv)
              end
        in prove source premise end
      fun regex_semantic_simp theorems =
        prove_implication (Tactical.THEN
          (bossLib.SIMP_TAC (bossLib.srw_ss())
             [boolTheory.EQ_CLAUSES, integerTheory.int_gt,
              integerTheory.int_ge, smtstringTheory.reglan_equiv_def,
              smtstringTheory.re_lang_def,
              smtstringTheory.smtstr_rep_def],
           Tactical.THEN
             (Tactic.CONV_TAC (Conv.DEPTH_CONV Drule.ETA_CONV),
              bossLib.SIMP_TAC (bossLib.srw_ss())
          ([smtstringTheory.reglan_dot_assoc,
            smtstringTheory.reglan_kstar_dot_comm,
            smtstringTheory.reglan_kstar_dot_subsume,
            smtstringTheory.reglan_kstar_idem,
            smtstringTheory.reglan_kstar_epsilon,
            smtstringTheory.reglan_kstar_none,
            smtstringTheory.reglan_kstar_drop_epsilon,
            smtstringTheory.reglan_kstar_allchar,
            smtstringTheory.reglan_kstar_allchar_sandwich,
            smtstringTheory.reglan_star_swap_suffix,
            smtstringTheory.reglan_star_swap_suffix_fun,
            smtstringTheory.reglan_star_repeat_suffix,
            smtstringTheory.reglan_star_repeat_suffix_fun,
            smtstringTheory.reglan_star_subsume_right_lang,
            smtstringTheory.reglan_star_subsume_left_lang,
            smtstringTheory.reglan_star_subsume_right_suffix,
            smtstringTheory.reglan_star_subsume_right_suffix_fun,
            Rewrite.REWRITE_RULE [smtstringTheory.re_lang_def]
              smtstringTheory.reglan_star_subsume_right_suffix_fun,
            smtstringTheory.reglan_star_subsume_left_suffix,
            smtstringTheory.reglan_star_subsume_left_suffix_fun,
            Rewrite.REWRITE_RULE [smtstringTheory.re_lang_def]
              smtstringTheory.reglan_star_subsume_left_suffix_fun,
            smtstringTheory.reglan_star_union_allchar_lang,
            Rewrite.REWRITE_RULE [smtstringTheory.re_lang_def]
              smtstringTheory.reglan_star_union_allchar_lang,
            smtstringTheory.reglan_concat_literals_suffix_fun,
            smtstringTheory.reglan_concat_literals_suffix_rep_fun,
            smtstringTheory.re_lang_wf] @ theorems))))
      fun regex_semantic_metis theorems =
        prove_implication (Tactical.THEN
          (bossLib.SIMP_TAC (bossLib.srw_ss())
             [boolTheory.EQ_CLAUSES, integerTheory.int_gt,
              integerTheory.int_ge, smtstringTheory.reglan_equiv_def,
              smtstringTheory.re_lang_def,
              smtstringTheory.smtstr_rep_def,
              smtstringTheory.smt_in_re_rep,
              smtstringTheory.reglan_kstar_allchar],
           Tactical.THEN
             (Tactic.CONV_TAC (Conv.DEPTH_CONV Drule.ETA_CONV),
              metisLib.METIS_TAC
                (smtstringTheory.re_lang_wf :: theorems))))
      fun regex_star_union_char () =
        prove_implication (Tactical.THEN
          (bossLib.SIMP_TAC (bossLib.srw_ss())
             [smtstringTheory.reglan_equiv_def,
              smtstringTheory.re_lang_def,
              smtstringTheory.reglan_kstar_allchar],
           Tactical.THEN
             (Tactic.CONV_TAC (Conv.DEPTH_CONV Drule.ETA_CONV),
              Tactical.THEN
                (Tactical.REPEAT Tactic.STRIP_TAC,
                 Tactical.THEN
                   (Tactic.MATCH_MP_TAC
                      smtstringTheory.reglan_kstar_allchar_sandwich,
                    Tactical.THENL
                      (Tactic.CONJ_TAC,
                       [Tactical.THEN
                          (Tactical.REPEAT Tactic.STRIP_TAC,
                           Tactical.THEN
                             (bossLib.FULL_SIMP_TAC
                                (bossLib.srw_ss()) [],
                              metisLib.METIS_TAC
                                [smtstringTheory.re_lang_wf])),
                        bossLib.SIMP_TAC (bossLib.srw_ss()) []]))))))
      fun regex_star_union_drop_epsilon () =
        prove_implication (Tactical.THEN
          (bossLib.SIMP_TAC (bossLib.srw_ss())
             [smtstringTheory.reglan_equiv_def,
              smtstringTheory.re_lang_def,
              smtstringTheory.smtstr_rep_def],
           Tactical.THEN
             (Tactic.CONV_TAC (Conv.DEPTH_CONV Drule.ETA_CONV),
              Tactical.THEN
                (Tactical.REPEAT Tactic.STRIP_TAC,
                 Tactical.THEN
                   (Tactic.MATCH_MP_TAC
                      smtstringTheory.reglan_kstar_epsilon_invariant,
                    metisLib.METIS_TAC [])))))
      fun regex_family_prove () =
        if name = "re-concat-star-subsume1" then
          regex_concat_context
            [smtstringTheory.reglan_equiv_star_subsume_right_context,
             smtstringTheory.reglan_equiv_star_subsume_right_suffix]
            expected
        else if name = "re-concat-star-subsume2" then
          regex_concat_context
            [smtstringTheory.reglan_equiv_star_subsume_left_context,
             smtstringTheory.reglan_equiv_star_subsume_left_suffix]
            expected
        else if name = "re-concat-star-swap" orelse
           name = "re-concat-star-repeat" orelse
           name = "re-concat-merge" then
          regex_semantic_simp []
        else if name = "re-star-union-char" then
          regex_star_union_char ()
        else if name = "re-star-union-drop-emp" then
          regex_star_union_drop_epsilon ()
        else if name = "re-union-all" then regex_union_all expected
        else if name = "re-inter-all" then
          regex_remove_identity ``reglan_inter``
            ``reglan_star reglan_allchar``
            smtstringTheory.reglan_inter_equiv
            smtstringTheory.reglan_equiv_inter_star_all_left
            smtstringTheory.reglan_equiv_inter_star_all expected
        else if name = "re-inter-cstring" then regex_inter_cstring ()
        else if name = "re-inter-cstring-neg" then
          regex_semantic_metis []
        else if name = "re-union-const-elim" then regex_metis
          [smtstringTheory.reglan_equiv_union_const]
        else if name = "re-star-none" then regex_metis
          [smtstringTheory.reglan_equiv_star_none]
        else if name = "re-star-emp" then regex_metis
          [smtstringTheory.reglan_equiv_star_epsilon]
        else if name = "re-star-star" then regex_metis
          [smtstringTheory.reglan_equiv_star_star]
        else if name = "re-range-refl" then regex_metis
          [smtstringTheory.reglan_equiv_range_refl]
        else if name = "re-range-emp" then regex_metis
          [smtstringTheory.reglan_equiv_range_empty]
        else if name = "re-range-non-singleton-1" then regex_metis
          [smtstringTheory.reglan_equiv_range_non_singleton_left]
        else if name = "re-range-non-singleton-2" then regex_metis
          [smtstringTheory.reglan_equiv_range_non_singleton_right]
        else if name = "re-loop-neg" then regex_metis
          [smtstringTheory.reglan_equiv_loop_empty]
        else if name = "re-all-elim" then regex_metis
          [smtstringTheory.reglan_equiv_all]
        else if name = "re-diff-elim" then regex_metis
          [smtstringTheory.reglan_equiv_diff]
        else if name = "re-opt-elim" then regex_metis
          [smtstringTheory.reglan_equiv_opt]
        else if name = "re-plus-elim" then regex_metis
          [smtstringTheory.reglan_equiv_plus]
        else if name = "re-repeat-elim" then regex_metis
          [smtstringTheory.reglan_equiv_power_loop]
        else missing_recipe ()
      fun seq_family_prove () =
        let
          (* Recipes state Seq semantics independently of the parser's
             choice of named operators or their defining HOL expressions.
             Normalize that representation with checked definitions before
             running the fixed family proof. *)
          val prove_source_implication = prove_implication
          fun prove_implication tactic =
            prove_source_implication (Tactical.THEN
              (Rewrite.PURE_REWRITE_TAC
                 [HolSmtTheory.smt_seq_extract_def,
                  HolSmtTheory.smt_seq_at_def], tactic))
        in
        if name = "str-eq-ctn-false" then
          prove_implication (metisLib.METIS_TAC
            [boolTheory.EQ_CLAUSES, listTheory.APPEND_ASSOC,
             rich_listTheory.IS_SUBLIST_APPEND])
        else if name = "str-eq-ctn-full-false1" orelse
           name = "str-eq-ctn-full-false2" then
          prove_implication (metisLib.METIS_TAC
            [rare_seq_contains_refl])
        else if name = "seq-rev-rev" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [listTheory.REVERSE_REVERSE])
        else if name = "str-substr-concat1" then
          prove_implication (metisLib.METIS_TAC
            [boolTheory.EQ_CLAUSES, integerTheory.int_ge,
             HolSmtTheory.smt_seq_extract_body_concat_left_bound2])
        else if name = "str-substr-empty-range" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [boolTheory.EQ_CLAUSES, integerTheory.int_ge,
             HolSmtTheory.smt_seq_extract_def])
        else if name = "str-substr-empty-str" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [listTheory.LENGTH_EQ_0, HolSmtTheory.smt_seq_extract_def])
        else if name = "str-substr-eq-empty" then
          prove_implication (Tactical.THEN
            (Tactical.REPEAT Tactic.STRIP_TAC,
             Tactical.THEN
               (bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
                  [boolTheory.EQ_CLAUSES, integerTheory.int_gt,
                   Conv.GSYM HolSmtTheory.smt_seq_extract_def],
                Tactical.THEN
                  (Tactic.MATCH_MP_TAC
                     HolSmtTheory.smt_seq_extract_zero_empty_iff,
                   Tactical.THEN
                     (bossLib.ASM_SIMP_TAC (bossLib.srw_ss())
                        [integerTheory.INT_NOT_LE],
                      intLib.ARITH_TAC)))))
        else if name = "str-substr-full-eq" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [HolSmtTheory.smt_seq_extract_body_full_eq])
        else if name = "str-at-elim" then
          let
            val generic = HolSmtTheory.smt_seq_at_extract
          in
            (Drule.INST_TY_TERM
               (Term.match_term (Thm.concl generic) expected) generic
             handle Feedback.HOL_ERR _ =>
               let val symmetric = Thm.SYM generic in
                 Drule.INST_TY_TERM
                   (Term.match_term (Thm.concl symmetric) expected)
                   symmetric
               end)
          end
        else if name = "str-substr-empty-start" orelse
                name = "str-substr-empty-start-neg" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [integerTheory.int_ge,
             HolSmtTheory.smt_seq_extract_body_empty_start,
             HolSmtTheory.smt_seq_extract_body_empty_start_neg])
        else if name = "str-substr-substr-start-geq-len" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [integerTheory.int_ge,
             HolSmtTheory.smt_seq_extract_body_nested_empty_start])
        else if name = "str-substr-z-eq-empty-leq" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [integerTheory.int_le,
             HolSmtTheory.smt_seq_extract_body_zero_eq_empty])
        else if name = "str-substr-eq-empty-leq-len" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [integerTheory.int_ge, integerTheory.int_gt,
             integerTheory.int_le,
             HolSmtTheory.smt_seq_extract_body_eq_empty_length])
        else if name = "str-update-in-first-concat" then
          prove_implication (metisLib.METIS_TAC
            [integerTheory.int_ge, integerTheory.int_lt,
             listTheory.APPEND_ASSOC,
             HolSmtTheory.smt_seq_extract_def,
             HolSmtTheory.smt_seq_update_concat_first])
        else if name = "str-concat-clash-rev" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [boolTheory.EQ_CLAUSES, integerTheory.INT_INJ,
             Thm.CONJUNCT2 listTheory.APPEND_11_LENGTH])
        else if name = "str-concat-unify-rev" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [listTheory.APPEND_ASSOC])
        else if name = "str-concat-clash" then
          prove_implication (metisLib.METIS_TAC
            [boolTheory.EQ_CLAUSES, integerTheory.INT_INJ,
             listTheory.APPEND_ASSOC,
             HolSmtTheory.list_append_neq_same_length])
        else if name = "str-concat-clash2" then
          prove_implication (Tactic.MATCH_ACCEPT_TAC
            HolSmtTheory.list_neq_append2_same_int_length)
        else if name = "str-concat-clash2-rev" then
          prove_implication (Tactic.MATCH_ACCEPT_TAC
            HolSmtTheory.list_neq_prepend2_same_int_length)
        else if name = "str-concat-unify" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [listTheory.APPEND_ASSOC])
        else if name = "str-concat-unify-base" orelse
                name = "str-concat-unify-base-rev" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [listTheory.APPEND_ASSOC, listTheory.APPEND_EQ_SELF])
        else if name = "str-suffixof-elim" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [integerTheory.INT_SUB,
             HolSmtTheory.smt_seq_extract_def,
             HolSmtTheory.smt_seq_suffix_extract])
        else if name = "str-suffixof-eq" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [integerTheory.int_ge,
             HolSmtTheory.list_suffix_equal_length])
        else if name = "str-suffixof-one" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [HolSmtTheory.list_suffix_length_one])
        else if name = "str-substr-combine1" then
          prove_implication (Tactical.THEN
            (Tactical.REPEAT Tactic.STRIP_TAC,
             Tactical.THEN
               (Rewrite.PURE_REWRITE_TAC
                  [Conv.GSYM HolSmtTheory.smt_seq_extract_def],
                Tactical.THEN
                  (Tactic.MATCH_MP_TAC
                     HolSmtTheory.smt_seq_extract_combine_right,
                   bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
                     [integerTheory.int_ge]))))
        else if name = "str-substr-combine2" then
          prove_implication (Tactical.THEN
            (Tactical.REPEAT Tactic.STRIP_TAC,
             Tactical.THEN
               (Rewrite.PURE_REWRITE_TAC
                  [Conv.GSYM HolSmtTheory.smt_seq_extract_def],
                Tactical.THEN
                  (Tactic.MATCH_MP_TAC
                     HolSmtTheory.smt_seq_extract_combine_left,
                   bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
                     [integerTheory.int_ge]))))
        else if name = "str-substr-combine3" then
          prove_implication (Tactical.THEN
            (Tactical.REPEAT Tactic.STRIP_TAC,
             Tactical.THEN
               (Tactic.RULE_ASSUM_TAC
                  (Rewrite.REWRITE_RULE
                    [Conv.GSYM HolSmtTheory.smt_seq_extract_def]),
                Tactical.THEN
                  (Tactical.THEN
                     (Rewrite.PURE_REWRITE_TAC
                        [Conv.GSYM HolSmtTheory.smt_seq_extract_def],
                      Tactic.MATCH_MP_TAC
                        HolSmtTheory.smt_seq_extract_combine_inner_bound),
                   bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
                     [integerTheory.int_ge]))))
        else if name = "str-substr-combine4" then
          prove_implication (Tactical.THEN
            (Tactical.REPEAT Tactic.STRIP_TAC,
             Tactical.THEN
               (Tactic.RULE_ASSUM_TAC
                  (Rewrite.REWRITE_RULE
                    [Conv.GSYM HolSmtTheory.smt_seq_extract_def]),
                Tactical.THEN
                  (Tactical.THEN
                     (Rewrite.PURE_REWRITE_TAC
                        [Conv.GSYM HolSmtTheory.smt_seq_extract_def],
                      Tactic.MATCH_MP_TAC
                        HolSmtTheory.smt_seq_extract_combine_actual_bound),
                   bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
                     [integerTheory.int_ge]))))
        else if name = "str-substr-concat2" then
          prove_implication (metisLib.METIS_TAC
            [boolTheory.EQ_CLAUSES, integerTheory.int_ge,
             listTheory.APPEND_ASSOC,
             HolSmtTheory.smt_seq_extract_def,
             HolSmtTheory.smt_seq_extract_drop_prefix])
        else if name = "str-substr-replace" then
          prove_implication (Tactical.THEN
            (Tactical.REPEAT Tactic.STRIP_TAC,
             Tactical.THEN
               (Rewrite.PURE_REWRITE_TAC
                  [Conv.GSYM HolSmtTheory.smt_seq_extract_def],
                Tactical.THEN
                  (Tactic.MATCH_MP_TAC
                     HolSmtTheory.smt_seq_extract_replace_len_one,
                   bossLib.FULL_SIMP_TAC (bossLib.srw_ss()) []))))
        else if name = "str-substr-full" then
          prove_implication (Tactical.THEN
            (Tactical.REPEAT Tactic.STRIP_TAC,
             Tactical.THEN
               (Rewrite.PURE_REWRITE_TAC
                  [Conv.GSYM HolSmtTheory.smt_seq_extract_def],
                Tactical.THEN
                  (Tactic.MATCH_MP_TAC HolSmtTheory.smt_seq_extract_full,
                   bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
                     [integerTheory.int_ge]))))
        else if name = "str-substr-ctn-contra" then
          prove_implication (Tactical.THEN
            (Tactical.REPEAT Tactic.STRIP_TAC,
             Tactical.THEN
               (Rewrite.PURE_REWRITE_TAC
                  [Conv.GSYM HolSmtTheory.smt_seq_extract_def],
                bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
                  [boolTheory.EQ_CLAUSES,
                   HolSmtTheory.smt_seq_extract_contains_contra])))
        else if name = "str-substr-ctn" then
          prove_implication (Tactical.THEN
            (Rewrite.PURE_REWRITE_TAC
               [Conv.GSYM HolSmtTheory.smt_seq_extract_def],
             bossLib.SIMP_TAC (bossLib.srw_ss())
               [HolSmtTheory.smt_seq_extract_sublist]))
        else if name = "str-substr-char-start-eq-len" then
          prove_implication (Tactical.THEN
            (Rewrite.PURE_REWRITE_TAC
               [Conv.GSYM HolSmtTheory.smt_seq_extract_def],
             bossLib.SIMP_TAC (bossLib.srw_ss())
               [boolTheory.EQ_CLAUSES, integerTheory.int_ge,
                HolSmtTheory.smt_seq_extract_short_self_count]))
        else if name = "str-substr-len-include" then
          prove_implication (Tactical.THEN
            (Tactical.REPEAT Tactic.STRIP_TAC,
             Tactical.THEN
               (Rewrite.PURE_REWRITE_TAC
                  [Conv.GSYM HolSmtTheory.smt_seq_extract_def],
                Tactical.THEN
                  (Tactic.MATCH_MP_TAC
                     HolSmtTheory.smt_seq_extract_concat_left_bound2,
                   bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
                     [integerTheory.int_ge]))))
        else if name = "str-substr-len-include-pre" then
          prove_implication (Tactical.THEN
            (Tactical.REPEAT Tactic.STRIP_TAC,
             Tactical.THEN
               (Rewrite.PURE_REWRITE_TAC
                  [Conv.GSYM listTheory.APPEND_ASSOC,
                   Conv.GSYM HolSmtTheory.smt_seq_extract_def],
                Tactical.THEN
                  (Tactic.MATCH_MP_TAC
                     HolSmtTheory.smt_seq_extract_concat_prefix_bound,
                   bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
                     [integerTheory.int_ge]))))
        else if name = "str-substr-len-norm" then
          prove_implication (Tactical.THEN
            (Tactical.REPEAT Tactic.STRIP_TAC,
             Tactical.THEN
               (Rewrite.PURE_REWRITE_TAC
                  [Conv.GSYM HolSmtTheory.smt_seq_extract_def],
                Tactical.THEN
                  (Tactic.MATCH_MP_TAC
                     HolSmtTheory.smt_seq_extract_count_normalize,
                   bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
                     [integerTheory.int_ge]))))
        else if name = "str-replace-dual-ctn" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [boolTheory.EQ_CLAUSES,
             HolSmtTheory.smt_seq_replace_preserves_contains])
        else if name = "str-replace-dual-ctn-false" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [boolTheory.EQ_CLAUSES,
             HolSmtTheory.smt_seq_replace_avoids_outer])
        else if name = "str-replace-self-ctn-simp" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [HolSmtTheory.smt_seq_replace_pattern_self_contains])
        else if name = "str-replace-emp-ctn-src" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [HolSmtTheory.smt_seq_replace_empty_source_contains])
        else if name = "str-contains-repl-char" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [boolTheory.EQ_CLAUSES,
             HolSmtTheory.smt_seq_replace_contains_len_one])
        else if name = "str-contains-repl-self-tgt-char" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [HolSmtTheory.smt_seq_replace_self_contains_len_one])
        else if name = "str-contains-repl-self" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [HolSmtTheory.smt_seq_replace_self_contains])
        else if name = "str-contains-repl-tgt" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [HolSmtTheory.smt_seq_replace_contains_replacement])
        else if name = "str-repl-repl-len-id" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [boolTheory.EQ_CLAUSES, integerTheory.int_ge,
             HolSmtTheory.smt_seq_replace_self_target])
        else if name = "str-repl-repl-src-tgt-no-ctn" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [boolTheory.EQ_CLAUSES,
             HolSmtTheory.smt_seq_replace_nested_source_target_absent])
        else if name = "str-repl-repl-tgt-self" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [HolSmtTheory.smt_seq_replace_nested_target_self])
        else if name = "str-repl-repl-tgt-no-ctn" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [boolTheory.EQ_CLAUSES,
             HolSmtTheory.smt_seq_replace_nested_target_absent])
        else if name = "str-repl-repl-src-self" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [HolSmtTheory.smt_seq_replace_nested_source_self])
        else if name = "str-repl-repl-src-inv-no-ctn1" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [boolTheory.EQ_CLAUSES,
             HolSmtTheory.smt_seq_replace_nested_source_inverse_absent1])
        else if name = "str-repl-repl-src-inv-no-ctn2" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [boolTheory.EQ_CLAUSES,
             HolSmtTheory.smt_seq_replace_nested_source_inverse_absent2])
        else if name = "str-repl-repl-src-inv-no-ctn3" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [boolTheory.EQ_CLAUSES,
             HolSmtTheory.smt_seq_replace_nested_source_inverse_absent3])
        else if name = "str-repl-repl-dual-self" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [HolSmtTheory.smt_seq_replace_nested_dual_self])
        else if name = "str-repl-repl-dual-ite1" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [boolTheory.EQ_CLAUSES,
             HolSmtTheory.smt_seq_replace_nested_dual_ite1])
        else if name = "str-repl-repl-dual-ite2" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [boolTheory.EQ_CLAUSES,
             HolSmtTheory.smt_seq_replace_nested_dual_ite2])
        else if name = "str-repl-repl-lookahead-id-simp" then
          prove_implication (Tactical.THEN
            (Tactical.REPEAT Tactic.STRIP_TAC,
             Tactical.THEN
               (Tactic.MATCH_MP_TAC
                  HolSmtTheory.smt_seq_replace_nested_lookahead_id_simp,
                bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
                  [boolTheory.EQ_CLAUSES, integerTheory.int_ge])))
        else if name = "str-replace-self" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [HolSmtTheory.smt_seq_replace_self])
        else if name = "str-replace-id" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [HolSmtTheory.smt_seq_replace_id])
        else if name = "str-replace-prefix" then
          prove_implication (metisLib.METIS_TAC
            [HolSmtTheory.smt_seq_replace_prefix,
             listTheory.APPEND_ASSOC])
        else if name = "str-replace-no-contains" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [boolTheory.EQ_CLAUSES,
             HolSmtTheory.smt_seq_replace_absent])
        else if name = "str-replace-find-base" then
          prove_implication (Tactical.THEN
            (Tactical.REPEAT Tactic.STRIP_TAC,
             Tactical.THEN
               (Tactic.RULE_ASSUM_TAC
                  (Rewrite.REWRITE_RULE
                    [Conv.GSYM HolSmtTheory.smt_seq_extract_def]),
                Tactical.THEN
                  (Q.PAT_X_ASSUM
                     `rare_tpre = smt_seq_extract rare_t 0
                        (smt_seq_indexof rare_t rare_s 0)`
                     Tactic.SUBST_ALL_TAC,
                   Tactical.THEN
                     (Q.PAT_X_ASSUM
                        `rare_tpost = smt_seq_extract rare_t
                           (smt_seq_indexof rare_t rare_s 0 +
                            &(LENGTH rare_s)) (&(LENGTH rare_t))`
                        Tactic.SUBST_ALL_TAC,
                      Tactical.THEN
                        (Tactic.MATCH_MP_TAC
                           HolSmtTheory.smt_seq_replace_find,
                         bossLib.FULL_SIMP_TAC boolSimps.bool_ss
                           [boolTheory.EQ_CLAUSES,
                            integerTheory.int_ge]))))))
        else if name = "str-replace-find-first-concat" then
          prove_implication (Tactical.THEN
            (Tactical.REPEAT Tactic.STRIP_TAC,
             Tactical.THEN
               (Tactic.RULE_ASSUM_TAC
                  (Rewrite.REWRITE_RULE
                    [Conv.GSYM HolSmtTheory.smt_seq_extract_def]),
                Tactical.THEN
                  (Q.PAT_X_ASSUM
                     `rare_tpre = smt_seq_extract rare_t 0
                        (smt_seq_indexof rare_t rare_s 0)`
                     Tactic.SUBST_ALL_TAC,
                   Tactical.THEN
                     (Q.PAT_X_ASSUM
                        `rare_tpost = smt_seq_extract rare_t
                           (smt_seq_indexof rare_t rare_s 0 +
                            &(LENGTH rare_s)) (&(LENGTH rare_t))`
                        Tactic.SUBST_ALL_TAC,
                      metisLib.METIS_TAC
                        [boolTheory.EQ_CLAUSES,
                         integerTheory.int_ge,
                         HolSmtTheory.smt_seq_replace_find_append,
                         listTheory.APPEND_ASSOC])))))
        else if name = "str-replace-empty" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [HolSmtTheory.smt_seq_replace_empty])
        else if name = "str-replace-one-pre" then
          prove_implication (metisLib.METIS_TAC
            [integerTheory.INT_INJ,
             HolSmtTheory.smt_seq_replace_repeated_segment_suffix,
             listTheory.APPEND_ASSOC])
        else if name = "str-replace-find-pre" then
          prove_implication (metisLib.METIS_TAC
            [HolSmtTheory.smt_seq_replace_known_match_suffix,
             listTheory.APPEND_ASSOC])
        else if name = "str-replace-all-no-contains" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [boolTheory.EQ_CLAUSES,
             HolSmtTheory.smt_seq_replace_all_absent])
        else if name = "str-replace-all-empty" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [HolSmtTheory.smt_seq_replace_all_empty])
        else if name = "str-replace-all-id" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [HolSmtTheory.smt_seq_replace_all_id])
        else if name = "str-replace-all-self" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [boolTheory.EQ_CLAUSES,
             HolSmtTheory.smt_seq_replace_all_self])
        else if name = "str-eq-repl-self-emp" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [HolSmtTheory.smt_seq_replace_self_empty_eq])
        else if name = "str-eq-repl-self-src" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [HolSmtTheory.smt_seq_replace_self_source_eq])
        else if name = "str-eq-repl-no-change" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [boolTheory.EQ_CLAUSES,
             HolSmtTheory.smt_seq_replace_no_change_eq])
        else if name = "str-eq-repl-tgt-eq-len" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [HolSmtTheory.smt_seq_replace_target_equal_length_eq])
        else if name = "str-eq-repl-len-one-emp-prefix" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [HolSmtTheory.smt_seq_replace_empty_result_len_one])
        else if name = "str-eq-repl-emp-tgt-nemp" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [boolTheory.EQ_CLAUSES,
             HolSmtTheory.smt_seq_replace_empty_result_nonempty])
        else if name = "str-eq-repl-nemp-src-emp" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [boolTheory.EQ_CLAUSES,
             HolSmtTheory.smt_seq_replace_empty_source_nonempty])
        else if name = "str-indexof-self" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [HolSmtTheory.smt_seq_indexof_self])
        else if name = "str-indexof-no-contains" then
          prove_implication (Tactical.THEN
            (Tactical.REPEAT Tactic.STRIP_TAC,
             Tactical.THEN
               (Tactic.RULE_ASSUM_TAC
                  (Rewrite.REWRITE_RULE
                    [Conv.GSYM HolSmtTheory.smt_seq_extract_def]),
                bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
                  [boolTheory.EQ_CLAUSES,
                   HolSmtTheory.smt_seq_indexof_no_contains])))
        else if name = "str-indexof-contains-pre" then
          prove_implication (Tactical.THEN
            (Tactical.REPEAT Tactic.STRIP_TAC,
             Tactical.THEN
               (Tactic.RULE_ASSUM_TAC
                  (Rewrite.REWRITE_RULE
                    [Conv.GSYM HolSmtTheory.smt_seq_extract_def]),
                Tactical.THEN
                  (Tactic.MATCH_MP_TAC
                     HolSmtTheory.smt_seq_indexof_concat_contains2,
                   bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
                     [boolTheory.EQ_CLAUSES,
                      integerTheory.int_gt]))))
        else if name = "str-indexof-contains-concat-pre" then
          prove_implication (metisLib.METIS_TAC
            [HolSmtTheory.smt_seq_indexof_known_occurrence_suffix,
             listTheory.APPEND_ASSOC])
        else if name = "str-indexof-find-emp" then
          prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
            [boolTheory.EQ_CLAUSES, integerTheory.int_ge,
             HolSmtTheory.smt_seq_indexof_empty])
        else if name = "str-indexof-eq-irr" then
          prove_implication (Tactical.THEN
            (Tactical.REPEAT Tactic.STRIP_TAC,
             Tactical.THEN
               (Tactic.RULE_ASSUM_TAC
                  (Rewrite.REWRITE_RULE
                    [Conv.GSYM HolSmtTheory.smt_seq_extract_def]),
                bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
                  [boolTheory.EQ_CLAUSES, integerTheory.int_le,
                   HolSmtTheory.smt_seq_indexof_suffix_equal])))
        else if name = "str-indexof-oob" orelse
                name = "str-indexof-oob2" then
          owning_procedure ()
        else if name = "seq-len-rev" orelse
                name = "seq-rev-concat" orelse
                name = "seq-len-unit" orelse
                name = "seq-nth-unit" orelse
                name = "seq-rev-unit" then
          owning_procedure ()
        else missing_recipe ()
        end
      fun source_uses_hol_sequence () =
        List.exists
          (fn (((_, kind, source), argument)) =>
            if source <> RareSourceSeq then false
            else case kind of
              RareSourceTerm =>
                listSyntax.is_list_type (Term.type_of argument)
            | RareSourceList _ =>
                listSyntax.is_list_type (Term.type_of argument) andalso
                listSyntax.is_list_type
                  (listSyntax.dest_list_type (Term.type_of argument))
            | RareSourceIndex => false)
          (ListPair.zip (#formals recipe, args))
      fun family_prove () =
        if source_uses_hol_sequence () then
          seq_family_prove ()
        else case family of
          RareConcatEquality =>
            if name = "str-eq-ctn-false" then
              prove_implication (Tactical.THEN
                (bossLib.SIMP_TAC (bossLib.srw_ss())
                   [boolTheory.EQ_CLAUSES,
                    smtstringTheory.smtstr_contains_refl],
                 metisLib.METIS_TAC
                   [smtstringTheory.smtstr_contains_decompose,
                    smtstringTheory.smtstr_concat_assoc]))
            else if name = "str-eq-ctn-full-false1" orelse
                    name = "str-eq-ctn-full-false2" then
              prove_implication (metisLib.METIS_TAC
                [smtstringTheory.smtstr_contains_refl])
            else if name = "str-eq-len-false" then
              prove_implication (metisLib.METIS_TAC [])
            else if name = "str-update-in-first-concat" then
              prove_implication (bossLib.FULL_SIMP_TAC
                (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES, integerTheory.int_ge,
                 integerTheory.int_lt,
                 smtstringTheory.smtstr_concat_assoc,
                 smtstringTheory.smtstr_update_concat_first])
            else if name = "str-concat-clash-rev" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_concat_assoc,
                 smtstringTheory.smtstr_concat_equal_suffix_lengths])
            else if name = "str-concat-unify-rev" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_concat_assoc,
                 smtstringTheory.smtstr_concat_right_cancel])
            else if name = "str-concat-clash" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_concat_assoc,
                 smtstringTheory.smtstr_concat_equal_prefix_lengths])
            else if name = "str-concat-clash2" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_concat_assoc,
                 smtstringTheory.smtstr_equal_concat_same_prefix_length])
            else if name = "str-concat-clash2-rev" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_concat_assoc,
                 smtstringTheory.smtstr_equal_concat_same_suffix_length])
            else if name = "str-concat-unify" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_concat_assoc,
                 smtstringTheory.smtstr_concat_left_cancel])
            else if name = "str-concat-unify-base" then
              prove_implication (metisLib.METIS_TAC
                [smtstringTheory.smtstr_concat_assoc,
                 smtstringTheory.smtstr_concat_self_prefix])
            else if name = "str-concat-unify-base-rev" then
              prove_implication (metisLib.METIS_TAC
                [smtstringTheory.smtstr_concat_assoc,
                 smtstringTheory.smtstr_concat_self_suffix])
            else if name = "str-leq-concat-false" orelse
                    name = "str-leq-concat-true" then
              prove_implication (metisLib.METIS_TAC
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_le_refl,
                 smtstringTheory.smtstr_le_common_prefix,
                 smtstringTheory.smtstr_le_equal_length_tail,
                 smtstringTheory.smtstr_concat_assoc])
            else if name = "str-leq-concat-base-1" then
              prove_implication (metisLib.METIS_TAC
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_le_equal_length_left_tail,
                 smtstringTheory.smtstr_concat_assoc])
            else if name = "str-leq-concat-base-2" then
              prove_implication (metisLib.METIS_TAC
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_le_equal_length_right_tail,
                 smtstringTheory.smtstr_concat_assoc])
            else if name = "str-to-int-concat-neg-one" then
              prove_implication (metisLib.METIS_TAC
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_len_eq_zero,
                 smtstringTheory.smtstr_to_int_concat_nondigit,
                 smtstringTheory.smtstr_concat_assoc])
            else missing_recipe ()
        | RareSubstringSuffix =>
            if name = "str-at-elim" then
              (case args of
                 [sequence, index] =>
                   if is_smtstr_type (Term.type_of sequence) then
                     owning_procedure ()
                   else
                     let
                       val theorem = Drule.SPECL [sequence, index]
                         HolSmtTheory.smt_seq_at_extract
                     in
                       if Term.aconv (Thm.concl theorem) expected then theorem
                       else if Term.aconv (Thm.concl (Thm.SYM theorem))
                           expected then Thm.SYM theorem
                       else raise ERR name
                         "generic Seq at/extract theorem did not match"
                     end
               | _ => raise ERR name
                   "expected sequence and index source arguments")
            else if name = "str-substr-concat1" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES, integerTheory.int_ge,
                 smtstringTheory.smtstr_substr_concat_left_bound,
                 smtstringTheory.smtstr_concat_assoc])
            else if name = "str-substr-empty-range" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES, integerTheory.int_ge,
                 smtstringTheory.smtstr_substr_def])
            else if name = "str-substr-empty-str" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_len_eq_zero,
                 smtstringTheory.smtstr_substr_def])
            else if name = "str-substr-eq-empty" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES, integerTheory.int_gt,
                 smtstringTheory.smtstr_substr_zero_empty_iff])
            else if name = "str-substr-full-eq" then
              prove_implication (metisLib.METIS_TAC
                [smtstringTheory.smtstr_substr_full])
            else if name = "str-suffixof-elim" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_suffixof_substr])
            else if name = "str-suffixof-eq" then
              prove_implication (Tactical.THEN
                (Tactical.REPEAT Tactic.STRIP_TAC,
                 Tactical.THEN
                   (bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
                      [boolTheory.EQ_CLAUSES, integerTheory.int_ge],
                    metisLib.METIS_TAC
                      [smtstringTheory.smtstr_suffixof_length_bound])))
            else if name = "str-suffixof-one" then
              prove_implication (metisLib.METIS_TAC
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_suffixof_length_one])
            else if name = "str-substr-empty-start" then
              prove_implication (Tactical.THEN
                (bossLib.SIMP_TAC (bossLib.srw_ss()) [boolTheory.EQ_CLAUSES],
                 Tactical.THEN (Tactical.REPEAT Tactic.STRIP_TAC,
                   Tactical.THEN
                     (Tactic.MATCH_MP_TAC
                        smtstringTheory.smtstr_substr_empty_start,
                      intLib.ARITH_TAC))))
            else if name = "str-substr-empty-start-neg" then
              prove_implication (Tactical.THEN
                (bossLib.SIMP_TAC (bossLib.srw_ss()) [boolTheory.EQ_CLAUSES],
                 Tactical.THEN (Tactical.REPEAT Tactic.STRIP_TAC,
                   Tactical.THEN
                     (Tactic.MATCH_MP_TAC
                        smtstringTheory.smtstr_substr_empty_start_neg,
                      bossLib.ASM_SIMP_TAC (bossLib.srw_ss()) []))))
            else if name = "str-substr-substr-start-geq-len" then
              prove_implication (Tactical.THEN
                (bossLib.SIMP_TAC (bossLib.srw_ss()) [boolTheory.EQ_CLAUSES],
                 Tactical.THEN (Tactical.REPEAT Tactic.STRIP_TAC,
                   Tactical.THEN
                     (Tactic.MATCH_MP_TAC
                        smtstringTheory.smtstr_substr_nested_empty,
                      intLib.ARITH_TAC))))
            else if name = "str-substr-z-eq-empty-leq" then
              prove_implication (metisLib.METIS_TAC
                [smtstringTheory.smtstr_substr_zero_eq_empty])
            else if name = "str-substr-eq-empty-leq-len" then
              prove_implication (Tactical.THEN
                (Tactical.REPEAT Tactic.STRIP_TAC,
                 Tactical.THEN
                   (bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
                      [boolTheory.EQ_CLAUSES],
                    Tactical.THEN
                      (Tactic.irule
                         smtstringTheory.smtstr_substr_eq_empty,
                       Tactical.THEN
                          (bossLib.FULL_SIMP_TAC (bossLib.srw_ss()) [],
                          intLib.ARITH_TAC)))))
            else if name = "str-substr-combine1" then
              prove_implication (Tactical.THEN
                (bossLib.SIMP_TAC (bossLib.srw_ss())
                   [boolTheory.EQ_CLAUSES,
                    smtstringTheory.smtstr_concat_assoc],
                 Tactical.THEN
                   (Tactical.REPEAT Tactic.STRIP_TAC,
                    Tactical.THEN
                      (Tactic.MATCH_MP_TAC
                         smtstringTheory.smtstr_substr_combine_right,
                       intLib.ARITH_TAC))))
            else if name = "str-substr-combine2" then
              prove_implication (Tactical.THEN
                (bossLib.SIMP_TAC (bossLib.srw_ss())
                   [boolTheory.EQ_CLAUSES],
                 Tactical.THEN
                   (Tactical.REPEAT Tactic.STRIP_TAC,
                    Tactical.THEN
                      (Tactic.MATCH_MP_TAC
                         smtstringTheory.smtstr_substr_combine_left,
                       intLib.ARITH_TAC))))
            else if name = "str-substr-combine3" then
              prove_implication (Tactical.THEN
                (bossLib.SIMP_TAC (bossLib.srw_ss())
                   [boolTheory.EQ_CLAUSES],
                 Tactical.THEN
                   (Tactical.REPEAT Tactic.STRIP_TAC,
                    Tactical.THEN
                      (Tactic.MATCH_MP_TAC
                         smtstringTheory.smtstr_substr_combine_inner_bound,
                       intLib.ARITH_TAC))))
            else if name = "str-substr-combine4" then
              prove_implication (Tactical.THEN
                (bossLib.SIMP_TAC (bossLib.srw_ss())
                   [boolTheory.EQ_CLAUSES],
                 Tactical.THEN
                   (Tactical.REPEAT Tactic.STRIP_TAC,
                    Tactical.THEN
                      (Tactic.MATCH_MP_TAC
                         smtstringTheory.smtstr_substr_combine_actual_bound,
                       intLib.ARITH_TAC))))
            else if name = "str-substr-concat2" then
              prove_implication (metisLib.METIS_TAC
                [boolTheory.EQ_CLAUSES, integerTheory.int_ge,
                 smtstringTheory.smtstr_concat_assoc,
                 smtstringTheory.smtstr_substr_drop_concat_prefix])
            else if name = "str-substr-full" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES, integerTheory.int_ge,
                 smtstringTheory.smtstr_substr_full_bound])
            else if name = "str-substr-ctn" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_contains_substr])
            else if name = "str-substr-ctn-contra" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_substr_contains_contra])
            else if name = "str-substr-char-start-eq-len" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES, integerTheory.int_ge,
                 smtstringTheory.smtstr_len_eq_zero,
                 smtstringTheory.smtstr_substr_short_self_count])
            else if name = "str-substr-len-include" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES, integerTheory.int_ge,
                 smtstringTheory.smtstr_substr_concat_left_bound,
                 smtstringTheory.smtstr_concat_assoc])
            else if name = "str-substr-len-include-pre" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES, integerTheory.int_ge,
                 smtstringTheory.smtstr_substr_concat_prefix_bound,
                 smtstringTheory.smtstr_concat_assoc])
            else if name = "str-substr-len-norm" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES, integerTheory.int_ge,
                 smtstringTheory.smtstr_substr_count_normalize])
            else missing_recipe ()
        | RareReplace =>
            if name = "str-replace-self" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_replace_self])
            else if name = "str-replace-id" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_replace_id])
            else if name = "str-replace-no-contains" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_replace_absent])
            else if name = "str-replace-prefix" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_replace_prefix,
                 smtstringTheory.smtstr_concat_assoc])
            else if name = "str-replace-empty" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_len_eq_zero,
                 smtstringTheory.smtstr_replace_empty])
            else if name = "str-replace-all-no-contains" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_replace_all_absent])
            else if name = "str-replace-all-empty" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_replace_all_empty])
            else if name = "str-replace-all-id" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_replace_all_id])
            else if name = "str-replace-all-self" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_replace_all_self])
            else if name = "str-replace-re-none" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_replace_re_none])
            else if name = "str-replace-re-all-none" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_replace_re_all_none])
            else if name = "str-replace-dual-ctn" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_replace_preserves_contains])
            else if name = "str-replace-dual-ctn-false" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_replace_avoids_outer])
            else if name = "str-replace-self-ctn-simp" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_replace_pattern_self_contains])
            else if name = "str-replace-emp-ctn-src" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_replace_empty_source_contains])
            else if name = "str-contains-repl-char" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_replace_contains_len_one])
            else if name = "str-contains-repl-self-tgt-char" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_replace_self_contains_len_one])
            else if name = "str-contains-repl-self" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_replace_self_contains])
            else if name = "str-contains-repl-tgt" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_replace_contains_replacement])
            else if name = "str-repl-repl-len-id" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES, integerTheory.int_ge,
                 smtstringTheory.smtstr_replace_self_target])
            else if name = "str-repl-repl-src-tgt-no-ctn" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_replace_nested_source_target_absent])
            else if name = "str-repl-repl-tgt-self" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_replace_nested_target_self])
            else if name = "str-repl-repl-tgt-no-ctn" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_replace_nested_target_absent])
            else if name = "str-repl-repl-src-self" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_replace_nested_source_self])
            else if name = "str-repl-repl-src-inv-no-ctn1" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_replace_nested_source_inverse_absent1])
            else if name = "str-repl-repl-src-inv-no-ctn2" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_replace_nested_source_inverse_absent2])
            else if name = "str-repl-repl-src-inv-no-ctn3" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_replace_nested_source_inverse_absent3])
            else if name = "str-repl-repl-dual-self" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_replace_nested_dual_self])
            else if name = "str-repl-repl-dual-ite1" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_replace_nested_dual_ite1])
            else if name = "str-repl-repl-dual-ite2" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_replace_nested_dual_ite2])
            else if name = "str-repl-repl-lookahead-id-simp" then
              prove_implication
                (Tactical.THEN
                  (bossLib.SIMP_TAC (bossLib.srw_ss())
                     [boolTheory.EQ_CLAUSES, integerTheory.int_ge],
                   Tactical.THEN
                    (Tactical.REPEAT Tactic.strip_tac,
                     Tactical.THEN
                      (Tactic.irule
                       smtstringTheory.smtstr_replace_nested_lookahead_id_simp,
                       bossLib.simp []))))
            else if name = "str-substr-replace" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_substr_replace_len_one])
            else if name = "str-replace-find-base" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES, integerTheory.int_ge,
                 smtstringTheory.smtstr_replace_find,
                 smtstringTheory.smtstr_concat_assoc])
            else if name = "str-replace-find-first-concat" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES, integerTheory.int_ge,
                 smtstringTheory.smtstr_indexof_zero_nonnegative,
                 smtstringTheory.smtstr_replace_concat_after_match,
                 smtstringTheory.smtstr_replace_find,
                 smtstringTheory.smtstr_concat_assoc])
            else if name = "str-replace-find-pre" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_replace_concat_after_match,
                 smtstringTheory.smtstr_contains_concat,
                 smtstringTheory.smtstr_contains_refl,
                 smtstringTheory.smtstr_concat_assoc])
            else if name = "str-replace-one-pre" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_replace_concat_contained_suffix,
                 smtstringTheory.smtstr_contains_concat,
                 smtstringTheory.smtstr_contains_refl,
                 smtstringTheory.smtstr_concat_assoc])
            else if name = "str-eq-repl-self-emp" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_replace_self_empty_eq])
            else if name = "str-eq-repl-self-src" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_replace_self_source_eq])
            else if name = "str-eq-repl-no-change" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_replace_no_change_eq])
            else if name = "str-eq-repl-tgt-eq-len" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_replace_target_equal_length_eq])
            else if name = "str-eq-repl-len-one-emp-prefix" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_replace_empty_result_len_one])
            else if name = "str-eq-repl-emp-tgt-nemp" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_replace_empty_result_nonempty])
            else if name = "str-eq-repl-nemp-src-emp" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_replace_empty_source_nonempty])
            else missing_recipe ()
        | RareIndexof =>
            if name = "str-indexof-self" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_indexof_self])
            else if name = "str-indexof-no-contains" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_indexof_no_contains])
            else if name = "str-indexof-oob" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES, integerTheory.int_gt,
                 smtstringTheory.smtstr_indexof_oob])
            else if name = "str-indexof-oob2" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES, integerTheory.int_gt,
                 smtstringTheory.smtstr_indexof_negative_start])
            else if name = "str-indexof-find-emp" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES, integerTheory.int_ge,
                 smtstringTheory.smtstr_indexof_empty])
            else if name = "str-indexof-contains-pre" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES, integerTheory.int_gt,
                 smtstringTheory.smtstr_indexof_concat_contains,
                 smtstringTheory.smtstr_concat_assoc])
            else if name = "str-indexof-contains-concat-pre" then
              prove_implication (metisLib.METIS_TAC
                [smtstringTheory.smtstr_indexof_concat_occurrence_right,
                 smtstringTheory.smtstr_concat_assoc])
            else if name = "str-indexof-eq-irr" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES, integerTheory.int_le,
                 smtstringTheory.smtstr_indexof_suffix_equal])
            else missing_recipe ()
        | RareRegexStar => regex_family_prove ()
        | RareConversionOrder =>
            if name = "str-is-digit-elim" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_is_digit_elim])
            else if name = "str-lt-elim" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_lt_elim])
            else if name = "str-leq-empty" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_le_empty_left])
            else if name = "str-leq-empty-eq" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_le_empty_right])
            else if name = "str-from-int-no-ctn-nondigit" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES,
                 smtstringTheory.smtstr_from_int_no_nondigit_substring])
            else missing_recipe ()
        | RareRegexOther => regex_family_prove ()
        | RareRegexMembership =>
            if name = "str-in-re-range-elim" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smt_in_re_range_elim])
            else if name = "re-in-empty" orelse
               name = "str-in-re-inter-elim" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smt_in_re_def,
                 boolTheory.CONJ_ASSOC])
            else if name = "re-in-sigma" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smt_in_re_allchar_len])
            else if name = "re-in-sigma-star" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smt_in_re_star_allchar])
            else if name = "str-in-re-contains" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smt_in_re_allchar_contains])
            else if name = "str-in-re-from-int-nemp-dig-range" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [boolTheory.EQ_CLAUSES, integerTheory.int_ge,
                 smtstringTheory.smt_in_re_plus_digit,
                 smtstringTheory.smtstr_from_int_nonempty,
                 smtstringTheory.smtstr_from_int_digits])
            else if name = "str-in-re-from-int-dig-range" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smt_in_re_star_digit,
                 smtstringTheory.smtstr_from_int_digits])
            else if name = "re-in-cstring" orelse name = "re-in-comp" orelse
                    name = "str-in-re-union-elim" then
              owning_procedure ()
            else missing_recipe ()
        | RareSequence =>
            if name = "seq-rev-rev" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_rev_rev])
            else if name = "seq-len-rev" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_len_rev])
            else if name = "seq-rev-concat" then
              prove_implication (bossLib.SIMP_TAC (bossLib.srw_ss())
                [smtstringTheory.smtstr_rev_concat])
            else if name = "seq-len-unit" orelse
                    name = "seq-nth-unit" orelse
                    name = "seq-rev-unit" then
              owning_procedure ()
            else missing_recipe ()
        | _ => missing_recipe ()
      val theorem = family_prove ()
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else raise ERR name
            ("cvc5-1.3.4 RARE rule " ^ name ^
             " did not prove its exact declarative source recipe: " ^
             Feedback.message_of holerr)
    in
      discharge_rare_inventory_contract name prems theorem
    end

  fun validate_rare_inventory_contract name prems conclusion synthesized =
    let
      val declared = case conclusion of
          SOME declared => declared
        | NONE => raise ERR name
            ("cvc5-1.3.4 RARE rule " ^ name ^
             " requires an explicit declared conclusion")
      val _ = Term.aconv (Thm.concl synthesized) declared orelse
        raise ERR name
          ("cvc5-1.3.4 RARE rule " ^ name ^
           " conclusion does not match its synthesized theorem")
    in
      discharge_rare_inventory_contract name prems synthesized
    end

  fun validate_recursive_rare_inventory_contract name prems conclusion
      synthesized =
    case conclusion of
      NONE => discharge_rare_inventory_contract name prems synthesized
    | SOME _ => raise ERR name
        ("cvc5-1.3.4 recursive RARE rule " ^ name ^
         " requires its authoritative omitted conclusion")

  fun replay_rare_inventory state name prems conclusion located_args =
    case rare_inventory_lookup name of
      NONE => raise ERR "rare_inventory"
        ("internal cvc5-1.3.4 RARE inventory drift: " ^ name)
    | SOME entry =>
        let
          val args = List.map (fn (located : located_term) => #term located)
            located_args
          fun source_args recipe =
            normalize_rare_source_arguments name (#formals recipe)
              located_args
          fun source_unsupported reason =
            raise ERR name
              ("unsupported cvc5-1.3.4 RARE rule " ^ name ^ ": " ^ reason)
        in
        case #replay_kind entry of
           RareArgumentRewrite =>
             validate_rare_inventory_contract name prems conclusion
               (replay_rare_rewrite name args)
         | RareRecursiveArgumentRewrite =>
             validate_recursive_rare_inventory_contract name prems conclusion
               (replay_rare_rewrite name args)
         | RareSourceRecipe recipe =>
             replay_rare_source_recipe (#family entry) name recipe
               prems conclusion (source_args recipe)
         | RareSourceUnsupported (_, reason) =>
             source_unsupported reason
         | RareStringRecipe recipe =>
             if rare_string_recipe_name recipe = name then
               replay_inventory_string_rule name prems conclusion args
             else raise ERR name "internal TASK23 String recipe mismatch"
         | RareContainsRefl =>
             validate_rare_inventory_contract name prems conclusion
               (replay_str_contains_refl args)
         | RareContainsSplitChar =>
             replay_contains_split_char prems conclusion args
         | RareUnsupported diagnostic => raise ERR name diagnostic
        end

  fun unsupported_step ({id, rule, conclusion, ...} : step) =
    let
      val conclusion_text =
        case conclusion of NONE => "<omitted>"
        | SOME located => Library.term_to_string (#term located)
    in
      raise ERR "replay_step"
        ("unsupported CPC step: rule=" ^ #name rule ^ "; namespace=" ^
         namespace_name (#namespace rule) ^ "; step=" ^ id ^
         "; conclusion=" ^ conclusion_text)
    end

  fun replay_step strong_canon state (step : step) =
    let
      val {id, conclusion = located_conclusion, rule, premises,
        args = located_args} = step
      val conclusion = Option.map
        (fn (located : located_term) => #term located) located_conclusion
      val args = List.map (fn (located : located_term) => #term located)
        located_args
      val premise_steps = List.map
        (find_step "replay_step" state) premises
      val prems = List.map step_theorem premise_steps
      val premise_rules = List.map (lookup_rule state) premises
      fun opaque theorem =
        let
          val term = Thm.concl theorem
          val reason = "CPC rule " ^ #name rule ^
            " omitted a result containing an exact conjunction"
        in
          if use_compact_provenance term then
            exact_result
              (conjunction_free_semantic_provenance reason term) theorem
          else raw_unavailable_result reason theorem
        end
      (* Arithmetic relation rewrites construct both equality endpoints from
         their typed operands.  When the successful theorem contains no HOL
         conjunction at either endpoint, Atomic is exact: there is no erased
         conjunction boundary to recover or guess. *)
      fun conjunction_free_equality_result reason theorem =
        let val _ = boolSyntax.dest_eq (Thm.concl theorem) in
          exact_result
            (conjunction_free_semantic_provenance reason
              (Thm.concl theorem)) theorem
        end
        handle Feedback.HOL_ERR _ => unavailable_result reason theorem
      fun require_declared name theorem =
        case conclusion of
          NONE => theorem
        | SOME target =>
            if Term.aconv (Thm.concl theorem) target then theorem
            else raise ERR name
              "direct result differs from the declared conclusion"
      fun attempt work fallback =
        work () handle Feedback.HOL_ERR _ => fallback ()
      fun trans_phase name work =
        if OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" = SOME "full" then
          profile ("CPC(trans:" ^ name ^ ")") work ()
        else work ()
      (* Canonical rung shared by trans and eq_resolve: replay canonically,
         then restore the declared conclusion through the weak canonicalizer
         and, failing that, the strong one. *)
      fun canonical_rung name replay =
        let val theorem = replay prems in
          require_declared name theorem
          handle Feedback.HOL_ERR _ =>
            (restore_canonical_conclusion name conclusion
               (SmtReplayCanon.cpc_canon_rule theorem)
             handle Feedback.HOL_ERR _ =>
               restore_strong_canonical_conclusion strong_canon
                 name conclusion theorem)
        end
      fun canonical_handler name replay =
        let val exposed = List.map expose_true_equality prems in
          require_declared name (replay exposed)
        handle Feedback.HOL_ERR _ =>
          (restore_canonical_conclusion name conclusion
             (replay
               (List.map expose_true_equality
                 (canonical_premises exposed)))
           handle Feedback.HOL_ERR _ =>
             restore_strong_canonical_conclusion strong_canon
               name conclusion
               (replay
                 (List.map expose_true_equality
                   (List.map
                     (Conv.CONV_RULE strong_canon) exposed))))
        end
      fun arithmetic_bridge theorems target =
        let
          val hypotheses = HOLset.listItems
            (HOLset.fromList Term.compare
              (List.filter boolSyntax.is_eq
                (List.concat (List.map Thm.hyp theorems))))
          val assumptions = List.map Thm.ASSUME hypotheses
          fun relation_bridge proposition =
            let
              val arithmetic_type = SmtReplayCanon.is_arith_type
              fun private_integer_division tm =
                let
                  val (head, _) = boolSyntax.strip_comb tm
                  val {Thy, Name, ...} = Term.dest_thy_const head
                in
                  Thy = "integer" andalso
                  (Name = "ediv" orelse Name = "emod")
                end
                handle Feedback.HOL_ERR _ => false
              fun total_integer_division tm =
                let val (head, _) = boolSyntax.strip_comb tm in
                  Term.is_const head andalso
                  (Term.same_const head SmtReplayCanon.smt_ediv_total_tm
                   orelse Term.same_const head
                     SmtReplayCanon.smt_emod_total_tm)
                end
                handle Feedback.HOL_ERR _ => false
              fun opaque_arithmetic tm =
                arithmetic_type (Term.type_of tm) andalso
                (boolSyntax.is_cond tm orelse intSyntax.is_div tm orelse
                 intSyntax.is_mod tm orelse private_integer_division tm orelse
                 total_integer_division tm)
              fun is_relation tm =
                Lib.can arith_dest_less tm orelse
                Lib.can arith_dest_leq tm orelse
                Lib.can arith_dest_greater tm orelse
                Lib.can arith_dest_geq tm
              fun normalize_arithmetic_equality tm =
                let
                  val (left, right) = boolSyntax.dest_eq tm
                  val _ = arithmetic_type (Term.type_of left) andalso
                          arithmetic_type (Term.type_of right) orelse
                    raise Conv.UNCHANGED
                in
                  Conv.CHANGED_CONV
                    (Conv.BINOP_CONV
                      (Conv.QCONV
                        SmtReplayCanon.arith_poly_norm_conversion)) tm
                end
              fun normalize_endpoint tm =
                if is_relation tm orelse
                   arithmetic_type (Term.type_of tm) then
                  SmtReplayCanon.compose
                    [neutral_arithmetic_conv,
                     Conv.DEPTH_CONV normalize_arithmetic_equality,
                     SmtReplayCanon.cpc_operand_canon_conv,
                     SmtReplayCanon.arith_poly_norm_conversion]
                    tm
                else raise ERR "trans"
                  "middle endpoint is not arithmetic"
              fun normalized_prove target =
                let
                  val (target_left, target_right) =
                    boolSyntax.dest_eq target
                  val left_norm = normalize_endpoint target_left
                  val right_norm = normalize_endpoint target_right
                  val normalized_left =
                    boolSyntax.rhs (Thm.concl left_norm)
                  val normalized_right =
                    boolSyntax.rhs (Thm.concl right_norm)
                  val same = Term.aconv normalized_left normalized_right
                  val _ = same orelse
                    raise ERR "trans"
                      "polynomial relation endpoints differ"
                  val theorem = Thm.TRANS left_norm (Thm.SYM right_norm)
                in theorem end
              fun abstract_bridge () =
                prove_from_prems_abstracting normalized_prove
                  opaque_arithmetic [] proposition
            in
              abstract_bridge ()
              handle Feedback.HOL_ERR _ => normalized_prove proposition
            end
          fun division_prove proposition =
            let
              val total_div = SmtReplayCanon.smt_ediv_total_tm
              fun dest_total term =
                let val (head, operands) = boolSyntax.strip_comb term in
                  case operands of
                    [dividend, divisor] =>
                      if Term.same_const head total_div then
                        (dividend, divisor)
                      else raise ERR "trans" "not a totalized division"
                  | _ => raise ERR "trans" "not a totalized division"
                end
              val pairs =
                List.map intSyntax.dest_div
                  (HolKernel.find_terms intSyntax.is_div proposition) @
                List.map intSyntax.dest_mod
                  (HolKernel.find_terms intSyntax.is_mod proposition) @
                List.map dest_total
                  (HolKernel.find_terms (Lib.can dest_total) proposition)
              fun division_identities (dividend, divisor) =
                let
                  val nonzero = simpLib.SIMP_PROVE (bossLib.srw_ss ()) []
                    (boolSyntax.mk_neg
                      (boolSyntax.mk_eq (divisor, intSyntax.zero_tm)))
                  val division = Thm.SPEC dividend
                    (Thm.MP (Thm.SPEC divisor integerTheory.INT_DIVISION)
                      nonzero)
                  val identity = Thm.CONJUNCT1 division
                in
                  [identity, Thm.SYM identity]
                end
                handle Feedback.HOL_ERR _ => []
              val identities = List.concat
                (List.map division_identities pairs)
              fun adapt theorem =
                let
                  val (theorem_left, theorem_right) =
                    boolSyntax.dest_eq (Thm.concl theorem)
                  val (target_left, target_right) =
                    boolSyntax.dest_eq proposition
                  fun polynomial_bridge left right =
                    SmtReplayCanon.prove_polynomial_equality
                      (boolSyntax.mk_eq (left, right))
                in
                  if Term.aconv theorem_left target_left then
                    Thm.TRANS theorem
                      (polynomial_bridge theorem_right target_right)
                  else if Term.aconv theorem_right target_left then
                    Thm.TRANS (Thm.SYM theorem)
                      (polynomial_bridge theorem_left target_right)
                  else if Term.aconv theorem_left target_right then
                    Thm.TRANS
                      (polynomial_bridge target_left theorem_right)
                      (Thm.SYM theorem)
                  else if Term.aconv theorem_right target_right then
                    Thm.TRANS
                      (polynomial_bridge target_left theorem_left) theorem
                  else raise ERR "trans"
                    "division identity has different endpoints"
                end
            in
              (Lib.tryfind adapt identities
               handle Feedback.HOL_ERR _ =>
                 Tactical.TAC_PROOF (([], proposition),
                   bossLib.FULL_SIMP_TAC bossLib.arith_ss
                     (identities @
                      [HolSmtTheory.smt_ediv_total_def,
                       integerTheory.EDIV_DEF])))
              handle Feedback.HOL_ERR holerr =>
                raise ERR "trans"
                  ("division identity proof failed; proposition=" ^
                   Library.term_to_string proposition ^
                   "; pairs=" ^ Int.toString (List.length pairs) ^
                   "; identities=" ^ String.concatWith "; "
                     (List.map
                       (Library.term_to_string o Thm.concl) identities) ^
                   "; underlying=" ^ Feedback.message_of holerr)
            end
          fun contradiction theorem =
            let
              val (left, right) = boolSyntax.dest_eq (Thm.concl theorem)
              val (equality, proposition) =
                if Term.aconv right boolSyntax.F then (theorem, left)
                else if Term.aconv left boolSyntax.F then
                  (Thm.SYM theorem, right)
                else raise ERR "trans"
                  "division contradiction premise is not false-valued"
              val contradiction_thm = Thm.EQ_MP equality
                (division_prove proposition)
            in
              Thm.MP (Thm.SPEC target boolTheory.FALSITY) contradiction_thm
            end
          fun false_valued theorem =
            let val (left, right) = boolSyntax.dest_eq (Thm.concl theorem) in
              Term.aconv left boolSyntax.F orelse
              Term.aconv right boolSyntax.F
            end
            handle Feedback.HOL_ERR _ => false
          fun fallback () =
            (prove_from_prems division_prove
               (assumptions @ theorems) target
             handle Feedback.HOL_ERR _ =>
               arith_prove_from_prems assumptions target)
        in
          relation_bridge target
          handle Feedback.HOL_ERR _ =>
          case List.find false_valued theorems of
            SOME theorem =>
              (contradiction theorem
               handle Feedback.HOL_ERR division_error =>
                 (fallback ()
                  handle Feedback.HOL_ERR _ =>
                    raise Feedback.HOL_ERR division_error))
          | NONE => fallback ()
        end
      fun arithmetic_trans () =
        let
          fun oriented theorem reverse =
            if reverse then Thm.SYM theorem else theorem
          fun compose (next, accumulated) =
            let
              fun attempt reverse_accumulated reverse_next =
                let
                  val accumulated' =
                    oriented accumulated reverse_accumulated
                  val next' = oriented next reverse_next
                  val (_, middle_left) =
                    boolSyntax.dest_eq (Thm.concl accumulated')
                  val (middle_right, _) =
                    boolSyntax.dest_eq (Thm.concl next')
                  val bridge = arithmetic_bridge [accumulated', next']
                    (boolSyntax.mk_eq (middle_left, middle_right))
                in
                  Thm.TRANS (Thm.TRANS accumulated' bridge) next'
                end
            in
              attempt false false
              handle Feedback.HOL_ERR _ => attempt false true
              handle Feedback.HOL_ERR _ => attempt true false
              handle Feedback.HOL_ERR _ => attempt true true
            end
        in
          case prems of
            [] => raise ERR "trans" "expected CPC equality premises"
          | first :: rest => List.foldl compose first rest
        end
      fun normalized_proposition_eq_resolve () =
        let
          fun normalize theorem =
            Conv.CONV_RULE strong_canon theorem
        in
          case prems of
            [left, right] =>
              (replay_arithmetic_eq_resolve_pair (normalize left) right
               handle Feedback.HOL_ERR _ =>
                 replay_arithmetic_eq_resolve_pair (normalize right) left)
          | _ => raise ERR "eq_resolve" "expected two CPC premises"
        end
      fun eq_resolve_from_scope_hypotheses target =
        let
          val hypotheses = HOLset.listItems
            (HOLset.fromList Term.compare
              (List.concat (List.map Thm.hyp prems)))
          val _ = List.null hypotheses andalso
            raise ERR "eq_resolve" "premises have no scope hypotheses"
          val assumptions = List.map Thm.ASSUME hypotheses
        in
          arith_prove_from_prems assumptions target
          handle Feedback.HOL_ERR holerr =>
            raise ERR "eq_resolve"
              ("scope-hypothesis arithmetic failed for " ^
               Library.term_to_string
                 (boolSyntax.list_mk_imp (hypotheses, target)) ^ "; " ^
               Feedback.message_of holerr)
        end
      fun canonical_trans () =
        let
          fun direct () = require_declared "trans" (replay_trans prems)
          fun evaluated_arithmetic () =
            let
              fun is_total subterm =
                Term.is_const subterm andalso
                (Term.same_const subterm SmtReplayCanon.smt_ediv_total_tm
                 orelse Term.same_const subterm
                   SmtReplayCanon.smt_emod_total_tm)
              fun has_total theorem =
                not (List.null
                  (HolKernel.find_terms is_total (Thm.concl theorem)))
              fun arithmetic_expression_equality theorem =
                let
                  val (left, right) =
                    boolSyntax.dest_eq (Thm.concl theorem)
                  fun arithmetic_operand tm =
                    SmtReplayCanon.is_arith_type (Term.type_of tm)
                in
                  arithmetic_operand left andalso arithmetic_operand right
                end
                handle Feedback.HOL_ERR _ => false
              val evaluate_chain =
                List.exists (fn name => name = "evaluate") premise_rules
              val expression_chain =
                List.all arithmetic_expression_equality prems
            in
            if not (Option.isSome conclusion) andalso
                (evaluate_chain orelse expression_chain) andalso
                List.exists has_total prems then
              arithmetic_trans ()
            else raise ERR "trans"
              "no omitted evaluate endpoint for arithmetic preflight"
            end
          fun canonical () = canonical_rung "trans"
            (replay_canonical_trans strong_canon)
          fun fallback () =
            case conclusion of
              (* E1(b): general arithmetic implication proving is the
                 coverage terminal after canonical composition. *)
              SOME target =>
                profile "CPC(rung:canonical_trans/general-arithmetic)"
                  (fn () => arith_prove_from_prems prems target) ()
            | NONE =>
                (arithmetic_trans ()
                 handle Feedback.HOL_ERR holerr =>
                   raise ERR "trans"
                     ("checked middle-equality reconstruction failed; " ^
                      "premises=" ^ String.concatWith "; "
                        (List.map Library.thm_to_string prems) ^
                      "; underlying=" ^ Feedback.message_of holerr))
        in
          attempt direct (fn () =>
            attempt evaluated_arithmetic (fn () =>
              attempt canonical fallback))
        end
      fun canonical_eq_resolve () =
        let
          fun direct () =
            require_declared "eq_resolve" (replay_eq_resolve prems)
          fun ground_false () =
            let
              fun prove_false theorem =
                let
                  val proposition = Thm.concl theorem
                  val _ = List.null (Term.free_vars proposition) orelse
                    raise ERR "eq_resolve"
                      "ground contradiction premise has free variables"
                  val evaluation = bossLib.EVAL proposition
                  val normalized = boolSyntax.rhs (Thm.concl evaluation)
                  val _ = Term.aconv normalized boolSyntax.F orelse
                    raise ERR "eq_resolve"
                      "closed premise does not evaluate to false"
                in
                  Thm.EQ_MP evaluation theorem
                end
              val contradiction = Lib.tryfind prove_false prems
              val with_support = retain_all contradiction prems
            in
              require_declared "eq_resolve" with_support
            end
          fun arithmetic () =
            case (conclusion, enabled_eq_resolve_preflight_route prems) of
              (SOME _, SOME route) =>
                let
                  val () = profile_event
                    ("CPC(eq_resolve:preflight/" ^
                     eq_resolve_preflight_name route ^ ")")
                in
                  case route of
                    EqResolveArithmetic => require_declared "eq_resolve"
                      (replay_arithmetic_eq_resolve prems)
                  | _ => raise ERR "eq_resolve"
                      (eq_resolve_preflight_diagnostic route)
                end
            | (NONE, _) => raise ERR "eq_resolve"
                "arithmetic preflight requires a declared conclusion"
            | (_, NONE) => raise ERR "eq_resolve"
                "arithmetic preflight fast path is disabled"
          fun canonical () =
            canonical_rung "eq_resolve"
              (replay_canonical_eq_resolve strong_canon)
          fun normalized () =
            require_declared "eq_resolve"
              (normalized_proposition_eq_resolve ())
          fun fallbacks () =
            case conclusion of
              SOME target =>
                (arith_prove_from_prems prems target
                 handle Feedback.HOL_ERR _ =>
                   (eq_resolve_from_scope_hypotheses target
                    handle Feedback.HOL_ERR scope_error =>
                      (prove_cast_arithmetic prems target
                       handle Feedback.HOL_ERR cast_error =>
                         raise ERR "eq_resolve"
                           ("scope fallback: " ^
                            Feedback.message_of scope_error ^
                            "; cast fallback: " ^
                            Feedback.message_of cast_error))))
            | NONE => raise ERR "eq_resolve"
                ("canonical premises do not rewrite one another; " ^
                 "premises=" ^ String.concatWith "; "
                   (List.map (Library.term_to_string o Thm.concl) prems))
        in
          attempt direct (fn () =>
            attempt ground_false (fn () =>
              attempt arithmetic (fn () =>
                attempt canonical (fn () =>
                  attempt normalized fallbacks))))
        end
      fun canonical_resolution () =
        let
          (* Compact chain resolution may omit the conclusion while recording
             it as the first argument.  Keep that inferred endpoint available
             for restoration; a two-argument binary resolution instead
             records polarity and pivot, so its result is premise-derived. *)
          val replay_target =
            case (conclusion, args) of
              (SOME target, _) => SOME target
            | (NONE, [_, _]) => NONE
            | (NONE, target :: _) => SOME target
            | (NONE, []) => NONE
          fun restore theorem =
            case replay_target of
              NONE => theorem
            | SOME target =>
                Thm.EQ_MP
                  (Thm.SYM (SmtReplayCanon.cpc_operand_canon_conv target))
                  theorem
          fun restore_strong theorem =
            restore_with strong_canon "strong" "resolution"
              replay_target theorem
          fun normalized_resolution () =
            let
              val normalized_prems = List.map
                (Conv.CONV_RULE SmtReplayCanon.cpc_operand_canon_conv) prems
              val normalized_conclusion =
                Option.map canonical_operand conclusion
              val normalized_args = List.map canonical_operand args
            in
              restore (replay_resolution normalized_prems
                normalized_conclusion normalized_args)
            end
          fun integer_resolution () =
            let
              val integer_prems = List.map
                (Conv.CONV_RULE cpc_integer_normal_form_conv) prems
              val integer_conclusion = Option.map (fn target =>
                boolSyntax.rhs
                  (Thm.concl (cpc_integer_normal_form_conv target)))
                conclusion
              val integer_args = List.map (fn argument =>
                boolSyntax.rhs
                  (Thm.concl (cpc_integer_normal_form_conv argument))) args
              val theorem = replay_resolution integer_prems
                integer_conclusion integer_args
            in
              restore_with cpc_integer_normal_form_conv
                "integer spelling" "resolution" replay_target theorem
            end
        in
        (require_declared "resolution"
           (replay_resolution prems conclusion args)
         handle Feedback.HOL_ERR _ =>
           (normalized_resolution ()
            handle Feedback.HOL_ERR _ =>
              (integer_resolution ()
               handle Feedback.HOL_ERR _ =>
               let
                val strong_prems =
                  List.map (Conv.CONV_RULE strong_canon) prems
                val strong_args = List.map (fn arg =>
                  boolSyntax.rhs
                    (Thm.concl (strong_canon arg))) args
                val strong_conclusion = Option.map (fn target =>
                  boolSyntax.rhs
                    (Thm.concl (strong_canon target))) conclusion
                val theorem =
                  case strong_conclusion of
                    SOME target =>
                      if Term.aconv target boolSyntax.T then
                        retain_all boolTheory.TRUTH strong_prems
                      else replay_resolution strong_prems
                        strong_conclusion strong_args
                  | NONE => replay_resolution strong_prems
                      strong_conclusion strong_args
              in
                restore_strong theorem
              end)))
        handle Feedback.HOL_ERR _ =>
          (case replay_target of
             SOME target =>
               (arith_prove_from_prems prems target
                handle Feedback.HOL_ERR holerr =>
                  raise ERR "resolution"
                    ("explicit target resolution failed; target=" ^
                     Library.term_to_string target ^ "; premises=" ^
                     String.concatWith "; "
                       (List.map
                         (Library.term_to_string o Thm.concl) prems) ^
                     "; arithmetic fallback: " ^
                     Feedback.message_of holerr))
           | NONE => raise ERR "resolution"
               ("canonical CPC clauses do not resolve; premises=" ^
                String.concatWith "; "
                  (List.map (Library.term_to_string o Thm.concl) prems) ^
                "; arguments=" ^ String.concatWith "; "
                  (List.map Library.term_to_string args)))
        end
      fun resolution_observation_inputs () =
        let
          val clauses = List.map (#clause o #result) premise_steps
          fun named_terms label terms = Lib.mapi
            (fn index => fn term =>
              (label ^ Int.toString index, term)) terms
          val occurrence_terms = List.concat (Lib.mapi
            (fn index => fn clause => case clause of NONE => []
              | SOME clause => named_terms
                  ("premise-literal/" ^ Int.toString index ^ "/")
                  (SmtClause.literals clause)) clauses)
          val premise_metadata = List.concat (Lib.mapi
            (fn index => fn (name, clause) =>
              [("premise-id/" ^ Int.toString index, name),
               ("clause-arity/" ^ Int.toString index,
                case clause of NONE => "unknown"
                  | SOME clause => Int.toString
                      (List.length (SmtClause.literals clause)))])
            (ListPair.zip (premises, clauses)))
          fun definition index
              (SmtLib.EmittedDefinition
                {emitted_symbol, replay_head, unfolding}) =
            case emitted_symbol of
              SmtLib.EncodedSymbol {hol_term, smt_symbol, arity} =>
                ((smt_symbol, replay_head, unfolding),
                 ("emitted-hol-term/" ^ Int.toString index, hol_term),
                 ("emitted-arity/" ^ Int.toString index, Int.toString arity))
            | _ => raise ERR "resolution_observation_inputs"
                "emitted definition lacks its exact encoded-symbol record"
          val emitted = Lib.mapi definition (#translation_definitions state)
        in
          {domain = "cpc/resolution", identifier = id,
           premises = Lib.mapi (fn index => fn theorem =>
             (Int.toString index, theorem)) prems,
           terms = (case conclusion of NONE => []
              | SOME target => [("target", target)]) @
             named_terms "argument/" args @ occurrence_terms @
             List.map #2 emitted,
           scope = HOLset.listItems (#asserted_hyps state) @ #scope_hyps state,
           definitions = List.map #1 emitted,
           metadata = premise_metadata @ List.map #3 emitted}
        end
      fun occurrence_resolution_result () =
        let
          val normalized = ref false
          val needs_normalization = ref false
          val normalize_literals = SmtClause.new_normalizer
            SmtReplayCanon.cpc_operand_canon_conv
          fun normalize_clause clause =
            if not (!normalized) then clause
            else let
              val (literals, bridge) = normalize_literals
                (SmtClause.literals clause)
            in SmtClause.from_literals literals
              (Thm.EQ_MP bridge (SmtClause.theorem clause)) end
          fun decline reason =
            (if reason = "literal-alignment" orelse reason = "binary-pivot"
             then needs_normalization := true else ();
             profile_event ("CPC(occurrence-decline:" ^ reason ^ ")"); NONE)
          fun clauses [] = SOME []
            | clauses (premise :: rest) =
                case (#clause (#result premise), clauses rest) of
                  (SOME clause, SOME tail) => SOME (normalize_clause clause :: tail)
                | _ => NONE
          fun signed polarity pivot =
            let val literal =
              if Term.type_of pivot <> Type.bool then NONE
              else if Term.aconv polarity boolSyntax.T then SOME pivot
              else if Term.aconv polarity boolSyntax.F then
                SOME (case Lib.total boolSyntax.dest_neg pivot of
                  SOME body => body | NONE => boolSyntax.mk_neg pivot)
              else NONE
            in Option.map (fn term => if not (!normalized) then term
              else List.hd (#1 (normalize_literals [term]))) literal end
          fun pivots [] [] = SOME []
            | pivots (polarity :: polarities) (pivot :: terms) =
                (case (signed polarity pivot, pivots polarities terms) of
                   (SOME literal, SOME tail) => SOME (literal :: tail)
                 | _ => NONE)
            | pivots _ _ = NONE
          fun finish target clause =
            case target of
              NONE => SOME (clause_result
                "annotated resolution has explicit occurrences" clause)
            | SOME located =>
                (case source_clause_literals located of
                   NONE => decline "target-boundaries"
                 | SOME literals =>
                     let
                       val (target_literals, bridge) =
                         if !normalized then normalize_literals literals
                         else (literals, Thm.REFL (SmtClause.term literals))
                     in case SmtClause.align target_literals clause of
                         NONE => decline "literal-alignment"
                       | SOME aligned => SOME (clause_result
                           "annotated resolution has explicit occurrences"
                           (SmtClause.from_literals literals
                             (Thm.EQ_MP (Thm.SYM bridge)
                               (SmtClause.theorem aligned)))) end)
          fun chain target annotations premises =
            let val count = List.length premises - 1 in
              if count < 1 orelse List.length annotations <> 2 * count then
                decline "annotation-arity"
              else case (pivots (List.take (annotations, count))
                  (List.drop (annotations, count)),
                  source_clause_literals target) of
                (NONE, _) => decline "polarity"
              | (_, NONE) => decline "target-boundaries"
              | (SOME signed_pivots, SOME target_literals) =>
                  let
                    val (destination, bridge) = if !normalized then
                        normalize_literals target_literals
                      else (target_literals,
                        Thm.REFL (SmtClause.term target_literals))
                  in case SmtClause.resolve_chain
                      {pivots = signed_pivots, premises = premises,
                       target = SOME destination} of
                      NONE => decline "literal-alignment"
                    | SOME aligned => SOME (clause_result
                        "annotated resolution has explicit occurrences"
                        (SmtClause.from_literals target_literals
                          (Thm.EQ_MP (Thm.SYM bridge)
                            (SmtClause.theorem aligned))))
                  end
            end
          fun run () = case clauses premise_steps of
            NONE => decline "premise-boundaries"
          | SOME clause_prems =>
              case (located_args, args, clause_prems) of
                ([_, _], [polarity, pivot], [first, second]) =>
                  (case signed polarity pivot of
                     NONE => decline "polarity"
                   | SOME literal =>
                       let
                         val opposite = case Lib.total boolSyntax.dest_neg
                             literal of SOME body => body
                           | NONE => boolSyntax.mk_neg literal
                       in
                         if not (SmtClause.contains literal first andalso
                             SmtClause.contains opposite second) then
                           decline "binary-pivot"
                         else case SmtClause.resolve_chain
                             {pivots = [literal], premises = [first, second],
                              target = NONE} of
                           NONE => decline "binary-pivot"
                         | SOME result => finish located_conclusion result
                       end)
              | (target :: _, _ :: annotations, _) =>
                  if Option.getOpt (Option.map (fn located =>
                      not (Term.aconv (#term located) (#term target)))
                      located_conclusion, false) then
                    decline "conflicting-targets"
                  else chain target annotations clause_prems
              | _ => decline "annotations"
          fun complete_raw () =
            let
              val destination = case located_conclusion of
                  SOME target => SOME target
                | NONE => if List.length args = 2 then NONE
                    else Lib.total List.hd located_args
            in case destination of
                NONE => NONE
              | SOME target => case source_clause_literals target of
                  NONE => NONE
                | SOME literals =>
                    let
                      val source = SmtCircuitSat.balanced_conjunction prems
                      val law = semantic_tseitin_law
                        (Thm.concl source) (#term target)
                      val theorem = Thm.MP law source
                    in SOME (clause_result
                      "complete original-premise Boolean implication"
                      (SmtClause.from_literals literals theorem)) end
            end
            handle HolSatLib.SAT_cex _ => NONE
                 | HolSatLib.SAT_satisfiable _ => NONE
                 | Conv.UNCHANGED => NONE
                 | Feedback.HOL_ERR holerr =>
                     if SmtResource.is_resource_gate holerr then
                       raise Feedback.HOL_ERR holerr
                     else NONE
        in
          case run () of
            SOME result => SOME result
          | NONE => if not (!needs_normalization) then NONE
            else if List.length args = 2 andalso
                not (Option.isSome located_conclusion) then
              decline "normalization-without-target"
            else
              (* A structural decline need not require a theory rewrite.
                 Check the complete recorded obligation before normalizing
                 opaque literals; retain normalization for ordinary decline. *)
              case profile "CPC(rung:resolution/complete_raw)"
                  (fn () => complete_raw ()) () of
                SOME result => SOME result
              | NONE => (normalized := true;
                  profile "CPC(rung:resolution/normalized_occurrences)" run ())
        end
      fun occurrence_resolution_or_fallback () =
        case profile "CPC(rung:resolution/occurrences)"
            (fn () => occurrence_resolution_result ()
              handle Feedback.HOL_ERR holerr =>
                if SmtResource.is_resource_gate holerr then
                  raise Feedback.HOL_ERR holerr
                else (profile_event "CPC(occurrence-decline:conversion)";
                  NONE)) () of
          SOME result => result
        | NONE =>
            let
              val theorem = canonical_resolution ()
              val recorded = case located_conclusion of
                  SOME target => SOME target
                | NONE =>
                    if List.length prems > 1 andalso
                        List.length located_args = 2 * List.length prems - 1
                    then Lib.total List.hd located_args else NONE
            in case recorded of
                SOME target =>
                  if Term.aconv (Thm.concl theorem) (#term target) then
                    located_result "checked resolution recorded target"
                      theorem target
                  else opaque theorem
              | NONE => opaque theorem
            end
      fun canonical_reordering () =
        let
          val target = expect_one_arg "reordering" args
          fun contains_real_div term =
            Library.contains_const SmtReplayCanon.smt_rdiv_tm term orelse
            not (List.null
              (HolKernel.find_terms realSyntax.is_div term))
          val uses_real_div =
            List.exists contains_real_div
              (target :: List.map Thm.concl prems)
          fun real_div_reordering () =
            if uses_real_div then
              profile "CPC(rung:reordering/real_div)"
                (fn () => replay_normalized_reordering
                  (real_div_reordering_conv strong_canon) prems target) ()
            else
              raise ERR "reordering"
                "real-division normalization is inapplicable"
        in
          replay_normalized_reordering SmtReplayCanon.cpc_canon_conv
            prems target
          handle Feedback.HOL_ERR _ =>
            real_div_reordering ()
          handle Feedback.HOL_ERR _ =>
            replay_normalized_reordering strong_canon prems target
        end
      fun canonical_cong () =
        restore_canonical_conclusion "cong" conclusion
          (replay_cong (canonical_conclusion conclusion)
            (List.map canonical_term args) (canonical_premises prems))
      fun canonical_cong_result_with canon description =
        case conclusion of
          SOME _ => unavailable_result
            ("declared " ^ description ^
             " congruence uses its exact conclusion")
            (canonical_cong ())
        | NONE =>
            let
              fun normalized_term term =
                boolSyntax.rhs (Thm.concl (canon term))
              val normalized_args = List.map normalized_term args
              val normalized_prems =
                List.map (Conv.CONV_RULE canon) prems
            in
              case (located_args, normalized_args) of
                ([source], [normalized_source]) =>
                  let
                    val source_normalization = canon (#term source)
                    val normalized_located = {
                      term = normalized_source,
                      provenance = align_canonical_provenance
                        canon (#term source) normalized_source
                        (#provenance source)
                    }
                    fun normalized_step
                        ((premise_step : replayed_step), normalized_theorem) =
                      let
                        val original_theorem = step_theorem premise_step
                        val normalized_provenance =
                          align_canonical_provenance
                            canon (Thm.concl original_theorem)
                            (Thm.concl normalized_theorem)
                            (step_provenance premise_step)
                      in
                        {rule_name = #rule_name premise_step,
                         result = exact_result normalized_provenance
                           normalized_theorem}
                      end
                    val normalized_steps = ListPair.mapEq normalized_step
                      (premise_steps, normalized_prems)
                    val exact = replay_exact_cong_result NONE
                      normalized_located normalized_steps
                    val theorem = Thm.TRANS source_normalization
                      (result_theorem exact)
                    val rewritten_provenance =
                      case #provenance (result_located exact) of
                        EqualityProvenance (_, right) => right
                      | other => other
                  in
                    exact_result
                      (EqualityProvenance
                        (#provenance source, rewritten_provenance))
                      theorem
                  end
              | _ => raise ERR "cong_provenance"
                  (description ^
                   " congruence lacks one exact source occurrence")
            end
      fun canonical_cong_result () =
        canonical_cong_result_with SmtReplayCanon.cpc_canon_conv
          "canonical"
      fun strong_canonical_cong_result () =
        canonical_cong_result_with strong_canon
          "strong canonical"
      fun integer_spelling_cong_result () =
        canonical_cong_result_with cpc_integer_normal_form_conv
          "integer spelling canonical"
      fun reducing_cong () =
        let
          val source = expect_one_arg "cong" args
          val polynomial_normalization = Conv.QCONV
            SmtReplayCanon.arith_poly_norm_conversion source
          val polynomial_source =
            boolSyntax.rhs (Thm.concl polynomial_normalization)
          val ground_normalization =
            Conv.QCONV ground_neutral_arithmetic_conv polynomial_source
          val normalization =
            Thm.TRANS polynomial_normalization ground_normalization
          val normalized_source =
            boolSyntax.rhs (Thm.concl normalization)
          (* Once [normalization] is exactly the declared conclusion, an
             unused premise is logically irrelevant, but still contributes
             its hypotheses. *)
          fun retained () = retain_all normalization prems
          val theorem =
            (Thm.TRANS normalization
              (replay_cong NONE [normalized_source] prems)
             handle Feedback.HOL_ERR _ => retained ())
        in
          require_declared "cong" theorem
          handle Feedback.HOL_ERR _ =>
            restore_canonical_conclusion "cong" conclusion
              (SmtReplayCanon.cpc_canon_rule theorem)
        end
      fun reducing_cong_result () =
        let
          val source =
            case located_args of
              [located] => located
            | _ => raise ERR "cong_provenance"
                "reducing congruence lacks one exact source occurrence"
          val polynomial_conv = Conv.QCONV
            SmtReplayCanon.arith_poly_norm_conversion
          val polynomial_normalization = polynomial_conv (#term source)
          val polynomial_source = boolSyntax.rhs
            (Thm.concl polynomial_normalization)
          val polynomial_provenance = align_canonical_provenance
            polynomial_conv (#term source) polynomial_source
            (#provenance source)
          val ground_conv = Conv.QCONV ground_neutral_arithmetic_conv
          val ground_normalization = ground_conv polynomial_source
          val normalization = Thm.TRANS polynomial_normalization
            ground_normalization
          val normalized_source = boolSyntax.rhs (Thm.concl normalization)
          val normalized_provenance = align_canonical_provenance
            ground_conv polynomial_source normalized_source
            polynomial_provenance
          val normalized_located = {
            term = normalized_source,
            provenance = normalized_provenance
          }
          fun normalize_step (premise_step : replayed_step) =
            let
              val original_theorem = step_theorem premise_step
              val polynomial_theorem =
                Conv.CONV_RULE polynomial_conv original_theorem
              val polynomial_premise_provenance =
                align_canonical_provenance polynomial_conv
                  (Thm.concl original_theorem)
                  (Thm.concl polynomial_theorem)
                  (step_provenance premise_step)
              val normalized_theorem =
                Conv.CONV_RULE ground_conv polynomial_theorem
              val normalized_premise_provenance =
                align_canonical_provenance ground_conv
                  (Thm.concl polynomial_theorem)
                  (Thm.concl normalized_theorem)
                  polynomial_premise_provenance
            in
              {rule_name = #rule_name premise_step,
               result = exact_result normalized_premise_provenance
                 normalized_theorem}
            end
            handle Feedback.HOL_ERR holerr =>
              raise ERR "cong_provenance"
                ("reducing congruence could not normalize premise " ^
                 Library.term_to_string
                   (Thm.concl (step_theorem premise_step)) ^ "; " ^
                 Feedback.message_of holerr)
          val normalized_steps = List.map normalize_step premise_steps
        in
          let
            val exact = replay_exact_cong_result NONE normalized_located
              normalized_steps
              handle Feedback.HOL_ERR holerr =>
                raise ERR "cong_provenance"
                  ("reducing congruence exact rewrite failed: " ^
                   Feedback.message_of holerr ^ "; source=" ^
                   Library.term_to_string normalized_source ^
                   "; premises=" ^ String.concatWith "; "
                     (List.map (fn premise =>
                       Library.term_to_string
                         (Thm.concl (step_theorem premise)) ^
                       " [" ^ provenance_shape
                         (step_provenance premise) ^ "]")
                       normalized_steps))
            val theorem = Thm.TRANS normalization (result_theorem exact)
            val result = result_located exact
          in
            exact_result
              (EqualityProvenance
                (#provenance source,
                 (case #provenance result of
                    EqualityProvenance (_, right) => right
                  | other => other)))
              theorem
          end
        end
      (* Exact CPC occurrence provenance is needed while a rewrite could
         otherwise guess an erased conjunction boundary.  Once every
         premise is an ordinary HOL equality, however, the kernel can lift
         that equality through the elaborated source term directly.  This
         final route is useful when an atomic Boolean consumer (for example
         [smt_in_re]) is replaced by a conjunction: it consumes each premise
         once, in CPC order, without treating RegLan language equivalence as
         HOL equality. *)
      fun bounded_ordinary_cong_result () =
        let
          val source = expect_one_arg "cong" args
          val _ = List.all (boolSyntax.is_eq o Thm.concl) prems orelse
            raise ERR "cong"
              "ordinary congruence fallback requires equality premises"
          val maximum = SmtResource.max_term_nodes_for "String"
          fun replay source =
            let
              val _ = SmtResource.check_dag_size_with_limit
                "String" "cpc-ordinary-cong" maximum
                (SmtResource.dag_nodes_up_to maximum source)
              val theorem = replay_cong NONE [source] prems
              fun endpoint_provenance () =
                case (located_args, premise_steps) of
                  ([located_source], [premise_step]) =>
                    let
                      val (theorem_left, theorem_right) =
                        boolSyntax.dest_eq (Thm.concl theorem)
                      val _ = Term.aconv theorem_left (#term located_source)
                        orelse raise ERR "cong_provenance"
                          "ordinary congruence source endpoint changed"
                      val (premise_left, premise_right) = boolSyntax.dest_eq
                        (Thm.concl (step_theorem premise_step))
                      val (left_provenance, right_provenance) =
                        case step_provenance premise_step of
                          EqualityProvenance endpoints => endpoints
                        | provenance =>
                            (UnavailableProvenance
                               ("congruence left endpoint inherited from " ^
                                provenance_shape provenance),
                             UnavailableProvenance
                               ("congruence right endpoint inherited from " ^
                                provenance_shape provenance))
                      fun strip_binder destination term 0 = term
                        | strip_binder destination term count =
                            let
                              val (_, body) =
                                if destination = "forall" then
                                  boolSyntax.dest_forall term
                                else boolSyntax.dest_exists term
                            in strip_binder destination body (count - 1) end
                      fun rewrite_provenance source destination provenance =
                        if Term.aconv source premise_left andalso
                           Term.aconv destination premise_right then
                          right_provenance
                        else if Term.aconv source premise_right andalso
                                Term.aconv destination premise_left then
                          left_provenance
                        else if Term.aconv source destination then provenance
                        else
                          case provenance of
                            ApplicationProvenance (head, children) =>
                              let
                                val (source_head, source_arguments) =
                                  boolSyntax.strip_comb source
                                val (destination_head,
                                     destination_arguments) =
                                  boolSyntax.strip_comb destination
                                val _ = Term.aconv source_head destination_head
                                  orelse raise ERR "cong_provenance"
                                    "ordinary congruence changed an operator"
                                val _ =
                                  List.length source_arguments =
                                  List.length destination_arguments andalso
                                  List.length source_arguments =
                                  List.length children orelse
                                  raise ERR "cong_provenance"
                                    "ordinary congruence changed operator arity"
                              in
                                ApplicationProvenance
                                  (head, ListPair.mapEq
                                    (fn ((source_argument,
                                          destination_argument), child) =>
                                      rewrite_provenance source_argument
                                        destination_argument child)
                                    (ListPair.zip
                                      (source_arguments,
                                       destination_arguments), children))
                              end
                          | BinderBlockProvenance (head, size, body) =>
                              BinderBlockProvenance
                                (head, size,
                                 rewrite_provenance
                                   (strip_binder head source size)
                                   (strip_binder head destination size) body)
                          | BinderProvenance (head, body) =>
                              let
                                val source_body =
                                  strip_binder head source 1
                                val destination_body =
                                  strip_binder head destination 1
                              in
                                BinderProvenance
                                  (head, rewrite_provenance source_body
                                    destination_body body)
                              end
                          | _ => raise ERR "cong_provenance"
                              "ordinary congruence source shell is not exact"
                      val result_provenance = rewrite_provenance
                        (#term located_source) theorem_right
                        (#provenance located_source)
                    in
                      EqualityProvenance
                        (#provenance located_source, result_provenance)
                    end
                | _ => raise ERR "cong_provenance"
                    "ordinary congruence is not unary"
            in
              exact_result (endpoint_provenance ()) theorem
              handle Feedback.HOL_ERR holerr => unavailable_result
                ("ordinary CPC congruence lifted by kernel equality: " ^
                 Feedback.message_of holerr) theorem
            end
        in
          SmtResource.with_resource_step_time
            "String" "cpc-ordinary-cong" replay source
        end
      (* This rule-specific result validates every SKOLEMIZE premise,
         source boundary, and declared conclusion before a generic theorem
         with the same conclusion can be reused.  On a cache miss dispatch
         consumes it; NONE is retained only so an ablation can demonstrate
         that dispatch itself also fails closed. *)
      val rule_preflight =
        ((case #replay_handler rule of
            "skolemize" => SOME
              (skolemize_preflight conclusion located_args premise_steps)
          | _ => NONE)
         handle Feedback.HOL_ERR holerr =>
           if SmtResource.is_resource_gate holerr then
             raise Feedback.HOL_ERR holerr
           else
             raise ERR "replay_step"
               ("CPC step " ^ id ^ " (rule " ^ #name rule ^
                ") failed preflight: " ^ Feedback.message_of holerr))
      (* Cache/proforma probe follows every rule-specific preflight.  We can
         only probe a declared conclusion; omitted CPC conclusions are
         rule-derived. *)
      fun omitted_conclusion () =
            (#omitted_bypasses (#cache_stats state) :=
               !(#omitted_bypasses (#cache_stats state)) + 1;
             profile_event "CPC(cache:omitted_conclusion)";
             NONE)
      val cached =
        if #replay_handler rule = "scope" then
          (case conclusion of
             NONE => omitted_conclusion ()
           | SOME _ =>
               (profile_event "CPC(cache:scope_bypass)"; NONE))
        else case conclusion of
          SOME target => (SOME (cached_thm state target)
            handle Feedback.HOL_ERR _ => NONE)
        | NONE => omitted_conclusion ()
      val (state, result) =
        if #replay_handler rule = "scope" then
          let
            val (state, theorem) =
              profile ("CPC(handler:" ^ namespace_name (#namespace rule) ^
                "/" ^ #name rule ^ ")")
                (fn () => replay_scope state prems) ()
          in
            (state, opaque theorem)
          end
        else
          let
            val result = case cached of
              SOME theorem =>
                (case located_conclusion of
                   SOME located =>
                     located_result "cached CPC step" theorem located
                 | NONE => raise ERR "replay_step"
                     "omitted CPC conclusion unexpectedly used theorem cache")
            | NONE =>
              (profile ("CPC(handler:" ^ namespace_name (#namespace rule) ^
                 "/" ^ #name rule ^ ")") (fn () =>
               (case #replay_handler rule of
           "refl" =>
               let
                 val theorem = replay_refl conclusion args
                 val provenance =
                   case located_args of
                     [located] => EqualityProvenance
                       (#provenance located, #provenance located)
                   | _ => UnavailableProvenance
                       "refl lacks one exact operand occurrence"
               in exact_result provenance theorem end
           | "eq_refl" =>
               let
                 val theorem = replay_eq_refl args
                 val provenance =
                   case located_args of
                     [located] => EqualityProvenance
                       (#provenance located, #provenance located)
                   | _ => UnavailableProvenance
                       "eq_refl lacks one exact operand occurrence"
               in exact_result provenance theorem end
           | "symm" => replay_symm_result premise_steps
           | "trans" =>
               (if List.exists (is_reglan_equiv o Thm.concl) prems then
                  unavailable_result
                    "RegLan transitivity uses semantic language equivalence"
                    (require_declared "trans" (replay_trans prems))
                else case conclusion of
                  SOME _ => opaque (canonical_trans ())
                | NONE =>
                    (case trans_phase "classify" (fn () =>
                       let
                         val measures = trans_phase "measure" (fn () =>
                           List.map (fn premise =>
                             let
                               val term = Thm.concl premise
                               val dag_nodes = SmtResource.dag_nodes_up_to
                                 (max_exact_provenance_dag_nodes + 1) term
                               val tree_large =
                                 not (Option.isSome (Term.term_size_bounded
                                   max_exact_provenance_dag_nodes term))
                             in (dag_nodes, tree_large) end) prems)
                         val large = List.exists
                           (fn (dag_nodes, tree_large) =>
                             dag_nodes > max_exact_provenance_dag_nodes orelse
                             tree_large) measures
                       in
                         if large then
                           (SOME (trans_phase "shared" (fn () =>
                              replay_shared_trans_result premise_steps))
                            handle Feedback.HOL_ERR holerr =>
                              if SmtResource.is_resource_gate holerr then
                                raise Feedback.HOL_ERR holerr
                              else NONE)
                         else NONE
                       end) of
                       SOME result => result
                     | NONE =>
                    let
                      val (theorem, provenance) =
                        (trans_phase "direct" (fn () =>
                           replay_trans_with_provenance premise_steps)
                         handle Feedback.HOL_ERR direct_error =>
                           let
                             val canonical =
                               replay_canonical_trans_with_provenance
                                 strong_canon
                                 premise_steps
                           in
                             canonical
                           end
                           handle Feedback.HOL_ERR canonical_error =>
                             ((let
                                 val shared =
                                   replay_shared_trans_result premise_steps
                               in
                                 (result_theorem shared,
                                  result_provenance shared)
                               end)
                              handle Feedback.HOL_ERR shared_error =>
                                if SmtResource.is_resource_gate shared_error then
                                  raise Feedback.HOL_ERR shared_error
                                else
                                  (canonical_trans (),
                                   UnavailableProvenance
                                     ("trans exact endpoint unavailable; " ^
                                      "direct: " ^
                                      Feedback.message_of direct_error ^
                                      "; canonical: " ^
                                      Feedback.message_of canonical_error ^
                                      "; shared: " ^
                                      Feedback.message_of shared_error ^
                                      "; premises: " ^
                                      String.concatWith "; "
                                        (List.map (fn premise =>
                                          Library.term_to_string
                                            (Thm.concl
                                              (step_theorem premise)) ^
                                          " [" ^ provenance_shape
                                            (step_provenance premise) ^ "]")
                                          premise_steps)))))
                    in trans_phase "result" (fn () =>
                      exact_result provenance theorem) end)
                    )
           | "cong" =>
               (if Option.getOpt
                     (Option.map is_reglan_equiv conclusion, false) orelse
                   List.exists (is_reglan_equiv o Thm.concl) prems then
                  (case conclusion of
                     SOME _ => unavailable_result
                       "RegLan congruence uses semantic language equivalence"
                       (replay_reglan_cong conclusion prems)
                   | NONE =>
                       let val source = expect_one_arg "cong" args in
                         unavailable_result
                           "RegLan congruence uses semantic language equivalence"
                           (if is_reglan_equiv source then
                              replay_reglan_cong_from_source source prems
                            else if Type.compare
                              (Term.type_of source,
                               reglan_ty) = EQUAL then
                              replay_reglan_producer_cong_from_source
                                source prems
                            else
                              replay_reglan_consumer_cong_from_source
                                source prems)
                       end)
                else
               ((case (conclusion, located_args) of
                   (NONE, [source]) =>
                    let
                      val dag_nodes = SmtResource.dag_nodes_up_to
                        (max_exact_provenance_dag_nodes + 1) (#term source)
                      val exact_small =
                        dag_nodes <= max_exact_provenance_dag_nodes andalso
                        Option.isSome (Term.term_size_bounded
                          (16 * max_exact_provenance_dag_nodes)
                          (#term source))
                    in
                       if #name rule = "nary_cong" then
                         (* NARY_CONG is an operandwise rule.  Rebuild its
                            source application with checked kernel congruence
                            at the immediate argument spine; non-flat inputs
                            use the general DAG reconstruction. *)
                         raw_unavailable_result
                           "n-Cong n-ary congruence checked operandwise"
                           (replay_nary_cong (#term source) prems)
                       else if not exact_small andalso
                               not (has_binder_shell (#provenance source)) then
                         raw_unavailable_result
                           "congruence checked operandwise"
                           (replay_direct_nary_cong (#term source) prems)
                       else
                         (replay_exact_cong_result NONE source premise_steps
                          handle Feedback.HOL_ERR holerr =>
                            if SmtResource.is_resource_gate holerr then
                              raise Feedback.HOL_ERR holerr
                            else
                            if #name rule = "nary_cong" then
                              raw_unavailable_result
                                "n-Cong n-ary congruence checked directly"
                                (replay_direct_nary_cong
                                  (#term source) prems)
                            else if #name rule = "cong" andalso
                                    not (has_binder_shell
                                      (#provenance source)) then
                              raw_unavailable_result
                                "congruence exact provenance unavailable"
                                (replay_direct_nary_cong
                                  (#term source) prems)
                            else raise ERR "cong"
                              "exact congruence reconstruction failed")
                     end
                | _ => unavailable_result
                     "declared congruence uses its exact conclusion"
                     (require_declared "cong"
                       (replay_cong conclusion args prems)))
                handle Feedback.HOL_ERR direct_error =>
                  (canonical_cong_result ()
                   handle Feedback.HOL_ERR canonical_error =>
                     (integer_spelling_cong_result ()
                      handle Feedback.HOL_ERR spelling_error =>
                        (strong_canonical_cong_result ()
                         handle Feedback.HOL_ERR strong_error =>
                           (case conclusion of
                              NONE =>
                                (reducing_cong_result ()
                                 handle Feedback.HOL_ERR reducing_error =>
                                   if SmtResource.is_resource_gate
                                        reducing_error
                                   then raise Feedback.HOL_ERR reducing_error
                                   else
                                     (bounded_ordinary_cong_result ()
                                      handle Feedback.HOL_ERR ordinary_error =>
                                        if SmtResource.is_resource_gate
                                             ordinary_error
                                        then
                                          raise Feedback.HOL_ERR ordinary_error
                                        else
                                          raise ERR "cong_provenance"
                                            ("direct: " ^
                                             Feedback.message_of
                                               direct_error ^
                                             "; canonical: " ^
                                             Feedback.message_of
                                               canonical_error ^
                                             "; integer spelling: " ^
                                             Feedback.message_of
                                               spelling_error ^
                                             "; strong: " ^
                                             Feedback.message_of
                                               strong_error ^
                                             "; reducing: " ^
                                             Feedback.message_of
                                               reducing_error ^
                                             "; ordinary: " ^
                                             Feedback.message_of
                                               ordinary_error)))
                            | SOME _ => unavailable_result
                                ("congruence exact occurrence unavailable; " ^
                                 "direct: " ^
                                 Feedback.message_of direct_error ^
                                 "; canonical: " ^
                                 Feedback.message_of canonical_error ^
                                 "; integer spelling: " ^
                                 Feedback.message_of spelling_error ^
                                 "; strong: " ^
                                 Feedback.message_of strong_error)
                                (reducing_cong ())))))))
           | "ho_cong" => opaque ( replay_ho_cong prems)
           | "beta_reduce" => opaque ( replay_beta_reduce args)
           | "lambda_elim" => opaque ( replay_lambda_elim args)
           | "eq_resolve" =>
               (case conclusion of
                  SOME _ => opaque (canonical_eq_resolve ())
                | NONE =>
                    let
                      val (theorem, provenance) =
                        (replay_eq_resolve_with_provenance premise_steps
                         handle Feedback.HOL_ERR _ =>
                           (replay_canonical_eq_resolve_with_provenance
                              SmtReplayCanon.cpc_operand_canon_conv
                              premise_steps
                            handle Feedback.HOL_ERR _ =>
                              (replay_canonical_eq_resolve_with_provenance
                                 cpc_integer_normal_form_conv premise_steps
                               handle Feedback.HOL_ERR _ =>
                                 (replay_canonical_eq_resolve_with_provenance
                                    cpc_ground_arithmetic_guard_conv
                                    premise_steps
                                  handle Feedback.HOL_ERR _ =>
                                    (replay_canonical_eq_resolve_with_provenance
                                       strong_canon premise_steps
                                     handle Feedback.HOL_ERR _ =>
                                       let
                                         val fallback =
                                           canonical_eq_resolve ()
                                       in
                                         (fallback, UnavailableProvenance
                                           "eq_resolve used reconstruction without an exact equality-side occurrence")
                                       end)))))
                    in exact_result provenance theorem end)
           | "contra" => opaque ( canonical_handler "contra" replay_contra)
           | "false_intro" => opaque ( replay_false_intro prems)
           | "false_elim" => opaque ( replay_false_elim prems)
           | "true_elim" => replay_true_elim_result premise_steps
           | "true_intro" => opaque ( replay_true_intro prems)
           | "evaluate" =>
               conjunction_free_equality_result
                 "evaluation result contains an exact conjunction"
                 (replay_evaluate conclusion args)
           | "and_elim" =>
               (case premise_steps of
                  [premise_step] =>
                    let
                      val (theorem, provenance) =
                        replay_and_elim conclusion args premise_step
                    in exact_result provenance theorem end
                | _ => raise ERR "and_elim"
                    "expected exactly one CPC premise")
           | "instantiate" => opaque ( replay_instantiate args prems)
           | "not_implies_elim2" =>
               let
                 val theorem = replay_not_implies_elim2 prems
                 val provenance =
                   case premise_steps of
                     [premise] =>
                       (case step_provenance premise of
                          ApplicationProvenance
                            ("not", [ApplicationProvenance
                              (_, [_, consequent])]) =>
                            ApplicationProvenance ("not", [consequent])
                        | _ => UnavailableProvenance
                            ("not_implies_elim2 lacks exact implication syntax; " ^
                             "premise=" ^ provenance_shape
                               (step_provenance premise)))
                   | _ => UnavailableProvenance
                       "not_implies_elim2 has wrong premise count"
               in exact_result provenance theorem end
           | "not_implies_elim1" =>
               let
                 val theorem = replay_not_implies_elim1 prems
                 val provenance =
                   case premise_steps of
                     [premise] =>
                       (case step_provenance premise of
                          ApplicationProvenance
                            ("not", [ApplicationProvenance
                              (_, [antecedent, _])]) => antecedent
                        | _ => UnavailableProvenance
                            ("not_implies_elim1 lacks exact implication syntax; " ^
                             "premise=" ^ provenance_shape
                               (step_provenance premise)))
                   | _ => UnavailableProvenance
                       "not_implies_elim1 has wrong premise count"
                 val provenance =
                   case provenance of
                     UnavailableProvenance reason =>
                       conjunction_free_semantic_provenance reason
                         (Thm.concl theorem)
                   | exact => exact
               in exact_result provenance theorem end
           | "implies_elim" => opaque ( replay_implies_elim prems)
           | "factoring" =>
               let
                 fun pointer_unique [] = []
                   | pointer_unique (literal :: rest) = literal ::
                       pointer_unique (List.filter (fn other =>
                         not (Portable.pointer_eq (literal, other))) rest)
                 val direct = case premise_steps of
                     [premise] =>
                       (case #clause (#result premise) of
                          SOME clause =>
                            if List.exists boolSyntax.is_disj
                                (SmtClause.literals clause) then NONE
                            else SmtClause.align
                              (pointer_unique (SmtClause.literals clause))
                              clause
                        | NONE => NONE)
                   | _ => NONE
               in case direct of
                   SOME clause => clause_result
                     "factoring has explicit occurrences" clause
                 | NONE => opaque (replay_factoring prems)
               end
           | "reordering" =>
               let
                 val direct = case (premise_steps, located_args) of
                     ([premise], [target]) =>
                       (case (#clause (#result premise),
                              source_clause_literals target) of
                          (SOME clause, SOME literals) =>
                            SmtClause.align literals clause
                        | _ => NONE)
                   | _ => NONE
               in case direct of
                   SOME clause => clause_result
                     "reordering has explicit occurrences" clause
                 | NONE =>
                     let
                       val theorem = replay_reordering prems args
                         handle Feedback.HOL_ERR holerr =>
                           if SmtResource.is_resource_gate holerr then
                             raise Feedback.HOL_ERR holerr
                           else canonical_reordering ()
                     in case located_args of
                         [target] =>
                           if Term.aconv (Thm.concl theorem) (#term target) then
                             located_result
                               "checked reordering recorded target"
                               theorem target
                           else raw_unavailable_result
                             "reordering endpoint differs from recorded target"
                             theorem
                       | _ => raw_unavailable_result
                           "reordering lacks one recorded target" theorem end
               end
           | "exists_elim" => opaque ( replay_rare_rewrite "exists-elim" args)
           | "cnf" =>
               let val (theorem, literals) =
                 replay_cnf_with_literals (#name rule) args
               in clause_result "CPC CNF clause has explicit occurrences"
                 (SmtClause.from_literals literals theorem) end
           | "not_equiv_elim1" => opaque ( replay_not_equiv_elim "not_equiv_elim1" prems)
           | "not_equiv_elim2" => opaque ( replay_not_equiv_elim "not_equiv_elim2" prems)
           | "equiv_elim2" => opaque ( replay_equiv_elim2 conclusion prems)
           | "equiv_elim1" => opaque ( replay_equiv_elim1 conclusion prems)
           | "arith_rule" =>
               replay_arith_rule_result (#name rule) located_args
           | "arith_rel" =>
               let
                 val () = profile_event
                   (case conclusion of
                      SOME _ => "CPC(arith_rel:dispatch/declared)"
                    | NONE => "CPC(arith_rel:dispatch/omitted)")
               in opaque (replay_arith_rel prems args) end
           | "arith_abs_eq" => opaque ( replay_arith_abs_eq args)
           | "arith_abs_int_gt" => opaque ( replay_arith_abs_int_gt args)
           | "arrays_select_const" => opaque ( replay_arrays_select_const args)
           | "arrays_read_over_write" => opaque (
               replay_arrays_read_over_write (#name rule) prems conclusion args)
           | "ite_not_cond" => opaque ( replay_ite_not_cond args)
           | "ite_true_cond" => opaque ( replay_ite_true_cond args)
           | "ite_then_true" => opaque ( replay_ite_then_true args)
           | "ite_then_false" => opaque ( replay_ite_then_false args)
           | "ite_false_cond" => opaque ( replay_ite_false_cond args)
           | "ite_neg_branch" => opaque ( replay_ite_neg_branch args prems)
           | "trust" => opaque (replay_trust false state prems args)
           | "ite_eq" => opaque ( replay_ite_eq args)
           | "ite_elim1" => opaque ( replay_ite_elim1 prems)
           | "ite_elim2" => opaque ( replay_ite_elim2 prems)
           | "quant_unused_vars" => opaque ( replay_quant_unused_vars args)
           | "quant_rewrite" =>
               let
                 val theorem = replay_quant_rewrite (#name rule) args
               in
                 case located_args of
                   [located] => located_result
                     "quantifier rewrite exact argument" theorem located
                 | _ => unavailable_result
                     "quantifier rewrite lacks one exact equality argument"
                     theorem
               end
           | "alpha_equiv" => opaque ( replay_alpha_equiv args)
           | "process_scope" => opaque (
               replay_process_scope strong_canon args prems)
           | "not_and" => opaque ( replay_not_and prems)
           | "not_or_elim" => opaque ( replay_not_or_elim args prems)
           | "not_not_elim" =>
               let
                 val theorem = replay_not_not_elim prems
                 val provenance =
                   case premise_steps of
                     [premise] =>
                       (case step_provenance premise of
                          ApplicationProvenance
                            ("not", [ApplicationProvenance
                              ("not", [inner])]) => inner
                        | UnavailableProvenance reason =>
                            UnavailableProvenance
                              ("not_not_elim operand unavailable: " ^ reason)
                        | AmbiguousProvenance reason =>
                            AmbiguousProvenance
                              ("not_not_elim operand ambiguous: " ^ reason)
                        | _ => UnavailableProvenance
                            "not_not_elim premise lacks exact double-negation syntax")
                   | _ => UnavailableProvenance
                       "not_not_elim has wrong premise count"
               in exact_result provenance theorem end
           | "and_intro" =>
               let
                 val (theorem, provenance) =
                   replay_and_intro premise_steps
               in exact_result provenance theorem end
           | "skolemize" =>
               (case rule_preflight of
                  SOME result => result
                | NONE =>
                    skolemize_preflight conclusion located_args premise_steps)
           | "arith_mult_neg" => opaque ( replay_arith_mult_neg args)
           | "arith_mult_pos" => opaque ( replay_arith_mult_pos args)
           | "arith_mult_sign" => opaque ( replay_arith_mult_sign args)
           | "arith_trichotomy" => opaque ( replay_arith_trichotomy conclusion prems)
           | "arith_reduction" =>
               let
                 val (theorem, provenance) = replay_arith_reduction args
               in exact_result provenance theorem end
           | "arith_max_geq1" => opaque ( replay_arith_max_geq1 args)
           | "arith_min_lt2" => opaque ( replay_arith_min_lt2 args)
           | "int_tight_lb" => opaque ( replay_int_tight_lb prems)
           | "int_tight_ub" => opaque ( replay_int_tight_ub prems)
           | "modus_ponens" => opaque (
               (require_declared "modus_ponens" (replay_modus_ponens prems)
                 handle Feedback.HOL_ERR _ =>
                   require_declared "modus_ponens"
                    (replay_canonical_modus_ponens strong_canon prems)
                 handle Feedback.HOL_ERR _ =>
                   require_declared "modus_ponens"
                     (replay_arithmetic_modus_ponens prems)))
           | "arith_sum_ub" => opaque ( replay_arith_sum_ub prems)
           | "arith_mult_abs_comparison" => opaque (
               replay_arith_mult_abs_comparison prems conclusion)
           | "aci_norm" =>
               (case located_args of
                  [target] =>
                    let
                      val theorem = replay_aci_norm args
                      val (target_left, target_right) =
                        boolSyntax.dest_eq (#term target)
                      val theorem =
                        if Portable.pointer_eq
                             (boolSyntax.lhs (Thm.concl theorem),
                              target_left) then theorem
                        else Thm.TRANS (Thm.REFL target_left) theorem
                      val theorem =
                        if Portable.pointer_eq
                             (boolSyntax.rhs (Thm.concl theorem),
                              target_right) then theorem
                        else Thm.TRANS theorem (Thm.REFL target_right)
                      val dag_nodes = SmtResource.dag_nodes_up_to
                        (max_exact_provenance_dag_nodes + 1) (#term target)
                    in
                      if dag_nodes > max_exact_provenance_dag_nodes andalso
                         not (contains_binder_block_dag
                           (#provenance target)) then
                        raw_unavailable_result
                          "ACI provenance exceeds the replay tree budget"
                          theorem
                      else located_result "aci_norm result" theorem target
                    end
                | _ => unavailable_result
                    "aci_norm lacks one exact target occurrence"
                    (replay_aci_norm args))
           | "bv_xor_duplicate" => opaque ( replay_bv_xor_duplicate args)
           | "bv_not_idemp" => opaque ( replay_bv_not_idemp args)
           | "bv_shl_by_const_0" => opaque ( replay_bv_shl_by_const_0 args)
           | "bv_shl_by_const_2" => opaque ( replay_bv_shl_by_const_2 args)
           | "bv_lshr_by_const_0" => opaque ( replay_bv_lshr_by_const_0 args)
           | "bv_ashr_by_const_0" => opaque ( replay_bv_ashr_by_const_0 args)
           | "bv_poly_norm" =>
               let val theorem = replay_bv_poly_norm args in
                 case located_args of
                   [target] => located_result
                     "bv_poly_norm exact target" theorem target
                 | _ => opaque theorem
               end
           | "bv_poly_norm_eq" =>
               let val theorem = replay_bv_poly_norm_eq args in
                 case located_args of
                   [target] => located_result
                     "bv_poly_norm_eq exact target" theorem target
                 | _ => opaque theorem
               end
           | "seq_rewrite" => opaque (
               replay_seq_rewrite (#name rule) prems conclusion args)
           | "seq_rev_rev" => opaque ( replay_seq_rev_rev args)
           | "str_contains_refl" => opaque ( replay_str_contains_refl args)
           | "rare_inventory" => opaque (
               replay_rare_inventory state (#name rule) prems conclusion
                 located_args)
           | "str_substr_full_eq" => opaque ( replay_str_substr_full_eq args)
           | "seq_at_elim" => opaque ( replay_seq_at_elim conclusion args)
           | "sets" => opaque ( replay_sets state (#name rule) prems conclusion args)
           | "sets_ext" => opaque ( replay_sets_ext prems)
           | "sets_rewrite" => opaque (
               replay_sets state (#name rule) prems conclusion args)
           | "rewrite" =>
               let
                 val theorem = replay_rare_rewrite (#name rule) args
               in
                 if use_compact_provenance (Thm.concl theorem) then
                   let
                     val (_, provenance) =
                       replay_rare_rewrite_with_provenance
                         (#name rule) located_args
                   in exact_result provenance theorem end
                 else
                   raw_unavailable_result
                     "rewrite provenance exceeds the compact metadata budget"
                     theorem
               end
           | "datatype" => opaque ( replay_datatype args)
           | "dt_split" => opaque ( replay_dt_split args)
           | "datatype_eq" =>
               let
                 val theorem = replay_datatype_eq args
                 val provenance =
                   case located_args of
                     [located] => #provenance located
                   | _ => UnavailableProvenance
                       "datatype equality lacks its exact result argument"
               in exact_result provenance theorem end
           | "resolution" => SmtReplayObserve.run
               resolution_observation_inputs
               (fn (result : replay_result) => #thm result)
               occurrence_resolution_or_fallback
           | "bool" => opaque ( replay_bool prems conclusion)
           | "arith" => opaque ( replay_arith prems conclusion)
           | "string" => opaque (
               replay_string state (#name rule) prems conclusion args)
           | _ => unsupported_step step)) ()
           handle Conv.UNCHANGED =>
             raise ERR "replay_step"
               ("CPC step " ^ id ^ " (rule " ^ #name rule ^
                ") failed: proof-producing conversion reported unchanged")
                | Feedback.HOL_ERR holerr =>
             if SmtResource.is_resource_gate holerr then
               raise Feedback.HOL_ERR holerr
             else
               raise ERR "replay_step"
                 ("CPC step " ^ id ^ " (rule " ^ #name rule ^
                  ") failed: " ^ Feedback.message_of holerr))
          in (state, result) end
      val theorem = result_theorem result
      fun exact_cnf_or_neg_target target =
        case args of
          [disjunction, index_tm] =>
            let
              val (target_disjunction, target_negated) =
                boolSyntax.dest_disj target
              val target_selected = boolSyntax.dest_neg target_negated
              val index = Arbnum.toInt (numSyntax.dest_numeral
                (intSyntax.dest_injected index_tm))
              fun leaves term =
                case Lib.total boolSyntax.dest_disj term of
                  SOME (left, right) => leaves left @ leaves right
                | NONE => [term]
              val selected = List.nth (leaves disjunction, index)
            in
              Portable.pointer_eq (target_disjunction, disjunction) andalso
              Portable.pointer_eq (target_selected, selected)
            end
        | _ => false
      fun conclusion_matches target =
        (#name rule = "cnf_or_neg" andalso
         exact_cnf_or_neg_target target) orelse
        shared_aconv (Thm.concl theorem) target
      val _ = profile "CPC(check:step_conclusion)" (fn () =>
        case conclusion of
          NONE => ()
        | SOME target => if conclusion_matches target then () else
            raise ERR "replay_step" ("CPC rule " ^ #name rule ^
              " produced a conclusion different from its certificate")) ()
      val result = case located_conclusion of
          SOME located =>
            let
              val clause = case clause_from_located theorem located of
                  SOME exact => SOME exact
                | NONE => #clause result
              val located = case result_provenance result of
                  UnavailableProvenance _ => result_located result
                | _ => located
            in {thm = theorem, located = located, clause = clause} end
        | NONE => result
      val state = cache_step state id (#name rule) result
      val state =
        if Option.isSome cached orelse not (Option.isSome located_conclusion) then
          state
        else cache_thm state theorem
    in
      (state,
       theorem)
    end

  fun replay_commands initial commands =
    let
      fun profile_bound name =
        case OS.Process.getEnv name of
          NONE => NONE
        | SOME text =>
            (case Int.fromString text of
               SOME n => if n > 0 then SOME n else
                 raise ERR "replay_commands" (name ^ " must be positive")
             | NONE => raise ERR "replay_commands"
                 (name ^ " must be a positive step number"))
      val profile_from = profile_bound "HOL4_CPC_PROFILE_FROM"
      val profile_to = profile_bound "HOL4_CPC_PROFILE_TO"
      val profile_step_count = ref 0
      val _ = if Option.isSome profile_from then
        resolution_profile_counts := [] else ()
      val trace_setting = OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE"
      val trace_steps = trace_setting = SOME "1" orelse
        trace_setting = SOME "full"
      val traced_steps = ref 0
      val replay_cpu_timer = Timer.startCPUTimer ()
      fun trace_profile () =
        let
          val results = Profile.results ()
          fun report name =
            case List.find (fn (candidate, _) => candidate = name) results of
              NONE => name ^ "=0"
            | SOME (_, info) =>
                name ^ "=" ^ Int.toString (#n info) ^ "/" ^
                Time.toString (#usr info)
          val names =
            ["CPC(handler:ProofRule/chain_m_resolution)",
             "CPC(handler:ProofRule/reordering)",
             "CPC(handler:ProofRule/eq_resolve)",
             "CPC(handler:ProofRule/cnf_or_neg)",
             "CPC(chain:initial)",
             "CPC(chain:annotated)",
             "CPC(chain:dynamic)",
             "CPC(chain:schematic)",
             "CPC(chain:sat)",
             "CPC(chain:annotated_cleanup)",
             "CPC(chain:cleanup)",
             "CPC(chain:alignment)",
             "CPC(trans:shared/compare)",
             "CPC(trans:shared/nodewise)",
             "CPC(trans:shared/canonical_term)",
             "CPC(rung:trans/GRAPH_TAUT)_OK",
             "CPC(rung:trans/TAUT)_OK",
             "CPC(rung:trans/XOR_GRAPH)_OK",
             "CPC(rung:trans/XOR_TAUT)_OK",
             "CPC(xor_tautology:simp)_OK",
             "CPC(xor_tautology:taut)_OK",
             "CPC(xor_graph:simplify)_OK",
             "CPC(xor_graph:sat)_OK"]
          val ranked = Listsort.sort
            (fn ((_, left), (_, right)) =>
              Time.compare (#usr right, #usr left)) results
          val leaders = List.take (ranked, Int.min (5, List.length ranked))
          fun leader (name, info) =
            name ^ "=" ^ Time.toString (#usr info)
        in
          Feedback.HOL_MESG
            ("CPC replay profile: " ^
             String.concatWith " " (List.map report names));
          Feedback.HOL_MESG
            ("CPC replay leaders: " ^
             String.concatWith " " (List.map leader leaders));
          TextIO.flushOut TextIO.stdOut
        end
      fun trace_step (current : state) (step : CPC_Proof.step) =
        if trace_steps then
          let
            val count = !traced_steps + 1
            val _ = traced_steps := count
          in
            if count mod 25 = 0 orelse trace_setting = SOME "full" then
              let
                val {nongc, gc} = Timer.checkCPUTimes replay_cpu_timer
                val gc_time = Time.+ (#usr gc, #sys gc)
              in
                Feedback.HOL_MESG
                  ("CPC replay progress: step=" ^ #id step ^
                   " rule=" ^ #name (#rule step) ^
                   " count=" ^ Int.toString count ^
                   " live=" ^ Int.toString
                     (Redblackmap.numItems (#steps current)) ^
                   " cpu=" ^ Time.toString (#usr nongc) ^
                   " gc=" ^ Time.toString gc_time);
                TextIO.flushOut TextIO.stdOut
              end
            else ();
            if count mod 1000 = 0 then trace_profile () else ()
          end
        else ()
      val commands =
        case OS.Process.getEnv "HOL4_CPC_REPLAY_STEP" of
          NONE =>
            (case OS.Process.getEnv "HOL4_CPC_REPLAY_STOP" of
               NONE => commands
             | SOME wanted =>
                 let
                   fun through acc pending =
                     case pending of
                       [] => raise ERR "replay_commands"
                         ("diagnostic stop step not found: " ^ wanted)
                     | command :: rest =>
                         let val accumulated = command :: acc in
                           case command of
                             STEP step =>
                               if #id step = wanted then
                                 List.rev accumulated
                               else through accumulated rest
                           | _ => through accumulated rest
                         end
                 in through [] commands end)
        | SOME wanted =>
            (case List.find
                (fn STEP step => #id step = wanted | _ => false) commands of
               SOME command => [command]
             | NONE => raise ERR "replay_commands"
                 ("diagnostic step not found: " ^ wanted))
      val _ = if trace_steps then
        (Feedback.HOL_MESG
           ("CPC replay setup: commands=" ^
            Int.toString (List.length commands));
         TextIO.flushOut TextIO.stdOut)
        else ()
      (* The liveness pass touches every certificate edge before replay
         starts.  A functional map rebuilds a logarithmic search tree for
         every edge, which becomes the dominant cost on large CPC proofs.
         This proof-local mutable index records exactly the same use counts
         while making the prepass linear in the number of edges. *)
      val use_count_bucket_count = 65537
      val use_counts = Array.array
        (use_count_bucket_count, [] : (string * int ref) list)
      fun use_count_hash id =
        let
          fun loop index hash =
            if index = String.size id then hash
            else loop (index + 1)
              ((hash * 33 + Char.ord (String.sub (id, index))) mod
               use_count_bucket_count)
        in loop 0 5381 end
      fun use_count_ref id =
        let
          val bucket = use_count_hash id
          val entries = Array.sub (use_counts, bucket)
        in
          case List.find (fn (saved, _) => saved = id) entries of
            SOME (_, count) => count
          | NONE =>
              let val count = ref 0 in
                Array.update (use_counts, bucket, (id, count) :: entries);
                count
              end
        end
      fun add_use id =
        let val count = use_count_ref id in count := !count + 1 end
      val _ = List.app
        (fn command =>
          case command of
            STEP {premises, ...} => List.app add_use premises
          | _ => ()) commands
      val _ = if trace_steps then
        (Feedback.HOL_MESG "CPC replay setup: liveness complete";
         TextIO.flushOut TextIO.stdOut)
        else ()
      fun use_count id =
        case List.find (fn (saved, _) => saved = id)
          (Array.sub (use_counts, use_count_hash id)) of
          SOME (_, count) => !count
        | NONE => 0
      fun keep id = use_count id > 0
      fun discard_unreferenced state id =
        if keep id then state else remove_step state id
      fun consume state id =
        let
          val count = use_count_ref id
          val _ = !count > 0 orelse raise ERR "replay_commands"
            ("missing or exhausted premise-use count for step '" ^ id ^ "'")
          val remaining = !count - 1
          val _ = count := remaining
        in
          if remaining = 0 then remove_step state id else state
        end
      fun finish state id premises =
        discard_unreferenced
          (List.foldl
            (fn (premise, current) => consume current premise)
            state premises) id
      val strong_canon = strong_cpc_canon_conv
        (#translation_definitions initial)
      fun measured_step state step =
        case profile_from of
          NONE => replay_step strong_canon state step
        | SOME first =>
            let
              val _ = profile_step_count := !profile_step_count + 1
              val count = !profile_step_count
              val selected = count >= first andalso
                (case profile_to of NONE => true | SOME last => count <= last)
              fun work () = resolution_profile "step"
                (replay_step strong_canon state) step
            in
              if selected then
                Feedback.trace ("CPC_resolution_profile", 1)
                  (Feedback.trace ("HolSatLib_profile", 1) work) ()
              else replay_step strong_canon state step
            end
      val _ = if trace_steps then
        (Feedback.HOL_MESG "CPC replay setup: canonicalizer ready";
         TextIO.flushOut TextIO.stdOut)
        else ()
      fun loop state commands =
        case commands of
          [] => raise ERR "replay_commands" "empty CPC proof"
        | [ASSUME (id, {term, provenance})] =>
            let
              val thm = Thm.ASSUME term
              val state = cache_step (assert_hyp state term) id "assume"
                (exact_result provenance thm)
            in (cache_thm state thm, thm) end
        | ASSUME (id, {term, provenance}) :: rest =>
            let
              val thm = Thm.ASSUME term
              val state = cache_step (assert_hyp state term) id "assume"
                (exact_result provenance thm)
              val state = discard_unreferenced (cache_thm state thm) id
            in loop state rest end
        | [ASSUME_PUSH (id, {term, provenance})] =>
            let
              val thm = Thm.ASSUME term
              val state = cache_step (push_scope_hyp state term) id
                "assume-push" (exact_result provenance thm)
            in (cache_thm state thm, thm) end
        | ASSUME_PUSH (id, {term, provenance}) :: rest =>
            let
              val thm = Thm.ASSUME term
              val state = cache_step (push_scope_hyp state term) id
                "assume-push" (exact_result provenance thm)
              val state = discard_unreferenced (cache_thm state thm) id
            in loop state rest end
        | [STEP step] =>
            let
              val _ = trace_step state step
              val result = measured_step state step
              val _ = if trace_steps then
                (Feedback.HOL_MESG
                   ("CPC replay progress: completed=" ^ #id step);
                 trace_profile ();
                 TextIO.flushOut TextIO.stdOut)
              else ()
            in result end
        | STEP step :: rest =>
            let
              val _ = trace_step state step
              val (state, _) = measured_step state step
              val state = finish state (#id step) (#premises step)
            in loop state rest end
      fun report () =
        if not (Option.isSome profile_from) then ()
        else
          (Feedback.HOL_MESG ("CPC resolution counters: " ^
             String.concatWith " " (List.map
               (fn (name, count) => name ^ "=" ^ Int.toString count)
               (!resolution_profile_counts)));
           TextIO.flushOut TextIO.stdOut)
    in Portable.finally report (fn () => loop initial commands) () end

  (* cvc5's preprocessing can expose canonical arithmetic spellings, record
     and datatype eliminators, and FP bit representations in a proof
     assumption while the HOL goal retains its surface form.  Discharge only
     hypotheses that follow from the original replay context; this is a
     checked normalization bridge, never an assumption drop. *)
  fun remove_extra_hyps (asl, g, thm) =
    let
      val expected = HOLset.addList (Term.empty_tmset,
        boolSyntax.mk_neg g :: asl)
      val bad_hyps = HOLset.difference (Thm.hypset thm, expected)
      val context = boolSyntax.mk_neg g :: asl
      (* Match assumptions only after both sides pass through the same proved
         canonical conversion.  In particular, this absorbs cvc5's SMT-LIB
         ceiling-as-negated-floor spelling without a dedicated bridge rung. *)
      fun prove_canonical_hyp hyp =
        let
          val hyp_canon = SmtReplayCanon.cpc_canon_conv hyp
          val normalized_hyp = boolSyntax.rhs (Thm.concl hyp_canon)
          fun match assumption =
            let
              val normalized_assumption =
                SmtReplayCanon.cpc_canon_rule (Thm.ASSUME assumption)
              val _ = Term.aconv (Thm.concl normalized_assumption)
                normalized_hyp orelse
                raise ERR "remove_extra_hyps"
                  "canonical assumption did not match extra hypothesis"
              val theorem = Thm.EQ_MP (Thm.SYM hyp_canon)
                normalized_assumption
              val () = profile_event "CPC(canon:assumption-interface)"
            in theorem end
        in
          Lib.tryfind match context
        end
      fun prove_from_context hyp =
        Tactical.TAC_PROOF ((context, hyp),
          Tactical.THEN
            (Tactical.REPEAT Tactic.COND_CASES_TAC,
             Tactical.THEN
               (bossLib.FULL_SIMP_TAC (bossLib.srw_ss()) [],
                intLib.ARITH_TAC)))
      fun prove_hyp hyp =
        profile "CPC(remove_extra_hyps:canonical_assumption)"
          prove_canonical_hyp hyp
        handle Feedback.HOL_ERR _ =>
          profile "CPC(remove_extra_hyps:fp_special_values)"
            Tactical.TAC_PROOF
            ((boolSyntax.mk_neg g :: asl, hyp),
             bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
               [(* cvc5 expands canonical NaN to an FP bit triple. *)
                smtfloatTheory.smtfp_nan_bits,
                (* cvc5 expands positive zero to the all-zero bit triple. *)
                smtfloatTheory.smtfp_pzero_bits,
                (* cvc5 expands negative zero to sign-one, zero payload. *)
                smtfloatTheory.smtfp_nzero_bits,
                (* cvc5 expands positive infinity to its FP bit triple. *)
                smtfloatTheory.smtfp_pinf_bits,
                (* cvc5 expands negative infinity to its FP bit triple. *)
                smtfloatTheory.smtfp_ninf_bits])
        handle Feedback.HOL_ERR _ =>
          profile "CPC(remove_extra_hyps:floor_ceiling_neg)"
            Tactical.TAC_PROOF
            ((boolSyntax.mk_neg g :: asl, hyp),
             bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
               [(* cvc5 pushes real negation through to_int floor and
                   exposes the equivalent negated ceiling. *)
                intrealTheory.INT_FLOOR_NEG,
                (* cvc5 pushes real negation through encoded ceiling and
                   exposes the equivalent negated floor. *)
                intrealTheory.INT_CEILING_NEG])
        handle Feedback.HOL_ERR _ =>
          profile "CPC(remove_extra_hyps:datatype)"
            SmtDatatypeProve.datatype_consequence_prove
            (boolSyntax.mk_neg g :: asl, hyp)
        handle Feedback.HOL_ERR _ =>
          if Library.contains_conditional hyp then
            profile "CPC(remove_extra_hyps:conditional_arith)"
              prove_from_context hyp
          else raise ERR "remove_extra_hyps"
            "extra hypothesis is not a conditional arithmetic consequence"
      fun remove_hyp (hyp, result) =
        Drule.PROVE_HYP (prove_hyp hyp) result
        handle Feedback.HOL_ERR holerr =>
          raise ERR "remove_extra_hyps"
            ("extra hypothesis is not one of the enumerated cvc5 semantic " ^
             "bridges; hypothesis=" ^ Library.term_to_string hyp ^
             "; attempted=[canonical assumption, FP special values, " ^
             "floor/ceiling negation, datatype normalization, conditional " ^
             "arithmetic]; " ^
             "underlying=" ^ Feedback.message_of holerr)
    in
      HOLset.foldl remove_hyp thm bad_hyps
    end

in

  val prove_boolean_circuit =
    prove_boolean_circuit_tautology
  val sharing_aware_aconv = shared_aconv
  val replay_bv_poly_norm_for_test = replay_bv_poly_norm
  val replay_rare_rewrite_for_test = replay_rare_rewrite
  val replay_factoring_for_test = replay_factoring
  val disjunction_alignment_plan_for_test = disjunction_alignment_plan
  val boolean_dag_using_for_test =
    prove_boolean_dag_tautology_with_leaf_conversion_using

  val theorem_cache_enabled_for_test = theorem_cache_enabled

  val eq_resolve_preflight_with_worker_for_test =
    enabled_eq_resolve_preflight_route_with_worker

  fun cache_refusal_accounting_for_test theorem =
    let
      fun refuse _ _ _ =
        Library.fastpath_refusal "CPC theorem cache test"
          "injected refusal"
      val initial = initial_state [] []
      val before_stats = cache_stats initial
      val after_insert_state =
        cache_thm_with_fastpath refuse initial theorem
      val after_insert = cache_stats after_insert_state
      val () =
        (ignore (cached_thm_with_fastpath refuse after_insert_state
           (Thm.concl theorem));
         raise ERR "cache_refusal_accounting_for_test"
           "injected probe refusal was admitted")
        handle Feedback.HOL_ERR holerr =>
          if Feedback.top_structure_of holerr = "CPC_ProofReplay" andalso
             Feedback.top_function_of holerr = "cached_thm" andalso
             Feedback.message_of holerr =
               "CPC theorem cache budget refused" then ()
          else raise Feedback.HOL_ERR holerr
      val after_probe = cache_stats after_insert_state
    in
      {before_stats = before_stats,
       after_insert = after_insert,
       after_probe = after_probe}
    end

  val strong_cpc_canon_conv_for_test = strong_cpc_canon_conv
  val canonical_term_conv_for_test = canonical_term_conv

  fun replay_process_scope_for_test args prems =
    replay_process_scope (strong_cpc_canon_conv []) args prems

  fun replay_eq_resolve_routes_for_test prems =
    let
      val route = Option.map eq_resolve_preflight_name
        (enabled_eq_resolve_preflight_route prems)
    in
      {route = route,
       arithmetic = replay_arithmetic_eq_resolve prems,
       canonical = replay_canonical_eq_resolve
         (strong_cpc_canon_conv []) prems}
    end

  fun replay_rare_rewrite_for_test name args =
    replay_rare_rewrite name args

  fun replay_rare_inventory_string_for_test name args =
    let
      fun prove proposition =
        Drule.EQT_ELIM (bossLib.EVAL proposition)
      val premises = List.map prove
        (rare_string_expected_premises name args)
      val target = rare_string_expected_target name args
    in
      replay_inventory_string_rule name premises (SOME target) args
    end

  (* Build a complete public CPC step from the declarative source recipe.
     Unlike the direct theorem helper below, this returns cvc5 syntax: every
     :list argument is a bare identity or a native variadic aggregate.  Tests
     feed the result back through CPC_ProofParser before replay. *)
  fun rare_source_native_cpc_for_test use_seq list_width name =
    case rare_inventory_lookup name of
      SOME {replay_kind = RareSourceRecipe recipe, ...} =>
        let
          val formals = #formals recipe
          fun safe formal suffix = "task24_" ^ formal ^ suffix
          fun source_sort source =
            case source of
              RareSourceSeq => if use_seq then "(Seq Int)" else "String"
            | RareSourceString => "String"
            | RareSourceRegex => "RegLan"
            | RareSourceInt => "Int"
            | RareSourceElement => "Int"
          fun atom_for source symbol =
            case source of
              RareSourceRegex => RareList
                [RareAtom "str.to_re", RareAtom ("\"" ^ symbol ^ "\"")]
            | _ => RareAtom symbol
          fun declaration source symbol =
            case source of
              RareSourceRegex => []
            | _ => ["(declare-const " ^ symbol ^ " " ^
                source_sort source ^ ")"]
          fun aggregate_name aggregate source =
            case aggregate of
              RareSourceSeqConcat =>
                if use_seq andalso source = RareSourceSeq then "seq.++"
                else "str.++"
            | RareSourceRegexConcat => "re.++"
            | RareSourceRegexUnion => "re.union"
            | RareSourceRegexInter => "re.inter"
          fun identity aggregate source =
            case aggregate of
              RareSourceSeqConcat =>
                if use_seq andalso source = RareSourceSeq then
                  RareList [RareAtom "as", RareAtom "seq.empty",
                    RareList [RareAtom "Seq", RareAtom "Int"]]
                else RareAtom "\"\""
            | RareSourceRegexConcat => RareList
                [RareAtom "str.to_re", RareAtom "\"\""]
            | RareSourceRegexUnion => RareAtom "re.none"
            | RareSourceRegexInter => RareAtom "re.all"
          fun make_binding (formal, kind, source) =
            case kind of
              RareSourceIndex =>
                (formal, kind, source, RareAtom "1", [], [])
            | RareSourceTerm =>
                let val symbol = safe formal ""
                in
                  (formal, kind, source, atom_for source symbol, [],
                   declaration source symbol)
                end
            | RareSourceList aggregate =>
                let
                  fun part index =
                    let val symbol = safe formal
                      ("_part" ^ Int.toString index)
                    in
                      (atom_for source symbol, declaration source symbol)
                    end
                  val made = List.tabulate (list_width, part)
                  val parts = List.map #1 made
                  val declarations = List.concat (List.map #2 made)
                  val argument =
                    case parts of
                      [] => identity aggregate source
                    | _ => RareList
                        (RareAtom (aggregate_name aggregate source) :: parts)
                in
                  (formal, kind, source, argument, parts, declarations)
                end
          val environment = List.map make_binding formals
          fun lookup formal =
            case List.find (fn (candidate, _, _, _, _, _) =>
                candidate = formal) environment of
              SOME binding => binding
            | NONE => raise ERR "rare_source_native_cpc_for_test"
                (name ^ " has an unknown declarative formal " ^ formal)
          fun sequence_expression expression =
            case expression of
              RareAtom formal =>
                (case List.find (fn (candidate, _, source, _, _, _) =>
                    candidate = formal andalso source = RareSourceSeq)
                    environment of
                   SOME _ => use_seq
                 | NONE => false)
            | RareList expressions => List.exists sequence_expression
                expressions
          fun mapped_operator operator expression =
            if not (sequence_expression expression) then operator
            else case operator of
              "str.++" => "seq.++"
            | "str.len" => "seq.len"
            | "str.contains" => "seq.contains"
            | "str.substr" => "seq.extract"
            | "str.at" => "seq.at"
            | "str.indexof" => "seq.indexof"
            | "str.replace" => "seq.replace"
            | "str.replace_all" => "seq.replace_all"
            | "str.update" => "seq.update"
            | "str.prefixof" => "seq.prefixof"
            | "str.suffixof" => "seq.suffixof"
            | "str.rev" => "seq.rev"
            | other => other
          fun application operator source_expression operands =
            case (operator, operands) of
              ("str.++", []) =>
                if sequence_expression source_expression andalso use_seq then
                  RareList [RareAtom "as", RareAtom "seq.empty",
                    RareList [RareAtom "Seq", RareAtom "Int"]]
                else RareAtom "\"\""
            | ("seq.++", []) => RareList
                [RareAtom "as", RareAtom "seq.empty",
                 RareList [RareAtom "Seq", RareAtom "Int"]]
            | ("re.++", []) => RareList
                [RareAtom "str.to_re", RareAtom "\"\""]
            | ("re.union", []) => RareAtom "re.none"
            | ("re.inter", []) => RareAtom "re.all"
            | ("and", []) => RareAtom "true"
            | ("or", []) => RareAtom "false"
            | ("str.++", [operand]) => operand
            | ("seq.++", [operand]) => operand
            | ("re.++", [operand]) => operand
            | ("re.union", [operand]) => operand
            | ("re.inter", [operand]) => operand
            | ("and", [operand]) => operand
            | ("or", [operand]) => operand
            | _ => RareList (RareAtom operator :: operands)
          fun instantiate expression =
            case expression of
              RareAtom formal =>
                (case List.find (fn (candidate, _, _, _, _, _) =>
                    candidate = formal) environment of
                   SOME (_, RareSourceList _, _, _, _, _) =>
                     raise ERR "rare_source_native_cpc_for_test"
                       (name ^ " uses list formal " ^ formal ^
                        " outside its aggregate")
                 | SOME (_, _, _, argument, _, _) => argument
                 | NONE => RareAtom formal)
            | RareList
                [RareAtom "@seq.empty_of_type",
                 RareList [RareAtom "@type_of", RareAtom formal]] =>
                let val (_, _, source, _, _, _) = lookup formal
                in identity RareSourceSeqConcat source end
            | RareList (RareAtom operator :: expressions) =>
                let
                  fun operands [] = []
                    | operands (RareAtom formal :: rest) =
                        (case List.find (fn (candidate, _, _, _, _, _) =>
                            candidate = formal) environment of
                           SOME (_, RareSourceList _, _, _, parts, _) =>
                             parts @ operands rest
                         | _ => instantiate (RareAtom formal) ::
                             operands rest)
                    | operands (expression :: rest) =
                        instantiate expression :: operands rest
                  val operator = mapped_operator operator expression
                in
                  application operator expression (operands expressions)
                end
            | RareList [] => raise ERR "rare_source_native_cpc_for_test"
                (name ^ " has an empty declarative application")
            | RareList _ => raise ERR "rare_source_native_cpc_for_test"
                (name ^ " has a non-atomic declarative application head")
          fun render expression =
            case expression of
              RareAtom atom => atom
            | RareList expressions =>
                "(" ^ String.concatWith " " (List.map render expressions) ^
                ")"
          val premises = List.map
            (instantiate o parse_rare_source_sexp) (#premises recipe)
          val target = instantiate (parse_rare_source_sexp (#target recipe))
          val premise_ids = List.tabulate (List.length premises,
            fn index => "@task24_a" ^ Int.toString index)
          val assumptions = ListPair.map
            (fn (premise_id, premise) =>
              "(assume " ^ premise_id ^ " " ^ render premise ^ ")")
            (premise_ids, premises)
          val args = List.map
            (fn (_, _, _, argument, _, _) => render argument) environment
          val declarations = List.concat (List.map
            (fn (_, _, _, _, _, commands) => commands) environment)
          val premise_attribute =
            if List.null premise_ids then ""
            else " :premises (" ^ String.concatWith " " premise_ids ^ ")"
          val step = "(step @task24_result " ^ render target ^ " :rule " ^
            name ^ premise_attribute ^ " :args (" ^
            String.concatWith " " args ^ "))"
        in
          {proof = "(" ^ String.concatWith " "
             (declarations @ assumptions @ [step]) ^ ")",
           premise_count = List.length premises}
        end
    | SOME _ => raise ERR "rare_source_native_cpc_for_test"
        (name ^ " is not a proved declarative TASK24 recipe")
    | NONE => raise ERR "rare_source_native_cpc_for_test"
        (name ^ " is absent from the cvc5-1.3.4 RARE inventory")

  fun replay_rare_source_for_test_with_seq_type_and_list_width
      seq_type list_width name =
    case rare_inventory_lookup name of
      SOME {family, replay_kind = RareSourceRecipe recipe, ...} =>
        let
          fun source_type RareSourceSeq = seq_type
            | source_type RareSourceString =
                Type.mk_thy_type
                  {Thy = "smtstring", Tyop = "smtstr", Args = []}
            | source_type RareSourceRegex = reglan_ty
            | source_type RareSourceInt = intSyntax.int_ty
            | source_type RareSourceElement = intSyntax.int_ty
          fun argument (_, RareSourceIndex, _) =
                intSyntax.mk_injected (numSyntax.mk_numeral Arbnum.one)
            | argument (formal, RareSourceList _, source) =
                let
                  val ty = source_type source
                  val elements = List.tabulate (list_width, fn index =>
                    Term.mk_var
                      ("rare_" ^ formal ^ "_part" ^ Int.toString index, ty))
                in
                  listSyntax.mk_list (elements, ty)
                end
            | argument (formal, _, source) =
                Term.mk_var ("rare_" ^ formal, source_type source)
          val args = List.map argument (#formals recipe)
          val premises = List.map
            (eval_rare_source_recipe name (#formals recipe) args)
            (#premises recipe)
          val target = eval_rare_source_recipe name
            (#formals recipe) args (#target recipe)
          val theorem = replay_rare_source_recipe family name recipe
            (List.map Thm.ASSUME premises) (SOME target) args
          val closed = List.foldl
            (fn (premise, theorem) => Thm.DISCH premise theorem)
            theorem premises
        in
          {args = args, premises = premises, target = target,
           theorem = theorem, closed = closed}
        end
    | SOME _ => raise ERR "replay_rare_source_for_test"
        (name ^ " is not a declarative TASK24 recipe")
    | NONE => raise ERR "replay_rare_source_for_test"
        (name ^ " is absent from the cvc5-1.3.4 RARE inventory")

  fun replay_rare_source_for_test_with_seq_type seq_type name =
    replay_rare_source_for_test_with_seq_type_and_list_width seq_type 2 name

  fun replay_rare_source_for_test name =
    replay_rare_source_for_test_with_seq_type
      (Type.mk_thy_type
        {Thy = "smtstring", Tyop = "smtstr", Args = []}) name

  fun replay_rare_source_seq_for_test name =
    replay_rare_source_for_test_with_seq_type
      (listSyntax.mk_list_type intSyntax.int_ty) name

  fun replay_rare_source_empty_lists_for_test name =
    replay_rare_source_for_test_with_seq_type_and_list_width
      (Type.mk_thy_type
        {Thy = "smtstring", Tyop = "smtstr", Args = []}) 0 name

  fun replay_rare_source_seq_empty_lists_for_test name =
    replay_rare_source_for_test_with_seq_type_and_list_width
      (listSyntax.mk_list_type intSyntax.int_ty) 0 name

  fun replay_rare_source_unsupported_for_test name =
    case rare_inventory_lookup name of
      SOME {replay_kind = RareSourceUnsupported (_, reason), ...} =>
        raise ERR name
          ("unsupported cvc5-1.3.4 RARE rule " ^ name ^ ": " ^ reason)
    | SOME _ => raise ERR "replay_rare_source_unsupported_for_test"
        (name ^ " is not an unsupported TASK24 source recipe")
    | NONE => raise ERR "replay_rare_source_unsupported_for_test"
        (name ^ " is absent from the cvc5-1.3.4 RARE inventory")

  fun replay_arith_reduction_for_test args =
    #1 (replay_arith_reduction args)

  fun replay_and_elim_provenance_for_test premise provenance index
      conclusion =
    let
      val index_term = intSyntax.mk_injected
        (numSyntax.mk_numeral (Arbnum.fromInt index))
      val step : replayed_step =
        {rule_name = "test", result = exact_result provenance premise}
    in
      #1 (replay_and_elim conclusion [index_term] step)
    end

  fun replay_result_alignment_for_test theorem located =
    ignore (located_result "test result alignment" theorem located)

  fun replay_cnf_for_test name args =
    replay_cnf name args

  fun replay_arith_abs_eq_for_test args =
    replay_arith_abs_eq args

  fun replay_arith_abs_int_gt_for_test args =
    replay_arith_abs_int_gt args

  fun replay_arith_mult_abs_comparison_for_test prems conclusion =
    replay_arith_mult_abs_comparison prems (SOME conclusion)

  fun replay_arith_mult_neg_for_test args =
    replay_arith_mult_neg args

  fun replay_arith_mult_pos_for_test args =
    replay_arith_mult_pos args

  fun instantiate_cpc_fp_private_markers theorem =
    let
      fun marker_info variable =
        let
          val (name, _) = Term.dest_var variable
          val fields = String.tokens (fn character => character = #"#") name
        in
          case fields of
            [kind, serial] =>
              if String.isPrefix "@fp." kind then
                SOME (kind, valOf (Int.fromString serial))
              else NONE
          | _ => NONE
        end
        handle Feedback.HOL_ERR _ => NONE
             | Option => NONE
      val hypotheses = HOLset.listItems (Thm.hypset theorem)
      val variables = HOLset.listItems
        (HOLset.addList (Term.empty_tmset,
          List.concat (List.map Term.free_vars hypotheses)))
      val markers = List.mapPartial
        (fn variable => Option.map
          (fn (kind, serial) => (kind, serial, variable))
          (marker_info variable)) variables
      fun markers_of kind =
        Listsort.sort
          (fn ((_, first, _), (_, second, _)) => Int.compare (first, second))
          (List.filter (fn (saved, _, _) => saved = kind) markers)
      fun head_named theory name term =
        let
          val (head, _) = boolSyntax.strip_comb term
          val {Thy, Name, ...} = Term.dest_thy_const head
        in Thy = theory andalso Name = name end
        handle Feedback.HOL_ERR _ => false
      fun source_for marker =
        let
          fun contains hypothesis =
            List.exists (fn variable => Term.aconv variable marker)
              (Term.free_vars hypothesis)
          val hypothesis = Lib.tryfind
            (fn candidate =>
              if contains candidate then candidate
              else raise ERR "instantiate_cpc_fp_private_markers"
                "marker absent") hypotheses
        in
          case #2 (boolSyntax.strip_comb
              (HolKernel.find_term
                (head_named "smtfloat" "smtfp_is_infinite") hypothesis)) of
            [source] => source
          | _ => raise ERR "instantiate_cpc_fp_private_markers"
              "malformed infinite predicate"
        end
      val sources = List.map (source_for o #3) (markers_of "@fp.INF")
      fun unary theory name argument =
        let
          val constant = Term.prim_mk_const {Thy = theory, Name = name}
          val (domain, _) = Type.dom_rng (Term.type_of constant)
          val instantiation = Type.match_type domain (Term.type_of argument)
        in Term.mk_comb (Term.inst instantiation constant, argument) end
      fun application theory name arguments =
        let
          fun apply (argument, function) =
            let
              val (domain, _) = Type.dom_rng (Term.type_of function)
              val instantiation =
                Type.match_type domain (Term.type_of argument)
            in Term.mk_comb (Term.inst instantiation function, argument) end
        in
          List.foldl apply
            (Term.prim_mk_const {Thy = theory, Name = name}) arguments
        end
      fun representation source = unary "smtfloat" "smtfp_rep" source
      fun selector name source =
        unary "binary_ieee" ("recordtype.float.seldef." ^ name)
          (representation source)
      fun exact_predicate name source =
        let
          fun matching term =
            head_named "smtfloat" name term andalso
            case #2 (boolSyntax.strip_comb term) of
              [argument] => Term.aconv argument source
            | _ => false
          fun search hypothesis = HolKernel.find_term matching hypothesis
        in Lib.tryfind search hypotheses end
      fun classification name source =
        SmtLib_Theories.mk_bbterm
          [exact_predicate name source
           handle Feedback.HOL_ERR _ => unary "smtfloat" name source]
      fun unpacked (source, (_, _, significand_marker)) =
        let
          val zero = exact_predicate "smtfp_is_zero" source
            handle Feedback.HOL_ERR _ =>
              unary "smtfloat" "smtfp_is_zero" source
          val nan = exact_predicate "smtfp_is_nan" source
          val inf = exact_predicate "smtfp_is_infinite" source
          val special = boolSyntax.mk_disj
            (zero, boolSyntax.mk_disj (nan, inf))
          val exponent = selector "Exponent" source
          val fraction = selector "Significand" source
        in
          {sign = selector "Sign" source,
           exponent = application "smtfloatReplayWord"
             "smtfp_cvc_unpacked_exponent"
             [special, exponent, fraction],
           significand = application "smtfloatReplayWord"
             "smtfp_cvc_unpacked_significand"
             [special, exponent, fraction,
              wordsSyntax.mk_word_L
                (wordsSyntax.dim_of significand_marker)],
           zero = SmtLib_Theories.mk_bbterm [zero],
           nan = SmtLib_Theories.mk_bbterm [nan],
           inf = SmtLib_Theories.mk_bbterm [inf]}
        end
      val unpacked_sources = ListPair.map unpacked
        (sources, markers_of "@fp.SIGNIFICAND")
      fun witnesses kind =
        if kind = "@fp.SIGN" then List.map #sign unpacked_sources
        else if kind = "@fp.EXPONENT" then List.map #exponent unpacked_sources
        else if kind = "@fp.SIGNIFICAND" then
          List.map #significand unpacked_sources
        else if kind = "@fp.ZERO" then List.map #zero unpacked_sources
        else if kind = "@fp.NAN" then List.map #nan unpacked_sources
        else if kind = "@fp.INF" then List.map #inf unpacked_sources
        else []
      (* Put compact flag witnesses first. *)
      val kinds = ["@fp.ZERO", "@fp.NAN", "@fp.INF", "@fp.SIGN",
        "@fp.EXPONENT", "@fp.SIGNIFICAND"]
      fun substitutions kind =
        let
          val kind_markers = markers_of kind
          val kind_witnesses = witnesses kind
          val _ = List.length kind_markers = List.length kind_witnesses orelse
            raise ERR "instantiate_cpc_fp_private_markers"
              ("incomplete private-marker group for " ^ kind)
        in
          ListPair.map
            (fn ((_, _, marker), witness) =>
              {redex = marker, residue = witness})
            (kind_markers, kind_witnesses)
        end
      val substitution = List.concat (List.map substitutions kinds)
    in
      if List.null substitution then theorem else Thm.INST substitution theorem
    end

  (* The repaired CPC producer supplies the FP operand at every
     private-component occurrence.  Parsing keeps a small variable as an
     internal abbreviation so ordinary CPC congruence and transitivity do
     not repeatedly traverse a large Skolem term.  Eliminate all such
     abbreviations in one checked kernel instantiation before any deferred
     FP premise is discharged. *)
  fun cpc_fp_private_substitutions bindings =
    let
      fun unary theory name argument =
        let
          val constant = Term.prim_mk_const {Thy = theory, Name = name}
          val (domain, _) = Type.dom_rng (Term.type_of constant)
          val instantiation = Type.match_type domain (Term.type_of argument)
        in Term.mk_comb (Term.inst instantiation constant, argument) end
      fun application theory name arguments =
        let
          fun apply (argument, function) =
            let
              val (domain, _) = Type.dom_rng (Term.type_of function)
              val instantiation =
                Type.match_type domain (Term.type_of argument)
            in Term.mk_comb (Term.inst instantiation function, argument) end
        in
          List.foldl apply
            (Term.prim_mk_const {Thy = theory, Name = name}) arguments
        end
      fun selector name source =
        unary "binary_ieee" ("recordtype.float.seldef." ^ name)
          (unary "smtfloat" "smtfp_rep" source)
      fun predicate name source = unary "smtfloat" name source
      fun witness ({marker, kind, source} :
          CPC_ProofParser.cpc_fp_private_binding) =
        let
          val zero = predicate "smtfp_is_zero" source
          val nan = predicate "smtfp_is_nan" source
          val inf = predicate "smtfp_is_infinite" source
          val special = boolSyntax.mk_disj
            (zero, boolSyntax.mk_disj (nan, inf))
          val exponent = selector "Exponent" source
          val fraction = selector "Significand" source
          val shape = wordsSyntax.mk_word_L (wordsSyntax.dim_of marker)
          val replacement =
            if kind = "@fp.SIGN" then selector "Sign" source
            else if kind = "@fp.EXPONENT" then
              application "smtfloatReplayWord"
                "smtfp_cvc_unpacked_exponent"
                [special, exponent, fraction, shape]
            else if kind = "@fp.SIGNIFICAND" then
              application "smtfloatReplayWord"
                "smtfp_cvc_unpacked_significand"
                [special, exponent, fraction, shape]
            else if kind = "@fp.ZERO" then
              SmtLib_Theories.mk_bbterm [zero]
            else if kind = "@fp.NAN" then
              SmtLib_Theories.mk_bbterm [nan]
            else if kind = "@fp.INF" then
              SmtLib_Theories.mk_bbterm [inf]
            else raise ERR "instantiate_cpc_fp_private_markers"
              ("unknown explicit private FP component " ^ kind)
          val _ = Type.compare
            (Term.type_of marker, Term.type_of replacement) = EQUAL orelse
            raise ERR "instantiate_cpc_fp_private_markers"
              (kind ^ " witness has the wrong type")
        in {redex = marker, residue = replacement} end
    in List.map witness bindings end

  fun instantiate_cpc_fp_private_bindings bindings theorem =
    let val substitutions = cpc_fp_private_substitutions bindings in
      if List.null substitutions then theorem
      else Thm.INST substitutions theorem
    end

  fun instantiate_cpc_fp_private_markers theorem =
    instantiate_cpc_fp_private_bindings
      (CPC_ProofParser.cpc_fp_private_bindings ()) theorem

  (* Older CPC producers omit the operand on private FP components.  Each
     occurrence is a fresh internal bitvector, not the same nullary HOL
     constant as another occurrence with the same printed spelling.  The
     checked classification bridges identify the FP operands; search the
     finite one-to-one assignments of the remaining components to those
     operands, accepting only an assignment for which every deferred bridge
     has an independent kernel proof.  No TRUST proposition is assumed. *)
  fun instantiate_cpc_fp_unbound_markers state allowed theorem =
    let
      val kinds =
        ["@fp.SIGN", "@fp.EXPONENT", "@fp.SIGNIFICAND",
         "@fp.ZERO", "@fp.NAN", "@fp.INF"]
      fun marker_kind term =
        let val (name, _) = Term.dest_var term in
          List.find (fn kind =>
            String.isPrefix (kind ^ "#unbound") name) kinds
        end handle Feedback.HOL_ERR _ => NONE
      fun unique terms = List.rev (List.foldl
        (fn (term, kept) =>
          if List.exists (Term.aconv term) kept then kept
          else term :: kept) [] terms)
      fun markers term =
        let
          val found = ref ([] : (Term.term * string) list)
          val graph = SmtResource.bounded_structure_with_inspector
            (fn node =>
              case marker_kind node of
                SOME kind => found := (node, kind) :: !found
              | NONE => ())
            SmtResource.max_bitblast_term_nodes term
          val _ = #complete graph orelse
            raise ERR "instantiate_cpc_fp_unbound_markers"
              "private FP marker scan exceeded the DAG resource limit"
        in !found end
      val extra = HOLset.listItems
        (HOLset.difference (Thm.hypset theorem, allowed))
      val _ = List.all (List.null o markers)
          (HOLset.listItems allowed) orelse
        raise ERR "instantiate_cpc_fp_unbound_markers"
          "private FP component occurs in the original proof context"
      val all_markers = unique
        (List.map #1 (List.concat (List.map markers extra)))
      fun classified_source term =
        let
          val (head, arguments) = boolSyntax.strip_comb term
          val {Thy, Name, ...} = Term.dest_thy_const head
        in
          case (Thy, Name, arguments) of
            ("smtfloat", "smtfp_is_zero", [source]) =>
              SOME ("@fp.ZERO", source)
          | ("smtfloat", "smtfp_is_nan", [source]) =>
              SOME ("@fp.NAN", source)
          | ("smtfloat", "smtfp_is_infinite", [source]) =>
              SOME ("@fp.INF", source)
          | _ => NONE
        end handle Feedback.HOL_ERR _ => NONE
      fun anchor atom encoding =
        case classified_source atom of
          NONE => NONE
        | SOME (kind, source) =>
            (case List.filter (fn (_, found_kind) =>
                found_kind = kind) (markers encoding) of
               [(marker, _)] => SOME
                 ({marker = marker, kind = kind, source = source} :
                   CPC_ProofParser.cpc_fp_private_binding)
             | _ => NONE)
      fun anchors hypothesis =
        case Lib.total boolSyntax.dest_eq hypothesis of
          SOME (left, right) =>
            List.mapPartial Lib.I
              [anchor left right, anchor right left]
        | NONE => []
      val fixed = List.concat (List.map anchors extra)
      val sources = unique (List.map #source fixed)
      fun fixed_source marker =
        case List.filter (fn binding =>
            Term.aconv (#marker binding) marker) fixed of
          [] => NONE
        | first :: rest =>
            if List.all (fn binding =>
                Term.aconv (#source binding) (#source first)) rest then
              SOME (#source first)
            else raise ERR "instantiate_cpc_fp_unbound_markers"
              "inconsistent private FP classification anchors"
      fun assignments kind group =
        let
          fun choose [] _ chosen = [List.rev chosen]
            | choose (marker :: remaining) used chosen =
                let
                  val available =
                    case fixed_source marker of
                      SOME source => [source]
                    | NONE => sources
                in
                  List.concat (List.map (fn source =>
                    if List.exists (Term.aconv source) used then []
                    else choose remaining (source :: used)
                      ({marker = marker, kind = kind,
                        source = source} :: chosen)) available)
                end
        in choose group [] [] end
      val groups = List.map (fn kind =>
        (kind, List.filter (fn marker =>
          marker_kind marker = SOME kind) all_markers)) kinds
      fun combine [] = [[]]
        | combine ((kind, group) :: remaining) =
            let val tails = combine remaining in
              List.concat (List.map (fn bindings =>
                List.map (fn tail => bindings @ tail) tails)
                (assignments kind group))
            end
      val candidates = combine groups
      val _ = List.length candidates <= 4096 orelse
        raise ERR "instantiate_cpc_fp_unbound_markers"
          "private FP witness search exceeds fixed assignment budget"
      fun fp_bridge hypothesis =
        case Lib.total boolSyntax.dest_eq hypothesis of
          SOME (left, right) =>
            SmtFpGraph.lower_atom_domain left orelse
            SmtFpGraph.lower_atom_domain right orelse
            SmtFpGraph.lower_atom_domain hypothesis
        | NONE => false
      fun fp_operation_cost hypothesis =
        let
          val atom =
            case Lib.total boolSyntax.dest_eq hypothesis of
              SOME (left, right) =>
                if SmtFpGraph.lower_atom_domain left then left
                else if SmtFpGraph.lower_atom_domain right then right
                else hypothesis
            | NONE => hypothesis
          fun cost term =
            if boolSyntax.is_select term then 0
            else if Term.is_comb term then
              let
                val (head, arguments) = boolSyntax.strip_comb term
                val own =
                  if Term.is_const head then
                    let val {Thy, Name, ...} =
                      Term.dest_thy_const head
                    in if Thy = "smtfloat" andalso
                         List.exists (fn operation => Name = operation)
                           ["smtfp_add", "smtfp_sub", "smtfp_mul",
                            "smtfp_div", "smtfp_fma", "smtfp_sqrt"]
                       then 1 else 0 end
                  else 0
              in own + List.foldl
                (fn (argument, total) => cost argument + total)
                0 arguments end
            else 0
        in cost atom end
      (* Cheap atom bridges filter impossible private-symbol assignments
         before the shared arithmetic circuits are lowered.  Every bridge
         is still checked before a witness assignment can be selected. *)
      val bridges = Listsort.sort
        (fn (left, right) =>
          Int.compare (fp_operation_cost left,
                       fp_operation_cost right))
        (List.filter fp_bridge extra)
      fun trace_private message =
        if OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" = SOME "full" then
          (Feedback.HOL_MESG ("CPC private FP " ^ message);
           TextIO.flushOut TextIO.stdOut)
        else ()
      fun valid bindings =
        let
          val substitutions = cpc_fp_private_substitutions bindings
          fun check hypothesis =
            let
              val _ = trace_private
                ("bridge cost=" ^
                 Int.toString (fp_operation_cost hypothesis) ^ " begin")
              val instance = Term.subst substitutions hypothesis
              val proof = replay_trust true state [] [instance]
              val _ = trace_private "bridge proved"
            in
              Term.aconv (Thm.concl proof) instance andalso
              HOLset.isSubset (Thm.hypset proof, allowed)
            end
        in List.all check bridges end
        (* A resource gate is inconclusive for this candidate, just as a
           failed checked proof is.  Other finite assignments may still
           admit a checked proof; none is accepted without one. *)
        handle Feedback.HOL_ERR holerr =>
          (trace_private ("bridge failed: " ^
             Feedback.message_of holerr); false)
             | HolSatLib.SAT_cex _ =>
          (trace_private "bridge counterexample"; false)
      val candidate_index = ref 0
      fun find [] = raise ERR "instantiate_cpc_fp_unbound_markers"
          "no checked assignment discharges private FP bridges"
        | find (candidate :: remaining) =
            (candidate_index := !candidate_index + 1;
             trace_private ("candidate " ^
               Int.toString (!candidate_index) ^ "/" ^
               Int.toString (List.length candidates));
             List.app (fn binding => trace_private
               (#kind binding ^ " " ^
                Library.term_to_string (#marker binding) ^ " -> " ^
                Library.term_to_string (#source binding))) candidate;
             if valid candidate then candidate else find remaining)
    in
      if List.null all_markers then theorem
      else if List.null fixed then
        raise ERR "instantiate_cpc_fp_unbound_markers"
          "private FP components have no classification anchors"
      else instantiate_cpc_fp_private_bindings
        (find candidates) theorem
    end

  fun discharge_later_checked_steps state allowed theorem =
    let
      val extra = HOLset.difference (Thm.hypset theorem, allowed)
      val trace = OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" = SOME "1"
        orelse OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" = SOME "full"
      val checked_count = ref 0
      fun trace_checked message =
        if trace then
          (Feedback.HOL_MESG ("CPC checked closure: " ^ message);
           TextIO.flushOut TextIO.stdOut)
        else ()
      fun shallow_shape depth term =
        let
          fun head_name head =
            if Term.is_const head then
              let val {Thy, Name, ...} = Term.dest_thy_const head
              in Thy ^ "$" ^ Name end
            else if Term.is_var head then "variable"
            else if Term.is_abs head then "abstraction"
            else "application"
          fun take 0 _ = []
            | take _ [] = []
            | take n (first :: rest) = first :: take (n - 1) rest
        in
          if depth = 0 orelse not (Term.is_comb term) then
            head_name term
          else
            let val (head, arguments) = boolSyntax.strip_comb term
            in
              head_name head ^ "(" ^
              String.concatWith ","
                (List.map (shallow_shape (depth - 1))
                  (take 4 arguments)) ^ ")"
            end
        end
      val _ = trace_checked
        ("hypotheses=" ^ Int.toString
          (List.length (HOLset.listItems extra)))
      val dependency_memo = ref ([] : (Term.term * Thm.thm) list)
      fun prove_exact_hyp proof result =
        let
          val conclusion = Thm.concl proof
          val hypotheses = Thm.hyp result
          val hypothesis =
            case List.find (fn candidate =>
                Portable.pointer_eq (candidate, conclusion)) hypotheses of
              SOME candidate => candidate
            | NONE =>
                (case List.find (Term.aconv conclusion) hypotheses of
                   SOME candidate => candidate
                 | NONE => raise ERR "discharge_later_checked_steps"
                     "proved hypothesis is absent from the target theorem")
          val proof =
            if Portable.pointer_eq (Thm.concl proof, hypothesis) then proof
            else
              Thm.EQ_MP
                (SmtSkeletonProve.bounded_nodewise_equality
                  SmtResource.max_bitblast_term_nodes
                  (Thm.concl proof) hypothesis)
                proof
        in Thm.MP (Thm.DISCH hypothesis result) proof end
      fun dependency_proof ancestors target =
        case List.find (fn (saved, _) => Term.aconv saved target)
            (!dependency_memo) of
          SOME (_, proof) => proof
        | NONE =>
            let
              val _ = List.exists (fn saved => Term.aconv saved target)
                  ancestors andalso
                raise ERR "discharge_later_checked_steps"
                  "cyclic deferred proof dependency"
              fun conclusion_matches cached =
                Term.aconv (Thm.concl (#thm cached)) target
              fun raw_self theorem =
                HOLset.member (Thm.hypset theorem, target)
              val candidates = List.filter
                (fn cached => conclusion_matches cached andalso
                  not (raw_self (#thm cached)))
                (Net.match target (#thm_cache state))
              fun close theorem =
                let
                  val dependencies = HOLset.listItems
                    (HOLset.difference (Thm.hypset theorem, allowed))
                in
                  List.foldl
                    (fn (dependency, current) =>
                      prove_exact_hyp
                        (dependency_proof (target :: ancestors) dependency)
                        current)
                    theorem dependencies
                end
              val proof = Lib.tryfind (fn cached => close (#thm cached))
                candidates
              val _ = dependency_memo := (target, proof) :: !dependency_memo
            in proof end
      fun discharge (hypothesis, result) =
        let
          val _ = checked_count := !checked_count + 1
          val ordinal = Int.toString (!checked_count)
          val _ = trace_checked ("begin=" ^ ordinal ^ " nodes=" ^
            Int.toString (SmtResource.dag_nodes_up_to 1025 hypothesis))
          val _ = if trace then
            trace_checked ("shape=" ^ shallow_shape 3 hypothesis)
            else ()
          fun replay_checked () =
            let
              val proof = replay_trust true state [] [hypothesis]
              val _ = HOLset.member (Thm.hypset proof, hypothesis) andalso
                raise ERR "discharge_later_checked_steps"
                  "checked trust replay deferred the hypothesis again"
            in proof end
          fun checked_proof () =
            let
              val large =
                SmtResource.dag_nodes_up_to 257 hypothesis > 256 orelse
                not (Option.isSome
                  (Term.term_size_bounded 256 hypothesis))
            in if large then
              replay_checked ()
            else
              (cached_thm state hypothesis
               handle Feedback.HOL_ERR holerr =>
                 if SmtResource.is_resource_gate holerr then
                   raise Feedback.HOL_ERR holerr
                 else
                   (dependency_proof [] hypothesis
                    handle Feedback.HOL_ERR dependency_error =>
                      if SmtResource.is_resource_gate dependency_error then
                        raise Feedback.HOL_ERR dependency_error
                      else replay_checked ()))
            end
          fun checked_generalization () =
            let
              val (variables, body) = boolSyntax.strip_forall hypothesis
              val _ = List.null variables andalso
                raise ERR "discharge_later_checked_steps"
                  "hypothesis is not universally closed"
              val body_proof = cached_thm state body
            in List.foldr
              (fn (variable, theorem) => Thm.GEN variable theorem)
              body_proof variables
            end
          fun checked_then_generalized () =
            checked_proof ()
            handle Feedback.HOL_ERR holerr =>
              if SmtResource.is_resource_gate holerr then
                raise Feedback.HOL_ERR holerr
              else checked_generalization ()
          val proof =
            if boolSyntax.is_forall hypothesis then
              (checked_generalization ()
               handle Feedback.HOL_ERR holerr =>
                 if SmtResource.is_resource_gate holerr then
                   raise Feedback.HOL_ERR holerr
                 else checked_then_generalized ())
            else checked_then_generalized ()
          val discharged = prove_exact_hyp proof result
          val _ = trace_checked ("done=" ^ ordinal)
        in discharged end
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else
            (trace_checked
               ("deferred: " ^ Feedback.message_of holerr);
             result)
    in
      HOLset.foldl discharge theorem extra
    end

  fun check_proof_impl definitions (asl, g, proof : proof) =
    let
      val trace = OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" = SOME "1"
        orelse OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" = SOME "full"
      fun trace_check message =
        if trace then
          (Feedback.HOL_MESG ("CPC proof closure: " ^ message);
           TextIO.flushOut TextIO.stdOut)
        else ()
      val _ = resolution_literal_normalizations :=
        Redblackmap.mkDict Term.compare
      val _ = fp_canonical_fact_laws :=
        Redblackmap.mkDict Type.compare
      val _ = fp_atom_lowerings := Redblackmap.mkDict Term.compare
      val _ = fp_boolean_atom_normalizations :=
        Redblackmap.mkDict Term.compare
      val _ = fp_atom_bridge_laws := []
      val (state, thm) = replay_commands (initial_state definitions asl)
        (proof_commands proof)
      val _ = trace_check "replay complete"
      val _ = profile_cardinalities state
      val _ = profile "CPC(check:conclusion)"
        (fn (left, right) => Term.aconv left right)
        (Thm.concl thm, boolSyntax.F) orelse
        raise ERR "check_proof" "final CPC conclusion is not F"
      val allowed = HOLset.addList (Term.empty_tmset,
        boolSyntax.mk_neg g :: asl)
      val thm = profile "CPC(check:fp_private_abbreviations)"
        instantiate_cpc_fp_private_markers thm
      val _ = trace_check "private markers instantiated"
      val thm = profile "CPC(check:fp_private_unbound)"
        (instantiate_cpc_fp_unbound_markers state allowed) thm
      val _ = trace_check "unbound private markers reconstructed"
      val thm = profile "CPC(check:discharge_later_checked_steps)"
        (discharge_later_checked_steps state allowed) thm
      val _ = trace_check "checked hypotheses discharged"
      val thm = profile "CPC(check:remove_extra_hyps)" remove_extra_hyps
        (asl, g, thm)
      val _ = trace_check "extra hypotheses removed"
      val _ = profile "CPC(check:hypotheses)" HOLset.isSubset
        (Thm.hypset thm, allowed) orelse
        raise ERR "check_proof"
          ("CPC proof retains unexpected hypotheses: " ^
           String.concatWith ", " (List.map Library.term_to_string
             (HOLset.listItems (HOLset.difference (Thm.hypset thm, allowed)))) ^
           "; allowed: " ^ String.concatWith ", "
             (List.map Library.term_to_string (HOLset.listItems allowed)))
    in
      thm
    end

  fun check_proof_with_definitions definitions args =
    profile "CPC(check_proof:total)" (check_proof_impl definitions) args

  fun check_proof args = check_proof_with_definitions [] args

  fun replay_trust_for_test target =
    replay_trust true (initial_state [] []) [] [target]

  fun discharge_private_fp_for_test theorem =
    let
      val state = initial_state [] []
      val allowed = Term.empty_tmset
      val instantiated = instantiate_cpc_fp_unbound_markers
        state allowed theorem
    in discharge_later_checked_steps state allowed instantiated end

  fun replay_root_with_definitions_for_test definitions proof =
    let
      val (state, thm) = replay_commands (initial_state definitions [])
        (proof_commands proof)
      val _ = profile_cardinalities state
    in thm end

  fun replay_root_for_test proof =
    replay_root_with_definitions_for_test [] proof

  fun replay_step_provenance_with_definitions_for_test definitions proof id =
    let
      (* Replay only through the requested occurrence.  Normal replay drops
         steps after their final premise use to bound live certificate state. *)
      fun through accumulated commands =
        case commands of
          [] => raise ERR "replay_step_provenance_for_test"
            ("CPC step '" ^ id ^ "' was not found")
        | command :: rest =>
            let
              val prefix = command :: accumulated
              val name =
                case command of
                  ASSUME (name, _) => name
                | ASSUME_PUSH (name, _) => name
                | STEP step => #id step
            in
              if name = id then List.rev prefix else through prefix rest
            end
      val (state, _) = replay_commands
        (initial_state definitions [])
        (through [] (proof_commands proof))
    in
      step_provenance (find_step "test provenance" state id)
    end

  fun replay_step_provenance_for_test proof id =
    replay_step_provenance_with_definitions_for_test [] proof id

  fun replay_root_with_cache_stats_and_definitions_for_test definitions proof =
    let
      val (state, thm) = replay_commands
        (initial_state definitions [])
        (proof_commands proof)
      val _ = profile_cardinalities state
    in (thm, cache_stats state) end

  fun replay_root_with_cache_stats_for_test proof =
    replay_root_with_cache_stats_and_definitions_for_test [] proof
end

end
