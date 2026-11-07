(* Copyright (c) 2026 The HOL4 contributors. *)

(* Solver-neutral checked replay support for SMT-LIB Unicode-string lemmas. *)

structure SmtStringProve =
struct

  val ERR = Feedback.mk_HOL_ERR "SmtStringProve"

  fun profile name f x = Profile.profile_with_exn_name name f x

  fun with_string_budget case_id prove t =
    SmtResource.with_resource_step_time "String" case_id
      (fn target =>
        (SmtResource.check_resource_goal "String" case_id target;
         prove target)) t

  fun with_string_dag_budget case_id prove t =
    SmtResource.with_resource_step_time "String" case_id
      (fn target =>
        let val maximum = SmtResource.max_term_nodes_for "String" in
          SmtResource.check_dag_size_with_limit
            "String" case_id maximum
            (SmtResource.dag_nodes_up_to maximum target);
          prove target
        end) t

  fun rethrow_resource holerr =
    if SmtResource.is_resource_gate holerr then raise Feedback.HOL_ERR holerr
    else ()

  (* Keep future first-order string rungs under the shared replay bound. *)
  val metis_limit : mlibMeter.limit = {time = SOME 1.0, infs = SOME 5000}
  fun with_metis_limit f =
    Lib.with_flag (metisTools.limit, metis_limit)
      (Feedback.trace ("metis", 0) f)

  fun unsupported theory t =
    raise ERR (theory ^ "_prove")
      ("unsupported th-lemma shape: theory=" ^ theory ^
       "; checked replay is only implemented for Unicode-string proforma, " ^
       "ground evaluation, length/arithmetic, and symbolic " ^
       "concat/prefix/suffix/contains and regex/aut.accept lemmas; " ^
       "conclusion=" ^
       Library.term_to_string t)

  (* `check_seq_type` is a boundary guard for direct users of the String
     prover.  Z3 th-lemma dispatch classifies genuine lists first and sends
     them to SmtSeqProve; this guard therefore cannot hide a native Seq
     failure behind a String-prover fallback. *)
  fun nonstring_seq_error t =
    raise ERR "check_seq_type"
      ("unsupported th-lemma shape: theory=seq; " ^
       "shape=non-string-sequence; dispatch genuine (Seq A) terms through " ^
       "SmtSeqProve; conclusion=" ^ Library.term_to_string t)

  fun smtstring_consts thy names =
    List.map (fn name => Term.prim_mk_const {Thy = thy, Name = name}) names

  (* Rung guards test a term against a whole family of constants.  Comparing
     (theory, name) pairs against a set keeps that to one traversal, rather
     than one traversal per constant, while agreeing with
     'Term.same_const' in ignoring the type instance. *)
  fun const_name_set consts =
    Redblackset.addList
      (Redblackset.empty (Lib.pair_compare (String.compare, String.compare)),
       List.map
         (fn c =>
           let val {Thy, Name, ...} = Term.dest_thy_const c
           in (Thy, Name) end)
         consts)

  fun is_named_const names tm =
    Term.is_const tm andalso
    let val {Thy, Name, ...} = Term.dest_thy_const tm
    in Redblackset.member (names, (Thy, Name)) end

  fun mentions_any names t =
    SmtResource.contains (is_named_const names) t

  fun list_element_type tm =
    Lib.total listSyntax.dest_list_type (Term.type_of tm)

  (* Z3 uses the seq rule for both String and its polymorphic Seq extension.
     Phase 4 String has its own type.  Its constructor payload is an
     implementation detail, while every other HOL list belongs to the
     native SmtSeqProve replayer. *)
  fun check_seq_type t =
    let
      fun is_smtstr_value tm =
        case boolSyntax.strip_comb tm of
          (head, [_]) =>
            Term.is_const head andalso
            let val {Thy, Name, ...} = Term.dest_thy_const head
            in Thy = "smtstring" andalso Name = "SmtStr" end
        | _ => false
      fun contains_sequence tm =
        if is_smtstr_value tm then
          false
        else if Option.isSome (list_element_type tm) then
          true
        else
          (let val (rator, rand) = Term.dest_comb tm
           in contains_sequence rator orelse contains_sequence rand end
           handle Feedback.HOL_ERR _ =>
             (let val (_, body) = Term.dest_abs tm
              in contains_sequence body end
              handle Feedback.HOL_ERR _ => false))
    in
      if contains_sequence t then nonstring_seq_error t else ()
    end

  (* ':smtstr' is a type definition rather than a datatype, so evaluation
     goes through the representation: 'smtstr_rep_compute' unfolds a
     wellformed literal and 'SmtStr_eq_compute' supplies the equality test
     that a datatype constructor would otherwise have given us.  Both are
     load-bearing here -- without them ground string steps do not reduce. *)
  val ground_eval_thms = [
    smtstringTheory.smtstr_rep_compute,
    smtstringTheory.SmtStr_eq_compute,
    smtstringTheory.smtstr_concat_def,
    smtstringTheory.smtstr_len_def,
    smtstringTheory.smtstr_substr_def,
    smtstringTheory.smtstr_update_def,
    smtstringTheory.smtstr_rev_def,
    smtstringTheory.smtstr_at_def,
    smtstringTheory.smtstr_prefixof_def,
    smtstringTheory.smtstr_suffixof_def,
    smtstringTheory.smtstr_contains_def,
    smtstringTheory.smtstr_indexof_aux_def,
    smtstringTheory.smtstr_indexof_def,
    smtstringTheory.smtstr_lt_def,
    smtstringTheory.smtstr_le_def,
    smtstringTheory.smtstr_char_def,
    smtstringTheory.smt_in_re_deriv,
    smtstringTheory.smtstr_replace_def,
    smtstringTheory.smtstr_replace_all_def,
    smtstringTheory.smtstr_replace_re_def,
    smtstringTheory.smtstr_replace_re_all_def,
    smtstringTheory.smtstr_is_digit_compute,
    smtstringTheory.smtstr_to_code_def,
    smtstringTheory.smtstr_from_code_def,
    smtstringTheory.smtstr_digits_def,
    smtstringTheory.smtstr_to_int_def,
    smtstringTheory.smtstr_from_int_def,
    smtstringz3Theory.seq_unit_def,
    smtstringz3Theory.seq_tail_def,
    smtstringz3Theory.seq_eq_def,
    smtstringz3Theory.seq_nth_i_compute,
    smtstringz3Theory.char_is_digit_def,
    smtstringz3Theory.seq_digit2int_def,
    smtstringz3Theory.seq_digit_def,
    smtstringz3Theory.seq_stoi_def,
    smtstringz3Theory.aut_state_def,
    smtstringz3Theory.aut_accept_compute
  ]

  val ground_eval_compset =
    computeLib.add_thms ground_eval_thms
      (computeLib.copy (computeLib.the_compset()))

  fun ground_eval_conv t =
    computeLib.CBV_CONV ground_eval_compset t

  fun ground_eval_prove t =
    Drule.EQT_ELIM (ground_eval_conv t)
    handle Conv.UNCHANGED =>
      raise ERR "ground_eval_prove"
        "ground evaluation did not change the conclusion"
         | Fail message =>
      raise ERR "ground_eval_prove"
        ("ground evaluation failed: " ^ message)

  val length_arith_rewrites = [
    smtstringTheory.smtstr_len_concat,
    smtstringTheory.smtstr_len_substr,
    smtstringTheory.smtstr_len_at,
    smtstringTheory.smtstr_len_nonnegative,
    smtstringTheory.smtstr_len_char,
    smtstringz3Theory.seq_unit_length,
    smtstringz3Theory.seq_tail_length,
    smtstringz3Theory.seq_eq_def,
    integerTheory.int_ge,
    integerTheory.INT_LE_ADDR
  ]

  fun length_arith_prove arith_prove t =
    let
      val normalized =
        simpLib.SIMP_CONV
          (simpLib.++ (bossLib.srw_ss(), intSimps.INT_REDUCE_ss))
          length_arith_rewrites t
      val t' = boolSyntax.rhs (Thm.concl normalized)
      val _ = if Term.aconv t t' then
          raise ERR "length_arith_prove"
            "length normalization did not change the conclusion"
        else ()
    in
      Thm.EQ_MP (Thm.SYM normalized)
        (arith_prove t'
         handle Feedback.HOL_ERR holerr =>
           raise ERR "length_arith_prove"
             ("arithmetic prover rejected normalized conclusion " ^
              Parse.term_to_string t' ^ ": " ^
              Feedback.message_of holerr))
    end
    handle Conv.UNCHANGED =>
      raise ERR "length_arith_prove"
        "length normalization did not change the conclusion"
         | Fail message =>
      raise ERR "length_arith_prove"
        ("length/arithmetic replay failed: " ^ message)

  val seq_shape_rules = [
    smtstringz3Theory.smtstr_at_index,
    smtstringz3Theory.smtstr_at_length,
    smtstringz3Theory.seq_nth_i_to_code_char_z3_index,
    smtstringz3Theory.seq_nth_i_to_code_char_z3,
    smtstringz3Theory.seq_nth_i_to_code_char,
    smtstringz3Theory.seq_nth_i_to_code,
    smtstringz3Theory.seq_nth_i_at,
    smtstringz3Theory.seq_nth_i_unit,
    smtstringz3Theory.seq_nth_i_bound,
    smtstringz3Theory.seq_nth_i_mod_2exp18,
    smtstringz3Theory.unicode_mod_2exp18_eq,
    smtstringz3Theory.seq_head_tail_int,
    smtstringz3Theory.seq_head_tail_int_zero_left,
    smtstringz3Theory.seq_prefixof_singleton,
    smtstringz3Theory.seq_prefixof_head
  ]

  val symbolic_normalizations = [
    smtstringTheory.smtstr_concat_assoc,
    smtstringTheory.smtstr_concat_nil_left,
    smtstringTheory.smtstr_concat_nil_right,
    smtstringTheory.smtstr_concat_middle_singleton,
    smtstringTheory.smtstr_singleton_concat_middle,
    smtstringTheory.smtstr_prefixof_refl,
    smtstringTheory.smtstr_suffixof_refl,
    smtstringTheory.smtstr_contains_refl,
    (* Normalize with the complete iff; the directional rule below lets the
       bounded prover consume a known straddling witness directly. *)
    smtstringTheory.smtstr_contains_concat,
    (* A singleton occurrence cannot split into two nonempty strings.  These
       representation laws reduce that general boundary fact to the complete
       list split in APPEND_EQ_SING; concrete SMT characters discharge their
       code-point side condition during simplification. *)
    smtstringTheory.smtstr_concat_def,
    smtstringTheory.smtstr_eq_singleton,
    smtstringTheory.smtstr_rep_eq_nil,
    listTheory.APPEND_EQ_SING,
    smtstringTheory.smtstr_prefixof_singleton
  ] @ seq_shape_rules @ [
    smtstringz3Theory.char_word18_w2n_n2w,
    smtstringz3Theory.char_num_of_int,
    smtstringz3Theory.char_seq_unit_at,
    smtstringz3Theory.char_seq_unit_inv,
    smtstringz3Theory.seq_unit_def,
    smtstringz3Theory.seq_eq_def,
    smtstringTheory.smtstr_update_def,
    smtstringTheory.smtstr_len_def
  ]

  (* These two semantic theorems cover both equality orientations of the
     general middle-singleton concat family. *)
  val symbolic_concat_lemmas = [
    smtstringTheory.smtstr_concat_middle_singleton,
    smtstringTheory.smtstr_singleton_concat_middle
  ]

  val symbolic_lemmas = symbolic_concat_lemmas @ [
    smtstringTheory.smtstr_len_eq_zero,
    smtstringTheory.smtstr_prefixof_decompose,
    smtstringTheory.smtstr_suffixof_decompose,
    smtstringTheory.smtstr_contains_decompose,
    smtstringTheory.smtstr_prefixof_refl,
    smtstringTheory.smtstr_suffixof_refl,
    smtstringTheory.smtstr_contains_refl,
    smtstringTheory.smtstr_prefixof_singleton,
    smtstringTheory.smtstr_prefixof_imp_contains,
    smtstringTheory.smtstr_suffixof_imp_contains,
    smtstringTheory.smtstr_contains_concat_straddling,
    smtstringTheory.smtstr_prefixof_trans,
    smtstringTheory.smtstr_suffixof_trans,
    smtstringTheory.smtstr_contains_trans
  ] @ seq_shape_rules @ [
    smtstringz3Theory.char_word18_w2n_n2w,
    smtstringz3Theory.char_num_of_int,
    smtstringz3Theory.char_seq_unit_at,
    smtstringz3Theory.char_seq_unit_inv,
    smtstringz3Theory.seq_unit_def,
    smtstringz3Theory.seq_eq_def
  ]

  val symbolic_string_names =
    const_name_set
      (smtstring_consts "smtstring"
        ["smtstr_at", "smtstr_concat", "smtstr_len", "smtstr_update",
         "smtstr_prefixof", "smtstr_suffixof", "smtstr_contains"] @
       smtstring_consts "smtstringz3" ["seq_nth_i", "seq_unit"])

  fun is_symbolic_string_goal t = mentions_any symbolic_string_names t

  (* Refute inconsistent concat decompositions by exposing their finite list
     representations.  The simplifier considers exactly the constructor
     splits present in the literal/unit lists in the goal, so the work is
     bounded by those input lengths rather than a recorded 2+2-versus-3
     theorem. *)
  fun bounded_concat_split_refute t =
    let
      val (antecedent, consequence) = boolSyntax.dest_imp t
      val _ = Term.aconv consequence boolSyntax.F orelse
        raise ERR "bounded_concat_split_refute"
          "concat split goal does not conclude false"
      val antecedent_thm = Thm.ASSUME antecedent
      val length_tm = Term.prim_mk_const
        {Thy = "smtstring", Name = "smtstr_len"}
      fun length_equality conjunct =
        let
          val equality = simpLib.SIMP_RULE boolSimps.bool_ss
            [smtstringz3Theory.seq_eq_def]
            (Library.conj_elim (antecedent_thm, conjunct))
          val length_equality = Thm.AP_TERM length_tm equality
        in
          simpLib.SIMP_RULE
            (simpLib.++ (bossLib.srw_ss(), numSimps.REDUCE_ss))
            [smtstringz3Theory.seq_unit_length,
             smtstringTheory.smtstr_len_concat]
            length_equality
        end
      val length_equalities =
        List.map length_equality (boolSyntax.strip_conj antecedent)
      val contradiction = Tactical.TAC_PROOF
        ((List.map Thm.concl length_equalities, boolSyntax.F),
         intLib.ARITH_TAC)
      val contradiction = List.foldl
        (fn (premise, proof) => Drule.PROVE_HYP premise proof)
        contradiction length_equalities
    in
      Thm.DISCH antecedent contradiction
    end

  (* Certificate numerals select one length schema and four position schemas.
     Code-point literals are deliberately ignored: expanding
     GENLIST at (say) Unicode 196607 would be both irrelevant and unbounded.
     SPECL fixes only the leading schema index; EVAL expands a concrete
     GENLIST and REDUCE_CONV normalizes SUC/numeral side conditions. *)
  val seq_position_names =
    const_name_set
      (smtstring_consts "smtstring" ["smtstr_at"] @
       smtstring_consts "smtstringz3" ["seq_nth_i", "seq_tail"])

  val seq_length_names =
    const_name_set (smtstring_consts "smtstring" ["smtstr_len"])

  fun dest_seq_position_numeral tm =
    let
      val (head, args) = boolSyntax.strip_comb tm
      val _ = is_named_const seq_position_names head orelse
        raise ERR "dest_seq_position_numeral" "not a seq position"
      val raw_index = List.last args
      val index =
        if numSyntax.is_numeral raw_index then raw_index
        else if Type.compare (Term.type_of raw_index, intSyntax.int_ty) =
                EQUAL then
          numSyntax.mk_numeral
            (Arbint.toNat (intSyntax.int_of_term raw_index))
        else boolSyntax.rhs (Thm.concl
          (simpLib.SIMP_CONV
            (simpLib.++ (bossLib.srw_ss(), intSimps.INT_REDUCE_ss))
            [smtstringz3Theory.char_num_of_int,
             smtstringz3Theory.char_num_zero] raw_index))
      val _ = numSyntax.is_numeral index orelse
        raise ERR "dest_seq_position_numeral" "position is symbolic"
    in
      index
    end

  fun dest_seq_length_numeral tm =
    let
      val (left, right) = boolSyntax.dest_eq tm
      fun dest (length, integer) =
        let
          val (head, args) = boolSyntax.strip_comb length
          val _ = is_named_const seq_length_names head andalso
            List.length args = 1 orelse
            raise ERR "dest_seq_length_numeral" "not a length equality"
          val numeral = intSyntax.dest_injected integer
          val _ = numSyntax.is_numeral numeral orelse
            raise ERR "dest_seq_length_numeral" "length is symbolic"
        in
          numeral
        end
    in
      dest (left, right)
      handle Feedback.HOL_ERR _ => dest (right, left)
    end

  (* Solver proofs share large Boolean and bit-vector subterms heavily.
     [HolKernel.find_terms] follows the displayed term tree and therefore
     revisits those shared nodes exponentially.  Traverse the HOL term DAG
     once when collecting replay parameters. *)
  fun dag_matching_terms predicate target =
    let
      fun children term pending =
        if Term.is_comb term then
          let val (operator, operand) = Term.dest_comb term
          in operator :: operand :: pending end
        else if Term.is_abs term then
          let val (_, body) = Term.dest_abs term in body :: pending end
        else
          pending
      fun collect _ found [] = found
        | collect seen found (term :: pending) =
            if HOLset.member (seen, term) then
              collect seen found pending
            else
              let
                val seen = HOLset.add (seen, term)
                val found = if predicate term then term :: found else found
              in
                collect seen found (children term pending)
              end
    in
      collect (HOLset.empty Term.compare) [] [target]
    end

  fun distinct_numerals dest target =
    HOLset.listItems
      (HOLset.addList (Term.empty_tmset,
        List.map dest (dag_matching_terms (Lib.can dest) target)))

  fun has_contextual_index_target target =
    not (List.null
      (distinct_numerals dest_seq_position_numeral target))

  val seq_instance_normalizations = [
    smtstringz3Theory.char_word18_w2n_n2w,
    integerTheory.int_ge,
    smtstringz3Theory.smtstr_from_code_length_valid,
    smtstringz3Theory.smtstr_from_to_code_length_one,
    smtstringz3Theory.seq_head_tail_word18,
    smtstringz3Theory.seq_head_tail_word18_eq,
    smtstringz3Theory.char_num_of_int,
    smtstringz3Theory.char_num_zero,
    smtstringz3Theory.seq_nth_i_mod_2exp18,
    smtstringz3Theory.seq_unit_def,
    smtstringz3Theory.seq_eq_def,
    smtstringTheory.smtstr_concat_def,
    smtstringTheory.smtstr_rep_def
  ]

  val seq_alias_normalizations = [
    smtstringz3Theory.smtstr_from_to_code_length_one,
    smtstringz3Theory.seq_unit_def,
    smtstringz3Theory.seq_eq_def,
    smtstringTheory.smtstr_concat_nil_left
  ]

  fun seq_normalization rewrites target =
    let
      val numeric =
        (simpLib.SIMP_CONV (bossLib.srw_ss())
           [smtstringz3Theory.char_num_of_int,
            smtstringz3Theory.char_num_zero,
            smtstringz3Theory.char_word18_w2n_n2w] target
         handle Conv.UNCHANGED => Thm.REFL target)
      val numeric_target = boolSyntax.rhs (Thm.concl numeric)
      val head_tail =
        (simpLib.SIMP_CONV (bossLib.srw_ss())
           [smtstringz3Theory.seq_head_tail_word18,
            smtstringz3Theory.seq_head_tail_word18_eq] numeric_target
         handle Conv.UNCHANGED => Thm.REFL numeric_target)
      val priority = Thm.TRANS numeric head_tail
      val priority_target = boolSyntax.rhs (Thm.concl priority)
      val normalized =
        (simpLib.SIMP_CONV (bossLib.srw_ss()) rewrites priority_target
         handle Conv.UNCHANGED => Thm.REFL priority_target)
    in
      Thm.TRANS priority normalized
    end

  fun seq_alias_normalization target =
    (simpLib.SIMP_CONV boolSimps.bool_ss
       seq_alias_normalizations target
     handle Conv.UNCHANGED => Thm.REFL target)

  fun prove_alias_metis lemmas target =
    let
      val normalization = seq_alias_normalization target
      val normalized_target = boolSyntax.rhs (Thm.concl normalization)
      val proof = with_metis_limit (fn () =>
        metisLib.METIS_PROVE lemmas normalized_target) ()
    in
      Thm.EQ_MP (Thm.SYM normalization) proof
    end

  fun replay_parametric_seq_prove target =
    let
      (* Length schemas carry their controlling numeral in a premise, so
         inspect the whole target for lengths.  Position schemas are selected
         from the certificate conclusion; this avoids specializing unrelated
         indices from a large shared assertion context. *)
      val (_, conclusion) = boolSyntax.strip_imp target
      val lengths = distinct_numerals dest_seq_length_numeral target
      val positions =
        distinct_numerals dest_seq_position_numeral conclusion
      fun eval_genlist tm =
        let
          val (_, length) = listSyntax.dest_genlist tm
          val _ = numSyntax.is_numeral length orelse
            raise ERR "replay_parametric_seq_prove"
              "GENLIST length is symbolic"
        in
          computeLib.EVAL_CONV tm
        end
      fun eval_rule theorem =
        Conv.CONV_RULE (Conv.TOP_DEPTH_CONV eval_genlist) theorem
        handle Conv.UNCHANGED => theorem
      fun reduce_rule theorem =
        reduceLib.REDUCE_RULE theorem
        handle Conv.UNCHANGED => theorem
      fun specialize theorem numeral =
        reduce_rule (eval_rule (Drule.SPECL [numeral] theorem))
      val length_instances =
        List.map (specialize smtstringz3Theory.seq_length_decompose) lengths
      val position_instances =
        List.concat (List.map (fn numeral =>
          List.map (fn theorem => specialize theorem numeral)
            [smtstringz3Theory.smtstr_at_length_num,
             smtstringz3Theory.smtstr_at_index_num,
             smtstringz3Theory.smtstr_at_unit,
             smtstringz3Theory.seq_split_at,
             smtstringz3Theory.seq_concat_position,
             smtstringz3Theory.seq_tail_step_guard,
             smtstringz3Theory.seq_tail_step]) positions)
      fun canonicalize rewrites theorem =
        let
          val equality = simpLib.SIMP_RULE boolSimps.bool_ss
            [smtstringz3Theory.seq_eq_def] theorem
          val oriented = Conv.CONV_RULE
            (Conv.QCONV (Conv.TOP_DEPTH_CONV
              SmtReplayCanon.reorient_equality_conv)) equality
        in
          Drule.SPEC_ALL
            (simpLib.SIMP_RULE (bossLib.srw_ss())
              rewrites oriented)
        end
      val instances = List.map
        (canonicalize seq_instance_normalizations)
        (length_instances @ position_instances)
      val fallback_instances = List.map
        (canonicalize seq_alias_normalizations)
        (length_instances @ position_instances)
      val support = List.map (canonicalize seq_alias_normalizations) [
        smtstringTheory.smtstr_len_nonnegative,
        integerTheory.INT_LE_ANTISYM,
        smtstringz3Theory.seq_head_tail_int_zero_left,
        smtstringz3Theory.seq_head_tail_word18,
        smtstringz3Theory.concat_singleton_prefix_length,
        smtstringTheory.smtstr_concat_middle_singleton,
        smtstringTheory.smtstr_singleton_concat_middle
      ]
      val _ = null instances andalso
        raise ERR "replay_parametric_seq_prove"
          "no concrete length or sequence-position numeral"
      val normalization =
        seq_normalization seq_instance_normalizations target
      val normalized_target = boolSyntax.rhs (Thm.concl normalization)
      val exact = Lib.total (Lib.tryfind (fn theorem =>
        let
          val substitution =
            Term.match_term (Thm.concl theorem) normalized_target
          val instance = Drule.INST_TY_TERM substitution theorem
        in
          if Term.aconv (Thm.concl instance) normalized_target then instance
          else raise ERR "replay_parametric_seq_prove"
            "specialized schema has a different conclusion"
        end)) (instances @ support)
    in
      if Term.aconv normalized_target boolSyntax.T then
        Thm.EQ_MP (Thm.SYM normalization) boolTheory.TRUTH
      else case exact of
        SOME proof => Thm.EQ_MP (Thm.SYM normalization) proof
      | NONE =>
          let
            val fallback_normalization =
              seq_alias_normalization target
            val fallback_target =
              boolSyntax.rhs (Thm.concl fallback_normalization)
            val proof = with_metis_limit (fn () =>
              metisLib.METIS_PROVE
                (fallback_instances @ support) fallback_target) ()
          in
            Thm.EQ_MP (Thm.SYM fallback_normalization) proof
          end
    end

  (* One budgeted symbolic implementation serves both the String th-lemma
     ladder and Z3's rewrite ladder.  Keep the resource classification at
     this shared boundary so neither consumer can relabel a refusal as an
     ordinary unsupported shape. *)
  fun symbolic_string_prove t =
    with_string_budget "symbolic" (fn t =>
      if not (is_symbolic_string_goal t) orelse
         mentions_any
           (const_name_set
             (smtstring_consts "smtstringz3" ["aut_accept"])) t then
        raise ERR "symbolic_string_prove"
          "no exclusively symbolic concat/prefix/suffix/contains term"
      else
        (* E1(b): bounded constructor splitting is general for the literal
           concat-refutation shape and fails loudly outside that family. *)
        profile "string-symbolic(1)(bounded-concat-split)"
          bounded_concat_split_refute t
        handle Feedback.HOL_ERR holerr =>
        (rethrow_resource holerr;
         profile "string-symbolic(2)(parametric-seq)"
           replay_parametric_seq_prove t)
        handle Feedback.HOL_ERR holerr =>
        (rethrow_resource holerr;
         (* E1(b): normalization plus bounded first-order search is the
            general symbolic String-family procedure and has a loud failure
            boundary. *)
         profile "string-symbolic(3)(general)"
           (fn target =>
             (* The two-orientation concat procedure is part of this general
                rung; it is not a one-theorem, certificate-shape cache. *)
             profile "string-symbolic(general:concat-family)"
               (prove_alias_metis symbolic_concat_lemmas) target
             handle Feedback.HOL_ERR holerr =>
             (rethrow_resource holerr;
              profile "string-symbolic(general:lemma-set)"
                (prove_alias_metis symbolic_lemmas) target)
             handle Feedback.HOL_ERR holerr =>
             (rethrow_resource holerr;
              with_metis_limit (fn () =>
                Tactical.prove (target,
                  Tactical.THEN
                    (bossLib.RW_TAC
                       (simpLib.++
                         (bossLib.srw_ss(), intSimps.INT_REDUCE_ss))
                       symbolic_normalizations,
                     bossLib.METIS_TAC symbolic_lemmas))) ())) t)) t

  (* General automaton rules only.  Literal states and loop bounds are
     specialized from these at replay time below. *)
  val aut_transition_rules = [
    smtstringz3Theory.aut_accept_range_deriv,
    smtstringz3Theory.aut_accept_loop_deriv,
    smtstringz3Theory.aut_accept_loop_nullable_deriv,
    smtstringz3Theory.aut_accept_range_transition,
    smtstringz3Theory.aut_accept_loop_transition,
    smtstringz3Theory.aut_accept_loop_nullable_transition,
    smtstringz3Theory.aut_accept_comp_transition,
    smtstringz3Theory.aut_accept_comp_range_transition,
    smtstringz3Theory.aut_accept_inter_range_comp_transition,
    smtstringz3Theory.aut_accept_loop_empty,
    smtstringz3Theory.aut_accept_loop_range_deriv,
    smtstringz3Theory.aut_accept_loop_range_transition,
    smtstringz3Theory.aut_accept_loop_once
  ]

  val regex_normalizations = [
    smtstringz3Theory.seq_unit_def,
    smtstringTheory.re_nullable_def,
    smtstringTheory.re_deriv_def,
    smtstringTheory.reglan_power_deriv_def,
    smtstringTheory.reglan_loop_deriv_def,
    smtstringTheory.smt_in_re_loop_singleton,
    smtstringTheory.smt_in_re_loop_nullable_singleton,
    smtstringTheory.smt_in_re_loop_empty,
    smtstringTheory.re_deriv_loop_singleton,
    smtstringTheory.re_deriv_loop_nullable_singleton,
    smtstringTheory.smt_in_re_star_allchar,
    smtstringTheory.smt_in_re_plus_allchar,
    smtstringTheory.smt_in_re_def,
    smtstringTheory.smtstr_len_def,
    smtstringz3Theory.aut_accept_zero,
    smtstringz3Theory.aut_accept_none,
    smtstringz3Theory.aut_accept_transition_int
  ] @ aut_transition_rules @ [
    smtstringz3Theory.aut_accept_empty,
    smtstringz3Theory.aut_accept_loop_range_length_int,
    smtstringz3Theory.smt_in_loop_range_nth_at,
    smtstringz3Theory.smt_in_power_range_nth_at,
    smtstringz3Theory.aut_accept_empty_terminal_int
  ]

  val regex_lemmas = [
    smtstringTheory.re_nullable_def,
    smtstringTheory.smt_in_re_loop_singleton,
    smtstringTheory.smt_in_re_loop_nullable_singleton,
    smtstringTheory.smt_in_re_loop_empty,
    smtstringTheory.re_deriv_loop_singleton,
    smtstringTheory.re_deriv_loop_nullable_singleton,
    smtstringTheory.smt_in_re_star_allchar,
    smtstringTheory.smt_in_re_plus_allchar,
    smtstringTheory.re_deriv_correct,
    smtstringTheory.re_nullable_correct,
    smtstringz3Theory.aut_accept_nonnullable_length,
    smtstringz3Theory.aut_accept_nonnullable_length_int,
    smtstringz3Theory.aut_accept_range_length_int,
    smtstringz3Theory.aut_accept_range_length_zero,
    smtstringz3Theory.aut_accept_loop_positive_length_zero,
    smtstringz3Theory.aut_accept_loop_positive_length_seq_unit,
    smtstringz3Theory.aut_accept_plus_allchar_length_one,
    smtstringz3Theory.aut_accept_step,
    smtstringz3Theory.aut_accept_transition,
    smtstringz3Theory.aut_accept_transition_int
  ] @ aut_transition_rules @ [
    smtstringz3Theory.aut_accept_empty,
    smtstringz3Theory.aut_accept_none,
    smtstringz3Theory.aut_accept_loop_range_length_int,
    smtstringz3Theory.smt_in_loop_range_nth_at,
    smtstringz3Theory.smt_in_power_range_nth_at,
    smtstringz3Theory.aut_accept_empty_terminal_int
  ]

  val regex_names =
    const_name_set
      (smtstring_consts "smtstring" ["smt_in_re"] @
       smtstring_consts "smtstringz3" ["aut_accept"])

  (* Length facts are implications whose automaton premise already occurs in
     the goal.  Match the parametric theorem after introducing that premise,
     then reduce only its concrete numeral/code-point side conditions. *)
  val parametric_regex_length_rules = [
    smtstringz3Theory.aut_accept_range_length_int,
    smtstringz3Theory.aut_accept_loop_range_length_int,
    smtstringz3Theory.aut_accept_loop_positive_length_zero,
    smtstringz3Theory.aut_accept_loop_positive_length_seq_unit,
    smtstringz3Theory.aut_accept_plus_allchar_length_one
  ]

  (* Numeral reduction shared by the regex-length and automaton rungs; the
     simpset is built once rather than per replay step. *)
  val char_representation_bridge_theorems =
    [smtstringz3Theory.seq_unit_inv_def,
     smtstringz3Theory.seq_unit_inv_unit,
     smtstringz3Theory.char_word18_w2n_n2w,
     smtstringz3Theory.char_word18_n2w_w2n,
     smtstringz3Theory.unicode_mod_2exp18_eq,
     smtstringz3Theory.char_num_of_int]

  val regex_normalization_theorems =
    [smtstringTheory.smtstr_len_nonnegative,
     integerTheory.int_ge,
     smtstringz3Theory.aut_accept_none,
     smtstringz3Theory.aut_accept_loop_once,
     smtstringz3Theory.num_not_leq_prev,
     smtstringz3Theory.char_num_zero,
     smtstringz3Theory.seq_unit_def,
     smtstringz3Theory.seq_nth_i_unit,
     smtstringz3Theory.seq_nth_i_bound,
     smtstringz3Theory.seq_nth_i_mod_2exp18] @
    char_representation_bridge_theorems

  val regex_reduce_ss = simpLib.++
    (simpLib.++
      (simpLib.++ (boolSimps.bool_ss, numSimps.REDUCE_ss),
       intSimps.INT_REDUCE_ss),
     simpLib.rewrites regex_normalization_theorems)

  fun regex_normalize term = Conv.QCONV
    (simpLib.SIMP_CONV regex_reduce_ss [])
    term

  fun replay_parametric_regex_length_prove target =
    let
      val normalized_target = target
      val target_premise =
        Lib.fst (boolSyntax.dest_imp normalized_target)
      fun instantiate rule =
        let
          val rule_premise =
            Lib.fst (boolSyntax.dest_imp (Thm.concl rule))
          fun match_premise premise =
            let
              val normalized_premise =
                boolSyntax.rhs (Thm.concl (regex_normalize premise))
            in
              Term.match_term normalized_premise target_premise
            end
          val substitution =
            Lib.tryfind match_premise (boolSyntax.strip_conj rule_premise)
          val instance = Drule.INST_TY_TERM substitution rule
          val instance = simpLib.SIMP_RULE regex_reduce_ss [] instance
          val _ = Term.aconv (Thm.concl instance) normalized_target orelse
            raise ERR "replay_parametric_regex_length_prove"
              "specialized length rule has the wrong conclusion"
        in
          instance
        end
    in
      Lib.tryfind instantiate parametric_regex_length_rules
    end

  val automaton_state_names =
    const_name_set
      (smtstring_consts "smtstringz3" ["aut_accept", "seq_nth_i"])

  val automaton_loop_names =
    const_name_set (smtstring_consts "smtstring" ["reglan_loop"])

  fun combination_arg_conv index arity conversion =
    if index = arity - 1 then Conv.RAND_CONV conversion
    else Conv.RATOR_CONV
      (combination_arg_conv index (arity - 1) conversion)

  (* State and loop-bound numerals have one canonical spelling at the replay
     boundary.  In particular, REDUCE_CONV proves SUC k = k+1 after a schema
     is instantiated.  The conversion is deliberately scoped to aut.accept,
     seq.nth_i and re.loop control arguments: Unicode payload numerals are
     neither expanded into Peano form nor otherwise treated as states. *)
  fun automaton_control_atom_conv term =
    let
      val (head, args) = boolSyntax.strip_comb term
      val arity = List.length args
      val reduce = Conv.QCONV reduceLib.REDUCE_CONV
      fun changed conversion =
        let
          val theorem = conversion term
          val (left, right) = boolSyntax.dest_eq (Thm.concl theorem)
        in
          if Term.aconv left right then raise Conv.UNCHANGED else theorem
        end
    in
      if is_named_const automaton_state_names head andalso arity >= 2 then
        changed (combination_arg_conv 1 arity reduce)
      else if is_named_const automaton_loop_names head andalso arity = 3 then
        changed (Conv.THENC
          (combination_arg_conv 1 arity reduce,
           combination_arg_conv 2 arity reduce))
      else
        raise Conv.UNCHANGED
    end

  fun automaton_control_conv term =
    Conv.QCONV
      (Conv.TOP_DEPTH_CONV automaton_control_atom_conv) term

  fun replay_parametric_automaton_prove target =
    let
      fun is_aut_accept term =
        let
          val (head, args) = boolSyntax.strip_comb term
        in
          is_named_const automaton_state_names head andalso
          List.length args = 3 andalso
          let val {Name, ...} = Term.dest_thy_const head
          in Name = "aut_accept" end
        end
        handle Feedback.HOL_ERR _ => false
      fun anchors term = HolKernel.find_terms is_aut_accept term
      val control_normalization = automaton_control_conv target
      val control_target = boolSyntax.rhs (Thm.concl control_normalization)
      val normalized_target = control_target
      val target_anchors = anchors normalized_target
      fun instantiate theorem (schema_anchor, target_anchor) =
        let
          val substitution =
            Term.match_term schema_anchor target_anchor
          val instance = Drule.INST_TY_TERM substitution theorem
          val instance = Conv.CONV_RULE automaton_control_conv instance
          val instance = simpLib.SIMP_RULE regex_reduce_ss
            [smtstringz3Theory.aut_accept_loop_empty] instance
          val oriented = Conv.CONV_RULE
            (Conv.QCONV (Conv.TOP_DEPTH_CONV
              SmtReplayCanon.reorient_equality_conv)) instance
          val instance =
            if Term.aconv (Thm.concl instance) normalized_target then instance
            else if Term.aconv (Thm.concl oriented) normalized_target then
              oriented
            else raise ERR "replay_parametric_automaton_prove"
              "specialized automaton rule has the wrong conclusion"
        in
          instance
        end
      fun theorem_instances theorem =
        let val schema_anchors = anchors (Thm.concl theorem)
        in
          List.concat (List.map (fn schema_anchor =>
            List.map (fn target_anchor =>
              (theorem, (schema_anchor, target_anchor))) target_anchors)
            schema_anchors)
        end
      val candidates = List.concat
        (List.map theorem_instances aut_transition_rules)
      val theorem = Lib.tryfind
        (fn (schema, anchors) => instantiate schema anchors) candidates
    in
      Thm.EQ_MP (Thm.SYM control_normalization) theorem
    end

  fun is_regex_goal t = mentions_any regex_names t

  fun regex_prove t =
    if not (is_regex_goal t) then
      raise ERR "regex_prove" "no regex membership or aut.accept term"
    else
      let
        (* Normalize once at the family boundary so every complete rung sees
           the identical checked Char/Int representation.  Schema matching
           remains on [regex_reduce_ss], so bridge knowledge still has one
           owner. *)
        val normalization = profile "regex(entry)(normalize-target)"
          regex_normalize t
        val normalized = boolSyntax.rhs (Thm.concl normalization)
        fun prove normalized =
          ((* E1(b): general instantiation for the named parametric
               regex-length schemas, with a loud shape boundary. *)
           profile "regex(1)(parametric-length)"
             replay_parametric_regex_length_prove normalized
           handle Feedback.HOL_ERR _ =>
           (* E1(b): structural instantiation plus proof-producing
              control-numeral normalization for the named parametric
              automaton schemas. *)
           profile "regex(2)(parametric-automaton)"
             replay_parametric_automaton_prove normalized
           handle Feedback.HOL_ERR _ =>
           (* E1(b): bounded first-order search over the complete named regex
              lemma set used by this replay family. *)
           profile "regex(3)(bounded-metis)"
             (fn target => with_metis_limit
               (fn () => metisLib.METIS_PROVE regex_lemmas target) ())
             normalized
           handle Feedback.HOL_ERR _ =>
           (* E1(b): the general normalized regex/automaton procedure is
              terminal for the family and fails loudly when it cannot
              reconstruct a fact. *)
           profile "regex(4)(normalized-metis)"
             (fn target => with_metis_limit (fn () =>
               Tactical.prove (target,
                 Tactical.THEN
                   (bossLib.RW_TAC
                      (simpLib.++
                        (bossLib.srw_ss(), intSimps.INT_REDUCE_ss))
                      regex_normalizations,
                    bossLib.METIS_TAC regex_lemmas))) ()) normalized)
        val theorem = prove normalized
      in
        Thm.EQ_MP (Thm.SYM normalization) theorem
      end

  (* `rewrite` steps are a separate customer of the string theory.  Keep
     their entry point narrow: a failed string attempt must not turn an
     ordinary arithmetic rewrite into a string diagnostic. *)
  val string_theory_names =
    const_name_set
      (smtstring_consts "smtstring"
         ["smtstr_concat", "smtstr_len", "smtstr_substr", "smtstr_update",
          "smtstr_rev", "smtstr_at", "smtstr_prefixof", "smtstr_suffixof",
          "smtstr_contains",
          "smtstr_indexof", "smtstr_lt", "smtstr_le", "smtstr_replace",
          "smtstr_replace_all", "smtstr_replace_re",
          "smtstr_replace_re_all", "smtstr_is_digit", "smtstr_to_code",
          "smtstr_from_code", "smtstr_to_int", "smtstr_from_int",
          "smt_in_re", "reglan_to_re", "reglan_concat", "reglan_union",
          "reglan_inter", "reglan_diff", "reglan_comp", "reglan_star",
          "reglan_plus", "reglan_opt", "reglan_range", "reglan_power",
          "reglan_loop"] @
       smtstring_consts "smtstringz3"
         ["seq_unit", "seq_tail", "seq_eq", "seq_nth_i", "seq_stoi",
          "seq_digit", "char_is_digit", "char_bit", "aut_state",
          "aut_accept"])

  datatype family_scan_policy =
      GateLateFamily
    | GateTraversal

  datatype family_scan_result =
      FamilyAbsent
    | FamilyFound of int
    | TraversalLimit of int

  fun scan_string_family policy maximum t =
    let
      (* Admission and its cost measurement are deliberately one traversal.
         In particular, a large completed non-String DAG is an ordinary
         decline under [GateLateFamily], while [GateTraversal] retains the
         generic String classifier's established whole-traversal cap. *)
      fun scan target =
      let
          val bucket_count = 4093
          val seen_buckets = Array.array
            (bucket_count, [] : Term.term list)
          fun name_hash name =
            let
              fun loop index hash =
                if index = String.size name then hash
                else loop (index + 1)
                  ((hash * 33 + Char.ord (String.sub (name, index))) mod
                   bucket_count)
            in
              loop 0 5381
            end
          fun pointer_hash depth term =
            if Term.is_var term then
              name_hash (Lib.fst (Term.dest_var term))
            else if Term.is_const term then
              name_hash (#Name (Term.dest_thy_const term))
            else if depth = 0 then
              if Term.is_abs term then 17 else 19
            else if Term.is_abs term then
              let val (_, body) = Term.dest_abs term in
                (23 + 37 * pointer_hash (depth - 1) body) mod bucket_count
              end
            else
              let
                val (operator, operand) = Term.dest_comb term
              in
                (29 + 37 * pointer_hash (depth - 1) operator +
                 pointer_hash (depth - 1) operand) mod bucket_count
              end
            handle Feedback.HOL_ERR _ => 31
          fun seen term =
            let
              val index = pointer_hash 3 term
              val bucket = Array.sub (seen_buckets, index)
            in
              if List.exists
                   (fn saved => Portable.pointer_eq (term, saved)) bucket
              then true
              else
                (Array.update (seen_buckets, index, term :: bucket); false)
            end
          fun children term rest =
            if Term.is_comb term then
              let val (operator, operand) = Term.dest_comb term
              in operator :: operand :: rest end
            else if Term.is_abs term then
              let val (_, body) = Term.dest_abs term in body :: rest end
            else
              rest
          fun loop observed [] = FamilyAbsent
            | loop observed (term :: rest) =
                if seen term then
                  loop observed rest
                else
                  let
                    val observed = Int.min (maximum + 1, observed + 1)
                    val named_head =
                      let val (head, _) = boolSyntax.strip_comb term
                      in is_named_const string_theory_names head end
                      handle Feedback.HOL_ERR _ => false
                  in
                    if policy = GateTraversal andalso observed > maximum then
                      TraversalLimit observed
                    else if named_head orelse
                            is_named_const string_theory_names term then
                      FamilyFound observed
                    else
                      loop observed (children term rest)
                  end
        in
          loop 0 [target]
        end
      val found = SmtResource.with_resource_step_time
        "String" "family-admission" scan t
    in
      case found of
        FamilyAbsent => false
      | FamilyFound observed =>
          (SmtResource.check_dag_size_with_limit
             "String" "family-admission" maximum observed;
           true)
      | TraversalLimit observed =>
          (SmtResource.check_dag_size_with_limit
             "String" "family-admission" maximum observed;
           false)
    end

  fun check_string_family_admission t =
    scan_string_family GateLateFamily
      SmtResource.max_skeleton_replay_dag_nodes t

  fun has_string_theory_term t =
    scan_string_family GateTraversal
      (SmtResource.max_term_nodes_for "String") t
    handle Feedback.HOL_ERR holerr =>
      (* Classification is deliberately non-gating: a traversal cap means
         that the target is too large for this family, not that it ceased to
         be a String target.  Let the caller's named rung budget report the
         resource diagnostic (e.g. String/rewrite) instead of leaking the
         internal family-admission probe. *)
      if SmtResource.is_resource_gate holerr then true
      else raise Feedback.HOL_ERR holerr

  (* These are semantic rewrite facts, rather than a general-purpose simp
     set.  In particular, do not include METIS here: each rewrite rung must
     reconstruct the recorded equality by a targeted conversion. *)
  val rewrite_normalizations = [
    smtstringTheory.smtstr_concat_def,
    smtstringTheory.smtstr_substr_def,
    smtstringTheory.smtstr_concat_assoc,
    smtstringTheory.smtstr_concat_nil_left,
    smtstringTheory.smtstr_concat_nil_right,
    smtstringTheory.smtstr_update_def,
    smtstringTheory.smtstr_rev_def,
    smtstringTheory.smtstr_len_concat,
    smtstringTheory.smtstr_len_concat_rec,
    smtstringTheory.smtstr_len_eq_zero,
    smtstringTheory.smtstr_prefixof_refl,
    smtstringTheory.smtstr_suffixof_refl,
    smtstringTheory.smtstr_contains_refl,
    smtstringTheory.smtstr_lt_irrefl,
    smtstringTheory.smtstr_le_refl,
    smtstringTheory.smtstr_lt_imp_le,
    smtstringTheory.smt_in_re_deriv,
    smtstringTheory.smt_in_re_power_loop,
    smtstringz3Theory.seq_unit_def,
    smtstringz3Theory.seq_tail_def,
    smtstringz3Theory.seq_eq_def,
    smtstringz3Theory.seq_nth_i_compute,
    smtstringz3Theory.char_is_digit_def,
    smtstringz3Theory.seq_digit_def,
    smtstringz3Theory.seq_stoi_def,
    smtstringz3Theory.aut_state_def,
    smtstringz3Theory.aut_accept_compute
  ]

  val contextual_normalizations =
    ground_eval_thms @ rewrite_normalizations @ regex_normalizations @ [
      smtstringz3Theory.char_word18_w2n_n2w,
      smtstringz3Theory.char_num_of_int,
      smtstringz3Theory.char_seq_unit_at,
      smtstringz3Theory.char_seq_unit_inv
    ]

  (* Forward rules expose guarded consequences whose parameters occur in
     the String/regex context rather than in the replay target.  Such rules
     cannot be used reliably as ordinary simplifier rewrites because their
     range and loop parameters are not determined by the target subterm. *)
  val contextual_forward_rules = [
    smtstringz3Theory.aut_accept_loop_range_nth_at,
    smtstringz3Theory.smt_in_loop_range_nth_at,
    smtstringz3Theory.smt_in_power_range_nth_at
  ]

  val contextual_index_rules = [
    smtstringz3Theory.aut_accept_loop_range_nth_at,
    smtstringz3Theory.smt_in_loop_range_nth_at,
    smtstringz3Theory.smt_in_power_range_nth_at
  ]

  type contextual_index_cache = {
    entries : (Term.term * Thm.thm) list ref,
    hits : int ref,
    misses : int ref
  }

  fun new_contextual_index_cache () : contextual_index_cache = {
    entries = ref [], hits = ref 0, misses = ref 0
  }

  fun contextual_index_cache_metrics
      ({entries, hits, misses} : contextual_index_cache) =
    {entries = List.length (!entries), hits = !hits, misses = !misses}

  (* Build every exact specialization selected by the asserted context.  The
     indexed schema alone is not a cache key: two assertions can use the
     same rule and index while differing in their string, range, power or
     automaton state.  Retain the normalized implication as the key so the
     cached theorem is tied to the assertion instance that justified it. *)
  fun contextual_index_candidates context numeral rule =
    let
      val indexed = Thm.INST
        [{redex = Term.mk_var ("j", numSyntax.num), residue = numeral}] rule
      val schema_premise = Lib.fst (boolSyntax.dest_imp (Thm.concl indexed))
      val schema_anchor = List.last (boolSyntax.strip_conj schema_premise)
      val anchors = List.concat (List.map
        (dag_matching_terms (Lib.can (Term.match_term schema_anchor))) context)
      fun candidate anchor =
        let
          val substitution = Term.match_term schema_anchor anchor
          val instance = Drule.INST_TY_TERM substitution indexed
          val aliases = simpLib.SIMP_RULE boolSimps.bool_ss
            [integerTheory.int_ge,
             smtstringTheory.smtstr_len_nonnegative] instance
          val reduced = reduceLib.REDUCE_RULE aliases
            handle Conv.UNCHANGED => aliases
          val key = Thm.concl reduced
          fun prove () =
            let
              val premise = Lib.fst (boolSyntax.dest_imp key)
              val premise_theorem = Tactical.TAC_PROOF ((context, premise),
                Tactical.THEN
                  (bossLib.ASM_SIMP_TAC
                     (simpLib.++ (bossLib.srw_ss(), intSimps.INT_REDUCE_ss))
                     [integerTheory.int_ge,
                      smtstringTheory.smtstr_len_nonnegative],
                   bossLib.METIS_TAC []))
            in
              Drule.MATCH_MP reduced premise_theorem
            end
        in
          (key, prove)
        end
      fun unique _ [] = []
        | unique seen ((entry as (key, _)) :: rest) =
            if HOLset.member (seen, key) then unique seen rest
            else entry :: unique (HOLset.add (seen, key)) rest
    in
      unique Term.empty_tmset (List.map candidate anchors)
    end

  fun contextual_index_fact context numeral rule =
    Lib.tryfind (fn (_, prove) => prove ())
      (contextual_index_candidates context numeral rule)

  fun cached_contextual_index_facts
      (cache : contextual_index_cache) context numeral rule =
    let
      fun lookup key [] = NONE
        | lookup key ((cached_key, theorem) :: rest) =
            if Term.aconv cached_key key then SOME theorem
            else lookup key rest
      fun fetch (key, prove) =
        case lookup key (!(#entries cache)) of
          SOME theorem =>
            (#hits cache := !(#hits cache) + 1; SOME theorem)
        | NONE =>
            let
              val _ = #misses cache := !(#misses cache) + 1
            in
              case Lib.total prove () of
                SOME theorem =>
                  (#entries cache := (key, theorem) :: !(#entries cache);
                   SOME theorem)
              | NONE => NONE
            end
    in
      List.mapPartial fetch
        (contextual_index_candidates context numeral rule)
    end

  fun cached_contextual_index_fact cache context numeral rule =
    case cached_contextual_index_facts cache context numeral rule of
      theorem :: _ => theorem
    | [] => raise ERR "cached_contextual_index_fact"
        "specialization failed"

  fun indexed_char_clause fact target =
    let
      val clause = Drule.MATCH_MP
        smtstringz3Theory.char_bit_eq_clause fact
      val substitution = Term.match_term (Thm.concl clause) target
      val exact = Drule.INST_TY_TERM substitution clause
      val _ = Term.aconv (Thm.concl exact) target orelse
        raise ERR "indexed_char_clause" "target mismatch"
    in
      exact
    end

  fun indexed_unit_inv_at fact target =
    let
      val target_left = boolSyntax.lhs target
      val target_right = boolSyntax.rhs target
      val n2w = Term.rator target_right
      val unit_inv = smtstringz3Theory.char_seq_unit_inv
      val substitution = profile "string-contextual(unit-inv-match)"
        (fn () => Term.match_term
          (boolSyntax.lhs (Thm.concl unit_inv)) target_left) ()
      val unit_inv = Drule.INST_TY_TERM substitution unit_inv
      val original_word = boolSyntax.rhs (Thm.concl unit_inv)
      val indexed_words = profile "string-contextual(unit-inv-ap-term)"
        (fn () => Thm.AP_TERM n2w fact) ()
      fun reduce term =
        Conv.RAND_CONV
          (Conv.RAND_CONV
            (simpLib.SIMP_CONV boolSimps.bool_ss
              [smtstringz3Theory.char_num_of_int,
               smtstringz3Theory.char_num_zero])) term
        handle Conv.UNCHANGED => Thm.REFL term
      val original_reduction = reduce original_word
      val indexed_reduction = reduce target_right
      val bridge = Thm.TRANS original_reduction
        (Thm.TRANS (Thm.SYM indexed_words) (Thm.SYM indexed_reduction))
      val exact = profile "string-contextual(unit-inv-trans)"
        (fn () => Thm.TRANS unit_inv bridge) ()
      val _ = Term.aconv (Thm.concl exact) target orelse
        raise ERR "indexed_unit_inv_at" "target mismatch"
    in
      exact
    end

  fun indexed_proof fact target =
    if Term.aconv (Thm.concl fact) target then fact
    else
      let val symmetric = Thm.SYM fact in
        if Term.aconv (Thm.concl symmetric) target then symmetric
        else
          indexed_char_clause fact target
          handle Feedback.HOL_ERR _ =>
            indexed_unit_inv_at fact target
            handle Feedback.HOL_ERR _ =>
              Thm.SYM (indexed_unit_inv_at fact
                (boolSyntax.mk_eq
                  (boolSyntax.rhs target, boolSyntax.lhs target)))
      end

  fun first_indexed_proof [] target =
        raise ERR "first_indexed_proof" "no matching index fact"
    | first_indexed_proof (fact :: facts) target =
        indexed_proof fact target
        handle Feedback.HOL_ERR _ =>
          first_indexed_proof facts target

  (* Contextual rung: the recorded conclusion follows from the assertion
     context by simplification with the shared string-theory rule sets.
     Callers order this after the rewrite and theory rungs. *)
  fun string_contextual_prove_cached index_cache context target =
    with_string_dag_budget "contextual"
      (fn current_target =>
        let
          val maximum = SmtResource.max_term_nodes_for "String"
          fun check_context context_term =
            SmtResource.check_dag_size_with_limit
              "String" "contextual" maximum
              (SmtResource.dag_nodes_up_to maximum context_term)
          val _ = profile "string-contextual(check-context)"
            (fn () => List.app check_context context) ()
          val positions = profile "string-contextual(positions)"
            (fn () =>
              distinct_numerals dest_seq_position_numeral current_target) ()
          val index_facts = profile "string-contextual(index-facts)"
            (fn () => List.concat (List.map (fn numeral =>
              List.concat (List.map
                (fn rule =>
                  cached_contextual_index_facts
                    index_cache context numeral rule)
                contextual_index_rules)) positions)) ()
          val char_index_rewrites = [
            smtstringz3Theory.char_num_of_int,
            smtstringz3Theory.char_seq_unit_at,
            smtstringz3Theory.char_seq_unit_inv
          ]
          val indexed_target = not (List.null positions)
        in
          if indexed_target then profile "string-contextual(indexed-proof)"
            (fn () =>
              first_indexed_proof index_facts current_target) ()
          else
            Tactical.TAC_PROOF ((context, current_target),
              Tactical.THEN
                (Tactical.THEN
                   (Tactical.map_every Tactic.ASSUME_TAC index_facts,
                    Tactical.map_every Tactic.IMP_RES_TAC
                      contextual_forward_rules),
                 Tactical.ORELSE
                   (bossLib.ASM_SIMP_TAC boolSimps.bool_ss
                      char_index_rewrites,
                    Tactical.ORELSE
                      (bossLib.ASM_SIMP_TAC
                         (simpLib.++
                           (bossLib.srw_ss(), intSimps.INT_REDUCE_ss))
                         [smtstringz3Theory.char_word18_n2w_w2n],
                       bossLib.ASM_SIMP_TAC
                         (simpLib.++
                           (bossLib.srw_ss(), intSimps.INT_REDUCE_ss))
                         contextual_normalizations))))
        end)
      target

  fun string_contextual_prove context target =
    string_contextual_prove_cached
      (new_contextual_index_cache ()) context target

  fun rewrite_simp_prove t =
    simpLib.SIMP_PROVE
      (simpLib.++ (bossLib.srw_ss(), intSimps.INT_REDUCE_ss))
      rewrite_normalizations t
    handle Feedback.HOL_ERR _ =>
      raise ERR "rewrite_simp_prove"
        "string rewrite normalization did not close the conclusion"

  val regex_rewrite_names =
    const_name_set
      (smtstring_consts "smtstring"
         ["reglan_to_re", "reglan_none", "reglan_all", "reglan_allchar",
          "reglan_concat", "reglan_union", "reglan_inter", "reglan_diff",
          "reglan_comp", "reglan_star", "reglan_plus", "reglan_opt",
          "reglan_range", "reglan_power", "reglan_loop"])

  fun has_regex_rewrite_term t = mentions_any regex_rewrite_names t

  fun rewrite_evaluation_prove t =
    if has_regex_rewrite_term t andalso not (is_regex_goal t) then
      (* Regex constructor equalities are normalized structurally.  Sending
         them through CBV unfolds the derivative engine unnecessarily. *)
      rewrite_simp_prove t
    else if List.null (Term.free_vars t) then
      ground_eval_prove t
    else
      raise ERR "rewrite_ground_eval_prove"
        "ground evaluation requires a closed conclusion"

  (* The ordering is intentional and mirrors `string_prove`: executable
     evaluation precedes the small, named normalization set above. *)
  fun string_rewrite_prove t =
    if (case Lib.total boolSyntax.dest_eq t of
          SOME (left, right) => Term.aconv left right
        | NONE => false) then
      let val (left, _) = boolSyntax.dest_eq t in Thm.REFL left end
    else if not (has_string_theory_term t) then
      (* Family admission must precede the String-specific size gate.  A
         large word-only rewrite belongs to the later BV rungs and must not
         be rejected under a String resource diagnostic. *)
      raise ERR "string_rewrite_prove" "no Unicode-string term"
    else
      with_string_budget "rewrite" (fn t =>
        (* E1(a): executable evaluation is complete for closed String/regex
           constructor equalities (and structural regex constructors). *)
        profile "string-rewrite(1)(ground-eval)"
          rewrite_evaluation_prove t
        handle Feedback.HOL_ERR holerr =>
        (rethrow_resource holerr;
         (* E1(b): the named semantic String normalization family is general
            for its rewrite set and fails loudly outside it. *)
         profile "string-rewrite(2)(normalization)"
           rewrite_simp_prove t)
        handle Feedback.HOL_ERR holerr =>
        (rethrow_resource holerr;
         ((* The same bounded symbolic rung used by String th-lemmas closes
             solver rewrite nodes involving concat/prefix/suffix/contains. *)
          profile "string-rewrite(3)(symbolic)"
            symbolic_string_prove t
          handle Feedback.HOL_ERR symbolic_error =>
            (rethrow_resource symbolic_error;
             (* Preserve the established unsupported-shape boundary when
                neither rewrite procedure applies. *)
             raise Feedback.HOL_ERR holerr)))) t

  fun string_prove_canonical arith_prove t =
    let val () = check_seq_type t in
        (* E1(a): CBV decides the closed executable String fragment. *)
        profile "string(1)(ground-eval)" ground_eval_prove t
        handle Feedback.HOL_ERR holerr =>
        (rethrow_resource holerr;
         (* E1(b): length normalization followed by the supplied arithmetic
            procedure is general for the selected length family. *)
         profile "string(2)(length-arith)"
           (length_arith_prove arith_prove) t)
        handle Feedback.HOL_ERR holerr =>
        (rethrow_resource holerr;
         (* E1(b): the symbolic sub-ladder is general for selected concat,
            prefix, suffix and contains clauses, with loud refusal. *)
         profile "string(3)(symbolic)" symbolic_string_prove t)
        handle Feedback.HOL_ERR holerr =>
        (rethrow_resource holerr;
         (* E1(b): the regex sub-ladder is general for selected membership
            and aut.accept clauses, with loud refusal. *)
         profile "string(4)(regex)" regex_prove t)
        handle Feedback.HOL_ERR holerr =>
        (rethrow_resource holerr;
         (* E1(b): terminal loud String/regex family boundary. *)
         profile "string(5)(unsupported)" (unsupported "seq") t)
    end

  (* Normalize the solver's 'seq_eq' equality alias, then orient every
     equality before selecting a prover rung.  Both conversions prove their
     equivalences; after replaying the canonical proposition, EQ_MP transports
     the theorem back to the exact proposition declared by the caller. *)
  fun string_prove arith_prove target =
    with_string_budget "replay" (fn target =>
      let
        val seq_equality = Conv.QCONV
          (Rewrite.PURE_REWRITE_CONV
            [smtstringz3Theory.seq_eq_def]) target
        val equality_target = boolSyntax.rhs (Thm.concl seq_equality)
        val orientation =
          if mentions_any
            (const_name_set
              (smtstring_consts "smtstringz3" ["aut_accept"]))
            equality_target then Thm.REFL equality_target
          else Conv.QCONV
            (Conv.TOP_DEPTH_CONV
              SmtReplayCanon.reorient_equality_conv) equality_target
        val normalization = Thm.TRANS seq_equality orientation
        val canonical = boolSyntax.rhs (Thm.concl orientation)
        val _ = if Term.aconv equality_target canonical then ()
          else profile "string(entry)(equality-orientation)"
            (fn () => ()) ()
        val theorem = string_prove_canonical arith_prove canonical
      in
        Thm.EQ_MP (Thm.SYM normalization) theorem
      end) target

  (* Z3 shares each tail of its bitwise comparison through proof lets.
     Parsing expands those lets, so compact the Boolean recurrence
     top-down before bit-blasting to keep the checked term linear. *)
  val compact_char_compare =
    Drule.SPEC_ALL (tautLib.TAUT_PROVE
      ``!c d r:bool. ((~d /\ c) \/ (~d /\ r) \/ (c /\ r)) =
        ((c /\ ~d) \/ ((c = d) /\ r))``)

  val char_word_expansion_theorems =
    [smtstringz3Theory.char_bit_word18,
     smtstringz3Theory.char_is_digit_word18,
     smtstringz3Theory.char_le_word18,
     smtstringz3Theory.seq_nth_i_mod_2exp18,
     smtstringz3Theory.unicode_mod_2exp18_eq]

  (* Preserve the production character prover's historical syntactic
     admission boundary.  The prototype owner below is intentionally more
     precise and theorem-driven; it must not widen this public prover. *)
  val char_decomposition_names =
    const_name_set
      (smtstring_consts "smtstringz3" ["char_bit", "char_is_digit"] @
       smtstring_consts "words" ["word_or"])

  val char_word_domain_ss =
    simpLib.++ (simpLib.empty_ss, numSimps.REDUCE_ss)

  fun theorem_rewrite_lhs theorem =
    let
      val (_, body) = boolSyntax.strip_forall (Thm.concl theorem)
      val equation =
        if boolSyntax.is_imp body then Lib.snd (boolSyntax.dest_imp body)
        else body
    in
      Lib.fst (boolSyntax.dest_eq equation)
    end

  fun char_theorem_applies_at theorem term =
    if Lib.can (Term.match_term (theorem_rewrite_lhs theorem)) term then
      let
        val rewritten = simpLib.SIMP_CONV char_word_domain_ss
          [theorem] term
      in
        not (Term.aconv term (boolSyntax.rhs (Thm.concl rewritten)))
      end
      handle Conv.UNCHANGED => false
    else false

  (* Exact, theorem-driven ownership boundary for the character expansion
     kit.  It recognizes only shapes to which one of the three checked
     word18 bridge theorems actually applies, including the raw
     [w2n c <= w2n d] order shape. *)
  fun char_word_expansion_domain_scan applies target =
    SmtResource.with_resource_step_time
      "String" "char-family-admission"
      (fn target =>
        let
          val maximum = SmtResource.max_skeleton_replay_dag_nodes
          (* This admission walk is deliberately pointer-based.  Character
             expansion fixtures contain deeply shared Boolean structure; a
             structural [HOLset] lookup repeatedly compares that entire
             shared spine and can consume the step-time budget before the
             DAG cap is reached.  The resource metric is a physical-DAG
             bound, so pointer identity is the appropriate key here. *)
          val bucket_count = 4093
          val seen_buckets = Array.array
            (bucket_count, [] : Term.term list)
          fun name_hash name =
            let
              fun loop index hash =
                if index = String.size name then hash
                else loop (index + 1)
                  ((hash * 33 + Char.ord (String.sub (name, index))) mod
                   bucket_count)
            in
              loop 0 5381
            end
          fun pointer_hash depth term =
            if Term.is_var term then
              name_hash (Lib.fst (Term.dest_var term))
            else if Term.is_const term then
              name_hash (#Name (Term.dest_thy_const term))
            else if depth = 0 then
              if Term.is_abs term then 17 else 19
            else if Term.is_abs term then
              let val (_, body) = Term.dest_abs term in
                (23 + 37 * pointer_hash (depth - 1) body) mod bucket_count
              end
            else
              let
                val (operator, operand) = Term.dest_comb term
              in
                (29 + 37 * pointer_hash (depth - 1) operator +
                 pointer_hash (depth - 1) operand) mod bucket_count
              end
            handle Feedback.HOL_ERR _ => 31
          fun seen term =
            let
              val index = pointer_hash 3 term
              val bucket = Array.sub (seen_buckets, index)
            in
              if List.exists
                   (fn saved => Portable.pointer_eq (term, saved)) bucket
              then true
              else
                (Array.update (seen_buckets, index, term :: bucket); false)
            end
          fun loop _ [] = false
            | loop observed (term :: pending) =
                if seen term then
                  loop observed pending
                else
                  let
                    val observed = Int.min (maximum + 1, observed + 1)
                    val () = SmtResource.check_dag_size_with_limit
                      "String" "char-family-admission"
                      maximum observed
                  in
                    if applies term then true
                    else
                      loop observed
                        (SmtResource.term_children term @ pending)
                  end
        in
          loop 0 [target]
        end) target

  fun char_word_expansion_domain target =
    char_word_expansion_domain_scan
      (fn term => List.exists
        (fn theorem => char_theorem_applies_at theorem term)
        char_word_expansion_theorems) target

  fun compact_char_word_core_unbounded t =
    let
      val compacted =
        Conv.TRY_CONV
          (Conv.TOP_DEPTH_CONV
            (Conv.REWR_CONV compact_char_compare)) t
        handle Conv.UNCHANGED => Thm.REFL t
             | Feedback.HOL_ERR _ => Thm.REFL t
      val compacted_t = boolSyntax.rhs (Thm.concl compacted)
      val conditional_rewrites =
        [smtstringz3Theory.int_cond_weight_nonpositive,
         smtstringz3Theory.int_cond_weight_nonnegative,
         smtstringz3Theory.int_cond_weight_at_least,
         smtstringz3Theory.int_cond_weight_upper_endpoint,
         smtstringz3Theory.int_cond_weight_lower_endpoint]
      val simplifier =
        simpLib.++
          (simpLib.++ (bossLib.srw_ss(), wordsLib.WORD_BIT_EQ_ss),
           intSimps.INT_REDUCE_ss)
      val simplified =
        (simpLib.SIMP_CONV simplifier
           (integerTheory.int_ge :: char_word_expansion_theorems @
            conditional_rewrites) compacted_t
         handle Conv.UNCHANGED => Thm.REFL compacted_t)
      val simplified_t = boolSyntax.rhs (Thm.concl simplified)
      val endpoints =
        (simpLib.SIMP_CONV simplifier conditional_rewrites simplified_t
         handle Conv.UNCHANGED => Thm.REFL simplified_t)
    in
      Thm.TRANS compacted (Thm.TRANS simplified endpoints)
    end

  fun compact_char_word_core t =
    with_string_dag_budget "char-compaction"
      compact_char_word_core_unbounded t

  fun char_word_normalization_core_unbounded t =
    let
      val compacted =
        Conv.TRY_CONV
          (Conv.TOP_DEPTH_CONV
            (Conv.REWR_CONV compact_char_compare)) t
        handle Conv.UNCHANGED => Thm.REFL t
             | Feedback.HOL_ERR _ => Thm.REFL t
      val compacted_t = boolSyntax.rhs (Thm.concl compacted)
      val summed =
        Conv.TRY_CONV
          (Conv.ONCE_DEPTH_CONV
            (Conv.REWR_CONV smtstringz3Theory.char_bit_sum_18))
          compacted_t
        handle Conv.UNCHANGED => Thm.REFL compacted_t
             | Feedback.HOL_ERR _ => Thm.REFL compacted_t
      val summed_t = boolSyntax.rhs (Thm.concl summed)
      val simplified =
        (simpLib.SIMP_CONV
           (simpLib.++ (bossLib.srw_ss(), wordsLib.WORD_BIT_EQ_ss))
           char_word_expansion_theorems summed_t
         handle Conv.UNCHANGED => Thm.REFL summed_t)
      val normalized = Thm.TRANS compacted (Thm.TRANS summed simplified)
    in
      normalized
    end

  fun char_word_normalization_core t =
    with_string_dag_budget "char-normalization"
      char_word_normalization_core_unbounded t

  fun char_word_expansion_conv t =
    let
      val _ =
        if char_word_expansion_domain t then ()
        else raise ERR "char_word_expansion_conv"
          "term is outside the checked character expansion domain"
    in
      char_word_normalization_core t
    end

  fun char_bitblast_prove t =
    let
      val _ =
        if mentions_any char_decomposition_names t then ()
        else raise ERR "char_prove" "no char decomposition atom"
      val normalized = char_word_normalization_core t
      val t' = boolSyntax.rhs (Thm.concl normalized)
      val thm = Tactical.prove (t', blastLib.BBLAST_TAC)
    in
      Thm.EQ_MP (Thm.SYM normalized) thm
    end

  fun char_prove t =
    SmtResource.with_resource_step_time "String" "char-bitblast"
      (fn target =>
        let
          (* Compact shared word/character structure before measuring the
             term.  Measuring Z3's DAG-shaped character spelling as an
             unfolded HOL tree can otherwise reject a small normalized
             obligation before the checked normalizer gets to see it. *)
          val normalized = char_word_normalization_core target
          val normalized_target = boolSyntax.rhs (Thm.concl normalized)
          val _ = SmtResource.check_resource_goal
            "String" "char-bitblast" normalized_target
          val proved =
            profile "char(1)(bitblast)"
              (fn t => Tactical.prove (t, blastLib.BBLAST_TAC))
              normalized_target
            handle Feedback.HOL_ERR holerr =>
              (rethrow_resource holerr;
               profile "char(2)(unsupported)" (unsupported "char")
                 normalized_target)
        in
          Thm.EQ_MP (Thm.SYM normalized) proved
        end) t

end
