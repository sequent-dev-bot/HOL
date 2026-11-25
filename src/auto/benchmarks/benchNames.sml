structure benchNames :> benchNames =
struct

open HolKernel

datatype resolution =
    Theorems of benchLib.named_thm list
  | Context
  | Inlined
  | Native
  | Unrepresented

fun named theory theorem =
  {name = theory ^ "$" ^ theorem, theorem = DB.fetch theory theorem}

(* A HOL4 library theorem, named the way the benchmark reports names.
   Nothing records which Isabelle statement it is meant to be, so a
   wrong one shows up only by reading the two side by side. *)
fun library theory theorem () = Theorems [named theory theorem]

(* A lemma of the translation theory.  Each one cites the Isabelle file
   and lemma it renders at its definition in parityTranslationScript.sml,
   so faithfulness against f7e02b7e is checked there, not restated here. *)
fun translated theorem () = Theorems [named "parityTranslation" theorem]

(* Isabelle's [t.split] and [t.split_asm] come out of the datatype
   package; HOL4's counterparts are derived from TypeBase on demand and
   stored nowhere, so they are named after the case constant they split,
   which is the identity the simplifier registers them under.  The
   [t_case_eq] theorems the table used to name here are not split rules
   at all -- their left side is an equation and not [P (case ...)] -- so
   the splitter dropped every one of them and the [split:] element of
   the method never reached the goal. *)
fun split_named theorem =
  {name =
     splitLib.split_thm_name theorem ^
     (if splitLib.is_asm_split theorem then "[split_asm]" else "[split]"),
   theorem = theorem}

fun datatype_split ty () = Theorems [split_named (splitLib.type_split_of ty)]

fun datatype_asm_split ty () =
  Theorems [split_named (splitLib.type_asm_split_of ty)]

fun datatype_splits ty () =
  Theorems (map split_named (splitLib.type_split_rules ty))

(* The combinators below -- [bundle], [symmetric], [first_case],
   [later_cases] -- only make sense over an entry that names theorems.
   Applying one to an entry that names none is an authoring mistake,
   not an empty list. *)
fun resolved build =
  case build () of
      Theorems theorems => theorems
    | _ =>
        raise mk_HOL_ERR "benchNames" "resolved"
          "a derived entry was built from one that names no theorem"

(* What an Isabelle fact-list name abbreviates. *)
fun bundle builds () = Theorems (List.concat (map resolved builds))

fun symmetric build () =
  Theorems
    (map (fn {name, theorem} =>
           {name = name ^ "[symmetric]", theorem = Conv.GSYM theorem})
       (resolved build))

(* An Isabelle theorem is stored in hhf normal form, so a rule never
   quantifies the subject its conclusion is about: [option.induct]
   concludes the atom [?P ?option].  HOL4 has no meta level and states
   the same rule with an object binder -- [option_induction] concludes
   [!x. P x] -- which as a rule indexes a universal formula and meets no
   atomic goal.  The two are the same theorem; this is the shape the
   Isabelle name denotes, so an entry whose source rule is hhf-normal
   says so here rather than leaving the method a rule it cannot use. *)
fun hhf build () =
  Theorems
    (map (fn {name, theorem} =>
           {name = name, theorem = clasetRules.atomise_conclusion theorem})
       (resolved build))

(* An attribute that only instantiates -- [of ...], [where ...] --
   names the same theorem at particular arguments, and the arguments
   are read off the source method rather than chosen here.  It is not
   always a control hint: where the instance mentions constants the
   general statement does not -- an identity key collapsing
   [insort_key f] to [insort] -- HOL4 cannot recover it by matching,
   because the general statement's left-hand side occurs nowhere in
   the goal.  Each binding names a variable of the theorem and the
   term the method instantiates it with. *)
fun instantiated bindings build () =
  let
    (* The instantiating term carries type variables of its own -- the
       quoted identity parses at [:'a] -- and matching it against the
       theorem as written identifies the theorem's variable of that
       name with it, collapsing two independent types wherever the
       names meet: [zip_map_map[of f xs "\\<lambda>x. x" ys]] otherwise
       loses the distinction between [f]'s domain and the identity's.
       The theorem is renamed apart first, so a binding instantiates
       only what the method instantiates.  The instance's remaining
       type variables are its own, and INSERT_FACTS_TAC specialises
       them at the goal each citation is inserted into. *)
    fun renamed_apart terms theorem =
      let
        fun variables_of terms =
          List.foldl
            (fn (term, seen) => Lib.union (type_vars_in_term term) seen)
            [] terms
        val occupied = variables_of terms
        val own = variables_of (Thm.concl theorem :: Thm.hyp theorem)
        (* A type variable's name is a quote and alphanumerics, so a
           fresh one is numbered rather than primed. *)
        fun fresh taken variable =
          let
            val base = dest_vartype variable
            fun attempt index =
              let val candidate = mk_vartype (base ^ Int.toString index)
              in
                if Lib.mem candidate taken then attempt (index + 1)
                else candidate
              end
          in
            attempt 1
          end
        val (substitution, _) =
          List.foldl
            (fn (variable, (substitution, taken)) =>
              if Lib.mem variable occupied then
                let val replacement = fresh taken variable
                in
                  (substitution @ [variable |-> replacement],
                   replacement :: taken)
                end
              else
                (substitution, taken))
            ([], Lib.union occupied own)
            own
      in
        Thm.INST_TYPE substitution theorem
      end
    fun bind (name, term) theorem =
      case List.find (fn variable => fst (dest_var variable) = name)
             (free_vars (concl theorem)) of
          NONE =>
            raise mk_HOL_ERR "benchNames" "instantiated"
              (name ^ " is not a variable of the cited theorem")
        | SOME variable =>
            let val (terms, types) = Term.match_term variable term
            in Thm.INST terms (Thm.INST_TYPE types theorem)
            end
    fun instance theorem =
      Drule.GEN_ALL
        (Drule.DISCH_ALL
          (List.foldl (fn (binding, current) => bind binding current)
            (Drule.SPEC_ALL
              (Drule.UNDISCH_ALL
                (Drule.SPEC_ALL
                  (renamed_apart (map snd bindings) theorem))))
            bindings))
  in
    Theorems
      (map (fn {name, theorem} => {name = name, theorem = instance theorem})
        (resolved build))
  end

(* The instance itself: each binding names a variable of the HOL4
   statement and builds, from that variable's type, the term standing
   in its place.  A position the method leaves open contributes no
   binding and its variable stays quantified, which is what a
   remaining schematic amounts to in an inserted premise; an
   instantiated one does not get quantified again. *)
fun at_goal_instance caller bindings build () =
  let
    fun instance theorem =
      let
        val body = Drule.SPEC_ALL theorem
        val variables = free_vars (concl body)
        fun paired (name, argument) =
          case List.find (fn v => fst (dest_var v) = name) variables of
              NONE =>
                raise mk_HOL_ERR "benchNames" caller
                  (name ^ " is not a variable of the cited theorem")
            | SOME variable =>
                let
                  val replacement = argument (type_of variable)
                in
                  if Type.compare (type_of replacement, type_of variable)
                     = EQUAL
                  then (variable, replacement)
                  else
                    raise mk_HOL_ERR "benchNames" caller
                      (name ^ " is instantiated at a term of another type")
                end
        val pairs = map paired bindings
        fun instantiated variable =
          List.exists (fn (bound, _) => aconv bound variable) pairs
        val specialised =
          Thm.INST (map (fn (bound, term) => bound |-> term) pairs) body
      in
        Thm.GENL (List.filter (not o instantiated) variables) specialised
      end
  in
    Theorems
      (map (fn {name, theorem} => {name = name, theorem = instance theorem})
        (resolved build))
  end

(* An attribute that instantiates at plain variables names the same
   theorem at the source lemma's own variables, and the translation
   names a goal's variables after them -- Isabelle's [xs] is [v_xs0] --
   so the instance can be written from the names the method wrote and
   says the same thing for every goal that cites that string.  The
   source's positions are its own statement's, which the translation
   does not preserve, so the pairing is written out rather than
   counted off.

   Matching does not always recover such an instance.  A supplied fact
   reaches the goal as a premise, and splitting an iff is a case
   analysis on a ground equivalence: a quantified one is not something
   a safe step takes apart, so a citation the source instantiates
   before inserting has to be instantiated here too. *)
fun at_goal_variables bindings build () =
  at_goal_instance "at_goal_variables"
    (map
      (fn (name, argument) =>
        (name, fn ty => mk_var ("v_" ^ argument ^ "0", ty)))
      bindings)
    build ()

(* The same instance, where the method instantiates at a term over a
   goal's variables rather than at one of them: [of "\\<lambda>x. \\<not>
   P x"] on an iff about [P] states the same iff about its negation,
   and the translation's name for the goal's [P] is what the term is
   written over.  The goal variables the term mentions stay free, as
   the ones it replaces do: Isabelle instantiates at a variable its
   proof state has fixed, and re-generalising here would hand the
   search a quantified predicate to guess instead -- measured, the
   generalised form does not return in five minutes where this one
   closes the goal in 0.026s. *)
fun at_goal_terms bindings build () =
  at_goal_instance "at_goal_terms"
    (map (fn (name, term) => (name, fn _ => term)) bindings)
    build ()

(* A HOL4 recursion equation or characterisation bundles clauses an
   Isabelle citation names one at a time, and handing over the bundle
   gives a method facts it did not name.  The conjunction can sit under
   the theorem's quantifiers and premises -- [MIN_SET_LEM] states both
   its clauses inside [~(s = {}) ==> _] -- so the prefix comes off
   before the clause is taken and goes back on after. *)
fun conjunct_of part theorem =
  let
    fun peel current =
      case Lib.total Drule.UNDISCH (Drule.SPEC_ALL current) of
          NONE => Drule.SPEC_ALL current
        | SOME stripped => peel stripped
    val body = peel theorem
    val selected = part body
  in
    Drule.GEN_ALL
      (List.foldl (fn (hypothesis, current) => Thm.DISCH hypothesis current)
        selected (Thm.hyp body))
  end

(* The first equation of a multi-clause definition. *)
fun first_case build () =
  Theorems
    (map (fn {name, theorem} =>
            {name = name, theorem = conjunct_of CONJUNCT1 theorem})
       (resolved build))

(* The rest of one. *)
fun later_cases build () =
  Theorems
    (map (fn {name, theorem} =>
            {name = name, theorem = conjunct_of CONJUNCT2 theorem})
       (resolved build))

fun context () = Context
fun inlined () = Inlined
fun native () = Native
fun unrepresented () = Unrepresented

val table : (string * (unit -> resolution)) list =
[
  (* ---- Isar context facts ---------------------------------------- *)
  ("assms", context),
  ("that", context),
  ("a", context),
  ("b", context),
  ("d", context),
  ("j", context),

  (* ---- Set.thy ---------------------------------------------------- *)
  ("set_eqI", library "pred_set" "EXTENSION"),
  ("equalityE", translated "source_equalityE"),
  ("less_eq_set_def", library "pred_set" "SUBSET_DEF"),
  ("bot_set_def", library "pred_set" "EMPTY_DEF"),
  ("empty_def", library "pred_set" "EMPTY_DEF"),
  ("top_set_def", library "pred_set" "UNIV_DEF"),
  ("UNIV_def", library "pred_set" "UNIV_DEF"),
  ("Pow_def", library "pred_set" "POW_DEF"),
  ("uminus_set_def", library "pred_set" "COMPL_DEF"),
  ("inf_set_def", library "pred_set" "INTER_DEF"),
  ("sup_set_def", library "pred_set" "UNION_DEF"),
  ("Un_def", library "pred_set" "UNION_DEF"),
  ("minus_set_def", library "pred_set" "DIFF_DEF"),
  ("insert_compr", library "pred_set" "INSERT_DEF"),
  ("image_constant", translated "source_image_constant"),
  ("subset_insert_iff", library "pred_set" "SUBSET_INSERT_DELETE"),
  ("psubset_eq", library "pred_set" "PSUBSET_DEF"),
  ("subset_antisym", library "pred_set" "SUBSET_ANTISYM"),
  ("vimage_def", library "pred_set" "PREIMAGE_def"),
  ("is_singleton_def", library "pred_set" "SING_DEF"),
  (* HOL4's [pairwise] omits the [x <> y] guard Isabelle's carries,
     so it is a different predicate; the translated goals write
     Isabelle's definition out and leave the citation nothing. *)
  ("pairwise_def", inlined),
  ("disjnt_def", library "pred_set" "DISJOINT_DEF"),
  ("disjnt_iff", library "pred_set" "IN_DISJOINT"),
  ("disjoint_iff", library "pred_set" "IN_DISJOINT"),
  ("sym", library "bool" "EQ_SYM"),
  ("all_conj_distrib", library "bool" "FORALL_AND_THM"),
  ("bind_def", library "option" "OPTION_BIND_def"),

  (* ---- Names the translation theory renders ----------------------- *)
  ("Ball_def",
   translated "source_ball_def"),
  ("Bex_def",
   translated "source_bex_def"),
  ("conj_cong",
   translated "source_conj_cong"),
  ("subset_imageE",
   translated "source_subset_imageE"),
  ("image_def",
   translated "source_image_def"),
  ("subsetD",
   translated "source_subsetD"),
  ("bool_induct",
   translated "source_bool_induct"),
  ("bool_contrapos",
   translated "source_bool_contrapos"),
  ("inj_onI",
   translated "source_inj_onI"),
  ("inj_on_def",
   translated "source_inj_on_def"),
  ("hd_append",
   translated "source_hd_append"),
  ("tl_append",
   translated "source_tl_append"),
  ("map_inj_on",
   translated "source_map_inj_on"),
  ("map_injective",
   translated "source_map_injective"),
  ("inj_mapD",
   translated "source_inj_mapD"),
  ("inj_mapI",
   translated "source_inj_mapI"),
  ("inj_onD",
   translated "source_inj_onD"),
  ("rev_swap",
   translated "source_rev_swap"),
  ("split_list",
   translated "source_split_list"),
  ("split_list_first",
   translated "source_split_list_first"),
  ("split_list_last",
   translated "source_split_list_last"),
  (* The entry names the fact these citations resolve, as it stands:
     [benchRecipe.to_recipe] reads the instance out of the goal whose
     assumptions [OF assms] names, so the table says the same thing for
     every goal that cites the string. *)
  ("split_list_prop[OF assms]",
   translated "source_split_list_prop"),
  ("split_list_first_prop[OF assms]",
   translated "source_split_list_first_prop"),
  ("split_list_last_prop[OF assms]",
   translated "source_split_list_last_prop"),
  ("Cons_eq_append_conv",
   translated "source_Cons_eq_append_conv"),
  ("concat_eq_concat_iff",
   translated "source_concat_eq_concat_iff"),
  ("concat_eq_appendD",
   translated "source_concat_eq_appendD"),
  ("filter_eq_ConsD",
   translated "source_filter_eq_ConsD"),
  ("set_conv_nth",
   translated "source_set_conv_nth"),
  ("set_update_subset_insert[THEN subsetD]",
   translated "source_set_update_subset_insert"),
  ("last_append",
   translated "source_last_append"),
  ("neq_Nil_conv",
   translated "source_neq_nil_conv"),
  ("takeWhile_append1[of _ xs P ys]",
   at_goal_variables
     [("items", "xs"), ("predicate", "P"), ("suffix", "ys")]
     (translated "source_takeWhile_append1")),
  ("takeWhile_append2[of xs P ys]",
   at_goal_variables
     [("items", "xs"), ("predicate", "P"), ("suffix", "ys")]
     (translated "source_takeWhile_append2")),
  ("takeWhile_dropWhile_id[of P xs]",
   at_goal_variables
     [("predicate", "P"), ("items", "xs")]
     (translated "source_takeWhile_dropWhile_id")),
  ("takeWhile_eq_Nil_iff[of P xs]",
   at_goal_variables
     [("predicate", "P"), ("items", "xs")]
     (translated "source_takeWhile_eq_nil_iff")),
  ("dropWhile_append1[of _ xs P ys]",
   at_goal_variables
     [("items", "xs"), ("predicate", "P"), ("suffix", "ys")]
     (translated "source_dropWhile_append1")),
  ("dropWhile_append2[of xs P ys]",
   at_goal_variables
     [("items", "xs"), ("predicate", "P"), ("suffix", "ys")]
     (translated "source_dropWhile_append2")),
  ("zip_append1",
   translated "source_zip_append1"),
  ("zip_map_map[of f xs \"\\<lambda>x. x\" ys]",
   instantiated [("g", ``combin$I``)]
     (translated "source_zip_map_map")),
  ("zip_map_map[of \"\\<lambda>x. x\" xs f ys]",
   instantiated [("f", ``combin$I``)]
     (translated "source_zip_map_map")),
  ("zip_map1",
   translated "source_zip_map1"),
  ("zip_map2",
   translated "source_zip_map2"),
  ("rev_conj_cong",
   translated "source_rev_conj_cong"),
  ("update_zip",
   translated "source_update_zip"),
  ("set_zip_leftD",
   translated "source_set_zip_leftD"),
  ("set_zip_rightD",
   translated "source_set_zip_rightD"),
  ("zip_map_fst_snd",
   translated "source_zip_map_fst_snd"),
  ("zip_rev", symmetric (library "rich_list" "REVERSE_ZIP")),
  ("set_zip",
   translated "source_set_zip"),
  ("fold_Cons_rev",
   translated "source_fold_Cons_rev"),
  ("minus_set_fold",
   translated "source_minus_set_fold"),
  ("foldr_conv_fold",
   translated "source_foldr_conv_fold"),
  ("foldl_conv_fold",
   translated "source_foldl_conv_fold"),
  ("fold_cong",
   translated "source_fold_cong"),
  ("fold_map",
   translated "source_fold_map"),
  ("fold_filter",
   translated "source_fold_filter"),
  ("fold_append_concat_rev",
   translated "source_fold_append_concat_rev"),
  ("upt_rec",
   translated "source_upt_rec"),
  ("nth_eq_iff_index_eq",
   translated "source_nth_eq_iff_index_eq"),
  ("inj_on_nth",
   translated "source_inj_on_nth"),
  ("minus_list_set_def",
   translated "source_minus_list_set_def"),
  ("takeWhile_eq_Nil_iff",
   translated "source_takeWhile_eq_nil_iff"),
  ("dropWhile_eq_self_iff",
   translated "source_dropWhile_eq_self_iff"),
  ("set_Cons_def",
   translated "source_set_Cons_def"),
  ("strict_sorted_iff",
   translated "source_strict_sorted_iff"),
  ("upto_aux_def",
   translated "source_upto_aux_def"),
  ("upto_rec2",
   translated "source_upto_rec2"),
  ("distinct_adj_def",
   translated "source_distinct_adj_def"),
  ("successively_conv_nth",
   translated "source_successively_conv_nth"),
  ("successively_append_iff",
   translated "source_successively_append_iff"),
  ("distinct_adj_append_iff",
   translated "source_distinct_adj_append_iff"),
  ("extract_def",
   translated "source_extract_def"),
  ("minus_list_mset_def",
   translated "source_minus_list_mset_def"),
  ("rotate_def",
   translated "source_rotate_def"),
  ("nths_def",
   translated "source_nths_def"),
  ("sorted_insort_key[where f=\"\\<lambda>x. x\"]",
   instantiated [("function", ``combin$I``)]
     (translated "source_sorted_insort_key")),
  ("sorted_sort_key[where f=\"\\<lambda>x. x\"]",
   instantiated [("function", ``combin$I``)]
     (translated "source_sorted_sort_key")),
  ("sort_key_id_if_sorted",
   translated "source_sort_key_id_if_sorted"),
  ("sorted_distinct_set_unique",
   translated "source_sorted_all_distinct_unique"),
  ("sorted_map_same[of \"\\<lambda>x. x\"]",
   translated "source_sorted_same"),
  ("sorted_wrt01",
   translated "source_sorted_wrt_length01"),
  ("strict_sorted_equal",
   translated "source_strict_sorted_equal_unique"),
  ("sorted_replicate",
   translated "source_sorted_replicate"),
  ("sorted_sort_id",
   translated "source_sorted_sort_id"),
  ("insort_insert_key_def",
   translated "source_insort_insert_key_def"),
  ("insort_insert_key_triv[of \"\\<lambda>x. x\"]",
   instantiated [("function", ``combin$I``)]
     (translated "source_insort_insert_key_triv")),
  ("insort_insert_insort_key[of \"\\<lambda>x. x\"]",
   instantiated [("function", ``combin$I``)]
     (translated "source_insort_insert_insort_key")),
  ("set_insort_key",
   translated "source_set_insort_key"),
  ("sorted_insort_key",
   translated "source_sorted_insort_key"),
  ("sorted_insort_insert_key[of \"\\<lambda>x. x\"]",
   instantiated [("function", ``combin$I``)]
     (translated "source_sorted_insort_insert_key")),
  ("stable_sort_key_def",
   translated "source_stable_sort_key_def"),
  ("sort_key_stable",
   translated "source_sort_key_stable"),
  ("inj_on",
   translated "source_inj_on_def"),
  ("sorted_list_of_set.sorted_key_list_of_set_unique[symmetric]",
   translated "source_sorted_key_list_of_set_unique"),
  ("greaterThanAtMost_def",
   translated "source_greaterThanAtMost_def"),
  ("map_filter_def",
   translated "source_map_filter_def"),
  ("subseqs_powset",
   translated "source_subseqs_powset"),
  ("length_subseqs",
   translated "source_length_subseqs"),
  ("Id_on_def",
   translated "source_Id_on_def"),
  ("listrel1_def",
   translated "source_listrel1_def"),
  ("measures_def",
   translated "source_measures_def"),
  ("lex_def",
   translated "source_lex_def"),
  ("lenlex_def",
   translated "source_lenlex_def"),
  (* The two constants [lenlex_def] composes over. *)
  ("inv_image_def",
   library "relation" "inv_image_def"),
  ("lex_prod_def",
   library "pair" "LEX_DEF"),
  (* The three facts [asym_lenlex] is proved from; Isabelle's [asym] is
     an abbreviation over a set the translation writes out. *)
  ("asym_inv_image",
   translated "source_asym_inv_image"),
  ("asym_less_than",
   translated "source_asym_less_than"),
  ("asym_lex",
   translated "source_asym_lex"),
  ("lex_conv",
   translated "source_lex_conv"),
  ("lexord_partial_trans",
   translated "source_lexord_partial_trans"),
  ("lexord_irreflexive",
   translated "source_lexord_irreflexive"),
  ("lexord_def",
   translated "source_lexord_conv"),
  ("trans_list_step_def",
   translated "source_trans_list_step_def"),
  ("equiv_def",
   translated "source_equiv_def"),
  ("map_upd_upds_conv_if",
   translated "source_map_upd_upds_conv_if"),
  ("domI",
   translated "source_domI"),
  ("graph_eq_to_snd_dom",
   translated "source_graph_eq_to_snd_dom"),
  ("finite_dom_map_of",
   translated "source_finite_dom_map_of"),
  ("map_add_comm",
   translated "source_map_add_comm"),
  ("map_add_le_mapI",
   translated "source_map_add_le_mapI"),
  ("map_add_def",
   translated "source_map_add_def"),
  ("map_le_antisym",
   translated "source_map_le_antisym"),
  ("map_le_def",
   translated "source_map_le_def"),
  ("map_upds_def",
   translated "source_map_upds_def"),
  ("map_option_case",
   translated "source_map_option_case"),
  ("rel_option_iff",
   translated "source_rel_option_iff"),
  ("rel_option_unfold",
   translated "source_rel_option_unfold"),
  ("these_def",
   translated "source_these_def"),
  ("these_empty_eq",
   translated "source_these_empty_eq"),
  ("UNIV_option_conv",
   translated "source_UNIV_option_conv"),
  ("of_char_def",
   translated "source_of_char_def"),
  ("char_of_def",
   translated "source_char_of_def"),
  ("of_char_eqI",
   translated "source_of_char_eqI"),
  ("String.char_of_def",
   translated "source_char_of_def"),
  ("bit_cut_integer_def",
   translated "source_bit_cut_integer_def"),
  ("char_of_integer_def",
   translated "source_char_of_integer_def"),
  ("integer_of_char_def",
   translated "source_integer_of_char_def"),

  ("sorted_wrt_append",
   translated "source_sorted_wrt_append"),
  ("sorted_wrt_drop",
   translated "source_sorted_wrt_drop"),
  ("sorted_wrt_map",
   translated "source_sorted_wrt_map"),
  ("sorted_wrt_iff_nth_Suc_transp",
   translated "source_sorted_wrt_iff_nth_Suc_transp"),
  ("sorted_iff_nth_mono",
   translated "source_sorted_iff_nth_mono"),
  ("sorted_map_remove1[of \"\\<lambda>x. x\"]",
   instantiated [("function", ``combin$I``)]
     (translated "source_sorted_map_remove1")),
  ("set_nths",
   translated "source_set_nths"),
  ("rotate_drop_take",
   translated "source_rotate_drop_take"),
  (* Isabelle fills the schematics in the order they occur in the
     proposition, the premise first: [n], [xs], then the rotation count.
     Only the count is a term the citation brings; the other two name the
     goal's own variables and instantiate to themselves. *)
  ("nth_rotate[of n xs 1]",
   instantiated [("steps", ``1n``)] (translated "source_nth_rotate")),
  ("sorted_wrt_mono_rel[OF _ sorted_wrt_upt]",
   translated "source_sorted_wrt_mono_rel_upt"),
  ("sorted_wrt_mono_rel[OF _ sorted_wrt_upto]",
   translated "source_sorted_wrt_mono_rel_upto"),
  ("nth_transpose",
   translated "source_nth_transpose"),
  ("ran_distinct",
   translated "source_ran_distinct"),
  ("lessThan_Suc_atMost",
   translated "source_lessThan_Suc_atMost"),
  ("lessThan_atLeast0",
   translated "source_lessThan_atLeast0"),
  ("upt_Suc_append",
   translated "source_upt_suc_append"),
  ("distinct_adj_conv_nth",
   translated "source_distinct_adj_conv_nth"),
  ("distinct_adj_mapD",
   translated "source_distinct_adj_mapD"),
  ("distinct_adj_mapI",
   translated "source_distinct_adj_mapI"),
  (* src/HOL/List.thy:1036.  The rule a proof uses to build an equation
     between two appends out of a cut of one side. *)
  ("append_eq_appendI", translated "source_append_eq_appendI"),
  ("hd_def", translated "source_hd_def"),
  ("last_def", translated "source_last_def"),
  (* Isabelle's [refl] is an abbreviation for [refl_on UNIV]
     (src/HOL/Relation.thy:155), so a [refl] premise is a [refl_on]
     premise and this citation unfolds it.  The translation renders the
     abbreviation as HOL4's own [reflexive], which the translated
     definition says nothing about, so the citation resolves to both
     spellings of the one constant it unfolds in Isabelle. *)
  ("refl_on_def",
   bundle
     [translated "source_refl_on_def",
      library "relation" "reflexive_def"]),
  ("remove1_commute", translated "source_remove1_commute"),
  ("removeAll_commute", translated "source_removeAll_commute"),
  ("upto_rec1", translated "source_upto_rec1"),
  ("upto_split1", translated "source_upto_split1"),
  ("sorted_list_of_set_lessThan_Suc",
   translated "source_sorted_list_of_set_less_than_suc"),
  ("sorted_list_of_set_range",
   translated "source_sorted_list_of_set_range"),
  ("foldr_fold[of _ remove1]",
   instantiated [("operation", ``parityTranslation$source_remove1``)]
     (translated "source_foldr_fold")),
  ("foldr_fold[of _ removeAll]",
   instantiated [("operation", ``parityTranslation$source_removeAll``)]
     (translated "source_foldr_fold")),
  (* [OF i] and [OF j] discharge a premise with a label the enclosing
     Isar block bound, and the translated goal carries that label's
     content as a hypothesis, so the citation is the general theorem. *)
  ("nth_transpose[OF i]", translated "source_nth_transpose"),

  (* ---- Isabelle definitions the translated goal writes out in full ---- *)
  ("List.insert_def", inlined),
  ("Product_Type.product_def", translated "source_product_def"),
  ("Sigma_def",
   translated "source_Sigma_def"),
  ("graph_def", inlined),
  ("Uniq_def", inlined),
  ("apfst_def", inlined),
  ("apsnd_def", inlined),
  ("combine_options_def", inlined),
  ("dom_def", inlined),
  ("equal", inlined),
  ("fcomp_def", inlined),
  ("inter_list_set_def", inlined),
  ("map_comp_Some_iff", inlined),
  ("map_comp_def", inlined),
  ("map_prod_def", inlined),
  ("minus_list_set_eq_filter", inlined),
  ("override_on_def", inlined),
  ("prod.swap_def", inlined),
  ("product_def", translated "source_product_def"),
  ("ran_def", inlined),
  ("relcomp_unfold", inlined),
  ("restrict_map_def", inlined),
  ("scomp_def", inlined),
  ("scomp_unfold", inlined),
  ("simp_implies_def", inlined),

  (* ---- Rules a HOL4 engine or the ambient context supplies
         without an argument ---- *)
  ("classical", native),
  ("exI[where ?x = \"- u\" for u]", native),
  ("if_split_asm", native),
  ("if_splits", native),
  ("arg_cong2[where f=nths, OF refl]", native),
  ("nat_less_le", native),

  (* ---- Isabelle facts with no HOL4 counterpart ---- *)
  ("Pow_top", unrepresented),
  ("atLeastLessThan_iff[symmetric]", unrepresented),
  ("dom_map_option[of \"\\<lambda>_. g\" m]", unrepresented),
  ("drop_eq_nths", unrepresented),
  ("filter_equals_takeWhile_sorted_rev[OF sorted, of i]", unrepresented),
  ("inj_on_apfst[of f UNIV]", unrepresented),
  ("inj_on_apsnd[of f UNIV]", unrepresented),
  (* [lexn_conv] characterises [lexn r n], the length-indexed family
     Isabelle's [lex] is the union of, by a common prefix and a
     related pair at the position after it.  HOL4 has no [lexn], and
     no such characterisation of [LLEX]: [LLEX_EL_THM] reads the two
     lists at an index instead. *)
  ("lexn_conv", unrepresented),
  ("list.pred_transfer", unrepresented),
  ("nth_sorted_list_of_set_greaterThanLessThan[of n \"Suc j\" i]",
   unrepresented),
  ("nths_nths", unrepresented),
  ("partition_filter1[symmetric]", unrepresented),
  ("partition_filter2[symmetric]", unrepresented),
  ("bit_iff_odd_drop_bit", unrepresented),
  ("bit_simps", unrepresented),
  ("bit_take_bit_iff", unrepresented),
  ("distinct_zipI1", translated "source_distinct_zipI1"),
  ("div_mult2_numeral_eq", library "arithmetic" "DIV_DIV_DIV_MULT"),
  ("dropWhile_append3", library "list" "dropWhile_APPEND_NOT"),
  ("dropWhile_eq_Cons_conv",
   translated "source_dropWhile_eq_cons_conv"),
  ("dropWhile_eq_drop", library "list" "dropWhile_eq_DROP"),
  ("drop_bit_eq_div", unrepresented),
  ("drop_bit_of_nat", unrepresented),
  ("fold_insort_key.remove", unrepresented),
  ("greaterThanLessThan_eq", unrepresented),
  ("idem_if_sorted_distinct", unrepresented),
  ("listrel_subset", translated "source_LIST_REL_in_lists"),
  (* Isabelle's [Wellfounded.acc] is [relationTheory.WFP]; both lemmas
     are about the accessible part of its [lists] set, which the
     translation states pointwise.  The second is cited already
     resolved through [Cons_in_lists_iff], and the translation states
     it in that resolved form. *)
  ("lists_accD", translated "source_lists_accD"),
  ("lists_accI[THEN Cons_in_lists_iff[THEN iffD1, THEN conjunct1]]",
   translated "source_lists_accI"),
  ("possible_bit_def", unrepresented),
  (* HOL4 states the same relation by its graph -- a set of pairs whose
     projections are the two sides -- rather than by Isabelle's two
     bounded quantifiers.  It is still the definition of the constant
     the translated goal is stated with. *)
  ("rel_set_def", library "list" "SET_REL_def"),
  ("set_takeWhileD",
   translated "source_set_takeWhileD"),
  ("takeWhile_nth", library "list" "EL_takeWhile"),
  ("wf_iff_acc", library "relation" "WF_EQ_WFP"),

  (* ---- Names resolved to a HOL4 theorem ---- *)
  ("Int_def", library "pred_set" "INTER_DEF"),
  ("insert_def", library "pred_set" "INSERT_DEF"),
  ("bij_betw_def", library "pred_set" "BIJ_DEF"),
  ("le0", library "arithmetic" "ZERO_LESS_EQ"),
  ("nth_map[OF j]", library "list" "EL_MAP"),
  ("list_all2_Cons1", library "list" "LIST_REL_CONS1"),
  ("list_all2_Cons2", library "list" "LIST_REL_CONS2"),
  ("append_same_eq[of _ _ \"[]\"]", library "list" "APPEND_11"),
  ("set_take_subset", library "list" "LIST_TO_SET_TAKE"),
  ("dropWhile_eq_Nil_conv", library "list" "dropWhile_eq_nil"),
  ("split_option_all", library "option" "FORALL_OPTION"),
  (* The negation the method instantiates at is what turns the
     universal characterisation into the existential one; the general
     statement reaches the goal not at all, because splitting it at
     the goal's predicate is exactly the instantiation, and the
     predicate is the goal's own. *)
  ("split_option_all[of \"\\<lambda>x. \\<not> P x\"]",
   at_goal_terms [("P", ``\b_x:'a option. ~ v_P0 b_x``)]
     (library "option" "FORALL_OPTION")),
  ("list_eq_iff_nth_eq",
   library "list" "LIST_EQ_REWRITE"),
  (* [bijI] is an introduction rule; HOL4 has its content as the
     definition of [BIJ], an equivalence the claset cannot take as
     one. *)
  ("bijI",
   translated "source_bijI"),
  ("inj_rotate1",
   translated "source_rotate1_inj"),
  ("surj_rotate1",
   translated "source_rotate1_surj"),
  ("Diff_eq[symmetric]",
   translated "source_Diff_eq_symmetric"),
  ("Min_in",
   first_case (library "pred_set" "MIN_SET_LEM")),
  ("Nat.gr0_conv_Suc",
   translated "source_gr0_conv_Suc"),
  ("Option.is_none_def",
   library "option" "IS_NONE_DEF"),
  ("Option.these_eq",
   translated "source_these_def"),
  ("UNIV_char_of_nat",
   library "string" "UNIV_IMAGE_CHR_count_256"),
  ("ac_simps",
   bundle [library "arithmetic" "ADD_ASSOC",
           library "arithmetic" "ADD_COMM",
           library "arithmetic" "MULT_ASSOC",
           library "arithmetic" "MULT_COMM"]),
  ("add.assoc",
   library "arithmetic" "ADD_ASSOC"),
  ("all_set_conv_all_nth",
   library "list" "EVERY_EL"),
  ("append_eq_Cons_conv",
   library "list" "APPEND_EQ_CONS"),
  ("append_eq_append_conv2",
   library "list" "APPEND_EQ_APPEND"),
  ("bij_def",
   library "pred_set" "BIJ_DEF"),
  ("bot_fun_def",
   library "pred_set" "EMPTY_DEF"),
  ("butlast_append",
   translated "source_butlast_append"),
  ("butlast_conv_take",
   translated "source_front_by_take"),
  ("card_Pow",
   library "pred_set" "CARD_POW"),
  ("card_distinct",
   library "list" "CARD_LIST_TO_SET_ALL_DISTINCT"),
  ("card_image",
   library "pred_set" "CARD_IMAGE_INJ"),
  ("card_mono",
   library "pred_set" "CARD_SUBSET"),
  ("case_prod_eta",
   symmetric (library "pair" "LAMBDA_PROD")),
  ("case_prod_unfold",
   library "pair" "ELIM_UNCURRY"),
  ("comp_def",
   library "combin" "o_DEF"),
  ("count_list_0_iff",
   translated "source_count_list_zero"),
  ("curry_def",
   translated "source_curry_def"),
  ("distinct_card",
   library "list" "ALL_DISTINCT_CARD_LIST_TO_SET"),
  ("distinct_card[symmetric]",
   symmetric (library "list" "ALL_DISTINCT_CARD_LIST_TO_SET")),
  ("distinct_conv_nth",
   library "list" "EL_ALL_DISTINCT_EL_EQ"),
  ("distinct_map",
   bundle [library "list" "ALL_DISTINCT_MAP",
           library "list" "ALL_DISTINCT_MAP_INJ"]),
  ("drop_Cons'",
   library "list" "DROP_def"),
  ("drop_map",
   symmetric (library "list" "MAP_DROP")),
  ("drop_take",
   library "list" "DROP_TAKE"),
  ("eq_commute",
   library "bool" "EQ_SYM_EQ"),
  ("filter_map",
   library "rich_list" "FILTER_MAP"),
  ("finite_imageD",
   library "pred_set" "INJECTIVE_IMAGE_FINITE"),
  ("finite_trancl_ntranl",
   translated "source_finite_tc_ntrancl"),
  ("fun_Compl_def",
   library "pred_set" "COMPL_DEF"),
  ("fun_diff_def",
   library "pred_set" "DIFF_DEF"),
  ("fun_eq_iff",
   library "bool" "FUN_EQ_THM"),
  ("funpow_add",
   library "arithmetic" "FUNPOW_ADD"),
  ("funpow_swap1",
   library "arithmetic" "FUNPOW_COMM"),
  ("hd_conv_nth",
   symmetric (first_case (library "list" "EL"))),
  ("image_cong[of M N f g]",
   library "pred_set" "IMAGE_CONG"),
  ("image_eqI",
   library "pred_set" "IMAGE_IN"),
  ("image_eqI[where ?x = \"u - {a}\" for u]",
   library "pred_set" "IMAGE_IN"),
  ("image_image",
   library "pred_set" "IMAGE_IMAGE"),
  ("in_set_butlastD",
   translated "source_mem_front"),
  (* src/HOL/List.thy @ f7e02b7e: split_list is the implication and
     in_set_conv_decomp the equivalence.  Answering both citations with the
     translation of the implication measures every goal that names the
     equivalence without the direction that builds a member from a
     decomposition. *)
  ("in_set_conv_decomp",
   library "list" "MEM_SPLIT"),
  ("in_set_conv_nth",
   library "list" "MEM_EL"),
  ("indexed_from_eq_zip",
   translated "source_indexed_from_bridge"),
  ("inf_fun_def",
   library "pred_set" "INTER_DEF"),
  ("inj_Some",
   library "option" "SOME_11"),
  ("inj_eq",
   library "string" "ORD_11"),
  ("inj_of_char",
   library "string" "ORD_11"),
  ("irrefl_def",
   library "relation" "irreflexive_def"),
  ("is_none_def",
   library "option" "IS_NONE_DEF"),
  ("last_conv_nth",
   library "list" "LAST_EL"),
  ("le_Suc_eq",
   later_cases (library "arithmetic" "LE")),
  ("le_funE",
   translated "source_le_funE"),
  ("le_fun_def",
   library "pred_set" "SUBSET_DEF"),
  ("length_Suc_conv",
   library "rich_list" "LENGTH_CONS"),
  ("length_filter_conv_card",
   translated "source_length_filter_count"),
  ("length_filter_less",
   translated "source_length_filter_less"),
  ("length_remdups_card_conv",
   symmetric (library "list" "CARD_LIST_TO_SET_EQN")),
  ("less_eq_unit_def",
   translated "source_unit_le_def"),
  ("less_le",
   library "pred_set" "PSUBSET_DEF"),
  ("lexord_same_pref_iff",
   translated "source_lexord_same_prefix_iff"),
  ("lexordp_conv_lexordp_eq",
   translated "source_lexordp_conv_lexordp_eq"),
  ("lexordp_eq_antisym",
   translated "source_lexordp_eq_antisym"),
  ("lexordp_eq_refl",
   translated "source_lexordp_eq_refl"),
  ("lexordp_iff",
   translated "source_lexordp_iff"),
  ("lfp_unfold[OF monoI, of F]",
   first_case (library "fixedPoint" "lfp_fixedpoint")),
  (* src/HOL/List.thy @ f7e02b7e.  [native] would say the engine has the
     rule without being handed it, which holds of a simplification and
     not of a first-order step: that step sees the facts its method
     names and no ambient context at all, so a citation that is a
     theorem resolves to the theorem. *)
  ("list.distinct(1)",
   library "list" "NOT_CONS_NIL"),

  ("list.pred_set",
   library "list" "EVERY_MEM"),
  ("list.split",
   datatype_split ``:'a list``),
  ("list.splits",
   datatype_splits ``:'a list``),
  ("list_all2_append",
   library "list" "LIST_REL_APPEND_EQ"),
  ("list_all2_conv_all_nth",
   library "list" "LIST_REL_EL_EQN"),
  ("list_all2_eq",
   library "list" "LIST_REL_eq"),
  ("list_all2_iff",
   library "list" "EVERY2_EVERY"),
  ("list_all2_lengthD",
   library "list" "EVERY2_LENGTH"),
  ("list_all_iff",
   library "list" "EVERY_MEM"),
  ("list_ex1_iff",
   translated "source_list_ex1_def"),
  ("list_ex_iff",
   library "list" "EXISTS_MEM"),
  (* LIST_REL_rules stores the same general cons introduction as its
     second conjunct.  Extract it by kernel inference rather than citing
     LIST_REL_cons_I, which this HOL4 dependency does not export. *)
  ("listrel.intros",
   bundle [library "list" "LIST_REL_NIL",
           later_cases (library "list" "LIST_REL_rules")]),
  ("listrel1E",
   translated "source_listrel1E"),
  ("listrel_iff_nth",
   library "list" "LIST_REL_EL_EQN"),
  ("listrel_iff_zip",
   library "list" "LIST_REL_EVERY_ZIP"),
  ("listrel_refl_on",
   translated "source_LIST_REL_refl_on_preserve"),
  (* [of UNIV] fixes a carrier that occurs in neither side of the
     conclusion, and [OF refl_rtrancl] discharges the premise it
     leaves; neither is recoverable by matching, so the resolved
     instance is stated as its own theorem. *)
  ("listrel_refl_on[of UNIV, OF refl_rtrancl]",
   translated "source_LIST_REL_rtrancl_refl_on"),
  ("listrel_sym",
   translated "source_LIST_REL_symmetric"),
  ("listrel_trans",
   translated "source_LIST_REL_transitive"),
  ("map_nth_upt",
   library "rich_list" "MAP_COUNT_LIST"),
  ("map_of_eq_Some_iff",
   library "alist" "ALOOKUP_ALL_DISTINCT_MEM"),
  ("map_of_eq_Some_iff[symmetric]",
   symmetric (library "alist" "ALOOKUP_ALL_DISTINCT_MEM")),
  ("mono_def",
   library "fixedPoint" "monotone_def"),
  ("nth_Cons'",
   library "rich_list" "EL_CONS"),
  ("nth_append",
   library "list" "EL_APPEND_EQN"),
  ("nth_equalityI",
   library "list" "LIST_EQ"),
  ("nth_list_update",
   library "list" "EL_LUPDATE"),
  ("nths_Cons",
   translated "source_nths_recursion"),
  ("option.induct",
   hhf (library "option" "option_induction")),
  ("option.split",
   datatype_split ``:'a option``),
  ("option.split_asm",
   datatype_asm_split ``:'a option``),
  ("option.splits",
   datatype_splits ``:'a option``),
  (* With [pairwise] written out, [pairwiseI] is the reordering of a
     bounded quantifier that the engines do for themselves. *)
  ("pairwiseI", native),
  ("prod.split",
   datatype_split ``:'a # 'b``),
  ("prod_eq_iff",
   library "pair" "PAIR_FST_SND_EQ"),
  ("rel_fun_def",
   library "quotient" "FUN_REL"),
  ("removeAll_filter_not_eq",
   translated "source_removeAll_filter"),
  ("rev_filter",
   symmetric (library "list" "FILTER_REVERSE")),
  ("rev_map",
   symmetric (library "list" "MAP_REVERSE")),
  ("rev_nth",
   library "rich_list" "EL_REVERSE"),
  ("rotate_add",
   translated "source_rotate_add"),
  ("set_eq_iff",
   library "pred_set" "EXTENSION"),
  ("set_map[symmetric]",
   symmetric (library "list" "LIST_TO_SET_MAP")),
  ("set_replicate_conv_if",
   translated "source_set_replicate_conv_if"),
  ("sorted_iff_nth_mono_less",
   translated "source_sorted_iff_nth_mono_less"),
  ("sorted_wrt_iff_nth_less",
   translated "source_sorted_wrt_nth_less"),
  ("split_tupled_all",
   library "pair" "FORALL_PROD"),
  ("sup_fun_def",
   library "pred_set" "UNION_DEF"),
  ("sym_def",
   translated "source_sym_def"),
  ("take_Cons'",
   library "list" "TAKE_def"),
  ("take_bit_eq_mod",
   translated "source_take_bit_def"),
  ("take_map",
   symmetric (library "list" "MAP_TAKE")),
  ("the_elem_def",
   library "pred_set" "CHOICE_DEF"),
  ("top_fun_def",
   library "pred_set" "UNIV_DEF"),
  ("trans_def",
   library "relation" "transitive_def"),
  ("upt_conv_Cons",
   translated "source_upt_rec"),
  ("upto.simps",
   translated "source_upto_def"),
  ("wf_iff_acyclic_if_finite",
   translated "source_finite_wf_acyclic"),
  ("zip_append2",
   translated "source_zip_append2"),
]

(* Insert from right to left so the first entry wins on duplicate names. *)
val builders =
  List.foldr (fn (entry, index) => Symtab.update entry index)
    Symtab.empty table

fun lookup citation =
  Option.map (fn build => build ()) (Symtab.lookup builders citation)

fun resolve citation =
  case lookup citation of
      SOME resolution => resolution
    | NONE =>
        raise mk_HOL_ERR "benchNames" "resolve"
          ("no HOL4 theorem for the Isabelle name " ^ citation)

fun theorems citation =
  case resolve citation of
      Theorems found => found
    | _ => []

val names = map #1 table

(* [set_zip] reads any zip pointwise: its left side is the set of a zip
   of two pattern variables, and its right side leaves those two lists
   under an index, where no rule about a zip's own head reaches them.
   HOL4 rewrites the outermost redex first, so it fires above
   [zip_append] -- src/HOL/List.thy:2749, simp there and seeded here --
   which Isabelle applies first, the zip being the innermost redex.
   Installed at low priority the two apply in Isabelle's order. *)
val normalised_subjects = ["set_zip"]

fun normalised_subject citation = Lib.mem citation normalised_subjects

end
