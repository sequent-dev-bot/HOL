structure benchAmbient :> benchAmbient =
struct

open HolKernel boolSyntax

(* True of a theorem that states equations, which is what a definition
   contributes to a simpset.  A translated type's [TY_DEF] predicate is
   not one; it would sit in every rewrite set matching nothing.  The
   selftest reads the translation theory through this. *)
fun equational term =
  case strip_conj (snd (strip_forall term)) of
      [single] => is_eq single
    | conjuncts => List.all equational conjuncts

(* One theorem per mined constant.  Reading [DB.definitions] instead
   would miss four: HOL4 keeps the equations of a definition made by
   well-founded recursion in the theorem class, so [source_alookup],
   [source_lexordp], [source_lexordp_eq] and [source_upto] never appear
   there.  The theory read is the check rather than the construction --
   the selftest requires every definition it records to have a mined
   row -- and a row naming nothing raises here, at load. *)
val definitions =
  map
    (fn (name, _, _) =>
      {name = name, theorem = DB.fetch "parityTranslation" name})
    benchIsabelleAmbient.introductions

(* The one lemma in the ambient set.  Isabelle's [sorted] *is*
   [sorted_wrt (<=)], so every fact its simpset carries about a sorted
   list -- [sorted_upt] and the rest -- applies to the [sorted_wrt]
   reading without anyone naming it.  HOL4 states those facts about its
   own adjacent SORTED, and the translation's [source_sorted] unfolds
   to [source_sorted_wrt], whose definition takes a nil or a cons apart
   and says nothing about a list variable; without the correspondence
   the predicate is opaque and the ambient facts cannot reach it.  The
   bridge is conditional on transitivity, which is what the source
   linorder supplies, so it hands a goal nothing that Isabelle's
   [sorted] did not already have. *)
val sorted_wrt_correspondence =
  {name = "parityTranslation$source_sorted_wrt_bridge",
   theorem = DB.fetch "parityTranslation" "source_sorted_wrt_bridge"}

(* Results Isabelle declares simp about a constant the translation
   carries.  Its ambient context is its simpset and so has them; ours
   is the translation's definitions, so a method whose simp step leans
   on one reaches a residual that is the declared result itself, stated
   and out of reach.  Every entry cites the declaration it transplants.
   An entry may be a corpus goal's statement -- two Isabelle facts can
   translate onto one HOL4 theorem, and [map_add_find_right] is
   map_L887 once [map_le] is unfolded -- and the measurement then
   withholds it on that one goal, exactly as it withholds a citation
   that states its goal.  The list is the source's own ambient context
   and never a goal's answer.

   src/HOL/List.thy @ f7e02b7e declares [fold_append] simp, and
   List.thy:3424 [foldl_append] is reached through it.  The same file
   declares [takeWhile_append1] and [takeWhile_append2] simp, which is
   how a source proof that pushes a takeWhile across an append never
   names them: List.thy:2545 [takeWhile_append] states the two together
   and still cites them, and List.thy:4637 [extract_Some_iff] reaches
   one after unfolding [extract].

   Relation.thy:1572 declares [Image_singleton_iff] [iff]: the simpset
   takes a relational image of a singleton apart, though [Image] itself
   is a plain definition and stays folded.  String.thy:64 [char_of_char]
   and String.thy:91 [of_char_of] are the roundtrip pair Isabelle
   declares simp about [char_of], whose own definition it withholds;
   neither line was mined into the corpus, so transplanting them hands
   no goal its own statement.

   List.thy:2789 declares [nth_zip] simp, which is how a source proof
   that indexes into a zip never names it; HOL4's [EL_ZIP] asks for
   equal lengths instead of the two bounds the truncating ZIP needs,
   so the translation states Isabelle's form.

   List.thy:3788 declares [distinct_upt] simp, List.thy:3478
   [take_upt] and List.thy:3485 [drop_upt], which is how a source proof
   that asks whether an interval repeats, or cuts one at a length,
   never names them.  HOL4's list library answers the first with an
   injectivity condition and carries neither of the other two, so the
   three transplants below are what its interval vocabulary lacks
   against Isabelle's.

   Map.thy:91-92 states [map_of]'s clauses as equations between
   functions, and Map.thy declares [map_add_empty] (:346),
   [map_add_upd] (:369) and [map_of_append] (:378) simp.  That is the
   whole context a source proof about a list update runs in: it splits
   the association list at the append, reads the last pair as an
   update, and drops the empty map, naming none of them.  HOL4's
   recursion takes the key as well, so the translation's own clauses
   are the pointwise reading and the unapplied map the three rewrites
   need is never exposed; the two clauses are restated here in the
   source's form.

   Map.thy declares [map_add_find_right], [map_add_assoc],
   [map_le_refl] and [map_le_map_add] simp and [map_add_None] iff,
   about [map_add] and [map_le], whose definitions it withholds: a
   method that never names [map_add_def] still reads a value out of the
   right-hand map, reassociates two of them, and settles the order
   between a map and a sum it is part of.

   Fun.thy declares [fun_upd_apply] (:872) and [fun_upd_upd] (:883)
   simp and [fun_upd_triv] (:869) iff, about [fun_upd], whose
   definition it withholds.  They are what a source proof about an
   update runs on: the first takes the constant apart wherever the
   proof reaches a point, and the other two are the only two shapes
   Isabelle collapses without one.

   List.thy introduces [lists] as an inductive set (:6857) and leaves
   its definition folded, declaring instead [lists.Nil] (:6861) and
   [lists_Int_eq] (:6890), [lists_empty] (:6922) and [lists_UNIV]
   (:6925) simp.  Reading the definition as ambient instead -- which is
   what a set whose introduction rules carry simp otherwise means -- is
   generous in one direction and disarming in the other: Isabelle's simp
   takes a nil or a cons apart and never touches a [lists] at a list
   variable, while unfolding the definition rewrites every occurrence
   and leaves the classical rules below, all stated about the constant,
   matching nothing.  [list_L6972] is the goal that separates them --
   [lists A SUBSET lists B] from [A SUBSET B] is settled by the three
   declarations and not by any rewrite.

   List.thy:7713 introduces [measures] by a plain definition and
   declares its two recursion clauses, :7719 [in_measures], simp.  The
   translation introduces it the same way, so the clauses are a
   consequence here too, and that transplant is the whole simpset a
   source proof about a list of measure functions runs in.  It unfolds
   to Isabelle's equal-length [lex], whose own ambient facts -- :7227
   and :7230 [iff], :7233 and :7295 [simp] -- have no HOL4 constant to
   sit on: LLEX is the prefix order and SHORTLEX compares lengths
   first, so neither one's declarations reach two lists already known
   to be the same length.

   List.thy:7064 introduces [lenlex] by a plain definition of the same
   shape -- an [inv_image] of the pair product of [less_than] and that
   same [lex] -- and declares :7244 [Nil_lenlex_iff1] and :7245
   [Nil_lenlex_iff2] simp.  The pair product carries an ambient fact
   of its own, Wellfounded.thy:1318 [asym_lex_prod], which is what
   takes the asymmetry of the two components across it.  HOL4 has the
   product as [LEX] and the inverse image as [inv_image], so the rules
   about those two are seeded; [asym] is Isabelle's abbreviation over
   a set the translation writes out, and has no HOL4 constant to sit
   on.

   The last row is not a declaration but an equation: List.thy:315
   states [shuffles xs [] = {xs}] at a list variable, and HOL4 takes
   the definition's rows apart to make them disjoint, so the equation
   its ambient definition keeps is the cons case.  A goal spelling the
   variable case is one the source's simpset rewrites and the
   translation's would not, and the row puts it back. *)
val declared_results =
  let
    fun named name =
      {name = "parityTranslation$" ^ name,
       theorem = DB.fetch "parityTranslation" name}
  in
    map named
      ["source_fun_upd_apply",
       "source_fun_upd_upd",
       "source_fun_upd_triv",
       "source_fold_append",
       "source_takeWhile_append1",
       "source_takeWhile_append2",
       "source_nth_zip",
       "source_distinct_upt",
       "source_take_upt",
       "source_drop_upt",
       "source_map_of_Nil",
       "source_map_add_empty",
       "source_map_of_Cons",
       "source_map_of_append",
       "source_map_add_upd",
       "source_map_add_find_right",
       "source_map_add_assoc",
       "source_map_add_None",
       "source_map_le_refl",
       "source_map_le_map_add",
       "source_mem_Sigma_iff",
       "source_rel_image_singleton",
       "source_char_roundtrip",
       "source_code_roundtrip",
       "source_lists_Nil",
       "source_lists_Int_eq",
       "source_lists_empty",
       "source_lists_UNIV",
       "source_Nil_notin_lex",
       "source_Nil_lenlex_iff1",
       "source_Nil_lenlex_iff2",
       "source_Nil2_notin_lex",
       "source_Cons_in_lex",
       "source_lexl_not_refl",
       "source_asym_lex_prod",
       "source_not_Nil_listrel1",
       "source_not_listrel1_Nil",
       "source_Cons_listrel1_Cons",
       "source_in_measures",
       "source_shuffles_nil_right"]
  end

(* An alias definition is ambient, so by the time one of the lemmas
   above is tried the goal no longer spells the alias: [source_of_char]
   is gone and ORD stands where it was.  A lemma still stated on the
   alias then matches nothing -- [source_code_roundtrip] is the ambient
   reading of Isabelle's [of_char_of], and the residual it has to close
   spells the same term with ORD.  Reading the lemmas through the
   aliases states them in the vocabulary the ambient set leaves, and
   makes which of the two rules reaches a term first stop mattering.
   Only the aliases are unfolded: they rename a constant argument for
   argument, so the reading is the same statement. *)
val alias_definitions =
  List.filter
    (fn {name, ...} : benchLib.named_thm =>
      List.exists
        (fn (entry, introduction, _) =>
          entry = name andalso introduction = benchIsabelleAmbient.Alias)
        benchIsabelleAmbient.introductions)
    definitions

fun through_aliases ({name, theorem} : benchLib.named_thm) =
  {name = name,
   theorem =
     Rewrite.PURE_REWRITE_RULE (map #theorem alias_definitions) theorem}

val ambient_lemmas =
  map through_aliases (sorted_wrt_correspondence :: declared_results)

(* Isabelle's simpset carries a [fun]'s equations and not a plain
   [definition]'s, so the ambient set is the translation's definitions
   cut to that line.  [benchIsabelleAmbient] draws it one constant at a
   time against the Isabelle source, and raises on a definition it does
   not cover: a definition added to the translation is measured only
   once someone has read how Isabelle introduces it. *)
val ambient_definitions =
  List.filter
    (fn {name, ...} : benchLib.named_thm =>
      benchIsabelleAmbient.is_ambient name)
    definitions

(* The claset half.  Isabelle declares these about a constant whose
   definition it withholds, with a classical attribute rather than
   [simp], and its [blast], [safe], [clarify], [auto] and [force] read
   them without naming them.  A rewrite cannot stand in for one: the
   rules above match a map sum under [= NONE] or build one from a
   value, and none of them takes a sum apart under [= SOME x], which is
   the residual Isabelle's [dest!] rule closes.  As with the rewrites,
   a rule that states a corpus goal is withheld on that goal.

   An entry carries the class Isabelle gives it, [!] safe and plain
   unsafe, with the one exception below.  The two directions were
   measured and they disagree, so neither reading can be applied
   blanket.  A safe elimination whose major premise is entirely
   schematic is applied at every tableau node, so it meets the
   undetermined literals a witness-guessing branch leaves behind: the
   seed clasets measured [set_L1610_Pow_Compl] at 88 tableau branches
   with such a rule unsafe and 3638 and past budget with it [sdest]
   (measured 2026-09-09; that goal has since become a shortfall of its
   own, over budget in either class, so the contrast is the record of
   what the class cost and not a goal to re-run for it), and
   [map_add_SomeD] is that shape.  It costs nothing there --
   [map_L611] closes in 0.107s safe and 0.100s unsafe -- so it is
   carried unsafe against its [dest!].  The Sigma rules run the other
   way: safe, they close [split_paired_Ball_Sigma], its [Bex] twin,
   [Times_subset_cancel2] and [SigmaE]; unsafe, the same rules did not
   return in twenty minutes on the first of those.  Their major
   premise names the constant, so a tableau node meets them only where
   a Sigma is on the branch. *)
val declared_rules =
  let
    fun named constructor safety name =
      constructor
        (safety,
         through_aliases
           {name = "parityTranslation$" ^ name,
            theorem = DB.fetch "parityTranslation" name})
  in
    [(* src/HOL/Map.thy:359 [map_add_SomeD], declared [dest!]. *)
     named benchLib.DestAdd benchLib.UnsafeRule "source_map_add_SomeD",
     (* src/HOL/Product_Type.thy:1027 [SigmaI], declared [intro!]. *)
     named benchLib.IntroAdd benchLib.SafeRule "source_SigmaI",
     (* src/HOL/Product_Type.thy:1030 [SigmaE], declared [elim!]. *)
     named benchLib.ElimAdd benchLib.SafeRule "source_SigmaE",
     (* src/HOL/List.thy:6861 [lists.Nil], declared [intro!] as well as
        simp. *)
     named benchLib.IntroAdd benchLib.SafeRule "source_lists_Nil",
     (* src/HOL/List.thy:6909 [in_listsD], declared [dest!]. *)
     named benchLib.DestAdd benchLib.SafeRule "source_in_listsD",
     (* src/HOL/List.thy:6914 [in_listsI], declared [intro!]. *)
     named benchLib.IntroAdd benchLib.SafeRule "source_in_listsI",
     (* src/HOL/List.thy:7083 [wf_lex], declared [intro!].  HOL4 has no
        equal-length lexicographic order to state it about, so unlike
        [wf_inv_image] and [wf_less_than] -- seeded on WF_inv_image and
        WF_LESS -- this one has nowhere to sit but the translation. *)
     named benchLib.IntroAdd benchLib.SafeRule "source_wf_lex",
     (* src/HOL/List.thy:7197 [wf_lenlex], declared [intro!], and
        :7223 [lenlex_transI], declared [intro].  [lenlex] composes in
        the source as well, so neither rule has a HOL4 carrier once it
        is stated that way. *)
     named benchLib.IntroAdd benchLib.SafeRule "source_wf_lenlex",
     named benchLib.IntroAdd benchLib.UnsafeRule "source_lenlex_transI",
     (* src/HOL/List.thy:7773 [Cons_listrel1E1] and :7780
        [Cons_listrel1E2], both declared [elim!]; :7834
        [Cons_acc_listrel1I], declared [intro!]. *)
     named benchLib.ElimAdd benchLib.SafeRule "source_Cons_listrel1E1",
     named benchLib.ElimAdd benchLib.SafeRule "source_Cons_listrel1E2",
     named benchLib.IntroAdd benchLib.SafeRule
       "source_Cons_acc_listrel1I"]
  end

(* Isabelle's [iff] declares one theorem into both its simpset and its
   claset, and the rules the claset gets are derived from the
   equivalence rather than stated.  An entry declared that way is
   carried as an [iff] and reaches a method reading either half; an
   entry declared [simp] is a rewrite and reaches only the simpset
   half.  Carrying an [iff] as a rewrite alone would leave Isabelle's
   [blast], [safe] and [clarify] without a declaration they had --
   [mem_Sigma_iff] is what closes the [Sigma] distributivity goals
   there, and every one of them is proved [by blast]. *)
val iff_declarations =
  ["parityTranslation$source_map_add_None",
   "parityTranslation$source_rel_image_singleton",
   "parityTranslation$source_mem_Sigma_iff",
   (* src/HOL/List.thy:6898 [append_in_lists_conv], declared [iff]. *)
   "parityTranslation$source_append_in_lists_conv",
   (* src/HOL/List.thy:6892 [Cons_in_lists_iff] is declared simp alone,
      and the claset halves the equivalence yields here are Isabelle's
      own two declarations about the same shape: :6862 [lists.Cons]
      [intro!] is its right-to-left reading and :6864 [listsE] [elim!]
      its left-to-right one.  Carrying it as an [iff] is those three
      declarations together and not more than Isabelle has. *)
   "parityTranslation$source_Cons_in_lists_iff",
   (* src/HOL/List.thy:7227 [Nil_notin_lex] and :7230 [Nil2_notin_lex],
      both declared [iff]. *)
   "parityTranslation$source_Nil_notin_lex",
   "parityTranslation$source_Nil2_notin_lex",
   (* src/HOL/List.thy:7750 [not_Nil_listrel1], :7753
      [not_listrel1_Nil] and :7756 [Cons_listrel1_Cons], all three
      declared [iff]. *)
   "parityTranslation$source_not_Nil_listrel1",
   "parityTranslation$source_not_listrel1_Nil",
   "parityTranslation$source_Cons_listrel1_Cons"]

fun ambient_argument (named as {name, ...} : benchLib.named_thm) =
  if List.exists (fn entry => entry = name) iff_declarations then
    benchLib.IffAdd named
  else benchLib.RewriteAdd named

val arguments =
  map ambient_argument (ambient_definitions @ ambient_lemmas) @
  declared_rules

val _ = benchLib.set_ambient_citations arguments

(* Where Isabelle declares each result and rule the ambient set
   transplants: the line whose attribute puts it in the default simpset
   or claset, which is also the line from which it is in scope.  A
   definition's line [benchIsabelleAmbient] records already, and an
   argument the tables do not cover raises there. *)
val declaration_sites =
  [("parityTranslation$source_sorted_wrt_bridge",
    "src/HOL/List.thy:409"),
   ("parityTranslation$source_fun_upd_apply", "src/HOL/Fun.thy:872"),
   ("parityTranslation$source_fun_upd_upd", "src/HOL/Fun.thy:883"),
   ("parityTranslation$source_fun_upd_triv", "src/HOL/Fun.thy:869"),
   ("parityTranslation$source_fold_append", "src/HOL/List.thy:3231"),
   ("parityTranslation$source_takeWhile_append1",
    "src/HOL/List.thy:2500"),
   ("parityTranslation$source_takeWhile_append2",
    "src/HOL/List.thy:2504"),
   ("parityTranslation$source_nth_zip", "src/HOL/List.thy:2789"),
   ("parityTranslation$source_distinct_upt", "src/HOL/List.thy:3788"),
   ("parityTranslation$source_take_upt", "src/HOL/List.thy:3478"),
   ("parityTranslation$source_drop_upt", "src/HOL/List.thy:3485"),
   ("parityTranslation$source_map_of_Nil", "src/HOL/Map.thy:91"),
   ("parityTranslation$source_map_add_empty", "src/HOL/Map.thy:346"),
   ("parityTranslation$source_map_of_Cons", "src/HOL/Map.thy:92"),
   ("parityTranslation$source_map_of_append", "src/HOL/Map.thy:378"),
   ("parityTranslation$source_map_add_upd", "src/HOL/Map.thy:369"),
   ("parityTranslation$source_map_add_find_right",
    "src/HOL/Map.thy:363"),
   ("parityTranslation$source_map_add_assoc", "src/HOL/Map.thy:352"),
   ("parityTranslation$source_map_add_None", "src/HOL/Map.thy:366"),
   ("parityTranslation$source_map_le_refl", "src/HOL/Map.thy:846"),
   ("parityTranslation$source_map_le_map_add", "src/HOL/Map.thy:856"),
   ("parityTranslation$source_mem_Sigma_iff",
    "src/HOL/Product_Type.thy:1069"),
   ("parityTranslation$source_rel_image_singleton",
    "src/HOL/Relation.thy:1572"),
   ("parityTranslation$source_char_roundtrip", "src/HOL/String.thy:64"),
   ("parityTranslation$source_code_roundtrip", "src/HOL/String.thy:91"),
   ("parityTranslation$source_map_add_SomeD", "src/HOL/Map.thy:359"),
   ("parityTranslation$source_SigmaI",
    "src/HOL/Product_Type.thy:1027"),
   ("parityTranslation$source_SigmaE",
    "src/HOL/Product_Type.thy:1030"),
   ("parityTranslation$source_lists_Nil", "src/HOL/List.thy:6861"),
   ("parityTranslation$source_lists_Int_eq", "src/HOL/List.thy:6890"),
   ("parityTranslation$source_Cons_in_lists_iff",
    "src/HOL/List.thy:6892"),
   ("parityTranslation$source_append_in_lists_conv",
    "src/HOL/List.thy:6898"),
   ("parityTranslation$source_in_listsD", "src/HOL/List.thy:6909"),
   ("parityTranslation$source_in_listsI", "src/HOL/List.thy:6914"),
   ("parityTranslation$source_lists_empty", "src/HOL/List.thy:6922"),
   ("parityTranslation$source_lists_UNIV", "src/HOL/List.thy:6925"),
   ("parityTranslation$source_Nil_notin_lex", "src/HOL/List.thy:7227"),
   ("parityTranslation$source_Nil2_notin_lex", "src/HOL/List.thy:7230"),
   ("parityTranslation$source_Cons_in_lex", "src/HOL/List.thy:7233"),
   ("parityTranslation$source_lexl_not_refl", "src/HOL/List.thy:7295"),
   ("parityTranslation$source_in_measures", "src/HOL/List.thy:7719"),
   ("parityTranslation$source_wf_lex", "src/HOL/List.thy:7083"),
   ("parityTranslation$source_wf_lenlex", "src/HOL/List.thy:7197"),
   ("parityTranslation$source_lenlex_transI", "src/HOL/List.thy:7223"),
   ("parityTranslation$source_Nil_lenlex_iff1",
    "src/HOL/List.thy:7244"),
   ("parityTranslation$source_Nil_lenlex_iff2",
    "src/HOL/List.thy:7245"),
   ("parityTranslation$source_asym_lex_prod",
    "src/HOL/Wellfounded.thy:1318"),
   ("parityTranslation$source_not_Nil_listrel1",
    "src/HOL/List.thy:7750"),
   ("parityTranslation$source_not_listrel1_Nil",
    "src/HOL/List.thy:7753"),
   ("parityTranslation$source_Cons_listrel1_Cons",
    "src/HOL/List.thy:7756"),
   ("parityTranslation$source_Cons_listrel1E1",
    "src/HOL/List.thy:7773"),
   ("parityTranslation$source_Cons_listrel1E2",
    "src/HOL/List.thy:7780"),
   ("parityTranslation$source_Cons_acc_listrel1I",
    "src/HOL/List.thy:7834"),
   ("parityTranslation$source_shuffles_nil_right",
    "src/HOL/List.thy:318")]

fun declaration_site name =
  case List.find (fn (entry, _) => entry = name) declaration_sites of
      SOME (_, where_) => where_
    | NONE => benchIsabelleAmbient.location name

val argument_sites =
  map (fn argument =>
    (argument, benchIsabelleAmbient.parse_location
      (declaration_site (benchLib.argument_name argument)))) arguments

(* Cross-file scope stays fixed as the corpus moves through a file.
   Keep same-file declarations in order for the per-goal scope check. *)
val arguments_in_file =
  memoUtil.keyed_memo
    (fn (file : string, _) => fn (previous, _) => file = previous)
    (fn site as (file, _) =>
      let
        fun eligible (argument, declared as (declared_file, _)) =
          if declared_file = file then SOME (argument, SOME declared)
          else if
            benchIsabelleAmbient.in_scope_at {declared = declared, goal = site}
          then SOME (argument, NONE)
          else NONE
      in
        List.mapPartial eligible argument_sites
      end)

(* Isabelle's ambient context is theory-ordered: a goal reads what its
   own theory has declared above it and what its ancestors declare, not
   what the library declares somewhere.  This is the cut, and it is the
   set the measurement uses.  [goal] is the goal's own Isabelle line,
   which is mined provenance and not anything about the goal's
   statement, so the context still cannot be tuned against one goal. *)
fun arguments_at goal =
  let
    val site = benchIsabelleAmbient.parse_location goal
    fun before_goal (argument, NONE) = SOME argument
      | before_goal (argument, SOME declared) =
          if benchIsabelleAmbient.in_scope_at {declared = declared, goal = site}
          then SOME argument else NONE
  in
    List.mapPartial before_goal (arguments_in_file site)
  end

(* A definition unfolds one constant; a characterisation relates
   several.  [define_new_type_bijections] yields a single theorem whose
   clauses head on two different constants -- one of them stating
   [source_literal_valid r <=> source_literal_explode (source_literal_abs
   r) = r] -- and reading that as a definition would make every fact one
   ambient rewrite away from a goal count as stating it.  Clauses that
   all define the same head are what a wrapper and a [fun] definition
   look like, and the wrapper is what the comparison has to see
   through. *)
fun clausal term =
  let
    fun head clause =
      case Lib.total dest_eq (snd (strip_forall clause)) of
          NONE => NONE
        | SOME (left, _) =>
            Lib.total (#1 o dest_const) (fst (strip_comb left))
    val heads = map head (strip_conj (snd (strip_forall term)))
  in
    case heads of
        [] => false
      | first :: rest =>
          Option.isSome first andalso List.all (fn other => other = first) rest
  end

val wrapper_definitions =
  List.filter (clausal o concl o #theorem) definitions

(* The comparison that withholds a rule stating the goal reads these,
   and it lives in a module built below the translation theory.  Every
   definition is filtered, not just the ambient ones: a rule states a
   goal, or does not, whether or not the goal's context could have
   unfolded its way there. *)
val _ = benchLib.set_definitional_context (map #theorem wrapper_definitions)

(* The bridge is also the correspondence a recipe's own rules are
   offered across: it is what rewrites a goal out of [source_sorted_wrt]
   and into SORTED, so a cited rule stated on the translated predicate
   has to be available on the other side too.

   The alias definitions cross for the same reason.  They are ambient,
   so a goal spelling [source_lexord] spells LLEX by the time a rule is
   tried; the lemmas above are read through them where they are
   declared, and a citation the source method names is read nowhere.
   [list_L7508_lexord_trans] cites [lexord_partial_trans] as an intro
   rule and its residual is stated on LLEX, which that rule does not
   mention; across the correspondence the goal closes in 0.065s.
   Crossed rather than read through, because the ambient context is cut
   to what was in scope at the goal's own line: a goal above the
   definition does not carry it and still spells the alias. *)
val _ =
  benchLib.set_correspondences
    (#theorem sorted_wrt_correspondence ::
     map #theorem alias_definitions)

end
