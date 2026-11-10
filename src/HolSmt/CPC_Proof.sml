(* Proof reconstruction for cvc5 CPC: proof representation and rule registry. *)

structure CPC_Proof =
struct

  datatype rule_namespace = ProofRule | RareRewrite

  datatype proof_version_support = AllCVCVersions
                                 | CVCVersionPrefixes of string list
                                 | CVCVersions of string list

  type proof_rule = {
    name : string,
    namespace : rule_namespace,
    version_support : proof_version_support,
    replay_handler : string
  }

  (* The frozen CPC vocabulary was captured and replayed with cvc5 1.3.4.
     These are the versions whose dialect was actually measured; a patch
     release does not change it, so the whole 1.3 series counts as tested.
     Another version is admitted here once its matrix has been recaptured and
     replayed.  Until then it is not rejected: `resolve_version` warns and
     replays it under the nearest measured dialect. *)
  val supported_cvc_versions = ["1.3.4"]

  (* CPC names each skolem with [@quantifiers_skolemize q i], while its
     skolemize proof rule exposes all witnesses at once.  Construct both from
     the same kernel operation so their choice terms cannot drift.  The CPC
     contract starts specifically from a source [~(forall (x1 ... xn) body)]
     block, with n > 0.  HOL erases whether adjacent foralls came from that
     block or a nested source forall, so callers supply the recorded immediate
     block size.  Push NOT_FORALL and select through exactly that boundary.
     Neither a direct existential nor a binder inside [body] belongs to it. *)
  fun cpc_skolem_witnesses immediate_count theorem =
    let
      val ERR = Feedback.mk_HOL_ERR "CPC_Proof" "cpc_skolem_witnesses"
      val _ = if immediate_count > 0 then ()
        else raise ERR "expected a positive immediate FORALL binder count"
      val conclusion = Thm.concl theorem
      val quantified =
        if boolSyntax.is_neg conclusion then boolSyntax.dest_neg conclusion
        else raise ERR
          "expected ~FORALL theorem conclusion with at least one binder"
      fun immediate_variables 0 _ variables = List.rev variables
        | immediate_variables remaining tm variables =
            (case Lib.total boolSyntax.dest_forall tm of
               SOME (variable, body) =>
                 immediate_variables (remaining - 1) body
                   (variable :: variables)
             | NONE => raise ERR
                 "immediate FORALL binder count exceeds theorem binder spine")
      val variables = immediate_variables immediate_count quantified []
      fun push_not_foralls [] tm = Conv.ALL_CONV tm
        | push_not_foralls (_ :: rest) tm =
            if boolSyntax.is_neg tm andalso
               boolSyntax.is_forall (boolSyntax.dest_neg tm)
            then
              Conv.THENC
                (Conv.HO_REWR_CONV boolTheory.NOT_FORALL_THM,
                 Conv.BINDER_CONV (push_not_foralls rest)) tm
            else raise ERR "malformed leading ~FORALL binder spine"
      val prenexed = Conv.CONV_RULE
        (push_not_foralls variables) theorem
      fun select_exact [] thm witnesses =
            {theorem = thm, witnesses = List.rev witnesses}
        | select_exact (_ :: rest) thm witnesses =
            (case Lib.total boolSyntax.dest_exists (Thm.concl thm) of
               SOME (variable, body) =>
                 select_exact rest (Drule.SELECT_RULE thm)
                   (boolSyntax.mk_select (variable, body) :: witnesses)
             | NONE => raise ERR "malformed generated existential spine")
    in
      select_exact variables prenexed []
    end

  fun mk_rule namespace (name, replay_handler) : proof_rule = {
    name = name,
    namespace = namespace,
    version_support = CVCVersions supported_cvc_versions,
    replay_handler = replay_handler
  }

  datatype rare_string_recipe =
      ContainsConcatFind
    | ContainsConcatFindContra
    | ContainsLeqLenEq
    | ContainsEmpty
    | ContainsChar
    | LenReplaceInv
    | LenReplaceAllInv
    | LenUpdateInv
    | LenSubstrInRange
    | LenConcatRec
    | LenEqZeroConcatRec
    | LenEqZeroBase
    | PrefixElim
    | PrefixEq
    | PrefixOne

  datatype rare_source_aggregate =
      RareSourceSeqConcat
    | RareSourceRegexConcat
    | RareSourceRegexUnion
    | RareSourceRegexInter

  datatype rare_source_arg_kind =
      RareSourceTerm
    | RareSourceList of rare_source_aggregate
    | RareSourceIndex

  datatype rare_source_type =
      RareSourceSeq
    | RareSourceString
    | RareSourceRegex
    | RareSourceInt
    | RareSourceElement

  type rare_source_recipe = {
    formals :
      (string * rare_source_arg_kind * rare_source_type) list,
    premises : string list,
    target : string
  }

  fun rare_string_recipe_name recipe =
    case recipe of
      ContainsConcatFind => "str-contains-concat-find"
    | ContainsConcatFindContra => "str-contains-concat-find-contra"
    | ContainsLeqLenEq => "str-contains-leq-len-eq"
    | ContainsEmpty => "str-contains-emp"
    | ContainsChar => "str-contains-char"
    | LenReplaceInv => "str-len-replace-inv"
    | LenReplaceAllInv => "str-len-replace-all-inv"
    | LenUpdateInv => "str-len-update-inv"
    | LenSubstrInRange => "str-len-substr-in-range"
    | LenConcatRec => "str-len-concat-rec"
    | LenEqZeroConcatRec => "str-len-eq-zero-concat-rec"
    | LenEqZeroBase => "str-len-eq-zero-base"
    | PrefixElim => "str-prefixof-elim"
    | PrefixEq => "str-prefixof-eq"
    | PrefixOne => "str-prefixof-one"

  datatype rare_replay_kind =
      RareArgumentRewrite
    | RareRecursiveArgumentRewrite
    | RareStringRecipe of rare_string_recipe
    | RareSourceRecipe of rare_source_recipe
    | RareSourceUnsupported of rare_source_recipe * string
    | RareContainsRefl
    | RareContainsSplitChar
    | RareUnsupported of string

  datatype rare_inventory_family =
      RareContains
    | RareLength
    | RarePrefix
    | RareArray
    | RareReplace
    | RareIndexof
    | RareRegexStar
    | RareConcatEquality
    | RareSubstringSuffix
    | RareConversionOrder
    | RareRegexOther
    | RareRegexMembership
    | RareSequence

  type rare_inventory_entry = {
    name : string,
    family : rare_inventory_family,
    replay_kind : rare_replay_kind
  }

  fun rare_entry family replay_kind name : rare_inventory_entry =
    {name = name, family = family, replay_kind = replay_kind}

  fun unsupported name reason =
    RareUnsupported
      ("unsupported cvc5-1.3.4 RARE rule " ^ name ^ ": " ^ reason)

  fun unsupported_source_entry family recipe name reason =
    rare_entry family (RareSourceUnsupported (recipe, reason)) name

  fun string_entry family recipe =
    rare_entry family (RareStringRecipe recipe)
      (rare_string_recipe_name recipe)

  (* Generated from cvc5-1.3.4's authoritative
       src/theory/strings/rewrites and src/theory/arrays/rewrites.
     The first string tranche contains 7 contains, 7 length, and 3 prefix
     rules.  The adjacent closed Array inventory has 6 rules.  TASK_24
     extends this same block with the remaining string families.

     A disposition is part of every entry: registry membership can therefore
     never silently fall through to a generic replay handler. *)
  val cvc134_rare_first_tranche : rare_inventory_entry list = [
    rare_entry RareContains RareContainsRefl "str-contains-refl",
    string_entry RareContains ContainsConcatFind,
    string_entry RareContains ContainsConcatFindContra,
    rare_entry RareContains RareContainsSplitChar
      "str-contains-split-char",
    string_entry RareContains ContainsLeqLenEq,
    string_entry RareContains ContainsEmpty,
    string_entry RareContains ContainsChar,
    string_entry RareLength LenReplaceInv,
    string_entry RareLength LenReplaceAllInv,
    string_entry RareLength LenUpdateInv,
    string_entry RareLength LenSubstrInRange,
    string_entry RareLength LenConcatRec,
    string_entry RareLength LenEqZeroConcatRec,
    string_entry RareLength LenEqZeroBase,
    string_entry RarePrefix PrefixElim,
    string_entry RarePrefix PrefixEq,
    string_entry RarePrefix PrefixOne,
    rare_entry RareArray RareArgumentRewrite "array-read-over-write",
    rare_entry RareArray RareArgumentRewrite "array-read-over-write2",
    rare_entry RareArray RareArgumentRewrite "array-store-overwrite",
    rare_entry RareArray RareArgumentRewrite "array-store-self",
    rare_entry RareArray RareRecursiveArgumentRewrite
      "array-read-over-write-split",
    rare_entry RareArray RareArgumentRewrite "array-store-swap"
  ]

  val cvc134_rare_source_recipe_table : rare_inventory_entry list = [
    rare_entry RareConcatEquality (RareSourceRecipe {
      formals =
        [("x1", RareSourceList RareSourceSeqConcat, RareSourceSeq),
         ("x", RareSourceTerm, RareSourceSeq),
         ("x2", RareSourceList RareSourceSeqConcat, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (str.contains y x) false)"],
      target = "(= (= (str.++ x1 x x2) y) false)"}) "str-eq-ctn-false",
    rare_entry RareConcatEquality (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (str.contains y x) false)"],
      target = "(= (= x y) false)"}) "str-eq-ctn-full-false1",
    rare_entry RareConcatEquality (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (str.contains x y) false)"],
      target = "(= (= x y) false)"}) "str-eq-ctn-full-false2",
    rare_entry RareConcatEquality (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceString),
         ("y", RareSourceTerm, RareSourceString)],
      premises = ["(= (= (str.len x) (str.len y)) false)"],
      target = "(= (= x y) false)"}) "str-eq-len-false",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("n", RareSourceTerm, RareSourceInt),
         ("m", RareSourceTerm, RareSourceInt)],
      premises = ["(= (>= n (str.len x)) true)"],
      target =
        "(= (str.substr x n m) (@seq.empty_of_type (@type_of x)))"})
      "str-substr-empty-start",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("n", RareSourceTerm, RareSourceInt),
         ("m", RareSourceTerm, RareSourceInt)],
      premises = ["(= (< n 0) true)"],
      target =
        "(= (str.substr x n m) (@seq.empty_of_type (@type_of x)))"})
      "str-substr-empty-start-neg",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("n1", RareSourceTerm, RareSourceInt),
         ("m1", RareSourceTerm, RareSourceInt),
         ("n2", RareSourceTerm, RareSourceInt),
         ("m2", RareSourceTerm, RareSourceInt)],
      premises = ["(= (>= n2 m1) true)"],
      target =
        "(= (str.substr (str.substr x n1 m1) n2 m2) " ^
        "(@seq.empty_of_type (@type_of x)))"})
      "str-substr-substr-start-geq-len",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals =
        [("s", RareSourceTerm, RareSourceSeq),
         ("r", RareSourceTerm, RareSourceSeq),
         ("m", RareSourceTerm, RareSourceInt)],
      premises = ["(= (= (str.len s) 0) false)", "(= (str.len r) 0)"],
      target =
        "(= (= (str.substr s 0 m) r) (<= m 0))"}) "str-substr-z-eq-empty-leq",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals =
        [("s", RareSourceTerm, RareSourceSeq),
         ("emp", RareSourceTerm, RareSourceSeq),
         ("n", RareSourceTerm, RareSourceInt),
         ("m", RareSourceTerm, RareSourceInt)],
      premises =
        ["(= (>= n 0) true)",
         "(= (> m 0) true)",
         "(= (str.len emp) 0)"],
      target =
        "(= (= (str.substr s n m) emp) (<= (str.len s) n))"})
      "str-substr-eq-empty-leq-len",
    rare_entry RareConcatEquality (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceSeq),
         ("ts", RareSourceList RareSourceSeqConcat, RareSourceSeq),
         ("s", RareSourceTerm, RareSourceSeq),
         ("n", RareSourceTerm, RareSourceInt),
         ("tpre", RareSourceTerm, RareSourceSeq),
         ("tpost", RareSourceTerm, RareSourceSeq)],
      premises =
        ["(= (>= n 0) true)",
         "(= (< (+ n (str.len s)) (str.len t)) true)",
         "(= tpre (str.substr t 0 n))",
         "(= tpost (str.substr t (+ n (str.len s)) (str.len t)))"],
      target =
        "(= (str.update (str.++ t ts) n s) (str.++ tpre s tpost " ^
        "ts))"}) "str-update-in-first-concat",
    rare_entry RareConcatEquality (RareSourceRecipe {
      formals =
        [("s1", RareSourceTerm, RareSourceSeq),
         ("s2", RareSourceList RareSourceSeqConcat, RareSourceSeq),
         ("t1", RareSourceTerm, RareSourceSeq),
         ("t2", RareSourceList RareSourceSeqConcat, RareSourceSeq)],
      premises = ["(= (= s1 t1) false)", "(= (str.len s1) (str.len t1))"],
      target =
        "(= (= (str.++ s1 s2) (str.++ t1 t2)) false)"}) "str-concat-clash",
    rare_entry RareConcatEquality (RareSourceRecipe {
      formals =
        [("s1", RareSourceTerm, RareSourceSeq),
         ("t1", RareSourceTerm, RareSourceSeq),
         ("t2", RareSourceList RareSourceSeqConcat, RareSourceSeq)],
      premises = ["(= (= s1 t1) false)", "(= (str.len s1) (str.len t1))"],
      target = "(= (= s1 (str.++ t1 t2)) false)"}) "str-concat-clash2",
    rare_entry RareConcatEquality (RareSourceRecipe {
      formals =
        [("s1", RareSourceTerm, RareSourceSeq),
         ("t1", RareSourceTerm, RareSourceSeq),
         ("t2", RareSourceList RareSourceSeqConcat, RareSourceSeq)],
      premises = ["(= (= s1 t1) false)", "(= (str.len s1) (str.len t1))"],
      target = "(= (= s1 (str.++ t2 t1)) false)"}) "str-concat-clash2-rev",
    rare_entry RareConcatEquality (RareSourceRecipe {
      formals =
        [("s1", RareSourceTerm, RareSourceSeq),
         ("s2", RareSourceTerm, RareSourceSeq),
         ("s3", RareSourceList RareSourceSeqConcat, RareSourceSeq),
         ("t2", RareSourceTerm, RareSourceSeq),
         ("t3", RareSourceList RareSourceSeqConcat, RareSourceSeq)],
      premises = [],
      target =
        "(= (= (str.++ s1 s2 s3) (str.++ s1 t2 t3)) (= (str.++ s2 " ^
        "s3) (str.++ t2 t3)))"}) "str-concat-unify",
    rare_entry RareConcatEquality (RareSourceRecipe {
      formals =
        [("s", RareSourceTerm, RareSourceSeq),
         ("t1", RareSourceTerm, RareSourceSeq),
         ("t2", RareSourceList RareSourceSeqConcat, RareSourceSeq)],
      premises = [],
      target =
        "(= (= s (str.++ s t1 t2)) (= (@seq.empty_of_type (@type_of " ^
        "s)) (str.++ t1 t2)))"}) "str-concat-unify-base",
    rare_entry RareConcatEquality (RareSourceRecipe {
      formals =
        [("s", RareSourceTerm, RareSourceSeq),
         ("t1", RareSourceTerm, RareSourceSeq),
         ("t2", RareSourceList RareSourceSeqConcat, RareSourceSeq)],
      premises = [],
      target =
        "(= (= s (str.++ t1 t2 s)) (= (@seq.empty_of_type (@type_of " ^
        "s)) (str.++ t1 t2)))"}) "str-concat-unify-base-rev",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals =
        [("s", RareSourceTerm, RareSourceSeq),
         ("t", RareSourceTerm, RareSourceSeq)],
      premises = [],
      target =
        "(= (str.suffixof s t) (= s (str.substr t (- (str.len t) " ^
        "(str.len s)) (str.len s))))"}) "str-suffixof-elim",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals =
        [("s", RareSourceTerm, RareSourceSeq),
         ("t", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (>= (str.len s) (str.len t)) true)"],
      target = "(= (str.suffixof s t) (= s t))"}) "str-suffixof-eq",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals =
        [("s", RareSourceTerm, RareSourceSeq),
         ("t", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (str.len t) 1)"],
      target =
        "(= (str.suffixof s t) (str.contains t s))"}) "str-suffixof-one",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals =
        [("s", RareSourceTerm, RareSourceSeq),
         ("n1", RareSourceTerm, RareSourceInt),
         ("m1", RareSourceTerm, RareSourceInt),
         ("n2", RareSourceTerm, RareSourceInt),
         ("m2", RareSourceTerm, RareSourceInt)],
      premises =
        ["(= (>= n1 0) true)",
         "(= (>= n2 0) true)",
         "(= (>= (- m2 (- m1 n2)) 0) true)"],
      target =
        "(= (str.substr (str.substr s n1 m1) n2 m2) (str.substr s " ^
        "(+ n1 n2) (- m1 n2)))"}) "str-substr-combine1",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals =
        [("s", RareSourceTerm, RareSourceSeq),
         ("n1", RareSourceTerm, RareSourceInt),
         ("m1", RareSourceTerm, RareSourceInt),
         ("n2", RareSourceTerm, RareSourceInt),
         ("m2", RareSourceTerm, RareSourceInt)],
      premises =
        ["(= (>= n1 0) true)",
         "(= (>= n2 0) true)",
         "(= (>= (- (- m1 n2) m2) 0) true)"],
      target =
        "(= (str.substr (str.substr s n1 m1) n2 m2) (str.substr s " ^
        "(+ n1 n2) m2))"}) "str-substr-combine2",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals =
        [("s", RareSourceTerm, RareSourceSeq),
         ("n1", RareSourceTerm, RareSourceInt),
         ("m1", RareSourceTerm, RareSourceInt),
         ("n2", RareSourceTerm, RareSourceInt),
         ("m2", RareSourceTerm, RareSourceInt)],
      premises =
        ["(= (>= n1 0) true)",
         "(= (>= n2 0) true)",
         "(= (>= (str.len (str.substr s n1 m1)) (+ n2 m2)) true)"],
      target =
        "(= (str.substr (str.substr s n1 m1) n2 m2) (str.substr s " ^
        "(+ n1 n2) m2))"}) "str-substr-combine3",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals =
        [("s", RareSourceTerm, RareSourceSeq),
         ("n1", RareSourceTerm, RareSourceInt),
         ("m1", RareSourceTerm, RareSourceInt),
         ("n2", RareSourceTerm, RareSourceInt),
         ("m2", RareSourceTerm, RareSourceInt)],
      premises =
        ["(= (>= n1 0) true)",
         "(= (>= n2 0) true)",
         "(= (>= (+ n2 m2) (str.len (str.substr s n1 m1))) true)"],
      target =
        "(= (str.substr (str.substr s n1 m1) n2 m2) (str.substr s " ^
        "(+ n1 n2) (- m1 n2)))"}) "str-substr-combine4",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals =
        [("s1", RareSourceTerm, RareSourceSeq),
         ("s2", RareSourceTerm, RareSourceSeq),
         ("s3", RareSourceList RareSourceSeqConcat, RareSourceSeq),
         ("n", RareSourceTerm, RareSourceInt),
         ("m", RareSourceTerm, RareSourceInt)],
      premises = ["(= (>= n (str.len s1)) true)"],
      target =
        "(= (str.substr (str.++ s1 s2 s3) n m) (str.substr (str.++ " ^
        "s2 s3) (- n (str.len s1)) m))"}) "str-substr-concat2",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("s", RareSourceTerm, RareSourceSeq),
         ("t", RareSourceTerm, RareSourceSeq),
         ("r", RareSourceTerm, RareSourceSeq),
         ("n", RareSourceTerm, RareSourceInt)],
      premises = ["(= (str.len t) (str.len r))", "(= (str.len t) 1)"],
      target =
        "(= (str.substr (str.replace s t r) 0 n) (str.replace " ^
        "(str.substr s 0 n) t r))"}) "str-substr-replace",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals =
        [("s", RareSourceTerm, RareSourceSeq),
         ("n", RareSourceTerm, RareSourceInt)],
      premises = ["(= (>= n (str.len s)) true)"],
      target = "(= (str.substr s 0 n) s)"}) "str-substr-full",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceSeq),
         ("s", RareSourceTerm, RareSourceSeq)],
      premises = [],
      target = "(= (str.replace t t s) s)"}) "str-replace-self",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceSeq),
         ("s", RareSourceTerm, RareSourceSeq)],
      premises = [],
      target = "(= (str.replace t s s) t)"}) "str-replace-id",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("t1", RareSourceTerm, RareSourceSeq),
         ("t2", RareSourceTerm, RareSourceSeq),
         ("r", RareSourceList RareSourceSeqConcat, RareSourceSeq),
         ("s", RareSourceTerm, RareSourceSeq)],
      premises = [],
      target =
        "(= (str.replace (str.++ t1 t2 r) t1 s) (str.++ s t2 r))"})
      "str-replace-prefix",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceSeq),
         ("s", RareSourceTerm, RareSourceSeq),
         ("r", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (str.contains t s) false)"],
      target = "(= (str.replace t s r) t)"}) "str-replace-no-contains",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceSeq),
         ("s", RareSourceTerm, RareSourceSeq),
         ("r", RareSourceTerm, RareSourceSeq),
         ("tpre", RareSourceTerm, RareSourceSeq),
         ("tpost", RareSourceTerm, RareSourceSeq)],
      premises =
        ["(= (>= (str.indexof t s 0) 0) true)",
         "(= tpre (str.substr t 0 (str.indexof t s 0)))",
         "(= tpost (str.substr t (+ (str.indexof t s 0) (str.len " ^
         "s)) (str.len t)))"],
      target =
        "(= (str.replace t s r) (str.++ tpre r tpost))"})
      "str-replace-find-base",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceSeq),
         ("ts", RareSourceList RareSourceSeqConcat, RareSourceSeq),
         ("s", RareSourceTerm, RareSourceSeq),
         ("r", RareSourceTerm, RareSourceSeq),
         ("tpre", RareSourceTerm, RareSourceSeq),
         ("tpost", RareSourceTerm, RareSourceSeq)],
      premises =
        ["(= (>= (str.indexof t s 0) 0) true)",
         "(= tpre (str.substr t 0 (str.indexof t s 0)))",
         "(= tpost (str.substr t (+ (str.indexof t s 0) (str.len " ^
         "s)) (str.len t)))"],
      target =
        "(= (str.replace (str.++ t ts) s r) (str.++ tpre r tpost " ^
        "ts))"}) "str-replace-find-first-concat",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceSeq),
         ("s", RareSourceTerm, RareSourceSeq),
         ("r", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (str.len r) 0)"],
      target = "(= (str.replace t r s) (str.++ s t))"}) "str-replace-empty",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceSeq),
         ("s", RareSourceTerm, RareSourceSeq),
         ("r", RareSourceTerm, RareSourceSeq),
         ("ts", RareSourceList RareSourceSeqConcat, RareSourceSeq),
         ("ss", RareSourceList RareSourceSeqConcat, RareSourceSeq)],
      premises = ["(= (str.len s) 1)"],
      target =
        "(= (str.replace (str.++ ts t ss t) s r) (str.++ " ^
        "(str.replace (str.++ ts t ss) s r) t))"}) "str-replace-one-pre",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceSeq),
         ("r", RareSourceTerm, RareSourceSeq),
         ("ts", RareSourceList RareSourceSeqConcat, RareSourceSeq),
         ("ss", RareSourceList RareSourceSeqConcat, RareSourceSeq)],
      premises = [],
      target =
        "(= (str.replace (str.++ ts t ss) t r) (str.++ (str.replace " ^
        "(str.++ ts t) t r) ss))"}) "str-replace-find-pre",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceSeq),
         ("s", RareSourceTerm, RareSourceSeq),
         ("r", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (str.contains t s) false)"],
      target = "(= (str.replace_all t s r) t)"}) "str-replace-all-no-contains",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceSeq),
         ("s", RareSourceTerm, RareSourceSeq),
         ("r", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (str.len s) 0)"],
      target = "(= (str.replace_all t s r) t)"}) "str-replace-all-empty",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceSeq),
         ("s", RareSourceTerm, RareSourceSeq)],
      premises = [],
      target = "(= (str.replace_all t s s) t)"}) "str-replace-all-id",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceSeq),
         ("s", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (= (str.len t) 0) false)"],
      target = "(= (str.replace_all t t s) s)"}) "str-replace-all-self",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceSeq),
         ("r", RareSourceTerm, RareSourceSeq)],
      premises = [],
      target = "(= (str.replace_re t re.none r) t)"}) "str-replace-re-none",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceSeq),
         ("r", RareSourceTerm, RareSourceSeq)],
      premises = [],
      target =
        "(= (str.replace_re_all t re.none r) t)"}) "str-replace-re-all-none",
    rare_entry RareIndexof (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceSeq),
         ("n", RareSourceTerm, RareSourceInt)],
      premises = [],
      target =
        "(= (str.indexof t t n) (str.indexof (@seq.empty_of_type " ^
        "(@type_of t)) (@seq.empty_of_type (@type_of t)) n))"})
      "str-indexof-self",
    rare_entry RareIndexof (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceSeq),
         ("s", RareSourceTerm, RareSourceSeq),
         ("n", RareSourceTerm, RareSourceInt)],
      premises = ["(= (str.contains (str.substr t n (str.len t)) s) false)"],
      target = "(= (str.indexof t s n) (- 1))"}) "str-indexof-no-contains",
    rare_entry RareIndexof (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceSeq),
         ("s", RareSourceTerm, RareSourceSeq),
         ("n", RareSourceTerm, RareSourceInt)],
      premises = ["(= (> n (str.len t)) true)"],
      target = "(= (str.indexof t s n) (- 1))"}) "str-indexof-oob",
    rare_entry RareIndexof (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceSeq),
         ("s", RareSourceTerm, RareSourceSeq),
         ("n", RareSourceTerm, RareSourceInt)],
      premises = ["(= (> 0 n) true)"],
      target = "(= (str.indexof t s n) (- 1))"}) "str-indexof-oob2",
    rare_entry RareIndexof (RareSourceRecipe {
      formals =
        [("t1", RareSourceTerm, RareSourceSeq),
         ("t2", RareSourceList RareSourceSeqConcat, RareSourceSeq),
         ("s", RareSourceTerm, RareSourceSeq),
         ("n", RareSourceTerm, RareSourceInt)],
      premises =
        ["(= (> (str.len s) 0) true)",
         "(= (str.contains (str.substr t1 n (str.len t1)) s) true)"],
      target =
        "(= (str.indexof (str.++ t1 t2) s n) (str.indexof t1 s " ^
        "n))"})
      "str-indexof-contains-pre",
    rare_entry RareIndexof (RareSourceRecipe {
      formals =
        [("t1", RareSourceList RareSourceSeqConcat, RareSourceSeq),
         ("t", RareSourceTerm, RareSourceSeq),
         ("t2", RareSourceList RareSourceSeqConcat, RareSourceSeq),
         ("s", RareSourceTerm, RareSourceSeq)],
      premises = [],
      target =
        "(= (str.indexof (str.++ t1 t s t2) t 0) (str.indexof " ^
        "(str.++ t1 t) t 0))"}) "str-indexof-contains-concat-pre",
    rare_entry RareIndexof (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceSeq),
         ("emp", RareSourceTerm, RareSourceSeq),
         ("n", RareSourceTerm, RareSourceInt)],
      premises =
        ["(= (str.len emp) 0)",
         "(= (>= (str.len t) n) true)",
         "(= (>= n 0) true)"],
      target = "(= (str.indexof t emp n) n)"}) "str-indexof-find-emp",
    rare_entry RareIndexof (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceSeq),
         ("s", RareSourceTerm, RareSourceSeq),
         ("r", RareSourceTerm, RareSourceSeq),
         ("n", RareSourceTerm, RareSourceInt)],
      premises =
        ["(= (<= n (str.len t)) true)",
         "(= (<= n (str.len r)) true)",
         "(= (str.substr t n (str.len t)) (str.substr r n (str.len r)))"],
      target =
        "(= (= (str.indexof t s n) (str.indexof r s n)) true)"})
      "str-indexof-eq-irr",
    rare_entry RareIndexof (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceString),
         ("n", RareSourceTerm, RareSourceInt)],
      premises = [],
      target =
        "(= (str.indexof_re t re.none n) (- 1))"}) "str-indexof-re-none",
    rare_entry RareIndexof (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceString),
         ("r", RareSourceTerm, RareSourceRegex),
         ("n", RareSourceTerm, RareSourceInt)],
      premises =
        ["(= (str.in_re \"\" r) true)",
         "(= (>= (str.len t) n) true)",
         "(= (>= n (- 1)) true)"],
      target = "(= (str.indexof_re t r n) n)"}) "str-indexof-re-emp-re",
    rare_entry RareConcatEquality (RareSourceRecipe {
      formals =
        [("s1", RareSourceTerm, RareSourceString),
         ("s2", RareSourceTerm, RareSourceString),
         ("s3", RareSourceList RareSourceSeqConcat, RareSourceString)],
      premises = [],
      target =
        "(= (str.to_lower (str.++ s1 s2 s3)) (str.++ (str.to_lower " ^
        "s1) (str.to_lower (str.++ s2 s3))))"}) "str-to-lower-concat",
    rare_entry RareConcatEquality (RareSourceRecipe {
      formals =
        [("s1", RareSourceTerm, RareSourceString),
         ("s2", RareSourceTerm, RareSourceString),
         ("s3", RareSourceList RareSourceSeqConcat, RareSourceString)],
      premises = [],
      target =
        "(= (str.to_upper (str.++ s1 s2 s3)) (str.++ (str.to_upper " ^
        "s1) (str.to_upper (str.++ s2 s3))))"}) "str-to-upper-concat",
    rare_entry RareConversionOrder (RareSourceRecipe {
      formals = [("s", RareSourceTerm, RareSourceString)],
      premises = [],
      target =
        "(= (str.to_lower (str.to_upper s)) (str.to_lower s))"})
      "str-to-lower-upper",
    rare_entry RareConversionOrder (RareSourceRecipe {
      formals = [("s", RareSourceTerm, RareSourceString)],
      premises = [],
      target =
        "(= (str.to_upper (str.to_lower s)) (str.to_upper s))"})
      "str-to-upper-lower",
    rare_entry RareConversionOrder (RareSourceRecipe {
      formals = [("s", RareSourceTerm, RareSourceString)],
      premises = [],
      target =
        "(= (str.len (str.to_lower s)) (str.len s))"}) "str-to-lower-len",
    rare_entry RareConversionOrder (RareSourceRecipe {
      formals = [("s", RareSourceTerm, RareSourceString)],
      premises = [],
      target =
        "(= (str.len (str.to_upper s)) (str.len s))"}) "str-to-upper-len",
    rare_entry RareConversionOrder (RareSourceRecipe {
      formals = [("n", RareSourceTerm, RareSourceInt)],
      premises = [],
      target =
        "(= (str.to_lower (str.from_int n)) (str.from_int n))"})
      "str-to-lower-from-int",
    rare_entry RareConversionOrder (RareSourceRecipe {
      formals = [("n", RareSourceTerm, RareSourceInt)],
      premises = [],
      target =
        "(= (str.to_upper (str.from_int n)) (str.from_int n))"})
      "str-to-upper-from-int",
    rare_entry RareConcatEquality (RareSourceRecipe {
      formals =
        [("s1", RareSourceList RareSourceSeqConcat, RareSourceString),
         ("s2", RareSourceTerm, RareSourceString),
         ("s3", RareSourceList RareSourceSeqConcat, RareSourceString)],
      premises = ["(= (str.to_int s2) (- 1))", "(= (= (str.len s2) 0) false)"],
      target =
        "(= (str.to_int (str.++ s1 s2 s3)) (- 1))"})
      "str-to-int-concat-neg-one",
    rare_entry RareConversionOrder (RareSourceRecipe {
      formals = [("s", RareSourceTerm, RareSourceString)],
      premises = [],
      target = "(= (str.<= \"\" s) true)"}) "str-leq-empty",
    rare_entry RareConversionOrder (RareSourceRecipe {
      formals = [("s", RareSourceTerm, RareSourceString)],
      premises = [],
      target = "(= (str.<= s \"\") (= s \"\"))"}) "str-leq-empty-eq",
    rare_entry RareConcatEquality (RareSourceRecipe {
      formals =
        [("s", RareSourceList RareSourceSeqConcat, RareSourceString),
         ("t1", RareSourceTerm, RareSourceString),
         ("s1", RareSourceTerm, RareSourceString),
         ("t2", RareSourceList RareSourceSeqConcat, RareSourceString),
         ("s2", RareSourceList RareSourceSeqConcat, RareSourceString)],
      premises = ["(= (str.len t1) (str.len s1))", "(= (str.<= t1 s1) false)"],
      target =
        "(= (str.<= (str.++ s t1 t2) (str.++ s s1 s2)) false)"})
      "str-leq-concat-false",
    rare_entry RareConcatEquality (RareSourceRecipe {
      formals =
        [("s", RareSourceList RareSourceSeqConcat, RareSourceString),
         ("t1", RareSourceTerm, RareSourceString),
         ("s1", RareSourceTerm, RareSourceString),
         ("t2", RareSourceList RareSourceSeqConcat, RareSourceString),
         ("s2", RareSourceList RareSourceSeqConcat, RareSourceString)],
      premises =
        ["(= (str.len t1) (str.len s1))",
         "(= (= t1 s1) false)",
         "(= (str.<= t1 s1) true)"],
      target =
        "(= (str.<= (str.++ s t1 t2) (str.++ s s1 s2)) true)"})
      "str-leq-concat-true",
    rare_entry RareConcatEquality (RareSourceRecipe {
      formals =
        [("t1", RareSourceTerm, RareSourceString),
         ("t2", RareSourceList RareSourceSeqConcat, RareSourceString),
         ("s", RareSourceTerm, RareSourceString)],
      premises = ["(= (str.len t1) (str.len s))", "(= (= t1 s) false)"],
      target =
        "(= (str.<= (str.++ t1 t2) s) (str.<= t1 s))"})
      "str-leq-concat-base-1",
    rare_entry RareConcatEquality (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceString),
         ("s1", RareSourceTerm, RareSourceString),
         ("s2", RareSourceList RareSourceSeqConcat, RareSourceString)],
      premises = ["(= (str.len t) (str.len s1))", "(= (= t s1) false)"],
      target =
        "(= (str.<= t (str.++ s1 s2)) (str.<= t s1))"})
      "str-leq-concat-base-2",
    rare_entry RareConversionOrder (RareSourceRecipe {
      formals =
        [("n", RareSourceTerm, RareSourceInt),
         ("s", RareSourceTerm, RareSourceString)],
      premises = ["(= (= s \"\") false)", "(= (str.to_int s) (- 1))"],
      target =
        "(= (str.contains (str.from_int n) s) false)"})
      "str-from-int-no-ctn-nondigit",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals =
        [("t", RareSourceTerm, RareSourceSeq),
         ("s", RareSourceTerm, RareSourceSeq),
         ("n", RareSourceTerm, RareSourceInt),
         ("m", RareSourceTerm, RareSourceInt)],
      premises = ["(= (str.contains t s) false)"],
      target =
        "(= (str.contains (str.substr t n m) s) false)"})
      "str-substr-ctn-contra",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals =
        [("s", RareSourceTerm, RareSourceSeq),
         ("n", RareSourceTerm, RareSourceInt),
         ("m", RareSourceTerm, RareSourceInt)],
      premises = [],
      target =
        "(= (str.contains s (str.substr s n m)) true)"}) "str-substr-ctn",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("s", RareSourceTerm, RareSourceSeq),
         ("t", RareSourceTerm, RareSourceSeq),
         ("r", RareSourceTerm, RareSourceSeq),
         ("u", RareSourceTerm, RareSourceSeq)],
      premises =
        ["(= (str.contains s u) true)",
         "(= (str.contains r u) true)"],
      target =
        "(= (str.contains (str.replace s t r) u) true)"})
      "str-replace-dual-ctn",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("s", RareSourceTerm, RareSourceSeq),
         ("t", RareSourceTerm, RareSourceSeq),
         ("r", RareSourceTerm, RareSourceSeq),
         ("u", RareSourceTerm, RareSourceSeq)],
      premises =
        ["(= (str.contains s t) false)",
         "(= (str.contains s u) false)"],
      target =
        "(= (str.contains s (str.replace t r u)) false)"})
      "str-replace-dual-ctn-false",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("s", RareSourceTerm, RareSourceSeq),
         ("t", RareSourceTerm, RareSourceSeq)],
      premises = [],
      target =
        "(= (str.contains s (str.replace t s t)) (str.contains s " ^
        "t))"}) "str-replace-self-ctn-simp",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("s", RareSourceTerm, RareSourceSeq),
         ("t", RareSourceTerm, RareSourceSeq),
         ("emp", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (str.len emp) 0)"],
      target =
        "(= (str.contains s (str.replace emp s t)) (= emp " ^
        "(str.replace emp s t)))"}) "str-replace-emp-ctn-src",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("n", RareSourceTerm, RareSourceInt)],
      premises = ["(= (>= 1 (str.len x)) true)"],
      target =
        "(= (str.substr x n n) (@seq.empty_of_type (@type_of x)))"})
      "str-substr-char-start-eq-len",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq),
         ("z", RareSourceTerm, RareSourceSeq),
         ("w", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (str.len w) 1)", "(= (str.contains y w) false)"],
      target =
        "(= (str.contains (str.replace x y z) w) (or (str.contains " ^
        "x w) (and (str.contains x y) (str.contains z w))))"})
      "str-contains-repl-char",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq),
         ("w", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (str.len w) 1)"],
      target =
        "(= (str.contains (str.replace x y x) w) (str.contains x " ^
        "w))"}) "str-contains-repl-self-tgt-char",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq)],
      premises = [],
      target =
        "(= (str.contains (str.replace x y x) y) (str.contains x " ^
        "y))"}) "str-contains-repl-self",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq),
         ("z", RareSourceTerm, RareSourceSeq)],
      premises = [],
      target =
        "(= (str.contains (str.replace x y z) z) (or (str.contains " ^
        "x y) (str.contains x z)))"}) "str-contains-repl-tgt",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (>= (str.len y) (str.len x)) true)"],
      target = "(= (str.replace x y x) x)"}) "str-repl-repl-len-id",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq),
         ("z", RareSourceTerm, RareSourceSeq),
         ("w", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (str.contains z w) false)"],
      target =
        "(= (str.replace x w (str.replace z x y)) (str.replace x w " ^
        "z))"}) "str-repl-repl-src-tgt-no-ctn",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq)],
      premises = [],
      target =
        "(= (str.replace x y (str.replace y x y)) x)"})
      "str-repl-repl-tgt-self",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq),
         ("z", RareSourceTerm, RareSourceSeq),
         ("w", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (str.contains x z) false)"],
      target =
        "(= (str.replace x y (str.replace y z w)) x)"})
      "str-repl-repl-tgt-no-ctn",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq),
         ("z", RareSourceTerm, RareSourceSeq)],
      premises = [],
      target =
        "(= (str.replace x (str.replace y x y) z) (str.replace x y " ^
        "z))"}) "str-repl-repl-src-self",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq),
         ("z", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (str.contains y z) false)"],
      target =
        "(= (str.replace x (str.replace y x z) y) (str.replace x y " ^
        "y))"}) "str-repl-repl-src-inv-no-ctn1",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq),
         ("z", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (str.contains y z) false)"],
      target =
        "(= (str.replace x (str.replace y x z) x) (str.replace x y " ^
        "x))"}) "str-repl-repl-src-inv-no-ctn2",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq),
         ("z", RareSourceTerm, RareSourceSeq),
         ("w", RareSourceTerm, RareSourceSeq),
         ("u", RareSourceTerm, RareSourceSeq)],
      premises =
        ["(= (str.contains x z) false)",
         "(= (str.contains x w) false)"],
      target =
        "(= (str.replace x (str.replace y z w) u) (str.replace x y " ^
        "u))"}) "str-repl-repl-src-inv-no-ctn3",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq)],
      premises = [],
      target =
        "(= (str.replace x (str.replace x y x) x) x)"})
      "str-repl-repl-dual-self",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq),
         ("z", RareSourceTerm, RareSourceSeq),
         ("w", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (str.contains x z) false)"],
      target =
        "(= (str.replace x (str.replace x y z) w) (ite " ^
        "(str.contains x y) x w))"}) "str-repl-repl-dual-ite1",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq),
         ("z", RareSourceTerm, RareSourceSeq),
         ("w", RareSourceTerm, RareSourceSeq)],
      premises =
        ["(= (str.contains y z) false)",
         "(= (str.contains z y) false)"],
      target =
        "(= (str.replace x (str.replace x y z) w) (ite " ^
        "(str.contains x y) x w))"}) "str-repl-repl-dual-ite2",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("y", RareSourceTerm, RareSourceSeq),
         ("z", RareSourceTerm, RareSourceSeq),
         ("w", RareSourceTerm, RareSourceSeq)],
      premises =
        ["(= (= w z) false)",
         "(= (>= (str.len w) (str.len z)) true)"],
      target =
        "(= (str.replace (str.replace y w y) y z) (str.replace " ^
        "(str.replace y w z) y z))"}) "str-repl-repl-lookahead-id-simp",
    rare_entry RareRegexStar (RareSourceRecipe {
      formals =
        [("xs", RareSourceList RareSourceRegexConcat, RareSourceRegex),
         ("r", RareSourceTerm, RareSourceRegex),
         ("ys", RareSourceList RareSourceRegexConcat, RareSourceRegex)],
      premises = [],
      target =
        "(= (re.++ xs (re.* r) r ys) (re.++ xs r (re.* r) ys))"})
      "re-concat-star-swap",
    rare_entry RareRegexStar (RareSourceRecipe {
      formals =
        [("xs", RareSourceList RareSourceRegexConcat, RareSourceRegex),
         ("r", RareSourceTerm, RareSourceRegex),
         ("ys", RareSourceList RareSourceRegexConcat, RareSourceRegex)],
      premises = [],
      target =
        "(= (re.++ xs (re.* r) (re.* r) ys) (re.++ xs (re.* r) " ^
        "ys))"})
      "re-concat-star-repeat",
    rare_entry RareRegexStar (RareSourceRecipe {
      formals =
        [("xs", RareSourceList RareSourceRegexConcat, RareSourceRegex),
         ("r", RareSourceTerm, RareSourceRegex),
         ("ys", RareSourceList RareSourceRegexConcat, RareSourceRegex)],
      premises = [],
      target =
        "(= (re.++ xs (re.* r) (re.* re.allchar) ys) (re.++ xs " ^
        "(re.* re.allchar) ys))"}) "re-concat-star-subsume1",
    rare_entry RareRegexStar (RareSourceRecipe {
      formals =
        [("xs", RareSourceList RareSourceRegexConcat, RareSourceRegex),
         ("r", RareSourceTerm, RareSourceRegex),
         ("ys", RareSourceList RareSourceRegexConcat, RareSourceRegex)],
      premises = [],
      target =
        "(= (re.++ xs (re.* re.allchar) (re.* r) ys) (re.++ xs " ^
        "(re.* re.allchar) ys))"}) "re-concat-star-subsume2",
    rare_entry RareRegexOther (RareSourceRecipe {
      formals =
        [("xs", RareSourceList RareSourceRegexUnion, RareSourceRegex),
         ("ys", RareSourceList RareSourceRegexUnion, RareSourceRegex)],
      premises = [],
      target =
        "(= (re.union xs (re.* re.allchar) ys) (re.* re.allchar))"})
      "re-union-all",
    rare_entry RareRegexOther (RareSourceRecipe {
      formals =
        [("r", RareSourceTerm, RareSourceRegex),
         ("s", RareSourceTerm, RareSourceString)],
      premises = ["(= (str.in_re s r) true)"],
      target = "(= (re.union (str.to_re s) r) r)"}) "re-union-const-elim",
    rare_entry RareRegexOther (RareSourceRecipe {
      formals =
        [("xs", RareSourceList RareSourceRegexInter, RareSourceRegex),
         ("ys", RareSourceList RareSourceRegexInter, RareSourceRegex)],
      premises = [],
      target =
        "(= (re.inter xs (re.* re.allchar) ys) (re.inter xs ys))"})
      "re-inter-all",
    rare_entry RareRegexStar (RareSourceRecipe {
      formals = [],
      premises = [],
      target = "(= (re.* re.none) (str.to_re \"\"))"}) "re-star-none",
    rare_entry RareRegexStar (RareSourceRecipe {
      formals = [],
      premises = [],
      target = "(= (re.* (str.to_re \"\")) (str.to_re \"\"))"}) "re-star-emp",
    rare_entry RareRegexStar (RareSourceRecipe {
      formals = [("x", RareSourceTerm, RareSourceRegex)],
      premises = [],
      target = "(= (re.* (re.* x)) (re.* x))"}) "re-star-star",
    rare_entry RareRegexOther (RareSourceRecipe {
      formals = [("s", RareSourceTerm, RareSourceString)],
      premises = ["(= (str.len s) 1)"],
      target = "(= (re.range s s) (str.to_re s))"}) "re-range-refl",
    rare_entry RareRegexOther (RareSourceRecipe {
      formals =
        [("s", RareSourceTerm, RareSourceString),
         ("t", RareSourceTerm, RareSourceString)],
      premises =
        ["(= (str.len s) 1)",
         "(= (str.len t) 1)",
         "(= (< (str.to_code t) (str.to_code s)) true)"],
      target = "(= (re.range s t) re.none)"}) "re-range-emp",
    rare_entry RareRegexOther (RareSourceRecipe {
      formals =
        [("s", RareSourceTerm, RareSourceString),
         ("t", RareSourceTerm, RareSourceString)],
      premises = ["(= (= (str.len s) 1) false)"],
      target = "(= (re.range s t) re.none)"}) "re-range-non-singleton-1",
    rare_entry RareRegexOther (RareSourceRecipe {
      formals =
        [("s", RareSourceTerm, RareSourceString),
         ("t", RareSourceTerm, RareSourceString)],
      premises = ["(= (= (str.len t) 1) false)"],
      target = "(= (re.range s t) re.none)"}) "re-range-non-singleton-2",
    rare_entry RareRegexStar (RareSourceRecipe {
      formals =
        [("x", RareSourceList RareSourceRegexUnion, RareSourceRegex),
         ("y", RareSourceList RareSourceRegexUnion, RareSourceRegex)],
      premises = [],
      target =
        "(= (re.* (re.union x re.allchar y)) (re.* re.allchar))"})
      "re-star-union-char",
    rare_entry RareRegexStar (RareSourceRecipe {
      formals =
        [("x", RareSourceList RareSourceRegexUnion, RareSourceRegex),
         ("y", RareSourceList RareSourceRegexUnion, RareSourceRegex)],
      premises = [],
      target =
        "(= (re.* (re.union x (str.to_re \"\") y)) (re.* (re.union " ^
        "x y)))"}) "re-star-union-drop-emp",
    rare_entry RareRegexOther (RareSourceRecipe {
      formals =
        [("n", RareSourceIndex, RareSourceInt),
         ("m", RareSourceIndex, RareSourceInt),
         ("r", RareSourceTerm, RareSourceRegex)],
      premises = ["(= (> n m) true)"],
      target = "(= (re.loop n m r) re.none)"}) "re-loop-neg",
    rare_entry RareRegexOther (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceRegex),
         ("ys", RareSourceList RareSourceRegexInter, RareSourceRegex),
         ("s", RareSourceTerm, RareSourceString)],
      premises = ["(= (str.in_re s (re.inter (str.to_re s) x ys)) false)"],
      target =
        "(= (re.inter (str.to_re s) x ys) re.none)"}) "re-inter-cstring-neg",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals =
        [("s1", RareSourceTerm, RareSourceSeq),
         ("s2", RareSourceList RareSourceSeqConcat, RareSourceSeq),
         ("n", RareSourceTerm, RareSourceInt),
         ("m", RareSourceTerm, RareSourceInt)],
      premises = ["(= (>= (str.len s1) (+ n m)) true)"],
      target =
        "(= (str.substr (str.++ s1 s2) n m) (str.substr s1 n m))"})
      "str-substr-len-include",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals =
        [("s1", RareSourceTerm, RareSourceSeq),
         ("s2", RareSourceTerm, RareSourceSeq),
         ("s3", RareSourceList RareSourceSeqConcat, RareSourceSeq),
         ("n", RareSourceTerm, RareSourceInt)],
      premises = ["(= (>= n (str.len s1)) true)"],
      target =
        "(= (str.substr (str.++ s1 s2 s3) 0 n) (str.++ s1 " ^
        "(str.substr (str.++ s2 s3) 0 (- n (str.len s1)))))"})
      "str-substr-len-include-pre",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals =
        [("s", RareSourceTerm, RareSourceSeq),
         ("n", RareSourceTerm, RareSourceInt),
         ("m", RareSourceTerm, RareSourceInt)],
      premises = ["(= (>= m (str.len s)) true)"],
      target =
        "(= (str.substr s n m) (str.substr s n (str.len s)))"})
      "str-substr-len-norm",
    rare_entry RareSequence (RareSourceRecipe {
      formals = [("x", RareSourceTerm, RareSourceSeq)],
      premises = [],
      target = "(= (str.len (str.rev x)) (str.len x))"}) "seq-len-rev",
    rare_entry RareSequence (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceList RareSourceSeqConcat, RareSourceSeq),
         ("z", RareSourceTerm, RareSourceSeq)],
      premises = [],
      target =
        "(= (str.rev (str.++ x y z)) (str.++ (str.rev z) (str.rev " ^
        "(str.++ x y))))"}) "seq-rev-concat",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq),
         ("emp", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (str.len emp) 0)"],
      target =
        "(= (= (str.replace x y x) emp) (= x emp))"}) "str-eq-repl-self-emp",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq),
         ("z", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (= y z) false)"],
      target =
        "(= (= (str.replace x y z) x) (not (str.contains x y)))"})
      "str-eq-repl-no-change",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq),
         ("z", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (str.len y) (str.len z))"],
      target =
        "(= (= (str.replace x y z) z) (or (= x y) (= x z)))"})
      "str-eq-repl-tgt-eq-len",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq),
         ("emp", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (str.len emp) 0)", "(= (str.len y) 1)"],
      target =
        "(= (= (str.replace x y emp) emp) (str.prefixof x y))"})
      "str-eq-repl-len-one-emp-prefix",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq),
         ("z", RareSourceTerm, RareSourceSeq),
         ("emp", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (str.len emp) 0)", "(= (= z emp) false)"],
      target =
        "(= (= (str.replace x y z) emp) (and (= x emp) (not (= y " ^
        "emp))))"}) "str-eq-repl-emp-tgt-nemp",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq),
         ("z", RareSourceTerm, RareSourceSeq),
         ("emp", RareSourceTerm, RareSourceSeq)],
      premises = ["(= (str.len emp) 0)", "(= (= z emp) false)"],
      target =
        "(= (= (str.replace emp x y) z) (and (= x emp) (= y z)))"})
      "str-eq-repl-nemp-src-emp",
    rare_entry RareReplace (RareSourceRecipe {
      formals =
        [("x", RareSourceTerm, RareSourceSeq),
         ("y", RareSourceTerm, RareSourceSeq)],
      premises = [],
      target =
        "(= (= (str.replace x y x) y) (= x y))"}) "str-eq-repl-self-src",
    rare_entry RareSequence (RareSourceRecipe {
      formals = [("x", RareSourceTerm, RareSourceElement)],
      premises = [],
      target = "(= (str.len (seq.unit x)) 1)"}) "seq-len-unit",
    rare_entry RareSequence (RareSourceRecipe {
      formals = [("x", RareSourceTerm, RareSourceElement)],
      premises = [],
      target = "(= (seq.nth (seq.unit x) 0) x)"}) "seq-nth-unit",
    rare_entry RareSequence (RareSourceRecipe {
      formals = [("x", RareSourceTerm, RareSourceElement)],
      premises = [],
      target = "(= (str.rev (seq.unit x)) (seq.unit x))"}) "seq-rev-unit",
    rare_entry RareRegexMembership (RareSourceRecipe {
      formals = [("t", RareSourceTerm, RareSourceString)],
      premises = [],
      target = "(= (str.in_re t re.none) false)"}) "re-in-empty",
    rare_entry RareRegexMembership (RareSourceRecipe {
      formals = [("t", RareSourceTerm, RareSourceString)],
      premises = [],
      target =
        "(= (str.in_re t re.allchar) (= (str.len t) 1))"})
      "re-in-sigma",
    rare_entry RareRegexMembership (RareSourceRecipe {
      formals = [("t", RareSourceTerm, RareSourceString)],
      premises = [],
      target = "(= (str.in_re t (re.* re.allchar)) true)"})
      "re-in-sigma-star",
    rare_entry RareRegexMembership (RareSourceRecipe {
      formals = [("s", RareSourceTerm, RareSourceString),
                 ("r1", RareSourceTerm, RareSourceRegex),
                 ("r2", RareSourceTerm, RareSourceRegex),
                 ("rs", RareSourceList RareSourceRegexInter, RareSourceRegex)],
      premises = [],
      target =
        "(= (str.in_re s (re.inter r1 r2 rs)) (and (str.in_re s " ^
        "r1) (str.in_re s (re.inter r2 rs))))"})
      "str-in-re-inter-elim",
    rare_entry RareRegexMembership (RareSourceRecipe {
      formals = [("t", RareSourceTerm, RareSourceString),
                 ("s", RareSourceTerm, RareSourceString)],
      premises = [],
      target =
        "(= (str.in_re t (re.++ (re.* re.allchar) (str.to_re s) " ^
        "(re.* re.allchar))) (str.contains t s))"})
      "str-in-re-contains",
    rare_entry RareRegexMembership (RareSourceRecipe {
      formals = [("n", RareSourceTerm, RareSourceInt)],
      premises = ["(= (>= n 0) true)"],
      target =
        "(= (str.in_re (str.from_int n) (re.++ (re.range \"0\" " ^
        "\"9\") (re.* (re.range \"0\" \"9\")))) true)"})
      "str-in-re-from-int-nemp-dig-range",
    rare_entry RareRegexMembership (RareSourceRecipe {
      formals = [("n", RareSourceTerm, RareSourceInt)],
      premises = [],
      target =
        "(= (str.in_re (str.from_int n) (re.* (re.range \"0\" \"9\"))) true)"})
      "str-in-re-from-int-dig-range",
    rare_entry RareRegexOther (RareSourceRecipe {
      formals = [],
      premises = [],
      target = "(= re.all (re.* re.allchar))"})
      "re-all-elim",
    rare_entry RareRegexOther (RareSourceRecipe {
      formals = [("xs", RareSourceList RareSourceRegexConcat, RareSourceRegex),
                 ("s", RareSourceTerm, RareSourceString),
                 ("t", RareSourceTerm, RareSourceString),
                 ("ys", RareSourceList RareSourceRegexConcat,
                  RareSourceRegex)],
      premises = [],
      target =
        "(= (re.++ xs (str.to_re s) (str.to_re t) ys) (re.++ xs " ^
        "(str.to_re (str.++ s t)) ys))"})
      "re-concat-merge",
    rare_entry RareRegexMembership (RareSourceRecipe {
      formals = [("t", RareSourceTerm, RareSourceString),
                 ("r", RareSourceTerm, RareSourceRegex)],
      premises = [],
      target =
        "(= (str.in_re t (re.comp r)) (not (str.in_re t r)))"})
      "re-in-comp",
    rare_entry RareRegexMembership (RareSourceRecipe {
      formals = [("t", RareSourceTerm, RareSourceString),
                 ("s", RareSourceTerm, RareSourceString)],
      premises = [],
      target = "(= (str.in_re t (str.to_re s)) (= t s))"})
      "re-in-cstring",
    rare_entry RareRegexOther (RareSourceRecipe {
      formals = [("x", RareSourceTerm, RareSourceRegex),
                 ("y", RareSourceTerm, RareSourceRegex)],
      premises = [],
      target = "(= (re.diff x y) (re.inter x (re.comp y)))"})
      "re-diff-elim",
    rare_entry RareRegexOther (RareSourceRecipe {
      formals = [("x", RareSourceTerm, RareSourceRegex),
                 ("ys", RareSourceList RareSourceRegexInter, RareSourceRegex),
                 ("s", RareSourceTerm, RareSourceString)],
      premises =
        ["(= (str.in_re s (re.inter (str.to_re s) x ys)) true)"],
      target = "(= (re.inter (str.to_re s) x ys) (str.to_re s))"})
      "re-inter-cstring",
    rare_entry RareRegexOther (RareSourceRecipe {
      formals = [("x", RareSourceTerm, RareSourceRegex)],
      premises = [],
      target = "(= (re.opt x) (re.union (str.to_re \"\") x))"})
      "re-opt-elim",
    rare_entry RareRegexOther (RareSourceRecipe {
      formals = [("x", RareSourceTerm, RareSourceRegex)],
      premises = [],
      target = "(= (re.+ x) (re.++ x (re.* x)))"})
      "re-plus-elim",
    rare_entry RareRegexOther (RareSourceRecipe {
      formals = [("n", RareSourceIndex, RareSourceInt),
                 ("x", RareSourceTerm, RareSourceRegex)],
      premises = [],
      target = "(= (re.^ n x) (re.loop n n x))"})
      "re-repeat-elim",
    rare_entry RareSequence (RareSourceRecipe {
      formals = [("x", RareSourceTerm, RareSourceSeq)],
      premises = [],
      target = "(= (str.rev (str.rev x)) x)"})
      "seq-rev-rev",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals = [("x", RareSourceTerm, RareSourceSeq),
                 ("n", RareSourceTerm, RareSourceInt)],
      premises = [],
      target = "(= (str.at x n) (str.substr x n 1))"})
      "str-at-elim",
    rare_entry RareConcatEquality (RareSourceRecipe {
      formals = [("s1", RareSourceTerm, RareSourceSeq),
                 ("s2", RareSourceList RareSourceSeqConcat, RareSourceSeq),
                 ("t1", RareSourceTerm, RareSourceSeq),
                 ("t2", RareSourceList RareSourceSeqConcat, RareSourceSeq)],
      premises = ["(= (= s1 t1) false)",
                  "(= (str.len s1) (str.len t1))"],
      target = "(= (= (str.++ s2 s1) (str.++ t2 t1)) false)"})
      "str-concat-clash-rev",
    rare_entry RareConcatEquality (RareSourceRecipe {
      formals = [("s1", RareSourceTerm, RareSourceSeq),
                 ("s2", RareSourceTerm, RareSourceSeq),
                 ("s3", RareSourceList RareSourceSeqConcat, RareSourceSeq),
                 ("t2", RareSourceTerm, RareSourceSeq),
                 ("t3", RareSourceList RareSourceSeqConcat, RareSourceSeq)],
      premises = [],
      target =
        "(= (= (str.++ s2 s3 s1) (str.++ t2 t3 s1)) (= (str.++ s2 " ^
        "s3) (str.++ t2 t3)))"})
      "str-concat-unify-rev",
    rare_entry RareRegexMembership (RareSourceRecipe {
      formals = [("s", RareSourceTerm, RareSourceString),
                 ("c1", RareSourceTerm, RareSourceString),
                 ("c2", RareSourceTerm, RareSourceString)],
      premises = ["(= (str.len c1) 1)", "(= (str.len c2) 1)"],
      target =
        "(= (str.in_re s (re.range c1 c2)) (and (<= (str.to_code " ^
        "c1) (str.to_code s)) (<= (str.to_code s) (str.to_code " ^
        "c2))))"})
      "str-in-re-range-elim",
    rare_entry RareRegexMembership (RareSourceRecipe {
      formals = [("s", RareSourceTerm, RareSourceString),
                 ("r1", RareSourceTerm, RareSourceRegex),
                 ("r2", RareSourceTerm, RareSourceRegex),
                 ("rs", RareSourceList RareSourceRegexUnion, RareSourceRegex)],
      premises = [],
      target =
        "(= (str.in_re s (re.union r1 r2 rs)) (or (str.in_re s " ^
        "r1) (str.in_re s (re.union r2 rs))))"})
      "str-in-re-union-elim",
    rare_entry RareConversionOrder (RareSourceRecipe {
      formals = [("s", RareSourceTerm, RareSourceString)],
      premises = [],
      target =
        "(= (str.is_digit s) (and (<= 48 (str.to_code s)) (<= " ^
        "(str.to_code s) 57)))"})
      "str-is-digit-elim",
    rare_entry RareConversionOrder (RareSourceRecipe {
      formals = [("s", RareSourceTerm, RareSourceString),
                 ("t", RareSourceTerm, RareSourceString)],
      premises = [],
      target = "(= (str.< s t) (and (not (= s t)) (str.<= s t)))"})
      "str-lt-elim",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals = [("s1", RareSourceTerm, RareSourceSeq),
                 ("s2", RareSourceList RareSourceSeqConcat, RareSourceSeq),
                 ("n", RareSourceTerm, RareSourceInt),
                 ("m", RareSourceTerm, RareSourceInt)],
      premises = ["(= (>= n 0) true)",
                  "(= (>= (str.len s1) (+ n m)) true)"],
      target =
        "(= (str.substr (str.++ s1 s2) n m) (str.substr s1 n m))"})
      "str-substr-concat1",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals = [("x", RareSourceTerm, RareSourceSeq),
                 ("n", RareSourceTerm, RareSourceInt),
                 ("m", RareSourceTerm, RareSourceInt)],
      premises = ["(= (>= 0 m) true)"],
      target =
        "(= (str.substr x n m) (@seq.empty_of_type (@type_of x)))"})
      "str-substr-empty-range",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals = [("x", RareSourceTerm, RareSourceSeq),
                 ("n", RareSourceTerm, RareSourceInt),
                 ("m", RareSourceTerm, RareSourceInt)],
      premises = ["(= (str.len x) 0)"],
      target = "(= (str.substr x n m) x)"})
      "str-substr-empty-str",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals = [("s", RareSourceTerm, RareSourceSeq),
                 ("r", RareSourceTerm, RareSourceSeq),
                 ("n", RareSourceTerm, RareSourceInt),
                 ("m", RareSourceTerm, RareSourceInt)],
      premises = ["(= n 0)", "(= (> m n) true)", "(= (str.len r) 0)"],
      target = "(= (= (str.substr s n m) r) (= s r))"})
      "str-substr-eq-empty",
    rare_entry RareSubstringSuffix (RareSourceRecipe {
      formals = [("s", RareSourceTerm, RareSourceSeq),
                 ("n", RareSourceTerm, RareSourceInt)],
      premises = ["(= (str.len s) n)"],
      target = "(= (str.substr s 0 n) s)"})
      "str-substr-full-eq"
  ]


  val cvc134_rare_unsupported_source_reasons = [
    ("str-indexof-re-none",
     "str.indexof_re has no HOL operator or parser dictionary entry"),
    ("str-indexof-re-emp-re",
     "str.indexof_re has no HOL operator or parser dictionary entry"),
    ("str-to-lower-concat",
     "str.to_lower has no HOL operator or parser dictionary entry"),
    ("str-to-upper-concat",
     "str.to_upper has no HOL operator or parser dictionary entry"),
    ("str-to-lower-upper",
     "str.to_lower/str.to_upper have no HOL operator or dictionary entry"),
    ("str-to-upper-lower",
     "str.to_upper/str.to_lower have no HOL operator or dictionary entry"),
    ("str-to-lower-len",
     "str.to_lower has no HOL operator or parser dictionary entry"),
    ("str-to-upper-len",
     "str.to_upper has no HOL operator or parser dictionary entry"),
    ("str-to-lower-from-int",
     "str.to_lower has no HOL operator or parser dictionary entry"),
    ("str-to-upper-from-int",
     "str.to_upper has no HOL operator or parser dictionary entry")
  ]

  fun classify_source_entry (entry : rare_inventory_entry) =
    case List.find (fn (name, _) => name = #name entry)
        cvc134_rare_unsupported_source_reasons of
      NONE => entry
    | SOME (_, reason) =>
        (case #replay_kind entry of
           RareSourceRecipe recipe =>
             unsupported_source_entry (#family entry) recipe
               (#name entry) reason
         | _ => raise Fail
             "unsupported TASK24 source disposition lacks its recipe")

  val cvc134_rare_source_extension =
    List.map classify_source_entry cvc134_rare_source_recipe_table

  val cvc134_rare_rewrite_inventory =
    cvc134_rare_first_tranche @ cvc134_rare_source_extension

  (* Exact closure of the two cvc5-1.3.4 String RARE source files.  Every
     source name now has a typed recipe and a proved or exact-unsupported
     disposition in this inventory; none is delegated to the generic String
     replay ladder. *)
  val cvc134_rare_str_re_seq_names =
    List.map #name (List.filter
      (fn entry => #family entry <> RareArray)
      cvc134_rare_rewrite_inventory)

  fun family_count family =
    List.length (List.filter
      (fn entry => #family entry = family) cvc134_rare_rewrite_inventory)

  val _ =
    let
      val names = List.map #name cvc134_rare_rewrite_inventory
      fun duplicates [] = false
        | duplicates (name :: rest) =
            List.exists (Lib.equal name) rest orelse duplicates rest
      fun exact_recipe (entry : rare_inventory_entry) =
        case #replay_kind entry of
          RareStringRecipe recipe =>
            rare_string_recipe_name recipe = #name entry
        | _ => true
      fun source_unsupported (entry : rare_inventory_entry) =
        case #replay_kind entry of
          RareSourceUnsupported _ => true
        | _ => false
      val unsupported_entries =
        List.filter source_unsupported cvc134_rare_rewrite_inventory
      val unsupported_names = List.map #1
        cvc134_rare_unsupported_source_reasons
      val recursive_names = List.map #name (List.filter
        (fn entry => #replay_kind entry = RareRecursiveArgumentRewrite)
        cvc134_rare_rewrite_inventory)
      fun source_formals (entry : rare_inventory_entry) =
        case #replay_kind entry of
          RareSourceRecipe {formals, ...} => formals
        | RareSourceUnsupported ({formals, ...}, _) => formals
        | _ => []
      val all_source_formals =
        List.concat (List.map source_formals cvc134_rare_rewrite_inventory)
      val list_aggregates = List.mapPartial
        (fn (_, RareSourceList aggregate, _) => SOME aggregate
          | _ => NONE) all_source_formals
      fun count_aggregate aggregate = List.length (List.filter
        (Lib.equal aggregate) list_aggregates)
      fun compatible_aggregate (_, kind, source) =
        case kind of
          RareSourceList RareSourceSeqConcat =>
            source = RareSourceSeq orelse source = RareSourceString
        | RareSourceList _ => source = RareSourceRegex
        | _ => true
    in
      if List.length names = 175 andalso not (duplicates names) andalso
         List.length cvc134_rare_str_re_seq_names = 169 andalso
         not (duplicates cvc134_rare_str_re_seq_names) andalso
         List.all exact_recipe cvc134_rare_rewrite_inventory andalso
         List.all compatible_aggregate all_source_formals andalso
         count_aggregate RareSourceSeqConcat = 41 andalso
         count_aggregate RareSourceRegexConcat = 10 andalso
         count_aggregate RareSourceRegexUnion = 7 andalso
         count_aggregate RareSourceRegexInter = 5 andalso
         List.length unsupported_names = 10 andalso
         not (duplicates unsupported_names) andalso
         List.length unsupported_entries = 10 andalso
         List.all (fn entry => List.exists
           (fn name => name = #name entry) unsupported_names)
           unsupported_entries andalso
         recursive_names = ["array-read-over-write-split"] andalso
         family_count RareContains = 7 andalso
         family_count RareLength = 7 andalso
         family_count RarePrefix = 3 andalso
         family_count RareArray = 6 andalso
         family_count RareReplace = 43 andalso
         family_count RareIndexof = 10 andalso
         family_count RareRegexStar = 9 andalso
         family_count RareConcatEquality = 20 andalso
         family_count RareSubstringSuffix = 26 andalso
         family_count RareConversionOrder = 11 andalso
         family_count RareRegexOther = 16 andalso
         family_count RareRegexMembership = 11 andalso
         family_count RareSequence = 6 then ()
      else raise Fail
        "cvc5-1.3.4 RARE inventory is not closed and unique"
    end

  fun rare_inventory_lookup name =
    List.find (fn entry : rare_inventory_entry => #name entry = name)
      cvc134_rare_rewrite_inventory

  fun rare_unsupported_diagnostic name =
    case rare_inventory_lookup name of
      SOME {replay_kind = RareSourceUnsupported (_, reason), ...} =>
        SOME ("unsupported cvc5-1.3.4 RARE rule " ^ name ^ ": " ^ reason)
    | SOME {replay_kind = RareUnsupported diagnostic, ...} =>
        SOME diagnostic
    | _ => NONE

  val rare_inventory_rules = List.map
    (fn entry : rare_inventory_entry =>
      mk_rule RareRewrite (#name entry, "rare_inventory"))
    cvc134_rare_rewrite_inventory

  (* This is deliberately a registry, rather than a catch-all replay case.
     Entries are promoted from the recorded CPC corpus.  The initial list is
     the cvc5 1.3.4 dsl-rewrite seed inventory; an unlisted rule is a checked
     replay failure, never an implicit trust step. *)
  val proof_rule_registry : proof_rule list = [
    mk_rule ProofRule ("refl", "refl"),
    mk_rule ProofRule ("eq-refl", "eq_refl"),
    mk_rule ProofRule ("symm", "symm"),
    mk_rule ProofRule ("trans", "trans"),
    mk_rule ProofRule ("cong", "cong"),
    mk_rule ProofRule ("nary_cong", "cong"),
    mk_rule ProofRule ("ho_cong", "ho_cong"),
    mk_rule ProofRule ("beta-reduce", "beta_reduce"),
    mk_rule ProofRule ("lambda-elim", "lambda_elim"),
    mk_rule ProofRule ("eq_resolve", "eq_resolve"),
    mk_rule ProofRule ("evaluate", "evaluate"),
    mk_rule ProofRule ("and_elim", "and_elim"),
    mk_rule ProofRule ("instantiate", "instantiate"),
    mk_rule ProofRule ("contra", "contra"),
    mk_rule ProofRule ("false_intro", "false_intro"),
    mk_rule ProofRule ("false_elim", "false_elim"),
    mk_rule ProofRule ("distinct_values", "datatype"),
    mk_rule ProofRule ("dt_split", "dt_split"),
    mk_rule ProofRule ("dt-cycle", "datatype_eq"),
    mk_rule ProofRule ("dt", "datatype"),
    mk_rule ProofRule ("resolution", "resolution"),
    mk_rule ProofRule ("chain_m_resolution", "resolution"),
    mk_rule ProofRule ("reordering", "reordering"),
    mk_rule ProofRule ("arith", "arith"),
    mk_rule ProofRule ("array", "array"),
    mk_rule ProofRule ("arrays-select-const", "arrays_select_const"),
    mk_rule ProofRule ("arrays_read_over_write_1", "arrays_read_over_write"),
    mk_rule ProofRule ("arrays_read_over_write", "arrays_read_over_write"),
    (* cvc5 has used both this macro and the narrow [sets-*] rewrites. *)
    mk_rule ProofRule ("sets", "sets"),
    mk_rule ProofRule ("sets_ext", "sets_ext"),
    mk_rule ProofRule ("bool", "bool"),
    mk_rule ProofRule ("trust", "trust"),
    mk_rule ProofRule ("str", "string"),
    mk_rule ProofRule ("string_eager_reduction", "string"),
    mk_rule ProofRule ("string_length_pos", "string"),
    mk_rule ProofRule ("string_reduction", "string"),
    mk_rule ProofRule ("concat_unify", "string"),
    mk_rule ProofRule ("re_unfold_pos", "string"),
    mk_rule ProofRule ("aci_norm", "aci_norm"),
    mk_rule ProofRule ("bv_poly_norm", "bv_poly_norm"),
    mk_rule ProofRule ("bv_poly_norm_eq", "bv_poly_norm_eq"),
    mk_rule ProofRule ("bv_bitblast_step", "bv_poly_norm"),
    mk_rule RareRewrite ("bv-xor-duplicate", "bv_xor_duplicate"),
    mk_rule RareRewrite ("bv-not-idemp", "bv_not_idemp"),
    mk_rule RareRewrite ("bv-shl-by-const-0", "bv_shl_by_const_0"),
    mk_rule RareRewrite ("bv-shl-by-const-2", "bv_shl_by_const_2"),
    mk_rule RareRewrite ("bv-lshr-by-const-0", "bv_lshr_by_const_0"),
    mk_rule RareRewrite ("bv-ashr-by-const-0", "bv_ashr_by_const_0"),
    mk_rule RareRewrite ("eq-symm", "rewrite"),
    (* Native (Seq A) rules observed in the frozen cvc5 CPC corpus. *)
    mk_rule RareRewrite ("seq-eval-op", "seq_rewrite"),
    (* Complete frozen cvc5 1.3.4 Set RARE inventory.  Keep this explicit:
       an unrecorded sets-* spelling must fail registry lookup loudly. *)
    mk_rule RareRewrite ("sets-card-emp", "sets_rewrite"),
    mk_rule RareRewrite ("sets-card-singleton", "sets_rewrite"),
    mk_rule RareRewrite ("sets-card-union", "sets_rewrite"),
    mk_rule RareRewrite ("sets-card-minus", "sets_rewrite"),
    mk_rule RareRewrite ("sets-choose-singleton", "sets_rewrite"),
    mk_rule RareRewrite ("sets-eval-op", "sets_rewrite"),
    mk_rule RareRewrite ("sets-insert-elim", "sets_rewrite"),
    mk_rule RareRewrite ("sets-inter-comm", "sets_rewrite"),
    mk_rule RareRewrite ("sets-inter-member", "sets_rewrite"),
    mk_rule RareRewrite ("sets-is-empty-elim", "sets_rewrite"),
    mk_rule RareRewrite ("sets-is-singleton-elim", "sets_rewrite"),
    mk_rule RareRewrite ("sets-member-emp", "sets_rewrite"),
    mk_rule RareRewrite ("sets-member-singleton", "sets_rewrite"),
    mk_rule RareRewrite ("sets-minus-member", "sets_rewrite"),
    mk_rule RareRewrite ("sets-minus-self", "sets_rewrite"),
    mk_rule RareRewrite ("sets-subset-elim", "sets_rewrite"),
    mk_rule RareRewrite ("sets-union-comm", "sets_rewrite"),
    mk_rule RareRewrite ("sets-union-member", "sets_rewrite"),
    mk_rule RareRewrite ("exists-elim", "exists_elim"),
    mk_rule RareRewrite ("absorb", "rewrite"),
    mk_rule RareRewrite ("arith-divisible-elim", "rewrite"),
    mk_rule RareRewrite ("arith-abs-eq", "arith_abs_eq"),
    mk_rule RareRewrite ("arith-abs-int-gt", "arith_abs_int_gt"),
    mk_rule RareRewrite ("arith-geq-ite-lift", "rewrite"),
    mk_rule RareRewrite ("arith-leq-ite-lift", "rewrite"),
    mk_rule RareRewrite ("arith-div-total-zero-real", "rewrite"),
    mk_rule RareRewrite ("arith-div-total-zero-int", "rewrite"),
    mk_rule RareRewrite ("arith-int-div-total", "rewrite"),
    mk_rule RareRewrite ("arith-int-div-total-one", "rewrite"),
    mk_rule RareRewrite ("arith-int-div-total-zero", "rewrite"),
    mk_rule RareRewrite ("arith-int-div-total-neg", "rewrite"),
    mk_rule RareRewrite ("arith-int-mod-total", "rewrite"),
    mk_rule RareRewrite ("arith-int-mod-total-one", "rewrite"),
    mk_rule RareRewrite ("arith-int-mod-total-zero", "rewrite"),
    mk_rule RareRewrite ("arith-int-mod-total-neg", "rewrite"),
    mk_rule RareRewrite ("arith-mod-over-mod-1", "rewrite"),
    mk_rule RareRewrite ("arith-mod-over-mod", "rewrite"),
    mk_rule RareRewrite ("arith-mod-over-mod-mult", "rewrite"),
    mk_rule RareRewrite ("bool-double-not-elim", "rewrite"),
    mk_rule RareRewrite ("bool-and-de-morgan", "rewrite"),
    mk_rule RareRewrite ("bool-eq-false", "rewrite"),
    mk_rule RareRewrite ("bool-eq-true", "rewrite"),
    mk_rule RareRewrite ("bool-xor-comm", "rewrite"),
    mk_rule RareRewrite ("bool-xor-false", "rewrite"),
    mk_rule RareRewrite ("bool-xor-true", "rewrite"),
    mk_rule RareRewrite ("bool-impl-elim", "rewrite"),
    mk_rule RareRewrite ("bool-impl-false1", "rewrite"),
    mk_rule RareRewrite ("bool-impl-true1", "rewrite"),
    mk_rule RareRewrite ("bool-impl-true2", "rewrite"),
    mk_rule RareRewrite ("bool-eq-nrefl", "rewrite"),
    mk_rule RareRewrite ("bool-not-eq-elim2", "rewrite"),
    mk_rule RareRewrite ("bool-not-eq-elim1", "rewrite"),
    mk_rule RareRewrite ("distinct-elim", "rewrite"),
    mk_rule RareRewrite ("eq-ite-lift", "rewrite"),
    mk_rule RareRewrite ("ite-neg-branch", "ite_neg_branch"),
    mk_rule RareRewrite ("re-loop-elim", "string"),
    mk_rule RareRewrite ("str-in-re-eval", "string"),
    mk_rule RareRewrite ("str-replace-re-all-eval", "string"),
    mk_rule RareRewrite ("str-replace-re-eval", "string"),
    mk_rule RareRewrite ("bool-or-de-morgan", "rewrite"),
    mk_rule RareRewrite ("bool-implies-de-morgan", "rewrite"),
    mk_rule ProofRule ("not_implies_elim2", "not_implies_elim2"),
    mk_rule ProofRule ("not_implies_elim1", "not_implies_elim1"),
    mk_rule ProofRule ("implies_elim", "implies_elim"),
    mk_rule ProofRule ("factoring", "factoring"),
    mk_rule ProofRule ("cnf_implies_neg1", "cnf"),
    mk_rule ProofRule ("cnf_implies_neg2", "cnf"),
    mk_rule ProofRule ("cnf_implies_pos", "cnf"),
    mk_rule ProofRule ("cnf_and_pos", "cnf"),
    mk_rule ProofRule ("cnf_and_neg", "cnf"),
    mk_rule ProofRule ("cnf_or_neg", "cnf"),
    mk_rule ProofRule ("cnf_or_pos", "cnf"),
    mk_rule ProofRule ("cnf_equiv_neg1", "cnf"),
    mk_rule ProofRule ("cnf_equiv_neg2", "cnf"),
    mk_rule ProofRule ("cnf_equiv_pos1", "cnf"),
    mk_rule ProofRule ("cnf_equiv_pos2", "cnf"),
    mk_rule ProofRule ("cnf_xor_pos1", "cnf"),
    mk_rule ProofRule ("cnf_xor_pos2", "cnf"),
    mk_rule ProofRule ("cnf_xor_neg1", "cnf"),
    mk_rule ProofRule ("cnf_xor_neg2", "cnf"),
    mk_rule ProofRule ("cnf_ite_pos1", "cnf"),
    mk_rule ProofRule ("cnf_ite_pos2", "cnf"),
    mk_rule ProofRule ("cnf_ite_pos3", "cnf"),
    mk_rule ProofRule ("cnf_ite_neg1", "cnf"),
    mk_rule ProofRule ("cnf_ite_neg2", "cnf"),
    mk_rule ProofRule ("cnf_ite_neg3", "cnf"),
    mk_rule ProofRule ("not_equiv_elim1", "not_equiv_elim1"),
    mk_rule ProofRule ("not_equiv_elim2", "not_equiv_elim2"),
    mk_rule ProofRule ("equiv_elim2", "equiv_elim2"),
    mk_rule ProofRule ("equiv_elim1", "equiv_elim1"),
    mk_rule ProofRule ("arith_poly_norm", "arith_rule"),
    mk_rule ProofRule ("arith_poly_norm_rel", "arith_rel"),
    mk_rule ProofRule ("arith-elim-lt", "arith_rule"),
    mk_rule ProofRule ("arith-elim-leq", "arith_rule"),
    mk_rule ProofRule ("arith-elim-gt", "arith_rule"),
    mk_rule ProofRule ("arith-leq-norm", "arith_rule"),
    mk_rule ProofRule ("arith-eq-elim-int", "arith_rule"),
    mk_rule ProofRule ("skolem_intro", "refl"),
    mk_rule ProofRule ("skolemize", "skolemize"),
    mk_rule ProofRule ("true_elim", "true_elim"),
    mk_rule ProofRule ("true_intro", "true_intro"),
    mk_rule ProofRule ("ite_eq", "ite_eq"),
    mk_rule ProofRule ("ite_elim1", "ite_elim1"),
    mk_rule ProofRule ("ite_elim2", "ite_elim2"),
    mk_rule ProofRule ("quant-unused-vars", "quant_unused_vars"),
    mk_rule ProofRule ("quant-dt-split", "quant_dt_split"),
    mk_rule ProofRule ("quant-miniscope-and", "quant_rewrite"),
    mk_rule ProofRule ("quant-miniscope-or", "quant_rewrite"),
    mk_rule ProofRule ("quant-var-elim-eq", "quant_rewrite"),
    mk_rule ProofRule ("alpha_equiv", "alpha_equiv"),
    mk_rule ProofRule ("scope", "scope"),
    mk_rule ProofRule ("process_scope", "process_scope"),
    mk_rule ProofRule ("not_and", "not_and"),
    mk_rule ProofRule ("not_or_elim", "not_or_elim"),
    mk_rule ProofRule ("not_not_elim", "not_not_elim"),
    mk_rule ProofRule ("and_intro", "and_intro"),
    mk_rule ProofRule ("arith_mult_neg", "arith_mult_neg"),
    mk_rule ProofRule ("arith_mult_pos", "arith_mult_pos"),
    mk_rule ProofRule ("arith_mult_sign", "arith_mult_sign"),
    mk_rule ProofRule ("arith_trichotomy", "arith_trichotomy"),
    mk_rule ProofRule ("arith_reduction", "arith_reduction"),
    mk_rule ProofRule ("int_tight_lb", "int_tight_lb"),
    mk_rule ProofRule ("int_tight_ub", "int_tight_ub"),
    mk_rule ProofRule ("modus_ponens", "modus_ponens"),
    mk_rule ProofRule ("arith_sum_ub", "arith_sum_ub"),
    mk_rule ProofRule
      ("arith_mult_abs_comparison", "arith_mult_abs_comparison"),
    mk_rule ProofRule ("aci_norm", "aci_norm"),
    mk_rule RareRewrite ("arith-geq-norm1-int", "arith_rule"),
    mk_rule RareRewrite ("arith-geq-norm1-real", "arith_rule"),
    mk_rule RareRewrite ("arith-geq-tighten", "arith_rule"),
    mk_rule RareRewrite ("arith-int-geq-tighten", "arith_rule"),
    mk_rule RareRewrite ("arith-max-geq1", "arith_max_geq1"),
    mk_rule RareRewrite ("arith-min-lt2", "arith_min_lt2"),
    mk_rule RareRewrite ("ite-not-cond", "ite_not_cond"),
    mk_rule RareRewrite ("ite-true-cond", "ite_true_cond"),
    mk_rule RareRewrite ("ite-then-true", "ite_then_true"),
    mk_rule RareRewrite ("ite-then-false", "ite_then_false"),
    mk_rule RareRewrite ("ite-false-cond", "ite_false_cond"),
    mk_rule RareRewrite ("bv-nego-eliminate", "rewrite"),
    mk_rule RareRewrite ("bv-sdivo-eliminate", "rewrite"),
    mk_rule RareRewrite ("bv-sge-eliminate", "rewrite"),
    mk_rule RareRewrite ("bv-sgt-eliminate", "rewrite"),
    mk_rule RareRewrite ("bv-sle-eliminate", "rewrite"),
    mk_rule RareRewrite ("bv-uge-eliminate", "rewrite"),
    mk_rule RareRewrite ("bv-ugt-eliminate", "rewrite"),
    mk_rule RareRewrite ("bv-ule-eliminate", "rewrite"),
    mk_rule RareRewrite ("distinct-false", "rewrite"),
    mk_rule RareRewrite ("distinct-binary-elim", "rewrite"),
    (* Complete cvc5 1.3.4 datatype rewrite family from Datatypes.eo.  Each
       certificate is a closed datatype equality discharged by the shared
       checked datatype prover. *)
    mk_rule RareRewrite ("dt-inst", "datatype_eq"),
    mk_rule RareRewrite ("dt-collapse-selector", "datatype_eq"),
    mk_rule RareRewrite ("dt-collapse-tester", "datatype_eq"),
    mk_rule RareRewrite ("dt-collapse-tester-singleton", "datatype_eq"),
    mk_rule RareRewrite ("dt-cons-eq", "datatype_eq"),
    mk_rule RareRewrite ("dt-cons-eq-clash", "datatype_eq"),
    mk_rule RareRewrite ("dt-collapse-updater", "datatype_eq"),
    mk_rule RareRewrite ("dt-updater-elim", "datatype_eq")
  ] @ rare_inventory_rules

  val unknown_cvc_version = "<unknown>"

  (* Resolves a discovered cvc5 version to the tested version whose CPC
     dialect the registry replays under; see `Library`.  Callers resolve once,
     at the proof-parsing boundary, so `version_supported` below always sees a
     tested version and an unknown or untested cvc5 never fails a proof by
     itself -- it warns and replays under the nearest measured dialect. *)
  fun resolve_version version =
    Library.resolve_solver_version
      {solver = "cvc5", supported = supported_cvc_versions, version = version}

  fun version_supported version (rule : proof_rule) =
    case #version_support rule of
      AllCVCVersions => true
    | CVCVersions versions => List.exists (Lib.equal version) versions
    | CVCVersionPrefixes prefixes =>
        List.exists (fn prefix => String.isPrefix prefix version) prefixes

  fun lookup_rule version name =
    case List.find (fn (rule : proof_rule) => #name rule = name)
      proof_rule_registry of
      SOME rule => if version_supported version rule then SOME rule else NONE
    | NONE => NONE

  fun namespace_name ProofRule = "ProofRule"
    | namespace_name RareRewrite = "RARE rewrite"

  fun registry_lookup_failure version name =
    case List.find (fn (rule : proof_rule) => #name rule = name)
      proof_rule_registry of
      SOME rule => "CPC proof rule registry lookup failed: " ^
        namespace_name (#namespace rule) ^ " rule " ^ name ^
        " is not supported by cvc5 version " ^ version
    | NONE => "CPC proof rule registry lookup failed: unknown rule " ^ name ^
      " for cvc5 version " ^ version

  datatype conjunction_source =
      ParsedConjunction
    | AndIntroConjunction
    | ArithReductionConjunction
    | EqResolveConjunction
    | CongruenceConjunction

  datatype term_provenance =
      AtomicProvenance
    | ApplicationProvenance of string * term_provenance list
    | BinderProvenance of string * term_provenance
    | BinderBlockProvenance of string * int * term_provenance
    | EqualityProvenance of term_provenance * term_provenance
    | ConjunctionProvenance of
        conjunction_source * term_provenance list
    | UnavailableProvenance of string
    | AmbiguousProvenance of string

  type located_term = {
    term : Term.term,
    provenance : term_provenance
  }

  (* The Core parser right-associates exactly the operands of each source
     OR application.  Split only that recorded arity; an operand which is
     itself a disjunction remains one occurrence.  Unavailable provenance
     never authorizes flattening the already elaborated HOL term. *)
  fun source_clause_literals ({term, provenance} : located_term) =
    let
      fun operands 1 tm = SOME [tm]
        | operands count tm =
            if count < 2 then NONE
            else case Lib.total boolSyntax.dest_disj tm of
              SOME (left, right) => Option.map (fn rest => left :: rest)
                (operands (count - 1) right)
            | NONE => NONE
    in
      if Term.type_of term <> Type.bool then NONE
      else case provenance of
        ApplicationProvenance ("or", children) =>
          operands (List.length children) term
      | UnavailableProvenance _ => NONE
      | AmbiguousProvenance _ => NONE
      | AtomicProvenance =>
          if boolSyntax.is_disj term then NONE
          else SOME (if Term.aconv term boolSyntax.F then [] else [term])
      | _ => SOME [term]
    end

  type step = {
    id : string,
    conclusion : located_term option,
    rule : proof_rule,
    premises : string list,
    args : located_term list
  }

  datatype command = ASSUME of string * located_term
                   | ASSUME_PUSH of string * located_term
                   | STEP of step

  type proof = {
    commands : command list,
    cvc_version : string
  }

  fun proof_commands (proof : proof) = #commands proof
  fun proof_version (proof : proof) = #cvc_version proof

end
