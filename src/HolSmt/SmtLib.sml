(* Copyright (c) 2009-2011 Tjark Weber. All rights reserved. *)

(* Translation of HOL terms into SMT-LIB 2 format *)

structure SmtLib = struct

datatype logic_features = LogicFeatures of {
  quantifiers : bool,
  uninterpreted : bool,
  arrays : bool,
  bitvectors : bool,
  integers : bool,
  reals : bool,
  floating_point : bool,
  strings : bool,
  sequences : bool,
  sets : bool,
  bags : bool,
  datatypes : bool,
  nonlinear : bool,
  higher_order : bool
}

datatype encoding_mode =
    NativeSMTLIB
  | ConservativeEmbedding
  | Preprocessing

datatype ho_dialect = Standard27 | Z3LambdaArray

datatype standard27_apply_operator = ApplyUnderscore | ApplyAt

datatype regime = FirstOrder | HigherOrder of ho_dialect

datatype translation_record =
    RegimeSelection of {regime : regime, reason : string}
  | LogicSelection of {logic : string, reason : string,
                       features : logic_features}
  | TypeDeclaration of {hol_type : Type.hol_type, smt_name : string,
                        declaration : string}
  | DatatypeDeclaration of {hol_types : Type.hol_type list,
                            smt_names : string list, declaration : string}
  | TermDeclaration of {hol_term : Term.term, arity : int,
                        smt_name : string, domain_sorts : string list,
                        range_sort : string, declaration : string}
  | DefinitionRecord of {hol_term : Term.term, smt_name : string,
                         sort : string, definition : string}
  | EncodedSymbol of {hol_term : Term.term, smt_symbol : string,
                      arity : int}
  | HOLTheoryEncoding of {feature : string, smt_theory : string,
                          mode : encoding_mode, parse : bool,
                          typecheck : bool, translate : bool,
                          replay : bool, notes : string,
                          proof_obligation : string}

(* A proved HOL definition attached to the exact EncodedSymbol record that
   caused the corresponding SMT operator to be emitted in one translation.
   Replay consumers must obtain these through [translation_definitions], not
   from a constant-name inventory: the record is the per-run provenance key. *)
datatype emitted_definition = EmittedDefinition of {
  emitted_symbol : translation_record,
  replay_head : Term.term,
  unfolding : Thm.thm
}

type translation = {
  logic : string,
  regime : regime,
  tydict : (Type.hol_type, string) Redblackmap.dict,
  tmdict : (Term.term * int, string) Redblackmap.dict,
  (* Built lazily.  Diagnostics and checked replay force this through
     [translation_records] and [translation_definitions], respectively. *)
  records : unit -> translation_record list
}

type logic_selection_policy = {
  features : logic_features,
  inferred_logic : string,
  reason : string
} -> {logic : string, reason : string} option

(* The per-theory emitters register the exact stock HOL head that implements
   an SMT operator, together with every solver/version that accepts it.  The
   check deliberately ignores unregistered heads: this infrastructure lands
   before the Seq/Set/Bag emitters, and ordinary pre-existing translations
   must retain their behaviour. *)
type operator_availability = {
  hol_head : Term.term,
  operator : string,
  solver : string,
  versions : string list
}

val operator_availabilities = ref ([] : operator_availability list)

fun register_operator_availability availability =
  operator_availabilities := availability :: !operator_availabilities

fun clear_operator_availabilities () = operator_availabilities := []

fun term_heads tm =
  let
    fun walk tm acc =
      if Term.is_abs tm then
        walk (Lib.snd (Term.dest_abs tm)) acc
      else if Term.is_comb tm then
        let val (rator, rand) = Term.dest_comb tm in
          walk rand (walk rator acc)
        end
      else tm :: acc
  in
    walk tm []
  end

fun check_goal_operator_availability_unless ignore {solver, version}
    (assumptions, conclusion) =
  let
    val heads = List.concat (List.map term_heads (conclusion :: assumptions))
    fun occurs head = List.exists (fn tm =>
      Term.same_const tm head handle Feedback.HOL_ERR _ => false) heads
    fun available ({solver = registered_solver, versions, ...}
                   : operator_availability) =
      solver = registered_solver andalso
      (case version of NONE => false
       | SOME target_version =>
           (case Library.version_series target_version of
              NONE => false
            | SOME target_series =>
                List.exists (fn registered =>
                  Library.version_series registered = SOME target_series)
                  versions))
    fun check ({hol_head, operator, ...} : operator_availability) =
      if not (ignore hol_head) andalso occurs hol_head andalso
         not (List.exists available (List.filter
           (fn ({hol_head = candidate, operator = candidate_name, ...}
                : operator_availability) =>
             Term.same_const hol_head candidate andalso operator = candidate_name)
           (!operator_availabilities))) then
        raise Feedback.mk_HOL_ERR "SmtLib" "check_goal_operator_availability"
          ("SMT-LIB operator '" ^ operator ^ "' is unavailable for solver '" ^
           solver ^ "'" ^
           (case version of NONE => "" | SOME v => " at version '" ^ v ^ "'"))
      else
        ()
  in
    List.app check (!operator_availabilities)
  end

fun check_goal_operator_availability target =
  check_goal_operator_availability_unless (Lib.K false) target

local

  (* For successful proof reconstruction, it is important that the
     translation implemented in SmtLib_{Theories,Logics}.sml is an
     inverse of the translation implemented in this file. *)

  val ERR = Feedback.mk_HOL_ERR "SmtLib"
  val WARNING = Feedback.HOL_WARNING "SmtLib"

  val reglan_ty =
    Type.mk_thy_type {Thy = "smtstring", Tyop = "reglan", Args = []}
  val smtstr_ty =
    Type.mk_thy_type {Thy = "smtstring", Tyop = "smtstr", Args = []}
  val smtfp_ty =
    Type.mk_thy_type {
      Thy = "smtfloat", Tyop = "smtfp", Args = [Type.alpha, Type.beta]}
  val smt_rounding_ty =
    Type.mk_thy_type {
      Thy = "smtfloat", Tyop = "smt_rounding", Args = []}

  fun smtstring_const name =
    Term.prim_mk_const {Thy = "smtstring", Name = name}

  fun numeric_type_width ty = fcpSyntax.dest_numeric_type ty

  fun smtfp_format ty =
    let
      val {Thy, Tyop, Args, ...} = Type.dest_thy_type ty
      val (significand_ty, exponent_ty) =
        case Args of
          [significand_ty, exponent_ty] =>
            (significand_ty, exponent_ty)
        | _ => raise ERR "smtfp_format" "smtfp must have two type arguments"
      val _ =
        if Thy = "smtfloat" andalso Tyop = "smtfp" then ()
        else raise ERR "smtfp_format" "not an smtfp type"
      val eb = numeric_type_width exponent_ty
      val sb = Arbnum.plus1 (numeric_type_width significand_ty)
      val two = Arbnum.fromInt 2
      val _ =
        if Arbnum.compare (eb, two) = LESS then
          raise ERR "smtfp_format"
            "exponent width eb must be at least 2"
        else
          ()
      val _ =
        if Arbnum.compare (sb, two) = LESS then
          raise ERR "smtfp_format"
            "significand width sb must be at least 2"
        else
          ()
    in
      (eb, sb)
    end

  fun smtfp_sort ty =
    let val (eb, sb) = smtfp_format ty in
      "(_ FloatingPoint " ^ Arbnum.toString eb ^ " " ^
      Arbnum.toString sb ^ ")"
    end

  (* (HOL type, a function that maps the type to its SMT-LIB sort name) *)
  val builtin_types = List.foldl
    (fn ((ty, x), net) => TypeNet.insert (net, ty, x)) TypeNet.empty [
    (Type.bool, Lib.K "Bool"),
    (intSyntax.int_ty, Lib.K "Int"),
    (realSyntax.real_ty, Lib.K "Real"),
    (* HOL's own :string (a char list) is deliberately absent: string content
       reaches SMT-LIB only through the str_inj images that
       HOL_STRING_TO_SMT_CONV produces, and those have type smtstr. *)
    (smtstr_ty, Lib.K "String"),
    (reglan_ty, Lib.K "(RegLan String)"),
    (* The canonical-NaN subtype has exactly the SMT FloatingPoint universe.
       Raw binary_ieee float records deliberately have no entry here. *)
    (smtfp_ty, smtfp_sort),
    (smt_rounding_ty, Lib.K "RoundingMode"),
    (* bit-vector types *)
    (wordsSyntax.mk_word_type Type.alpha, fn ty =>
      "(_ BitVec " ^ Arbnum.toString
        (fcpSyntax.dest_numeric_type (wordsSyntax.dest_word_type ty)) ^ ")")
   ]

  val apfst_K = Lib.apfst o Lib.K
  val int_emod_tm = Term.prim_mk_const {Thy="integer", Name="emod"}
  val str_inj_tm = smtstring_const "str_inj"
  val smtfp_intro_tm =
    Term.prim_mk_const {Thy = "smtfloat", Name = "smtfp_intro"}
  val smtstr_char_tm = smtstring_const "smtstr_char"
  val smtstr_concat_tm = smtstring_const "smtstr_concat"
  val smtstr_prefixof_tm = smtstring_const "smtstr_prefixof"
  val smtstr_lt_tm = smtstring_const "smtstr_lt"
  val smtstr_le_tm = smtstring_const "smtstr_le"

  fun smtfloat_const name =
    Term.prim_mk_const {Thy = "smtfloat", Name = name}

  type native_fp_info = {
    hol_name : string,
    smt_name : string
  }

  val native_fp_infos : native_fp_info list = [
    {hol_name = "RNE", smt_name = "roundNearestTiesToEven"},
    {hol_name = "RNA", smt_name = "roundNearestTiesToAway"},
    {hol_name = "RTP", smt_name = "roundTowardPositive"},
    {hol_name = "RTN", smt_name = "roundTowardNegative"},
    {hol_name = "RTZ", smt_name = "roundTowardZero"},
    {hol_name = "smtfp_bits", smt_name = "fp"},
    {hol_name = "smtfp_add", smt_name = "fp.add"},
    {hol_name = "smtfp_sub", smt_name = "fp.sub"},
    {hol_name = "smtfp_mul", smt_name = "fp.mul"},
    {hol_name = "smtfp_div", smt_name = "fp.div"},
    {hol_name = "smtfp_fma", smt_name = "fp.fma"},
    {hol_name = "smtfp_sqrt", smt_name = "fp.sqrt"},
    {hol_name = "smtfp_round_to_integral",
     smt_name = "fp.roundToIntegral"},
    {hol_name = "smtfp_rem", smt_name = "fp.rem"},
    {hol_name = "smtfp_min", smt_name = "fp.min"},
    {hol_name = "smtfp_max", smt_name = "fp.max"},
    {hol_name = "smtfp_abs", smt_name = "fp.abs"},
    {hol_name = "smtfp_neg", smt_name = "fp.neg"},
    {hol_name = "smtfp_le", smt_name = "fp.leq"},
    {hol_name = "smtfp_lt", smt_name = "fp.lt"},
    {hol_name = "smtfp_ge", smt_name = "fp.geq"},
    {hol_name = "smtfp_gt", smt_name = "fp.gt"},
    {hol_name = "smtfp_eq", smt_name = "fp.eq"},
    {hol_name = "smtfp_is_normal", smt_name = "fp.isNormal"},
    {hol_name = "smtfp_is_subnormal", smt_name = "fp.isSubnormal"},
    {hol_name = "smtfp_is_zero", smt_name = "fp.isZero"},
    {hol_name = "smtfp_is_infinite", smt_name = "fp.isInfinite"},
    {hol_name = "smtfp_is_nan", smt_name = "fp.isNaN"},
    {hol_name = "smtfp_is_negative", smt_name = "fp.isNegative"},
    {hol_name = "smtfp_is_positive", smt_name = "fp.isPositive"},
    {hol_name = "smtfp_to_real", smt_name = "fp.to_real"}
  ]

  val native_fp_special_infos : native_fp_info list = [
    {hol_name = "smtfp_pzero", smt_name = "+zero"},
    {hol_name = "smtfp_nzero", smt_name = "-zero"},
    {hol_name = "smtfp_pinf", smt_name = "+oo"},
    {hol_name = "smtfp_ninf", smt_name = "-oo"},
    {hol_name = "smtfp_nan", smt_name = "NaN"}
  ]

  val native_fp_conversion_names = [
    "smtfp_from_ieee_bv", "smtfp_to_fp", "smtfp_from_real",
    "smtfp_from_sbv", "smtfp_from_ubv", "smtfp_to_ubv",
    "smtfp_to_sbv"
  ]

  val native_fp_names =
    List.map #hol_name (native_fp_infos @ native_fp_special_infos) @
    native_fp_conversion_names

  type native_string_info = {
    hol_name : string,
    smt_name : string
  }

  val native_string_infos : native_string_info list = [
    {hol_name = "smtstr_concat", smt_name = "str.++"},
    {hol_name = "smtstr_len", smt_name = "str.len"},
    {hol_name = "smtstr_substr", smt_name = "str.substr"},
    {hol_name = "smtstr_update", smt_name = "str.update"},
    {hol_name = "smtstr_rev", smt_name = "str.rev"},
    {hol_name = "smtstr_at", smt_name = "str.at"},
    {hol_name = "smtstr_prefixof", smt_name = "str.prefixof"},
    {hol_name = "smtstr_suffixof", smt_name = "str.suffixof"},
    {hol_name = "smtstr_contains", smt_name = "str.contains"},
    {hol_name = "smtstr_indexof", smt_name = "str.indexof"},
    {hol_name = "smtstr_lt", smt_name = "str.<"},
    {hol_name = "smtstr_le", smt_name = "str.<="},
    {hol_name = "smtstr_char", smt_name = "char"},
    {hol_name = "smtstr_replace", smt_name = "str.replace"},
    {hol_name = "smtstr_replace_all", smt_name = "str.replace_all"},
    {hol_name = "smtstr_replace_re", smt_name = "str.replace_re"},
    {hol_name = "smtstr_replace_re_all", smt_name = "str.replace_re_all"},
    {hol_name = "smtstr_is_digit", smt_name = "str.is_digit"},
    {hol_name = "smtstr_to_code", smt_name = "str.to_code"},
    {hol_name = "smtstr_from_code", smt_name = "str.from_code"},
    {hol_name = "smtstr_to_int", smt_name = "str.to_int"},
    {hol_name = "smtstr_from_int", smt_name = "str.from_int"},
    {hol_name = "reglan_to_re", smt_name = "str.to_re"},
    {hol_name = "smt_in_re", smt_name = "str.in_re"},
    {hol_name = "reglan_none", smt_name = "re.none"},
    {hol_name = "reglan_all", smt_name = "re.all"},
    {hol_name = "reglan_allchar", smt_name = "re.allchar"},
    {hol_name = "reglan_concat", smt_name = "re.++"},
    {hol_name = "reglan_union", smt_name = "re.union"},
    {hol_name = "reglan_inter", smt_name = "re.inter"},
    {hol_name = "reglan_diff", smt_name = "re.diff"},
    {hol_name = "reglan_comp", smt_name = "re.comp"},
    {hol_name = "reglan_star", smt_name = "re.*"},
    {hol_name = "reglan_plus", smt_name = "re.+"},
    {hol_name = "reglan_opt", smt_name = "re.opt"},
    {hol_name = "reglan_range", smt_name = "re.range"},
    {hol_name = "reglan_power", smt_name = "re.^"},
    {hol_name = "reglan_loop", smt_name = "re.loop"}
  ]

  fun native_string_info tm =
    if Term.is_const tm then
      let
        val {Thy, Name, ...} = Term.dest_thy_const tm
      in
        if Thy = "smtstring" then
          List.find
            (fn {hol_name, ...} : native_string_info =>
              hol_name = Name)
            native_string_infos
        else
          NONE
      end
    else
      NONE

  fun is_native_string_const tm = Option.isSome (native_string_info tm)

  (* Recursive failures must bypass the recognizer exception cascade: once a
     term's shape is known, an error in its body is the real diagnostic. *)
  exception NestedTranslation of exn

  fun numeral_string function_name tm =
    Arbnum.toString (numSyntax.dest_numeral tm)
    handle Feedback.HOL_ERR _ =>
      raise ERR function_name "expected a numeral index"

  fun hexadecimal_string function_name tm =
    let
      val value =
        numSyntax.dest_numeral tm
        handle Feedback.HOL_ERR _ =>
          raise ERR function_name "expected a numeral character index"
    in
      SmtLib_String_Literal.hex_num
        (SmtLib_String_Literal.check_code_point "character index" value)
      handle SmtLib_String_Literal.InvalidCodePoint detail =>
        raise ERR function_name detail
    end

  fun indexed_char_encoding (_, args) =
    (SmtLib_Theories.one_arg
       (fn code =>
         ("(_ char #x" ^
          hexadecimal_string "<builtin_symbols.smtstr_char>" code ^ ")",
          []))
       args)
    handle e as Feedback.HOL_ERR _ => raise NestedTranslation e

  fun indexed_power_encoding (_, args) =
    SmtLib_Theories.two_args
      (fn (regex, power) =>
        ("(_ re.^ " ^
         numeral_string "<builtin_symbols.reglan_power>" power ^ ")",
         [regex]))
      args

  fun indexed_loop_encoding (_, args) =
    SmtLib_Theories.three_args
      (fn (regex, lower, upper) =>
        ("(_ re.loop " ^
         numeral_string "<builtin_symbols.reglan_loop>" lower ^ " " ^
         numeral_string "<builtin_symbols.reglan_loop>" upper ^ ")",
         [regex]))
      args

  fun dest_injected_string tm =
    let
      val (inject, string) = Term.dest_comb tm
      val _ =
        if Term.same_const inject str_inj_tm then ()
        else raise ERR "dest_injected_string" "not str_inj"
    in
      string
    end

  fun is_injected_string tm = Lib.can dest_injected_string tm

  fun dest_injected_float tm =
    let
      val (inject, float) = Term.dest_comb tm
      val _ =
        if Term.same_const inject smtfp_intro_tm then ()
        else raise ERR "dest_injected_float" "not smtfp_intro"
    in
      float
    end

  fun is_injected_float tm = Lib.can dest_injected_float tm

  fun injected_string_operator tm =
    if Term.same_const tm smtstr_concat_tm then "str.++"
    else if Term.same_const tm smtstr_prefixof_tm then "str.prefixof"
    else if Term.same_const tm smtstr_lt_tm then "str.<"
    else if Term.same_const tm smtstr_le_tm then "str.<="
    else raise ERR "injected_string_operator" "not an injection operator"

  fun dest_injected_string_operation tm =
    let
      val (rator, rands) = boolSyntax.strip_comb tm
      val name = injected_string_operator rator
      val _ =
        if List.length rands = 2 then ()
        else raise ERR "dest_injected_string_operation" "wrong arity"
    in
      (name, rands)
    end

  fun is_injected_string_expression tm =
    is_injected_string tm orelse
    (case Lib.total dest_injected_string_operation tm of
       SOME ("str.++", rands) =>
         List.all is_injected_string_expression rands
     | _ => false)

  fun is_injected_string_operation tm =
    case Lib.total dest_injected_string_operation tm of
      SOME (_, rands) => List.all is_injected_string_expression rands
    | NONE => false

  fun mk_int_emod (dividend, divisor) =
    Term.list_mk_comb (int_emod_tm, [dividend, divisor])

  fun literal_int_divides_mod_eq (divisor, dividend) =
    if intSyntax.is_int_literal divisor andalso
       Arbint.> (intSyntax.int_of_term divisor, Arbint.zero) then
      [mk_int_emod (dividend, divisor), intSyntax.term_of_int Arbint.zero]
    else
      raise ERR "<builtin_symbols.int_divides>" "not a positive literal divisor"

  (* returns true iff 'ty' is a word type that is not fixed-width *)
  fun is_non_numeric_word_type ty =
    not (fcpSyntax.is_numeric_type (wordsSyntax.dest_word_type ty))
      handle Feedback.HOL_ERR _ => false

  (* make sure that all word types in 't' are of fixed width; return 's' *)
  fun apfst_fixed_width s =
    Lib.apfst (fn t =>
      let
        val (domtys, rngty) = boolSyntax.strip_fun (Term.type_of t)
      in
        if List.exists is_non_numeric_word_type (rngty :: domtys) then
          raise ERR ("<builtin_symbols." ^ s ^ ">")
            "not a fixed-width word type"
        else
          s
      end)

  (* (HOL term, a function that maps a pair (rator, rands) to an
     SMT-LIB symbol and a list of remaining (still-to-be-encoded)
     argument terms) *)
  type builtin_encoding =
    (Term.term * Term.term list) -> (string * Term.term list)

  (* Native smtstringTheory UnicodeStrings and RegLan surface, derived from
     'native_string_infos' so that the SMT name of an operator is recorded
     in one table only. *)
  val native_string_encodings : (Term.term * builtin_encoding) list =
    List.map
      (fn {hol_name, smt_name} : native_string_info =>
        (smtstring_const hol_name,
         case hol_name of
           "smtstr_char" => indexed_char_encoding
         | "reglan_power" => indexed_power_encoding
         | "reglan_loop" => indexed_loop_encoding
         | _ => apfst_K smt_name))
      native_string_infos

  fun instantiated_result_type tm =
    Lib.snd (boolSyntax.strip_fun (Term.type_of tm))

  fun indexed_fp_name operator tm =
    let val (eb, sb) = smtfp_format (instantiated_result_type tm) in
      "(_ " ^ operator ^ " " ^ Arbnum.toString eb ^ " " ^
      Arbnum.toString sb ^ ")"
    end

  fun fp_special_encoding name (tm, args) =
    if List.null args then
      (indexed_fp_name name tm, [])
    else
      raise ERR "fp_special_encoding"
        "floating-point special takes no arguments"

  fun fp_target_encoding operator (tm, args) =
    (indexed_fp_name operator tm, args)

  fun fp_to_bv_encoding operator (tm, args) =
    let
      val result_ty = instantiated_result_type tm
      val width = numeric_type_width (wordsSyntax.dest_word_type result_ty)
    in
      ("(_ " ^ operator ^ " " ^ Arbnum.toString width ^ ")", args)
    end

  val native_fp_encodings : (Term.term * builtin_encoding) list =
    List.map
      (fn {hol_name, smt_name} : native_fp_info =>
        (smtfloat_const hol_name, apfst_K smt_name))
      native_fp_infos @
    List.map
      (fn {hol_name, smt_name} : native_fp_info =>
        (smtfloat_const hol_name, fp_special_encoding smt_name))
      native_fp_special_infos @ [
    (smtfloat_const "smtfp_from_ieee_bv", fp_target_encoding "to_fp"),
    (smtfloat_const "smtfp_to_fp", fp_target_encoding "to_fp"),
    (smtfloat_const "smtfp_from_real", fp_target_encoding "to_fp"),
    (smtfloat_const "smtfp_from_sbv", fp_target_encoding "to_fp"),
    (smtfloat_const "smtfp_from_ubv",
      fp_target_encoding "to_fp_unsigned"),
    (smtfloat_const "smtfp_to_ubv", fp_to_bv_encoding "fp.to_ubv"),
    (smtfloat_const "smtfp_to_sbv", fp_to_bv_encoding "fp.to_sbv")
  ]

  val builtin_symbol_encodings = [
    (* Core *)
    (boolSyntax.T, apfst_K "true"),
    (boolSyntax.F, apfst_K "false"),
    (boolSyntax.negation, apfst_K "not"),
    (boolSyntax.implication, apfst_K "=>"),
    (boolSyntax.conjunction, apfst_K "and"),
    (boolSyntax.disjunction, apfst_K "or"),
    (Term.prim_mk_const {Thy="HolSmt", Name="xor"}, apfst_K "xor"),
    (boolSyntax.equality, apfst_K "="),
    (* The parser represents SMT-LIB Core.distinct as ALL_DISTINCT over a
       HOL list.  The list is only an internal n-ary encoding: emit its
       elements as the direct SMT-LIB arguments rather than translating the
       wrapper as a datatype value.  SMT-LIB requires at least two arguments;
       the corresponding shorter HOL lists are vacuously distinct. *)
    (listSyntax.all_distinct_tm, fn (_, ts) =>
      SmtLib_Theories.one_arg (fn list_tm =>
        case Lib.fst (listSyntax.dest_list list_tm) of
          elements as _ :: _ :: _ => ("distinct", elements)
        | _ => ("true", [])) ts),
    (boolSyntax.conditional, apfst_K "ite"),
    (* UnicodeStrings symbols are reached only through the smtstr operators
       appended from 'native_string_encodings'.  Encoding HOL's STRCAT and
       friends directly would emit str.* applied to arguments whose sort is
       no longer String (see 'builtin_types'). *)
    (* Reals_Ints *)
    (* numerals (excluding 'intSyntax.negate_tm') *)
    (Term.mk_var ("x", intSyntax.int_ty), Lib.apfst (fn tm =>
      if intSyntax.is_int_literal tm andalso not (intSyntax.is_negated tm) then
        let
          val i = intSyntax.int_of_term tm
          val s = Arbint.toString (Arbint.abs i)
          val s = String.substring (s, 0, String.size s - 1)
        in
          if Arbint.< (i, Arbint.zero) then
            "(- " ^ s ^ ")"
          else
            s
        end
      else
        raise ERR "<builtin_symbols.x:int>" "not a numeral (negated?)")),
    (intSyntax.negate_tm, apfst_K "-"),
    (intSyntax.Num_tm, apfst_K "abs"),
    (intSyntax.minus_tm, apfst_K "-"),
    (intSyntax.plus_tm, apfst_K "+"),
    (intSyntax.mult_tm, apfst_K "*"),
    (Term.prim_mk_const {Thy="integer", Name="ediv"}, apfst_K "div"),
    (Term.prim_mk_const {Thy="integer", Name="emod"}, apfst_K "mod"),
    (intSyntax.absval_tm, apfst_K "abs"),
    (intSyntax.divides_tm, fn (_, ts) =>
      SmtLib_Theories.two_args (fn (divisor, dividend) =>
        ("=", literal_int_divides_mod_eq (divisor, dividend))) ts),
    (intSyntax.leq_tm, apfst_K "<="),
    (intSyntax.less_tm, apfst_K "<"),
    (intSyntax.geq_tm, apfst_K ">="),
    (intSyntax.greater_tm, apfst_K ">"),
    (* decimals (excluding 'realSyntax.negate_tm') *)
    (Term.mk_var ("x", realSyntax.real_ty), Lib.apfst (fn tm =>
      if realSyntax.is_real_literal tm andalso not (realSyntax.is_negated tm)
          then
        let
          val i = realSyntax.int_of_term tm
          val s = Arbint.toString (Arbint.abs i)
          val s = String.substring (s, 0, String.size s - 1)
          val s = s ^ ".0"
        in
          if Arbint.< (i, Arbint.zero) then
            "(- " ^ s ^ ")"
          else
            s
        end
      else
        raise ERR "<builtin_symbols.x:real>" "not a decimal (negated?)")),
    (realSyntax.negate_tm, apfst_K "-"),
    (realSyntax.minus_tm, apfst_K "-"),
    (realSyntax.plus_tm, apfst_K "+"),
    (realSyntax.mult_tm, apfst_K "*"),
    (Term.prim_mk_const {Thy="HolSmt", Name="smt_rdiv"}, apfst_K "/"),
    (realSyntax.leq_tm, apfst_K "<="),
    (realSyntax.less_tm, apfst_K "<"),
    (realSyntax.geq_tm, apfst_K ">="),
    (realSyntax.greater_tm, apfst_K ">"),
    (intrealSyntax.real_of_int_tm, apfst_K "to_real"),
    (intrealSyntax.INT_FLOOR_tm, apfst_K "to_int"),
    (* SMT-LIB has no ceiling operator, but HOL's integer ceiling has the
       closed-form definition ceil r = -floor (-r).  Encode that expression
       directly instead of introducing a quantified defining axiom. *)
    (intrealSyntax.INT_CEILING_tm, fn (_, ts) =>
      SmtLib_Theories.one_arg (fn r =>
        ("-", [Term.mk_comb (intrealSyntax.INT_FLOOR_tm,
          Term.mk_comb (realSyntax.negate_tm, r))])) ts),
    (intrealSyntax.is_int_tm, apfst_K "is_int"),
    (* bit-vector constants *)
    (Term.mk_var ("x", wordsSyntax.mk_word_type Type.alpha), Lib.apfst (fn tm =>
      if wordsSyntax.is_word_literal tm then
        let
          val value = wordsSyntax.dest_word_literal tm
          val width = fcpSyntax.dest_numeric_type (wordsSyntax.dim_of tm)
        in
          "(_ bv" ^ Arbnum.toString value ^ " " ^ Arbnum.toString width ^ ")"
        end
      else
        raise ERR "<builtin_symbols.x:'a word>" "not a word literal")),
    (wordsSyntax.word_concat_tm, fn (t, ts) =>
      SmtLib_Theories.two_args (fn (w1, w2) =>
        let
          (* make sure that the result in HOL has the expected width *)
          val dim1 = fcpSyntax.dest_numeric_type (wordsSyntax.dim_of w1)
          val dim2 = fcpSyntax.dest_numeric_type (wordsSyntax.dim_of w2)
          val rngty = Lib.snd (boolSyntax.strip_fun (Term.type_of t))
          val rngdim = fcpSyntax.dest_numeric_type
            (wordsSyntax.dest_word_type rngty)
          val _ = if rngdim = Arbnum.+ (dim1, dim2) then
              ()
            else (
              if !Library.trace > 0 then
                WARNING "translate_term" "word_concat: wrong result type"
              else
                ();
              raise ERR "<builtin_symbols.word_concat_tm>" "wrong result type"
            )
        in
          ("concat", ts)
        end) ts),
    (wordsSyntax.word_extract_tm, fn (t, ts) =>
      SmtLib_Theories.three_args (fn (i, j, w) =>
        let
          (* make sure that j <= i < dim(w) *)
          val i = numSyntax.dest_numeral i
          val j = numSyntax.dest_numeral j
          val dim = fcpSyntax.dest_numeric_type (wordsSyntax.dim_of w)
          val _ = if Arbnum.<= (j, i) then
              ()
            else (
              if !Library.trace > 0 then
                WARNING "translate_term"
                  "word_extract: second index larger than first"
              else
                ();
              raise ERR "<builtin_symbols.word_extract_tm>"
                "second index larger than first"
            )
          val _ = if Arbnum.< (i, dim) then
              ()
            else (
              if !Library.trace > 0 then
                WARNING "translate_term" "word_extract: first index too large"
              else
                ();
              raise ERR "<builtin_symbols.word_extract_tm>"
                "first index too large"
            )
          (* make sure that the result in HOL has the expected width *)
          val rngty = Lib.snd (boolSyntax.strip_fun (Term.type_of t))
          val rngdim = fcpSyntax.dest_numeric_type
            (wordsSyntax.dest_word_type rngty)
          val _ = if rngdim = Arbnum.+ (Arbnum.- (i, j), Arbnum.one) then
              ()
            else (
              if !Library.trace > 0 then
                WARNING "translate_term" "word_extract: wrong result type"
              else
                ();
              raise ERR "<builtin_symbols.word_extract_tm>" "wrong result type"
            )
        in
          ("(_ extract " ^ Arbnum.toString i ^ " " ^ Arbnum.toString j ^ ")",
            [w])
        end) ts),
    (wordsSyntax.word_1comp_tm, apfst_fixed_width "bvnot"),
    (wordsSyntax.word_and_tm, apfst_fixed_width "bvand"),
    (wordsSyntax.word_or_tm, apfst_fixed_width "bvor"),
    (wordsSyntax.word_nand_tm, apfst_fixed_width "bvnand"),
    (wordsSyntax.word_nor_tm, apfst_fixed_width "bvnor"),
    (wordsSyntax.word_xor_tm, apfst_fixed_width "bvxor"),
    (wordsSyntax.word_xnor_tm, apfst_fixed_width "bvxnor"),
    (wordsSyntax.word_2comp_tm, apfst_fixed_width "bvneg"),
    (wordsSyntax.word_compare_tm, apfst_fixed_width "bvcomp"),
    (wordsSyntax.word_add_tm, apfst_fixed_width "bvadd"),
    (wordsSyntax.word_sub_tm, apfst_fixed_width "bvsub"),
    (wordsSyntax.word_mul_tm, apfst_fixed_width "bvmul"),
    (wordsSyntax.word_quot_tm, apfst_fixed_width "bvsdiv"),
    (wordsSyntax.word_rem_tm, apfst_fixed_width "bvsrem"),
    (integer_wordSyntax.word_smod_tm, apfst_fixed_width "bvsmod"),
    (wordsSyntax.word_div_tm, apfst_fixed_width "bvudiv"),
    (wordsSyntax.word_mod_tm, apfst_fixed_width "bvurem"),
    (* shift operations with two bit-vector arguments; the corresponding HOL
       shift operations that take a numeral as their second argument are not
       supported in SMT-LIB *)
    (wordsSyntax.word_lsl_bv_tm, apfst_fixed_width "bvshl"),
    (wordsSyntax.word_lsr_bv_tm, apfst_fixed_width "bvlshr"),
    (wordsSyntax.word_asr_bv_tm, apfst_fixed_width "bvashr"),
    (wordsSyntax.word_replicate_tm, fn (t, ts) =>
      SmtLib_Theories.two_args (fn (n, w) =>
        let
          val n = numSyntax.dest_numeral n
          (* make sure that the result in HOL has the expected width *)
          val dim = fcpSyntax.dest_numeric_type (wordsSyntax.dim_of w)
          val rngty = Lib.snd (boolSyntax.strip_fun (Term.type_of t))
          val rngdim = fcpSyntax.dest_numeric_type
            (wordsSyntax.dest_word_type rngty)
          val _ = if rngdim = Arbnum.* (n, dim) then
              ()
            else (
              if !Library.trace > 0 then
                WARNING "translate_term" "word_replicate: wrong result type"
              else
                ();
              raise ERR "<builtin_symbols.word_replicate_tm>"
                "wrong result type"
            )
        in
          ("(_ repeat " ^ Arbnum.toString n ^ ")", [w])
        end) ts),
    (wordsSyntax.w2w_tm, fn (t, ts) =>
      SmtLib_Theories.one_arg (fn w =>
        let
          (* make sure that the result in HOL is at least as long as 'w' *)
          val dim = fcpSyntax.dest_numeric_type (wordsSyntax.dim_of w)
          val rngty = Lib.snd (boolSyntax.strip_fun (Term.type_of t))
          val rngdim = fcpSyntax.dest_numeric_type
            (wordsSyntax.dest_word_type rngty)
          val _ = if Arbnum.>= (rngdim, dim) then
              ()
            else (
              if !Library.trace > 0 then
                WARNING "translate_term" "w2w: result type too short"
              else
                ();
              raise ERR "<builtin_symbols.w2w_tm>" "result type too short"
            )
          val n = Arbnum.- (rngdim, dim)
        in
          ("(_ zero_extend " ^ Arbnum.toString n ^ ")", [w])
        end) ts),
    (wordsSyntax.sw2sw_tm, fn (t, ts) =>
      SmtLib_Theories.one_arg (fn w =>
        let
          (* make sure that the result in HOL is at least as long as 'w' *)
          val dim = fcpSyntax.dest_numeric_type (wordsSyntax.dim_of w)
          val rngty = Lib.snd (boolSyntax.strip_fun (Term.type_of t))
          val rngdim = fcpSyntax.dest_numeric_type
            (wordsSyntax.dest_word_type rngty)
          val _ = if Arbnum.>= (rngdim, dim) then
              ()
            else (
              if !Library.trace > 0 then
                WARNING "translate_term" "sw2sw: result type too short"
              else
                ();
              raise ERR "<builtin_symbols.sw2sw_tm>" "result type too short"
            )
          val n = Arbnum.- (rngdim, dim)
        in
          ("(_ sign_extend " ^ Arbnum.toString n ^ ")", [w])
        end) ts),
    (* rotation by a numeral; the corresponding HOL rotation operations that
       take two bit-vector arguments are not supported in SMT-LIB *)
    (wordsSyntax.word_rol_tm, fn (t, ts) =>
      (
        apfst_fixed_width "rotate_left" (t, ());
        SmtLib_Theories.two_args (fn (w, n) =>
          ("(_ rotate_left " ^ Arbnum.toString (numSyntax.dest_numeral n)
            ^ ")", [w])) ts
      )),
    (wordsSyntax.word_ror_tm, fn (t, ts) =>
      (
        apfst_fixed_width "rotate_right" (t, ());
        SmtLib_Theories.two_args (fn (w, n) =>
          ("(_ rotate_right " ^ Arbnum.toString (numSyntax.dest_numeral n)
            ^ ")", [w])) ts
      )),
    (wordsSyntax.word_lo_tm, apfst_fixed_width "bvult"),
    (wordsSyntax.word_ls_tm, apfst_fixed_width "bvule"),
    (wordsSyntax.word_hi_tm, apfst_fixed_width "bvugt"),
    (wordsSyntax.word_hs_tm, apfst_fixed_width "bvuge"),
    (wordsSyntax.word_lt_tm, apfst_fixed_width "bvslt"),
    (wordsSyntax.word_le_tm, apfst_fixed_width "bvsle"),
    (wordsSyntax.word_gt_tm, apfst_fixed_width "bvsgt"),
    (wordsSyntax.word_ge_tm, apfst_fixed_width "bvsge")
  ] @ native_fp_encodings @ native_string_encodings

  val builtin_symbols =
    List.foldl (Lib.uncurry Net.insert) Net.empty builtin_symbol_encodings

  (* The (theory, name) pairs of the constant-headed builtin symbols, so that
     `has_ranked_semantics` can test membership in O(log n) rather than
     scanning `builtin_symbol_encodings` with `Term.same_const` per node. *)
  val builtin_const_names =
    List.foldl
      (fn ((builtin, _), acc) =>
        if Term.is_const builtin then
          let val {Thy, Name, ...} = Term.dest_thy_const builtin
          in Redblackset.add (acc, (Thy, Name)) end
        else acc)
      (Redblackset.empty (Lib.pair_compare (String.compare, String.compare)))
      builtin_symbol_encodings

  (* The declared arity of a constant depends only on its (theory, name), and
     'translate_term' asks for the same rator up to four times per application
     node; cache the symbol-table lookup and the type traversal. *)
  val declared_const_arities = ref (Redblackmap.mkDict
    (Lib.pair_compare (String.compare, String.compare)) :
      (string * string, int) Redblackmap.dict)

  fun declared_const_arity c =
    let
      val {Thy, Name, ...} = Term.dest_thy_const c
    in
      case Redblackmap.peek (!declared_const_arities, (Thy, Name)) of
        SOME arity => arity
      | NONE =>
        let
          val generic = Term.prim_mk_const {Thy = Thy, Name = Name}
          val (doms, _) = boolSyntax.strip_fun (Term.type_of generic)
          val arity = List.length doms
        in
          declared_const_arities :=
            Redblackmap.insert (!declared_const_arities, (Thy, Name), arity);
          arity
        end
    end

  (* SMT-LIB type and function names are uniformly generated as "tN"
     and "vN", respectively, where N is a number. Prefixes must be
     distinct. *)

  val ty_prefix = "t"  (* for types *)
  val tm_prefix = "v"  (* for terms *)
  val bv_prefix = "b"  (* for bound variables *)

  fun first_success f [] = NONE
    | first_success f (x :: xs) =
      SOME (f x) handle _ => first_success f xs

  fun has_type_builtin ty =
    Option.isSome (first_success (fn (_, f) => f ty)
      (TypeNet.match (builtin_types, ty)))

  fun is_function_type ty = Lib.can Type.dom_rng ty

  (* Lists are the native model of SMT sequences, except for HOL strings.
     The latter must retain Phase 4's str_inj/smtstr route rather than being
     silently reclassified as arbitrary (Seq Char) content. *)
  fun is_native_sequence_type ty =
    listSyntax.is_list_type ty andalso
    Type.compare (ty, stringSyntax.string_ty) <> EQUAL

  (* Checked Seq replay is introduced by TASK_18.  Until then, proof
     requests retain the old datatype encoding while oracle emission uses the
     native surface. *)
  val current_native_sequence_emission = ref true

  (* Some collection encodings introduce quantifiers which have no HOL binder
     in the source goal.  Every such emitter must construct its SMT-LIB forall
     through this helper, so logic selection and solver command policy observe
     the syntax that was actually emitted. *)
  val current_generated_forall_emissions = ref 0

  fun generated_forall declarations body =
    (current_generated_forall_emissions :=
       !current_generated_forall_emissions + 1;
     "(forall (" ^ String.concatWith " " declarations ^ ") " ^ body ^ ")")

  (* Snapshot a translation-context cell now; the returned thunk puts it
     back.  Each cell then costs one list entry rather than a declaration,
     a save and a restore that must be kept in step. *)
  fun save_cell r = let val saved = !r in fn () => r := saved end

  fun restore_cells restorers = List.app (fn f => f ()) restorers

  fun sequence_element_type tm =
    if is_native_sequence_type (Term.type_of tm) then
      listSyntax.dest_list_type (Term.type_of tm)
    else
      raise ERR "sequence_element_type" "not a native sequence term"

  fun smt_sort_of_type regime tydict ty =
    if !current_native_sequence_emission andalso
       is_native_sequence_type ty then
      "(Seq " ^ smt_sort_of_type regime tydict
        (listSyntax.dest_list_type ty) ^ ")"
    else if is_function_type ty then
      (case regime of
         HigherOrder Standard27 =>
           let
             val (doms, rng) = boolSyntax.strip_fun ty
             val names = List.map (smt_sort_of_type regime tydict)
               (doms @ [rng])
           in
             "(-> " ^ String.concatWith " " names ^ ")"
           end
       | _ =>
           let
             val (dom, rng) = Type.dom_rng ty
           in
             "(Array " ^ smt_sort_of_type regime tydict dom ^ " " ^
             smt_sort_of_type regime tydict rng ^ ")"
           end)
    else
      case first_success (fn (_, f) => f ty)
          (TypeNet.match (builtin_types, ty)) of
        SOME name => name
      | NONE => Redblackmap.find (tydict, ty)

  (* structural term/type helpers shared via Library (see Library.sml) *)
  val type_contains = Library.type_contains
  val type_contains_word = Library.type_contains_word
  val type_contains_int = Library.type_contains_int
  val type_contains_real = Library.type_contains_real
  fun type_has_name thy tyop ty =
    let val {Thy, Tyop, ...} = Type.dest_thy_type ty in
      Thy = thy andalso Tyop = tyop
    end
    handle Feedback.HOL_ERR _ => false
  fun type_is_smtfp ty =
    type_has_name "smtfloat" "smtfp" ty orelse
    type_has_name "smtfloat" "smt_rounding" ty
  fun type_is_binary_ieee_float ty =
    type_has_name "binary_ieee" "float" ty
  fun type_contains_fp ty =
    type_is_smtfp ty orelse
    (List.exists type_contains_fp (Lib.snd (Type.dest_type ty))
      handle Feedback.HOL_ERR _ => false)
  (* smtstr only, which is exactly the set of types that 'builtin_types' maps
     to the SMT-LIB String sort; HOL's :string is an ordinary HOL type here. *)
  val type_contains_string = Library.type_contains_string

  fun type_contains_function ty =
    type_contains is_function_type ty

  val same_const = Library.same_const

  (* HOL represents a set as an ordinary predicate, so the outbound boundary
     records set *terms*, rather than treating every `a -> bool` as a Set.
     The context is installed for one translation only (see
     goal_to_SmtLib_aux).  It lets cvc5 print its finite-set sort without
     changing the representation of unrelated predicates. *)
  datatype set_backend = Z3Set | CVC5NativeSet | CVC5ArraySet

  val current_set_backend = ref Z3Set
  val current_set_terms = ref ([] : Term.term list)
  val current_raw_num_terms = ref ([] : Term.term list)
  val current_collection_function_arguments =
    ref ([] : (Term.term * int * Term.term) list)

  fun contextual_collection_argument function index =
    case List.find
        (fn (other, other_index, _) =>
          index = other_index andalso Term.aconv function other)
        (!current_collection_function_arguments) of
      SOME (_, _, argument) => SOME argument
    | NONE => NONE

  fun has_contextual_collection_argument function =
    List.exists (fn (other, _, _) => Term.aconv function other)
      (!current_collection_function_arguments)

  val native_set_heads = [
    pred_setSyntax.in_tm, pred_setSyntax.insert_tm, pred_setSyntax.delete_tm,
    pred_setSyntax.union_tm, pred_setSyntax.inter_tm, pred_setSyntax.diff_tm,
    pred_setSyntax.compl_tm, pred_setSyntax.subset_tm, pred_setSyntax.empty_tm,
    pred_setSyntax.univ_tm, pred_setSyntax.card_tm
  ]

  (* SmtArrayProve's goal-directed fact table mirrors these emitted heads.
     Derive the audit input from the heads themselves, so extending the
     printer necessarily extends the replay-completeness check. *)
  val native_set_operator_names = List.map
    (fn head => #Name (Term.dest_thy_const head)) native_set_heads

  fun is_native_set_head tm =
    List.exists (fn head => same_const head tm) native_set_heads

  fun is_set_type tm =
    let
      val (_, result_ty) = Type.dom_rng (Term.type_of tm)
    in
      Type.compare (result_ty, Type.bool) = EQUAL
    end
    handle Feedback.HOL_ERR _ => false

  fun set_element_type tm =
    if is_set_type tm then Lib.fst (Type.dom_rng (Term.type_of tm))
    else raise ERR "set_element_type" "not a set-valued term"

  fun mem_aconv tm = List.exists (Term.aconv tm)

  fun add_set_term tm terms =
    if is_set_type tm andalso not (mem_aconv tm terms) then tm :: terms
    else terms

  (* A set expression is native precisely when the printer has a direct
     representation for every constructor in it.  In particular, GSPEC and
     IMAGE retain the old predicate expansion before outbound translation. *)
  fun native_set_term tm =
    Term.is_var tm orelse pred_setSyntax.is_empty tm orelse
    pred_setSyntax.is_univ tm orelse
    (case Lib.total pred_setSyntax.dest_insert tm of
       SOME (_, set) => native_set_term set
     | NONE =>
       (case Lib.total pred_setSyntax.dest_delete tm of
          SOME (set, _) => native_set_term set
        | NONE =>
          (case Lib.total pred_setSyntax.dest_union tm of
             SOME (left, right) =>
               native_set_term left andalso native_set_term right
           | NONE =>
             (case Lib.total pred_setSyntax.dest_inter tm of
                SOME (left, right) =>
                  native_set_term left andalso native_set_term right
              | NONE =>
                (case Lib.total pred_setSyntax.dest_diff tm of
                   SOME (left, right) =>
                     native_set_term left andalso native_set_term right
                 | NONE =>
                   (case Lib.total pred_setSyntax.dest_compl tm of
                      SOME set => native_set_term set
                    | NONE => false))))))

  (* Record only terms at set-typed positions.  Recording all arguments of
     INSERT, for example, incorrectly declares its element as a Set. *)
  fun collect_native_set_terms tm terms =
  let
    fun collect_set set terms =
      case Lib.total boolSyntax.dest_cond set of
        SOME (_, then_set, else_set) =>
          collect_set else_set (collect_set then_set (add_set_term set terms))
      | NONE => add_set_term set terms
    val (rator, rands) = boolSyntax.strip_comb tm
    val terms =
      (let
         val (_, body) = Term.dest_abs tm
       in
         collect_native_set_terms body terms
       end
       handle Feedback.HOL_ERR _ =>
         List.foldl (fn (arg, acc) => collect_native_set_terms arg acc)
           terms rands)
    (* A let-local which is used as a native Set must give its value the same
       representation.  The body is visited above, so propagate its marker
       back to the corresponding binding value. *)
    val terms =
      (let
         val (bindings, _) = pairSyntax.dest_anylet tm
       in
         List.foldl (fn ((variable, value), acc) =>
           if mem_aconv variable acc then collect_set value acc else acc)
           terms bindings
       end
       handle Feedback.HOL_ERR _ => terms)
  in
    if same_const rator pred_setSyntax.in_tm then
      (case rands of [_, set] => collect_set set terms | _ => terms)
    else if same_const rator pred_setSyntax.card_tm orelse
            same_const rator pred_setSyntax.finite_tm then
      (case rands of [set] => collect_set set terms | _ => terms)
    else if same_const rator pred_setSyntax.insert_tm then
      (case rands of [_, set] => collect_set tm (collect_set set terms)
       | _ => terms)
    else if same_const rator pred_setSyntax.delete_tm then
      (case rands of [set, _] => collect_set tm (collect_set set terms)
       | _ => terms)
    else if same_const rator pred_setSyntax.union_tm orelse
            same_const rator pred_setSyntax.inter_tm orelse
            same_const rator pred_setSyntax.diff_tm then
      (case rands of [left, right] =>
         collect_set tm (collect_set left (collect_set right terms))
       | _ => terms)
    else if same_const rator pred_setSyntax.compl_tm then
      (case rands of [set] => collect_set tm (collect_set set terms)
       | _ => terms)
    else if same_const rator pred_setSyntax.subset_tm then
      (case rands of [left, right] =>
         collect_set left (collect_set right terms)
       | _ => terms)
    else if pred_setSyntax.is_empty tm orelse pred_setSyntax.is_univ tm then
      add_set_term tm terms
    else if same_const rator boolSyntax.equality then
      (case rands of [left, right] =>
         if is_set_type left andalso is_set_type right then
           collect_set left (collect_set right terms)
         else terms
       | _ => terms)
    else
      terms
  end

  fun is_marked_set_term tm = mem_aconv tm (!current_set_terms)

  fun finite_set_hypothesis tm =
    SOME (pred_setSyntax.dest_finite tm) handle Feedback.HOL_ERR _ => NONE

  (* Bool and fixed-width word types have finite SMT-LIB domains.  A
     polymorphic word remains unsupported until its width is instantiated. *)
  fun finite_element_type ty =
    Type.compare (ty, Type.bool) = EQUAL orelse
    (Lib.can wordsSyntax.dest_word_type ty andalso
     Lib.can fcpSyntax.dest_numeric_type (wordsSyntax.dest_word_type ty))

  fun finite_set_term finite_terms tm =
    finite_element_type (set_element_type tm) orelse
    mem_aconv tm finite_terms orelse
    pred_setSyntax.is_empty tm orelse
    (pred_setSyntax.is_univ tm andalso
     finite_element_type (set_element_type tm)) orelse
    (case Lib.total pred_setSyntax.dest_insert tm of
       SOME (_, set) => finite_set_term finite_terms set
     | NONE =>
       (case Lib.total pred_setSyntax.dest_delete tm of
          SOME (set, _) => finite_set_term finite_terms set
        | NONE =>
          (case Lib.total pred_setSyntax.dest_union tm of
             SOME (left, right) =>
               finite_set_term finite_terms left andalso
               finite_set_term finite_terms right
           | NONE =>
             (case Lib.total pred_setSyntax.dest_inter tm of
                SOME (left, right) =>
                  finite_set_term finite_terms left orelse
                  finite_set_term finite_terms right
              | NONE =>
                (case Lib.total pred_setSyntax.dest_diff tm of
                   SOME (left, _) => finite_set_term finite_terms left
                 | NONE =>
                   (case Lib.total pred_setSyntax.dest_compl tm of
                      SOME _ => finite_element_type (set_element_type tm)
                    | NONE => false))))))

  (* A finite-evidence term is meaningful only in the scope in which it was
     assumed.  In particular, alpha conversion alone cannot distinguish a
     free variable in an assumption from an identically named variable bound
     beneath an abstraction.  Do not select cvc5's finite Set model when an
     evidence-dependent collection occurrence is shadowed in this way. *)
  fun shadowed_finite_collection is_collection native finite_terms terms =
  let
    fun evidence_uses_bound bound evidence =
      List.exists (fn free => List.exists (fn variable =>
        Term.aconv free variable) bound) (Term.free_vars evidence)
    fun visit bound tm =
      (is_collection tm andalso native tm andalso
       List.exists (fn evidence => mem_aconv tm finite_terms andalso
         evidence_uses_bound bound evidence) finite_terms) orelse
      ((let
          val (variable, body) = Term.dest_abs tm
        in visit (variable :: bound) body end)
       handle Feedback.HOL_ERR _ =>
         ((let
             val (rator, rand) = Term.dest_comb tm
           in visit bound rator orelse visit bound rand end)
          handle Feedback.HOL_ERR _ => false))
  in
    List.exists (visit []) terms
  end

  fun is_set_hol_type ty =
    case Lib.total Type.dom_rng ty of
      SOME (_, range) => Type.compare (range, Type.bool) = EQUAL
    | NONE => false

  (* cvc5's native Set and Bag sorts cannot be used as the element sort of a
     Seq or in a datatype field.  The HOL collection is a function there, so
     use the Array encoding consistently throughout the translation. *)
  fun collection_nested_in_container is_collection goal =
    let
      fun type_contains ty =
        is_collection ty orelse
        (List.exists type_contains (Lib.snd (Type.dest_type ty))
         handle Feedback.HOL_ERR _ => false)
      fun type_is_nested ty =
        (type_contains (listSyntax.dest_list_type ty)
         handle Feedback.HOL_ERR _ => false) orelse
        (case TypeBase.fetch ty of
           SOME tyinfo =>
             List.exists (fn constructor =>
               List.exists type_contains
                 (Lib.fst (boolSyntax.strip_fun (Term.type_of constructor))))
               (TypeBasePure.constructors_of tyinfo)
         | NONE => false)
        handle Feedback.HOL_ERR _ => false
      fun visit tm =
        type_is_nested (Term.type_of tm) orelse
        ((let val (rator, rand) = Term.dest_comb tm in
            visit rator orelse visit rand
          end)
         handle Feedback.HOL_ERR _ =>
           ((let val (_, body) = Term.dest_abs tm in visit body end)
            handle Feedback.HOL_ERR _ => false))
    in
      List.exists visit (Lib.fst goal @ [Lib.snd goal])
    end

  fun cvc5_native_sets goal set_terms =
  let
    val finite_terms = List.mapPartial finite_set_hypothesis (Lib.fst goal)
  in
    not (List.null set_terms) andalso
    not (collection_nested_in_container is_set_hol_type goal) andalso
    not (List.exists pred_setSyntax.is_compl set_terms) andalso
    not (shadowed_finite_collection is_set_type native_set_term finite_terms
      (Lib.fst goal @ [Lib.snd goal])) andalso
    not (List.exists (fn set =>
      pred_setSyntax.is_set_type (set_element_type set)) set_terms) andalso
    List.all (fn set => native_set_term set andalso
      finite_set_term finite_terms set) set_terms
  end

  fun backend_for_target target goal set_terms =
    case target of
      SOME {solver = "cvc5", ...} =>
        if cvc5_native_sets goal set_terms then CVC5NativeSet
        else CVC5ArraySet
    | _ => Z3Set

  (* Bags are likewise functions in HOL, but their integer-valued array
     representation must remain distinct from arbitrary functions. *)
  datatype bag_backend = Z3ArrayBag | CVC5NativeBag | CVC5ArrayBag

  val current_bag_backend = ref Z3ArrayBag
  val current_bag_terms = ref ([] : Term.term list)
  val current_bag_helpers = ref ([] : string list)

  fun bag_const name = Term.prim_mk_const {Thy = "bag", Name = name}

  val bag_in_tm = bag_const "BAG_IN"
  val bag_merge_tm = bag_const "BAG_MERGE"
  val bag_inter_tm = bag_const "BAG_INTER"
  val finite_bag_tm = bag_const "FINITE_BAG"

  val native_bag_heads = [
    bag_in_tm, bagSyntax.BAG_INSERT_tm, bagSyntax.BAG_UNION_tm,
    bagSyntax.BAG_DIFF_tm, bag_merge_tm, bag_inter_tm,
    bagSyntax.SUB_BAG_tm, bagSyntax.BAG_CARD_tm, bagSyntax.EMPTY_BAG_tm
  ]

  val native_bag_operator_names = List.map
    (fn head => #Name (Term.dest_thy_const head)) native_bag_heads

  fun is_native_bag_head tm =
    List.exists (fn head => same_const head tm) native_bag_heads

  fun is_bag_type tm = bagSyntax.is_bag_ty (Term.type_of tm)

  fun bag_element_type tm =
    if is_bag_type tm then bagSyntax.base_type tm
    else raise ERR "bag_element_type" "not a bag-valued term"

  fun collection_nested_in_collection set_terms bag_terms =
    List.exists (fn set =>
      let val ty = set_element_type set in
        is_set_hol_type ty orelse bagSyntax.is_bag_ty ty
      end) set_terms orelse
    List.exists (fn bag =>
      let val ty = bag_element_type bag in
        is_set_hol_type ty orelse bagSyntax.is_bag_ty ty
      end) bag_terms

  fun add_bag_term tm terms =
    if is_bag_type tm andalso not (mem_aconv tm terms) then tm :: terms
    else terms

  fun dest_bag_binary head tm =
    let val (rator, rands) = boolSyntax.strip_comb tm in
      if same_const rator head then
        case rands of [left, right] => (left, right)
        | _ => raise ERR "dest_bag_binary" "wrong arity"
      else
        raise ERR "dest_bag_binary" "wrong head"
    end

  (* cvc5 bag literals are parsed as their extensional HOL function.  Retain
     this exact shape so a checked proof can be sent back as a Bag literal,
     rather than as an unrelated higher-order lambda. *)
  fun dest_parsed_bag_literal tm =
    let
      val (bound, body) = Term.dest_abs tm
      val (cond_head, cond_args) = boolSyntax.strip_comb body
      val (test, count, otherwise) =
        if same_const cond_head boolSyntax.conditional then
          case cond_args of
            [test, count, otherwise] => (test, count, otherwise)
          | _ => raise ERR "dest_parsed_bag_literal" "wrong conditional arity"
        else
          raise ERR "dest_parsed_bag_literal" "not a conditional"
      val (eq_head, eq_args) = boolSyntax.strip_comb test
      val (left, element) =
        if same_const eq_head boolSyntax.equality then
          case eq_args of [left, element] => (left, element)
          | _ => raise ERR "dest_parsed_bag_literal" "wrong equality arity"
        else
          raise ERR "dest_parsed_bag_literal" "not an equality"
      val _ = if Term.aconv bound left then ()
              else raise ERR "dest_parsed_bag_literal" "wrong binder"
      val (count_head, count_args) = boolSyntax.strip_comb count
      val integer_count =
        if same_const count_head boolSyntax.conditional then
          (case count_args of
             [nonnegative, nat_count, zero] =>
               let
                 val _ = if intSyntax.is_Num nat_count then ()
                         else raise ERR "dest_parsed_bag_literal"
                           "not an integer count"
                 val integer_count = intSyntax.dest_Num nat_count
                 val (lower, upper) = intSyntax.dest_leq nonnegative
                 val _ =
                   if Term.aconv lower intSyntax.zero_tm andalso
                      Term.aconv upper integer_count andalso
                      Term.aconv zero numSyntax.zero_tm then ()
                   else raise ERR "dest_parsed_bag_literal" "wrong count clamp"
               in integer_count end
           | _ => raise ERR "dest_parsed_bag_literal" "wrong count arity")
        else if numSyntax.is_numeral count then
          Term.mk_comb (intSyntax.int_injection, count)
        else
          raise ERR "dest_parsed_bag_literal" "not a count"
      val _ =
        if Term.free_in bound element orelse
           Term.free_in bound integer_count orelse
           not (Term.aconv otherwise numSyntax.zero_tm) then
          raise ERR "dest_parsed_bag_literal"
            "literal element or count depends on binder"
        else ()
    in
      (element, integer_count)
    end

  fun is_parsed_bag_literal tm =
    Lib.can dest_parsed_bag_literal tm

  fun native_bag_term tm =
    Term.is_var tm orelse bagSyntax.is_empty tm orelse
    is_parsed_bag_literal tm orelse
    (case Lib.total bagSyntax.dest_insert tm of
       SOME (_, bag) => native_bag_term bag
     | NONE =>
       (case Lib.total bagSyntax.dest_union tm of
          SOME (left, right) =>
            native_bag_term left andalso native_bag_term right
        | NONE =>
          (case Lib.total bagSyntax.dest_diff tm of
             SOME (left, right) =>
               native_bag_term left andalso native_bag_term right
           | NONE =>
             (case Lib.total (dest_bag_binary bag_merge_tm) tm of
                SOME (left, right) =>
                  native_bag_term left andalso native_bag_term right
              | NONE =>
                (case Lib.total (dest_bag_binary bag_inter_tm) tm of
                   SOME (left, right) =>
                     native_bag_term left andalso native_bag_term right
                 | NONE => false)))))

  fun collect_native_bag_terms tm terms =
  let
    fun collect_bag bag terms =
      case Lib.total boolSyntax.dest_cond bag of
        SOME (_, then_bag, else_bag) =>
          collect_bag else_bag (collect_bag then_bag (add_bag_term bag terms))
      | NONE => add_bag_term bag terms
    val (rator, rands) = boolSyntax.strip_comb tm
    val terms =
      (let val (_, body) = Term.dest_abs tm in
         collect_native_bag_terms body terms
       end
       handle Feedback.HOL_ERR _ =>
         List.foldl (fn (arg, acc) => collect_native_bag_terms arg acc)
           terms rands)
    (* [strip_comb] flattens a partially applied bag operation into its head
       and all arguments.  Retain the immediate rator too: in [(b + c) x],
       it is the bag-valued prefix that must be marked for [bag.count]. *)
    val terms =
      (let val (immediate_rator, _) = Term.dest_comb tm in
         collect_native_bag_terms immediate_rator terms
       end
       handle Feedback.HOL_ERR _ => terms)
    fun binary () =
      case rands of [left, right] =>
        collect_bag tm (collect_bag left (collect_bag right terms))
      | _ => terms
  in
    if same_const rator bag_in_tm then
      (case rands of [_, bag] => collect_bag bag terms | _ => terms)
    else if same_const rator bagSyntax.BAG_CARD_tm orelse
            same_const rator finite_bag_tm then
      (case rands of [bag] => collect_bag bag terms | _ => terms)
    else if same_const rator bagSyntax.BAG_INSERT_tm then
      (case rands of [_, bag] => collect_bag tm (collect_bag bag terms)
       | _ => terms)
    else if same_const rator bagSyntax.BAG_UNION_tm orelse
            same_const rator bagSyntax.BAG_DIFF_tm orelse
            same_const rator bag_merge_tm orelse same_const rator bag_inter_tm
    then binary ()
    else if same_const rator bagSyntax.SUB_BAG_tm then
      (case rands of [left, right] =>
         collect_bag left (collect_bag right terms)
       | _ => terms)
    else if bagSyntax.is_empty tm then add_bag_term tm terms
    else if same_const rator boolSyntax.equality then
      (case rands of [left, right] =>
         if is_bag_type left andalso is_bag_type right then
           collect_bag left (collect_bag right terms)
         else terms
       | _ => terms)
    else terms
  end

  fun is_marked_bag_term tm = mem_aconv tm (!current_bag_terms)

  fun finite_bag_term finite_terms tm =
    mem_aconv tm finite_terms orelse bagSyntax.is_empty tm orelse
    is_parsed_bag_literal tm orelse
    finite_element_type (bag_element_type tm) orelse
    (case Lib.total bagSyntax.dest_insert tm of
       SOME (_, bag) => finite_bag_term finite_terms bag
     | NONE =>
       (case Lib.total bagSyntax.dest_union tm of
          SOME (left, right) =>
            finite_bag_term finite_terms left andalso
            finite_bag_term finite_terms right
        | NONE =>
          (case Lib.total bagSyntax.dest_diff tm of
             SOME (left, _) => finite_bag_term finite_terms left
           | NONE =>
             let val (rator, rands) = boolSyntax.strip_comb tm in
               if same_const rator bag_merge_tm then
                 (case rands of [left, right] =>
                    finite_bag_term finite_terms left andalso
                    finite_bag_term finite_terms right
                  | _ => false)
               else if same_const rator bag_inter_tm then
                 (case rands of [left, right] =>
                    finite_bag_term finite_terms left orelse
                    finite_bag_term finite_terms right
                  | _ => false)
               else false
             end)))

  fun finite_bag_hypothesis tm =
    let val (rator, rands) = boolSyntax.strip_comb tm in
      if same_const rator finite_bag_tm then
        case rands of [bag] => SOME bag | _ => NONE
      else NONE
    end

  fun cvc5_native_bags goal bag_terms =
  let val finite_terms = List.mapPartial finite_bag_hypothesis (Lib.fst goal)
  in
    not (List.null bag_terms) andalso
    not (collection_nested_in_container bagSyntax.is_bag_ty goal) andalso
    not (shadowed_finite_collection is_bag_type native_bag_term finite_terms
      (Lib.fst goal @ [Lib.snd goal])) andalso
    not (List.exists (fn bag =>
      bagSyntax.is_bag_ty (bag_element_type bag)) bag_terms) andalso
    List.all (fn bag => native_bag_term bag andalso
      finite_bag_term finite_terms bag) bag_terms
  end

  fun bag_backend_for_target target goal bag_terms =
    case target of
      SOME {solver = "cvc5", ...} =>
        if cvc5_native_bags goal bag_terms then CVC5NativeBag
        else CVC5ArrayBag
    | _ => Z3ArrayBag

  fun contains_bag_card tm =
    Lib.can (HolKernel.find_term bagSyntax.is_card) tm

  fun contains_set_card tm =
    Lib.can (HolKernel.find_term pred_setSyntax.is_card) tm

  (* The shared first-order Seq surface is represented directly by stock list
     terms.  MAP and FOLDL below are the Z3-only higher-order extension. *)
  fun list_const name = Term.prim_mk_const {Thy = "list", Name = name}
  fun rich_list_const name =
    Term.prim_mk_const {Thy = "rich_list", Name = name}
  fun holsmt_const name = Term.prim_mk_const {Thy = "HolSmt", Name = name}

  val seq_append_tm = list_const "APPEND"
  val seq_length_tm = list_const "LENGTH"
  val seq_cons_tm = list_const "CONS"
  val seq_reverse_tm = list_const "REVERSE"
  val seq_prefix_tm = list_const "isPREFIX"
  val seq_lupdate_tm = list_const "LUPDATE"
  val seq_map_tm = list_const "MAP"
  val seq_foldl_tm = list_const "FOLDL"
  val seq_contains_tm = rich_list_const "IS_SUBLIST"
  val seq_suffix_tm = rich_list_const "IS_SUFFIX"
  val smt_seq_nth_tm = holsmt_const "smt_seq_nth"
  val smt_seq_extract_tm = holsmt_const "smt_seq_extract"
  val smt_seq_at_tm = holsmt_const "smt_seq_at"
  val smt_seq_indexof_tm = holsmt_const "smt_seq_indexof"
  val smt_seq_replace_tm = holsmt_const "smt_seq_replace"
  val smt_seq_replace_all_tm = holsmt_const "smt_seq_replace_all"
  val smt_seq_update_tm = holsmt_const "smt_seq_update"
  val smtstr_update_tm = smtstring_const "smtstr_update"
  val smtstr_rev_tm = smtstring_const "smtstr_rev"
  val z3_seq_nth_i_tm =
    Term.prim_mk_const {Thy = "smtstringz3", Name = "seq_nth_i"}

  (* The parser represents String [seq.nth] with an explicit negative-index
     branch, since its out-of-range value is unspecified.  Recover the
     original surface operation before re-emission: translating the ARB
     branch separately loses sharing between repeated accesses. *)
  fun dest_string_nth_shape tm =
    let
      val (negative, _, in_range) = boolSyntax.dest_cond tm
      val (nth, index_num) = Term.dest_comb in_range
      val (head, string) = Term.dest_comb nth
      val index = intSyntax.dest_Num index_num
      val _ =
        if same_const head z3_seq_nth_i_tm andalso
           Term.aconv negative
             (intSyntax.mk_less (index, intSyntax.zero_tm)) then ()
        else raise ERR "dest_string_nth_shape" "not a String seq.nth"
    in
      (string, index)
    end

  fun dest_seq_extract_shape tm =
    let
      val (invalid, empty, body) = boolSyntax.dest_cond tm
      val (count, drop) = listSyntax.dest_take body
      val (start, sequence) = listSyntax.dest_drop drop
      val index = intSyntax.dest_Num start
      val size = intSyntax.dest_Num count
      val expected_invalid = boolSyntax.list_mk_disj [
        intSyntax.mk_less (index, intSyntax.zero_tm),
        intSyntax.mk_leq (size, intSyntax.zero_tm),
        numSyntax.mk_leq (listSyntax.mk_length sequence, start)]
      val _ =
        if listSyntax.is_nil empty andalso
           Type.compare (listSyntax.dest_nil empty,
             sequence_element_type sequence) = EQUAL andalso
           Term.aconv invalid expected_invalid then ()
        else raise ERR "dest_seq_extract_shape" "not a sequence extract"
    in
      (sequence, index, size)
    end

  fun dest_seq_at_shape tm =
    let
      val (invalid, empty, body) = boolSyntax.dest_cond tm
      val (element, body_empty) = listSyntax.dest_cons body
      val (index_num, sequence) = listSyntax.dest_el element
      val index = intSyntax.dest_Num index_num
      val expected_invalid = boolSyntax.mk_disj
        (intSyntax.mk_less (index, intSyntax.zero_tm),
         numSyntax.mk_leq (listSyntax.mk_length sequence, index_num))
      val _ =
        if listSyntax.is_nil empty andalso listSyntax.is_nil body_empty andalso
           Type.compare (listSyntax.dest_nil empty,
             sequence_element_type sequence) = EQUAL andalso
           Term.aconv invalid expected_invalid then ()
        else raise ERR "dest_seq_at_shape" "not a sequence at"
    in
      (sequence, index)
    end

  (* List types alone remain ordinary HOL datatypes: only a supported stock
     list operation (or one of TASK_16's exact totalized-access shapes)
     selects the Seq model.  This keeps unrelated recursive-list datatype
     goals on their existing encoding while refusing partial TAKE/DROP/EL
     terms that have no direct Seq counterpart. *)
  fun native_sequence_goal (assumptions, conclusion) =
    let
      val terms = conclusion :: assumptions
      val subterms = List.concat (List.map Library.subterms terms)
      val totalized = List.filter (fn tm =>
        Option.isSome (Lib.total dest_seq_extract_shape tm) orelse
        Option.isSome (Lib.total dest_seq_at_shape tm)) subterms
      val totalized_subterms =
        List.concat (List.map Library.subterms totalized)
      fun is_totalized_part tm =
        List.exists (fn part => Term.aconv tm part) totalized_subterms
      fun named theory names tm =
        case Lib.total Term.dest_thy_const tm of
          SOME {Thy, Name, ...} =>
            Thy = theory andalso List.exists (fn name => name = Name) names
        | NONE => false
      val direct_list_heads =
        ["APPEND", "LENGTH", "CONS", "NIL", "REVERSE", "isPREFIX",
         "LUPDATE", "MAP", "FOLDL"]
      val totalized_list_heads = ["TAKE", "DROP", "EL"]
      val rich_list_heads = ["IS_SUBLIST", "IS_SUFFIX"]
      val holsmt_heads =
        ["smt_seq_nth", "smt_seq_extract", "smt_seq_at", "smt_seq_indexof",
         "smt_seq_replace", "smt_seq_replace_all", "smt_seq_update"]
      fun supported tm =
        case Lib.total Term.dest_thy_const tm of
          SOME {Thy = "list", ...} =>
            named "list" direct_list_heads tm orelse
            (named "list" totalized_list_heads tm andalso
             is_totalized_part tm)
        | SOME {Thy = "rich_list", ...} =>
            named "rich_list" rich_list_heads tm
        | _ => true
      fun native_sequence_parts tm =
        List.all (fn sub =>
          not (listSyntax.is_list_type (Term.type_of sub)) orelse
          is_native_sequence_type (Term.type_of sub)) (Library.subterms tm)
      fun selects_seq tm =
        ((named "list" direct_list_heads tm orelse
          named "rich_list" rich_list_heads tm orelse
          named "HolSmt" holsmt_heads tm) andalso
         native_sequence_parts tm) orelse
        List.exists (fn whole => Term.aconv tm whole) totalized
      fun has_unconverted_word_num tm =
        Lib.can wordsSyntax.dest_w2n tm
    in
      List.all supported subterms andalso
      not (List.exists has_unconverted_word_num subterms) andalso
      List.exists selects_seq subterms
    end

  val smt_rdiv_tm = Term.prim_mk_const {Thy="HolSmt", Name="smt_rdiv"}
  val int_of_num_tm = Term.prim_mk_const {Thy="integer", Name="int_of_num"}
  val num_of_int_tm = Term.prim_mk_const {Thy="integer", Name="Num"}
  val int_ediv_tm = Term.prim_mk_const {Thy="integer", Name="ediv"}
  val int_emod_tm = Term.prim_mk_const {Thy="integer", Name="emod"}

  fun is_int_arith_const tm =
    List.exists (fn c => same_const c tm) [
      intSyntax.negate_tm, intSyntax.minus_tm, intSyntax.plus_tm,
      intSyntax.mult_tm, int_ediv_tm, int_emod_tm, intSyntax.absval_tm,
      intSyntax.leq_tm, intSyntax.less_tm, intSyntax.geq_tm,
      intSyntax.greater_tm
    ]

  fun is_real_arith_const tm =
    List.exists (fn c => same_const c tm) [
      realSyntax.negate_tm, realSyntax.minus_tm, realSyntax.plus_tm,
      realSyntax.mult_tm, smt_rdiv_tm, realSyntax.leq_tm,
      realSyntax.less_tm, realSyntax.geq_tm, realSyntax.greater_tm,
      intrealSyntax.real_of_int_tm, intrealSyntax.INT_FLOOR_tm,
      intrealSyntax.is_int_tm
    ]

  fun is_bv_const tm =
    List.exists (fn c => same_const c tm) [
      wordsSyntax.word_concat_tm, wordsSyntax.word_extract_tm,
      wordsSyntax.word_1comp_tm, wordsSyntax.word_and_tm,
      wordsSyntax.word_or_tm, wordsSyntax.word_nand_tm,
      wordsSyntax.word_nor_tm, wordsSyntax.word_xor_tm,
      wordsSyntax.word_xnor_tm, wordsSyntax.word_2comp_tm,
      wordsSyntax.word_compare_tm, wordsSyntax.word_add_tm,
      wordsSyntax.word_sub_tm, wordsSyntax.word_mul_tm,
      wordsSyntax.word_quot_tm, wordsSyntax.word_rem_tm,
      integer_wordSyntax.word_smod_tm, wordsSyntax.word_div_tm,
      wordsSyntax.word_mod_tm, wordsSyntax.word_lsl_bv_tm,
      wordsSyntax.word_lsr_bv_tm, wordsSyntax.word_asr_bv_tm,
      wordsSyntax.word_replicate_tm, wordsSyntax.w2w_tm,
      wordsSyntax.sw2sw_tm, wordsSyntax.word_rol_tm,
      wordsSyntax.word_ror_tm, wordsSyntax.word_lo_tm,
      wordsSyntax.word_ls_tm, wordsSyntax.word_hi_tm,
      wordsSyntax.word_hs_tm, wordsSyntax.word_lt_tm,
      wordsSyntax.word_le_tm, wordsSyntax.word_gt_tm,
      wordsSyntax.word_ge_tm
    ]

  fun is_nonlinear_arith_const tm =
    same_const intSyntax.mult_tm tm orelse
    same_const realSyntax.mult_tm tm orelse
    same_const int_ediv_tm tm orelse
    same_const int_emod_tm tm

  fun is_string_const tm =
    same_const str_inj_tm tm orelse is_native_string_const tm

  fun is_fp_const tm =
    if Term.is_const tm then
      let val {Thy, Name, ...} = Term.dest_thy_const tm in
        Thy = "smtfloat" andalso
        List.exists (fn name => name = Name) native_fp_names
      end
    else
      false

  fun native_string_literal tm =
    let
      val (constructor, representation) = Term.dest_comb tm
      val _ =
        if same_const
            (smtstring_const "SmtStr") constructor then ()
        else raise ERR "native_string_literal" "not an SMT String"
      val (elements, element_ty) = listSyntax.dest_list representation
      val _ =
        if Type.compare (element_ty, numSyntax.num) = EQUAL then ()
        else raise ERR "native_string_literal"
          "String representation is not a num list"
      fun code_point element =
        Arbnum.toInt
          (SmtLib_String_Literal.check_code_point "code point"
            (numSyntax.dest_numeral element))
        handle SmtLib_String_Literal.InvalidCodePoint detail =>
          raise ERR "native_string_literal" detail
      val code_points = List.map code_point elements
    in
      "\"" ^ SmtLib_String_Literal.encode_string_literal code_points ^ "\""
    end

  val subterms = Library.subterms

  val has_quantifier = Library.has_quantifier

  fun builtin_encoding tm =
    let
      val (rator, rands) = boolSyntax.strip_comb tm
      fun try_whole () =
        if not (Lib.can Type.dom_rng (Term.type_of tm)) then
          (case first_success (fn parsefn => parsefn (tm, []))
              (Net.match tm builtin_symbols) of
             SOME (symbol, _) => SOME (symbol, 0)
           | NONE => NONE)
        else
          NONE
        handle _ => NONE
    in
      case first_success (fn parsefn => parsefn (rator, rands))
          (Net.match rator builtin_symbols) of
        SOME (symbol, _) => SOME (symbol, List.length rands)
      | NONE => try_whole ()
    end

  fun insert_builtin_record (record, records) =
    if List.exists
        (fn EncodedSymbol {hol_term, smt_symbol, arity} =>
              (case record of
                 EncodedSymbol {hol_term = hol_term',
                   smt_symbol = smt_symbol', arity = arity'} =>
                   Term.compare (hol_term, hol_term') = EQUAL andalso
                   smt_symbol = smt_symbol' andalso arity = arity'
               | _ => false)
          | _ => false) records
    then records
    else record :: records

  fun encoded_symbol_records terms =
    let
      fun add (tm, records) =
        case builtin_encoding tm of
          SOME (symbol, arity) =>
            insert_builtin_record
              (EncodedSymbol {hol_term = Lib.fst (boolSyntax.strip_comb tm),
                smt_symbol = symbol, arity = arity}, records)
        | NONE => records
    in
      List.foldl add [] (List.concat (List.map subterms terms))
    end

  fun features_to_string (LogicFeatures {
      quantifiers, uninterpreted, arrays, bitvectors, integers, reals,
      floating_point, strings, sequences, sets, bags, datatypes, nonlinear,
      higher_order}) =
    String.concatWith "," (List.map Lib.fst (List.filter Lib.snd [
      ("quantifiers", quantifiers),
      ("uninterpreted", uninterpreted),
      ("arrays", arrays),
      ("bitvectors", bitvectors),
      ("integers", integers),
      ("reals", reals),
      ("floating-point", floating_point),
      ("strings", strings),
      ("sequences", sequences),
      ("sets", sets),
      ("bags", bags),
      ("datatypes", datatypes),
      ("nonlinear", nonlinear),
      ("higher-order", higher_order)
    ]))

  fun infer_logic_from_features_for_regime regime
      (features as LogicFeatures {
      quantifiers, uninterpreted, arrays, bitvectors, integers, reals,
      floating_point, strings, sequences, sets, bags, datatypes, nonlinear,
      higher_order}) =
    let
      val qf = if quantifiers then "" else "QF_"
      fun datatype_arith_logic () =
        if arrays then
          if integers andalso reals then
            "AUFDT" ^ (if nonlinear then "NIRA" else "LIRA")
          else if integers then
            if nonlinear then "AUFDTNIRA" else "AUFDTLIA"
          else if reals then
            "AUFDT" ^ (if nonlinear then "NIRA" else "LIRA")
          else
            "AUFDTLIA"
        else if integers andalso reals then
          if nonlinear then "UFDTNIRA"
          else qf ^ "UFDTLIRA"
        else if integers then
          if nonlinear then qf ^ "UFDTNIA"
          else qf ^ "UFDTLIA"
        else if reals then
          if nonlinear then "UFDTNIRA"
          else qf ^ "UFDTLIRA"
        else if quantifiers orelse uninterpreted then
          qf ^ "UFDT"
        else
          "QF_DT"
      fun quantified_array_arith_logic () =
        (* Non-QF AUFNIA/AUFNRA are not in the supported logic table here;
           use the recognized A*NIRA/A*LIRA supersets when needed. *)
        if integers andalso reals then
          if uninterpreted then
            "AUF" ^ (if nonlinear then "NIRA" else "LIRA")
          else
            "A" ^ (if nonlinear then "NIRA" else "LIRA")
        else if integers then
          if uninterpreted then
            if nonlinear then "AUFNIRA" else "AUFLIA"
          else
            "A" ^ (if nonlinear then "NIA" else "LIA")
        else if reals then
          if uninterpreted then
            "AUF" ^ (if nonlinear then "NIRA" else "LIRA")
          else
            "A" ^ (if nonlinear then "NIRA" else "LIRA")
        else if uninterpreted then
          "AUFLIA"
        else
          "ALIA"
      fun arith_logic () =
        if integers andalso reals then
          if quantifiers andalso arrays then
            quantified_array_arith_logic ()
          else if quantifiers orelse arrays orelse uninterpreted then
            "AUFNIRA"
          else if nonlinear then qf ^ "NIRA" else qf ^ "LIRA"
        else if integers then
          if arrays then
            if quantifiers then
              quantified_array_arith_logic ()
            else
              qf ^ "AUF" ^ (if nonlinear then "NIA" else "LIA")
          else if uninterpreted then
            (* QF_UFNIA is not an official SMT-LIB logic; widen the
               quantifier-free nonlinear case to the recognized QF_UFNIRA
               superset (the quantified UFNIA case is already official). *)
            if nonlinear andalso not quantifiers then "QF_UFNIRA"
            else qf ^ "UF" ^ (if nonlinear then "NIA" else "LIA")
          else
            qf ^ (if nonlinear then "NIA" else "LIA")
        else if reals then
          if arrays then
            if quantifiers then
              quantified_array_arith_logic ()
            else
              (* QF_AUFNRA / QF_AUFLRA are not official SMT-LIB logics;
                 widen to the recognized QF_AUFNIRA / QF_AUFLIRA supersets. *)
              qf ^ "AUF" ^ (if nonlinear then "NIRA" else "LIRA")
          else if uninterpreted then
            qf ^ "UF" ^ (if nonlinear then "NRA" else "LRA")
          else
            qf ^ (if nonlinear then "NRA" else "LRA")
        else if arrays then
          if quantifiers then quantified_array_arith_logic () else "QF_AX"
        else
          qf ^ "UF"
      fun bitvector_datatype_logic () =
        if integers orelse reals then
          "ALL"
        else if arrays then
          "AUFBVDT"
        else
          "UFBVDT"
      fun floating_point_logic () =
        if strings orelse datatypes orelse integers orelse nonlinear then
          "ALL"
        else if reals andalso uninterpreted then
          (* SMT-LIB has no UFFPLRA or AUFBVFPLRA packet. *)
          "ALL"
        else if arrays then
          if reals then qf ^ "ABVFPLRA"
          else if uninterpreted then qf ^ "AUFBVFP"
          else qf ^ "ABVFP"
        else if reals then
          qf ^ (if bitvectors then "BVFPLRA" else "FPLRA")
        else if uninterpreted then
          qf ^ (if bitvectors then "UFBVFP" else "UFFP")
        else
          qf ^ (if bitvectors then "BVFP" else "FP")
      val logic =
        if sequences orelse sets orelse bags then
          "ALL"
        else if floating_point then
          floating_point_logic ()
        else if strings then
          (* RegLan and dedicated smtstring symbols are classified as the
             UnicodeStrings feature, not as HOL datatypes or UFs.  Only
             genuinely orthogonal theories force the conservative fallback. *)
          if bitvectors orelse reals orelse quantifiers orelse arrays orelse
             uninterpreted orelse datatypes then
            "ALL"
          else if integers then
            if nonlinear then "QF_SNIA" else "QF_SLIA"
          else
            "QF_S"
        else if bitvectors then
          if datatypes then
            bitvector_datatype_logic ()
          else if integers orelse reals orelse quantifiers then
            "ALL"
          else if arrays then
            if uninterpreted then qf ^ "AUFBV" else qf ^ "ABV"
          else if uninterpreted then
            qf ^ "UFBV"
          else
            qf ^ "BV"
        else if datatypes then
          datatype_arith_logic ()
        else
          arith_logic ()
      val curated_ho_stems = [
        "ALL", "UF", "QF_UF", "UFLIA", "QF_UFLIA",
        "UFLRA", "QF_UFLRA", "AUFLIA", "AUFLIRA", "QF_AUFLIA"
      ]
      val logic =
        case regime of
          HigherOrder Standard27 =>
            if higher_order then
              if List.exists (fn stem => stem = logic) curated_ho_stems then
                "HO_" ^ logic
              else
                "HO_ALL"
            else
              logic
        | _ => logic
      val reason =
        "deterministic feature scan: " ^
        (case features_to_string features of "" => "core" | s => s)
    in
      (logic, reason)
    end

  fun term_declaration_text regime name domain_sorts range_sort =
    case (regime, domain_sorts) of
      (HigherOrder Standard27, []) =>
        "(declare-const " ^ name ^ " " ^ range_sort ^ ")\n"
    | _ =>
        "(declare-fun " ^ name ^ " (" ^
        String.concatWith " " domain_sorts ^ ") " ^ range_sort ^ ")\n"

  val emitted_term_sorts =
    ref ([] : ((Term.term * int) * (string list * string)) list)

  fun record_emitted_term_sorts key sorts =
    emitted_term_sorts := (key, sorts) :: !emitted_term_sorts

  fun emitted_term_sorts_for (tm, arity) =
    case List.find (fn ((other_tm, other_arity), _) =>
      arity = other_arity andalso Term.aconv tm other_tm) (!emitted_term_sorts)
      of
        SOME (_, sorts) => SOME sorts
      | NONE => NONE

  fun term_decl_for_tmdict regime tydict ((tm, arity), name) =
    let
      fun doms_rng acc 0 ty = (List.rev acc, ty)
        | doms_rng acc n ty =
          let val (dom, rng) = Type.dom_rng ty
          in doms_rng (dom :: acc) (n - 1) rng end
      val injected_string = arity = 0 andalso is_injected_string tm
      val injected_float = arity = 0 andalso is_injected_float tm
      val (domtys, rngty) = doms_rng [] arity (Term.type_of tm)
      val (domain_sorts, range_sort) =
        case emitted_term_sorts_for (tm, arity) of
          SOME sorts => sorts
        | NONE =>
            (List.map (smt_sort_of_type regime tydict) domtys,
             if injected_string then "String"
             else if injected_float then smtfp_sort rngty
             else smt_sort_of_type regime tydict rngty)
      val declaration =
        term_declaration_text regime name domain_sorts range_sort
    in
      TermDeclaration {hol_term = tm, arity = arity, smt_name = name,
        domain_sorts = domain_sorts, range_sort = range_sort,
        declaration = declaration}
    end

  val smt_reserved_type_names = [
    "Bool", "Int", "Real", "String", "RoundingMode", "FloatingPoint",
    "Float16", "Float32", "Float64", "Float128", "Array", "BitVec",
    "Seq", "Set", "Bag", "RegLan"
  ]

  val smt_reserved_term_names = [
    "true", "false", "not", "and", "or", "xor", "=>", "=", "distinct",
    "ite", "select", "store", "div", "mod", "abs", "to_real", "to_int",
    "is_int"
  ]

  fun is_smt_reserved names name = List.exists (fn s => s = name) names

  fun starts_with_alpha s =
    String.size s > 0 andalso Char.isAlpha (String.sub (s, 0))

  fun smt_simple_symbol prefix raw =
    let
      val sanitized = SmtLib_Theories.sanitize_name raw
      val base =
        if starts_with_alpha sanitized then sanitized else prefix ^ sanitized
    in
      if base = prefix then prefix ^ "x" else base
    end

  fun capitalize s =
    if s = "" then "T"
    else
      String.str (Char.toUpper (String.sub (s, 0))) ^
      String.extract (s, 1, NONE)

  fun type_name_stem ty =
    case first_success (fn (_, f) => f ty)
        (TypeNet.match (builtin_types, ty)) of
      SOME name => smt_simple_symbol "T_" name
    | NONE =>
      if Type.is_vartype ty then
        smt_simple_symbol "T_" (Type.dest_vartype ty)
      else if is_function_type ty then
        let
          val (dom, rng) = Type.dom_rng ty
        in
          "Fun_" ^ type_name_stem dom ^ "_" ^ type_name_stem rng
        end
      else
        let
          val {Tyop, Args, ...} = Type.dest_thy_type ty
          val base = smt_simple_symbol "T_" (capitalize Tyop)
        in
          case Args of
            [] => base
          | _ => base ^ "_" ^ String.concatWith "_"
              (List.map type_name_stem Args)
        end

  fun dict_type_names tydict =
    Redblackmap.foldl (fn (_, name, acc) => name :: acc) [] tydict

  fun fresh_smt_name reserved used stem =
    let
      val stem = smt_simple_symbol "S_" stem
      fun unavailable s =
        is_smt_reserved reserved s orelse List.exists (fn t => t = s) used
      fun loop n =
        let
          val candidate =
            if n = 0 then stem else stem ^ "_" ^ Int.toString n
        in
          if unavailable candidate then loop (n + 1) else candidate
        end
    in
      loop 0
    end

  fun same_type (ty1, ty2) = Type.compare (ty1, ty2) = EQUAL

  fun member_type ty tys = List.exists (fn ty' => same_type (ty, ty')) tys

  fun add_type ty tys = if member_type ty tys then tys else ty :: tys

  fun free_datatype_tyinfo tyinfo =
    not (List.null (TypeBasePure.constructors_of tyinfo)) andalso
    Lib.can TypeBasePure.nchotomy_of tyinfo andalso
    Lib.can TypeBasePure.case_def_of tyinfo andalso
    Lib.can TypeBasePure.induction_of tyinfo

  (* 'num' is transferred to SMT Int by preprocessing.  A residual HOL :string
     is a char list, but its content reaches SMT only through str_inj, so
     enumerating its list structure would burden the solver with a datatype no
     emitted symbol ever inspects; it stays an opaque sort instead. *)
  fun datatype_translation_excluded ty =
    same_type (ty, numSyntax.num) orelse
    same_type (ty, stringSyntax.string_ty) orelse
    type_is_binary_ieee_float ty

  fun predicate_domain_type pred =
    let
      val (dom, rng) = Type.dom_rng (Term.type_of pred)
    in
      if same_type (rng, Type.bool) then SOME dom else NONE
    end
    handle Feedback.HOL_ERR _ => NONE

  fun datatype_family_types tyinfo ty =
    let
      val (preds, _) =
        boolSyntax.strip_forall (Thm.concl (TypeBasePure.induction_of tyinfo))
      val patterns = List.mapPartial predicate_domain_type preds
      fun instantiate pattern =
        let val theta = Type.match_type pattern ty
        in List.map (Type.type_subst theta) patterns end
    in
      case Lib.get_first (Lib.total instantiate) patterns of
        SOME family =>
          List.rev (List.foldl (fn (fam_ty, acc) => add_type fam_ty acc)
            [] family)
      | NONE => raise ERR "datatype_family_types" "no matching family member"
    end

  fun datatype_family ty =
    if datatype_translation_excluded ty then
      NONE
    else case TypeBase.fetch ty of
      NONE => NONE
    | SOME tyinfo =>
      if free_datatype_tyinfo tyinfo then
        let
          val family = datatype_family_types tyinfo ty
          val tyinfos = List.map TypeBase.fetch family
        in
          if List.all Option.isSome tyinfos andalso
             List.all (free_datatype_tyinfo o valOf) tyinfos then
            SOME family
          else
            NONE
        end
        handle Feedback.HOL_ERR _ => NONE
      else
        NONE

  val invented_uf_native_datatype_domain_diagnostic =
    "HOLSMT_TRANSLATION_INVENTED_UF_NATIVE_DATATYPE_DOMAIN"

  val uninterpreted_native_datatype_destructor_diagnostic =
    "HOLSMT_TRANSLATION_UNINTERPRETED_NATIVE_DATATYPE_DESTRUCTOR"

  val unsupported_smtfloat_constant_diagnostic =
    "HOLSMT_TRANSLATION_UNSUPPORTED_SMTFLOAT_CONSTANT"

  (* The generic symbol emitter is deliberately closed over the smtfloat
     theory.  These constants are representation or replay scaffolding, not
     additional SMT FloatingPoint operations: replay may keep them opaque
     while proving the surrounding formula.  Every name is explicit so a new
     smtfloat definition cannot silently acquire invented-UF semantics. *)
  val smtfloat_opaque_replay_constants =
    Redblackset.addList
      (Redblackset.empty String.compare,
       ["SmtFp", "smtfp_rep", "canon",
        "smtfp_circuit_sig", "smtfp_circuit_exp",
        "smtfp_circuit_round_up", "smtfp_circuit_round",
        "smtfp_circuit_infinity", "smtfp_circuit_top",
        "smtfp_circuit_overflow", "smtfp_circuit_wanted_exponent",
        "smtfp_circuit_encoded_exponent",
        "smtfp_circuit_effective_exponent", "smtfp_circuit_shift",
        "smtfp_circuit_divisor", "smtfp_circuit_quotient",
        "smtfp_circuit_remainder", "smtfp_circuit_rounded",
        "smtfp_circuit_pack", "smtfp_circuit_encode",
        "smtfp_addsub_trace", "smtfp_addsub_zero_sign",
        "smtfp_addsub_circuit",
        "smtfp_mul_trace", "smtfp_mul_sign", "smtfp_mul_product",
        "smtfp_mul_exponent_sum", "smtfp_mul_wanted_exponent",
        "smtfp_mul_encoded_exponent", "smtfp_mul_shift_right",
        "smtfp_mul_divisor", "smtfp_mul_quotient",
        "smtfp_mul_remainder", "smtfp_mul_encode",
        "smtfp_mul_circuit"])

  fun reject_unsupported_smtfloat_constant rator =
    if not (Term.is_const rator) then ()
    else
      case Lib.total Term.dest_thy_const rator of
        SOME {Thy = "smtfloat", Name, ...} =>
          if Redblackset.member (smtfloat_opaque_replay_constants, Name) then
            ()
          else
            raise ERR "translate_term"
              (unsupported_smtfloat_constant_diagnostic ^
               ": refusing to invent SMT semantics for smtfloat$" ^ Name ^
               "; constant=" ^ Hol_pp.term_to_string rator ^
               "; type=" ^ Hol_pp.type_to_string (Term.type_of rator))
      | _ => ()

  fun datatype_destructor_head theorem =
    let
      val (_, body) = boolSyntax.strip_forall (Thm.concl theorem)
      val clauses = boolSyntax.strip_conj body
      fun clause_head clause =
        let
          val (_, equation) = boolSyntax.strip_forall clause
          val (lhs, _) = boolSyntax.dest_eq equation
          val (head, arguments) = boolSyntax.strip_comb lhs
          val _ = if List.length arguments = 1 then () else
            raise ERR "datatype_destructor_head"
              "destructor equation is not unary"
        in
          head
        end
      val heads = List.map clause_head clauses
      val head = List.hd heads
      val _ = List.all (Term.same_const head) heads orelse
        raise ERR "datatype_destructor_head"
          "destructor theorem defines multiple constants"
    in
      head
    end

  fun datatype_destructor_theorem tyinfo destructor =
    List.find
      (fn theorem =>
        Term.same_const destructor (datatype_destructor_head theorem))
      (TypeBasePure.destructors_of tyinfo)

  (* This predicate follows the actual type emitter: ordinary native lists
     are datatypes, but a selected Seq backend emits them as `(Seq ...)` and
     therefore does not create the under-specified native-datatype boundary. *)
  fun emits_native_datatype_sort ty =
    not (is_function_type ty) andalso
    not (has_type_builtin ty) andalso
    not (!current_native_sequence_emission andalso
      is_native_sequence_type ty) andalso
    Option.isSome (datatype_family ty)

  fun registered_destructor_for_domain destructor domain =
    case TypeBase.fetch domain of
      SOME tyinfo =>
        Option.isSome (datatype_destructor_theorem tyinfo destructor)
    | NONE => false

  fun emitted_native_sort ty =
    emits_native_datatype_sort ty orelse
    (!current_native_sequence_emission andalso is_native_sequence_type ty)

  fun uninterpreted_native_destructor_domain rator domain_types =
    if Term.is_const rator then
      List.find (fn domain => emitted_native_sort domain andalso
        registered_destructor_for_domain rator domain) domain_types
    else
      NONE

  fun raise_uninterpreted_native_destructor rator domain =
    raise ERR "translate_term"
      (uninterpreted_native_datatype_destructor_diagnostic ^
       ": refusing an uninterpreted TypeBase destructor over a native " ^
       "sort; destructor=" ^ Hol_pp.term_to_string rator ^
       "; domain=" ^ Hol_pp.type_to_string domain)

  fun theorem_reduces_exact_application theorem tm =
    let
      val reduction = simpLib.SIMP_CONV pureSimps.pure_ss [theorem] tm
      val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl reduction)
      val _ = Term.aconv lhs tm orelse
        raise ERR "closed_constructor_destructor_residual"
          "registered destructor proof has the wrong left-hand side"
    in
      not (Term.aconv lhs rhs)
    end
    handle Conv.UNCHANGED => false

  (* A partial destructor on a closed constructor outside its owning branch
     is a fixed but unspecified HOL value.  It can soundly be represented by
     one zero-arity SMT constant keyed by the whole application: unlike an
     uninterpreted destructor function, that declaration has no native-sort
     domain.  Admission is theorem-sensitive: a registered equation which can
     reduce the exact application must be used by preprocessing, never hidden
     behind this residual boundary.  Any free/symbolic scrutinee remains behind
     the hard diagnostic. *)
  fun closed_constructor_destructor_residual tm =
    if not (Term.is_comb tm) then false
    else
        let
          val (destructor, scrutinee) = Term.dest_comb tm
          val domain = Term.type_of scrutinee
          val (constructor, _) = boolSyntax.strip_comb scrutinee
          val registered =
            case TypeBase.fetch domain of
              NONE => NONE
            | SOME tyinfo =>
                Option.map (fn theorem => (tyinfo, theorem))
                  (datatype_destructor_theorem tyinfo destructor)
        in
          case registered of
            NONE => false
          | SOME (_, theorem) =>
              emitted_native_sort domain andalso
              Term.is_const constructor andalso
              TypeBase.is_constructor constructor andalso
              List.null (Term.free_vars tm) andalso
              not (theorem_reduces_exact_application theorem tm)
        end

  fun reject_uninterpreted_native_destructors terms =
  let
    fun reject tm =
      if not (Term.is_comb tm) then ()
      else
        let val (rator, argument) = Term.dest_comb tm in
          if closed_constructor_destructor_residual tm then ()
          else
            (case uninterpreted_native_destructor_domain rator
                [Term.type_of argument] of
              SOME domain => raise_uninterpreted_native_destructor rator domain
            | NONE => ())
        end
  in
    List.app reject (List.concat (List.map Library.subterms terms))
  end


  fun reject_invented_native_datatype_domain rator domain_types =
  let
    val destructor_domain =
      uninterpreted_native_destructor_domain rator domain_types
  in
    case destructor_domain of
      SOME domain => raise_uninterpreted_native_destructor rator domain
    | NONE =>
        (case List.find emits_native_datatype_sort domain_types of
          NONE => ()
        | SOME domain =>
            raise ERR "translate_term"
              (invented_uf_native_datatype_domain_diagnostic ^
               ": refusing an invented function whose domain was emitted " ^
               "as a native datatype sort; the query is under-specified " ^
               "and its sat/unknown verdict is not a countermodel; " ^
               "function=" ^ Hol_pp.term_to_string rator ^ "; domain=" ^
               Hol_pp.type_to_string domain))
  end


  fun constructor_name type_name constructor used =
    let
      val raw = #Name (Term.dest_thy_const constructor)
        handle Feedback.HOL_ERR _ => Hol_pp.term_to_string constructor
    in
      fresh_smt_name smt_reserved_term_names used
        ("ctor_" ^ type_name ^ "_" ^ raw)
    end

  fun record_selector_names tyinfo constructor_name fields used =
    let
      fun field_name (_, {accessor, ...} : TypeBasePure.rcd_fieldinfo) =
        #Name (Term.dest_thy_const accessor)
        handle Feedback.HOL_ERR _ => Hol_pp.term_to_string accessor
      fun one ((field, info), (used, acc)) =
        let
          val raw =
            case field_name (field, info) of "" => field | name => name
          val name = fresh_smt_name smt_reserved_term_names used
            ("sel_" ^ constructor_name ^ "_" ^ raw)
        in
          (name :: used, name :: acc)
        end
      val (_, names) = List.foldl one (used, []) fields
    in
      List.rev names
    end

  fun generated_selector_names type_name constructor_name arity used =
    let
      fun one (n, (used, acc)) =
        let
          val name = fresh_smt_name smt_reserved_term_names used
            ("sel_" ^ type_name ^ "_" ^ constructor_name ^ "_" ^
             Int.toString n)
        in
          (name :: used, name :: acc)
        end
      val (_, names) =
        List.foldl one (used, []) (List.tabulate (arity, fn n => n))
    in
      List.rev names
    end

  fun datatype_constructor_infos ty type_name =
    let
      val tyinfo =
        case TypeBase.fetch ty of
          SOME info => info
        | NONE => raise ERR "datatype_constructor_infos"
            "missing TypeBase entry"
      val fields = TypeBasePure.fields_of tyinfo
      fun one (constructor, (used, acc)) =
        let
          val constructor = TypeBasePure.cinst ty constructor
          val cname = constructor_name type_name constructor used
          val (doms, _) = boolSyntax.strip_fun (Term.type_of constructor)
          val selector_names =
            if not (List.null fields) andalso List.length doms =
               List.length fields then
              record_selector_names tyinfo cname fields (cname :: used)
            else
              generated_selector_names type_name cname (List.length doms)
                (cname :: used)
          val selectors = ListPair.zipEq (selector_names, doms)
          val used = cname :: selector_names @ used
        in
          (used, (constructor, cname, selectors) :: acc)
        end
      val (_, infos) =
        List.foldl one (smt_reserved_term_names, [])
          (TypeBasePure.constructors_of tyinfo)
    in
      List.rev infos
    end

  fun type_decl_record (ty, name) =
    TypeDeclaration {hol_type = ty, smt_name = name,
      declaration = "(declare-sort " ^ name ^ " 0)\n"}

  fun datatype_declaration_text sort_of family names =
    let
      val name_of = ListPair.zipEq (family, names)
      fun lookup_name ty =
        case List.find (fn (ty', _) => same_type (ty, ty')) name_of of
          SOME (_, name) => name
        | NONE => raise ERR "datatype_declaration_text" "missing family name"
      fun constructor_decs (ty, type_name) =
        let
          val tyinfo =
            case TypeBase.fetch ty of
              SOME info => info
            | NONE => raise ERR "datatype_declaration_text"
                "missing TypeBase entry"
          val infos = datatype_constructor_infos ty type_name
          fun one (_, cname, selectors) =
            let
              val selectors = List.map
                (fn (sel, dom) => "(" ^ sel ^ " " ^ sort_of dom ^ ")")
                selectors
            in
              "(" ^ cname ^
              (case selectors of
                [] => ""
              | _ => " " ^ String.concatWith " " selectors) ^ ")"
            end
          val cdecs = List.map one infos
        in
          "(" ^ String.concatWith " " cdecs ^ ")"
        end
      val sort_decls = List.map (fn name => "(" ^ name ^ " 0)") names
      val datatype_decls = ListPair.mapEq constructor_decs (family, names)
    in
      "(declare-datatypes (" ^ String.concatWith " " sort_decls ^ ") (" ^
      String.concatWith " " datatype_decls ^ "))\n"
    end

  fun datatype_decl_record regime tydict ty =
    case datatype_family ty of
      NONE => NONE
    | SOME family =>
      let
        val names = List.map (fn fam_ty => Redblackmap.find (tydict, fam_ty))
          family
        val declaration = datatype_declaration_text
          (smt_sort_of_type regime tydict) family names
      in
        SOME (DatatypeDeclaration {hol_types = family, smt_names = names,
          declaration = declaration}, family)
      end
      handle Redblackmap.NotFound => NONE
           | Feedback.HOL_ERR _ => NONE

  fun infer_features regime terms tydict tmdict =
    let
      fun encoding_subterms tm =
        let
          fun walk (tm, acc) =
            tm ::
            (if listSyntax.is_all_distinct tm then
               let
                 val (elements, _) =
                   listSyntax.dest_list (listSyntax.dest_all_distinct tm)
               in
                 List.foldl (fn (element, rest) => walk (element, rest))
                   acc elements
               end
             else
               (let val (rator, rand) = Term.dest_comb tm
                in walk (rator, walk (rand, acc)) end
                handle Feedback.HOL_ERR _ =>
                  (let val (_, body) = Term.dest_abs tm
                   in walk (body, acc) end
                   handle Feedback.HOL_ERR _ => acc)))
        in
          walk (tm, [])
        end
      val all_subterms = List.concat (List.map encoding_subterms terms)
      fun subterm_types p =
        List.exists (fn tm => p (Term.type_of tm)) all_subterms
      fun is_smtfp_bits_application tm =
        let
          val (head, args) = boolSyntax.strip_comb tm
          val {Thy, Name, ...} = Term.dest_thy_const head
        in
          Thy = "smtfloat" andalso Name = "smtfp_bits" andalso
          List.length args = 3
        end
        handle Feedback.HOL_ERR _ => false
      (* The three bit-vector fields of the SMT [fp] constructor are part of
         every FP logic's core syntax; they do not independently require a BV
         logic packet.  Other word-valued terms, including FP/BV conversions,
         still select the mixed packet. *)
      fun has_nonconstructor_bitvector tm =
        if is_smtfp_bits_application tm then
          let val (_, fields) = boolSyntax.strip_comb tm
          in not (List.all wordsSyntax.is_word_literal fields) end
        else if type_contains_word (Term.type_of tm) orelse
                is_bv_const (Lib.fst (boolSyntax.strip_comb tm)) then true
        else if Term.is_comb tm then
          let val (rator, rand) = Term.dest_comb tm
          in
            has_nonconstructor_bitvector rator orelse
            has_nonconstructor_bitvector rand
          end
        else if Term.is_abs tm then
          has_nonconstructor_bitvector (Lib.snd (Term.dest_abs tm))
        else false
      val quantifiers = !current_generated_forall_emissions > 0 orelse
        List.exists has_quantifier terms
      val bitvectors = List.exists has_nonconstructor_bitvector terms
      val integers =
        subterm_types type_contains_int orelse
        List.exists (fn tm => is_int_arith_const
          (Lib.fst (boolSyntax.strip_comb tm))) all_subterms
      val reals =
        subterm_types type_contains_real orelse
        List.exists (fn tm => is_real_arith_const
          (Lib.fst (boolSyntax.strip_comb tm))) all_subterms
      val floating_point =
        subterm_types type_contains_fp orelse
        List.exists (fn tm => is_fp_const
          (Lib.fst (boolSyntax.strip_comb tm))) all_subterms
      val strings =
        subterm_types type_contains_string orelse
        subterm_types
          (Library.type_contains
            (fn ty => Type.compare (ty, reglan_ty) = EQUAL)) orelse
        List.exists (fn tm => is_string_const
          (Lib.fst (boolSyntax.strip_comb tm))) all_subterms
      fun thy_const_named theory names tm =
        case Lib.total Term.dest_thy_const tm of
          SOME {Thy, Name, ...} =>
            Thy = theory andalso List.exists (fn name => name = Name) names
        | NONE => false
      val sequence_names =
        ["APPEND", "LENGTH", "CONS", "NIL", "TAKE", "DROP", "EL",
         "MAP", "FOLDL", "REVERSE", "isPREFIX", "LUPDATE"]
      val rich_sequence_names = ["IS_SUBLIST", "IS_SUFFIX"]
      val holsmt_sequence_names =
        ["smt_seq_nth", "smt_seq_extract", "smt_seq_at", "smt_seq_indexof",
         "smt_seq_replace", "smt_seq_replace_all", "smt_seq_update"]
      val set_names =
        ["INSERT", "DELETE", "UNION", "INTER", "DIFF", "COMPL", "SUBSET",
         "EMPTY", "UNIV", "SING", "CARD"]
      val bag_names =
        ["BAG_IN", "BAG_INSERT", "BAG_UNION", "BAG_MERGE", "BAG_INTER",
         "BAG_DIFF", "BAG_CARD", "EMPTY_BAG", "SUB_BAG"]
      fun is_native_sequence_const tm =
        thy_const_named "list" sequence_names tm orelse
        thy_const_named "rich_list" rich_sequence_names tm orelse
        thy_const_named "HolSmt" holsmt_sequence_names tm
      fun is_native_set_const tm =
        thy_const_named "pred_set" set_names tm orelse
        thy_const_named "bool" ["IN"] tm
      fun is_native_bag_const tm = thy_const_named "bag" bag_names tm
      val sequences = !current_native_sequence_emission andalso
        (subterm_types is_native_sequence_type orelse
         List.exists (fn tm => is_native_sequence_const
           (Lib.fst (boolSyntax.strip_comb tm))) all_subterms)
      (* Finite-set hypotheses select cvc5's native Set sort and are removed
         before this scan, so backend selection itself is also a Set feature. *)
      val sets = not (List.null (!current_set_terms)) orelse
        !current_set_backend = CVC5NativeSet orelse
        List.exists (fn tm => is_native_set_const
          (Lib.fst (boolSyntax.strip_comb tm))) all_subterms
      (* Checked preprocessing can lower native bag operations to count
         applications.  The native cvc5 backend still emits Bag sorts. *)
      val bags = not (List.null (!current_bag_terms)) orelse
        !current_bag_backend = CVC5NativeBag orelse
        List.exists (fn tm => is_native_bag_const
          (Lib.fst (boolSyntax.strip_comb tm))) all_subterms
      fun term_is_native_string_surface tm =
        let val (rator, _) = boolSyntax.strip_comb tm
        in
          is_native_string_const rator orelse
          type_contains_string (Term.type_of tm) orelse
          Library.type_contains
            (fn ty => Type.compare (ty, reglan_ty) = EQUAL)
            (Term.type_of tm)
        end
      fun type_is_datatype ty =
        not (has_type_builtin ty) andalso Option.isSome (datatype_family ty)
      fun type_contains_datatype ty =
        type_contains type_is_datatype ty
      val has_injected_strings =
        List.exists is_injected_string all_subterms
      fun term_contains_datatype tm =
        let
          val (rator, _) = boolSyntax.strip_comb tm
        in
          not (term_is_native_string_surface tm) andalso
          not (strings andalso same_const boolSyntax.equality rator) andalso
          not (has_injected_strings andalso
            (is_string_const rator orelse
              Lib.can injected_string_operator rator)) andalso
          type_contains_datatype (Term.type_of tm)
        end
      fun term_is_datatype_constructor tm =
        TypeBase.is_constructor tm
      fun term_is_datatype_record_selector tm =
        let
          val (dom, _) = Type.dom_rng (Term.type_of tm)
          val tyinfo =
            case TypeBase.fetch dom of
              SOME info => info
            | NONE => raise ERR "infer_features" "not a datatype selector"
          val fields = TypeBasePure.fields_of tyinfo
        in
          List.exists
            (fn (_, {accessor, ...} : TypeBasePure.rcd_fieldinfo) =>
               Term.same_const tm accessor)
            fields
        end
      fun term_is_datatype_native ((tm, arity), _) =
        (arity = 0 andalso
         type_contains_datatype (Term.type_of tm)) orelse
        term_is_datatype_constructor tm orelse
        (case Lib.total term_is_datatype_record_selector tm of
           SOME result => result
         | NONE => false)
      val datatypes =
        List.exists term_contains_datatype all_subterms orelse
        Redblackmap.foldl (fn (ty, _, b) =>
          b orelse type_contains_datatype ty) false tydict orelse
        Redblackmap.foldl (fn ((tm, arity), _, b) =>
          b orelse
          (not (is_injected_string tm) andalso
           not (is_injected_float tm) andalso
           type_contains_datatype (Term.type_of tm))) false tmdict
      val nonlinear =
        List.exists (fn tm => is_nonlinear_arith_const
          (Lib.fst (boolSyntax.strip_comb tm))) all_subterms
      val has_uninterpreted_type =
        Redblackmap.foldl (fn (ty, _, b) =>
          b orelse not (type_contains_datatype ty)) false tydict
      fun range_after 0 ty = ty
        | range_after n ty = range_after (n - 1) (Lib.snd (Type.dom_rng ty))
      fun term_needs_uf ((tm, arity), _) =
        if term_is_datatype_native ((tm, arity), "") then
          false
        else if arity = 0 andalso
                (is_injected_string tm orelse is_injected_float tm) then
          false
        else
          arity > 0 orelse
          (arity = 0 andalso
           not (has_type_builtin (range_after arity (Term.type_of tm))) andalso
           not (is_function_type (range_after arity (Term.type_of tm))))
      val uninterpreted =
        has_uninterpreted_type orelse
        Redblackmap.foldl (fn (key, value, b) =>
          b orelse term_needs_uf (key, value)) false tmdict
      val higher_order =
        case regime of FirstOrder => false | HigherOrder _ => true
      val function_arrays =
        case regime of
          FirstOrder =>
            List.exists (fn tm =>
              Term.is_var tm andalso
              type_contains_function (Term.type_of tm)) all_subterms orelse
            Redblackmap.foldl (fn ((tm, arity), _, b) =>
              b orelse (arity = 0 andalso
                type_contains_function (Term.type_of tm))) false tmdict
        | HigherOrder _ => false
      val arrays =
        function_arrays orelse
        List.exists combinSyntax.is_update_comb all_subterms
    in
      LogicFeatures {quantifiers = quantifiers, uninterpreted = uninterpreted,
        arrays = arrays, bitvectors = bitvectors, integers = integers,
        reals = reals, floating_point = floating_point, strings = strings,
        sequences = sequences, sets = sets, bags = bags,
        datatypes = datatypes, nonlinear = nonlinear,
        higher_order = higher_order}
    end

  fun advanced_encoding_records regime terms
      (LogicFeatures {sequences, sets, bags, ...}) =
    let
      val all_subterms = List.concat (List.map subterms terms)
      fun subterm_types p =
        List.exists (fn tm => p (Term.type_of tm)) all_subterms
      val has_strings =
        subterm_types type_contains_string orelse
        List.exists (fn tm => is_string_const
          (Lib.fst (boolSyntax.strip_comb tm))) all_subterms
      val string_record =
        HOLTheoryEncoding {
          feature =
            "HOL strings: str_inj images of STRCAT, isPREFIX, string_lt, " ^
            "string_le and string equality",
          smt_theory = "UnicodeStrings",
          mode = NativeSMTLIB,
          parse = true,
          typecheck = true,
          translate = true,
          replay = false,
          notes =
            "HOL strings are rewritten through the proved str_inj transfer " ^
            "kit; injected occurrences are generalized to SMT-LIB String.  " ^
            "The HOL :string type itself is not the SMT String sort: a " ^
            "residual occurrence is emitted as an uninterpreted sort.  " ^
            "Ground native smtstr goals do replay; the oracle tactics " ^
            "cover the injected HOL-string surface.",
          proof_obligation =
            "Translation is discharged by the str_inj injectivity and " ^
            "operator-transfer theorems.  Checked replay of an injected " ^
            "HOL-string goal is not implemented: Z3 answers such goals " ^
            "with seq th-lemmas over the str_inj image, and cvc5 with the " ^
            "trust and str-substr-full-eq CPC rules, none of which the " ^
            "replay engines support."
        }
      val datatype_record =
        HOLTheoryEncoding {
          feature = "HOL datatypes and recursive datatypes",
          smt_theory = "Datatypes",
          mode = ConservativeEmbedding,
          parse = true,
          typecheck = true,
          translate = true,
          replay = true,
          notes =
            "SMT-LIB datatype commands are parsed/typechecked; HOL TypeBase " ^
            "datatypes are emitted as native SMT-LIB Datatypes with checked " ^
            "constructor, selector, tester, exhaustiveness, and acyclicity replay.",
          proof_obligation =
            "Replay is checked for TypeBase-backed constructor disjointness, injectivity, selectors, testers, exhaustiveness, and acyclicity; unsupported certificate shapes remain explicit diagnostics."
        }
      val fp_record =
        HOLTheoryEncoding {
          feature =
            "SMT floating point and proved binary_ieee classification, " ^
            "comparison, abs/neg, add/sub/mul/div/sqrt/fma transfer",
          smt_theory = "FloatingPoint",
          mode = NativeSMTLIB,
          parse = true,
          typecheck = true,
          translate = true,
          replay = true,
          notes =
            "The canonical-NaN smtfp carrier and its native operators are " ^
            "emitted as SMT-LIB FloatingPoint.  Native binary_ieee terms " ^
            "on the enumerated transfer surface are rewritten through " ^
            "smtfp_intro and proved homomorphism and binder theorems.  A " ^
            "residual raw float, including raw record equality, is emitted " ^
            "as an uninterpreted sort; it is never an SMT FloatingPoint sort.",
          proof_obligation =
            "The exact smtfp carrier justifies native sort equality, and " ^
            "the native_float_transfer_infos theorem list discharges the " ^
            "binary_ieee transfer.  Checked Z3 4.x and cvc5 CPC replay " ^
            "cover the native smtfp surface and transferred " ^
            "classification/comparison goals; " ^
            "over-budget bit-blasts use the reserved D12 diagnostic, while " ^
            "unsupported symbolic arithmetic uses the structured D2 rung."
        }
      val z3_ext_record =
        HOLTheoryEncoding {
          feature = "sequences, sets, and bags",
          smt_theory = "Z3 sequence/set/bag extensions",
          mode = if sets orelse bags then NativeSMTLIB
                 else ConservativeEmbedding,
          parse = true,
          typecheck = true,
          translate = true,
          replay = true,
          notes =
            if sequences andalso sets andalso bags then
              "Stock list, pred_set, and bag operations emit their native " ^
              "dialects; non-finite cvc5 goals use quantified arrays."
            else if sequences then
              "Stock list operations emit the shared first-order seq.* " ^
              "surface; seq.update and seq.rev are cvc5-only."
            else if sets andalso bags then
              "Stock pred_set and bag operations emit their native dual " ^
              "dialects; non-finite cvc5 goals use quantified arrays."
            else if sets then
              "Stock pred_set operations emit Z3 array-sets or cvc5 finite " ^
              "set.* terms; non-finite cvc5 goals use quantified arrays."
            else if bags then
              "Stock bag operations emit Z3 Int arrays with (_ map ...) or " ^
              "finite cvc5 bag.* terms; non-finite cvc5 goals use arrays."
            else
              "Z3 extension symbols are parser/typechecker entries only.",
          proof_obligation =
            "Checked Z3 replay uses SmtSeqProve for native Seq terms, " ^
            "SmtArrayProve for sets, and SmtBagProve over the array/arith " ^
            "bag encoding; cvc5 CPC replay uses the corresponding checked " ^
            "Seq/Set/Bag rules."
        }
      val regex_record =
        HOLTheoryEncoding {
          feature = "regular expressions",
          smt_theory = "UnicodeStrings RegLan",
          mode = ConservativeEmbedding,
          parse = true,
          typecheck = true,
          translate = true,
          replay = false,
          notes =
            "Native smtstring/RegLan terms use the UnicodeStrings surface; " ^
            "HOL regex libraries have no implicit RegLan injection.",
          proof_obligation =
            "A checked soundness argument must relate HOL regex languages to SMT-LIB RegLan membership and Unicode string semantics before replay support."
        }
      val (ho_mode, ho_notes) =
        case regime of
          FirstOrder =>
            (ConservativeEmbedding,
             "The FirstOrder regime conservatively embeds HOL function " ^
             "types as nested SMT-LIB Arrays, with select/store for " ^
             "application/update.")
        | HigherOrder Standard27 =>
            (NativeSMTLIB,
             "The HigherOrder Standard27 regime emits native SMT-LIB 2.7 " ^
             "HO-Core maps, lambdas, and application.")
        | HigherOrder Z3LambdaArray =>
            (NativeSMTLIB,
             "The HigherOrder Z3LambdaArray dialect lowers HO-Core maps " ^
             "to equivalent nested Arrays/select while retaining lambdas.")
      val ho_core_record =
        HOLTheoryEncoding {
          feature =
            "HOL function types, lambda abstractions, and application",
          smt_theory = "HO-Core",
          mode = ho_mode,
          parse = true,
          typecheck = true,
          translate = true,
          replay = false,
          notes = ho_notes,
          proof_obligation =
            "Checked replay must reconstruct lambda, beta/eta, partial " ^
            "application, and function-extensionality proof steps without " ^
            "oracles before replay support is claimed."
        }
    in
      (if has_strings then [string_record] else []) @
      [datatype_record, fp_record] @
      (if sequences orelse sets orelse bags then [z3_ext_record] else []) @
      [regex_record, ho_core_record]
    end

  fun build_translation_records regime regime_reason terms logic reason
      features tydict tmdict =
    let
      val regime_record =
        RegimeSelection {regime = regime, reason = regime_reason}
      val logic_record = LogicSelection {logic = logic, reason = reason,
        features = features}
      fun add_type_record (ty, name, (seen, acc)) =
        if member_type ty seen then
          (seen, acc)
        else
          case datatype_decl_record regime tydict ty of
            SOME (record, family) =>
              (List.foldl (fn (fam_ty, seen) => add_type fam_ty seen)
                seen family, record :: acc)
          | NONE =>
              (add_type ty seen, type_decl_record (ty, name) :: acc)
      val (_, type_records) = Redblackmap.foldl add_type_record ([], []) tydict
      val term_records = Redblackmap.foldl (fn (key, name, acc) =>
        term_decl_for_tmdict regime tydict (key, name) :: acc)
        [] tmdict
      val builtin_records = encoded_symbol_records terms
      val advanced_records = advanced_encoding_records regime terms features
    in
      regime_record :: logic_record :: List.rev type_records @
      List.rev term_records @ List.rev builtin_records @ advanced_records
    end

  fun datatype_tester_term ty constructor arg =
    let
      val type_name = type_name_stem ty
      val infos = datatype_constructor_infos ty type_name
      fun clause (constructor', _, _) =
        let
          val (doms, _) = boolSyntax.strip_fun (Term.type_of constructor')
          val vars = List.map Term.genvar doms
          val pat = Term.list_mk_comb (constructor', vars)
          val result =
            if Term.same_const constructor constructor' then boolSyntax.T
            else boolSyntax.F
        in
          (pat, result)
        end
    in
      TypeBase.mk_case (arg, List.map clause infos)
    end

  fun datatype_selector_term ty constructor selector_index arg =
    let
      val type_name = type_name_stem ty
      val infos = datatype_constructor_infos ty type_name
      val selector_ty =
        case List.find (fn (constructor', _, _) =>
            Term.same_const constructor constructor') infos of
          SOME (_, _, selectors) => Lib.snd (List.nth (selectors, selector_index))
        | NONE => raise ERR "datatype_selector_term" "missing constructor"
      fun clause (constructor', _, _) =
        let
          val (doms, _) = boolSyntax.strip_fun (Term.type_of constructor')
          val vars = List.map Term.genvar doms
          val pat = Term.list_mk_comb (constructor', vars)
          val result =
            if Term.same_const constructor constructor' then
              List.nth (vars, selector_index)
            else
              boolSyntax.mk_arb selector_ty
        in
          (pat, result)
        end
    in
      TypeBase.mk_case (arg, List.map clause infos)
    end

  datatype parser_datatype_case =
      ParserSelector of {constructor : Term.term, selector_index : int,
                         scrutinee : Term.term}
    | ParserTester of {constructor : Term.term, scrutinee : Term.term}

  fun datatype_constructors ty =
    case TypeBase.fetch ty of
      SOME tyinfo =>
        List.map (TypeBasePure.cinst ty)
          (TypeBasePure.constructors_of tyinfo)
    | NONE => raise ERR "datatype_constructors" "missing TypeBase entry"

  (* These are exactly the HOL terms installed in the parser dictionary for
     SMT datatype selectors and testers.  Recognizing them centrally makes
     them fixed points of both preprocessing and outbound translation. *)
  fun parser_datatype_case tm =
    let
      val (_, scrutinee, _) = TypeBase.dest_case tm
      val ty = Term.type_of scrutinee
      val constructors = datatype_constructors ty
      fun selector_for constructor =
        let
          val (doms, _) = boolSyntax.strip_fun (Term.type_of constructor)
          fun matches selector_index =
            Term.aconv tm
              (datatype_selector_term ty constructor selector_index
                scrutinee)
        in
          case List.find matches
              (List.tabulate (List.length doms, fn n => n)) of
            SOME selector_index =>
              SOME (ParserSelector {constructor = constructor,
                selector_index = selector_index, scrutinee = scrutinee})
          | NONE => NONE
        end
      fun tester_for constructor =
        if Term.aconv tm (datatype_tester_term ty constructor scrutinee) then
          SOME (ParserTester {constructor = constructor,
            scrutinee = scrutinee})
        else
          NONE
    in
      case Lib.get_first selector_for constructors of
        SOME result => SOME result
      | NONE => Lib.get_first tester_for constructors
    end
    handle Feedback.HOL_ERR _ => NONE

  type datatype_case_parts = {
    data_ty : Type.hol_type,
    scrutinee : Term.term,
    constructors : Term.term list,
    branches : Term.term list
  }

  (* Decompose a HOL datatype case using the same selector spelling that the
     parser assigns to SMT selector applications. *)
  fun datatype_case_parts tm : datatype_case_parts =
    let
      val (_, scrutinee, clauses) = TypeBase.dest_case tm
      val data_ty = Term.type_of scrutinee
      val constructors = datatype_constructors data_ty
      fun clause_for constructor =
        case List.find
            (fn (pattern, _) =>
              let val (head, _) = boolSyntax.strip_comb pattern
              in Term.same_const constructor head end)
            clauses of
          SOME clause => clause
        | NONE => raise ERR "datatype_case_parts" "missing case branch"
      fun branch constructor =
        let
          val (pattern, rhs) = clause_for constructor
          val (_, pattern_args) = boolSyntax.strip_comb pattern
          val (doms, _) = boolSyntax.strip_fun (Term.type_of constructor)
          val _ = if List.length pattern_args = List.length doms then ()
                  else raise ERR "datatype_case_parts"
                    "case pattern arity mismatch"
          val selectors = List.map
            (fn n => datatype_selector_term data_ty constructor n scrutinee)
            (List.tabulate (List.length doms, fn n => n))
          val subst = ListPair.mapEq
            (fn (redex, residue) => {redex = redex, residue = residue})
            (pattern_args, selectors)
        in
          Term.subst subst rhs
        end
    in
      {data_ty = data_ty, scrutinee = scrutinee,
       constructors = constructors, branches = List.map branch constructors}
    end

  fun datatype_case_normal_form tm =
    let
      val {data_ty, scrutinee, constructors, branches} =
        datatype_case_parts tm
      fun tester constructor =
        datatype_tester_term data_ty constructor scrutinee
      fun cascade [] [] = raise ERR "datatype_case_normal_form"
            "empty datatype case"
        | cascade [_] [branch] = branch
        | cascade (constructor :: constructors) (branch :: branches) =
            boolSyntax.mk_cond
              (tester constructor, branch, cascade constructors branches)
        | cascade _ _ = raise ERR "datatype_case_normal_form"
            "case branch mismatch"
    in
      cascade constructors branches
    end

  fun add_datatype_parser_entries (ty, type_name, dict) =
    let
      val infos = datatype_constructor_infos ty type_name
      fun add_constructor ((constructor, cname, selectors), dict) =
        let
          val (doms, _) = boolSyntax.strip_fun (Term.type_of constructor)
          val arity = List.length doms
          fun constructor_parse token indices args =
            if List.null indices andalso List.length args = arity then
              Term.list_mk_comb (constructor, args)
            else
              SmtLib_Theories.decline ("<" ^ token ^ ">")
                "wrong number of arguments"
          fun selector_entry ((selector_index, (selector_name, _)), dict) =
            let
              fun selector_parse token indices args =
                case (indices, args) of
                  ([], [arg]) =>
                    datatype_selector_term ty constructor selector_index arg
                | _ => SmtLib_Theories.decline ("<" ^ token ^ ">")
                    "one argument expected"
            in
              Library.extend_dict ((selector_name, selector_parse), dict)
            end
          fun tester_parse token indices args =
            case (indices, args) of
              ([index], [arg]) =>
                let
                  val index_matches_constructor =
                    Term.same_const index constructor
                    handle Feedback.HOL_ERR _ => false
                  val index_name =
                    Lib.fst (Term.dest_var index)
                    handle Feedback.HOL_ERR _ =>
                      #Name (Term.dest_thy_const index)
                in
                  if index_name = cname orelse index_matches_constructor then
                    datatype_tester_term ty constructor arg
                  else
                    SmtLib_Theories.decline
                      ("<" ^ token ^ " " ^ cname ^ ">")
                      "tester constructor mismatch"
                end
            | _ => SmtLib_Theories.decline
                ("<" ^ token ^ " " ^ cname ^ ">")
                "one constructor index and one argument expected"
          val dict = Library.extend_dict ((cname, constructor_parse), dict)
          val dict = Library.extend_dict (("is", tester_parse), dict)
          val numbered = ListPair.zipEq
            (List.tabulate (List.length selectors, fn n => n), selectors)
        in
          List.foldl selector_entry dict numbered
        end
    in
      List.foldl add_constructor dict infos
    end

  fun parser_dicts_for_translation_aux solver
      ({logic, regime, tydict, tmdict, ...} : translation) =
    let
      fun parsedicts_for_logic logic =
        (case solver of
           SOME solver => SmtLib_Logics.parsedicts_of_solver_logic solver logic
         | NONE => SmtLib_Logics.parsedicts_of_any_solver_logic logic)
        handle e as Feedback.HOL_ERR _ =>
          if String.isSubstring "DT" logic then
            (case solver of
               SOME solver =>
                 SmtLib_Logics.parsedicts_of_solver_logic solver "ALL"
             | NONE => SmtLib_Logics.parsedicts_of_any_solver_logic "ALL")
          else
            raise e
      val ty_dict = Redblackmap.foldl (fn (ty, s, dict) =>
        Redblackmap.insert (dict, s, [SmtLib_Theories.K_zero_zero ty]))
        (Redblackmap.mkDict String.compare) tydict
      val tm_dict = Redblackmap.foldl (fn ((tm, n), s, dict) =>
        let
          (* `full_arity` is only consulted in the HigherOrder regime, so it is
             computed lazily there rather than for every FirstOrder entry. *)
          val accepted_arity =
            case regime of
              FirstOrder => (fn args => List.length args = n)
            | HigherOrder _ =>
                let
                  val full_arity =
                    List.length (Lib.fst (boolSyntax.strip_fun
                      (Term.type_of tm)))
                in
                  fn args => List.length args <= full_arity
                end
        in
          Redblackmap.insert (dict, s, [Lib.K (SmtLib_Theories.zero_args
            (fn args =>
              if accepted_arity args then
                Term.list_mk_comb (tm, args)
              else
                SmtLib_Theories.decline ("<" ^ s ^ ">")
                  "wrong number of arguments"))])
        end)
        (Redblackmap.mkDict String.compare) tmdict
      val tm_dict = Redblackmap.foldl (fn (ty, name, dict) =>
        case datatype_family ty of
          SOME _ => add_datatype_parser_entries (ty, name, dict)
        | NONE => dict) tm_dict tydict
      val (logic_tydict, logic_tmdict) = parsedicts_for_logic logic
    in
      (Library.union_dict logic_tydict ty_dict,
       Library.union_dict logic_tmdict tm_dict)
    end

  (* returns an updated accumulator, a (possibly empty) list of
     SMT-LIB type declarations, and the SMT-LIB representation of the
     given type *)
  fun uninterpreted_type (tydict, ty) =
    let
      val name = ty_prefix ^ Int.toString (Redblackmap.numItems tydict)
      val decl = "(declare-sort " ^ name ^ " 0)\n"
    in
      if !Library.trace > 0 andalso Type.is_type ty then
        WARNING "translate_type"
          ("uninterpreted type " ^ Hol_pp.type_to_string ty)
      else
        ();
      if !Library.trace > 2 then
        Feedback.HOL_MESG ("HolSmtLib (SmtLib): inventing name '" ^ name ^
          "' for HOL type '" ^ Hol_pp.type_to_string ty ^ "'")
      else
        ();
      (Redblackmap.insert (tydict, ty, name), ([decl], name))
    end
  fun translate_type regime (tydict, ty) =
    if !current_native_sequence_emission andalso
       is_native_sequence_type ty then
      let
        val (tydict, (decls, element_sort)) =
          translate_type regime (tydict, listSyntax.dest_list_type ty)
      in
        (tydict, (decls, "(Seq " ^ element_sort ^ ")"))
      end
    else if is_function_type ty then
      (case regime of
         HigherOrder Standard27 =>
           let
             val (doms, rng) = boolSyntax.strip_fun ty
             val (tydict, declnames) =
               Lib.foldl_map (translate_type regime) (tydict, doms @ [rng])
             val (declss, names) = Lib.split declnames
           in
             (tydict, (List.concat declss,
               "(-> " ^ String.concatWith " " names ^ ")"))
           end
       | _ =>
           let
             val (dom, rng) = Type.dom_rng ty
             val (tydict, (domdecls, domname)) =
               translate_type regime (tydict, dom)
             val (tydict, (rngdecls, rngname)) =
               translate_type regime (tydict, rng)
           in
             (tydict, (domdecls @ rngdecls, "(Array " ^ domname ^ " " ^
               rngname ^ ")"))
           end)
    else
      case first_success (fn (_, f) => f ty)
          (TypeNet.match (builtin_types, ty)) of
        SOME name => (tydict, ([], name))
      | NONE =>
        (case Redblackmap.peek (tydict, ty) of
          SOME name => (tydict, ([], name))
        | NONE =>
          (case translate_datatype_type regime (tydict, ty) of
            SOME result => result
          | NONE =>
            let
              val _ =
                case TypeBase.fetch ty of
                  SOME _ =>
                    if !Library.trace > 0 then
                      WARNING "translate_type"
                        ("datatype fallback for " ^ Hol_pp.type_to_string ty)
                    else
                      ()
                | NONE => ()
            in
              uninterpreted_type (tydict, ty)
            end))
  and translate_datatype_type regime (tydict, ty) =
    case datatype_family ty of
      NONE => NONE
    | SOME family =>
      let
        val used0 = dict_type_names tydict @ smt_reserved_type_names
        fun add_name (fam_ty, (used, acc)) =
          let
            val name = fresh_smt_name smt_reserved_type_names used
              (type_name_stem fam_ty)
          in
            (name :: used, name :: acc)
          end
        val (_, names_rev) = List.foldl add_name (used0, []) family
        val names = List.rev names_rev
        val tydict_with_family = ListPair.foldlEq
          (fn (fam_ty, name, dict) => Redblackmap.insert (dict, fam_ty, name))
          tydict (family, names)
        fun translate_constructor_doms (fam_ty, (dict, decls, sorts)) =
          let
            val tyinfo =
              case TypeBase.fetch fam_ty of
                SOME info => info
              | NONE => raise ERR "translate_datatype_type"
                  "missing TypeBase entry"
            fun translate_one (constructor, (dict, decls, sorts)) =
              let
                val constructor = TypeBasePure.cinst fam_ty constructor
                val (doms, _) = boolSyntax.strip_fun (Term.type_of constructor)
                fun translate_dom (dom, (dict, decls, sorts)) =
                  let
                    val (dict, (new_decls, sort)) =
                      translate_type regime (dict, dom)
                  in
                    (dict, decls @ new_decls, (dom, sort) :: sorts)
                  end
              in
                List.foldl translate_dom (dict, decls, sorts) doms
              end
          in
            List.foldl translate_one (dict, decls, sorts)
              (TypeBasePure.constructors_of tyinfo)
          end
        val (tydict, dependency_decls, field_sorts) =
          List.foldl translate_constructor_doms
            (tydict_with_family, [], []) family
        fun field_sort ty =
          case List.find (fn (field_ty, _) => same_type (ty, field_ty))
              field_sorts of
            SOME (_, sort) => sort
          | NONE => smt_sort_of_type regime tydict ty
        val declaration = datatype_declaration_text field_sort family names
        val name =
          case Redblackmap.peek (tydict, ty) of
            SOME n => n
          | NONE => raise ERR "translate_datatype_type" "unregistered type"
      in
        SOME (tydict, (dependency_decls @ [declaration], name))
      end
      handle Feedback.HOL_ERR _ => NONE
           | Redblackmap.NotFound => NONE

  (* Translation has two regimes.  FirstOrder preserves the legacy,
     arity-keyed encoding: function values use nested Array sorts and
     application/update use select/store.  HigherOrder preserves first-class
     functions, lambdas, and partial application.  Standard27 emits native
     HO-Core syntax; Z3LambdaArray lowers function sorts and applications to
     nested Array/select.  Both dialects eta-expand partially applied ranked
     constants when omission would lose their built-in semantics. *)

  (* returns an updated accumulator, a (possibly empty) list of
     SMT-LIB (type and term) declarations, and the SMT-LIB
     representation of the given term *)
  fun translate_term regime apply_operator
      (acc as (tydict, tmdict), (bounds, tm)) =
  let
    fun sexpr x [] = x
      | sexpr x xs = "(" ^ x ^ " " ^ String.concatWith " " xs ^ ")"
    fun explicit_apply function argument =
      case regime of
        HigherOrder Standard27 =>
          sexpr (case apply_operator of
              ApplyUnderscore => "_"
            | ApplyAt => "@") [function, argument]
      | _ => sexpr "select" [function, argument]
    fun beta_reduce t =
      boolSyntax.rhs (Thm.concl (Drule.LIST_BETA_CONV t))
      handle Feedback.HOL_ERR _ => t
    (* Create a mapping from bound variables to their SMT-LIB names; if a
       variable is already mapped, return its existing SMT-LIB name. *)
    fun create_bound_name (bounds, v) =
      (bounds, Redblackmap.find (bounds, v))
      handle Redblackmap.NotFound =>
        let
          val name = bv_prefix ^ Int.toString (Redblackmap.numItems bounds)
        in
          (Redblackmap.insert (bounds, v, name), name)
        end
    fun builtin_symbol (rator, rands) =
      let
        val _ =
          if same_const rator intSyntax.Num_tm andalso
             mem_aconv tm (!current_raw_num_terms) then
            raise ERR "builtin_symbol" "Num retains its opaque result sort"
          else ()
        val (name, rands) = Lib.tryfind (fn parsefn => parsefn (rator, rands))
          (Net.match rator builtin_symbols)  (* may fail *)
        val (acc, declnames) = Lib.foldl_map
          (fn (a, t) =>
            translate_term regime apply_operator (a, (bounds, t)))
          (acc, rands)
        val (declss, names) = Lib.split declnames
      in
        (acc, (List.concat declss, sexpr name names))
      end
    (* Equality is a fully ranked Core operator at every HOL instantiation.
       Once its exact head and arity have been admitted, an operand failure
       must escape: falling through would eventually invent a function for
       polymorphic equality itself, and can obscure the actual unsupported
       operand (notably a residual function over a native datatype). *)
    fun builtin_equality (rator, rands) =
      if same_const rator boolSyntax.equality then
        case rands of
          [left, right] =>
            let
              val _ =
                if same_type (Term.type_of left, reglan_ty) then
                  raise ERR "builtin_equality"
                    ("HOL equality on smtstring$reglan is intensional; " ^
                     "SMT-LIB RegLan equality is language equivalence")
                else ()
              fun translate_argument (a, argument) =
                translate_term regime apply_operator
                  (a, (bounds, argument))
                handle e as Feedback.HOL_ERR _ =>
                  raise NestedTranslation e
              val (acc, declnames) =
                Lib.foldl_map translate_argument (acc, [left, right])
              val (declss, names) = Lib.split declnames
            in
              (acc, (List.concat declss, sexpr "=" names))
            end
        | _ => raise ERR "builtin_equality" "wrong equality arity"
      else
        raise ERR "builtin_equality" "not equality"
    fun set_sort tydict set =
      let
        val element_ty = set_element_type set
        val (tydict, (decls, element_sort)) =
          translate_type regime (tydict, element_ty)
      in
        (tydict, (decls, "(Set " ^ element_sort ^ ")"))
      end
    fun set_array_sort tydict set =
      let
        val element_ty = set_element_type set
        val (tydict, (decls, element_sort)) =
          translate_type regime (tydict, element_ty)
      in
        (tydict, (decls, "(Array " ^ element_sort ^ " Bool)"))
      end
    fun selected_set_sort tydict set =
      case !current_set_backend of
        CVC5ArraySet => set_array_sort tydict set
      | _ => set_sort tydict set
    fun set_constant tydict set value =
      let
        val element_ty = set_element_type set
        val (tydict, (decls, element_sort)) =
          translate_type regime (tydict, element_ty)
        val sort = "(Set " ^ element_sort ^ ")"
        val text =
          case !current_set_backend of
            Z3Set => "((as const " ^ sort ^ ") " ^ value ^ ")"
          | CVC5NativeSet =>
              "(as set." ^ (if value = "true" then "universe" else "empty") ^
              " " ^ sort ^ ")"
          | CVC5ArraySet => "((as const (Array " ^ element_sort ^
              " Bool)) " ^ value ^ ")"
      in
        (tydict, (decls, text))
      end
    fun bag_sort tydict bag =
      let
        val element_ty = bag_element_type bag
        val (tydict, (decls, element_sort)) =
          translate_type regime (tydict, element_ty)
      in
        (tydict, (decls, "(Bag " ^ element_sort ^ ")"))
      end
    fun bag_array_sort tydict bag =
      let
        val element_ty = bag_element_type bag
        val (tydict, (decls, element_sort)) =
          translate_type regime (tydict, element_ty)
      in
        (tydict, (decls, "(Array " ^ element_sort ^ " Int)"))
      end
    fun selected_bag_sort tydict bag =
      case !current_bag_backend of
        CVC5NativeBag => bag_sort tydict bag
      | _ => bag_array_sort tydict bag
    fun bound_variable_sort tydict var =
      if is_marked_set_term var then
        selected_set_sort tydict var
      else if is_marked_bag_term var then
        selected_bag_sort tydict var
      else
        translate_type regime (tydict, Term.type_of var)
    (* Emit [(head ((v0 T0) ...) body)].  [nest_errors] re-raises a body
       failure as NestedTranslation, which stops an enclosing
       [handle Feedback.HOL_ERR _] fallback from swallowing it silently. *)
    fun emit_binder {head, nest_errors} (acc as (tydict, tmdict)) vars body =
      let
        val (binder_bounds, smtvars) =
          Lib.foldl_map create_bound_name (bounds, vars)
        fun variable_type (tydict, var) = bound_variable_sort tydict var
        val (tydict, vardecltys) =
          Lib.foldl_map variable_type (tydict, vars)
        val (vardeclss, vartys) = Lib.split vardecltys
        val binders = ListPair.mapEq
          (fn (smtvar, ty) => "(" ^ smtvar ^ " " ^ ty ^ ")")
          (smtvars, vartys)
        val (acc, (bodydecls, bodyname)) =
          translate_term regime apply_operator
            ((tydict, tmdict), (binder_bounds, body))
          handle e as Feedback.HOL_ERR _ =>
            if nest_errors then raise NestedTranslation e else raise e
      in
        (acc, (List.concat vardeclss @ bodydecls,
          "(" ^ head ^ " (" ^ String.concatWith " " binders ^ ") " ^
          bodyname ^ ")"))
      end
    fun fallback_dependencies expression =
      let
        val free_vars = Term.free_vars expression
      in
        List.filter
          (fn (var, _) => List.exists (Term.aconv var) free_vars)
          (Redblackmap.listItems bounds)
      end
    fun fallback_application name dependencies =
      sexpr name (List.map Lib.snd dependencies)
    fun fallback_array_definition prefix range_sort element_type
        acc expression args body =
      let
        val dependencies = fallback_dependencies expression
        val dependency_vars = List.map Lib.fst dependencies
        val cache_key =
          (Term.list_mk_abs (dependency_vars, expression),
           List.length dependency_vars)
      in
        case Redblackmap.peek (Lib.snd acc, cache_key) of
          SOME name =>
            (acc, ([], fallback_application name dependencies))
        | NONE =>
          let
            val (tydict, (typedecls, element_sort)) =
              translate_type regime (Lib.fst acc, element_type)
            val tmdict = Lib.snd acc
            val name = prefix ^ Int.toString (Redblackmap.numItems tmdict)
            val tmdict = Redblackmap.insert (tmdict, cache_key, name)
            val binder = prefix ^ "_x" ^
              Int.toString (Redblackmap.numItems tmdict)
            val (tydict, dependency_declsorts) =
              Lib.foldl_map
                (fn (dict, (var, dependency_name)) =>
                  let
                    val (dict, (decls, sort)) =
                      bound_variable_sort dict var
                  in
                    (dict, ((decls, "(" ^ dependency_name ^ " " ^
                      sort ^ ")"), sort))
                  end)
                (tydict, dependencies)
            val (dependency_data, dependency_sorts) =
              Lib.split dependency_declsorts
            val (dependency_typedecls, dependency_decls) =
              Lib.split dependency_data
            val array_sort = "(Array " ^ element_sort ^ " " ^
              range_sort ^ ")"
            val _ = record_emitted_term_sorts cache_key
              (dependency_sorts, array_sort)
            val declaration =
              if List.null dependency_sorts then
                "(declare-const " ^ name ^ " " ^ array_sort ^ ")\n"
              else
                "(declare-fun " ^ name ^ " (" ^
                String.concatWith " " dependency_sorts ^ ") " ^
                array_sort ^ ")\n"
            val application = fallback_application name dependencies
            val quantified_decls = dependency_decls @
              ["(" ^ binder ^ " " ^ element_sort ^ ")"]
            val definition = "(assert " ^
              generated_forall quantified_decls
                ("(= (select " ^ application ^ " " ^ binder ^ ") " ^
                 body binder args ^ ")") ^ ")\n"
          in
            ((tydict, tmdict),
             (typedecls @ List.concat dependency_typedecls @
                [declaration, definition],
              application))
          end
      end
    (* cvc5's non-finite bridge deliberately stays in the ordinary array
       model.  Pointwise set operations are named arrays constrained by a
       quantified definition, rather than cvc5's finite set operators. *)
    fun fallback_set_definition acc set args body =
      fallback_array_definition "set" "Bool" (set_element_type set)
        acc set args body
    fun native_sequence_symbol rator rands =
      !current_native_sequence_emission andalso
      List.all (fn part =>
        not (listSyntax.is_list_type (Term.type_of part)) orelse
        is_native_sequence_type (Term.type_of part)) (tm :: rands) andalso
      (listSyntax.is_nil tm orelse
      ((same_const rator intSyntax.int_injection orelse
        same_const rator int_of_num_tm) andalso
       (case rands of
          [arg] => same_const (Lib.fst (boolSyntax.strip_comb arg))
            seq_length_tm
        | _ => false)) orelse
      Option.isSome (Lib.total dest_string_nth_shape tm) orelse
      Option.isSome (Lib.total dest_seq_extract_shape tm) orelse
      Option.isSome (Lib.total dest_seq_at_shape tm) orelse
      List.exists (fn head => same_const rator head) [
        seq_append_tm, seq_cons_tm, seq_reverse_tm,
        seq_prefix_tm, seq_lupdate_tm, seq_map_tm, seq_foldl_tm,
        seq_contains_tm, seq_suffix_tm,
        smt_seq_nth_tm,
        smt_seq_extract_tm, smt_seq_at_tm, smt_seq_indexof_tm,
        smt_seq_replace_tm, smt_seq_replace_all_tm, smt_seq_update_tm])
    fun native_sequence_builtin (rator, rands) =
      let
        fun translate_args_from start args =
          let
            val (acc, declnames) = Lib.foldl_map
              (fn (a, arg) =>
                translate_term regime apply_operator (a, (bounds, arg)))
              (start, args)
            val (declss, names) = Lib.split declnames
          in
            (acc, (List.concat declss, names))
          end
        fun translate_args args = translate_args_from acc args
        (* A function-valued fold callback must keep its own binders
           separate from the accumulator it returns, so the two callback
           arguments cannot be left to the single-binder lowering.  Unlike
           the two lambda sites, this one leaves a body failure as a plain
           HOL_ERR, so the enclosing fallback chain still gets to try the
           uninterpreted lowering. *)
        fun translate_fold_function function =
          case Term.strip_abs function of
            (element :: accumulator :: rest, body) =>
              emit_binder {head = "lambda", nest_errors = false} acc
                [element, accumulator] (Term.list_mk_abs (rest, body))
          | _ =>
              translate_term regime apply_operator (acc, (bounds, function))
        fun emit name args =
          let val (acc, (decls, names)) = translate_args args
          in (acc, (decls, sexpr name names)) end
        fun emit_foldl args =
          case args of
            function :: rest =>
              let
                val (acc, (function_decls, function_name)) =
                  translate_fold_function function
                val (acc, (rest_decls, rest_names)) =
                  translate_args_from acc rest
              in
                (acc, (function_decls @ rest_decls,
                  sexpr "seq.foldl" (function_name :: rest_names)))
              end
          | [] => raise ERR "native_sequence_builtin" "wrong FOLDL arity"
        fun emit_extract (sequence, index, size) =
          emit "seq.extract" [sequence, index, size]
        fun emit_at (sequence, index) = emit "seq.at" [sequence, index]
      in
        if same_const rator intSyntax.int_injection orelse
           same_const rator int_of_num_tm then
          (case rands of
             [length] =>
               let val (head, args) = boolSyntax.strip_comb length in
                 if same_const head seq_length_tm then emit "seq.len" args
                 else raise ERR "native_sequence_builtin" "wrong length"
               end
           | _ => raise ERR "native_sequence_builtin" "wrong coercion")
        else
          (case Lib.total dest_string_nth_shape tm of
             SOME (string, index) => emit "seq.nth" [string, index]
           | NONE =>
          (case Lib.total dest_seq_extract_shape tm of
          SOME shape => emit_extract shape
        | NONE =>
          (case Lib.total dest_seq_at_shape tm of
             SOME shape => emit_at shape
           | NONE =>
             if listSyntax.is_nil tm then
               let
                 val (tydict, (decls, element_sort)) =
                   translate_type regime
                     (Lib.fst acc, sequence_element_type tm)
               in
                 ((tydict, Lib.snd acc), (decls,
                   "(as seq.empty (Seq " ^ element_sort ^ "))"))
               end
             else if same_const rator seq_append_tm then emit "seq.++" rands
             else if same_const rator seq_length_tm then emit "seq.len" rands
             else if same_const rator seq_cons_tm then
               (case rands of
                  [element, tail] =>
                    let val (acc, (decls, names)) = translate_args rands in
                      case names of [element_name, tail_name] =>
                        if listSyntax.is_nil tail then
                          (acc, (decls, sexpr "seq.unit" [element_name]))
                        else
                          (acc, (decls, sexpr "seq.++"
                            [sexpr "seq.unit" [element_name], tail_name]))
                    | _ => raise ERR "native_sequence_builtin"
                        "wrong cons arity"
                    end
                | _ => raise ERR "native_sequence_builtin" "wrong cons arity")
             else if same_const rator seq_reverse_tm then emit "seq.rev" rands
             else if same_const rator seq_prefix_tm then
               emit "seq.prefixof" rands
             else if same_const rator seq_suffix_tm then
               (case rands of
                  [sequence, suffix] =>
                    emit "seq.suffixof" [suffix, sequence]
                | _ => raise ERR "native_sequence_builtin"
                    "wrong suffix arity")
             else if same_const rator seq_lupdate_tm then
               (case rands of [element, index, sequence] =>
                  emit "seq.update"
                    [sequence, Term.mk_comb (int_of_num_tm, index),
                     listSyntax.mk_cons (element,
                       listSyntax.mk_nil (Term.type_of element))]
                | _ => raise ERR "native_sequence_builtin"
                    "wrong LUPDATE arity")
             else if same_const rator seq_map_tm then emit "seq.map" rands
             else if same_const rator seq_foldl_tm then emit_foldl rands
             else if same_const rator seq_contains_tm then
               emit "seq.contains" rands
             else if same_const rator smt_seq_nth_tm then emit "seq.nth" rands
             else if same_const rator smt_seq_extract_tm then
               emit "seq.extract" rands
             else if same_const rator smt_seq_at_tm then emit "seq.at" rands
             else if same_const rator smt_seq_indexof_tm then
               emit "seq.indexof" rands
             else if same_const rator smt_seq_replace_tm then
               emit "seq.replace" rands
             else if same_const rator smt_seq_replace_all_tm then
               emit "seq.replace_all" rands
             else if same_const rator smt_seq_update_tm then
               emit "seq.update" rands
             else raise ERR "native_sequence_builtin"
               "unsupported native sequence term")))
      end
    fun native_set_symbol rator rands =
      same_const rator pred_setSyntax.in_tm orelse
      is_native_set_head rator orelse
      ((same_const rator intSyntax.int_injection orelse
        same_const rator int_of_num_tm) andalso
       (case rands of [arg] => pred_setSyntax.is_card arg | _ => false))
    fun native_set_builtin (rator, rands) =
      if same_const rator intSyntax.int_injection orelse
         same_const rator int_of_num_tm then
        (case rands of [card] =>
           let
             val set = pred_setSyntax.dest_card card
             val (acc, (decls, name)) =
               translate_term regime apply_operator (acc, (bounds, set))
           in
             case !current_set_backend of
               CVC5NativeSet => (acc, (decls, sexpr "set.card" [name]))
             | Z3Set => raise ERR "native_set_builtin"
                 "set.card is unavailable for solver Z3"
             | CVC5ArraySet => raise ERR "native_set_builtin"
                 "set.card requires a finiteness-entailing cvc5 goal"
           end
         | _ => raise ERR "native_set_builtin" "wrong card arity")
      else
      let
        val (acc, declnames) = Lib.foldl_map
          (fn (a, t) => translate_term regime apply_operator (a, (bounds, t)))
          (acc, rands)
        val (declss, names) = Lib.split declnames
        val decls = List.concat declss
        fun binary z3 cvc5 fallback =
          case names of [left, right] =>
            (case !current_set_backend of
               Z3Set => (acc, (decls, sexpr z3 [left, right]))
             | CVC5NativeSet => (acc, (decls, sexpr cvc5 [left, right]))
             | CVC5ArraySet =>
                 let
                   fun body x [l, r] = fallback x l r
                     | body _ _ = raise ERR "native_set_builtin" "arity"
                   val (acc, (defs, name)) =
                     fallback_set_definition acc tm names body
                 in (acc, (decls @ defs, name)) end)
          | _ => raise ERR "native_set_builtin" "wrong binary set arity"
        fun unary z3 cvc5 =
          case names of [set] =>
            (case !current_set_backend of
               Z3Set => (acc, (decls, sexpr z3 [set]))
             | CVC5NativeSet => (acc, (decls, sexpr cvc5 [set]))
             | CVC5ArraySet =>
                 let
                   fun body x [s] = sexpr "not" [sexpr "select" [s, x]]
                     | body _ _ = raise ERR "native_set_builtin" "arity"
                   val (acc, (defs, name)) =
                     fallback_set_definition acc tm names body
                 in (acc, (decls @ defs, name)) end)
          | _ => raise ERR "native_set_builtin" "wrong unary set arity"
      in
        if same_const rator pred_setSyntax.in_tm then
          (case names of [element, set] =>
             (acc, (decls,
               case !current_set_backend of
                 CVC5NativeSet => sexpr "set.member" [element, set]
               | _ => sexpr "select" [set, element]))
           | _ => raise ERR "native_set_builtin" "wrong membership arity")
        else if same_const rator pred_setSyntax.insert_tm then
          (case (rands, names) of
             ([element, set], [element_name, set_name]) =>
               let
                 val singleton = pred_setSyntax.is_empty set
                 val text =
                   case !current_set_backend of
                     Z3Set => sexpr "store" [set_name, element_name, "true"]
                   | CVC5NativeSet =>
                       if singleton then sexpr "set.singleton" [element_name]
                       else sexpr "set.insert" [element_name, set_name]
                   | CVC5ArraySet =>
                       sexpr "store" [set_name, element_name, "true"]
               in (acc, (decls, text)) end
           | _ => raise ERR "native_set_builtin" "wrong insert arity")
        else if same_const rator pred_setSyntax.delete_tm then
          (case names of [set, element] =>
             (case !current_set_backend of
                CVC5NativeSet => (acc, (decls,
                  sexpr "set.minus" [set, sexpr "set.singleton" [element]]))
              | _ => (acc, (decls, sexpr "store" [set, element, "false"])))
           | _ => raise ERR "native_set_builtin" "wrong delete arity")
        else if same_const rator pred_setSyntax.union_tm then
          binary "union" "set.union"
            (fn x => fn left => fn right =>
              sexpr "or" [sexpr "select" [left, x], sexpr "select" [right, x]])
        else if same_const rator pred_setSyntax.inter_tm then
          binary "intersection" "set.inter"
            (fn x => fn left => fn right =>
              sexpr "and" [sexpr "select" [left, x], sexpr "select" [right, x]])
        else if same_const rator pred_setSyntax.diff_tm then
          binary "setminus" "set.minus"
            (fn x => fn left => fn right =>
              let
                val in_left = sexpr "select" [left, x]
                val in_right = sexpr "select" [right, x]
              in
                sexpr "and" [in_left, sexpr "not" [in_right]]
              end)
        else if same_const rator pred_setSyntax.compl_tm then
          unary "complement" "set.complement"
        else if same_const rator pred_setSyntax.subset_tm then
          (case names of [left, right] =>
             (case !current_set_backend of
                Z3Set => (acc, (decls, sexpr "subset" [left, right]))
              | CVC5NativeSet => (acc, (decls, sexpr "set.subset" [left, right]))
              | CVC5ArraySet =>
                  let
                    val element_ty = set_element_type (List.hd rands)
                    val (tydict, (typedecls, element_sort)) =
                      translate_type regime (Lib.fst acc, element_ty)
                    val tmdict = Lib.snd acc
                    val binder = "set_x" ^ Int.toString
                      (Redblackmap.numItems tmdict)
                  in
                    ((tydict, tmdict), (decls @ typedecls,
                      generated_forall
                        ["(" ^ binder ^ " " ^ element_sort ^ ")"]
                        ("(=> (select " ^ left ^ " " ^ binder ^ ") " ^
                         "(select " ^ right ^ " " ^ binder ^ "))")))
                  end)
           | _ => raise ERR "native_set_builtin" "wrong subset arity")
        else if pred_setSyntax.is_empty tm then
          let val (tydict, (constant_decls, text)) =
            set_constant (Lib.fst acc) tm "false"
          in ((tydict, Lib.snd acc), (constant_decls, text)) end
        else if pred_setSyntax.is_univ tm then
          let val (tydict, (constant_decls, text)) =
            set_constant (Lib.fst acc) tm "true"
          in ((tydict, Lib.snd acc), (constant_decls, text)) end
        else
          raise ERR "native_set_builtin" "unsupported native set term"
      end
    fun bag_constant tydict bag =
      let
        val element_ty = bag_element_type bag
        val (tydict, (decls, element_sort)) =
          translate_type regime (tydict, element_ty)
        val text =
          case !current_bag_backend of
            CVC5NativeBag => "(as bag.empty (Bag " ^ element_sort ^ "))"
          | _ => "((as const (Array " ^ element_sort ^ " Int)) 0)"
      in
        (tydict, (decls, text))
      end
    fun translate_parsed_bag_literal acc =
      let
        val (element, count) = dest_parsed_bag_literal tm
        val (acc, (element_decls, element_name)) =
          translate_term regime apply_operator (acc, (bounds, element))
        val (acc, (count_decls, count_name)) =
          translate_term regime apply_operator (acc, (bounds, count))
        val (tydict, (type_decls, element_sort)) =
          translate_type regime (Lib.fst acc, Term.type_of element)
        val text =
          case !current_bag_backend of
            CVC5NativeBag => sexpr "bag" [element_name, count_name]
          | _ =>
              let
                val array_count =
                  sexpr "ite"
                    [sexpr "<=" ["0", count_name], count_name, "0"]
              in
                sexpr "store"
                  ["((as const (Array " ^ element_sort ^ " Int)) 0)",
                   element_name, array_count]
              end
      in
        ((tydict, Lib.snd acc),
         (element_decls @ count_decls @ type_decls, text))
      end
    fun fallback_bag_definition acc bag args body =
      fallback_array_definition "bag" "Int" (bag_element_type bag)
        acc bag args body
    fun z3_bag_helper name definition =
      if List.exists (fn known => known = name) (!current_bag_helpers) then []
      else
        (current_bag_helpers := name :: !current_bag_helpers; [definition])
    fun native_bag_count_application rator rands =
      case rands of
        [left, right, element] =>
          if same_const rator bagSyntax.BAG_INSERT_tm orelse
             same_const rator bagSyntax.BAG_UNION_tm orelse
             same_const rator bagSyntax.BAG_DIFF_tm orelse
             same_const rator bag_merge_tm orelse
             same_const rator bag_inter_tm then
            SOME (Term.list_mk_comb (rator, [left, right]), element)
          else NONE
      | [element] =>
          if same_const rator bagSyntax.EMPTY_BAG_tm then
            SOME (rator, element)
          else NONE
      | _ => NONE
    fun native_bag_symbol rator rands =
      ((case rands of
          [_, _] => same_const rator bag_in_tm orelse
                    same_const rator bagSyntax.BAG_INSERT_tm orelse
                    same_const rator bagSyntax.BAG_UNION_tm orelse
                    same_const rator bagSyntax.BAG_DIFF_tm orelse
                    same_const rator bag_merge_tm orelse
                    same_const rator bag_inter_tm orelse
                    same_const rator bagSyntax.SUB_BAG_tm
        | [arg] =>
            (same_const rator bagSyntax.BAG_CARD_tm andalso
             not (mem_aconv (Term.mk_comb (rator, arg))
               (!current_raw_num_terms)))
        | [] => same_const rator bagSyntax.EMPTY_BAG_tm
        | _ => false) orelse
       ((same_const rator intSyntax.int_injection orelse
         same_const rator int_of_num_tm) andalso
        (case rands of
           [arg] =>
             bagSyntax.is_card arg orelse
             Option.isSome
               (native_bag_count_application (Lib.fst (boolSyntax.strip_comb arg))
                 (Lib.snd (boolSyntax.strip_comb arg)))
         | _ => false)))
    fun native_bag_builtin (rator, rands) =
      if same_const rator intSyntax.int_injection orelse
         same_const rator int_of_num_tm then
        (case rands of [card] =>
           (case native_bag_count_application
               (Lib.fst (boolSyntax.strip_comb card))
               (Lib.snd (boolSyntax.strip_comb card)) of
              SOME (bag, element) =>
                let
                  val (acc, (bag_decls, bag_name)) =
                    translate_term regime apply_operator (acc, (bounds, bag))
                  val (acc, (element_decls, element_name)) =
                    translate_term regime apply_operator
                      (acc, (bounds, element))
                  val count =
                    case !current_bag_backend of
                      CVC5NativeBag =>
                        sexpr "bag.count" [element_name, bag_name]
                    | _ => sexpr "select" [bag_name, element_name]
                in
                  (acc, (bag_decls @ element_decls, count))
                end
            | NONE =>
                let
                  val bag = bagSyntax.dest_card card
                  val (acc, (decls, name)) =
                    translate_term regime apply_operator (acc, (bounds, bag))
                in
                  case !current_bag_backend of
                    CVC5NativeBag => (acc, (decls, sexpr "bag.card" [name]))
                  | Z3ArrayBag => raise ERR "native_bag_builtin"
                      "bag.card is unavailable for solver Z3"
                  | CVC5ArrayBag => raise ERR "native_bag_builtin"
                      "bag.card requires a finiteness-entailing cvc5 goal"
                end)
         | _ => raise ERR "native_bag_builtin" "wrong card arity")
      else if same_const rator bagSyntax.BAG_CARD_tm then
        (case rands of [bag] =>
           let
             val (acc, (decls, name)) =
               translate_term regime apply_operator (acc, (bounds, bag))
           in
             case !current_bag_backend of
               CVC5NativeBag => (acc, (decls, sexpr "bag.card" [name]))
             | Z3ArrayBag => raise ERR "native_bag_builtin"
                 "bag.card is unavailable for solver Z3"
             | CVC5ArrayBag => raise ERR "native_bag_builtin"
                 "bag.card requires a finiteness-entailing cvc5 goal"
           end
         | _ => raise ERR "native_bag_builtin" "wrong card arity")
      else
      let
        fun translate_bag_arg (a, t) =
          translate_term regime apply_operator (a, (bounds, t))
        val (acc, declnames) = Lib.foldl_map translate_bag_arg (acc, rands)
        val (declss, names) = Lib.split declnames
        val decls = List.concat declss
        fun fallback body =
          let
            val (acc, (defs, name)) =
              fallback_bag_definition acc tm names body
          in (acc, (decls @ defs, name)) end
        fun binary native z3 fallback_body =
          case names of [left, right] =>
            (case !current_bag_backend of
               CVC5NativeBag => (acc, (decls, sexpr native [left, right]))
             | Z3ArrayBag =>
                 let val (map_decls, map_name) = z3 () in
                   (acc, (decls @ map_decls,
                     "((_ map " ^ map_name ^ ") " ^ left ^ " " ^ right ^ ")"))
                 end
             | CVC5ArrayBag => fallback fallback_body)
          | _ => raise ERR "native_bag_builtin" "wrong binary bag arity"
      in
        if same_const rator bag_in_tm then
          (case names of [element, bag] =>
             (acc, (decls,
               case !current_bag_backend of
                 CVC5NativeBag => sexpr "bag.member" [element, bag]
               | _ => sexpr "<" ["0", sexpr "select" [bag, element]]))
           | _ => raise ERR "native_bag_builtin" "wrong membership arity")
        else if same_const rator bagSyntax.BAG_INSERT_tm then
          (case names of [element, bag] =>
             (acc, (decls,
               case !current_bag_backend of
                 CVC5NativeBag => sexpr "bag.union_disjoint"
                   [sexpr "bag" [element, "1"], bag]
               | _ => sexpr "store" [bag, element,
                   sexpr "+" [sexpr "select" [bag, element], "1"]]))
           | _ => raise ERR "native_bag_builtin" "wrong insert arity")
        else if same_const rator bagSyntax.BAG_UNION_tm then
          binary "bag.union_disjoint"
            (fn () => ([], "(+ (Int Int) Int)"))
            (fn x => fn [left, right] =>
              sexpr "+" [sexpr "select" [left, x],
                sexpr "select" [right, x]]
              | _ => raise ERR "native_bag_builtin" "wrong fallback arity")
        else if same_const rator bagSyntax.BAG_DIFF_tm then
          binary "bag.difference_subtract"
            (fn () => (z3_bag_helper "holsmt_bag_nat_sub"
              ("(define-fun holsmt_bag_nat_sub ((x Int) (y Int)) Int " ^
               "(ite (< x y) 0 (- x y)))\n"), "holsmt_bag_nat_sub"))
            (fn x => fn [left, right] =>
              sexpr "ite" [sexpr "<" [sexpr "select" [left, x],
                sexpr "select" [right, x]], "0",
                sexpr "-" [sexpr "select" [left, x],
                  sexpr "select" [right, x]]]
              | _ => raise ERR "native_bag_builtin" "wrong fallback arity")
        else if same_const rator bag_merge_tm then
          binary "bag.union_max"
            (fn () => (z3_bag_helper "holsmt_bag_max"
              ("(define-fun holsmt_bag_max ((x Int) (y Int)) Int " ^
               "(ite (< x y) y x))\n"), "holsmt_bag_max"))
            (fn x => fn [left, right] =>
              sexpr "ite" [sexpr "<" [sexpr "select" [left, x],
                sexpr "select" [right, x]], sexpr "select" [right, x],
                sexpr "select" [left, x]]
              | _ => raise ERR "native_bag_builtin" "wrong fallback arity")
        else if same_const rator bag_inter_tm then
          binary "bag.inter_min"
            (fn () => (z3_bag_helper "holsmt_bag_min"
              ("(define-fun holsmt_bag_min ((x Int) (y Int)) Int " ^
               "(ite (< x y) x y))\n"), "holsmt_bag_min"))
            (fn x => fn [left, right] =>
              sexpr "ite" [sexpr "<" [sexpr "select" [left, x],
                sexpr "select" [right, x]], sexpr "select" [left, x],
                sexpr "select" [right, x]]
              | _ => raise ERR "native_bag_builtin" "wrong fallback arity")
        else if same_const rator bagSyntax.SUB_BAG_tm then
          (case names of [left, right] =>
             (case !current_bag_backend of
                CVC5NativeBag =>
                  (acc, (decls, sexpr "bag.subbag" [left, right]))
              | _ =>
                  let
                    val element_ty = bag_element_type (List.hd rands)
                    val (tydict, (typedecls, element_sort)) =
                      translate_type regime (Lib.fst acc, element_ty)
                    val binder = "bag_x" ^ Int.toString
                      (Redblackmap.numItems (Lib.snd acc))
                  in
                    ((tydict, Lib.snd acc), (decls @ typedecls,
                      generated_forall
                        ["(" ^ binder ^ " " ^ element_sort ^ ")"]
                        ("(<= (select " ^ left ^ " " ^ binder ^ ") " ^
                         "(select " ^ right ^ " " ^ binder ^ "))")))
                  end)
           | _ => raise ERR "native_bag_builtin" "wrong subbag arity")
        else if bagSyntax.is_empty tm then
          let val (tydict, (constant_decls, text)) =
            bag_constant (Lib.fst acc) tm
          in ((tydict, Lib.snd acc), (constant_decls, text)) end
        else
          raise ERR "native_bag_builtin" "unsupported native bag term"
      end
    fun ensure_type ((tydict, tmdict), ty) =
      let val (tydict, (decls, name)) = translate_type regime (tydict, ty)
      in (((tydict, tmdict), decls), name) end
    fun translate_closed_destructor_residual acc =
      let
        val _ = closed_constructor_destructor_residual tm orelse
          raise ERR "translate_closed_destructor_residual"
            "not a closed constructor-headed destructor residue"
        val (((tydict, tmdict), typedecls), sort) =
          ensure_type (acc, Term.type_of tm)
      in
        case Redblackmap.peek (tmdict, (tm, 0)) of
          SOME name => ((tydict, tmdict), (typedecls, name))
        | NONE =>
            let
              val name = tm_prefix ^
                Int.toString (Redblackmap.numItems tmdict)
              val tmdict = Redblackmap.insert (tmdict, (tm, 0), name)
              val declaration = term_declaration_text regime name [] sort
              val _ = record_emitted_term_sorts (tm, 0) ([], sort)
            in
              ((tydict, tmdict), (typedecls @ [declaration], name))
            end
      end
    fun translate_injected_string acc =
      let
        val string = dest_injected_string tm
      in
        case Redblackmap.peek (bounds, string) of
          SOME name => (acc, ([], name))
        | NONE =>
          let
            val depends_on_bound =
              List.exists
                (fn v => Option.isSome (Redblackmap.peek (bounds, v)))
                (Term.free_vars string)
            val _ =
              if depends_on_bound then
                raise ERR "translate_injected_string"
                  "non-atomic injected term depends on a bound variable"
              else
                ()
          in
            case Redblackmap.peek (tmdict, (tm, 0)) of
              SOME name => (acc, ([], name))
            | NONE =>
              let
                val name =
                  tm_prefix ^ Int.toString (Redblackmap.numItems tmdict)
                val tmdict = Redblackmap.insert (tmdict, (tm, 0), name)
                val declaration =
                  term_declaration_text regime name [] "String"
              in
                ((tydict, tmdict), ([declaration], name))
              end
          end
      end
    fun translate_injected_float acc =
      let
        val float = dest_injected_float tm
        val sort = smtfp_sort (Term.type_of tm)
      in
        case Redblackmap.peek (bounds, float) of
          SOME _ =>
            raise ERR "translate_injected_float"
              "injected float binder was not transferred"
        | NONE =>
          let
            val depends_on_bound =
              List.exists
                (fn v => Option.isSome (Redblackmap.peek (bounds, v)))
                (Term.free_vars float)
            val _ =
              if depends_on_bound then
                raise ERR "translate_injected_float"
                  "non-atomic injected term depends on a bound variable"
              else
                ()
          in
            case Redblackmap.peek (tmdict, (tm, 0)) of
              SOME name => (acc, ([], name))
            | NONE =>
              let
                val name =
                  tm_prefix ^ Int.toString (Redblackmap.numItems tmdict)
                val tmdict = Redblackmap.insert (tmdict, (tm, 0), name)
                val declaration =
                  term_declaration_text regime name [] sort
              in
                ((tydict, tmdict), ([declaration], name))
              end
          end
      end
    fun translate_injected_string_operation acc =
      let
        val (name, rands) = dest_injected_string_operation tm
        val (acc, declnames) = Lib.foldl_map
          (fn (a, t) =>
            translate_term regime apply_operator (a, (bounds, t)))
          (acc, rands)
        val (declss, names) = Lib.split declnames
      in
        (acc, (List.concat declss, sexpr name names))
      end
    fun has_ranked_semantics c =
      TypeBase.is_constructor c orelse
      (Term.is_const c andalso
        let val {Thy, Name, ...} = Term.dest_thy_const c
        in Redblackset.member (builtin_const_names, (Thy, Name)) end)
    fun translate_lambda acc =
      let val (v, body) = Term.dest_abs tm in
        emit_binder {head = "lambda", nest_errors = true} acc [v] body
      end
    fun eta_expand_ranked_constant acc applied rator rank rands_count =
      let
        fun drop 0 ty = ty
          | drop n ty = drop (n - 1) (Lib.snd (Type.dom_rng ty))
        fun take_doms 0 _ acc = List.rev acc
          | take_doms n ty acc =
              let val (dom, rng) = Type.dom_rng ty
              in take_doms (n - 1) rng (dom :: acc) end
        val residual_ty = drop rands_count (Term.type_of rator)
        val missing_doms =
          take_doms (rank - rands_count) residual_ty []
        val vars = List.map Term.genvar missing_doms
        val expanded = Term.list_mk_abs
          (vars, Term.list_mk_comb (applied, vars))
      in
        translate_term regime apply_operator (acc, (bounds, expanded))
        handle e as Feedback.HOL_ERR _ => raise NestedTranslation e
      end
    fun constructor_info_for tydict ty constructor =
      let
        val type_name =
          case Redblackmap.peek (tydict, ty) of
            SOME name => name
          | NONE => raise ERR "translate_term" "datatype type not registered"
        val infos = datatype_constructor_infos ty type_name
      in
        case List.find (fn (constructor', _, _) =>
            Term.same_const constructor constructor') infos of
          SOME info => info
        | NONE => raise ERR "translate_term" "constructor name not found"
      end
    fun translate_constructor_application acc rator rands =
      let
        val _ = TypeBase.is_constructor rator
        val (doms, data_ty) = boolSyntax.strip_fun (Term.type_of rator)
        val _ = not (datatype_translation_excluded data_ty) orelse
          raise ERR "translate_term" "excluded datatype constructor"
        val arity = List.length doms
        val _ =
          if List.length rands = arity then ()
          else raise ERR "translate_term" "partial constructor application"
        val (((tydict, tmdict), typedecls), _) = ensure_type (acc, data_ty)
        val (_, cname, _) = constructor_info_for tydict data_ty rator
        val tmdict = Redblackmap.insert (tmdict, (rator, arity), cname)
        val acc = (tydict, tmdict)
        val (acc, declnames) = Lib.foldl_map
          (fn (a, t) =>
            translate_term regime apply_operator (a, (bounds, t)))
          (acc, rands)
        val (declss, names) = Lib.split declnames
      in
        (acc, (typedecls @ List.concat declss, sexpr cname names))
      end
    fun translate_selector_case acc =
      let
        val {constructor, selector_index, scrutinee} =
          case parser_datatype_case tm of
            SOME (ParserSelector fields) => fields
          | _ => raise ERR "translate_term" "not a selector case"
        val data_ty = Term.type_of scrutinee
        val (((tydict, tmdict), typedecls), _) =
          ensure_type (acc, data_ty)
        val type_name = Redblackmap.find (tydict, data_ty)
        val infos = datatype_constructor_infos data_ty type_name
        val selector_name =
          case List.find
              (fn (constructor', _, _) =>
                Term.same_const constructor constructor') infos of
            SOME (_, _, selectors) =>
              Lib.fst (List.nth (selectors, selector_index))
          | NONE => raise ERR "translate_term" "selector constructor missing"
        val acc = (tydict, tmdict)
        val (acc, (elemdecls, elemname)) =
          translate_term regime apply_operator (acc, (bounds, scrutinee))
      in
        (acc, (typedecls @ elemdecls, sexpr selector_name [elemname]))
      end
    fun translate_tester_case acc =
      let
        val {constructor, scrutinee} =
          case parser_datatype_case tm of
            SOME (ParserTester fields) => fields
          | _ => raise ERR "translate_term" "not a tester case"
        val data_ty = Term.type_of scrutinee
        val (((tydict, tmdict), typedecls), _) = ensure_type (acc, data_ty)
        val type_name = Redblackmap.find (tydict, data_ty)
        val infos = datatype_constructor_infos data_ty type_name
        val constructor_name =
          case List.find
              (fn (constructor', _, _) =>
                Term.same_const constructor constructor') infos of
            SOME (_, name, _) => name
          | NONE => raise ERR "translate_term" "tester constructor missing"
        val acc = (tydict, tmdict)
        val (acc, (elemdecls, elemname)) =
          translate_term regime apply_operator (acc, (bounds, scrutinee))
      in
        (acc, (typedecls @ elemdecls,
          sexpr ("(_ is " ^ constructor_name ^ ")") [elemname]))
      end
    fun translate_case_constant acc rator rands =
      let
        val (elem, cases) =
          case rands of
            elem :: cases => (elem, cases)
          | [] => raise ERR "translate_term" "case constant without scrutinee"
        val data_ty = Term.type_of elem
        val tyinfo =
          case TypeBase.fetch data_ty of
            SOME info => info
          | NONE => raise ERR "translate_term" "case scrutinee not datatype"
        val _ =
          if Term.same_const rator (TypeBasePure.case_const_of tyinfo) then ()
          else raise ERR "translate_term" "not datatype case constant"
        val _ =
          if List.length cases = List.length (TypeBasePure.constructors_of tyinfo)
          then ()
          else raise ERR "translate_term" "wrong number of case branches"
        val (((tydict, tmdict), typedecls), _) = ensure_type (acc, data_ty)
        val type_name = Redblackmap.find (tydict, data_ty)
        val infos = datatype_constructor_infos data_ty type_name
        fun selector_terms (constructor, _, selectors) =
          List.map (fn n => datatype_selector_term data_ty constructor n elem)
            (List.tabulate (List.length selectors, fn n => n))
        fun branch_term (casefn, info) =
          beta_reduce (Term.list_mk_comb (casefn, selector_terms info))
        val branch_terms = ListPair.mapEq branch_term (cases, infos)
        val acc = (tydict, tmdict)
        val (acc, (elemdecls, elemname)) =
          translate_term regime apply_operator (acc, (bounds, elem))
        val (acc, declbranches) = Lib.foldl_map
          (fn (a, t) =>
            translate_term regime apply_operator (a, (bounds, t)))
          (acc, branch_terms)
        val (branchdeclss, branchnames) = Lib.split declbranches
        fun tester (_, cname, _) = sexpr ("(_ is " ^ cname ^ ")") [elemname]
        fun cascaded [] [] = raise ERR "translate_term" "empty datatype case"
          | cascaded [_] [branch] = branch
          | cascaded (info :: infos) (branch :: branches) =
              sexpr "ite" [tester info, branch, cascaded infos branches]
          | cascaded _ _ = raise ERR "translate_term" "case branch mismatch"
      in
        (acc, (typedecls @ elemdecls @ List.concat branchdeclss,
          cascaded infos branchnames))
      end
    fun has_semantic_function_prefix head rands =
      let
        fun loop _ [] = false
          | loop applied (rand :: rands) =
              let val applied = Term.mk_comb (applied, rand)
              in
                (is_function_type (Term.type_of applied) andalso
                 (Lib.can TypeBase.dest_case applied orelse
                  combinSyntax.is_update_comb applied orelse
                  Option.isSome (builtin_encoding applied))) orelse
                loop applied rands
              end
      in
        loop head rands
      end
      handle Feedback.HOL_ERR _ => false
    val tm_has_base_type = not (Lib.can Type.dom_rng (Term.type_of tm))
    val _ =
      (case Lib.total Term.dest_comb tm of
         SOME (head, code) =>
           if same_const smtstr_char_tm head then
             ignore
               (hexadecimal_string
                 "<builtin_symbols.smtstr_char>" code)
           else ()
       | NONE => ())
      handle e as Feedback.HOL_ERR _ => raise NestedTranslation e
    val literal = Lib.total native_string_literal tm
  in
    case literal of
      SOME text => (acc, ([], text))
    | NONE =>
    (* binders *)
    let
      val (binder, vars, body) =
        if boolSyntax.is_forall tm then
          let val (vars, body) = boolSyntax.strip_forall tm
          in ("forall", vars, body) end
        else if boolSyntax.is_exists tm then
          let val (vars, body) = boolSyntax.strip_exists tm
          in ("exists", vars, body) end
        else
          raise ERR "translate_term" "not a binder"
    in
      emit_binder {head = binder, nest_errors = true} acc vars body
    end
    handle Feedback.HOL_ERR _ =>

    (* let binder - somewhat similar to quantifiers *)
    let
      val (bindings, body) = pairSyntax.dest_anylet tm
      val (vars, bodies) = ListPair.unzip bindings
      (* we should translate the bodies without first creating the bound names *)
      val bounds_bodies = List.map (fn body => (bounds, body)) bodies
      val (acc, decls_bodies) =
        Lib.foldl_map
          (fn (a, bound_body) =>
            translate_term regime apply_operator (a, bound_body))
          (acc, bounds_bodies)
      (* now we can create the bound names *)
      val (bounds, smtvars) = Lib.foldl_map create_bound_name (bounds, vars)
      val decls_bodies_smtvars = ListPair.zipEq (decls_bodies, smtvars)
      val (decls, smtbinds) = List.foldl (fn (((d, b), v), (decls, smtbinds)) =>
        (d @ decls, "(" ^ v ^ " " ^ b ^ ")" :: smtbinds)) ([], [])
          decls_bodies_smtvars
      val bindings_str = String.concatWith " " (List.rev smtbinds)
      val (acc, (bodydecls, body)) =
        translate_term regime apply_operator (acc, (bounds, body))
    in
      (acc, (decls @ bodydecls,
        "(let (" ^ bindings_str ^ ") " ^ body ^ ")"))
    end
    handle Feedback.HOL_ERR _ =>

    (* bound variables may shadow built-in symbols etc. *)
    (acc, ([], Redblackmap.find (bounds, tm)))
    handle Redblackmap.NotFound =>

    (* Each str_inj image is generalized to an SMT String value.  Proving the
       strengthened SMT formula over every Unicode string and then using the
       tactic validation at this image is the sound direction. *)
    (if is_injected_string tm then
       translate_injected_string acc
       handle e as Feedback.HOL_ERR _ => raise NestedTranslation e
     else
       raise ERR "translate_term" "not an injected string")
    handle e as NestedTranslation _ => raise e
         | Feedback.HOL_ERR _ =>

    (* Each smtfp_intro image is generalized to an SMT FloatingPoint value.
       The carrier theorem proves surjectivity, while the preprocessing
       homomorphisms ensure that only intro-invariant native operations reach
       this branch. *)
    (if is_injected_float tm then
       translate_injected_float acc
       handle e as Feedback.HOL_ERR _ => raise NestedTranslation e
     else
       raise ERR "translate_term" "not an injected float")
    handle e as NestedTranslation _ => raise e
         | Feedback.HOL_ERR _ =>

    (* Terms produced by HOL_STRING_TO_SMT_CONV use this transfer-specific
       path.  Dedicated smtstr terms use the ordinary builtin table above. *)
    (if is_injected_string_operation tm then
       translate_injected_string_operation acc
       handle e as Feedback.HOL_ERR _ => raise NestedTranslation e
     else
       raise ERR "translate_term" "not an injected string operation")
    handle e as NestedTranslation _ => raise e
         | Feedback.HOL_ERR _ =>

    (* A closed partial-destructor residue is one fixed HOL value.  Emit the
       whole residual as a reusable zero-arity symbol; never decompose it into
       a function whose domain is the native datatype/sequence sort. *)
    (if closed_constructor_destructor_residual tm then
       translate_closed_destructor_residual acc
       handle e as Feedback.HOL_ERR _ => raise NestedTranslation e
     else
       raise ERR "translate_term" "not a closed destructor residue")
    handle e as NestedTranslation _ => raise e
         | Feedback.HOL_ERR _ =>

    (* cvc5 parses a bag literal as a lambda, but retransmission must retain
       the Bag operation rather than send that lambda to Array consumers. *)
    (if is_parsed_bag_literal tm then translate_parsed_bag_literal acc
     else
       case regime of
         FirstOrder => raise ERR "translate_term" "not first-order"
       | HigherOrder _ => translate_lambda acc)
    handle Feedback.HOL_ERR _ =>

    (* translate the entire term (e.g., for numerals), using the dictionary of
       built-in symbols; however, only do this if 'tm' has base type *)
    (if tm_has_base_type then
      if native_sequence_symbol tm [] then native_sequence_builtin (tm, [])
      else if native_set_symbol tm [] then native_set_builtin (tm, [])
      else if native_bag_symbol tm [] then native_bag_builtin (tm, [])
      else builtin_symbol (tm, [])
    else
      raise ERR "translate_term" "not first-order")  (* handled below *)
    handle Feedback.HOL_ERR _ =>

    (* split the term into rator and rands *)
    let
      val (rator, rands) = boolSyntax.strip_comb tm
    in
      (* In an HO regime a fully ranked built-in may itself return a map.
         Translate that ranked prefix before any remaining map applications. *)
      (case native_bag_count_application rator rands of
         SOME (bag, element) =>
           let
             val (acc, (bag_decls, bag_name)) =
               translate_term regime apply_operator (acc, (bounds, bag))
             val (acc, (element_decls, element_name)) =
               translate_term regime apply_operator (acc, (bounds, element))
             val count =
               case !current_bag_backend of
                 CVC5NativeBag => sexpr "bag.count" [element_name, bag_name]
               | _ => sexpr "select" [bag_name, element_name]
           in
             (acc, (bag_decls @ element_decls, count))
           end
       | NONE =>
           if same_const rator boolSyntax.equality then
             builtin_equality (rator, rands)
           else if native_sequence_symbol rator rands orelse
              native_set_symbol rator rands orelse
              native_bag_symbol rator rands orelse
              (case regime of
                 FirstOrder => tm_has_base_type
               | HigherOrder _ =>
                   Term.is_const rator andalso
                   List.length rands = declared_const_arity rator)
           then
             if native_sequence_symbol rator rands then
               native_sequence_builtin (rator, rands)
             else if native_set_symbol rator rands then
               native_set_builtin (rator, rands)
             else if native_bag_symbol rator rands then
               native_bag_builtin (rator, rands)
             else builtin_symbol (rator, rands)
           else
             raise ERR "translate_term" "not first-order")  (* handled below *)
    handle Feedback.HOL_ERR _ =>

      translate_constructor_application acc rator rands
    handle Feedback.HOL_ERR _ =>

      translate_selector_case acc
    handle Feedback.HOL_ERR _ =>

      translate_tester_case acc
    handle Feedback.HOL_ERR _ =>

      translate_case_constant acc rator rands
    handle Feedback.HOL_ERR _ =>

      (* FO functions and the Z3 dialect are arrays.  Standard 2.7 maps have
         no store operator, so preserve HOL UPDATE with a native lambda. *)
      let
        val ((index, value), array) = combinSyntax.dest_update_comb tm
      in
        case regime of
          HigherOrder Standard27 =>
            let
              val v = Term.genvar (Term.type_of index)
              val (lambda_bounds, smtvar) = create_bound_name (bounds, v)
              val (((tydict, tmdict), typedecls), tyname) =
                ensure_type (acc, Term.type_of v)
              val old_value = Term.mk_comb (array, v)
              val (acc, (arraydecls, oldname)) =
                translate_term regime apply_operator
                  ((tydict, tmdict), (lambda_bounds, old_value))
              val (acc, (indexdecls, indexname)) =
                translate_term regime apply_operator (acc, (bounds, index))
              val (acc, (valuedecls, valuename)) =
                translate_term regime apply_operator (acc, (bounds, value))
              val body = sexpr "ite"
                [sexpr "=" [smtvar, indexname], valuename, oldname]
            in
              (acc, (typedecls @ arraydecls @ indexdecls @ valuedecls,
                "(lambda ((" ^ smtvar ^ " " ^ tyname ^ ")) " ^ body ^ ")"))
            end
        | _ =>
            let
              val (acc, (arraydecls, arrayname)) =
                translate_term regime apply_operator (acc, (bounds, array))
              val (acc, (indexdecls, indexname)) =
                translate_term regime apply_operator (acc, (bounds, index))
              val (acc, (valuedecls, valuename)) =
                translate_term regime apply_operator (acc, (bounds, value))
            in
              (acc, (arraydecls @ indexdecls @ valuedecls,
                sexpr "store" [arrayname, indexname, valuename]))
            end
      end
    handle Feedback.HOL_ERR _ =>

      let
        val (function, argument) = Term.dest_comb tm
        (* Defer curried applications with native collection arguments to the
           full-application path, which retains every declaration sort. *)
        val _ =
          if Term.is_var rator andalso List.length rands > 1 andalso
             ((!current_set_backend = CVC5NativeSet andalso
               List.exists is_marked_set_term rands) orelse
              (!current_bag_backend = CVC5NativeBag andalso
               List.exists is_marked_bag_term rands))
          then raise ERR "translate_term" "native collection application"
          else ()
        val _ = Type.dom_rng (Term.type_of function)
        val native_set_argument =
          !current_set_backend = CVC5NativeSet andalso
          is_marked_set_term argument
        val native_bag_argument =
          !current_bag_backend = CVC5NativeBag andalso
          is_marked_bag_term argument
        val native_collection_argument =
          Term.is_var function andalso
          (native_set_argument orelse native_bag_argument)
        val _ =
          if !current_bag_backend = CVC5NativeBag andalso
             is_marked_bag_term function andalso
             mem_aconv tm (!current_raw_num_terms) then
            raise NestedTranslation (ERR "translate_term"
              "native cvc5 bag.count requires an Int coercion")
          else ()
        val semantically_ranked_partial =
          Term.is_const rator andalso
          let val rank = declared_const_arity rator
          in
            List.length rands < rank andalso
            has_ranked_semantics rator
          end
        val symbol_head =
          (Term.is_const rator orelse Term.is_var rator) andalso
          (semantically_ranked_partial orelse
           not (has_semantic_function_prefix rator rands))
        val _ =
          case regime of
            HigherOrder Standard27 =>
              if symbol_head then
                raise ERR "translate_term" "symbol-headed application"
              else
                ()
          | _ =>
              if Term.is_const rator andalso
                 not (combinSyntax.is_update_comb function) then
                (case regime of
                   FirstOrder =>
                     raise ERR "translate_term"
                       "HOL constants are emitted as functions"
                 | HigherOrder _ =>
                     if List.length rands >
                          declared_const_arity rator orelse
                        has_semantic_function_prefix rator rands then
                       ()
                     else
                       raise ERR "translate_term"
                         "ranked HOL constant application")
              else
                ()
        val (acc, (functiondecls, functionname)) =
          if native_collection_argument then
            (case Redblackmap.peek (tmdict, (function, 1)) of
               SOME name => (acc, ([], name))
             | NONE =>
                 let
                   val (_, range) = Type.dom_rng (Term.type_of function)
                   val (tydict, (domdecls, domain_sort)) =
                     if native_set_argument then selected_set_sort tydict argument
                     else selected_bag_sort tydict argument
                   val (tydict, (rngdecls, range_sort)) =
                     translate_type regime (tydict, range)
                   val name = tm_prefix ^
                     Int.toString (Redblackmap.numItems tmdict)
                   val tmdict = Redblackmap.insert
                     (tmdict, (function, 1), name)
                   val declaration = term_declaration_text regime name
                     [domain_sort] range_sort
                   val _ = record_emitted_term_sorts (function, 1)
                     ([domain_sort], range_sort)
                 in
                   ((tydict, tmdict),
                    (domdecls @ rngdecls @ [declaration], name))
                 end)
          else
            translate_term regime apply_operator (acc, (bounds, function))
            handle e as Feedback.HOL_ERR _ => raise NestedTranslation e
        val (acc, (argumentdecls, argumentname)) =
          translate_term regime apply_operator (acc, (bounds, argument))
          handle e as Feedback.HOL_ERR _ => raise NestedTranslation e
      in
        (acc, (functiondecls @ argumentdecls,
          if native_collection_argument then sexpr functionname [argumentname]
          else if !current_set_backend = CVC5ArraySet andalso
                  is_marked_set_term function then
            sexpr "select" [functionname, argumentname]
          else if !current_bag_backend = CVC5ArrayBag andalso
                  is_marked_bag_term function then
            sexpr "select" [functionname, argumentname]
          else
            case !current_set_backend of
              CVC5NativeSet =>
                if is_marked_set_term function then
                  sexpr "set.member" [argumentname, functionname]
                else if !current_bag_backend = CVC5NativeBag andalso
                        is_marked_bag_term function then
                  sexpr "bag.count" [argumentname, functionname]
                else explicit_apply functionname argumentname
            | _ =>
                if !current_bag_backend = CVC5NativeBag andalso
                   is_marked_bag_term function then
                  sexpr "bag.count" [argumentname, functionname]
                else explicit_apply functionname argumentname))
      end
    handle Feedback.HOL_ERR _ =>

      let
        val rands_count = List.length rands
        val _ =
          if Term.is_const rator orelse Term.is_var rator then ()
          else
            raise ERR "translate_term"
              ("unsupported higher-order rator expression: " ^
               Hol_pp.term_to_string rator)
        val declaration_arity =
          case regime of
            FirstOrder => rands_count
          | HigherOrder _ =>
              if Term.is_const rator then declared_const_arity rator else 0
      in
        if declaration_arity > rands_count andalso
           (regime = HigherOrder Z3LambdaArray orelse
            regime = HigherOrder Standard27 andalso
              has_ranked_semantics rator) then
          eta_expand_ranked_constant acc tm rator declaration_arity
            rands_count
        else
          let
            (* All preceding rungs preserve official SMT operators,
               constructors, carrier injections, and ranked eta expansion.
               Only the generic invented-symbol boundary is closed here. *)
            val _ = reject_unsupported_smtfloat_constant rator
            val (acc, (decls, name)) =
              (* A function-valued binder is a symbol head too. *)
              (acc, ([], Redblackmap.find (bounds, rator)))
              handle Redblackmap.NotFound =>
              (* translate the rator as a previously defined symbol *)
              (acc, ([], Redblackmap.find
                (tmdict, (rator, declaration_arity))))
              handle Redblackmap.NotFound =>

              (* translate the rator as a new (i.e., uninterpreted) symbol *)
              let
                (* translate 'rator' types required for the rator's
                   SMT-LIB declaration *)
                fun doms_rng acc 0 ty =
                  (List.rev acc, ty)
                  | doms_rng acc n ty =
                  let
                    val (dom, rng) = Type.dom_rng ty
                  in
                    doms_rng (dom :: acc) (n - 1) rng
                  end
                (* In the HO regime constants use their declared rank, not
                   their occurrence arity.  This canonical key prevents
                   partial and full applications from splitting one symbol. *)
                val (domtys, rngty) = doms_rng [] declaration_arity
                  (Term.type_of rator)
                (* A native collection argument determines the corresponding
                   declaration position.  Translating its HOL function type
                   alone would otherwise erase the selected Set/Bag sort. *)
                fun translate_domain (tydict, (index, ty)) =
                  let
                    val argument =
                      if index < List.length rands then
                        SOME (List.nth (rands, index))
                      else contextual_collection_argument rator index
                  in
                    case argument of
                      SOME arg =>
                        if is_marked_set_term arg then
                          selected_set_sort tydict arg
                        else if is_marked_bag_term arg then
                          selected_bag_sort tydict arg
                        else
                          translate_type regime (tydict, ty)
                    | NONE => translate_type regime (tydict, ty)
                  end
                val (tydict, domdecltys) =
                  Lib.foldl_map translate_domain (tydict,
                    ListPair.zip (List.tabulate (List.length domtys, Lib.I),
                      domtys))
                val _ = reject_invented_native_datatype_domain rator domtys
                val (domdeclss, domtys) = Lib.split domdecltys
                val domdecls = List.concat domdeclss
                fun translate_variable_function_type (tydict, index, ty) =
                  if Type.compare (ty, Term.type_of tm) = EQUAL andalso
                     is_marked_set_term tm then
                    selected_set_sort tydict tm
                  else if Type.compare (ty, Term.type_of tm) = EQUAL andalso
                          is_marked_bag_term tm then
                    selected_bag_sort tydict tm
                  else
                    case Lib.total Type.dom_rng ty of
                      SOME (domain, range) =>
                        let
                          val (tydict, (ddecls, dsort)) =
                            translate_domain (tydict, (index, domain))
                          val (tydict, (rdecls, rsort)) =
                            translate_variable_function_type
                              (tydict, index + 1, range)
                        in
                          (tydict, (ddecls @ rdecls,
                            "(-> " ^ dsort ^ " " ^ rsort ^ ")"))
                        end
                    | NONE => translate_type regime (tydict, ty)
                val (tydict, (rngdecls, rngty)) =
                  if declaration_arity = 0 andalso
                     (case regime of
                        HigherOrder Standard27 =>
                          Term.is_var rator andalso
                          (is_marked_set_term tm orelse
                           is_marked_bag_term tm orelse
                           has_contextual_collection_argument rator orelse
                           List.exists (fn argument =>
                             is_marked_set_term argument orelse
                             is_marked_bag_term argument) rands)
                      | _ => false) then
                    translate_variable_function_type
                      (tydict, 0, Term.type_of rator)
                  else if is_marked_set_term tm then
                    selected_set_sort tydict tm
                  else if is_marked_bag_term tm then
                    selected_bag_sort tydict tm
                  else
                    translate_type regime (tydict, rngty)
                (* invent new name for 'rator' *)
                val name = tm_prefix ^
                  Int.toString (Redblackmap.numItems tmdict)
                val _ = if !Library.trace > 0 andalso Term.is_const rator then
                  WARNING "translate_term"
                    ("uninterpreted constant " ^ Hol_pp.term_to_string rator)
                  else
                    ();
                val _ = if !Library.trace > 2 then
                    Feedback.HOL_MESG
                      ("HolSmtLib (SmtLib): inventing name '" ^ name ^
                       "' for HOL term '" ^ Hol_pp.term_to_string rator ^
                       "' (declared at rank " ^
                       Int.toString declaration_arity ^ ")")
                  else
                    ()
                val tmdict = Redblackmap.insert
                  (tmdict, (rator, declaration_arity), name)
                val decl =
                  term_declaration_text regime name domtys rngty
                val _ = record_emitted_term_sorts
                  (rator, declaration_arity) (domtys, rngty)
              in
                ((tydict, tmdict),
                 (domdecls @ rngdecls @ [decl], name))
              end
            (* translate 'rands' *)
            val (acc, declnames) = Lib.foldl_map
              (fn (a, t) =>
                translate_term regime apply_operator (a, (bounds, t)))
              (acc, rands)
            val (declss, names) = Lib.split declnames
          in
            (acc, (decls @ List.concat declss,
              case regime of
                HigherOrder Standard27 =>
                  if Term.is_var rator andalso
                     (is_marked_set_term tm orelse
                      is_marked_bag_term tm orelse
                      List.exists (fn argument =>
                        is_marked_set_term argument orelse
                        is_marked_bag_term argument) rands) andalso
                     not (Option.isSome
                       (Redblackmap.peek (bounds, rator))) then
                    List.foldl (fn (argument, function) =>
                      explicit_apply function argument) name names
                  else sexpr name names
              | _ => sexpr name names))
          end
      end
    end
  end

  datatype datatype_case_scan =
      NotDatatypeCase
    | DatatypeCase of string option

  fun first_reason scan [] = NONE
    | first_reason scan (tm :: tms) =
      (case scan tm of
         SOME reason => SOME reason
       | NONE => first_reason scan tms)

  (* Report higher-order shapes that the first-order translator rejects or
     would encode without preserving a built-in's semantics.  Binder, let,
     datatype-case, and update abstractions are encoding scaffolding rather
     than first-class function values. *)
  fun goal_ho_reason (assumptions, conclusion) =
    let
      fun is_function_valued_conditional tm =
        let
          val (rator, rands) = boolSyntax.strip_comb tm
          val conditional =
            case rands of
              test :: then_tm :: else_tm :: _ =>
                Term.list_mk_comb (rator, [test, then_tm, else_tm])
            | _ => raise ERR "goal_ho_reason" "partial conditional"
        in
          Term.same_const rator boolSyntax.conditional andalso
          is_function_type (Term.type_of conditional)
        end
        handle Feedback.HOL_ERR _ => false
      fun datatype_case_reason scan inherited tm =
        let
          val (_, elem, clauses) = TypeBase.dest_case tm
          fun clause_reason (pattern, rhs) =
            let
              val (_, pattern_args) = boolSyntax.strip_comb pattern
              val selector_vars = List.filter
                (is_function_type o Term.type_of) pattern_args
            in
              scan (selector_vars @ inherited) rhs
            end
        in
          DatatypeCase
            (case scan inherited elem of
               SOME reason => SOME reason
             | NONE => Lib.get_first clause_reason clauses)
        end
        handle Feedback.HOL_ERR _ => NotDatatypeCase
      fun record_update_operands tm =
        let
          val (update_f, record) = Term.dest_comb tm
          val (update, updater) = Term.dest_comb update_f
          val new_value =
            combinSyntax.dest_K_1 updater
            handle Feedback.HOL_ERR _ =>
              let
                val (var1, body) = Term.dest_abs updater
                val (k_tm, var2) = Term.dest_comb body
                val _ = if Term.aconv var1 var2 then ()
                        else raise ERR "goal_ho_reason" "not record update"
              in
                combinSyntax.dest_K_1 k_tm
              end
          val record_ty = Term.type_of record
          val value_ty = Term.type_of new_value
          val fields = TypeBase.fields_of record_ty
          val _ =
            case List.find
              (fn (_, {ty = field_ty, fupd, ...} :
                       TypeBasePure.rcd_fieldinfo) =>
                Term.same_const update fupd andalso
                Lib.can (Type.match_type field_ty) value_ty) fields of
              SOME _ => ()
            | NONE => raise ERR "goal_ho_reason" "not record update"
        in
          SOME [record, new_value]
        end
        handle Feedback.HOL_ERR _ => NONE
      fun is_seq_ho_combinator tm =
        case Lib.total boolSyntax.strip_comb tm of
          SOME (rator, _) =>
            same_const rator seq_map_tm orelse same_const rator seq_foldl_tm
        | NONE => false
      fun partial_ranked_builtin rator rands =
        Term.is_const rator andalso
        let
          val {Thy, Name, ...} = Term.dest_thy_const rator
        in
          List.length rands < declared_const_arity rator andalso
          Redblackset.member (builtin_const_names, (Thy, Name))
        end
      fun scan inherited tm =
        if is_seq_ho_combinator tm then
          SOME "automatic:seq-ho-combinator"
        else if boolSyntax.is_forall tm then
          scan inherited (Lib.snd (boolSyntax.dest_forall tm))
        else if boolSyntax.is_exists tm then
          scan inherited (Lib.snd (boolSyntax.dest_exists tm))
        else
          case Lib.total pairSyntax.dest_anylet tm of
            SOME (bindings, body) =>
              first_reason (scan inherited)
                (List.map Lib.snd bindings @ [body])
          | NONE =>
            if is_function_valued_conditional tm then
              (* The FO datatype-case path treats a function-valued
                 conditional as abstraction scaffolding, then emits its
                 branches without preserving ite semantics.  Select HO before
                 datatype-case normalization so the native function-valued
                 result is retained. *)
              SOME "automatic:function-valued-conditional"
            else
              (case datatype_case_reason scan inherited tm of
                 DatatypeCase reason => reason
               | NotDatatypeCase =>
                 (case Lib.total combinSyntax.dest_update_comb tm of
                  SOME ((index, value), array) =>
                    first_reason (scan inherited) [array, index, value]
                | NONE =>
                  (case record_update_operands tm of
                     SOME operands =>
                       first_reason (scan inherited) operands
                   | NONE =>
                     if Term.is_abs tm then
                       SOME "automatic:surviving-abstraction"
                     else
                       case Lib.total boolSyntax.strip_comb tm of
                         SOME (rator, rands) =>
                           if List.exists (Term.aconv rator) inherited then
                             SOME
                               "automatic:non-constant/non-variable-rator"
                           else if partial_ranked_builtin rator rands then
                             SOME "automatic:partial-ranked-builtin"
                           else if Term.is_const rator orelse
                                   Term.is_var rator then
                             first_reason (scan inherited) rands
                           else
                             SOME
                               "automatic:non-constant/non-variable-rator"
                       | NONE => NONE)))
    in
      first_reason (scan []) (assumptions @ [conclusion])
    end

  fun goal_requires_ho_aux goal = Option.isSome (goal_ho_reason goal)

  datatype regime_request =
      AutomaticRegime of ho_dialect
    | RegimeOverride of regime

  fun select_regime request goal =
    case request of
      RegimeOverride regime => (regime, "explicit override")
    | AutomaticRegime dialect =>
        (case goal_ho_reason goal of
           NONE => (FirstOrder, "automatic:no-ho-trigger")
         | SOME reason => (HigherOrder dialect, reason))

  (* Returns the selected translation and SMT-LIB text for the input goal;
     the conclusion is negated before emission.  A term-dictionary integer is
     the occurrence arity in FirstOrder.  HigherOrder uses a constant's
     declared rank, or zero for a function-valued variable, so partial and
     full applications share one symbol. *)
  fun goal_to_SmtLib_aux_inner request apply_operator
      (policy : logic_selection_policy) target emit_sequences
      (goal as (original_ts, t)) : translation * string list =
  let
    val _ = current_native_sequence_emission := emit_sequences
    val _ = current_generated_forall_emissions := 0
    val _ = emitted_term_sorts := []
    val set_terms = List.foldl (fn (term, acc) =>
      collect_native_set_terms term acc) [] (t :: original_ts)
    val bag_terms = List.foldl (fn (term, acc) =>
      collect_native_bag_terms term acc) [] (t :: original_ts)
    (* Num is an Int-valued SMT abs only beneath its integer coercion.  In an
       opaque HOL-num position it must remain an uninterpreted function. *)
    fun raw_num_terms term =
      let
        fun insert tm terms =
          if mem_aconv tm terms then terms else tm :: terms
        fun visit expected tm acc =
          if Term.is_abs tm then
            let
              val (_, body) = Term.dest_abs tm
              val (_, range) = Type.dom_rng (Term.type_of tm)
              val expected_body =
                if mem_aconv tm bag_terms then NONE else SOME range
            in
              visit expected_body body acc
            end
          else if Term.is_comb tm then
            let
              val (rator, rand) = Term.dest_comb tm
              val domain = Lib.fst (Type.dom_rng (Term.type_of rator))
              val expected_arg =
                if same_const rator intSyntax.int_injection orelse
                   same_const rator int_of_num_tm then NONE else SOME domain
              val acc = visit NONE rator acc
              val acc = visit expected_arg rand acc
            in
              if (same_const rator intSyntax.Num_tm orelse
                  same_const rator bagSyntax.BAG_CARD_tm orelse
                  (case boolSyntax.strip_comb tm of
                     (bag, [_]) => mem_aconv bag bag_terms
                   | _ => false)) andalso
                 Option.isSome expected andalso
                 Type.compare (Option.valOf expected, numSyntax.num) = EQUAL
              then insert tm acc else acc
            end
          else acc
      in
        visit NONE term []
      end
    val raw_num_terms = List.foldl (fn (term, acc) =>
      List.foldl (fn (num_tm, nums) =>
        if mem_aconv num_tm nums then nums else num_tm :: nums)
        acc (raw_num_terms term)) [] (t :: original_ts)
    (* A symbol has one fixed SMT domain sort.  A collection argument is
       ambiguous only if that same function position is also used as an
       ordinary array argument. *)
    val subterms = List.concat (List.map Library.subterms (t :: original_ts))
    fun ordinary_symbol_application function =
      let val (head, applied) = boolSyntax.strip_comb function in
        Term.is_var head orelse
        (Term.is_const head andalso
         List.length applied < declared_const_arity head)
      end
    fun collection_parameter_index function argument variable =
      let
        val residual_type = Term.type_of function
        val argument_type = Term.type_of argument
        fun find index ty =
          if Type.compare (ty, residual_type) = EQUAL then
            case Lib.total Type.dom_rng ty of
              SOME (domain, _) =>
                if Type.compare (domain, argument_type) = EQUAL then
                  SOME index
                else
                  NONE
            | NONE => NONE
          else
            case Lib.total Type.dom_rng ty of
              SOME (_, range) => find (index + 1) range
            | NONE => NONE
      in
        find 0 (Term.type_of variable)
      end
    (* The (variable, parameter index, argument) triples by which [tm]
       applies a computed function to a native collection. *)
    fun computed_collection_pairs collection_terms tm =
      case Lib.total Term.dest_comb tm of
        SOME (function, argument) =>
          if mem_aconv argument collection_terms andalso
             not (ordinary_symbol_application function) then
            List.mapPartial (fn variable =>
              Option.map (fn index => (variable, index, argument))
                (collection_parameter_index function argument variable))
              (Term.free_vars function)
          else []
      | NONE => []
    fun computed_collection_applications collection_terms =
      if List.null collection_terms then []
      else List.concat
        (List.map (computed_collection_pairs collection_terms) subterms)
    val computed_set_applications =
      computed_collection_applications set_terms
    val computed_bag_applications =
      computed_collection_applications bag_terms
    fun has_mixed_collection_argument collection_terms =
      let
        fun positions function [] _ = []
          | positions function (argument :: arguments) index =
              (function, index, argument) ::
              positions function arguments (index + 1)
        fun application_positions subterm =
          let val (function, arguments) = boolSyntax.strip_comb subterm in
            if Term.is_var function orelse Term.is_const function then
              positions function arguments 0
            else []
          end
        val applications = List.concat (List.map application_positions subterms)
      in
        List.exists (fn (function, index, argument) =>
          mem_aconv argument collection_terms andalso
          List.exists (fn (other_function, other_index, other_argument) =>
            Term.aconv function other_function andalso index = other_index andalso
            not (mem_aconv other_argument collection_terms)) applications)
          applications
      end
    (* A bound predicate/count function applied to a native collection needs a
       collection domain in its binder declaration.  Bound-variable names are
       not globally unique, so the term dictionary cannot safely give it that
       declaration.  Use the array representation for this scoped shape. *)
    fun bound_collection_application collection_terms =
      let
        fun visit bound tm =
          if Term.is_abs tm then
            let val (var, body) = Term.dest_abs tm in visit (var :: bound) body end
          else
            let
              val (function, arguments) = boolSyntax.strip_comb tm
              val applies_bound =
                List.exists (fn var => Term.aconv function var) bound
              val has_collection_argument =
                List.exists (fn argument => mem_aconv argument collection_terms)
                  arguments
              fun computed_applies_bound () =
                List.exists (fn (variable, _, _) => mem_aconv variable bound)
                  (computed_collection_pairs collection_terms tm)
            in
              (applies_bound andalso has_collection_argument) orelse
              computed_applies_bound () orelse
              List.exists (visit bound) arguments
            end
      in
        List.exists (visit []) (t :: original_ts)
      end
    val _ =
      case target of
        SOME {solver = "cvc5", ...} =>
          if bound_collection_application set_terms orelse
             bound_collection_application bag_terms then
            raise ERR "goal_to_SmtLib_aux_inner"
              "higher-order cvc5 functions over Sets or Bags are unsupported"
          else ()
      | _ => ()
    val initial_backend = backend_for_target target goal set_terms
    val initial_bag_backend =
      bag_backend_for_target target goal bag_terms
    val (backend, bag_backend) =
      case target of
        SOME {solver = "cvc5", ...} =>
          if collection_nested_in_collection set_terms bag_terms then
            (CVC5ArraySet, CVC5ArrayBag)
          else
            (if not (List.null computed_set_applications) then
               CVC5ArraySet
             else initial_backend,
             if not (List.null computed_bag_applications) then
               CVC5ArrayBag
             else initial_bag_backend)
      | _ => (initial_backend, initial_bag_backend)
    val _ =
      case target of
        SOME {solver = "cvc5", ...} =>
          if (backend <> CVC5ArraySet andalso
              has_mixed_collection_argument set_terms) orelse
             (bag_backend = CVC5NativeBag andalso
              has_mixed_collection_argument bag_terms) then
            raise ERR "goal_to_SmtLib_aux_inner"
              "native collection passed to an ambiguously typed HOL function"
          else ()
      | _ => ()
    val _ =
      case target of
        SOME {solver = "cvc5", ...} =>
          if backend = CVC5ArraySet andalso
             List.exists contains_set_card (t :: original_ts) then
            raise ERR "goal_to_SmtLib_aux_inner"
              "set.card requires a finiteness-entailing cvc5 goal"
          else if bag_backend = CVC5ArrayBag andalso
             List.exists contains_bag_card (t :: original_ts) then
            raise ERR "goal_to_SmtLib_aux_inner"
              "bag.card requires a finiteness-entailing cvc5 goal"
          else ()
      | _ => ()
    val _ = current_set_backend := backend
    val _ = current_set_terms := set_terms
    val _ = current_raw_num_terms := raw_num_terms
    val _ = current_bag_backend := bag_backend
    val _ = current_bag_terms := bag_terms
    val _ = current_collection_function_arguments :=
      computed_set_applications @ computed_bag_applications
    val _ = current_bag_helpers := []
    (* FINITE hypotheses are the evidence selecting cvc5's finite Set/Bag
       models; once selected they are semantic facts of those models and must
       not be serialized as unsupported HOL predicates. *)
    val finite_sets = List.mapPartial finite_set_hypothesis original_ts
    val finite_bags = List.mapPartial finite_bag_hypothesis original_ts
    (* In cvc5's native finite collection models, finiteness evidence is a
       semantic fact, including beneath Boolean connectives. *)
    fun replace_finite tm =
      case finite_set_hypothesis tm of
        SOME set =>
          if backend = CVC5NativeSet andalso finite_set_term finite_sets set
          then boolSyntax.T else descend tm
      | NONE =>
          (case finite_bag_hypothesis tm of
             SOME bag =>
               if bag_backend = CVC5NativeBag andalso
                  finite_bag_term finite_bags bag then boolSyntax.T
               else descend tm
           | NONE => descend tm)
    and descend tm =
      if Term.is_comb tm then
        let val (rator, rand) = Term.dest_comb tm
        in Term.mk_comb (replace_finite rator, replace_finite rand) end
      else if Term.is_abs tm then
        let val (var, body) = Term.dest_abs tm
        in Term.mk_abs (var, replace_finite body) end
      else tm
    val ts = List.map replace_finite (List.filter (fn tm =>
      not (backend = CVC5NativeSet andalso
           Option.isSome (finite_set_hypothesis tm)) andalso
      not (bag_backend = CVC5NativeBag andalso
           Option.isSome (finite_bag_hypothesis tm))) original_ts)
    val t = replace_finite t
    val (regime, regime_reason) = select_regime request (ts, t)
    val tydict = Redblackmap.mkDict Type.compare
    val tmdict = Redblackmap.mkDict
      (Lib.pair_compare (Term.compare, Int.compare))
    val bounds = Redblackmap.mkDict Term.compare
    val terms = ts @ [boolSyntax.mk_neg t]
    val _ = reject_uninterpreted_native_destructors terms
    val (acc, smtlibs) = Lib.foldl_map
      (fn (acc, tm) =>
        translate_term regime apply_operator (acc, (bounds, tm)))
      ((tydict, tmdict), terms)
      handle NestedTranslation e => raise e
    val (tydict, tmdict) = acc
    val features =
      infer_features regime terms tydict tmdict
    val (feature_logic, feature_reason) =
      infer_logic_from_features_for_regime regime features
    (* Z3's array-lambda extension is accepted uniformly under ALL, while
       narrower FO array logics reject lambda as quantified syntax on some
       supported Z3 versions.  The C1 replay corpus also uses ALL, so keeping
       that logic in the translation record gives proof parsing the same broad
       dictionaries as the solver.  Caller overrides still take precedence. *)
    val (inferred_logic, reason) =
      case regime of
        HigherOrder Z3LambdaArray =>
          ("ALL", "Z3 array-lambda lowering requires logic ALL; " ^
            feature_reason)
      | _ => (feature_logic, feature_reason)
    val (selected_logic, reason) =
      case policy {features = features, inferred_logic = inferred_logic,
                   reason = reason} of
        NONE => (inferred_logic, reason)
      | SOME {logic, reason} => (logic, reason)
    (* Metadata is public lazily, so retain the query's collection state for
       its eventual construction instead of consulting the restored ambient
       state. *)
    val record_sequence_emission = !current_native_sequence_emission
    val record_generated_forall_emissions =
      !current_generated_forall_emissions
    val record_set_backend = !current_set_backend
    val record_bag_backend = !current_bag_backend
    val record_emitted_term_sorts = !emitted_term_sorts
    fun records () =
      let
        val restorers = [
          save_cell current_native_sequence_emission,
          save_cell current_generated_forall_emissions,
          save_cell current_set_backend,
          save_cell current_bag_backend,
          save_cell emitted_term_sorts
        ]
        fun work () =
          (current_native_sequence_emission := record_sequence_emission;
           current_generated_forall_emissions :=
             record_generated_forall_emissions;
           current_set_backend := record_set_backend;
           current_bag_backend := record_bag_backend;
           emitted_term_sorts := record_emitted_term_sorts;
           build_translation_records regime regime_reason terms
             selected_logic reason features tydict tmdict)
        fun restore () = restore_cells restorers
      in
        Portable.finally restore work ()
      end
    val translation = {logic = selected_logic, regime = regime,
      tydict = tydict, tmdict = tmdict, records = records}
    (* we choose to intertwine declarations and assertions (for no
       particular reason; an alternative would be to emit all
       declarations before all assertions) *)
    val smtlibs = List.foldl
      (fn ((xs, s), acc) => acc @ xs @ ["(assert " ^ s ^ ")\n"]) [] smtlibs
  in
    (* A `(set-logic ...)` is always emitted, including on the implicit
       (no caller override) Z3/CVC path.  Older revisions emitted none for
       `NONE`, letting the solver default to accept-anything; relying on
       that default is fragile.  Emitting unconditionally is safe because
       `infer_logic_from_features` is a sound over-approximation of the
       goal's theory needs: every theory Phase 1 can translate contributes
       a feature, any multiplication is treated as nonlinear, and any
       un-modelled feature combination falls back to `ALL`.  So the
       declared fragment never excludes a term the goal actually contains
       (a too-narrow fragment would make the solver reject a goal it could
       otherwise prove), and the emitted name is always a recognised logic
       (see `infer_logic_from_features` and `parsedicts_of_logic`).  Any
       future widening of what Phase >1 can translate must preserve this
       invariant — add the feature and its logic mapping together, or keep
       the `ALL` fallback. *)
    (translation, ["(set-logic " ^ selected_logic ^ ")\n"] @ [
      "(set-info :source |Automatically generated from HOL4 by SmtLib.goal_to_SmtLib.\n",
      "Copyright (c) 2011 Tjark Weber. All rights reserved.|)\n",
      "(set-info :smt-lib-version 2.7)\n"
    ] @ smtlibs @ [
      "(check-sat)\n"
    ])
  end

  fun goal_to_SmtLib_aux request apply_operator policy target
      emit_sequences goal =
  let
    val restorers = [
      save_cell current_native_sequence_emission,
      save_cell current_generated_forall_emissions,
      save_cell emitted_term_sorts,
      save_cell current_set_backend,
      save_cell current_set_terms,
      save_cell current_raw_num_terms,
      save_cell current_bag_backend,
      save_cell current_bag_terms,
      save_cell current_bag_helpers,
      save_cell current_collection_function_arguments
    ]
    fun work () =
      goal_to_SmtLib_aux_inner request apply_operator policy target
        (emit_sequences andalso native_sequence_goal goal) goal
    fun restore () = restore_cells restorers
  in
    Portable.finally restore work ()
  end

  fun num_binder_to_int_once_conv tm =
  let
    fun is_num_var v = Type.compare (Term.type_of v, numSyntax.num) = EQUAL
    fun is_bag_var v =
      case Lib.total Type.dom_rng (Term.type_of v) of
        SOME (_, rng) => Type.compare (rng, numSyntax.num) = EQUAL
      | NONE => false
    val is_num_forall =
      boolSyntax.is_forall tm andalso
      is_num_var (Lib.fst (boolSyntax.dest_forall tm))
    val is_num_exists =
      boolSyntax.is_exists tm andalso
      is_num_var (Lib.fst (boolSyntax.dest_exists tm))
    val is_bag_forall =
      boolSyntax.is_forall tm andalso
      is_bag_var (Lib.fst (boolSyntax.dest_forall tm))
    val is_bag_exists =
      boolSyntax.is_exists tm andalso
      is_bag_var (Lib.fst (boolSyntax.dest_exists tm))
  in
    if is_num_forall then
      Conv.HO_REWR_CONV HolSmtTheory.NUM_FORALL_TO_INT tm
    else if is_num_exists then
      Conv.HO_REWR_CONV HolSmtTheory.NUM_EXISTS_TO_INT tm
    else if is_bag_forall then
      Conv.HO_REWR_CONV HolSmtTheory.BAG_FORALL_TO_INT tm
    else if is_bag_exists then
      Conv.HO_REWR_CONV HolSmtTheory.BAG_EXISTS_TO_INT tm
    else
      Conv.NO_CONV tm
  end

  fun NUM_BINDERS_TO_INT_CONV tm =
    (* TOP_DEPTH_CONV uses SUB_CONV/ABS_CONV, so surviving first-class
       abstractions are traversed as well as quantifier binders. *)
    Conv.THENC
      (Conv.TOP_DEPTH_CONV num_binder_to_int_once_conv,
       Conv.TOP_DEPTH_CONV Thm.BETA_CONV) tm
    handle Conv.UNCHANGED => Thm.REFL tm

  val exp_one_rewrites =
  let
    val th = Drule.SPEC_ALL arithmeticTheory.EXP_1
  in
    List.map Drule.GEN_ALL [Thm.CONJUNCT1 th, Thm.CONJUNCT2 th]
  end

  val INT_EXP_1 =
  let
    val i = Term.mk_var ("i", intSyntax.int_ty)
    val th =
      Thm.SPEC numSyntax.zero_tm
        (Thm.SPEC i (Thm.CONJUNCT2 integerTheory.int_exp))
  in
    Drule.GEN_ALL
      (simpLib.SIMP_RULE pureSimps.pure_ss
        [Thm.CONJUNCT1 integerTheory.int_exp, integerTheory.INT_MUL_RID,
         Conv.GSYM arithmeticTheory.ONE]
        th)
  end

  val INT_EXP_BASE_1 =
  let
    val n = Term.mk_var ("n", numSyntax.num)
    val one = numSyntax.mk_numeral Arbnum.one
    val th = Thm.SPEC n (Thm.SPEC one integerTheory.INT_EXP)
  in
    Drule.GEN_ALL
      (simpLib.SIMP_RULE pureSimps.pure_ss
        [List.hd exp_one_rewrites, integerTheory.INT] th)
  end

  val INT_EXP_2 =
  let
    val i = Term.mk_var ("i", intSyntax.int_ty)
    val one = numSyntax.mk_numeral Arbnum.one
    val th =
      Thm.SPEC one (Thm.SPEC i (Thm.CONJUNCT2 integerTheory.int_exp))
  in
    Drule.GEN_ALL
      (simpLib.SIMP_RULE pureSimps.pure_ss
         [INT_EXP_1, Conv.GSYM arithmeticTheory.TWO] th)
  end

  val INT_EXP_3 =
  let
    val i = Term.mk_var ("i", intSyntax.int_ty)
    val two = numSyntax.mk_numeral (Arbnum.fromInt 2)
    val th =
      numLib.REDUCE_RULE
        (Thm.SPEC two (Thm.SPEC i (Thm.CONJUNCT2 integerTheory.int_exp)))
  in
    Drule.GEN_ALL
      (simpLib.SIMP_RULE pureSimps.pure_ss
        [INT_EXP_2, integerTheory.INT_MUL_ASSOC] th)
  end

  val REAL_POW_3 =
  let
    val x = Term.mk_var ("x", realSyntax.real_ty)
    val two = numSyntax.mk_numeral (Arbnum.fromInt 2)
    val th =
      numLib.REDUCE_RULE
        (Thm.SPEC two (Thm.SPEC x (Thm.CONJUNCT2 realTheory.pow)))
  in
    Drule.GEN_ALL
      (simpLib.SIMP_RULE pureSimps.pure_ss
        [realTheory.POW_2, realTheory.REAL_MUL_ASSOC] th)
  end

  (* Unfold a real power with an arbitrary numeral exponent.  The recursive
     equations only syntactically match zero/SUC, whereas HOL numerals are
     binary terms; specialize the step equation to the predecessor and reduce
     that numeral before descending into the remaining power. *)
  fun REAL_POW_NUMERAL_CONV tm =
  let
    val (rator, args) = boolSyntax.strip_comb tm
    val _ =
      if Term.same_const rator realSyntax.exp_tm then ()
      else raise Conv.UNCHANGED
    val (x, n) = Lib.pair_of_list args
    val n = numSyntax.dest_numeral n
    val th =
      if n = Arbnum.zero then
        Thm.SPEC x (Thm.CONJUNCT1 realTheory.pow)
      else
        numLib.REDUCE_RULE
          (Thm.SPEC (numSyntax.mk_numeral (Arbnum.- (n, Arbnum.one)))
            (Thm.SPEC x (Thm.CONJUNCT2 realTheory.pow)))
    val rhs = boolSyntax.rhs (Thm.concl th)
    val rhs_th = Conv.DEPTH_CONV REAL_POW_NUMERAL_CONV rhs
      handle Conv.UNCHANGED => Thm.REFL rhs
  in
    Thm.TRANS th rhs_th
  end

  (* Discharge a positive real power with a concrete base before its symbolic
     nat exponent reaches the serializer.  This uses the general REAL_POW_LT
     theorem; only its closed arithmetic side-goal is evaluated here. *)
  fun REAL_POW_POS_LITERAL_CONV tm =
  let
    val (rel, args) = boolSyntax.strip_comb tm
    val _ =
      if Term.same_const rel realSyntax.less_tm then ()
      else raise Conv.UNCHANGED
    val (zero, pow_tm) = Lib.pair_of_list args
    val (pow_const, pow_args) = boolSyntax.strip_comb pow_tm
    val _ =
      if Term.same_const pow_const realSyntax.exp_tm then ()
      else raise Conv.UNCHANGED
    val (base, exponent) = Lib.pair_of_list pow_args
    val positive =
      Tactical.TAC_PROOF
        (([], realSyntax.mk_less (zero, base)),
         Tactical.THEN
           (simpLib.SIMP_TAC pureSimps.pure_ss
             [Conv.GSYM intrealTheory.real_of_int_num,
              intrealTheory.real_of_int_lt],
            intLib.ARITH_TAC))
    val pow_positive =
      Thm.MP
        (Thm.SPEC exponent (Thm.SPEC base realTheory.REAL_POW_LT)) positive
    val _ =
      if Term.aconv (Thm.concl pow_positive) tm then ()
      else raise Conv.UNCHANGED
  in
    Drule.EQT_INTRO pow_positive
  end
  handle Feedback.HOL_ERR _ => raise Conv.UNCHANGED

  fun thm_rhs_is_true th =
  let
    val (_, rhs) = boolSyntax.dest_eq (Thm.concl th)
  in
    Term.aconv rhs boolSyntax.T
  end

  fun INT_DIVIDES_LITERAL_MOD_CONV tm =
  let
    val (divisor, _) = intSyntax.dest_divides tm
    val zero = intSyntax.term_of_int Arbint.zero
    val _ =
      if intSyntax.is_int_literal divisor then ()
      else raise ERR "INT_DIVIDES_LITERAL_MOD_CONV" "non-literal divisor"
    val pos_th =
      simpLib.SIMP_CONV intLib.int_ss []
        (intSyntax.mk_less (zero, divisor))
    val _ =
      if thm_rhs_is_true pos_th then ()
      else raise ERR "INT_DIVIDES_LITERAL_MOD_CONV" "non-positive divisor"
    val nz_th =
      simpLib.SIMP_CONV intLib.int_ss []
        (boolSyntax.mk_neg (boolSyntax.mk_eq (divisor, zero)))
    val z_th =
      simpLib.SIMP_CONV intLib.int_ss []
        (boolSyntax.mk_eq (divisor, zero))
  in
    Conv.THENC
      (Conv.REWR_CONV integerTheory.INT_DIVIDES_MOD0,
       simpLib.SIMP_CONV pureSimps.pure_ss [
         pos_th, nz_th, z_th, integerTheory.INT_MOD_EMOD,
         boolTheory.COND_CLAUSES, boolTheory.AND_CLAUSES,
         boolTheory.OR_CLAUSES
       ]) tm
  end

  val num_transfer_rewrites = [
    HolSmtTheory.int_num_floor_total,
    HolSmtTheory.int_num_ceiling_total,
    HolSmtTheory.num_floor_to_int_eq,
    HolSmtTheory.num_ceiling_to_int_eq,
    HolSmtTheory.num_floor_nonpos,
    HolSmtTheory.num_sub_assoc,
    integerTheory.NUM_OF_INT,
    integerTheory.Num_EQ_ABS,
    integerTheory.INT_ABS,
    (* Prefer the guarded cancellation when a transferred natural has its
       standard non-negativity hypothesis; Num_EQ_ABS remains the total
       fallback for genuinely unguarded integer-to-natural conversions. *)
    HolSmtTheory.NUM_TO_INT_GUARDED,
    intrealTheory.INT_NUM_FLOOR,
    intrealTheory.INT_NUM_CEILING,
    realTheory.NUM_CEILING_BASE,
    (* Eliminate symbolic natural exponents whenever their real base makes
       the result independent of the exponent or establishes its sign. *)
    realTheory.POW_ONE,
    realTheory.REAL_POW_LT,
    (* These definitions can be introduced by ADD_THEOREMS_TAC after the
       first transfer pass.  Keep the final pass in the SMT-LIB fragment
       rather than serializing their quantified HOL definitions. *)
    integerTheory.INT_MAX,
    integerTheory.INT_MIN,
    HolSmtTheory.real_div_smt_rdiv,
    integerTheory.INT_POS,
    Conv.GSYM integerTheory.INT_INJ,
    Conv.GSYM integerTheory.INT_LE,
    Conv.GSYM integerTheory.INT_LT,
    Conv.GSYM integerTheory.INT_ADD,
    Conv.GSYM integerTheory.INT_MUL
  ] @ exp_one_rewrites @
    (* These equations only match syntactic numerals.  Keeping both base and
       step equations lets SIMP unfold every literal exponent, rather than
       the historical 1/2/3 subset, while leaving symbolic exponents alone. *)
    [Thm.CONJUNCT1 arithmeticTheory.EXP,
     Thm.CONJUNCT2 arithmeticTheory.EXP,
     Thm.CONJUNCT1 integerTheory.int_exp,
     Thm.CONJUNCT2 integerTheory.int_exp] @ [
    arithmeticTheory.ZERO_LT_EXP,
    Conv.GSYM integerTheory.INT_EXP,
    INT_EXP_1,
    INT_EXP_BASE_1,
    INT_EXP_2,
    INT_EXP_3,
    integerTheory.INT,
    int_arithTheory.INT_NUM_SUB,
    HolSmtTheory.INT_NUM_EDIV,
    HolSmtTheory.INT_NUM_EMOD,
    Conv.GSYM int_arithTheory.INT_NUM_DIVIDES,
    int_arithTheory.INT_NUM_COND,
    arithmeticTheory.GREATER_DEF,
    arithmeticTheory.GREATER_EQ,
    (* Rewrite inequalities against MAX before num-to-int transfer.  This
       keeps tautological bounds such as [y <= MAX x y] out of the much more
       expensive integer/absolute-value encoding. *)
    Thm.CONJUNCT1 (Drule.SPEC_ALL arithmeticTheory.MAX_LE),
    arithmeticTheory.MAX_DEF,
    arithmeticTheory.MIN_DEF,
    Drule.GEN_ALL (Thm.SYM intrealTheory.real_of_int_num)
  ]

  fun NUM_TO_INT_CONV tm =
    Conv.THENC
      (NUM_BINDERS_TO_INT_CONV,
       simpLib.SIMP_CONV pureSimps.pure_ss num_transfer_rewrites) tm
    handle Conv.UNCHANGED => Thm.REFL tm

  type native_float_transfer_info = {
    surface : string list,
    theorem : Thm.thm
  }

  (* The complete audited surface of the native binary_ieee transfer kit.
     Keep names and proofs together so extending preprocessing cannot silently
     outrun its coverage record. *)
  val native_float_transfer_infos : native_float_transfer_info list = [
    {surface = ["float record constructor"],
     theorem = smtfloatTheory.native_float_bits_transfer},
    {surface = ["universal float binder"],
     theorem = smtfloatTheory.native_float_forall_transfer},
    {surface = ["existential float binder"],
     theorem = smtfloatTheory.native_float_exists_transfer},
    {surface = ["float_plus_zero", "float_minus_zero",
                "float_plus_infinity", "float_minus_infinity",
                "float_some_qnan"],
     theorem = smtfloatTheory.native_float_special_transfer},
    {surface = ["float_is_nan", "float_is_infinite", "float_is_normal",
                "float_is_subnormal", "float_is_zero"],
     theorem = smtfloatTheory.native_float_classification_transfer},
    {surface = ["float_is_finite", "float_is_integral"],
     theorem = smtfloatTheory.native_float_finite_integral_transfer},
    {surface = ["float_is_signalling at canonical representative"],
     theorem = smtfloatTheory.native_float_signalling_transfer},
    {surface = ["negative sign predicate", "positive sign predicate"],
     theorem = smtfloatTheory.native_float_sign_transfer},
    {surface = ["float_abs"],
     theorem = smtfloatTheory.native_float_abs_transfer},
    {surface = ["float_negate"],
     theorem = smtfloatTheory.native_float_neg_transfer},
    {surface = ["float_less_than", "float_less_equal",
                "float_greater_than", "float_greater_equal",
                "float_equal", "float_unordered"],
     theorem = smtfloatTheory.native_float_comparison_transfer},
    {surface = ["float_add"],
     theorem = smtfloatTheory.native_float_add_transfer},
    {surface = ["float_sub"],
     theorem = smtfloatTheory.native_float_sub_transfer},
    {surface = ["float_mul"],
     theorem = smtfloatTheory.native_float_mul_transfer},
    {surface = ["float_div"],
     theorem = smtfloatTheory.native_float_div_transfer},
    {surface = ["float_sqrt"],
     theorem = smtfloatTheory.native_float_sqrt_transfer},
    {surface = ["float_mul_add"],
     theorem = smtfloatTheory.native_float_fma_transfer},
    {surface = ["float_to_real on finite input"],
     theorem = smtfloatTheory.native_float_to_real_transfer},
    {surface = ["float_to_ubv", "float_to_sbv"],
     theorem = smtfloatTheory.native_float_word_conversion_transfer},
    {surface = ["float_from_ieee_bv", "float_pack_ieee_bv at canon"],
     theorem = smtfloatTheory.native_float_ieee_bv_transfer},
    {surface = ["float_min"],
     theorem = smtfloatTheory.native_float_min_transfer},
    {surface = ["float_max"],
     theorem = smtfloatTheory.native_float_max_transfer},
    {surface = ["float_rem"],
     theorem = smtfloatTheory.native_float_rem_transfer},
    {surface = ["float_round with nonzero result or matching zero sign"],
     theorem = smtfloatTheory.native_float_round_transfer},
    {surface = ["real_to_float with nonzero result or matching zero sign"],
     theorem = smtfloatTheory.native_real_to_float_transfer},
    {surface = ["float_round_to_integral with nonzero result"],
     theorem = smtfloatTheory.native_float_round_to_integral_transfer}
  ]

  val native_float_transfer_surface =
    List.concat (List.map #surface native_float_transfer_infos)

  val native_float_transfer_theorems =
    List.map #theorem native_float_transfer_infos

  val native_float_transfer_rewrites =
    native_float_transfer_theorems @
    [smtfloatTheory.smtfp_is_finite_expansion,
     smtfloatTheory.smtfp_unordered_expansion,
     smtfloatTheory.smtfp_is_signalling_expansion,
     smtfloatTheory.smtfp_is_integral_expansion,
     smtfloatTheory.smtfp_rounding_of_binary_def,
     binary_ieeeTheory.rounding_case_def]

  (* Conditional transfers must see their native guards before the general
     pass lowers those guards to the smtfp surface. *)
  val native_float_guarded_context_rewrites =
    [smtfloatTheory.native_float_to_real_guarded_transfer,
     smtfloatTheory.native_float_round_sign_guarded_transfer,
     smtfloatTheory.native_float_round_guarded_transfer,
     smtfloatTheory.native_real_to_float_sign_guarded_transfer,
     smtfloatTheory.native_real_to_float_guarded_transfer,
     smtfloatTheory.native_float_round_to_integral_guarded_transfer]

  val native_float_guarded_transfer_rewrites =
    [smtfloatTheory.native_float_to_real_transfer,
     smtfloatTheory.native_float_round_transfer,
     smtfloatTheory.native_real_to_float_transfer,
     smtfloatTheory.native_float_round_to_integral_transfer]

  val native_float_ground_guard_transfers =
    [smtfloatTheory.native_float_round_transfer,
     smtfloatTheory.native_real_to_float_transfer]

  fun guarded_context_pattern theorem =
    let
      val (lhs, _) = boolSyntax.dest_eq (Thm.concl theorem)
      val (_, predicate_application) = boolSyntax.dest_imp lhs
      val (predicate, arguments) =
        boolSyntax.strip_comb predicate_application
      val _ = List.length arguments = 1 orelse
        raise ERR "guarded_context_pattern"
          "guarded transfer predicate is not unary"
    in
      (predicate, List.hd arguments)
    end

  (* HO_REWR_CONV deliberately does not guess an arbitrary surrounding
     predicate from an implication.  Match the raw result first, abstract
     its actual consequent context, and only then invoke the theorem-backed
     higher-order rewrite. *)
  fun instantiate_guarded_context theorem consequent occurrence =
    let
      val (_, raw_pattern) = guarded_context_pattern theorem
      val theorem = Drule.INST_TY_TERM
        (Term.match_term raw_pattern occurrence) theorem
      val (predicate, _) = guarded_context_pattern theorem
      val hole = Term.variant (Term.free_vars consequent)
        (Term.mk_var ("guarded_float_result", Term.type_of occurrence))
      val context = Term.mk_abs (hole,
        Term.subst [{redex = occurrence, residue = hole}] consequent)
    in
      Conv.BETA_RULE
        (Thm.INST [{redex = predicate, residue = context}] theorem)
    end

  val raw_float_result_predicates =
    [binary_ieeeSyntax.is_float_to_real,
     binary_ieeeSyntax.is_float_round,
     binary_ieeeSyntax.is_real_to_float,
     binary_ieeeSyntax.is_float_round_to_integral]

  fun count_raw_float_results tm =
    let
      val here = if List.exists (fn pred => pred tm)
        raw_float_result_predicates then 1 else 0
      val below =
        if Term.is_comb tm then
          let val (rator, rand) = Term.dest_comb tm in
            count_raw_float_results rator + count_raw_float_results rand
          end
        else if Term.is_abs tm then
          count_raw_float_results (Lib.snd (Term.dest_abs tm))
        else
          0
    in
      here + below
    end

  fun recognize_native_float_guarded_context tm =
    let
      fun guarded_implication () =
        if not (boolSyntax.is_imp tm) then NONE
        else
          let
            val (_, consequent) = boolSyntax.dest_imp tm
            val occurrences = Library.subterms consequent
            fun first_instantiation _ [] = NONE
              | first_instantiation theorem (occurrence :: rest) =
                  let
                    val (_, raw_pattern) = guarded_context_pattern theorem
                  in
                    if FCNet.can_match_term raw_pattern occurrence then
                      let
                        val instantiated = instantiate_guarded_context
                          theorem consequent occurrence
                        val (lhs, _) =
                          boolSyntax.dest_eq (Thm.concl instantiated)
                      in
                        if FCNet.can_match_term lhs tm then
                          SOME (Drule.INST_TY_TERM
                            (Term.match_term lhs tm) instantiated)
                        else
                          first_instantiation theorem rest
                      end
                    else
                      first_instantiation theorem rest
                  end
            fun first_theorem [] = NONE
              | first_theorem (theorem :: rest) =
                  (case first_instantiation theorem occurrences of
                     SOME instantiated => SOME instantiated
                   | NONE => first_theorem rest)
          in
            first_theorem native_float_guarded_context_rewrites
          end

      fun ground_pattern theorem =
        let
          val (_, transfer) = boolSyntax.dest_imp (Thm.concl theorem)
        in
          Lib.fst (boolSyntax.dest_eq transfer)
        end

      fun lift_transfer consequent occurrence transfer =
        let
          val hole = Term.variant (Term.free_vars consequent)
            (Term.mk_var
              ("ground_guarded_float_result", Term.type_of occurrence))
          val context = Term.mk_abs (hole,
            Term.subst [{redex = occurrence, residue = hole}] consequent)
        in
          Conv.BETA_RULE (Thm.AP_TERM context transfer)
        end

      fun ground_instantiation _ [] = NONE
        | ground_instantiation theorem (occurrence :: rest) =
            let
              val pattern = ground_pattern theorem
            in
              if FCNet.can_match_term pattern occurrence then
                let
                  val instantiated = Drule.INST_TY_TERM
                    (Term.match_term pattern occurrence) theorem
                  val (guard, _) =
                    boolSyntax.dest_imp (Thm.concl instantiated)
                in
                  if List.null (Term.free_vars guard) then
                    let
                      val evaluated = bossLib.EVAL guard
                      val (_, verdict) =
                        boolSyntax.dest_eq (Thm.concl evaluated)
                    in
                      if Term.aconv verdict boolSyntax.T then
                        let
                          val transfer = Drule.MATCH_MP instantiated
                            (Drule.EQT_ELIM evaluated)
                        in
                          SOME (lift_transfer tm occurrence transfer)
                        end
                      else
                        ground_instantiation theorem rest
                    end
                  else
                    ground_instantiation theorem rest
                end
              else
                ground_instantiation theorem rest
            end

      fun ground_theorem _ [] = NONE
        | ground_theorem occurrences (theorem :: rest) =
            (case ground_instantiation theorem occurrences of
               SOME instantiated => SOME instantiated
             | NONE => ground_theorem occurrences rest)
    in
      case guarded_implication () of
        SOME instantiated => SOME instantiated
      | NONE =>
      let
        val occurrences = Library.subterms tm
      in
        ground_theorem occurrences native_float_ground_guard_transfers
      end
    end

  fun native_float_guarded_context_match_conv_with prove tm =
    case recognize_native_float_guarded_context tm of
      NONE => raise Conv.UNCHANGED
    | SOME instantiated =>
    let
      val result = prove instantiated tm
      val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl result)
      val _ = Term.aconv lhs tm orelse
        raise ERR "native_float_guarded_context_match_conv_with"
          "admitted proof theorem has the wrong left-hand side"
      val count_before = count_raw_float_results tm
      val count_after = count_raw_float_results rhs
      val _ = count_after < count_before orelse
        raise ERR "native_float_guarded_context_match_conv_with"
          "admitted proof theorem does not strictly reduce raw FP results"
    in
      result
    end

  fun native_float_guarded_context_match_conv tm =
    native_float_guarded_context_match_conv_with
      (fn theorem => Conv.HO_REWR_CONV theorem) tm

  fun native_float_guarded_postorder_conv root_conversion tm =
    let
      fun theorem_rhs theorem =
        Lib.snd (boolSyntax.dest_eq (Thm.concl theorem))
      fun descend input =
        let
          val children =
            if Term.is_comb input then
              let val (rator, rand) = Term.dest_comb input
              in Thm.MK_COMB (descend rator, descend rand) end
            else if Term.is_abs input then
              let val (variable, body) = Term.dest_abs input
              in Thm.ABS variable (descend body) end
            else
              Thm.REFL input
          val current = theorem_rhs children
          val root = root_conversion current
            handle Conv.UNCHANGED => Thm.REFL current
          val revisited =
            if Term.aconv current (theorem_rhs root) then root
            else Thm.TRANS root (descend (theorem_rhs root))
        in
          Thm.TRANS children revisited
        end
      val result = descend tm
      val (lhs, _) = boolSyntax.dest_eq (Thm.concl result)
      val _ = Term.aconv lhs tm orelse
        raise ERR "native_float_guarded_postorder_conv"
          "recursive traversal produced a theorem for the wrong input"
    in
      result
    end

  val native_float_transfer_ss =
    simpLib.++
      (simpLib.++ (pureSimps.pure_ss, wordsLib.SIZES_ss),
       numSimps.REDUCE_ss)

  val native_float_guarded_transfer_ss =
    simpLib.++ (native_float_transfer_ss, realSimps.REAL_ARITH_ss)

  fun NATIVE_FLOAT_TO_SMT_CONV tm =
    let
      fun apply_or_refl conversion input = conversion input
        handle Conv.UNCHANGED => Thm.REFL input
      val guarded = native_float_guarded_postorder_conv
        native_float_guarded_context_match_conv tm
      val guarded_rhs = Lib.snd (boolSyntax.dest_eq (Thm.concl guarded))
      val lowered_guards = apply_or_refl
        (simpLib.SIMP_CONV native_float_guarded_transfer_ss
          native_float_guarded_transfer_rewrites) guarded_rhs
      val lowered_guards_rhs =
        Lib.snd (boolSyntax.dest_eq (Thm.concl lowered_guards))
      val lowered = apply_or_refl
        (simpLib.SIMP_CONV native_float_transfer_ss
          native_float_transfer_rewrites) lowered_guards_rhs
    in
      Thm.TRANS guarded (Thm.TRANS lowered_guards lowered)
    end

  val hol_string_transfer_rewrites = [
    Conv.GSYM smtstringTheory.str_inj_11,
    smtstringTheory.str_inj_STRCAT,
    smtstringTheory.str_inj_isPREFIX,
    smtstringTheory.str_inj_string_lt,
    smtstringTheory.str_inj_string_le
  ]

  fun HOL_STRING_TO_SMT_CONV tm =
    simpLib.SIMP_CONV pureSimps.pure_ss hol_string_transfer_rewrites tm
    handle Conv.UNCHANGED => Thm.REFL tm

  (* Boolean cases are already SMT's native `ite`; treating COND as a
     datatype case would recursively lower each generated conditional. *)
  fun datatype_normalization_excluded ty =
    datatype_translation_excluded ty orelse same_type (ty, Type.bool)

  fun explicit_depth_conv conversion tm =
    let
      fun changed theorem =
        let val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl theorem)
        in not (Term.aconv lhs rhs) end
      fun descend input =
        let
          val children =
            if Term.is_comb input then
              let val (rator, rand) = Term.dest_comb input
              in Thm.MK_COMB (descend rator, descend rand) end
            else if Term.is_abs input then
              let val (variable, body) = Term.dest_abs input
              in Thm.ABS variable (descend body) end
            else Thm.REFL input
          val (_, current) = boolSyntax.dest_eq (Thm.concl children)
          val root = conversion current
            handle Conv.UNCHANGED => Thm.REFL current
        in
          if changed children then Thm.TRANS children root else root
        end
    in
      descend tm
    end

  fun admitted_beta_conv tm =
    if Term.is_comb tm andalso Term.is_abs (Lib.fst (Term.dest_comb tm)) then
      Thm.BETA_CONV tm
    else
      raise Conv.UNCHANGED

  fun admitted_k_conv tm =
    if combinSyntax.is_K tm then Conv.REWR_CONV combinTheory.K_THM tm
    else raise Conv.UNCHANGED

  fun admitted_eta_conv tm =
    if Term.is_abs tm then
      let
        val (variable, body) = Term.dest_abs tm
      in
        if Term.is_comb body then
          let
            val (function, argument) = Term.dest_comb body
          in
            if Term.aconv argument variable andalso
               not (Term.free_in variable function) then
              Drule.ETA_CONV tm
            else
              raise Conv.UNCHANGED
          end
        else
          raise Conv.UNCHANGED
      end
    else
      raise Conv.UNCHANGED

  fun eta_expansion_reduction label function domains =
    let
      val variables = List.map Term.genvar domains
      val expanded = Term.list_mk_abs
        (variables, Term.list_mk_comb (function, variables))
      fun contract_introduced [] tm = Thm.REFL tm
        | contract_introduced (_ :: remaining) tm =
            if Term.is_abs tm then
              let
                val (variable, body) = Term.dest_abs tm
                val children = Thm.ABS variable
                  (contract_introduced remaining body)
                val (_, current) = boolSyntax.dest_eq (Thm.concl children)
                val step = admitted_eta_conv current
                val (step_lhs, step_rhs) =
                  boolSyntax.dest_eq (Thm.concl step)
                val _ = Term.aconv step_lhs current orelse
                  raise ERR label
                    "eta step theorem has the wrong left-hand side"
                val _ = not (Term.aconv step_lhs step_rhs) orelse
                  raise ERR label "eta step theorem made no progress"
              in
                Thm.TRANS children step
              end
            else
              raise ERR label "introduced eta binder was lost"
      val reduction = contract_introduced variables expanded
      val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl reduction)
      val _ = Term.aconv lhs expanded orelse
        raise ERR label "eta theorem has the wrong left-hand side"
      val _ = not (Term.aconv lhs rhs) orelse
        raise ERR label "eta theorem made no progress"
      val _ = Term.aconv rhs function orelse
        raise ERR label "eta proof did not reduce to the admitted function"
    in
      reduction
    end

  fun datatype_case_equality ty scrutinee extra_rewrites lhs_for rhs_for =
    let
      val tyinfo =
        case TypeBase.fetch ty of
          SOME info => info
        | NONE => raise ERR "datatype_case_equality"
            "missing TypeBase entry"
      val x = Term.genvar ty
      val equality = boolSyntax.mk_eq (lhs_for x, rhs_for x)
      val predicate = Term.mk_abs (x, equality)
      val type_subst = Type.match_type (TypeBasePure.ty_of tyinfo) ty
      val forall_cases = Thm.INST_TYPE type_subst
        (DatatypeSimps.mk_type_forall_thm_tyinfo tyinfo)
      val expanded = Thm.SPEC predicate forall_cases
      val rewrites = TypeBasePure.case_def_of tyinfo :: extra_rewrites tyinfo
      val constructor_cases =
        Lib.snd (boolSyntax.dest_eq (Thm.concl expanded))
      val beta = explicit_depth_conv admitted_beta_conv constructor_cases
      val beta_cases = Lib.snd (boolSyntax.dest_eq (Thm.concl beta))
      val simplified = simpLib.SIMP_CONV pureSimps.pure_ss
        (boolTheory.COND_CLAUSES :: boolTheory.REFL_CLAUSE ::
         boolTheory.FORALL_SIMP :: boolTheory.AND_CLAUSES :: rewrites)
        beta_cases
      val constructor_theorem =
        if boolSyntax.is_eq (Thm.concl simplified) then
          let
            val closed = Thm.TRANS beta simplified
            val closed_rhs = Lib.snd (boolSyntax.dest_eq (Thm.concl closed))
          in
            if Term.aconv closed_rhs boolSyntax.T then
              Drule.EQT_ELIM closed
            else
              raise ERR "datatype_case_equality"
                ("constructor cases did not close: " ^
                 Library.thm_to_string closed)
          end
        else
          Thm.EQ_MP (Thm.SYM beta) simplified
      val theorem = Thm.EQ_MP (Thm.SYM expanded) constructor_theorem
      val specialized0 = Thm.SPEC scrutinee theorem
      val specialized = Conv.CONV_RULE
        (explicit_depth_conv admitted_beta_conv) specialized0
    in
      Conv.CONV_RULE
        (Conv.RAND_CONV (explicit_depth_conv
          admitted_k_conv))
        specialized
    end

  (* A partial HOL destructor has no theorem fixing its value on constructors
     outside the owning branch.  Preserve such constructor applications
     literally: replacing them by the parser selector's ARB choice would be
     stronger than the registered theorem.  The resulting outer case is the
     parser's exact generic case form, and no destructor remains applied to a
     symbolic native-datatype value. *)
  fun datatype_destructor_case destructor theorem data_ty scrutinee =
    let
      fun clause constructor =
        let
          val (domains, _) = boolSyntax.strip_fun (Term.type_of constructor)
          val arguments = List.map Term.genvar domains
          val pattern = Term.list_mk_comb (constructor, arguments)
          val application = Term.mk_comb (destructor, pattern)
          val result =
            Lib.snd (boolSyntax.dest_eq (Thm.concl
              (simpLib.SIMP_CONV pureSimps.pure_ss [theorem] application)))
            handle Conv.UNCHANGED => application
        in
          (pattern, result)
        end
      val raw_case = TypeBase.mk_case
        (scrutinee, List.map clause (datatype_constructors data_ty))
    in
      datatype_case_normal_form raw_case
    end

  fun recognize_datatype_destructor tm =
    if not (Term.is_comb tm) then raise Conv.UNCHANGED
    else let
      val (destructor, scrutinee) = Term.dest_comb tm
      val data_ty = Term.type_of scrutinee
      val _ = not (datatype_normalization_excluded data_ty) orelse
        raise Conv.UNCHANGED
      val tyinfo =
        case TypeBase.fetch data_ty of
          SOME info => info
        | NONE => raise Conv.UNCHANGED
      val constructors = List.map (TypeBasePure.cinst data_ty)
        (TypeBasePure.constructors_of tyinfo)
      val theorem =
        case datatype_destructor_theorem tyinfo destructor of
          SOME theorem => theorem
        | NONE => raise Conv.UNCHANGED
      val (scrutinee_head, _) = boolSyntax.strip_comb scrutinee
      val constructor_headed = Term.is_const scrutinee_head andalso
        List.exists (Term.same_const scrutinee_head) constructors
      val constructor_reduces =
        not constructor_headed orelse
        theorem_reduces_exact_application theorem tm
      val _ = constructor_reduces orelse
        raise Conv.UNCHANGED
    in
      (destructor, theorem, scrutinee, data_ty)
    end

  fun datatype_destructor_normalize_conv_with proof tm =
    let
      val admitted = recognize_datatype_destructor tm
      val theorem = proof admitted
      val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl theorem)
      val _ = Term.aconv lhs tm orelse
        raise ERR "datatype_destructor_normalize_conv"
          "admitted proof theorem has the wrong left-hand side"
      val _ = not (Term.aconv lhs rhs) orelse
        raise ERR "datatype_destructor_normalize_conv"
          "admitted proof theorem is alpha-unchanged"
    in
      theorem
    end

  fun prove_datatype_destructor
      (destructor, theorem, scrutinee, data_ty) =
    let
      fun lhs x = Term.mk_comb (destructor, x)
      fun rhs x = datatype_destructor_case destructor theorem data_ty x
    in
      (* Recognition is complete above.  A failure here is a malformed
         registered family member and must remain a named proof error,
         never be relabelled as an inapplicable rung. *)
      datatype_case_equality data_ty scrutinee
        (fn _ => [theorem]) lhs rhs
    end

  val datatype_destructor_normalize_conv =
    datatype_destructor_normalize_conv_with prove_datatype_destructor

  fun record_accessor_normalize_conv tm =
    let
      val recognized =
        SOME (let
          val (accessor, record) = Term.dest_comb tm
          val record_ty = Term.type_of record
          val _ = not (datatype_normalization_excluded record_ty) orelse
            raise ERR "record_accessor_normalize_conv" "excluded datatype"
          val fields = TypeBase.fields_of record_ty
          val _ = if List.null fields then
              raise ERR "record_accessor_normalize_conv" "not a record"
            else ()
          val selector_index = Lib.index
            (fn (_, {accessor = candidate, ...} :
                     TypeBasePure.rcd_fieldinfo) =>
              Term.same_const accessor candidate) fields
          val constructor =
            case datatype_constructors record_ty of
              [constructor] => constructor
            | _ => raise ERR "record_accessor_normalize_conv"
                "record constructor count"
        in
          (accessor, record, record_ty, constructor, selector_index)
        end)
        handle Feedback.HOL_ERR _ => NONE
    in
      case recognized of
        NONE => raise Conv.UNCHANGED
      | SOME (accessor, record, record_ty, constructor, selector_index) =>
          let
            fun lhs x = Term.mk_comb (accessor, x)
            fun rhs x = datatype_selector_term record_ty constructor
              selector_index x
          in
            datatype_case_equality record_ty record
              TypeBasePure.accessors_of lhs rhs
          end
    end

  fun record_update_normalize_conv tm =
    let
      val recognized =
        SOME (let
          val (update_f, record) = Term.dest_comb tm
          val (update, updater) = Term.dest_comb update_f
          val record_ty = Term.type_of record
          val result_ty = Term.type_of tm
          val _ = not (datatype_normalization_excluded record_ty) andalso
                  not (datatype_normalization_excluded result_ty) orelse
            raise ERR "record_update_normalize_conv" "excluded datatype"
          val input_fields = TypeBase.fields_of record_ty
          val result_fields = TypeBase.fields_of result_ty
          val _ = if List.null input_fields orelse
                     List.length input_fields <> List.length result_fields then
              raise ERR "record_update_normalize_conv" "not matching records"
            else ()
          val update_index = Lib.index
            (fn (_, {fupd, ...} : TypeBasePure.rcd_fieldinfo) =>
              Term.same_const update fupd) input_fields
          val input_constructor =
            case datatype_constructors record_ty of
              [constructor] => constructor
            | _ => raise ERR "record_update_normalize_conv"
                "input record constructor count"
          val result_constructor =
            case datatype_constructors result_ty of
              [constructor] => constructor
            | _ => raise ERR "record_update_normalize_conv"
                "result record constructor count"
        in
          (update, updater, record, record_ty, result_fields, update_index,
           input_constructor, result_constructor)
        end)
        handle Feedback.HOL_ERR _ => NONE
    in
      case recognized of
        NONE => raise Conv.UNCHANGED
      | SOME (update, updater, record, record_ty, result_fields,
              update_index, input_constructor, result_constructor) =>
        let
      fun lhs x = Term.list_mk_comb (update, [updater, x])
      fun rhs x =
        let
          fun field selector_index =
            let
              val selected = datatype_selector_term record_ty
                input_constructor selector_index x
            in
              if selector_index = update_index then
                Term.mk_comb (updater, selected)
              else
                selected
            end
          val values = List.map field
            (List.tabulate (List.length result_fields, fn n => n))
        in
          Term.list_mk_comb (result_constructor, values)
        end
        in
          datatype_case_equality record_ty record
            (fn tyinfo => TypeBasePure.accessors_of tyinfo @
              TypeBasePure.updates_of tyinfo) lhs rhs
        end
    end

  (* Once the term has been admitted as a case over a constructor, proof
     construction is no longer a recognition probe.  In particular, never
     turn a proof-conversion failure into [UNCHANGED]: it is a checked-path
     failure and must retain its original diagnostic. *)
  fun admitted_datatype_constructor_case_reduce_conv proof_conv tm =
    let
      val theorem = proof_conv tm
      val (_, rhs) = boolSyntax.dest_eq (Thm.concl theorem)
    in
      if Term.aconv tm rhs then
        raise ERR "datatype_constructor_case_reduce_conv"
          "admitted proof conversion returned an alpha-unchanged result"
      else
        theorem
    end

  (* Reduce every TypeBase case whose scrutinee is already a constructor.
     Parser selectors and testers are cases too, so the datatype's own case
     theorem is the single generic proof source for all three forms. *)
  fun datatype_constructor_case_reduce_conv_with proof_conv tm =
    let
      val recognized =
        SOME (let
          val (_, scrutinee, _) = TypeBase.dest_case tm
          val data_ty = Term.type_of scrutinee
          val _ = not (datatype_normalization_excluded data_ty) orelse
            raise ERR "datatype_constructor_case_reduce_conv"
              "excluded datatype"
          val tyinfo =
            case TypeBase.fetch data_ty of
              SOME info => info
            | NONE => raise ERR "datatype_constructor_case_reduce_conv"
                "missing TypeBase entry"
          val (head, _) = boolSyntax.strip_comb scrutinee
          val constructors = List.map (TypeBasePure.cinst data_ty)
            (TypeBasePure.constructors_of tyinfo)
          val _ = List.exists (Term.same_const head) constructors orelse
            raise ERR "datatype_constructor_case_reduce_conv"
              "case scrutinee is not a constructor application"
        in
          tyinfo
        end)
        handle Feedback.HOL_ERR _ => NONE
    in
      case recognized of
        NONE => raise Conv.UNCHANGED
      | SOME tyinfo =>
          admitted_datatype_constructor_case_reduce_conv
            (proof_conv tyinfo) tm
    end

  val datatype_constructor_case_reduce_conv =
    datatype_constructor_case_reduce_conv_with (fn tyinfo =>
      simpLib.SIMP_CONV pureSimps.pure_ss
        [TypeBasePure.case_def_of tyinfo])

  (* [TypeBase.dest_case] requires every constructor branch to be presented
     as a syntactic lambda.  Direct uses of a case constant may instead pass
     a function-valued branch (for example option_CASE ... n s).  Eta-expand
     those branches from the current TypeBase constructor arities, with a
     kernel theorem, so the generic case normalizer below sees the same case
     rather than letting the emitter lower an unnormalized source term. *)
  fun recognize_datatype_case_branch_eta tm =
    let
      val (case_const, arguments) = boolSyntax.strip_comb tm
      fun candidate [] = NONE
        | candidate (scrutinee :: branches) =
            let
              val data_ty = Term.type_of scrutinee
            in
              if datatype_normalization_excluded data_ty then NONE
              else
                case TypeBase.fetch data_ty of
                  NONE => NONE
                | SOME tyinfo =>
                    let
                      val constructors = List.map
                        (TypeBasePure.cinst data_ty)
                        (TypeBasePure.constructors_of tyinfo)
                    in
                      if List.null constructors then NONE
                      else
                      let
                        val registered_case = TypeBasePure.cinst data_ty
                          (TypeBasePure.case_const_of tyinfo)
                      in
                      if not (Term.same_const case_const registered_case) then
                        NONE
                      else if List.length branches < List.length constructors
                      then NONE
                      else if List.length branches > List.length constructors
                      then NONE (* normalize the saturated rator prefix *)
                      else
                        let
                          fun needs_eta (constructor, branch) =
                            let
                              val (domains, _) = boolSyntax.strip_fun
                                (Term.type_of constructor)
                              val (variables, _) = Term.strip_abs branch
                            in
                              List.length variables < List.length domains
                            end
                        in
                          if List.exists needs_eta
                              (ListPair.zipEq (constructors, branches)) then
                            SOME (case_const, scrutinee,
                              constructors, branches)
                          else NONE
                        end
                      end
                    end
            end
    in
      case candidate arguments of
        NONE => raise Conv.UNCHANGED
      | SOME admitted => admitted
    end

  fun eta_expand_branch (constructor, branch) =
    let
      val (domains, _) = boolSyntax.strip_fun (Term.type_of constructor)
      val (existing_variables, body) = Term.strip_abs branch
      val constructor_arity = List.length domains
      val existing_arity = List.length existing_variables
    in
      if existing_arity >= constructor_arity then Thm.REFL branch
      else
        let
          val missing_domains = List.drop (domains, existing_arity)
          val body_expansion = Thm.SYM (eta_expansion_reduction
            "datatype_case_branch_eta_conv" body missing_domains)
        in
          List.foldr (fn (variable, theorem) =>
            Thm.ABS variable theorem) body_expansion existing_variables
        end
    end

  fun prove_datatype_case_branch_eta
      (case_const, scrutinee, constructors, branches) =
    let
      val branch_theorems = ListPair.mapEq eta_expand_branch
        (constructors, branches)
      val changed = List.exists (fn theorem =>
        let val (left, right) = boolSyntax.dest_eq (Thm.concl theorem)
        in not (Term.aconv left right) end) branch_theorems
      val _ = changed orelse raise ERR "datatype_case_branch_eta_conv"
        "admitted case had no eta-expandable branch"
    in
      List.foldl (fn (argument, application) =>
        Thm.MK_COMB (application, argument))
        (Thm.MK_COMB (Thm.REFL case_const, Thm.REFL scrutinee))
        branch_theorems
    end

  fun datatype_case_branch_eta_conv_with proof tm =
    let
      val admitted = recognize_datatype_case_branch_eta tm
      val theorem = proof admitted
      val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl theorem)
      val _ = Term.aconv lhs tm orelse
        raise ERR "datatype_case_branch_eta_conv"
          "admitted proof theorem has the wrong left-hand side"
      val _ = not (Term.aconv lhs rhs) orelse
        raise ERR "datatype_case_branch_eta_conv"
          "admitted proof theorem is alpha-unchanged"
    in
      theorem
    end

  val datatype_case_branch_eta_conv =
    datatype_case_branch_eta_conv_with prove_datatype_case_branch_eta

  fun datatype_case_normalize_conv tm =
    let
      val recognized =
        SOME (let
          val (_, scrutinee, clauses) = TypeBase.dest_case tm
          val data_ty = Term.type_of scrutinee
          val _ = not (datatype_normalization_excluded data_ty) orelse
            raise ERR "datatype_case_normalize_conv" "excluded datatype"
          val _ =
            case parser_datatype_case tm of
              SOME _ => raise ERR "datatype_case_normalize_conv"
                "already in parser normal form"
            | NONE => ()
        in
          (scrutinee, clauses, data_ty)
        end)
        handle Feedback.HOL_ERR _ => NONE
    in
      case recognized of
        NONE => raise Conv.UNCHANGED
      | SOME (scrutinee, clauses, data_ty) =>
          let
            fun lhs x = TypeBase.mk_case (x, clauses)
            fun rhs x = datatype_case_normal_form (lhs x)
          in
            datatype_case_equality data_ty scrutinee (fn _ => []) lhs rhs
          end
    end

  val datatype_normalization_rungs = [
    datatype_destructor_normalize_conv,
    record_accessor_normalize_conv,
    record_update_normalize_conv,
    datatype_case_branch_eta_conv,
    datatype_constructor_case_reduce_conv,
    datatype_case_normalize_conv
  ]

  fun first_datatype_normalization_rung [] _ = raise Conv.UNCHANGED
    | first_datatype_normalization_rung (rung :: rungs) tm =
        rung tm
        handle Conv.UNCHANGED =>
          first_datatype_normalization_rung rungs tm

  fun DATATYPE_TO_SMT_CONV tm =
    let
      fun changed theorem =
        let val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl theorem)
        in not (Term.aconv lhs rhs) end
      fun validate input theorem =
        let
          val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl theorem)
          val _ = Term.aconv lhs input orelse
            raise ERR "DATATYPE_TO_SMT_CONV"
              "normalization theorem has the wrong left-hand side"
          val _ = not (Term.aconv lhs rhs) orelse
            raise ERR "DATATYPE_TO_SMT_CONV"
              "normalization theorem made no progress"
        in rhs end
      fun normalize ancestors input =
        let
          val children =
            if Term.is_comb input then
              let
                val (rator, rand) = Term.dest_comb input
              in
                Thm.MK_COMB
                  (normalize ancestors rator, normalize ancestors rand)
              end
            else if Term.is_abs input then
              let val (variable, body) = Term.dest_abs input
              in Thm.ABS variable (normalize ancestors body) end
            else
              Thm.REFL input
          val (_, current) = boolSyntax.dest_eq (Thm.concl children)
          val root =
            (let
               val step = first_datatype_normalization_rung
                 datatype_normalization_rungs current
               val rhs = validate current step
               val _ = not (List.exists (Term.aconv rhs) ancestors) orelse
                 raise ERR "DATATYPE_TO_SMT_CONV"
                   "normalization revisited an earlier alpha-equivalent term"
             in
               Thm.TRANS step (normalize (current :: ancestors) rhs)
             end
             handle Conv.UNCHANGED => Thm.REFL current)
        in
          if changed children then Thm.TRANS children root else root
        end
    in
      normalize [] tm
    end

  fun num_free_concl_vars (asms, concl) =
  let
    fun is_num_var v =
      Term.is_var v andalso
      Type.compare (Term.type_of v, numSyntax.num) = EQUAL
    fun is_bag_var v =
      Term.is_var v andalso
      (case Lib.total Type.dom_rng (Term.type_of v) of
         SOME (_, rng) => Type.compare (rng, numSyntax.num) = EQUAL
       | NONE => false)
    val asm_fvs = List.concat (List.map Term.free_vars asms)
    fun free_in_asms v = List.exists (fn w => Term.aconv v w) asm_fvs
  in
    List.filter (fn v => (is_num_var v orelse is_bag_var v) andalso
      not (free_in_asms v)) (Term.free_vars concl)
  end

  fun SPEC_NUM_FREE_VARS_TAC_EXCEPT exclude g =
  let
    val vars = List.filter (not o exclude) (num_free_concl_vars g)
  in
    Tactical.MAP_EVERY (fn v => Tactic.SPEC_TAC (v, v)) vars g
  end

  val SPEC_NUM_FREE_VARS_TAC =
    SPEC_NUM_FREE_VARS_TAC_EXCEPT (fn _ => false)

  local
    structure A = arithmeticTheory
    structure I = integerTheory
    structure IR = intrealTheory
    structure R = realTheory
    structure RA = realaxTheory
  in
    fun thms_per_const const =
    let
      val { Thy, Name, Ty } = Term.dest_thy_const const
      val bool = Type.bool
      val num = numSyntax.num
      val op--> = Type.-->
      infixr 3 -->
    in
      (* NOTE: when adding a theorem to the list below, make sure that it
         doesn't have any free var -- otherwise, ASSUME_TAC will specialize
         the theorem to any free var in the goal that happens to have the same
         name, which very often is not what is desired. As an example,
         integerTheory's `INT_POW` should not be added -- instead, add
         `int_exp`. If no appropriate quantified theorem is available,
         `Drule.GEN_ALL` can be used to quantify all free vars in a theorem.

         Also, make sure the theorem is really needed -- some theorems seem to
         cause an explosion in the time needed to solve some goals, often
         making Z3 unable to solve them -- and it's not always easy to tell a
         priori which ones do. As an example, arithmeticTheory.EXP_1 doesn't
         seem to cause issues, but EXP_2 prevents Z3 from solving
         ``x DIV 42 <= x``. *)
      case (Thy, Name) of
        ("arithmetic", "*") => []
      | ("arithmetic", "+") => []
      | ("arithmetic", "-") => []
      | ("arithmetic", "<=") => []
      | ("arithmetic", ">") => []
      | ("arithmetic", ">=") => []
      | ("arithmetic", "DIV") => []
      | ("arithmetic", "EXP") => []
      | ("arithmetic", "MAX") => []
      | ("arithmetic", "MIN") => []
      | ("arithmetic", "MOD") => []
      | ("integer", "Num") => []
      | ("integer", "int_div") => [ I.INT_DIV_EDIV ]
      | ("integer", "int_exp") => [ I.int_exp ]
      | ("integer", "int_max") => [ I.INT_MAX ]
      | ("integer", "int_min") => [ I.INT_MIN ]
      | ("integer", "int_mod") => [ I.INT_MOD_EMOD ]
      | ("integer", "int_of_num") => []
      | ("integer", "int_quot") => [ I.INT_QUOT_EDIV ]
      | ("integer", "int_rem") => [ I.INT_REM_EMOD ]
      | ("intreal", "INT_CEILING") => []
      | ("marker", "Abbrev") => [ markerTheory.Abbrev_def ]
      | ("min", "=") =>
          if Type.compare (Ty, num --> num --> bool) = EQUAL then
            []
          else
            []
      | ("num", "SUC") => []
      | ("prim_rec", "<") => []
      | ("realax", "/") => [ HolSmtTheory.real_div_smt_rdiv ]
      | ("realax", "NUM_CEILING") => [ IR.INT_NUM_CEILING, R.NUM_CEILING_BASE ]
      | ("realax", "NUM_FLOOR") => [ IR.INT_NUM_FLOOR, R.NUM_FLOOR_BASE ]
      | ("realax", "abs") => [ R.abs ]
      | ("realax", "inv") => [ R.REAL_INV_1OVER ]
      | ("realax", "max") => [ RA.real_max ]
      | ("realax", "min") => [ RA.real_min ]
      | ("realax", "pow") => [ R.POW_2, R.POW_ONE, R.REAL_POW_LT, RA.real_pow ]
      | ("realax", "real_of_num") =>
          [ Drule.GEN_ALL (Thm.SYM IR.real_of_int_num) ]
      | _ => []
    end
  end

  (* Prepends the conclusion of a theorem to the list of its hypothesis and
     returns the resulting list of terms *)
  fun thm_terms thm =
  let
    val (hyps, concl) = Thm.dest_thm thm
  in
    concl :: hyps
  end

  (* Compares two theorems *)
  fun thm_compare (thm1, thm2) =
    List.collate Term.compare (thm_terms thm1, thm_terms thm2)

  (* An empty set of theorems *)
  val empty_thmset = HOLset.empty thm_compare

  (* Computes the list of theorems to add to the goal, given a list of all the
     terms in the goal. Since the resulting list of theorems might require more
     theorems to be added (for the SMT solvers to properly solve the goal), this
     function calls itself recursively until no new theorems are needed anymore. *)
  fun get_thms ([], acc) = HOLset.listItems acc
    | get_thms (terms, acc) =
      let
        (* Create a set of all the constants used in all the provided terms *)
        val atoms = Term.all_atomsl terms Term.empty_tmset
        val consts = HOLset.filter Term.is_const atoms

        (* Generate a set of all the theorems we want to add, based on these
           constants *)
        fun const_thms (const, acc) = HOLset.addList (acc, thms_per_const const)
        val wanted_thms = HOLset.foldl const_thms empty_thmset consts

        (* Apply NUM_TO_INT_CONV to these theorems, to convert any num literals
           they might have into int literals. We do this here because this
           conversion introduces constants that might trigger new theorems to be
           added in subsequent iterations *)
        fun conv_thm (thm, acc) =
          let
            val thm = Conv.CONV_RULE NUM_TO_INT_CONV thm
            val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl thm)
          in
            if Term.aconv lhs rhs then acc else HOLset.add (acc, thm)
          end
          handle Feedback.HOL_ERR _ => HOLset.add (acc, thm)
        val wanted_thms = HOLset.foldl conv_thm empty_thmset wanted_thms

        (* Since some of the theorems might have already been added in a
           previous recursive call, here we compute the theorems that will
           actually be newly added in this iteration *)
        val thms_to_add = HOLset.difference (wanted_thms, acc)

        (* Now we compute the new terms that will have to be analyzed in the
           next recursive call, which correspond to the terms used in the
           theorems newly added in this iteration *)
        fun add_new_terms (thm, acc) = HOLset.addList (acc, thm_terms thm)
        val new_terms = HOLset.foldl add_new_terms Term.empty_tmset thms_to_add
      in
        get_thms (HOLset.listItems new_terms, HOLset.union (acc, thms_to_add))
      end

in

  (* Controls whether HolSmt will try to include relevant theorems when trying
     to prove the goal, including theorems necessary for solving goals that
     have terms of type `num`. Unfortunately, these theorems may also hinder
     SMT performance in some cases, hence this escape hatch. *)
  val include_theorems = ref true

  fun translation_logic ({logic, ...} : translation) = logic
  fun translation_regime ({regime, ...} : translation) = regime
  fun translation_records ({records, ...} : translation) = records ()

  (* Solver command policies consume the feature scan recorded for this exact
     HOL translation, rather than trying to recognize syntax in printed
     SMT-LIB. *)
  fun translation_has_quantifiers translation =
    case List.find
      (fn LogicSelection _ => true | _ => false)
      (translation_records translation) of
      SOME (LogicSelection {
        features = LogicFeatures {quantifiers, ...}, ...}) => quantifiers
    | _ => raise ERR "translation_has_quantifiers"
        "translation has no LogicSelection record"

  (* This is the closed registry of unconditional definitions for HOL heads
     that checked proof parsers use to represent emitted SMT operators.  An
     entry is enabled only by an EncodedSymbol from the current translation.
     Matching uses HOL constant identity and arity, never an SMT or HOL name.

     Integer div/mod illustrate why [emitted_head] and [replay_head] may
     differ: translation emits HOL ediv/emod as SMT div/mod, while CPC parses
     their specified total semantics as smt_ediv_total/smt_emod_total.  Their
     compute theorems are the unconditional unfolding identities: they also
     expose the underlying HOL div/mod operation in one mechanically selected
     rewrite.  Real smt_rdiv is deliberately absent because its zero-divisor
     value is underspecified and therefore has no sound unconditional
     unfolding. *)
  type emitted_definition_spec = {
    emitted_head : Term.term,
    arity : int,
    replay_head : Term.term,
    unfolding : Thm.thm
  }

  val emitted_definition_specs : emitted_definition_spec list = [
    {emitted_head = wordsSyntax.word_compare_tm, arity = 2,
     replay_head = wordsSyntax.word_compare_tm,
     unfolding = wordsTheory.word_compare_def},
    {emitted_head = int_ediv_tm, arity = 2,
     replay_head = Term.prim_mk_const
       {Thy = "HolSmt", Name = "smt_ediv_total"},
     unfolding = HolSmtTheory.smt_ediv_total_compute},
    {emitted_head = int_emod_tm, arity = 2,
     replay_head = Term.prim_mk_const
       {Thy = "HolSmt", Name = "smt_emod_total"},
     unfolding = HolSmtTheory.smt_emod_total_compute}
  ]

  fun definition_for_record record =
    let
      fun matches ({emitted_head, arity, ...} : emitted_definition_spec) =
        case record of
          EncodedSymbol {hol_term, arity = emitted_arity, ...} =>
            arity = emitted_arity andalso
            Term.same_const emitted_head hol_term
        | _ => false
      fun attach ({replay_head, unfolding, ...} : emitted_definition_spec) =
        EmittedDefinition {emitted_symbol = record,
          replay_head = replay_head, unfolding = unfolding}
    in
      case List.filter matches emitted_definition_specs of
        [] => NONE
      | [spec] => SOME (attach spec)
      | _ => raise ERR "definition_for_record"
          "duplicate emitted-definition registry entry"
    end

  fun emitted_definitions_for_records records =
    List.mapPartial definition_for_record records

  fun translation_definitions translation =
    emitted_definitions_for_records (translation_records translation)

  fun emitted_definition_key (EmittedDefinition {emitted_symbol, ...}) =
    emitted_symbol
  fun emitted_definition_head (EmittedDefinition {replay_head, ...}) =
    replay_head
  fun emitted_definition_theorem (EmittedDefinition {unfolding, ...}) =
    unfolding

  (* TASK_12's completeness audit may inspect the closed registry, but replay
     must use [translation_definitions] so an absent per-run emission cannot
     enable an unfolding. *)
  fun all_emitted_definition_specs () = emitted_definition_specs

  fun translation_dicts ({tydict, tmdict, ...} : translation) = (tydict, tmdict)
  val parser_dicts_for_translation = parser_dicts_for_translation_aux NONE
  fun parser_dicts_for_solver_translation solver =
    parser_dicts_for_translation_aux (SOME solver)
  fun infer_logic_from_features features =
    infer_logic_from_features_for_regime FirstOrder features
  val infer_logic_from_features_with_regime =
    infer_logic_from_features_for_regime
  val goal_requires_ho = goal_requires_ho_aux
  fun regime_for_goal dialect goal =
    select_regime (AutomaticRegime dialect) goal

  fun option_logic_policy logic
      ({features, inferred_logic, reason} : {
        features : logic_features, inferred_logic : string, reason : string}) =
    case logic of
      NONE => NONE
    | SOME selected_logic =>
        SOME {logic = selected_logic, reason = "caller override"}

  type smtlib_emit_options = {
    request : regime_request,
    apply_operator : standard27_apply_operator,
    policy : logic_selection_policy,
    get_proof : bool,
    target : {solver : string, version : string option} option
  }

  fun reject_reglan_hol_equalities (assumptions, conclusion) =
    let
      fun children term pending =
        if Term.is_comb term then
          let val (operator, operand) = Term.dest_comb term
          in operator :: operand :: pending end
        else if Term.is_abs term then
          Lib.snd (Term.dest_abs term) :: pending
        else pending
      fun visit _ [] = ()
        | visit seen (term :: pending) =
            if HOLset.member (seen, term) then visit seen pending
            else
              let
                val seen = HOLset.add (seen, term)
                val (head, arguments) = boolSyntax.strip_comb term
                val _ =
                  case arguments of
                    left :: _ =>
                      if same_const head boolSyntax.equality andalso
                         same_type (Term.type_of left, reglan_ty) then
                        raise ERR "reject_reglan_hol_equalities"
                          ("HOL equality on smtstring$reglan is intensional; " ^
                           "SMT-LIB RegLan equality is language equivalence")
                      else ()
                  | [] => ()
              in
                visit seen (children term pending)
              end
    in
      visit (HOLset.empty Term.compare) (conclusion :: assumptions)
    end

  fun goal_to_SmtLib_translation_gen
      ({request, apply_operator, policy, get_proof, target} : smtlib_emit_options)
      goal =
    let
      val _ = reject_reglan_hol_equalities goal
      val tail =
        if get_proof then ["(get-proof)\n", "(exit)\n"] else ["(exit)\n"]
    in
      Lib.apsnd (fn xs => xs @ tail)
        (goal_to_SmtLib_aux request apply_operator policy target
           true goal)
    end

  fun goal_to_SmtLib_gen opts goal =
    Lib.apfst translation_dicts
      (goal_to_SmtLib_translation_gen opts goal)

  local

    (* Generic callers emit for the automatic Standard27 regime, with the `_`
       apply spelling used by our parser and corpus, no logic override and no
       proof request.  Each entry point below is these defaults plus the
       overrides it names, so a newly added option cannot be forgotten in all
       but one of them. *)
    val default_emit_options : smtlib_emit_options = {
      request = AutomaticRegime Standard27,
      apply_operator = ApplyUnderscore,
      policy = option_logic_policy NONE,
      get_proof = false,
      target = NONE
    }

    fun with_request request ({apply_operator, policy, get_proof, target, ...}
        : smtlib_emit_options) : smtlib_emit_options =
      {request = request, apply_operator = apply_operator, policy = policy,
       get_proof = get_proof, target = target}

    fun with_apply_operator apply_operator ({request, policy, get_proof, target, ...}
        : smtlib_emit_options) : smtlib_emit_options =
      {request = request, apply_operator = apply_operator, policy = policy,
       get_proof = get_proof, target = target}

    fun with_policy policy ({request, apply_operator, get_proof, target, ...}
        : smtlib_emit_options) : smtlib_emit_options =
      {request = request, apply_operator = apply_operator, policy = policy,
       get_proof = get_proof, target = target}

    fun with_get_proof get_proof ({request, apply_operator, policy, target, ...}
        : smtlib_emit_options) : smtlib_emit_options =
      {request = request, apply_operator = apply_operator, policy = policy,
       get_proof = get_proof, target = target}

    fun with_target target ({request, apply_operator, policy, get_proof, ...}
        : smtlib_emit_options) : smtlib_emit_options =
      {request = request, apply_operator = apply_operator, policy = policy,
       get_proof = get_proof, target = target}

    fun emit_options overrides =
      List.foldl (fn (override, opts) => override opts) default_emit_options
        overrides

  in

    (* A solver boundary that pins every emission dimension.  It takes a
       dialect rather than a full regime request: overriding the regime and
       asking for a proof are not combinations any boundary needs. *)
    fun goal_to_SmtLib_translation_for_solver
        {policy, dialect, apply_operator, get_proof, target} goal =
      let
        val _ =
          case target of
            NONE => ()
          | SOME solver_target =>
              if native_sequence_goal goal then
                check_goal_operator_availability solver_target goal
              else
                check_goal_operator_availability_unless
                  (fn head => List.exists (fn sequence_head =>
                    Term.same_const head sequence_head
                    handle Feedback.HOL_ERR _ => false)
                    [smt_seq_update_tm, smt_seq_replace_all_tm, seq_lupdate_tm,
                     seq_reverse_tm, seq_map_tm, seq_foldl_tm])
                  solver_target goal
      in
        goal_to_SmtLib_translation_gen
          (emit_options [with_request (AutomaticRegime dialect),
                         with_apply_operator apply_operator,
                         with_policy policy, with_get_proof get_proof,
                         with_target target]) goal
      end

    fun goal_to_SmtLib_translation_with_policy_and_dialect policy dialect =
      goal_to_SmtLib_translation_gen
        (emit_options [with_request (AutomaticRegime dialect),
                       with_policy policy])

    fun goal_to_SmtLib_translation_with_regime_and_apply_operator
        regime apply_operator logic =
      goal_to_SmtLib_translation_gen
        (emit_options [with_request (RegimeOverride regime),
                       with_apply_operator apply_operator,
                       with_policy (option_logic_policy logic)])

    fun goal_to_SmtLib_translation_with_regime regime logic =
      goal_to_SmtLib_translation_gen
        (emit_options [with_request (RegimeOverride regime),
                       with_policy (option_logic_policy logic)])

    fun goal_to_SmtLib_translation_with_dialect dialect logic =
      goal_to_SmtLib_translation_gen
        (emit_options [with_request (AutomaticRegime dialect),
                       with_policy (option_logic_policy logic)])

    fun goal_to_SmtLib_translation logic =
      goal_to_SmtLib_translation_gen
        (emit_options [with_policy (option_logic_policy logic)])

    fun goal_to_SmtLib_with_get_proof_translation_with_policy_and_dialect
        policy dialect =
      goal_to_SmtLib_translation_gen
        (emit_options [with_request (AutomaticRegime dialect),
                       with_policy policy, with_get_proof true])

    fun goal_to_SmtLib_with_get_proof_translation logic =
      goal_to_SmtLib_translation_gen
        (emit_options [with_policy (option_logic_policy logic),
                       with_get_proof true])

    fun goal_to_SmtLib logic =
      goal_to_SmtLib_gen
        (emit_options [with_policy (option_logic_policy logic)])

  end  (* local *)

  (* cvc5 alone supplies finite-set cardinality.  Keep this at the solver
     boundary rather than in the printer so every Z3 entry point gets the
     same structured availability diagnostic before serialization begins. *)
  val _ = register_operator_availability {
    hol_head = pred_setSyntax.card_tm, operator = "set.card", solver = "cvc5",
    versions = ["1.3.4"]
  }

  val _ = register_operator_availability {
    hol_head = bagSyntax.BAG_CARD_tm, operator = "bag.card", solver = "cvc5",
    versions = ["1.3.4"]
  }

  (* These spellings are cvc5-only even though the rest of the first-order
     Seq surface is shared.  Check them at the solver boundary, before any
     serializer can accidentally emit a Z3-rejected operator. *)
  val _ = register_operator_availability {
    hol_head = smt_seq_update_tm, operator = "seq.update", solver = "cvc5",
    versions = ["1.3.4"]
  }

  val _ = register_operator_availability {
    hol_head = smt_seq_replace_all_tm, operator = "seq.replace_all",
    solver = "cvc5", versions = ["1.3.4"]
  }

  val _ = register_operator_availability {
    hol_head = seq_lupdate_tm, operator = "seq.update", solver = "cvc5",
    versions = ["1.3.4"]
  }

  val _ = register_operator_availability {
    hol_head = seq_reverse_tm, operator = "seq.rev", solver = "cvc5",
    versions = ["1.3.4"]
  }

  val _ = register_operator_availability {
    hol_head = smtstr_update_tm, operator = "str.update", solver = "cvc5",
    versions = ["1.3.4"]
  }

  val _ = register_operator_availability {
    hol_head = smtstr_rev_tm, operator = "str.rev", solver = "cvc5",
    versions = ["1.3.4"]
  }

  (* Z3 accepts these higher-order Seq combinators at every supported anchor;
     cvc5 accepts neither.  The printer deliberately uses only `seq.foldl`:
     `seq.fold_left` is a version-gated parser alias, never an output name. *)
  val z3_seq_ho_versions = ["4.11.2", "4.12.4", "4.13.0", "4.14.1",
                            "4.15.3", "4.16.0"]

  val _ = register_operator_availability {
    hol_head = seq_map_tm, operator = "seq.map", solver = "Z3",
    versions = z3_seq_ho_versions
  }

  val _ = register_operator_availability {
    hol_head = seq_foldl_tm, operator = "seq.foldl", solver = "Z3",
    versions = z3_seq_ho_versions
  }

  val NUM_TO_INT_CONV = NUM_TO_INT_CONV
  val NUM_BINDERS_TO_INT_CONV = NUM_BINDERS_TO_INT_CONV
  val HOL_STRING_TO_SMT_CONV = HOL_STRING_TO_SMT_CONV
  val NATIVE_FLOAT_TO_SMT_CONV = NATIVE_FLOAT_TO_SMT_CONV
  val DATATYPE_TO_SMT_CONV = DATATYPE_TO_SMT_CONV
  val invented_uf_native_datatype_domain_diagnostic =
    invented_uf_native_datatype_domain_diagnostic
  val uninterpreted_native_datatype_destructor_diagnostic =
    uninterpreted_native_datatype_destructor_diagnostic
  val unsupported_smtfloat_constant_diagnostic =
    unsupported_smtfloat_constant_diagnostic
  val smtfloat_opaque_replay_constants_for_test =
    Redblackset.listItems smtfloat_opaque_replay_constants
  val reject_unsupported_smtfloat_constant_for_test =
    reject_unsupported_smtfloat_constant
  fun datatype_destructor_theorems_for_test ty =
    case TypeBase.fetch ty of
      SOME tyinfo => TypeBasePure.destructors_of tyinfo
    | NONE => []
  val datatype_destructor_head_for_test = datatype_destructor_head
  val datatype_destructor_case_for_test = datatype_destructor_case
  val recognize_datatype_destructor_for_test = recognize_datatype_destructor
  val datatype_destructor_normalize_conv_for_test =
    datatype_destructor_normalize_conv
  val datatype_destructor_normalize_conv_with_for_test =
    datatype_destructor_normalize_conv_with
  val datatype_constructors_for_test = datatype_constructors
  val datatype_selector_term_for_test = datatype_selector_term
  val datatype_case_normal_form_for_test = datatype_case_normal_form
  val datatype_constructor_case_reduce_conv_with_for_test =
    datatype_constructor_case_reduce_conv_with
  val datatype_case_branch_eta_conv_with_for_test =
    datatype_case_branch_eta_conv_with
  val datatype_case_branch_eta_conv_for_test =
    datatype_case_branch_eta_conv
  val closed_constructor_destructor_residual_for_test =
    closed_constructor_destructor_residual
  val reject_uninterpreted_native_destructors_for_test =
    reject_uninterpreted_native_destructors
  val native_float_guarded_context_match_conv_with_for_test =
    native_float_guarded_context_match_conv_with
  val native_float_guarded_postorder_conv_for_test =
    native_float_guarded_postorder_conv
  val native_float_transfer_surface = native_float_transfer_surface
  val native_float_transfer_theorems = native_float_transfer_theorems

  fun type_mentions_num ty =
    Type.compare (ty, numSyntax.num) = EQUAL orelse
    (case Lib.total Type.dom_rng ty of
       SOME (dom, rng) => type_mentions_num dom orelse type_mentions_num rng
     | NONE => false)

  fun is_num_transfer_const tm =
    if not (Term.is_const tm) orelse not (type_mentions_num (Term.type_of tm))
    then false
    else
      case Lib.total Term.dest_thy_const tm of
        SOME {Thy = "arithmetic", Name, ...} =>
          List.exists (fn n => n = Name)
            ["*", "+", "-", "<=", ">", ">=", "DIV", "EXP", "MAX", "MIN",
             "MOD"]
      | SOME {Thy = "num", Name = "SUC", ...} => true
      | SOME {Thy = "integer", Name = "int_exp", ...} => true
      | SOME {Thy = "prim_rec", Name = "<", ...} => true
      | SOME {Thy = "integer", Name = "Num", ...} => true
      | SOME {Thy = "integer", Name = "int_of_num", ...} => true
      | SOME {Thy = "realax", Name = "NUM_FLOOR", ...} => true
      | SOME {Thy = "realax", Name = "NUM_CEILING", ...} => true
      | SOME {Thy = "pred_set", Name = "CARD", ...} => true
      | SOME {Thy = "bag", Name = "BAG_CARD", ...} => true
      | _ => false

  fun atom_needs_num_transfer atom =
    (Term.is_var atom andalso type_mentions_num (Term.type_of atom)) orelse
    is_num_transfer_const atom

  fun term_is_num tm =
    Type.compare (Term.type_of tm, numSyntax.num) = EQUAL

  (* True when a natural in `tm` meets the word theory, in either of the two
     ways the transfer cannot follow: as an argument of a word symbol, because
     `word_extract` and friends require indices that stay literal numerals
     (see `builtin_symbols`) whereas the transfer rewrites them into `Num`
     applications; or as a natural computed from a word, such as `w2n w`, for
     which there is no transferred counterpart.  Naturals and words that never
     meet -- a goal reasoning about both independently -- are unaffected, and
     their naturals still transfer. *)
  fun num_meets_word tm =
    let
      (* LENGTH is transferred as an integer coercion around the whole list;
         word elements beneath it are not word-theory operands or indices. *)
      fun word_below_num tm =
        let val (rator, rands) = boolSyntax.strip_comb tm in
          if same_const rator seq_length_tm then false
          else type_contains_word (Term.type_of tm) orelse
            List.exists word_below_num rands
        end
        handle Feedback.HOL_ERR _ => type_contains_word (Term.type_of tm)
    in
    (term_is_num tm andalso word_below_num tm)
    orelse
    let
      val (rator, rands) = boolSyntax.strip_comb tm
    in
      type_contains_word (Term.type_of rator) andalso
      List.exists term_is_num rands
    end
    end

  fun goal_entangles_num_and_word (asms, concl) =
    List.exists num_meets_word
      (List.concat (List.map subterms (concl :: asms)))

  fun goal_mentions_num (asms, concl) =
  let
    val atoms = Term.all_atomsl (concl :: asms) Term.empty_tmset
  in
    HOLset.foldl (fn (atom, seen) => seen orelse atom_needs_num_transfer atom)
      false atoms
  end

  (* STRIP_ALL_THEN minus DISJ_CASES_THEN: flattens conjunctions and
     skolemizes existentials but never case-splits, because preprocessing
     must produce at most one subgoal (SolverSpec.simplify). *)
  val NO_SPLIT_STRIP_ASSUME_TAC =
    Thm_cont.REPEAT_TCL
      (Thm_cont.ORELSE_TCL (Thm_cont.CONJUNCTS_THEN, Thm_cont.CHOOSE_THEN))
      (fn th =>
        Tactical.FIRST [Tactic.CONTR_TAC th, Tactic.ACCEPT_TAC th,
                        Tactic.ASSUME_TAC th])

  fun NO_SPLIT_STRIP_ASSUMS_TAC g =
    Tactical.MAP_EVERY (fn _ => Tactical.POP_ASSUM NO_SPLIT_STRIP_ASSUME_TAC)
      (#1 g) g

  (* Runs the proved num-to-int transfer on the whole goal.  Assumptions are
     first moved into the conclusion so free num variables anywhere in the
     sequent are made explicit and get a non-negativity guard. *)
  fun NUM_TO_INT_TAC_EXCEPT exclude g =
  let
    open Tactic Tactical
    val undisch_assums = MAP_EVERY UNDISCH_TAC (#1 g)
  in
    if goal_mentions_num g andalso not (goal_entangles_num_and_word g) then
      (undisch_assums THEN
       SPEC_NUM_FREE_VARS_TAC_EXCEPT exclude THEN
       CONV_TAC NUM_TO_INT_CONV THEN
       REPEAT (GEN_TAC ORELSE DISCH_TAC) THEN
       (* The STRIP_ASSUME_TAC re-introduction inside REV_FULL_SIMP_TAC
          would case-split disjunctive assumptions into several subgoals. *)
       simpLib.NO_STRIP_REV_FULL_SIMP_TAC pureSimps.pure_ss
         num_transfer_rewrites THEN
       NO_SPLIT_STRIP_ASSUMS_TAC) g
    else
      ALL_TAC g
  end

  val NUM_TO_INT_TAC = NUM_TO_INT_TAC_EXCEPT (fn _ => false)

  (* Relativizes num-typed binders to guarded int-typed binders. *)
  val NUM_BINDERS_TO_INT_TAC =
  let
    open Tactic Tactical
  in
    RULE_ASSUM_TAC (Conv.CONV_RULE NUM_BINDERS_TO_INT_CONV) THEN
    CONV_TAC NUM_BINDERS_TO_INT_CONV
  end

  val HOL_STRING_TO_SMT_TAC =
    Tactical.THEN
      (Tactic.RULE_ASSUM_TAC (Conv.CONV_RULE HOL_STRING_TO_SMT_CONV),
       Tactic.CONV_TAC HOL_STRING_TO_SMT_CONV)

  val NATIVE_FLOAT_TO_SMT_TAC =
    Tactical.THEN
      (Tactic.RULE_ASSUM_TAC (Conv.CONV_RULE NATIVE_FLOAT_TO_SMT_CONV),
       Tactic.CONV_TAC NATIVE_FLOAT_TO_SMT_CONV)

  val DATATYPE_TO_SMT_TAC =
    Tactical.THEN
      (Tactic.RULE_ASSUM_TAC (Conv.CONV_RULE DATATYPE_TO_SMT_CONV),
       Tactic.CONV_TAC DATATYPE_TO_SMT_CONV)

  (* This tactic calls ASSUME_TAC on theorems that are deemed necessary for SMT
     solvers to solve the goal (but only if `include_theorems` is true) *)
  fun ADD_THEOREMS_TAC g =
  let
    val (asms, concl) = g
    val goal_terms = concl :: asms

    val thms_to_add =
      if !include_theorems then
        get_thms (goal_terms, empty_thmset)
      else
        []

    val tactic = Tactical.MAP_EVERY Tactic.ASSUME_TAC thms_to_add
  in
    tactic g
  end

  (* ADD_THEOREMS_TAC contributes global definition theorems as assumptions.
     Simplify each one in isolation afterwards: this removes definitions that
     have become reflexive after the semantic num-to-int transfer, without
     treating the assumptions themselves as rewrite rules. *)
  fun CLEANUP_ASSUMPTIONS_TAC g =
  let
    open Tactic Tactical
    val assumptions = #1 g
    fun is_true tm =
      Term.aconv tm boolSyntax.T orelse
      (let val (_, body) = boolSyntax.dest_forall tm
       in is_true body end
       handle Feedback.HOL_ERR _ => false)
    fun cleanup thm =
    let
      val thm = simpLib.SIMP_RULE pureSimps.pure_ss
        (boolTheory.REFL_CLAUSE :: num_transfer_rewrites) thm
    in
      if is_true (Thm.concl thm) then
        ALL_TAC
      else
        ASSUME_TAC thm
    end
    val cleanup_one = POP_ASSUM cleanup
  in
    MAP_EVERY (fn _ => cleanup_one) assumptions g
  end

  fun has_set_complement tm =
    List.exists (fn subterm =>
      Option.isSome (Lib.total pred_setSyntax.dest_compl subterm))
      (Library.subterms tm)

  (* Checked CARD needs its operands intact, while unrelated set atoms must
     still lower to predicates. Native-by-default mode only lowers operands
     outside the printer's native grammar. *)
  fun set_atom_needs_predicate_expansion expand_native tm =
  let
    val (rator, rands) = boolSyntax.strip_comb tm
    fun unsupported set = is_set_type set andalso
      (not (native_set_term set) orelse
       (expand_native andalso not (has_set_complement tm)))
  in
    if same_const rator pred_setSyntax.in_tm then
      (case rands of [_, set] => unsupported set | _ => false)
    else if same_const rator pred_setSyntax.subset_tm then
      (case rands of [left, right] => unsupported left orelse unsupported right
       | _ => false)
    else if same_const rator boolSyntax.equality then
      (case rands of [left, right] =>
         is_set_type left andalso is_set_type right andalso
         (unsupported left orelse unsupported right)
       | _ => false)
    else
      false
  end

  val card_operand_cong = Thm.REFL (pred_setSyntax.mk_card
    (Term.mk_var ("card_set", pred_setSyntax.mk_set_type Type.alpha)))

  fun native_set_preprocess_conv expand_native tm =
    if set_atom_needs_predicate_expansion expand_native tm then
      simpLib.SIMP_CONV
        (simpLib.mk_simpset [pred_setSimps.SET_SPEC_ss])
        [simpLib.Cong card_operand_cong,
         pred_setTheory.SPECIFICATION, pred_setTheory.GSPEC_ETA,
         pred_setTheory.EMPTY_DEF, pred_setTheory.UNIV_DEF,
         pred_setTheory.UNION_DEF, pred_setTheory.INTER_DEF] tm
    else
      raise Conv.UNCHANGED

  val NATIVE_SET_SIMP_TAC =
    Tactic.CONV_TAC
      (Conv.TOP_DEPTH_CONV (native_set_preprocess_conv false))

  fun CHECKED_SET_SIMP_TAC preserve_native_card g =
    if preserve_native_card andalso
        List.exists contains_set_card (#1 g @ [#2 g]) then
      let val conv =
        Conv.TOP_DEPTH_CONV (native_set_preprocess_conv true)
      in
        Tactical.THEN
          (Tactic.RULE_ASSUM_TAC (Conv.CONV_RULE conv), Tactic.CONV_TAC conv) g
      end
    else if List.exists has_set_complement (#1 g @ [#2 g]) then
      NATIVE_SET_SIMP_TAC g
    else
      Library.SET_SIMP_TAC g

  (* Preserve equality on native collections.  FUN_EQ_THM would turn it into
     a predicate equality before collection discovery can select Set or Bag. *)
  fun fun_eq_preprocess_conv preserve_native_collections tm =
    let
      val (left, right) = boolSyntax.dest_eq tm
      val collection_equality =
        (is_set_type left andalso is_set_type right) orelse
        (is_bag_type left andalso is_bag_type right)
    in
      if preserve_native_collections andalso collection_equality then
        raise Conv.UNCHANGED
      else
        Conv.REWR_CONV boolTheory.FUN_EQ_THM tm
    end
    handle Feedback.HOL_ERR _ => raise Conv.UNCHANGED

  fun cvc_native_bag_goal goal =
  let
    val bag_terms = List.foldl
      (fn (term, terms) => collect_native_bag_terms term terms) []
      (Lib.fst goal @ [Lib.snd goal])
  in
    cvc5_native_bags goal bag_terms
  end

  (* Eliminates some HOL terms that are not supported by the SMT-LIB
     translation. It also adds some useful theorems to the list of assumptions
     so that SMT solvers can reason about some symbols defined in HOL4 theories. *)
  (* Every preprocessing stage must keep the goal in at most one subgoal
     (SolverSpec.simplify consumes a single goal); name the stage that
     splits, instead of failing opaquely far from the cause. *)
  fun one_subgoal_stage name (tac : Tactical.tactic) : Tactical.tactic =
    fn g =>
      fn c =>
        let
          val (goals, validation) = tac g c
        in
          if List.length goals > 1 then
            raise Feedback.mk_HOL_ERR "SmtLib" "SIMP_TAC"
              ("preprocessing stage '" ^ name ^ "' produced " ^
               Int.toString (List.length goals) ^ " subgoals")
          else
            (goals, validation)
        end

  fun SIMP_TAC_WITH_NATIVE_BAGS preserve_native_bags simp_let =
  let
    open Tactical simpLib
    fun num_to_int g =
      if preserve_native_bags andalso cvc_native_bag_goal g then
        NUM_TO_INT_TAC_EXCEPT is_bag_type g
      else NUM_TO_INT_TAC g
    val stage = one_subgoal_stage
  in
    stage "hol-string" HOL_STRING_TO_SMT_TAC THEN
    stage "native-float" NATIVE_FLOAT_TO_SMT_TAC THEN
    (* This must precede num transfer: the native real numeral form lets the
       closed positivity proof erase the whole pow term, including its nat
       exponent. *)
    Tactic.CONV_TAC (Conv.DEPTH_CONV REAL_POW_POS_LITERAL_CONV) THEN
    (* Close algebraic natural identities while their saturated subtraction
       is still in its native form, before lowering introduces nested ites. *)
    stage "num-algebra" (SIMP_TAC pureSimps.pure_ss
      [HolSmtTheory.num_sub_assoc, HolSmtTheory.num_floor_zero,
       HolSmtTheory.num_ceiling_zero, arithmeticTheory.MAX_0,
       arithmeticTheory.MIN_0, boolTheory.REFL_CLAUSE]) THEN
    stage "num-to-int" num_to_int THEN
    stage "let-simp"
      (if simp_let then Library.LET_SIMP_TAC else ALL_TAC) THEN
    Tactic.CONV_TAC (Conv.DEPTH_CONV REAL_POW_NUMERAL_CONV) THEN
    stage "polymorphic-simp" (SIMP_TAC pureSimps.pure_ss [
      (* FIXME: polymorphic functions seem to be highly problematic at the
         moment because after HolSmt's translation, the symbols in these
         theorems (e.g. ``FST``, ``SND``, ``$,``, etc) won't be the same as the
         ones in the goal, apparently because they have different types (due to
         type instantiation). This means that currently, passing these theorems
         as facts/assumptions will be useless in most circumstances. We try to
         use these theorems in simplification here but this only helps solving
         the simpler goals. *)
      pairTheory.PAIR_EQ, pairTheory.FST, pairTheory.SND,
      combinTheory.UPDATE_APPLY1, combinTheory.APPLY_UPDATE_THM,
      combinTheory.UPDATE_EQ, boolTheory.REFL_CLAUSE,
      HolSmtTheory.ALL_DISTINCT_NIL, HolSmtTheory.ALL_DISTINCT_CONS,
      listTheory.MEM, realTheory.POW_1, realTheory.POW_2, REAL_POW_3,
      Thm.CONJUNCT1 realTheory.pow, Thm.CONJUNCT2 realTheory.pow,
      integerTheory.INT_MAX, integerTheory.INT_MIN,
      HolSmtTheory.real_div_smt_rdiv, HolSmtTheory.smt_rdiv_zero
    ]) THEN
    stage "real-div-simp" (SIMP_TAC realSimps.real_ss
      [HolSmtTheory.smt_rdiv_zero, HolSmtTheory.smt_rdiv_refl,
       HolSmtTheory.smt_rdiv_one, HolSmtTheory.smt_rdiv_neg_refl,
       HolSmtTheory.smt_rdiv_neg_one]) THEN
    stage "refl-simp" (SIMP_TAC pureSimps.pure_ss [boolTheory.REFL_CLAUSE])
      THEN
    Tactic.CONV_TAC
      (Conv.DEPTH_CONV (fun_eq_preprocess_conv preserve_native_bags)) THEN
    stage "word-simp" Library.WORD_SIMP_TAC THEN
    (* Checked set simplification normally uses the predicate encoding, but
       must retain complements: SET_SIMP_TAC lowers their membership to NOTIN,
       which does not have a native SMT Set translation. *)
    stage "set-simp"
      (if simp_let then CHECKED_SET_SIMP_TAC preserve_native_bags
       else NATIVE_SET_SIMP_TAC) THEN
    Tactic.RULE_ASSUM_TAC
      (Conv.CONV_RULE (Conv.DEPTH_CONV INT_DIVIDES_LITERAL_MOD_CONV)) THEN
    Tactic.CONV_TAC (Conv.DEPTH_CONV INT_DIVIDES_LITERAL_MOD_CONV) THEN
    Tactic.BETA_TAC THEN
    stage "num-to-int" num_to_int THEN
    stage "add-theorems" ADD_THEOREMS_TAC THEN
    stage "cleanup-assumptions" CLEANUP_ASSUMPTIONS_TAC THEN
    (* The theorem-discovery pass may expose a fresh num-valued occurrence.
       Run the semantic transfer last, then simplify its newly-added
       assumptions even when they no longer mention num themselves. *)
    stage "num-to-int" num_to_int THEN
    stage "cleanup-assumptions" CLEANUP_ASSUMPTIONS_TAC THEN
    stage "datatype-to-smt" DATATYPE_TO_SMT_TAC
  end

  fun SIMP_TAC simp_let = SIMP_TAC_WITH_NATIVE_BAGS false simp_let
  fun CVC_SIMP_TAC simp_let = SIMP_TAC_WITH_NATIVE_BAGS true simp_let

  datatype z3_roundtrip_expansion =
      Z3Inverse of Term.term
    | Z3Ceiling of Term.term
    | Z3SymbolicCons of Term.term * Term.term
    | Z3PartialRanked of Term.term * Term.term list * Type.hol_type list

  (* Recognition is proof-free.  In particular, a malformed proof below is
     never permitted to turn an admitted expansion back into UNCHANGED. *)
  fun recognize_z3_roundtrip_expansion tm =
    if realSyntax.is_inv tm then
      SOME (Z3Inverse (realSyntax.dest_inv tm))
    else if intrealSyntax.is_INT_CEILING tm then
      SOME (Z3Ceiling (intrealSyntax.dest_INT_CEILING tm))
    else if listSyntax.is_cons tm then
      let val (element, tail) = listSyntax.dest_cons tm in
        if listSyntax.is_nil tail orelse listSyntax.is_cons tail then NONE
        else SOME (Z3SymbolicCons (element, tail))
      end
    else
      let
        val (head, arguments) = boolSyntax.strip_comb tm
      in
        if not (Term.is_const head) then NONE
        else
          let
            val {Thy, Name, ...} = Term.dest_thy_const head
            val has_direct_encoding =
              Redblackset.member (builtin_const_names, (Thy, Name)) orelse
              is_native_set_head head orelse is_native_bag_head head
            val rank = declared_const_arity head
            val missing = rank - List.length arguments
            val (domains, _) = boolSyntax.strip_fun (Term.type_of tm)
          in
            if has_direct_encoding orelse TypeBase.is_constructor head orelse
               missing <= 0 orelse List.length domains <> missing then NONE
            else SOME (Z3PartialRanked (head, arguments, domains))
          end
      end

  (* The measure follows the emitter's maximal-application view.  Counting a
     rator prefix of a saturated application would incorrectly classify that
     prefix as an independently emitted partial symbol. *)
  fun z3_roundtrip_measure tm =
    let
      val contribution =
        if Option.isSome (recognize_z3_roundtrip_expansion tm) then 1 else 0
    in
      if Term.is_abs tm then
        let val (_, body) = Term.dest_abs tm
        in contribution + z3_roundtrip_measure body end
      else
        let val (_, arguments) = boolSyntax.strip_comb tm
        in contribution + List.foldl
          (fn (argument, total) => z3_roundtrip_measure argument + total)
          0 arguments
        end
    end

  fun eta_expansion_theorem function domains =
    Thm.SYM (eta_expansion_reduction
      "z3_assertion_roundtrip_conv" function domains)

  fun prove_z3_roundtrip_expansion (tm, expansion) =
    case expansion of
      Z3Inverse argument => let
        val variable = Term.genvar realSyntax.real_ty
        val totalized = boolSyntax.mk_cond
          (boolSyntax.mk_eq (variable, realSyntax.zero_tm),
           realSyntax.zero_tm,
           Term.list_mk_comb
             (smt_rdiv_tm, [realSyntax.one_tm, variable]))
        val generic = simpLib.SIMP_PROVE (bossLib.srw_ss ())
          [HolSmtTheory.smt_rinv_def, HolSmtTheory.smt_rdiv_eq_div]
          (boolSyntax.mk_forall (variable,
            boolSyntax.mk_eq (realSyntax.mk_inv variable, totalized)))
      in
        Thm.SPEC argument generic
      end
    | Z3Ceiling argument => let
        val variable = Term.genvar realSyntax.real_ty
        val lowered = intSyntax.mk_negated
          (intrealSyntax.mk_INT_FLOOR
            (realSyntax.mk_negated variable))
        val generic = simpLib.SIMP_PROVE (bossLib.srw_ss ())
          [intrealTheory.INT_FLOOR_NEG]
          (boolSyntax.mk_forall (variable,
            boolSyntax.mk_eq
              (intrealSyntax.mk_INT_CEILING variable, lowered)))
      in
        Thm.SPEC argument generic
      end
    | Z3SymbolicCons (element, tail) =>
      let
        val singleton = listSyntax.mk_list
          ([element], Term.type_of element)
        val appended = listSyntax.mk_append (singleton, tail)
        val reduction = simpLib.SIMP_PROVE (bossLib.srw_ss ())
          [listTheory.APPEND] (boolSyntax.mk_eq (appended, tm))
      in
        Thm.SYM reduction
      end
    | Z3PartialRanked (_, _, domains) =>
        eta_expansion_theorem tm domains

  (* Explicit terminating postorder/revisit traversal.  Every admitted
     expansion is checked at the same boundary, and its RHS is recursively
     normalized before the parent is retried. *)
  fun z3_assertion_roundtrip_conv_with prove tm =
  let
    fun changed theorem =
      let val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl theorem)
      in not (Term.aconv lhs rhs) end
    fun normalize input =
      let
        val children =
          if Term.is_abs input then
            let val (variable, body) = Term.dest_abs input
            in Thm.ABS variable (normalize body) end
          else
            let
              val (head, arguments) = boolSyntax.strip_comb input
              val argument_theorems = List.map normalize arguments
            in
              List.foldl (fn (argument, application) =>
                Thm.MK_COMB (application, argument))
                (Thm.REFL head) argument_theorems
            end
        val (_, current) = boolSyntax.dest_eq (Thm.concl children)
        val root =
          case recognize_z3_roundtrip_expansion current of
            NONE => Thm.REFL current
          | SOME admitted =>
              let
                val old_measure = z3_roundtrip_measure current
                val step = prove (current, admitted)
                val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl step)
                val _ = Term.aconv lhs current orelse
                  raise ERR "z3_assertion_roundtrip_conv"
                    "admitted expansion theorem has the wrong left-hand side"
                val new_measure = z3_roundtrip_measure rhs
                val _ = not (Term.aconv lhs rhs) orelse
                  raise ERR "z3_assertion_roundtrip_conv"
                    "admitted expansion theorem is alpha-unchanged"
                val _ = new_measure < old_measure orelse
                  raise ERR "z3_assertion_roundtrip_conv"
                    ("admitted expansion did not decrease the measure: " ^
                     Int.toString old_measure ^ " -> " ^
                     Int.toString new_measure)
              in
                Thm.TRANS step (normalize rhs)
              end
      in
        if changed children then Thm.TRANS children root else root
      end
  in
    normalize tm
  end

  val z3_assertion_roundtrip_total_conv =
    z3_assertion_roundtrip_conv_with prove_z3_roundtrip_expansion

  fun z3_assertion_roundtrip_conv tm =
    let val theorem = z3_assertion_roundtrip_total_conv tm in
      if let val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl theorem)
         in Term.aconv lhs rhs end then raise Conv.UNCHANGED
      else theorem
    end

  val Z3_ASSERTION_TO_SMT_TAC =
    Tactical.THEN
      (Tactic.RULE_ASSUM_TAC
        (Conv.CONV_RULE z3_assertion_roundtrip_total_conv),
       Tactic.CONV_TAC z3_assertion_roundtrip_total_conv)

  fun Z3_SIMP_TAC simp_let =
    Tactical.THEN (SIMP_TAC simp_let, Z3_ASSERTION_TO_SMT_TAC)

  val z3_assertion_roundtrip_conv_for_test =
    z3_assertion_roundtrip_conv
  val z3_assertion_roundtrip_conv_with_for_test =
    z3_assertion_roundtrip_conv_with

  (* Kept public for Unittest's outbound-scope audit. *)
  val builtin_encoding_for_test = builtin_encoding

  (* Kept public for Unittest's replay-table completeness audit. *)
  val native_set_operator_names_for_test = native_set_operator_names
  val native_bag_operator_names_for_test = native_bag_operator_names
end  (* local *)

end
