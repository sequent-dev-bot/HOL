(* Parsing cvc5's native CPC proof scripts. *)

structure CPC_ProofParser =
struct

local
  open CPC_Proof

  val ERR = Feedback.mk_HOL_ERR "CPC_ProofParser"

  type dicts = SmtLib_Parser.dicts

  val term_intern_bucket_count = 4093
  val cpc_term_intern = ref
    (Array.array (term_intern_bucket_count, [] : Term.term list))

  fun term_intern_hash term =
    let
      fun string_hash string =
        let
          fun loop index hash =
            if index = String.size string then hash
            else loop (index + 1)
              ((hash * 33 + Char.ord (String.sub (string, index))) mod
               term_intern_bucket_count)
        in loop 0 5381 end
      fun head_hash tm =
        if Term.is_var tm then string_hash (#1 (Term.dest_var tm))
        else if Term.is_const tm then
          string_hash (#Name (Term.dest_thy_const tm))
        else if Term.is_comb tm then 17
        else if Term.is_abs tm then 19
        else 23
      fun bounded 0 tm = head_hash tm
        | bounded depth tm =
            if Term.is_comb tm then
              let val (operator, operand) = Term.dest_comb tm in
                (bounded (depth - 1) operator * 37 +
                 bounded (depth - 1) operand * 17 + 3) mod
                  term_intern_bucket_count
              end
            else if Term.is_abs tm then
              let val (_, body) = Term.dest_abs tm in
                (bounded (depth - 1) body * 41 + 5) mod
                  term_intern_bucket_count
              end
            else head_hash tm
    in bounded 6 term end

  fun intern_cpc_term term =
    let
      (* Compound candidates are interned bottom-up.  Structural equality of
         such candidates is therefore pointer equality of their canonical
         children; avoid repeatedly alpha-comparing the full shared DAG. *)
      fun same_candidate saved candidate =
        Portable.pointer_eq (saved, candidate) orelse
        if Term.is_comb saved andalso Term.is_comb candidate then
          let
            val (saved_operator, saved_operand) = Term.dest_comb saved
            val (operator, operand) = Term.dest_comb candidate
          in
            Portable.pointer_eq (saved_operator, operator) andalso
            Portable.pointer_eq (saved_operand, operand)
          end
        else if Term.is_var saved andalso Term.is_var candidate then
          let
            val (saved_name, saved_type) = Term.dest_var saved
            val (name, ty) = Term.dest_var candidate
          in
            saved_name = name andalso Type.compare (saved_type, ty) = EQUAL
          end
        else if Term.is_const saved andalso Term.is_const candidate then
          Term.same_const saved candidate andalso
          Type.compare (Term.type_of saved, Term.type_of candidate) = EQUAL
        else Term.is_abs saved andalso Term.is_abs candidate andalso
          Term.aconv saved candidate
      fun lookup bucket candidate = List.find
        (fn saved => same_candidate saved candidate)
        (Array.sub (!cpc_term_intern, bucket))
      fun insert bucket candidate =
        let
          val entries = Array.sub (!cpc_term_intern, bucket)
        in
          Array.update (!cpc_term_intern, bucket, candidate :: entries);
          candidate
        end
      fun intern candidate =
        let val bucket = term_intern_hash candidate in
          case List.find (fn saved => Portable.pointer_eq (saved, candidate))
              (Array.sub (!cpc_term_intern, bucket)) of
            SOME saved => saved
          | NONE =>
            if Term.is_comb candidate then
              let
                val (operator, operand) = Term.dest_comb candidate
                val operator' = intern operator
                val operand' = intern operand
                val rebuilt =
                  if Portable.pointer_eq (operator, operator') andalso
                     Portable.pointer_eq (operand, operand') then candidate
                  else Term.mk_comb (operator', operand')
                (* Compute a candidate's hash once for both lookup and
                   insertion; child canonicalization needs a new hash only
                   when it actually rebuilt the candidate. *)
                val rebuilt_bucket =
                  if Portable.pointer_eq (candidate, rebuilt) then bucket
                  else term_intern_hash rebuilt
              in
                case lookup rebuilt_bucket rebuilt of
                  SOME saved => saved
                | NONE => insert rebuilt_bucket rebuilt
              end
            else
              case lookup bucket candidate of
                SOME saved => saved
              | NONE => insert bucket candidate
        end
    in intern term end

  fun intern_located ({term, provenance} : located_term) =
    {term = intern_cpc_term term, provenance = provenance}

  (* @list is CPC's compact representation for a list of binders or
     resolution annotations.  It is not an SMT-LIB term, so retain only the
     binder-list payload needed when it is referenced by a later quantifier. *)
  val cpc_list_definitions = ref (Redblackmap.mkDict String.compare)
  val cpc_list_names = ref ([] : string list)

  (* Definitions are syntax aliases.  Keep their exact occurrence tree so an
     alias use retains CPC's operand boundaries without consulting HOL-term
     identity.  This dictionary is used only while parsing the current proof;
     every command receives its own copied provenance value. *)
  val cpc_term_provenances = ref
    (Redblackmap.mkDict String.compare :
      (string, term_provenance) Redblackmap.dict)

  (* HOL represents a flat source forall block and the corresponding nested
     source foralls by the same term.  Record every parsed source occurrence
     by alpha-equivalent semantic term, retaining every distinct immediate
     block size.  A term with more than one size is deliberately ambiguous:
     the term-only parameterized-skolem callback must then fail closed. *)
  val cpc_forall_blocks = ref
    ([] : (Term.term * int list) list)

  fun add_distinct_int value values =
    if List.exists (Lib.equal value) values then values else value :: values

  fun record_forall_block (term, size) =
    let
      fun record [] = [(term, [size])]
        | record ((candidate, sizes) :: rest) =
            if Term.aconv candidate term then
              (candidate, add_distinct_int size sizes) :: rest
            else (candidate, sizes) :: record rest
    in
      cpc_forall_blocks := record (!cpc_forall_blocks)
    end

  fun record_cpc_binder_block (name, size, term) =
    if name = "forall" then record_forall_block (term, size) else ()

  (* Quoting is lexical for ordinary user symbols, but quoted spellings of
     syntax and baseline theory names denote separate user symbols.  Keep the
     baseline, source/query, and proof-declaration provenances separate.
     Thus a proof cannot shadow a builtin or duplicate its own declaration. *)
  val cpc_reserved_symbols = ref (HOLset.empty String.compare)
  val cpc_source_term_symbols = ref (HOLset.empty String.compare)
  val cpc_source_sort_symbols = ref (HOLset.empty String.compare)
  val cpc_proof_term_symbols = ref (HOLset.empty String.compare)
  val cpc_proof_sort_symbols = ref (HOLset.empty String.compare)

  fun set_member set item = HOLset.member (set, item)

  fun quoted_symbol_key token =
    case SmtLib_Parser.proof_quoted_symbol_token token of
      SOME name =>
        if set_member (!cpc_reserved_symbols) name then token else name
    | NONE => token

  (* Provenance follows the same semantic key as term elaboration.  In
     particular, an ordinary user symbol has one entry whether cvc5 prints
     it as [foo] or [|foo|]. *)
  fun provenance_key name = quoted_symbol_key name

  fun add_term_provenance name provenance =
    cpc_term_provenances := Redblackmap.insert
      (!cpc_term_provenances, provenance_key name, provenance)

  fun lookup_term_provenance name =
    SOME (Redblackmap.find (!cpc_term_provenances, provenance_key name))
    handle Redblackmap.NotFound => NONE

  fun add_cpc_list name terms =
    let val key = provenance_key name in
      cpc_list_definitions := Redblackmap.insert
        (!cpc_list_definitions, key, terms);
      cpc_list_names := key :: !cpc_list_names
    end

  fun lookup_cpc_list name =
    SOME (Redblackmap.find
      (!cpc_list_definitions, provenance_key name))
    handle Redblackmap.NotFound => NONE

  val cpc_cfg : SmtLib_Parser.parser_cfg = {
    mk_let_bindings = SmtLib_Parser.smtlib_mk_let_bindings,
    mk_let = SmtLib_Parser.smtlib_mk_let,
    mk_bound_var = Term.mk_var,
    lookup_binder_list = lookup_cpc_list,
    record_binder_block = record_cpc_binder_block,
    symbol_key = quoted_symbol_key,
    type_symbol_key = quoted_symbol_key,
    parse_choice = false,
    parse_lambda = true
  }

  fun cpc_symbol_key where_ token =
    case SmtLib_Parser.proof_string_token token of
      SOME _ => raise ERR where_ "string literal used as a symbol"
    | NONE => quoted_symbol_key token

  fun cpc_semantic_token token =
    case SmtLib_Parser.proof_string_token token of
      SOME _ => token
    | NONE => quoted_symbol_key token

  fun cpc_get_token get_token () = cpc_semantic_token (get_token ())

  fun parse_cpc_type get_token tydict =
    SmtLib_Parser.parse_type (cpc_get_token get_token) tydict

  fun parse_cpc_type_list get_token tydict =
    SmtLib_Parser.parse_type_list (cpc_get_token get_token) tydict

  fun cpc_symbol_name where_ token =
    SmtLib_Parser.proof_symbol_text (cpc_symbol_key where_ token)

  fun cpc_id_initial c =
    ((#"a" <= c andalso c <= #"z") orelse
     (#"A" <= c andalso c <= #"Z")) orelse
    List.exists (Lib.equal c)
      [#"~", #"!", #"@", #"$", #"%", #"^", #"&", #"*", #"_",
       #"-", #"+", #"=", #"<", #">", #".", #"?", #"/"]

  fun cpc_simple_symbol text =
    String.size text > 0 andalso
    cpc_id_initial (String.sub (text, 0)) andalso
    List.all (fn c => cpc_id_initial c orelse Char.isDigit c)
      (String.explode text)

  (* CPC command and premise IDs use the @-prefixed identifier production,
     not the wider atom production and never the String-token production.
     Apply the ordinary symbol key only after checking the original token
     kind and spelling.  Thus [@p] and [|@p|] share a key unless [@p] is a
     reserved symbol, whose quoted spelling remains a distinct symbol. *)
  fun cpc_id_key where_ description token =
    case SmtLib_Parser.proof_string_token token of
      SOME _ => raise ERR where_
        ("string literal is not a valid CPC " ^ description)
    | NONE =>
        let val text = SmtLib_Parser.proof_symbol_text token in
          if cpc_simple_symbol text andalso String.size text > 1 andalso
             String.sub (text, 0) = #"@"
          then quoted_symbol_key token
          else raise ERR where_
            ("invalid CPC " ^ description ^ " '" ^ text ^ "'")
        end

  (* cvc5's @var production is the one CPC context whose name is serialized
     as an SMT-LIB String token.  Decode it to the corresponding HOL name;
     no ordinary identifier position receives this exception. *)
  fun cpc_var_name token =
    case SmtLib_Parser.proof_string_token token of
      SOME name => name
    | NONE => SmtLib_Parser.proof_symbol_text token

  fun add_term (dicts_ref : dicts ref) name tm =
    let
      val (tydict, tmdict) = !dicts_ref
      val tmdict = Library.extend_dict ((name,
        SmtLib_Theories.K_zero_zero tm), tmdict)
    in
      dicts_ref := (tydict, tmdict)
    end

  (* CPC prints rational literals as atoms (for example `-1` and `4/3`),
     while SMT-LIB normally uses constructor syntax.  These occur in proof
     arguments and definitions even when the source query contained no
     rational atom.  Keep the compatibility layer narrow: standard literals
     remain delegated to the ordinary dictionaries and unknown proof tokens
     still fail loudly. *)
  fun cpc_literal_parsefn token indices args =
    if not (List.null indices) orelse not (List.null args) then
      SmtLib_Theories.decline "<cpc_literal_parsefn>"
        "not a nullary CPC literal"
    else case SmtLib_Parser.proof_string_token token of
      SOME value =>
        (SmtLib_String_Literal.mk_string_term value
         handle SmtLib_String_Literal.InvalidStringLiteral detail =>
           raise ERR "cpc_literal_parsefn" detail)
    | NONE =>
    if String.isPrefix "-" token orelse String.isSubstring "/" token then
      let
        val is_fraction = String.isSubstring "/" token
        val fields = String.fields (fn c => c = #"/") token
        val (numerator_text, denominator_text) =
          case fields of
            [numerator, denominator] => (numerator, denominator)
          | [numerator] => (numerator, "1")
          | _ => raise ERR "cpc_literal_parsefn" "malformed CPC rational literal"
        val numerator = Arbint.fromString numerator_text
        val denominator = Arbint.fromString denominator_text
      in
        if not is_fraction then intSyntax.term_of_int numerator
        else if denominator = Arbint.one then realSyntax.term_of_int numerator
        else realSyntax.mk_div (realSyntax.term_of_int numerator,
          realSyntax.term_of_int denominator)
      end
    else SmtLib_Theories.decline "<cpc_literal_parsefn>"
      "not a CPC rational literal"

  fun numeral_of_term where_ tm =
    numSyntax.dest_numeral tm
    handle Feedback.HOL_ERR _ =>
      Arbint.toNat (intSyntax.int_of_term tm)
      handle Feedback.HOL_ERR _ =>
        raise ERR where_ "expected a CPC natural-number argument"

  (* These compact constructors are emitted by cvc5's CPC printer, not by
     SMT-LIB source files.  They are definitional presentations of ordinary
     HOL bit-vector terms. *)
  fun cpc_bv_parsefn token indices args =
    if not (List.null indices) then
      SmtLib_Theories.decline "<cpc_bv_parsefn>"
        "unexpected indexed CPC bit-vector term"
    else
      case (token, args) of
        ("@bv", [value, width]) =>
          wordsSyntax.mk_word (numeral_of_term "@bv value" value,
            numeral_of_term "@bv width" width)
      | ("@bvsize", [word]) =>
          intSyntax.mk_injected
            (numSyntax.mk_numeral
              (fcpLib.index_to_num (wordsSyntax.dim_of word)))
      | ("@bit", [index, word]) =>
          wordsSyntax.mk_word_bit
            (numSyntax.mk_numeral (numeral_of_term "@bit index" index), word)
      | ("@from_bools", bits) => SmtLib_Theories.mk_bbterm bits
      | ("bvsltbv", [left, right]) =>
          boolSyntax.mk_cond
            (wordsSyntax.mk_word_lt (left, right),
             wordsSyntax.mk_word (Arbnum.one, Arbnum.one),
             wordsSyntax.mk_word (Arbnum.zero, Arbnum.one))
      | ("bvultbv", [left, right]) =>
          boolSyntax.mk_cond
            (wordsSyntax.mk_word_lo (left, right),
             wordsSyntax.mk_word (Arbnum.one, Arbnum.one),
             wordsSyntax.mk_word (Arbnum.zero, Arbnum.one))
      | ("concat", first :: rest) =>
          if List.null rest then
            SmtLib_Theories.decline "<cpc_bv_parsefn>"
              "concat expects at least two words"
          else List.foldl
            (fn (right, left) => wordsSyntax.mk_word_concat (left, right))
            first rest
      | _ => SmtLib_Theories.decline "<cpc_bv_parsefn>"
          "malformed CPC bit-vector term"

  (* A linear-integer source proof can introduce real-valued rational
     coefficients.  cvc5 writes the corresponding floor/coercion operators
     even though the input logic did not need the mixed Int/Real dictionary. *)
  fun cpc_intreal_parsefn token indices args =
    if not (List.null indices) then
      SmtLib_Theories.decline "<cpc_intreal_parsefn>"
        "unexpected indexed CPC arithmetic term"
    else
      case (token, args) of
        ("to_int", [real]) => intrealSyntax.mk_INT_FLOOR real
      | ("to_real", [integer]) => intrealSyntax.mk_real_of_int integer
      | ("int.pow2", [exponent]) =>
          intSyntax.mk_exp
            (intSyntax.term_of_int (Arbint.fromInt 2),
             intSyntax.mk_Num exponent)
      | _ => SmtLib_Theories.decline "<cpc_intreal_parsefn>"
          "malformed CPC arithmetic term"

  (* CPC prints every indexed SMT-LIB term identifier as an ordinary
     application whose leading arguments are the indices.  Derive the
     adapter from the authoritative ALL-logic registry, retaining the
     official SMT-LIB entries and cvc5's proof-term extensions (but not
     another solver's dialect).  This covers the current 23 entries,
     including duplicate overloaded entries, and makes a future applicable
     registry addition available without another CPC list. *)
  fun same_metadata
      ({theory = theory1, kind = kind1, name = name1, source = source1,
        attributes = attributes1, declarations = declarations1}
        : SmtLib_Theories.symbol_metadata)
      ({theory = theory2, kind = kind2, name = name2, source = source2,
        attributes = attributes2, declarations = declarations2}
        : SmtLib_Theories.symbol_metadata) =
    theory1 = theory2 andalso kind1 = kind2 andalso name1 = name2 andalso
    source1 = source2 andalso attributes1 = attributes2 andalso
    declarations1 = declarations2

  fun distinct_metadata metadata = List.foldl
    (fn (entry, result) =>
      if List.exists (same_metadata entry) result then result
      else result @ [entry]) [] metadata

  val cpc_indexed_term_registry = distinct_metadata (List.filter
    (fn ({kind, source, attributes, ...}
          : SmtLib_Theories.symbol_metadata) =>
      kind = "term" andalso #indexed attributes andalso
      (case source of
         SmtLib_Theories.Official => true
       | SmtLib_Theories.Extension "cvc5" => true
       | SmtLib_Theories.Extension _ => false))
    (SmtLib_Logics.metadata_of_logic "ALL"))

  fun indexed_family_arities metadata =
    let
      fun add ({name, attributes, ...}: SmtLib_Theories.symbol_metadata,
          families) =
        let
          val arity = List.length (#parametric_sorts attributes)
        in
          case Redblackmap.peek (families, name) of
            NONE => Redblackmap.insert (families, name, arity)
          | SOME old_arity =>
              if old_arity = arity then families
              else raise ERR "indexed_family_arities"
                ("inconsistent indexed arities for registry symbol " ^ name)
        end
    in
      Redblackmap.listItems (List.foldl add
        (Redblackmap.mkDict String.compare) metadata)
    end

  val cpc_indexed_term_families =
    indexed_family_arities cpc_indexed_term_registry

  fun cpc_deindexed_parsefn source_dict source_name index_arity token
      indices args =
    if source_name = "_" andalso token <> "_" then
      SmtLib_Theories.decline "<cpc_deindexed_parsefn>"
        "generic indexed adapter does not match this token"
    else if not (List.null indices) then
      SmtLib_Parser.apply_term source_dict source_name indices args
    else if List.length args < index_arity then
      SmtLib_Theories.decline "<cpc_deindexed_parsefn>"
        (token ^ " expects " ^ Int.toString index_arity ^
         " flattened index argument(s)")
    else
      SmtLib_Parser.apply_term source_dict source_name
        (List.take (args, index_arity)) (List.drop (args, index_arity))

  fun with_cpc_deindexed_entries tmdict =
    List.foldl
      (fn ((name, arity), dict) =>
        if Option.isSome (Redblackmap.peek (tmdict, name)) then
          let
            val adapter = cpc_deindexed_parsefn tmdict name arity
            (* [_] is also the parser's generic literal pseudo-entry.  Its
               non-indexed alternatives must remain available for atoms such
               as [#b0]; every real indexed family is replaced outright so
               malformed flattened applications cannot fall through. *)
            val entries = if name = "_" then
                adapter :: Redblackmap.find (tmdict, name)
              else [adapter]
          in
            Redblackmap.insert (dict, name, entries)
          end
        else dict)
      tmdict cpc_indexed_term_families

  (* [to_fp_bv] is a genuinely CPC-specific alias, rather than an indexed
     SMT-LIB registry name. *)
  fun cpc_to_fp_bv_parsefn token indices args =
    case (token, indices, args) of
      ("to_fp_bv", [_, _], _) =>
        SmtLib_Theories.FloatingPoint.to_fp indices args
    | ("to_fp_bv", [], eb :: sb :: rest) =>
        SmtLib_Theories.FloatingPoint.to_fp [eb, sb] rest
    | _ => raise ERR "cpc_to_fp_bv_parsefn"
        "to_fp_bv expects two FP format indices"

  (* cvc5's FP bit-blaster uses sort expressions as proof-term metadata,
     for example `(@fp.SIGN (_ BitVec 1))`.  HOL has no terms denoting
     types, so retain only the marker's HOL type.  The internal @fp names
     then become ordinary free HOL variables of that type; a later `trust`
     step must still prove every relationship between them and the source FP
     term.  This interpretation therefore grants no theorem. *)
  fun cpc_sort_marker_parsefn token indices args =
    let
      fun marker name ty = Term.mk_var (name, ty)
      fun width index = fcpLib.index_type (numeral_of_term token index)
    in
      case (token, indices, args) of
        ("BitVec", [bits], []) =>
          marker "@cpc.BitVec" (wordsSyntax.mk_word_type (width bits))
      | ("FloatingPoint", [eb, sb], []) =>
          marker "@cpc.FloatingPoint"
            (SmtLib_Theories.smtfp_type
              (numeral_of_term token eb, numeral_of_term token sb))
      | ("->", [], domain :: rest) =>
          if List.null rest then
            raise ERR "cpc_sort_marker_parsefn"
              "CPC function-sort marker needs a range"
          else
            let
              val (domains, range) = Lib.front_last (domain :: rest)
            in
              marker "@cpc.function"
                (boolSyntax.list_mk_fun
                  (List.map Term.type_of domains, Term.type_of range))
            end
      | _ => raise ERR "cpc_sort_marker_parsefn"
          ("malformed CPC sort marker " ^ token)
    end

  type cpc_fp_private_binding = {
    marker : Term.term,
    kind : string,
    source : Term.term
  }

  val cpc_fp_private_bindings_ref =
    ref ([] : cpc_fp_private_binding list)

  val cpc_fp_private_unbound_count = ref 0

  fun cpc_fp_private_bindings () = !cpc_fp_private_bindings_ref

  fun cpc_fp_private_abbreviation token sort_marker source =
    let
      fun same ({marker, kind, source = saved} : cpc_fp_private_binding) =
        kind = token andalso
        Type.compare (Term.type_of marker, Term.type_of sort_marker) = EQUAL
        andalso (Portable.pointer_eq (saved, source) orelse
                 Term.aconv saved source)
    in
      case List.find same (!cpc_fp_private_bindings_ref) of
        SOME {marker, ...} => marker
      | NONE =>
          let
            val marker = Term.mk_var
              (token ^ "#" ^
               Int.toString (List.length (!cpc_fp_private_bindings_ref)),
               Term.type_of sort_marker)
            val binding = {marker = marker, kind = token, source = source}
          in
            cpc_fp_private_bindings_ref :=
              binding :: !cpc_fp_private_bindings_ref;
            marker
          end
    end

  fun cpc_fp_private_parsefn token indices args =
    if not (List.null indices) then
      raise ERR "cpc_fp_private_parsefn" "unexpected indices"
    else
      case args of
        [sort_marker] =>
          let
            val serial = !cpc_fp_private_unbound_count
            val _ = cpc_fp_private_unbound_count := serial + 1
          in Term.mk_var
            (token ^ "#unbound" ^ Int.toString serial,
             Term.type_of sort_marker) end
      | [sort_marker, source] =>
          cpc_fp_private_abbreviation token sort_marker source
      | _ => raise ERR "cpc_fp_private_parsefn"
          (token ^ " expects a sort marker and at most one " ^
           "floating-point operand")

  fun cpc_fp_rounding_parsefn token indices args =
    if token <> "@fp.RMBITBLAST" orelse not (List.null indices) then
      raise ERR "cpc_fp_rounding_parsefn"
        "malformed private rounding-mode bit-blast"
    else
      case args of
        [source] =>
          let
            val constant = Term.prim_mk_const
              {Thy = "smtfloatReplayWord",
               Name = "smtfp_cvc_rounding_bits"}
            val (domain, _) = Type.dom_rng (Term.type_of constant)
            val instantiation =
              Type.match_type domain (Term.type_of source)
          in Term.mk_comb (Term.inst instantiation constant, source) end
      | _ => raise ERR "cpc_fp_rounding_parsefn"
          "private rounding-mode bit-blast expects one operand"

  fun cpc_private_const_parsefn token indices args =
    if token <> "@const" orelse not (List.null indices) then
      raise ERR "cpc_private_const_parsefn" "malformed private constant"
    else
      case args of
        [index, sort_marker] =>
          let
            val _ =
              Type.compare (Term.type_of index, intSyntax.int_ty) = EQUAL
              orelse raise ERR "cpc_private_const_parsefn"
                "@const index must have HOL int type"
          in
            Term.mk_var
              ("@cpc.const." ^
               Arbnum.toString (numeral_of_term token index),
               Term.type_of sort_marker)
          end
      | _ => raise ERR "cpc_private_const_parsefn"
          "@const expects an index and a sort marker"

  fun cpc_bvite_parsefn token indices args =
    if token <> "bvite" orelse not (List.null indices) then
      raise ERR "cpc_bvite_parsefn" "malformed bvite"
    else
      case args of
        [condition, then_branch, else_branch] =>
          boolSyntax.mk_cond
            (wordsSyntax.mk_word_bit (numSyntax.zero_tm, condition),
             then_branch, else_branch)
      | _ => raise ERR "cpc_bvite_parsefn" "bvite expects three arguments"

  (* Totalized FP operators are private bit-blaster vocabulary.  Keep each
     application as an uninterpreted HOL function: its defining `trust` step
     is accepted only if the FP re-prover can establish the relationship to
     the public SMT-LIB operator. *)
  fun cpc_fp_total_parsefn token indices args =
    if not (List.null indices) orelse List.null args then
      raise ERR "cpc_fp_total_parsefn" "malformed private FP operator"
    else
      let
        val result_type = Term.type_of (List.hd args)
        val function_type = boolSyntax.list_mk_fun
          (List.map Term.type_of args, result_type)
      in
        Term.list_mk_comb (Term.mk_var (token, function_type), args)
      end

  (* cvc5's CPC signature contains totalized arithmetic operators that are
     not SMT-LIB symbols.  Integer totals have specified zero branches;
     integer by-zero skolems remain HOL's underspecified ediv/emod at zero.
     Real by-zero uses smt_rdiv, since HOL real division is specified there. *)
  val smt_ediv_total_tm = Term.prim_mk_const
    {Thy = "HolSmt", Name = "smt_ediv_total"}
  val smt_emod_total_tm = Term.prim_mk_const
    {Thy = "HolSmt", Name = "smt_emod_total"}
  val smt_rdiv_tm = Term.prim_mk_const
    {Thy = "HolSmt", Name = "smt_rdiv"}

  fun cpc_arith_total_error message =
    raise ERR "cpc_arith_total_parsefn" message

  fun cpc_left_assoc name constructor args =
    case args of
      first :: rest =>
        if List.null rest then
          cpc_arith_total_error (name ^ " expects at least two arguments")
        else List.foldl (fn (right, left) => constructor (left, right))
          first rest
    | [] => cpc_arith_total_error (name ^ " expects arguments")

  fun cpc_real_arg arg =
    if Type.compare (Term.type_of arg, intSyntax.int_ty) = EQUAL then
      intrealSyntax.mk_real_of_int arg
    else arg

  fun cpc_arith_total_parsefn token indices args =
    if not (List.null indices) then
      cpc_arith_total_error (token ^ " does not accept indices")
    else
      case token of
        "div_total" => cpc_left_assoc token
          (fn (left, right) => Term.list_mk_comb
            (smt_ediv_total_tm, [left, right])) args
      | "mod_total" =>
          (case args of
             [left, right] => Term.list_mk_comb
               (smt_emod_total_tm, [left, right])
           | _ => cpc_arith_total_error "mod_total expects two arguments")
      | "/_total" => cpc_left_assoc token
          (fn (left, right) => realSyntax.mk_div (left, right))
          (List.map cpc_real_arg args)
      | "@int_div_by_zero" =>
          (case args of
             [arg] => SmtLib_Theories.mk_int_ediv
               (arg, intSyntax.zero_tm)
           | [] => Term.mk_var (token, intSyntax.int_ty)
           | _ => cpc_arith_total_error
               "@int_div_by_zero expects one argument")
      | "@mod_by_zero" =>
          (case args of
             [arg] => SmtLib_Theories.mk_int_emod
               (arg, intSyntax.zero_tm)
           | [] => Term.mk_var (token, intSyntax.int_ty)
           | _ => cpc_arith_total_error
               "@mod_by_zero expects one argument")
      | "@div_by_zero" =>
          (case args of
             [arg] => Term.list_mk_comb
               (smt_rdiv_tm, [arg, realSyntax.zero_tm])
           | [] => Term.mk_var (token, realSyntax.real_ty)
           | _ => cpc_arith_total_error
               "@div_by_zero expects one argument")
      | _ => cpc_arith_total_error
        ("unsupported totalized arithmetic symbol " ^ token)

  (* cvc5 uses unary variadic aggregates as compact list substitutions in
     RARE annotations.  They are proof metadata, not accepted benchmark
     syntax; interpret a singleton as itself and retain the standard
     left-associative meaning for longer lists. *)
  fun cpc_concat_parsefn theory_name token indices args =
    if not (List.null indices) then
      raise ERR "cpc_concat_parsefn" "unexpected concat indices"
    else
      let
        val constant =
          Term.prim_mk_const {Thy = "smtstring", Name = theory_name}
        fun concat (right, left) =
          Term.list_mk_comb (constant, [left, right])
      in
        case args of
          first :: rest => List.foldl concat first rest
        | [] => raise ERR "cpc_concat_parsefn"
            (token ^ " expects at least one CPC argument")
      end

  fun with_cpc_fp_entries tmdict =
    let
      val tmdict = List.foldl
        (fn (name, dict) => Library.extend_dict
          ((name, cpc_sort_marker_parsefn), dict))
        tmdict ["BitVec", "FloatingPoint", "->"]
      val tmdict = List.foldl
        (fn (name, dict) => Library.extend_dict
          ((name, cpc_fp_private_parsefn), dict))
        tmdict
        ["@fp.SIGN", "@fp.EXPONENT", "@fp.SIGNIFICAND", "@fp.ZERO",
         "@fp.NAN", "@fp.INF"]
      val tmdict = Library.extend_dict
        (("@fp.RMBITBLAST", cpc_fp_rounding_parsefn), tmdict)
      val tmdict = Library.extend_dict
        (("bvite", cpc_bvite_parsefn), tmdict)
      val tmdict = List.foldl
        (fn (name, dict) => Library.extend_dict
          ((name, cpc_fp_total_parsefn), dict))
        tmdict ["fp.max_total", "fp.min_total"]
    in
      Library.extend_dict
        (("to_fp_bv", cpc_to_fp_bv_parsefn), tmdict)
    end

  val cpc_smtstr_ty =
    Type.mk_thy_type {Thy = "smtstring", Tyop = "smtstr", Args = []}

  fun cpc_skolem_error where_ message = raise ERR where_ message

  fun cpc_exact_args where_ arity args =
    if List.length args = arity then args
    else cpc_skolem_error where_
      ("expected " ^ Int.toString arity ^ " explicit argument(s)")

  (* Parameterized CPC skolems are authoritative typed symbols, not an
     invitation to synthesize a fresh UF at whatever types happen to parse.
     Keep all sort/coherence checks in this fail-closed boundary. *)
  val cpc_reglan_ty =
    Type.mk_thy_type {Thy = "smtstring", Tyop = "reglan", Args = []}

  fun cpc_type_eq (left, right) = Type.compare (left, right) = EQUAL

  fun cpc_expect_type where_ expected term =
    if cpc_type_eq (Term.type_of term, expected) then ()
    else cpc_skolem_error where_ "parameterized-skolem sort mismatch"

  fun cpc_expect_same where_ left right =
    if cpc_type_eq (Term.type_of left, Term.type_of right) then ()
    else cpc_skolem_error where_
      "parameterized-skolem arguments have different sorts"

  fun cpc_expect_smtstr where_ term =
    cpc_expect_type where_ cpc_smtstr_ty term

  fun cpc_expect_reglan where_ term =
    cpc_expect_type where_ cpc_reglan_ty term

  fun cpc_reglan_equiv left right =
    SmtRegLanProve.mk_equiv (left, right)

  (* RegLan is an extensional sort in SMT-LIB and cvc5's CPC calculus.  This
     dictionary is proof-local: source HOL equality remains constructor
     equality and is rejected by translation below. *)
  fun cpc_equality_parsefn token indices args =
    let
      val _ = List.null indices orelse cpc_skolem_error
        "cpc_equality_parsefn" "equality does not accept indices"
      val _ = List.length args >= 2 orelse cpc_skolem_error
        "cpc_equality_parsefn" "equality expects at least two arguments"
      val ty = Term.type_of (List.hd args)
      val _ = List.all (fn arg => cpc_type_eq (Term.type_of arg, ty)) args
        orelse cpc_skolem_error "cpc_equality_parsefn"
          "equality arguments have different sorts"
      fun adjacent relation (left :: right :: rest) =
            relation left right :: adjacent relation (right :: rest)
        | adjacent _ _ = []
      val relation =
        if cpc_type_eq (ty, cpc_reglan_ty) then cpc_reglan_equiv
        else fn left => fn right => boolSyntax.mk_eq (left, right)
    in
      boolSyntax.list_mk_conj (adjacent relation args)
    end

  fun cpc_distinct_parsefn token indices args =
    let
      val _ = List.null indices orelse cpc_skolem_error
        "cpc_distinct_parsefn" "distinct does not accept indices"
      val _ = List.length args >= 2 orelse cpc_skolem_error
        "cpc_distinct_parsefn" "distinct expects at least two arguments"
      val ty = Term.type_of (List.hd args)
      val _ = List.all (fn arg => cpc_type_eq (Term.type_of arg, ty)) args
        orelse cpc_skolem_error "cpc_distinct_parsefn"
          "distinct arguments have different sorts"
      fun pairs _ [] = []
        | pairs relation (left :: rest) =
            List.map (fn right => boolSyntax.mk_neg (relation left right))
              rest @ pairs relation rest
    in
      if cpc_type_eq (ty, cpc_reglan_ty) then
        boolSyntax.list_mk_conj (pairs cpc_reglan_equiv args)
      else
        listSyntax.mk_all_distinct (listSyntax.mk_list (args, ty))
    end

  fun cpc_expect_int where_ term =
    cpc_expect_type where_ intSyntax.int_ty term

  fun cpc_sequence_element where_ term =
    if cpc_type_eq (Term.type_of term, cpc_smtstr_ty) then numSyntax.num
    else
      (listSyntax.dest_list_type (Term.type_of term)
       handle Feedback.HOL_ERR _ => cpc_skolem_error where_
         "expected a String or Seq argument")

  fun cpc_expect_same_sequence where_ left right =
    let
      val left_element = cpc_sequence_element where_ left
      val right_element = cpc_sequence_element where_ right
    in
      if cpc_type_eq (left_element, right_element) andalso
         cpc_type_eq (Term.type_of left, Term.type_of right) then ()
      else cpc_skolem_error where_
        "parameterized-skolem expected same-element Seq arguments"
    end

  fun cpc_function_types where_ function =
    Type.dom_rng (Term.type_of function)
    handle Feedback.HOL_ERR _ => cpc_skolem_error where_
      "expected a function argument"

  fun cpc_expect_function where_ domain range function =
    let val (actual_domain, actual_range) =
      cpc_function_types where_ function
    in
      if cpc_type_eq (domain, actual_domain) andalso
         cpc_type_eq (range, actual_range) then ()
      else cpc_skolem_error where_
        "parameterized-skolem function domain/range mismatch"
    end

  fun cpc_opaque_skolem token result_ty args =
    Term.list_mk_comb
      (Term.mk_var (token,
        boolSyntax.list_mk_fun (List.map Term.type_of args, result_ty)), args)

  fun cpc_purify_parsefn token indices args =
    case (token, indices, cpc_exact_args "cpc_purify_parsefn" 1 args) of
      ("@purify", [], [term]) => term
    | _ => cpc_skolem_error "cpc_purify_parsefn"
        "malformed @purify application"

  fun cpc_array_deq_diff_parsefn token indices args =
    case (token, indices,
        cpc_exact_args "cpc_array_deq_diff_parsefn" 2 args) of
      ("@array_deq_diff", [], [left, right]) =>
        let
          val (index, _) = cpc_function_types token left
          val _ = cpc_expect_same token left right
          val variable = Term.variant (Term.all_varsl [left, right])
            (Term.mk_var ("array_deq_diff_x", index))
        in
          boolSyntax.mk_select (variable, boolSyntax.mk_neg
            (boolSyntax.mk_eq (Term.mk_comb (left, variable),
              Term.mk_comb (right, variable))))
        end
    | _ => cpc_skolem_error "cpc_array_deq_diff_parsefn"
        "malformed @array_deq_diff application"

  fun immediate_forall_block where_ quantified =
    let
      fun lookup [] = cpc_skolem_error where_
            "source FORALL binder-block metadata is unavailable"
        | lookup ((candidate, sizes) :: rest) =
            if Term.aconv candidate quantified then
              (case sizes of
                 [size] => (candidate, size)
               | _ => cpc_skolem_error where_
                   "source FORALL binder-block metadata is ambiguous")
            else lookup rest
    in
      lookup (!cpc_forall_blocks)
    end

  fun cpc_quantifiers_skolemize_parsefn token indices args =
    case (token, indices,
        cpc_exact_args "cpc_quantifiers_skolemize_parsefn" 2 args) of
      ("@quantifiers_skolemize", [], [quantified, index_term]) =>
        let
          val where_ = "cpc_quantifiers_skolemize_parsefn"
          val _ = cpc_expect_int token index_term
          val index =
            (intSyntax.int_of_term index_term
             handle Feedback.HOL_ERR _ => cpc_skolem_error where_
               "expected a concrete integer binder index")
          val _ = if Arbint.< (index, Arbint.zero) then
              cpc_skolem_error where_ "binder index is negative"
            else ()
          val _ = if boolSyntax.is_forall quantified then ()
            else cpc_skolem_error where_
              "expected a FORALL Boolean formula"
          val (canonical_quantified, immediate_count) =
            immediate_forall_block where_ quantified
          val {witnesses, ...} = CPC_Proof.cpc_skolem_witnesses
            immediate_count
            (Thm.ASSUME (boolSyntax.mk_neg canonical_quantified))
          fun witness_at _ [] = cpc_skolem_error where_
                "binder index is outside the quantified formula"
            | witness_at current (witness :: rest) =
                (case Arbint.compare (index, current) of
                   EQUAL => witness
                 | GREATER =>
                     witness_at (Arbint.+ (current, Arbint.one)) rest
                 | LESS => cpc_skolem_error where_
                     "binder index is outside the quantified formula")
        in
          witness_at Arbint.zero witnesses
        end
    | _ => cpc_skolem_error "cpc_quantifiers_skolemize_parsefn"
        "malformed @quantifiers_skolemize application"

  fun cpc_sets_deq_diff_parsefn token indices args =
    case (token, indices, cpc_exact_args "cpc_sets_deq_diff_parsefn" 2 args) of
      ("@sets_deq_diff", [], [left, right]) =>
        let
          val (element, range) = cpc_function_types token left
          val _ = cpc_expect_type token Type.bool
            (Term.mk_var ("set_range", range))
          val _ = cpc_expect_same token left right
          val variable = Term.variant (Term.all_varsl [left, right])
            (Term.mk_var ("sets_deq_diff_x", element))
        in
          boolSyntax.mk_select (variable, boolSyntax.mk_neg
            (boolSyntax.mk_eq (Term.mk_comb (left, variable),
              Term.mk_comb (right, variable))))
        end
    | _ => cpc_skolem_error "cpc_sets_deq_diff_parsefn"
        "malformed @sets_deq_diff application"

  fun cpc_bag_element where_ bag =
    let val (element, count) =
      (Type.dom_rng (Term.type_of bag)
       handle Feedback.HOL_ERR _ => cpc_skolem_error where_
         "parameterized-skolem expected a Bag argument")
    in
      if Type.compare (count, numSyntax.num) = EQUAL then element
      else cpc_skolem_error where_
        "parameterized-skolem expected a Bag argument"
    end

  fun cpc_bag_element_type where_ bag_ty =
    let val (element, count) =
      (Type.dom_rng bag_ty
       handle Feedback.HOL_ERR _ => cpc_skolem_error where_
         "parameterized-skolem expected a nested Bag argument")
    in
      if cpc_type_eq (count, numSyntax.num) then element
      else cpc_skolem_error where_
        "parameterized-skolem expected a nested Bag argument"
    end

  fun cpc_bag_skolem_parsefn token indices args =
    if not (List.null indices) then
      cpc_skolem_error "cpc_bag_skolem_parsefn"
        (token ^ " does not accept indices")
    else
      case (token, args) of
        ("@bags_deq_diff", [left, right]) =>
          let
            val element = cpc_bag_element token left
            val _ =
              if Type.compare (Term.type_of left, Term.type_of right) = EQUAL
              then ()
              else cpc_skolem_error token
                "expected two Bags of the same type"
            val variable = Term.variant (Term.all_varsl [left, right])
              (Term.mk_var ("bags_deq_diff_x", element))
          in
            boolSyntax.mk_select (variable, boolSyntax.mk_neg
              (boolSyntax.mk_eq (Term.mk_comb (left, variable),
                Term.mk_comb (right, variable))))
          end
      | ("@tables_group_part", [table]) =>
          let
            val bag_ty = cpc_bag_element token table
            val element = cpc_bag_element_type token bag_ty
          in
            cpc_opaque_skolem token (Type.--> (element, bag_ty)) args
          end
      | ("@tables_group_part_element", [table, bag]) =>
          let
            val nested_bag_ty = cpc_bag_element token table
            val element = cpc_bag_element_type token nested_bag_ty
            val _ = cpc_expect_type token nested_bag_ty bag
          in
            cpc_opaque_skolem token element args
          end
      | ("@bags_map_sum", [function, bag, image]) =>
          let
            val element = cpc_bag_element token bag
            val (domain, range) = cpc_function_types token function
            val _ = cpc_type_eq (domain, element) orelse
              cpc_skolem_error token
                ("parameterized-skolem Bag-map function domain does not " ^
                 "match Bag element")
            val _ = cpc_expect_type token range image
          in
            cpc_opaque_skolem token
              (Type.--> (intSyntax.int_ty, intSyntax.int_ty)) args
          end
      | ("@bags_distinct_elements", [bag]) =>
          cpc_opaque_skolem token (Type.--> (intSyntax.int_ty,
            cpc_bag_element token bag)) args
      | ("@bags_distinct_elements_size", [bag]) =>
          (ignore (cpc_bag_element token bag);
           cpc_opaque_skolem token intSyntax.int_ty args)
      | ("@bags_map_preimage_injective", [function, bag, image]) =>
          let
            val element = cpc_bag_element token bag
            val (_, range) = cpc_function_types token function
            val _ = cpc_expect_function token element range function
            val _ = cpc_expect_type token range image
          in
            cpc_opaque_skolem token element args
          end
      | _ => cpc_skolem_error "cpc_bag_skolem_parsefn"
          ("malformed parameterized Bag skolem " ^ token)

  fun cpc_same_const thy name tm =
    case Lib.total Term.dest_thy_const tm of
      SOME {Thy, Name, ...} => Thy = thy andalso Name = name
    | NONE => false

  fun cpc_strip_regex_concat regex =
    case boolSyntax.strip_comb regex of
      (head, [left, right]) =>
        if cpc_same_const "smtstring" "reglan_concat" head then
          cpc_strip_regex_concat left @ cpc_strip_regex_concat right
        else [regex]
    | _ => [regex]

  fun cpc_regex_concat_pair regex =
    case boolSyntax.strip_comb regex of
      (head, [left, right]) =>
        if cpc_same_const "smtstring" "reglan_concat" head then
          SOME (left, right)
        else NONE
    | _ => NONE

  fun cpc_re_unfold_pos_direct_star regex =
    let
      fun recognized body middle suffix =
        case boolSyntax.strip_comb middle of
          (star, [star_body]) =>
            if cpc_same_const "smtstring" "reglan_star" star andalso
               Term.aconv body star_body andalso Term.aconv body suffix
            then SOME [body, middle, suffix]
            else NONE
        | _ => NONE
      val right_associated =
        case cpc_regex_concat_pair regex of
          SOME (body, rest) =>
            (case cpc_regex_concat_pair rest of
               SOME (middle, suffix) => recognized body middle suffix
             | NONE => NONE)
        | NONE => NONE
    in
      case right_associated of
        SOME components => SOME components
      | NONE =>
          (case cpc_regex_concat_pair regex of
             SOME (front, suffix) =>
               (case cpc_regex_concat_pair front of
                  SOME (body, middle) => recognized body middle suffix
                | NONE => NONE)
           | NONE => NONE)
    end

  fun cpc_re_unfold_pos_regexps regex =
    case cpc_re_unfold_pos_direct_star regex of
      SOME components => components
    | NONE => cpc_strip_regex_concat regex

  fun cpc_re_unfold_pos_decomposition string regex =
    let
      val regexps = cpc_re_unfold_pos_regexps regex
      val list_ty = listSyntax.mk_list_type cpc_smtstr_ty
      val pieces = Term.variant (Term.all_varsl [string, regex])
        (Term.mk_var ("re_unfold_pos_pieces", list_ty))
      fun piece position = listSyntax.mk_el
        (numSyntax.mk_numeral (Arbnum.fromInt position), pieces)
      val positions = List.tabulate (List.length regexps, Lib.I)
      val selected = List.map piece positions
      val regex_list = listSyntax.mk_list
        (regexps, Term.type_of (List.hd regexps))
      val count = listSyntax.mk_length regex_list
      val position = Term.mk_var ("i", numSyntax.num)
      fun selected_list candidate = listSyntax.mk_genlist
        (Term.mk_abs (position, listSyntax.mk_el (position, candidate)),
         count)
      val concat_list = Term.prim_mk_const
        {Thy = "smtstring", Name = "smtstr_concat_list"}
      val membership_relation = Term.prim_mk_const
        {Thy = "smtstring", Name = "smt_in_re"}
      val list_relation = Term.inst
        [{redex = Type.alpha, residue = cpc_smtstr_ty},
         {redex = Type.beta, residue = Term.type_of (List.hd regexps)}]
        (Term.prim_mk_const {Thy = "list", Name = "LIST_REL"})
      val empty = Term.mk_comb
        (Term.prim_mk_const {Thy = "smtstring", Name = "SmtStr"},
         listSyntax.mk_nil numSyntax.num)
      fun ordinary candidate = boolSyntax.list_mk_conj
        [boolSyntax.mk_eq (listSyntax.mk_length candidate, count),
         boolSyntax.mk_eq
           (string, Term.mk_comb (concat_list, selected_list candidate)),
         Term.list_mk_comb
           (list_relation,
            [membership_relation, selected_list candidate, regex_list])]
      fun endpoints candidate = boolSyntax.mk_conj
        (boolSyntax.mk_neg (boolSyntax.mk_eq
           (listSyntax.mk_el (numSyntax.zero_tm, candidate), empty)),
         boolSyntax.mk_neg (boolSyntax.mk_eq
           (listSyntax.mk_el
             (Term.mk_comb
                (Term.prim_mk_const {Thy = "prim_rec", Name = "PRE"},
                 count),
              candidate),
            empty)))
      val other = Term.variant (pieces :: Term.all_varsl [string, regex])
        (Term.mk_var ("re_unfold_pos_other", list_ty))
      val guarded_exists = boolSyntax.mk_exists
        (other, boolSyntax.mk_conj (ordinary other, endpoints other))
      val predicate = boolSyntax.mk_conj
        (ordinary pieces,
         boolSyntax.mk_imp (guarded_exists, endpoints pieces))
    in
      {pieces = pieces, regexps = regexps, selected = selected,
       predicate = predicate,
       witness = boolSyntax.mk_select (pieces, predicate)}
    end

  (* A RE_UNFOLD_POS component is a projection of one shared Hilbert-choice
     decomposition, not an independent opaque string.  Rebuilding the same
     choice predicate for every index makes all projections coherent while
     leaving the choice entirely theorem backed. *)
  fun cpc_re_unfold_pos_component string regex index =
    let
      val index = Arbint.toInt (intSyntax.int_of_term index)
        handle Overflow => cpc_skolem_error
          "cpc_re_unfold_pos_component" "component index is too large"
      val _ = if index >= 0 then () else cpc_skolem_error
        "cpc_re_unfold_pos_component" "component index is negative"
      val {regexps, witness, ...} =
        cpc_re_unfold_pos_decomposition string regex
      val _ = if index < List.length regexps then () else cpc_skolem_error
        "cpc_re_unfold_pos_component"
        "component index is outside the regular-expression concat"
    in
      listSyntax.mk_el
        (numSyntax.mk_numeral (Arbnum.fromInt index), witness)
    end

  fun cpc_string_skolem_parsefn token indices args =
    if not (List.null indices) then
      cpc_skolem_error "cpc_string_skolem_parsefn"
        (token ^ " does not accept indices")
    else
      let
        val arity =
          case token of
            "@re_unfold_pos_component" => 3
          | "@strings_deq_diff" => 2
          | "@strings_stoi_result" => 1
          | "@strings_stoi_non_digit" => 1
          | "@strings_itos_result" => 1
          | "@strings_num_occur" => 2
          | "@strings_num_occur_re" => 2
          | "@strings_occur_index" => 2
          | "@strings_occur_index_re" => 2
          | "@strings_replace_all_result" => 1
          | "@witness_string_length" => 1
          | _ => cpc_skolem_error "cpc_string_skolem_parsefn"
              ("unknown parameterized String skolem " ^ token)
        val args = cpc_exact_args "cpc_string_skolem_parsefn" arity args
      in
      case (token, args) of
        ("@re_unfold_pos_component", [string, regex, index]) =>
          (cpc_expect_smtstr token string;
           cpc_expect_reglan token regex;
           cpc_expect_int token index;
           cpc_re_unfold_pos_component string regex index)
      | ("@strings_deq_diff", [left, right]) =>
          (cpc_expect_same_sequence token left right;
           cpc_opaque_skolem token intSyntax.int_ty args)
      | ("@strings_stoi_result", [string]) =>
          (cpc_expect_smtstr token string;
          cpc_opaque_skolem token
            (Type.--> (intSyntax.int_ty, intSyntax.int_ty)) args)
      | ("@strings_stoi_non_digit", [string]) =>
          (cpc_expect_smtstr token string;
           cpc_opaque_skolem token intSyntax.int_ty args)
      | ("@strings_itos_result", [integer]) =>
          (cpc_expect_int token integer;
          cpc_opaque_skolem token
            (Type.--> (intSyntax.int_ty, intSyntax.int_ty)) args)
      | ("@strings_num_occur", [left, right]) =>
          (cpc_expect_same_sequence token left right;
           cpc_opaque_skolem token intSyntax.int_ty args)
      | ("@strings_num_occur_re", [string, regex]) =>
          (cpc_expect_smtstr token string;
           cpc_expect_reglan token regex;
           cpc_opaque_skolem token intSyntax.int_ty args)
      | ("@strings_occur_index", [left, right]) =>
          (cpc_expect_same_sequence token left right;
          cpc_opaque_skolem token
            (Type.--> (intSyntax.int_ty, intSyntax.int_ty)) args)
      | ("@strings_occur_index_re", [string, regex]) =>
          (cpc_expect_smtstr token string;
           cpc_expect_reglan token regex;
          cpc_opaque_skolem token
            (Type.--> (intSyntax.int_ty, intSyntax.int_ty)) args)
      | ("@strings_replace_all_result", [sequence]) =>
          (ignore (cpc_sequence_element token sequence);
           cpc_opaque_skolem token
             (Type.--> (intSyntax.int_ty, Term.type_of sequence)) args)
      | ("@witness_string_length", [sort_marker]) =>
          (ignore (cpc_sequence_element token sort_marker);
           cpc_opaque_skolem token
             (boolSyntax.list_mk_fun
               ([intSyntax.int_ty, intSyntax.int_ty],
                Term.type_of sort_marker)) args)
      | _ => cpc_skolem_error "cpc_string_skolem_parsefn"
          ("malformed parameterized String skolem " ^ token)
      end

  type cpc_skolem_entry = {
    name: string,
    parse: string -> Term.term list -> Term.term list -> Term.term
  }

  fun cpc_skolem_entry parse name : cpc_skolem_entry =
    {name = name, parse = parse}

  (* The closed opaque-skolem inventory in cvc5 1.3.4's safe CPC
     signature: Cpc.eo plus Arrays/Builtin/Quantifiers/Sets/Strings and the
     seven Bag skolems from the expert signature. *)
  val cpc_parameterized_skolem_registry : cpc_skolem_entry list =
    [cpc_skolem_entry cpc_purify_parsefn "@purify",
     cpc_skolem_entry cpc_array_deq_diff_parsefn "@array_deq_diff",
     cpc_skolem_entry cpc_private_const_parsefn "@const",
     cpc_skolem_entry cpc_string_skolem_parsefn
       "@re_unfold_pos_component",
     cpc_skolem_entry cpc_string_skolem_parsefn "@strings_deq_diff",
     cpc_skolem_entry cpc_string_skolem_parsefn "@strings_stoi_result",
     cpc_skolem_entry cpc_string_skolem_parsefn "@strings_stoi_non_digit",
     cpc_skolem_entry cpc_string_skolem_parsefn "@strings_itos_result",
     cpc_skolem_entry cpc_string_skolem_parsefn "@strings_num_occur",
     cpc_skolem_entry cpc_string_skolem_parsefn "@strings_num_occur_re",
     cpc_skolem_entry cpc_string_skolem_parsefn "@strings_occur_index",
     cpc_skolem_entry cpc_string_skolem_parsefn "@strings_occur_index_re",
     cpc_skolem_entry cpc_string_skolem_parsefn
       "@strings_replace_all_result",
     cpc_skolem_entry cpc_string_skolem_parsefn "@witness_string_length",
     cpc_skolem_entry cpc_sets_deq_diff_parsefn "@sets_deq_diff",
     cpc_skolem_entry cpc_quantifiers_skolemize_parsefn
       "@quantifiers_skolemize",
     cpc_skolem_entry cpc_bag_skolem_parsefn "@bags_deq_diff",
     cpc_skolem_entry cpc_bag_skolem_parsefn "@tables_group_part",
     cpc_skolem_entry cpc_bag_skolem_parsefn
       "@tables_group_part_element",
     cpc_skolem_entry cpc_bag_skolem_parsefn "@bags_map_sum",
     cpc_skolem_entry cpc_bag_skolem_parsefn
       "@bags_distinct_elements",
     cpc_skolem_entry cpc_bag_skolem_parsefn
       "@bags_distinct_elements_size",
     cpc_skolem_entry cpc_bag_skolem_parsefn
       "@bags_map_preimage_injective"]

  val cpc_parameterized_skolem_names =
    List.map (fn ({name, ...}: cpc_skolem_entry) => name)
      cpc_parameterized_skolem_registry

  val _ =
    let
      val unique = HOLset.numItems (HOLset.addList
        (HOLset.empty String.compare, cpc_parameterized_skolem_names))
    in
      if List.length cpc_parameterized_skolem_registry = 23 andalso
         unique = 23 then ()
      else cpc_skolem_error "cpc_parameterized_skolem_registry"
        "closed CPC parameterized-skolem registry must contain 23 unique names"
    end

  fun with_cpc_parameterized_skolems tmdict =
    List.foldl
      (fn ({name, parse}: cpc_skolem_entry, dict) =>
        Library.extend_dict ((name, parse), dict))
      tmdict cpc_parameterized_skolem_registry

  fun cpc_parameterized_skolem_for_test name args =
    case List.find
        (fn ({name = candidate, ...}: cpc_skolem_entry) =>
          candidate = name) cpc_parameterized_skolem_registry of
      SOME {parse, ...} => parse name [] args
    | NONE => cpc_skolem_error "cpc_parameterized_skolem_for_test"
        ("unknown parameterized skolem " ^ name)

  fun with_cpc_literals (tydict, tmdict) =
    let
      (* cvc5 writes [Bag Bool] in qualified bag literals.  A proof sort is
         parsed through the term dictionary, so retain Bool only as a marker. *)
      fun bool_sort_marker token indices args =
        if token = "Bool" andalso List.null indices andalso List.null args then
          boolSyntax.T
        else raise ERR "bool_sort_marker" "expected the Bool sort marker"
      fun string_sort_marker token indices args =
        if token = "String" andalso List.null indices andalso
           List.null args then
          Term.mk_var ("@cpc.String", cpc_smtstr_ty)
        else raise ERR "string_sort_marker"
          "expected the String sort marker"
      fun bag_sort_marker token indices args =
        case (token, indices, args) of
          ("Bag", [], [element]) => Term.mk_var ("@cpc.Bag",
            Type.--> (Term.type_of element, numSyntax.num))
        | _ => raise ERR "bag_sort_marker" "expected a Bag sort marker"
      fun set_sort_marker token indices args =
        case (token, indices, args) of
          ("Set", [], [element]) => Term.mk_var ("@cpc.Set",
            Type.--> (Term.type_of element, Type.bool))
        | _ => raise ERR "set_sort_marker" "expected a Set sort marker"
      fun as_sort_marker token indices args =
        case (token, indices, args) of
          ("as", [], [term, sort]) =>
            if Type.compare (Term.type_of term, Term.type_of sort) = EQUAL
            then term
            else raise ERR "as_sort_marker" "qualification sort mismatch"
        | _ => raise ERR "as_sort_marker" "expected a qualified term"
      fun function_sort token indices args =
        if token = "->" andalso List.null indices andalso
           List.length args >= 2 then
          let val (domains, range) = Lib.front_last args in
            boolSyntax.list_mk_fun (domains, range)
          end
        else raise ERR "function_sort"
          "expected a function sort with a domain and range"
      (* The source translation dictionary is deliberately as narrow as its
         declared logic.  CPC arithmetic lemmas may nevertheless contain
         rationals and their Real coercions, so add the mixed arithmetic
         overloads only while reading the proof. *)
      val tmdict = with_cpc_deindexed_entries tmdict
      val tmdict = Library.extend_dict (("String", string_sort_marker),
        Library.extend_dict (("Bool", bool_sort_marker),
          Library.extend_dict (("Bag", bag_sort_marker),
            Library.extend_dict (("Set", set_sort_marker),
              Library.extend_dict (("as", as_sort_marker),
                Library.union_dict tmdict
                  SmtLib_Theories.Reals_Ints.tmdict)))))
      val tmdict = with_cpc_parameterized_skolems tmdict
      val tmdict = Library.extend_dict (("=", cpc_equality_parsefn),
        Library.extend_dict (("distinct", cpc_distinct_parsefn), tmdict))
    in
    (Library.extend_dict (("->", function_sort), tydict),
      Library.extend_dict (("str.++",
        cpc_concat_parsefn "smtstr_concat"),
      Library.extend_dict (("re.++",
        cpc_concat_parsefn "reglan_concat"),
      Library.extend_dict (("re.union",
        cpc_concat_parsefn "reglan_union"),
      Library.extend_dict (("re.inter",
        cpc_concat_parsefn "reglan_inter"),
      Library.extend_dict (("to_int", cpc_intreal_parsefn),
      Library.extend_dict (("to_real", cpc_intreal_parsefn),
      Library.extend_dict (("int.pow2", cpc_intreal_parsefn),
      Library.extend_dict (("div_total", cpc_arith_total_parsefn),
      Library.extend_dict (("mod_total", cpc_arith_total_parsefn),
      Library.extend_dict (("/_total", cpc_arith_total_parsefn),
      Library.extend_dict (("@int_div_by_zero", cpc_arith_total_parsefn),
      Library.extend_dict (("@mod_by_zero", cpc_arith_total_parsefn),
      Library.extend_dict (("@div_by_zero", cpc_arith_total_parsefn),
      Library.extend_dict (("**_total", cpc_arith_total_parsefn),
      Library.extend_dict (("bvsltbv", cpc_bv_parsefn),
      Library.extend_dict (("bvultbv", cpc_bv_parsefn),
      Library.extend_dict (("concat", cpc_bv_parsefn),
      Library.extend_dict (("@bit", cpc_bv_parsefn),
      Library.extend_dict (("@from_bools", cpc_bv_parsefn),
      Library.extend_dict (("@bvsize", cpc_bv_parsefn),
        Library.extend_dict (("@bv", cpc_bv_parsefn),
          Library.extend_dict (("_", cpc_literal_parsefn),
            with_cpc_fp_entries tmdict)))))))))))))))))))))))
    end

  fun parse_term dicts_ref raw_get_token =
    let
      (* Keep the lexical spelling through the shared term parser.  Its
         [symbol_key] callback selects the semantic dictionary key, while
         the marked spelling tells overload dispatch that a quoted atom may
         not fall through to the unquoted literal catch-all. *)
      val get_token = raw_get_token
      val first = get_token ()
      val first_semantic = cpc_semantic_token first
      fun ordinary tokens = SmtLib_Parser.parse_term_with_cfg cpc_cfg
        (Library.undo_look_ahead tokens get_token) (!dicts_ref)
    in
      if first_semantic <> "(" then ordinary [first]
      else
        let
          val marked_head = get_token ()
          val head = cpc_semantic_token marked_head
        in
          if head = "_" then
            let
              fun application_terms terms =
                let val token = get_token () in
                  if token = ")" then List.rev terms
                  else application_terms
                    (parse_term dicts_ref
                       (Library.undo_look_ahead [token] get_token) :: terms)
                end
            in
              case application_terms [] of
                function :: arguments =>
                  if List.null arguments then
                    raise ERR "parse_term"
                      "CPC `_` application expects an argument"
                  else Term.list_mk_comb (function, arguments)
              | [] => raise ERR "parse_term"
                  "CPC `_` application expects a function"
            end
          (* CPC declares [is] as a parameterized constant whose first
             explicit argument is a constructor symbol, rather than as the
             indexed identifier used by SMT-LIB.  Keep that symbol opaque
             until the datatype scrutinee has been typed; in particular, do
             not elaborate it as a nullary constructor application. *)
          else if head = "is" then
            let
              val constructor = get_token ()
              val _ =
                if constructor = "(" orelse constructor = ")" then
                  raise ERR "parse_term"
                    "CPC datatype tester expects a constructor symbol"
                else ()
              val scrutinee = parse_term dicts_ref get_token
              val _ = Library.expect_token ")" (get_token ())
              val constructor_parameter = Term.mk_var
                (cpc_symbol_name "parse_term" constructor,
                 Type.gen_tyvar ())
              val (_, tmdict) = !dicts_ref
            in
              SmtLib_Parser.apply_term tmdict "is"
                [constructor_parameter] [scrutinee]
            end
          else if head = "@var" then
            let
              val var_name = cpc_var_name (get_token ())
              val var_type = parse_cpc_type get_token
                (#1 (!dicts_ref))
              val _ = Library.expect_token ")" (get_token ())
            in
              Term.mk_var (var_name, var_type)
            end
          else if head = "forall" orelse head = "exists" orelse
                  head = "lambda" then
            let
              val binders = get_token ()
              fun bind vars body =
                let
                  val term =
                    if head = "forall" then
                      boolSyntax.list_mk_forall (vars, body)
                    else if head = "exists" then
                      boolSyntax.list_mk_exists (vars, body)
                    else Term.list_mk_abs (vars, body)
                  val _ = record_cpc_binder_block
                    (head, List.length vars, term)
                in
                  term
                end
            in
              case lookup_cpc_list binders of
                SOME vars =>
                  let
                    val body = parse_term dicts_ref get_token
                    val _ = Library.expect_token ")" (get_token ())
                  in
                    bind vars body
                  end
              | NONE =>
                  if binders = "(" then
                    let
                      val binder_head = get_token ()
                      fun inline_binders terms =
                        let val token = get_token () in
                          if token = ")" then List.rev terms
                          else inline_binders
                            (parse_term dicts_ref
                              (Library.undo_look_ahead [token] get_token) ::
                             terms)
                        end
                    in
                      if binder_head = "@list" then
                        let
                          val vars = inline_binders []
                          val body = parse_term dicts_ref get_token
                          val _ = Library.expect_token ")" (get_token ())
                        in
                          bind vars body
                        end
                      else ordinary
                        ["(", marked_head, binders, binder_head]
                    end
                  else raise ERR "parse_term"
                    ("undefined CPC @list alias " ^ binders ^
                     " (known aliases: " ^
                     String.concatWith ", " (List.rev (!cpc_list_names)) ^ ")")
            end
          else ordinary ["(", marked_head]
        end
    end

  datatype raw_term =
      RawAtom of string
    | RawList of raw_term list

  (* CPC represents a datatype tester as the parameterized application
       (is Constructor scrutinee)
     even when it occurs below equality or another proof argument.  The
     shared SMT-LIB parser deliberately accepts only the standard indexed
     spelling.  Normalize the complete raw occurrence tree before
     elaboration so nested CPC testers take the same registered dictionary
     path as ((_ is Constructor) scrutinee).  Malformed arities remain
     untouched and therefore retain the ordinary parser diagnostic. *)
  fun normalize_cpc_testers raw =
    case raw of
      RawList [RawAtom "is", RawAtom constructor, scrutinee] =>
        RawList
          [RawList [RawAtom "_", RawAtom "is", RawAtom constructor],
           normalize_cpc_testers scrutinee]
    | RawList [RawAtom "set.insert",
        RawList (RawAtom "@list" :: (elements as _ :: _)), set] =>
        (* CPC packs the variadic element operands in a syntax-only list. *)
        RawList (RawAtom "set.insert" ::
          List.map normalize_cpc_testers (elements @ [set]))
    | RawList [RawAtom "and"] => RawAtom "true"
    | RawList [RawAtom "or"] => RawAtom "false"
    | RawList [RawAtom "and", operand] =>
        normalize_cpc_testers operand
    | RawList [RawAtom "or", operand] =>
        normalize_cpc_testers operand
    | RawList entries => RawList (List.map normalize_cpc_testers entries)
    | RawAtom _ => raw

  fun read_raw_term get_token =
    case get_token () of
      "(" =>
        let
          fun entries acc =
            case get_token () of
              ")" => RawList (List.rev acc)
            | token => entries
                (read_raw_term
                  (Library.undo_look_ahead [token] get_token) :: acc)
        in
          entries []
        end
    | ")" => raise ERR "read_raw_term" "unexpected closing parenthesis"
    | token => RawAtom token

  fun raw_tokens raw =
    case raw of
      RawAtom token => [token]
    | RawList entries =>
        "(" :: List.concat (List.map raw_tokens entries) @ [")"]

  fun raw_contains_let raw =
    case raw of
      RawAtom _ => false
    | RawList (RawAtom "let" :: _) => true
    | RawList entries => List.exists raw_contains_let entries

  fun exact_application head operands =
    ApplicationProvenance (head, operands)

  fun exact_binders head names body =
    BinderBlockProvenance (head, List.length names, body)

  (* Equality endpoints are semantic inputs to omitted SYM, TRANS,
     EQ_RESOLVE, and CONG.  Retain their boundary even when both endpoints
     are conjunction-free; AtomicProvenance for the whole equality would
     erase which exact side an equality-consuming route selected. *)
  fun sparse_equality left right = EqualityProvenance (left, right)

  fun lookup_lexical_provenance environment name =
    let
      val key = provenance_key name
      fun lookup [] = NONE
        | lookup ((bound, provenance) :: rest) =
            if provenance_key bound = key then SOME provenance
            else lookup rest
    in
      lookup environment
    end

  fun binder_names raw =
    case raw of
      RawList (RawAtom "@list" :: binders) =>
        let
          fun binder_name (RawAtom alias) = alias
            | binder_name (RawList
                [RawAtom "@var", RawAtom name, _]) = cpc_var_name name
            | binder_name _ = raise ERR "provenance_of_raw"
                "unsupported CPC inline binder"
        in
          SOME (List.map binder_name binders)
          handle Feedback.HOL_ERR _ => NONE
        end
    | RawList binders =>
        let
          fun binder_name (RawList [RawAtom name, _]) = name
            | binder_name _ = raise ERR "provenance_of_raw"
                "unsupported SMT-LIB binder declaration"
        in
          SOME (List.map binder_name binders)
          handle Feedback.HOL_ERR _ => NONE
        end
    | RawAtom alias =>
        (case lookup_cpc_list alias of
           SOME variables =>
             (SOME (List.map (Lib.fst o Term.dest_var) variables)
              handle Feedback.HOL_ERR _ => NONE)
         | NONE => NONE)

  fun let_bindings environment raw =
    case raw of
      RawList bindings =>
        let
          fun binding (RawList [RawAtom name, rhs]) =
                (provenance_key name,
                 provenance_of_raw_in environment rhs)
            | binding _ = raise ERR "provenance_of_raw"
                "unsupported SMT-LIB let binding"
        in
          SOME (List.map binding bindings)
          handle Feedback.HOL_ERR _ => NONE
        end
    | _ => NONE

  and provenance_of_raw_in environment raw =
    case raw of
      RawAtom token =>
        (case lookup_lexical_provenance environment token of
           SOME provenance => provenance
         | NONE =>
             (case lookup_term_provenance token of
                SOME provenance => provenance
              | NONE => AtomicProvenance))
    | RawList (RawAtom "and" :: operands) =>
        if List.length operands >= 2 then
          ConjunctionProvenance
            (ParsedConjunction,
             List.map (provenance_of_raw_in environment) operands)
        else UnavailableProvenance
          "parsed CPC conjunction has fewer than two operands"
    | RawList [RawAtom "=", left, right] =>
        sparse_equality (provenance_of_raw_in environment left)
          (provenance_of_raw_in environment right)
    | RawList [RawAtom head, binders, body] =>
        if head = "forall" orelse head = "exists" orelse
           head = "lambda"
         then
          (case binder_names binders of
             SOME names => exact_binders head names
               (provenance_of_raw_in
                 (List.map (fn name =>
                    (provenance_key name, AtomicProvenance)) names @
                  environment) body)
           | NONE => UnavailableProvenance
               ("unsupported " ^ head ^ " binder provenance"))
        else if head = "let" then
          (case let_bindings environment binders of
             SOME bindings =>
               provenance_of_raw_in (bindings @ environment) body
           | NONE => UnavailableProvenance
               "unsupported SMT-LIB let provenance")
        else exact_application head
          [provenance_of_raw_in environment binders,
           provenance_of_raw_in environment body]
    | RawList (RawAtom head :: operands) =>
        if List.exists (fn private_name => private_name = head)
             ["@fp.SIGN", "@fp.EXPONENT", "@fp.SIGNIFICAND",
              "@fp.ZERO", "@fp.NAN", "@fp.INF",
              "@fp.RMBITBLAST"] then
          AtomicProvenance
        else if head = "match" orelse head = "par" then
          UnavailableProvenance
            ("unsupported binding form " ^ head)
        else if head = "@var" then AtomicProvenance
        else exact_application head
          (List.map (provenance_of_raw_in environment) operands)
    | RawList entries =>
        exact_application "<computed-head>"
          (List.map (provenance_of_raw_in environment) entries)

  fun provenance_of_raw raw = provenance_of_raw_in [] raw

  (* Read exactly one CPC occurrence before elaborating it to HOL.  The raw
     occurrence tree retains every path to a nested conjunction and every
     conjunction's exact operand boundaries.  Conjunction-free subtrees use
     one atomic marker; no HOL-term equality participates in provenance
     recovery. *)
  fun parse_located_term dicts_ref get_token : located_term =
    let
      val raw = normalize_cpc_testers (read_raw_term get_token)
      val tokens = ref (raw_tokens raw)
      fun next_token () =
        case !tokens of
          token :: rest => (tokens := rest; token)
        | [] => raise ERR "parse_located_term"
            "internal CPC occurrence token stream exhausted"
      val parsed_term = parse_term dicts_ref next_token
      val _ = List.null (!tokens) orelse
        raise ERR "parse_located_term"
          "internal CPC occurrence parser left trailing tokens"
      (* SMT-LIB lets elaborate to kernel LET applications, while the exact
         lexical provenance above already describes their simultaneous,
         capture-avoiding substitution.  Reduce precisely those occurrences
         before pairing the HOL term with that substituted occurrence tree.
         The conversion is proof-producing; aliases consequently store the
         same normalized term/provenance pair as direct commands. *)
      val term =
        if raw_contains_let raw then
          boolSyntax.rhs (Thm.concl
            (Conv.DEPTH_CONV pairLib.let_CONV parsed_term))
          handle Conv.UNCHANGED => parsed_term
        else parsed_term
    in
      {term = term, provenance = provenance_of_raw raw}
    end

  fun parse_recorded_term dicts_ref get_token =
    #term (parse_located_term dicts_ref get_token)

  fun unavailable_term reason term : located_term =
    {term = term, provenance = UnavailableProvenance reason}

  fun skip_sexp get_token =
    let
      fun skip depth =
        case get_token () of
          "(" => skip (depth + 1)
        | ")" => if depth = 0 then () else skip (depth - 1)
        | _ => skip depth
    in
      skip 0
    end

  (* Read the remainder of a declaration after its command name.  We use the
     token copy both to decide whether it redeclares a symbol already supplied
     by HolSmt's translation dictionaries and, when it does not, to feed the
     ordinary SMT-LIB declaration parsers. *)
  fun declaration_tokens get_token =
    let
      fun loop depth acc =
        let val token = get_token () in
          case token of
            "(" => loop (depth + 1) (token :: acc)
          | ")" => if depth = 0 then List.rev (token :: acc)
                   else loop (depth - 1) (token :: acc)
          | _ => loop depth (token :: acc)
        end
    in
      loop 0 []
    end

  fun datatype_binding_names tokens =
    let
      fun bindings ("(" :: name :: _ :: ")" :: rest) acc =
            bindings rest (name :: acc)
        | bindings (")" :: _) acc = List.rev acc
        | bindings _ _ = []
    in
      case tokens of "(" :: rest => bindings rest [] | _ => []
    end

  type term_declaration = {
    key: string,
    name: string,
    domain: Type.hol_type list,
    range: Type.hol_type,
    parse: Term.term SmtLib_Parser.parse_fn
  }

  fun parse_term_declaration parse_domain get_token (tydict, _) =
    let
      val marked_name = get_token ()
      val key = cpc_symbol_key "parse_declaration" marked_name
      val name = cpc_symbol_name "parse_declaration" marked_name
      val domain =
        if parse_domain then parse_cpc_type_list get_token tydict
        else []
      val range = parse_cpc_type get_token tydict
      val _ = Library.expect_token ")" (get_token ())
      val tm = Term.mk_var
        (name, boolSyntax.list_mk_fun (domain, range))
      fun parse _ indices args =
        if not (List.null indices) orelse
           (parse_domain andalso
            List.length args <> List.length domain) then
          raise ERR ("<" ^ name ^ ">")
            "wrong number of CPC declaration arguments"
        else
          Term.list_mk_comb (tm, args)
          handle Feedback.HOL_ERR holerr =>
            raise ERR ("<" ^ name ^ ">")
              ("ill-typed CPC declaration application: " ^
               Feedback.message_of holerr)
    in
      {key = key, name = name, domain = domain,
       range = range, parse = parse}
    end

  fun declaration_compatible tmdict
      ({key, domain, range, ...}: term_declaration) =
    let
      fun make_args _ [] = []
        | make_args index (ty :: rest) =
            Term.mk_var
              ("cpc_decl_arg" ^ Int.toString index, ty) ::
            make_args (index + 1) rest
      val signatures =
        if List.null domain andalso Lib.can Type.dom_rng range then
          let val (function_domain, function_range) =
            boolSyntax.strip_fun range
          in
            [([], range), (function_domain, function_range)]
          end
        else [(domain, range)]
      val candidates =
        case Redblackmap.peek (tmdict, key) of
          SOME parsefns => parsefns
        | NONE => []
      fun compatible_signature parsefn (argument_types, result_type) =
        Type.compare
          (Term.type_of
             (parsefn (SmtLib_Parser.proof_symbol_text key) []
               (make_args 0 argument_types)),
           result_type) = EQUAL
        handle Feedback.HOL_ERR _ => false
             | _ => false
      fun compatible parsefn =
        List.exists (compatible_signature parsefn) signatures
    in
      List.exists compatible candidates
    end

  fun parse_or_keep_term_declaration parse_domain dicts_ref get_token =
    let
      val tokens = declaration_tokens get_token
      val declaration = parse_term_declaration parse_domain
        (Library.undo_look_ahead tokens get_token) (!dicts_ref)
      val (tydict, tmdict) = !dicts_ref
      val {key, name, parse, ...} = declaration
      val source_symbol = set_member (!cpc_source_term_symbols) key
      val proof_symbol = set_member (!cpc_proof_term_symbols) key
      val builtin_symbol = set_member (!cpc_reserved_symbols) key orelse
        set_member (!cpc_reserved_symbols) name
      fun incompatible () = raise ERR "parse_declaration"
        ("incompatible redeclaration of CPC symbol " ^ name)
    in
      if builtin_symbol then
        raise ERR "parse_declaration"
          ("CPC declaration may not shadow builtin symbol " ^ name)
      else if proof_symbol then
        raise ERR "parse_declaration"
          ("duplicate CPC declaration of symbol " ^ name)
      else if source_symbol then
        if declaration_compatible tmdict declaration then ()
        else incompatible ()
      else if Option.isSome (Redblackmap.peek (tmdict, key)) then
        incompatible ()
      else
        (dicts_ref :=
           (tydict, Library.extend_dict ((key, parse), tmdict));
         cpc_proof_term_symbols :=
           HOLset.add (!cpc_proof_term_symbols, key))
    end

  val parse_declare_const = false
  val parse_declare_fun = true

  fun parse_declare_sort get_token (tydict, tmdict) =
    let
      val marked_name = get_token ()
      val key = cpc_symbol_key "parse_declare_sort" marked_name
      val name = cpc_symbol_name "parse_declare_sort" marked_name
      val arity_text = get_token ()
      val arity =
        case Int.fromString arity_text of
          SOME value =>
            if value < 0 then raise ERR "parse_declare_sort"
              "CPC sort arity must be non-negative"
            else value
        | NONE => raise ERR "parse_declare_sort"
            "CPC sort arity must be a numeral"
      val _ = Library.expect_token ")" (get_token ())
      val ty = Type.mk_vartype ("'cpc_" ^ name)
      fun parsefn _ indices args =
        if List.null indices andalso arity = 0 andalso List.null args then ty
        else raise ERR ("<" ^ name ^ ">") "wrong number of arguments"
    in
      {key = key, name = name, arity = arity, parse = parsefn,
       dicts = (tydict, tmdict)}
    end

  fun sort_declaration_compatible tydict key arity =
    let
      val arguments = List.tabulate (arity, fn index =>
        Type.mk_vartype ("'cpc_sort_arg" ^ Int.toString index))
    in
      case Redblackmap.peek (tydict, key) of
        NONE => false
      | SOME parsefns => List.exists
          (fn parsefn =>
            (ignore
               (parsefn (SmtLib_Parser.proof_symbol_text key) [] arguments);
             true)
            handle Feedback.HOL_ERR _ => false
                 | _ => false) parsefns
    end

  fun parse_or_keep_sort_declaration dicts_ref get_token =
    let
      val tokens = declaration_tokens get_token
      val declaration = parse_declare_sort
        (Library.undo_look_ahead tokens get_token) (!dicts_ref)
      val {key, name, arity, parse, dicts = (tydict, tmdict)} = declaration
      val source_symbol = set_member (!cpc_source_sort_symbols) key
      val proof_symbol = set_member (!cpc_proof_sort_symbols) key
      val builtin_symbol = set_member (!cpc_reserved_symbols) key orelse
        set_member (!cpc_reserved_symbols) name
    in
      if builtin_symbol then
        raise ERR "parse_declaration"
          ("CPC declaration may not shadow builtin sort " ^ name)
      else if proof_symbol then
        raise ERR "parse_declaration"
          ("duplicate CPC declaration of sort " ^ name)
      else if source_symbol then
        if sort_declaration_compatible tydict key arity then ()
        else raise ERR "parse_declaration"
          ("incompatible redeclaration of CPC sort " ^ name)
      else if arity <> 0 then
        raise ERR "parse_declaration"
          ("unsupported non-nullary CPC sort declaration " ^ name)
      else if Option.isSome (Redblackmap.peek (tydict, key)) then
        raise ERR "parse_declaration"
          ("incompatible redeclaration of CPC sort " ^ name)
      else
        (dicts_ref :=
           (Library.extend_dict ((key, parse), tydict), tmdict);
         cpc_proof_sort_symbols :=
           HOLset.add (!cpc_proof_sort_symbols, key))
    end

  type datatype_selector = {
    key: string,
    name: string,
    sort: raw_term
  }

  type datatype_constructor = {
    key: string,
    name: string,
    selectors: datatype_selector list
  }

  type datatype_declaration = {
    sort_key: string,
    sort_name: string,
    arity: int,
    params: string list,
    constructors: datatype_constructor list
  }

  fun all_chars predicate text =
    List.all predicate (String.explode text)

  fun valid_simple_symbol text =
    let
      fun letter c =
        (#"a" <= c andalso c <= #"z") orelse
        (#"A" <= c andalso c <= #"Z")
      fun initial c =
        letter c orelse List.exists (Lib.equal c)
          [#"~", #"!", #"@", #"$", #"%", #"^", #"&", #"*",
           #"_", #"-", #"+", #"=", #"<", #">", #".", #"?", #"/"]
    in
      String.size text > 0 andalso initial (String.sub (text, 0)) andalso
      all_chars (fn c => initial c orelse Char.isDigit c) text
    end

  fun datatype_symbol where_ role token =
    let
      val key = cpc_symbol_key where_ token
      val name = SmtLib_Parser.proof_symbol_text key
      val _ =
        case SmtLib_Parser.proof_quoted_symbol_token token of
          SOME _ => ()
        | NONE =>
            if valid_simple_symbol token andalso
               String.sub (token, 0) <> #":" then ()
            else raise ERR where_
              ("invalid " ^ role ^ " name '" ^ token ^ "'")
    in
      (key, name)
    end

  fun distinct_datatype_names where_ role names =
    let
      fun loop _ [] = ()
        | loop seen ((key, name) :: rest) =
            if set_member seen key then raise ERR where_
              ("duplicate " ^ role ^ " name " ^ name)
            else loop (HOLset.add (seen, key)) rest
    in
      loop (HOLset.empty String.compare) names
    end

  fun datatype_arity where_ name text =
    case Int.fromString text of
      SOME arity =>
        if arity >= 0 andalso all_chars Char.isDigit text andalso
           String.size text > 0 then arity
        else raise ERR where_
          ("datatype arity for '" ^ name ^ "' must be a natural numeral")
    | NONE => raise ERR where_
        ("datatype arity for '" ^ name ^ "' must be a natural numeral")

  fun parse_datatype_body where_ sort_key sort_name arity body =
    let
      val (param_tokens, constructor_raws) =
        case body of
          RawList [RawAtom "par", RawList params, RawList constructors] =>
            (params, constructors)
        | RawList (RawAtom "par" :: _) => raise ERR where_
            "parametric datatype body must be (par (params) (constructors))"
        | RawList constructors => ([], constructors)
        | RawAtom _ => raise ERR where_ "datatype body must be parenthesized"
      fun parameter raw =
        case raw of
          RawAtom token => datatype_symbol where_ "datatype parameter" token
        | RawList _ => raise ERR where_ "datatype parameter must be a symbol"
      val parameter_names = List.map parameter param_tokens
      val _ = distinct_datatype_names where_ "datatype parameter"
        parameter_names
      val _ =
        if List.length parameter_names = arity then ()
        else raise ERR where_
          ("datatype arity for '" ^ sort_name ^ "' is " ^
           Int.toString arity ^ " but its body has " ^
           Int.toString (List.length parameter_names) ^ " parameter(s)")
      fun selector raw : datatype_selector =
        case raw of
          RawList [RawAtom token, sort] =>
            let val (key, name) =
              datatype_symbol where_ "datatype selector" token
            in {key = key, name = name, sort = sort} end
        | _ => raise ERR where_
            "datatype selector must have the form (name sort)"
      fun constructor raw : datatype_constructor =
        case raw of
          RawList (RawAtom token :: selector_raws) =>
            let
              val (key, name) =
                datatype_symbol where_ "datatype constructor" token
              val selectors = List.map selector selector_raws
              val _ = distinct_datatype_names where_ "datatype selector"
                (List.map (fn ({key, name, ...}: datatype_selector) =>
                  (key, name)) selectors)
            in
              {key = key, name = name, selectors = selectors}
            end
        | _ => raise ERR where_
            "datatype constructor must be a nonempty parenthesized form"
      val _ = if List.null constructor_raws then
          raise ERR where_ "datatype constructor list must be nonempty"
        else ()
      val constructors = List.map constructor constructor_raws
      val _ = distinct_datatype_names where_ "datatype constructor"
        (List.map (fn ({key, name, ...}: datatype_constructor) =>
          (key, name)) constructors)
      val selector_names = List.concat (List.map
        (fn ({selectors, ...}: datatype_constructor) => List.map
          (fn ({key, name, ...}: datatype_selector) => (key, name))
          selectors) constructors)
      val _ = distinct_datatype_names where_ "datatype selector"
        selector_names
    in
      {sort_key = sort_key, sort_name = sort_name, arity = arity,
       params = List.map #1 parameter_names, constructors = constructors}
    end

  fun source_sort_type where_ tydict key arguments =
    let
      val candidates =
        case Redblackmap.peek (tydict, key) of
          SOME parsefns => parsefns
        | NONE => []
      fun first [] = raise ERR where_
            ("source datatype sort " ^
             SmtLib_Parser.proof_symbol_text key ^ " is unavailable")
        | first (parsefn :: rest) =
            (parsefn (SmtLib_Parser.proof_symbol_text key) [] arguments
             handle Feedback.HOL_ERR _ => first rest
                  | _ => first rest)
    in
      first candidates
    end

  fun validate_datatype_declarations dicts_ref declarations =
    let
      val (tydict, tmdict) = !dicts_ref
      val sort_names = List.map
        (fn ({sort_key, sort_name, ...}: datatype_declaration) =>
          (sort_key, sort_name)) declarations
      val _ = distinct_datatype_names "declare-datatypes" "datatype sort"
        sort_names
      val value_names = List.concat (List.map
        (fn ({constructors, ...}: datatype_declaration) =>
          List.concat (List.map
            (fn ({key, name, selectors}: datatype_constructor) =>
              (key, name) :: List.map
                (fn ({key, name, ...}: datatype_selector) => (key, name))
                selectors) constructors)) declarations)
      val _ = distinct_datatype_names "declare-datatypes"
        "datatype constructor/selector" value_names
      fun reject_sort ({sort_key, sort_name, arity, ...}:
          datatype_declaration) =
        if set_member (!cpc_reserved_symbols) sort_key orelse
           set_member (!cpc_reserved_symbols) sort_name then
          raise ERR "declare-datatypes"
            ("datatype may not shadow builtin sort " ^ sort_name)
        else if set_member (!cpc_proof_sort_symbols) sort_key then
          raise ERR "declare-datatypes"
            ("datatype sort conflicts with a proof declaration " ^ sort_name)
        else if not (set_member (!cpc_source_sort_symbols) sort_key) orelse
                not (sort_declaration_compatible tydict sort_key arity) then
          raise ERR "declare-datatypes"
            ("datatype sort is not identical to source sort " ^ sort_name)
        else ()
      val _ = List.app reject_sort declarations
      fun validate_one ({sort_key, sort_name, arity, params, constructors}:
          datatype_declaration) =
        let
          val param_tys = List.tabulate (arity, fn index =>
            Type.mk_vartype ("'cpc_datatype_param" ^ Int.toString index))
          val datatype_ty = source_sort_type "declare-datatypes" tydict
            sort_key param_tys
          val parameter_pairs = ListPair.zip (params, param_tys)
          fun add_parameter ((key, ty), dictionary) =
            let
              val name = SmtLib_Parser.proof_symbol_text key
              val _ =
                if set_member (!cpc_reserved_symbols) key orelse
                   set_member (!cpc_reserved_symbols) name orelse
                   set_member (!cpc_source_sort_symbols) key orelse
                   set_member (!cpc_proof_sort_symbols) key then
                  raise ERR "declare-datatypes"
                    ("datatype parameter shadows namespace symbol " ^ name)
                else ()
              fun parse _ indices arguments =
                if List.null indices andalso List.null arguments then ty
                else raise ERR "declare-datatypes"
                  ("datatype parameter " ^ name ^ " takes no arguments")
            in
              Library.extend_dict ((key, parse), dictionary)
            end
          val body_tydict = List.foldl add_parameter tydict parameter_pairs
          fun selector_type ({sort, ...}: datatype_selector) =
            let
              val tokens = ref (raw_tokens sort)
              fun next () =
                case !tokens of
                  token :: rest => (tokens := rest; token)
                | [] => raise ERR "declare-datatypes"
                    "datatype selector sort ended unexpectedly"
              val ty = parse_cpc_type next body_tydict
              val _ = if List.null (!tokens) then () else
                raise ERR "declare-datatypes"
                  "datatype selector sort has trailing syntax"
            in
              ty
            end
          fun constructor_domains ty =
            case Lib.total Type.dom_rng ty of
              NONE => []
            | SOME (domain, range) =>
                domain :: constructor_domains range
          val source_constructor_templates =
            TypeBase.constructors_of datatype_ty
            handle Feedback.HOL_ERR holerr =>
              raise ERR "declare-datatypes"
                ("source sort " ^ sort_name ^
                 " has no TypeBase datatype mapping: " ^
                 Feedback.message_of holerr)
          val source_constructors =
            List.map (TypeBasePure.cinst datatype_ty)
              source_constructor_templates
          val _ =
            if List.length constructors = List.length source_constructors
            then ()
            else raise ERR "declare-datatypes"
              ("datatype " ^ sort_name ^
               " constructor set is not identical to source: expected " ^
               Int.toString (List.length source_constructors) ^
               ", declared " ^ Int.toString (List.length constructors))
          fun require_source_symbol role key name =
            if set_member (!cpc_reserved_symbols) key orelse
               set_member (!cpc_reserved_symbols) name then
              raise ERR "declare-datatypes"
                ("datatype " ^ role ^ " may not shadow builtin symbol " ^
                 name)
            else if set_member (!cpc_proof_term_symbols) key then
              raise ERR "declare-datatypes"
                ("datatype " ^ role ^
                 " conflicts with a proof declaration " ^ name)
            else if not (set_member (!cpc_source_term_symbols) key) then
              raise ERR "declare-datatypes"
                ("datatype " ^ role ^
                 " is not identical to source symbol " ^ name)
            else ()
          fun parse_source role key name arguments =
            let
              val _ = require_source_symbol role key name
            in
              SmtLib_Parser.apply_term tmdict key [] arguments
              handle Feedback.HOL_ERR holerr =>
                raise ERR "declare-datatypes"
                  ("datatype " ^ role ^
                   " is not identical to source symbol " ^ name ^ ": " ^
                   Feedback.message_of holerr)
            end
          fun map_constructor
              ({key, name, selectors}: datatype_constructor) =
            let
              val _ = require_source_symbol "constructor" key name
              val declared_selector_tys = List.map selector_type selectors
              fun exact_parser_result constructor =
                let
                  val domains = constructor_domains
                    (Term.type_of constructor)
                  val arguments = Lib.mapi
                    (fn index => fn ty => Term.mk_var
                      ("cpc_datatype_argument" ^ Int.toString index, ty))
                    domains
                  val expected = Term.list_mk_comb (constructor, arguments)
                  val parsed =
                    SOME (SmtLib_Parser.apply_term tmdict key [] arguments)
                    handle Feedback.HOL_ERR _ => NONE
                in
                  case parsed of
                    SOME result => Term.aconv result expected
                  | NONE => false
                end
              fun probes_as (template, candidate) =
                if exact_parser_result template orelse
                   exact_parser_result candidate
                then SOME candidate
                else NONE
              val mappings = List.mapPartial probes_as
                (ListPair.zip
                  (source_constructor_templates, source_constructors))
              val source_constructor =
                case mappings of
                  [candidate] => candidate
                | _ => raise ERR "declare-datatypes"
                    ("datatype constructor " ^ name ^
                     " does not have one exact source parser mapping in " ^
                     sort_name)
              val source_selector_tys =
                constructor_domains (Term.type_of source_constructor)
              val _ =
                if List.length selectors = List.length source_selector_tys
                then ()
                else raise ERR "declare-datatypes"
                  ("datatype constructor " ^ name ^
                   " selector count is not identical to source: expected " ^
                   Int.toString (List.length source_selector_tys) ^
                   ", declared " ^ Int.toString (List.length selectors))
              val _ =
                if ListPair.allEq (fn (declared, source) =>
                     Type.compare (declared, source) = EQUAL)
                     (declared_selector_tys, source_selector_tys)
                then ()
                else raise ERR "declare-datatypes"
                  ("datatype constructor " ^ name ^
                   " has selector types different from its source")
            in
              (source_constructor, selectors, source_selector_tys)
            end
          val mapped_constructors = List.map map_constructor constructors
          fun same_constructor left right = Term.same_const left right
          fun unique_mapped [] = true
            | unique_mapped ((constructor, _, _) :: rest) =
                not (List.exists (fn (other, _, _) =>
                  same_constructor constructor other) rest) andalso
                unique_mapped rest
          val _ =
            if unique_mapped mapped_constructors andalso
               List.all (fn source_constructor =>
                 List.exists (fn (mapped, _, _) =>
                   same_constructor source_constructor mapped)
                   mapped_constructors) source_constructors
            then ()
            else raise ERR "declare-datatypes"
              ("datatype " ^ sort_name ^
               " constructor set is not identical to source")
          val scrutinee = Term.mk_var
            ("cpc_datatype_scrutinee", datatype_ty)
          fun validate_selectors
              (constructor, selectors, source_selector_tys) =
            let
              fun validate (index,
                  ({key, name, ...}: datatype_selector), source_range) =
                let
                  val parsed = parse_source "selector" key name [scrutinee]
                  val expected =
                    SmtLib_Parser.canonical_datatype_selector_case
                      constructor index scrutinee
                in
                  if Type.compare (Term.type_of parsed, source_range) = EQUAL
                     andalso Term.aconv parsed expected then ()
                  else raise ERR "declare-datatypes"
                    ("datatype selector " ^ name ^
                     " is not identical to source constructor/field " ^
                     "association " ^ Int.toString index)
                end
              val indexed = ListPair.zip
                (List.tabulate (List.length selectors, Lib.I),
                 ListPair.zip (selectors, source_selector_tys))
            in
              List.app (fn (index, (selector, source_range)) =>
                validate (index, selector, source_range)) indexed
            end
        in
          List.app validate_selectors mapped_constructors
        end
    in
      List.app validate_one declarations
    end

  fun parse_declare_datatype_command dicts_ref get_token =
    let
      val marked_name = get_token ()
      val (sort_key, sort_name) =
        datatype_symbol "declare-datatype" "datatype sort" marked_name
      val body = read_raw_term get_token
      val _ = Library.expect_token ")" (get_token ())
      val arity =
        case body of
          RawList [RawAtom "par", RawList params, RawList _] =>
            List.length params
        | _ => 0
      val declaration = parse_datatype_body "declare-datatype"
        sort_key sort_name arity body
    in
      validate_datatype_declarations dicts_ref [declaration]
    end

  fun parse_declare_datatypes_command dicts_ref get_token =
    let
      val bindings_raw = read_raw_term get_token
      val bodies_raw = read_raw_term get_token
      val _ = Library.expect_token ")" (get_token ())
      val bindings =
        case bindings_raw of
          RawList [] => raise ERR "declare-datatypes"
            "datatype sort binding list must be nonempty"
        | RawList entries => entries
        | RawAtom _ => raise ERR "declare-datatypes"
            "datatype sort bindings must be parenthesized"
      val bodies =
        case bodies_raw of
          RawList [] => raise ERR "declare-datatypes"
            "datatype body list must be nonempty"
        | RawList entries => entries
        | RawAtom _ => raise ERR "declare-datatypes"
            "datatype bodies must be parenthesized"
      val _ = if List.length bindings = List.length bodies then () else
        raise ERR "declare-datatypes"
          "datatype sort and body lists have different lengths"
      fun binding raw =
        case raw of
          RawList [RawAtom token, RawAtom arity_text] =>
            let
              val (key, name) = datatype_symbol "declare-datatypes"
                "datatype sort" token
            in
              (key, name,
               datatype_arity "declare-datatypes" name arity_text)
            end
        | _ => raise ERR "declare-datatypes"
            "datatype sort binding must have the form (name arity)"
      fun declaration ((key, name, arity), body) =
        parse_datatype_body "declare-datatypes" key name arity body
      val declarations = List.map declaration
        (ListPair.zip (List.map binding bindings, bodies))
    in
      validate_datatype_declarations dicts_ref declarations
    end

  fun parse_paren_name_list get_token =
    let
      fun loop acc =
        case get_token () of
          ")" => List.rev acc
        | name => loop (name :: acc)
      val first = get_token ()
    in
      if first = "(" then loop [] else [first]
    end

  fun parse_premise_ids get_token =
    List.map (cpc_id_key "parse_step" "premise ID")
      (parse_paren_name_list get_token)

  (* A CPC definition is a term alias, not a HOL hypothesis.  Resolving it in
     the parser preserves sharing without granting the solver any theorem. *)
  fun parse_define dicts_ref get_token =
    let
      val marked_name = get_token ()
      val key = cpc_symbol_key "parse_define" marked_name
      val name = cpc_symbol_name "parse_define" marked_name
      val _ =
        if set_member (!cpc_reserved_symbols) key orelse
           set_member (!cpc_reserved_symbols) name then
          raise ERR "parse_define"
            ("CPC definition may not shadow builtin symbol " ^ name)
        else if set_member (!cpc_proof_term_symbols) key then
          raise ERR "parse_define"
            ("duplicate CPC declaration or definition of symbol " ^ name)
        else if set_member (!cpc_source_term_symbols) key orelse
                Option.isSome (Redblackmap.peek (#2 (!dicts_ref), key)) then
          raise ERR "parse_define"
            ("CPC definition may not redefine source symbol " ^ name)
        else ()
      (* Most CPC definitions use SMT-LIB's ``()`` binder list, but cvc5
         also emits proof-local aliases without that list (notably for its
         @list bookkeeping values).  Both forms are nullary definitions. *)
      val definition_start = get_token ()
      val first =
        if definition_start = "(" then
          let val close = get_token () in
            if close = ")" then get_token ()
            else raise ERR "parse_define"
              "CPC parameterized definitions are unsupported"
          end
        else definition_start
      val defined_term =
        if first = "@list" then
          (* An unparenthesized @list is the same opaque resolution metadata
             as ``(@list ...)`` below. *)
          (skip_sexp get_token; NONE)
        else if first = "(" then
          let val head = get_token () in
            if head = "@list" then
              let
                fun list_terms acc =
                  let val token = get_token () in
                    if token = ")" then List.rev acc
                    else list_terms (parse_term dicts_ref
                      (Library.undo_look_ahead [token] get_token) :: acc)
                  end
                val terms = list_terms []
                val _ = add_cpc_list key terms
                val _ = Library.expect_token ")" (get_token ())
              in NONE end
            else if head = "@purify" then
              let
                val payload = parse_located_term dicts_ref get_token
                val _ = Library.expect_token ")" (get_token ())
              in
                (* CPC's purify definition names the payload and its
                   `skolem_intro` step exposes that definitional equality.
                   Keeping the alias avoids inventing an unconstrained HOL
                   variable for a proof-local sharing marker. *)
                SOME payload
              end
            else if head = "@var" then
              let
                val var_name = cpc_var_name (get_token ())
                val var_type = parse_cpc_type get_token
                  (#1 (!dicts_ref))
                val _ = Library.expect_token ")" (get_token ())
              in
                SOME {term = Term.mk_var (var_name, var_type),
                  provenance = AtomicProvenance}
              end
            else
              SOME (parse_located_term dicts_ref
                (Library.undo_look_ahead ["(", head] get_token))
          end
        else SOME (parse_located_term dicts_ref
          (Library.undo_look_ahead [first] get_token))
      val _ = case defined_term of
          SOME ({term, provenance} : located_term) =>
            let
              val term = intern_cpc_term term
            in
              Library.expect_token ")" (get_token ());
              add_term dicts_ref key term;
              add_term_provenance key provenance
            end
        | NONE => ()
      val _ = cpc_proof_term_symbols :=
        HOLset.add (!cpc_proof_term_symbols, key)
    in
      ()
    end

  fun duplicate_id id known_ids =
    HOLset.member (!known_ids, id)

  fun ensure_fresh_id where_ id known_ids =
    if duplicate_id id known_ids then
      raise ERR where_ ("duplicate CPC command ID " ^ id)
    else ()

  fun require_known_premise id known_ids premise =
    if HOLset.member (!known_ids, premise) then ()
    else raise ERR "parse_step"
      ("unknown premise ID '" ^ premise ^ "' in CPC step " ^ id)

  fun parse_step dicts_ref version known_ids record_unsupported get_token =
    let
      val id = cpc_id_key "parse_step" "command ID" (get_token ())
      val _ = ensure_fresh_id "parse_step" id known_ids
      val first = get_token ()
      (* CPC serializes the conclusion before [:rule].  Buffer exactly one
         raw term so rule dispatch can happen before SMT semantic parsing.
         Only an exact registered unsupported RARE rule may bypass semantic
         elaboration, and even that route validates the complete step below. *)
      val (raw_conclusion, attr) =
        if first = ":rule" then (NONE, first)
        else
          (SOME (read_raw_term
             (Library.undo_look_ahead [first] get_token)),
           get_token ())
      val _ = if attr = ":rule" then () else
        raise ERR "parse_step" "expected :rule"
      val rule_name = get_token ()
      val rule =
        case lookup_rule version rule_name of
          SOME rule => rule
        | NONE => raise ERR "parse_step"
            (registry_lookup_failure version rule_name)
      val unsupported_diagnostic =
        rare_unsupported_diagnostic rule_name
      (* Unsupported entries may contain symbols for which HOL deliberately
         has no dictionary entry.  They still have to be valid CPC steps:
         consume and check every premise/argument occurrence, every attribute,
         and the step's own closing delimiter before issuing the registered
         semantic diagnostic. *)
      fun structural_token context =
        get_token () handle SmtLib_Parser.CPCProofEOF =>
          raise ERR "parse_step"
            ("unexpected end of unsupported CPC step " ^ id ^ " " ^ context)
      (* This is a syntax-only CST validator.  Exact unsupported rules may
         mention operators that cannot be elaborated to HOL, but they do not
         get a weaker term language: applications, qualified identifiers,
         binders, lets, matches and annotations must still satisfy the
         SMT-LIB/CPC grammar accepted by this parser. *)
      fun raw_error detail = raise ERR "parse_step"
        ("malformed raw term in unsupported CPC step " ^ id ^ ": " ^
         detail)
      fun member token choices = List.exists (Lib.equal token) choices
      fun quoted_symbol token =
        SmtLib_Parser.proof_quoted_symbol_token token
      fun token_text token =
        Option.getOpt (quoted_symbol token, token)
      fun unquoted_is expected token =
        not (Option.isSome (quoted_symbol token)) andalso token = expected
      fun string_literal token =
        Option.isSome (SmtLib_Parser.proof_string_token token)
      val reserved =
        ["_", "!", "as", "let", "forall", "exists", "lambda",
         "match", "par"]
      fun all_chars predicate text =
        List.all predicate (String.explode text)
      fun ascii_letter c =
        (#"a" <= c andalso c <= #"z") orelse
        (#"A" <= c andalso c <= #"Z")
      fun simple_initial c =
        ascii_letter c orelse
        member c [#"~", #"!", #"@", #"$", #"%", #"^", #"&",
          #"*", #"_", #"-", #"+", #"=", #"<", #">", #".",
          #"?", #"/"]
      fun simple_symbol text =
        String.size text > 0 andalso
        simple_initial (String.sub (text, 0)) andalso
        all_chars (fn c => simple_initial c orelse Char.isDigit c) text
      fun keyword token =
        not (Option.isSome (quoted_symbol token)) andalso
        String.size token > 1 andalso String.sub (token, 0) = #":" andalso
        simple_symbol (String.extract (token, 1, NONE))
      fun digits text =
        String.size text > 0 andalso all_chars Char.isDigit text
      fun numeral text =
        text = "0" orelse
        (String.size text > 0 andalso String.sub (text, 0) <> #"0" andalso
         digits text)
      fun decimal text =
        case String.fields (Lib.equal #".") text of
          [whole, fraction] => numeral whole andalso digits fraction
        | _ => false
      fun radix_literal prefix predicate text =
        String.isPrefix prefix text andalso String.size text > 2 andalso
        all_chars predicate (String.extract (text, 2, NONE))
      fun hex_digit c =
        Char.isDigit c orelse (#"a" <= c andalso c <= #"f") orelse
        (#"A" <= c andalso c <= #"F")
      fun hexadecimal text =
        radix_literal "#x" hex_digit text
      fun binary text =
        radix_literal "#b" (fn c => c = #"0" orelse c = #"1") text
      fun unsigned_number text = numeral text orelse decimal text
      fun signed_number text =
        String.size text > 1 andalso String.sub (text, 0) = #"-" andalso
        unsigned_number (String.extract (text, 1, NONE))
      fun rational text =
        case String.fields (Lib.equal #"/") text of
          [numerator, denominator] =>
            (numeral numerator orelse signed_number numerator) andalso
            numeral denominator andalso denominator <> "0"
        | _ => false
      fun literal token =
        string_literal token orelse numeral token orelse decimal token orelse
        hexadecimal token orelse binary token orelse signed_number token orelse
        rational token
      fun valid_quoted text =
        (SmtLib_String_Literal.validate_lexical_text true text; true)
        handle SmtLib_String_Literal.InvalidStringLiteral _ => false
      fun validate_symbol description token =
        case SmtLib_Parser.proof_string_token token of
          SOME _ => raw_error
            ("string literal is not a valid " ^ description)
        | NONE =>
            (case quoted_symbol token of
               SOME text =>
                 if valid_quoted text then ()
                 else raw_error ("invalid quoted " ^ description)
             | NONE =>
                 if simple_symbol token andalso not (keyword token) andalso
                    not (member token reserved)
                 then ()
                 else raw_error
                   ("invalid " ^ description ^ " '" ^ token ^ "'"))
      val validate_identifier_symbol = validate_symbol
      fun validate_index raw =
        case raw of
          RawAtom token =>
            if Option.isSome (quoted_symbol token) then
              validate_symbol "indexed-identifier index" token
            else if numeral token then ()
            else validate_identifier_symbol
              "indexed-identifier index" token
        | RawList _ => raw_error "indexed-identifier index is not atomic"
      fun validate_simple_identifier description raw =
        case raw of
          RawAtom token => validate_identifier_symbol description token
        | RawList (RawAtom marker :: RawAtom name :: indices) =>
            if unquoted_is "_" marker then
              (validate_identifier_symbol
                 ("indexed " ^ description ^ " name") name;
               if List.null indices then
                 raw_error ("indexed " ^ description ^
                   " requires at least one index")
               else List.app validate_index indices)
            else raw_error
              (description ^ " is not a simple/indexed identifier")
        | RawList _ =>
            raw_error (description ^ " is not a simple/indexed identifier")
      fun validate_sort raw =
        case raw of
          RawAtom _ => validate_simple_identifier "sort identifier" raw
        | RawList (RawAtom marker :: RawAtom _ :: _) =>
            if unquoted_is "_" marker then
              validate_simple_identifier "sort identifier" raw
            else validate_sort_application raw
        | RawList [] => raw_error "empty sort"
        | RawList _ => validate_sort_application raw
      and validate_sort_application raw =
        case raw of
          RawList (head :: arguments) =>
            (validate_simple_identifier "sort application head" head;
             if List.null arguments then
               raw_error "sort application requires at least one argument"
             else List.app validate_sort arguments)
        | _ => raw_error "malformed sort application"
      fun validate_identifier raw =
        case raw of
          RawAtom _ => validate_simple_identifier "identifier" raw
        | RawList [RawAtom marker, identifier, sort] =>
            if unquoted_is "as" marker then
              (validate_simple_identifier "ascribed identifier" identifier;
               validate_sort sort)
            else if unquoted_is "_" marker then
              validate_simple_identifier "identifier" raw
            else raw_error
              "application head is not a qualified identifier"
        | RawList (RawAtom marker :: _) =>
            if unquoted_is "as" marker then
              raw_error
                "qualified identifier 'as' expects an identifier and sort"
            else if unquoted_is "_" marker then
              validate_simple_identifier "identifier" raw
            else raw_error
              "application head is not a qualified identifier"
        | RawList _ => raw_error
            "application head is not a qualified identifier"
      fun validate_sorted_variable raw =
        case raw of
          RawList [RawAtom name, sort] =>
            (validate_symbol "bound variable" name; validate_sort sort)
        | _ => raw_error
            "sorted variable must have the form (name sort)"
      fun validate_cpc_var name sort =
        (case SmtLib_Parser.proof_string_token name of
           SOME _ => ()
         | NONE => validate_symbol "bound variable" name;
         validate_sort sort)
      fun validate_binders binders =
        case binders of
          RawAtom alias => validate_symbol "CPC binder-list alias" alias
        | RawList (RawAtom marker :: variables) =>
            if unquoted_is "@list" marker then
              if List.null variables then
                raw_error "CPC binder list must be nonempty"
              else List.app (fn variable =>
                case variable of
                  RawAtom alias =>
                    validate_symbol "CPC bound-variable alias" alias
                | RawList [RawAtom var_marker, RawAtom name, sort] =>
                    if unquoted_is "@var" var_marker then
                      validate_cpc_var name sort
                    else raw_error
                      "CPC binder must be an alias or (@var name sort)"
                | _ => raw_error
                    "CPC binder must be an alias or (@var name sort)")
                variables
            else validate_sorted_variables binders
        | RawList _ => validate_sorted_variables binders
      and validate_sorted_variables binders =
        case binders of
          RawList variables =>
            if List.null variables then
              raw_error "sorted-variable list must be nonempty"
            else List.app validate_sorted_variable variables
        | _ => raw_error "sorted-variable list must be parenthesized"
      fun validate_pattern pattern =
        case pattern of
          RawAtom name => validate_symbol "match pattern" name
        | RawList (RawAtom constructor :: variables) =>
            (validate_symbol "match constructor" constructor;
             if List.null variables then
               raw_error "constructor pattern requires at least one variable"
             else List.app (fn variable => case variable of
                 RawAtom name => validate_symbol "match binder" name
               | RawList _ => raw_error "match binder is not atomic")
               variables)
        | RawList _ => raw_error "malformed match pattern"
      fun validate_sexp sexp =
        case sexp of
          RawAtom token =>
            if literal token orelse keyword token then ()
            else validate_symbol "annotation s-expression atom" token
        | RawList entries => List.app validate_sexp entries
      fun validate_attributes attributes =
        let
          fun loop [] = ()
            | loop (RawAtom attribute :: rest) =
                if not (keyword attribute) then
                  raw_error "annotation expects an attribute keyword"
                else
                  (case rest of
                     RawAtom next :: _ =>
                       if keyword next then loop rest
                       else (validate_sexp (List.hd rest);
                             loop (List.tl rest))
                   | RawList value :: tail =>
                       (validate_sexp (RawList value); loop tail)
                   | [] => ())
            | loop _ = raw_error "annotation expects an attribute keyword"
        in
          if List.null attributes then
            raw_error "annotation requires at least one attribute"
          else loop attributes
        end
      fun validate_application_arity head operands =
        let
          fun exact expected =
            if List.length operands = expected then ()
            else raw_error ("'" ^ head ^ "' expects exactly " ^
              Int.toString expected ^ " operand(s)")
          fun at_least expected =
            if List.length operands >= expected then ()
            else raw_error ("'" ^ head ^ "' expects at least " ^
              Int.toString expected ^ " operand(s)")
        in
          case head of
            "true" => raw_error "'true' must be an atomic term"
          | "false" => raw_error "'false' must be an atomic term"
          | "not" => exact 1
          | "ite" => exact 3
          | "=" => at_least 2
          | "distinct" => at_least 2
          | "=>" => at_least 2
          | "and" => at_least 2
          | "or" => at_least 2
          | "xor" => at_least 2
          | _ => at_least 1
        end
      fun validate_raw raw =
        case raw of
          RawAtom token =>
            if literal token then ()
            else validate_identifier_symbol "term identifier" token
        | RawList (RawAtom marked_head :: rest) =>
            let
              val head = token_text marked_head
              val special =
                not (Option.isSome (quoted_symbol marked_head))
              fun special_head name = special andalso head = name
            in
              if special_head "as" then
                (case rest of
                   [identifier, sort] =>
                     (validate_simple_identifier
                        "ascribed identifier" identifier;
                      validate_sort sort)
                 | _ => raw_error
                     ("qualified identifier 'as' expects an identifier " ^
                      "and sort"))
              else if special_head "_" then
                validate_simple_identifier "identifier" raw
              else if member head ["forall", "exists", "lambda"] andalso
                      special then
                (case rest of
                   [binders, body] =>
                     (validate_binders binders; validate_raw body)
                 | _ => raw_error ("malformed " ^ head ^ " binder"))
              else if special_head "let" then
                (case rest of
                   [RawList bindings, body] =>
                     (if List.null bindings then
                        raw_error "let requires at least one binding"
                      else List.app (fn binding => case binding of
                          RawList [RawAtom name, rhs] =>
                            (validate_symbol "let variable" name;
                             validate_raw rhs)
                        | _ => raw_error
                            "let binding must have the form (name term)")
                        bindings;
                      validate_raw body)
                 | _ => raw_error "malformed let term")
              else if special_head "!" then
                (case rest of
                   term :: attributes =>
                     (validate_raw term; validate_attributes attributes)
                 | [] => raw_error "annotation is missing its term")
              else if special_head "match" then
                (case rest of
                   [scrutinee, RawList branches] =>
                     (validate_raw scrutinee;
                      if List.null branches then
                        raw_error "match requires at least one branch"
                      else List.app (fn branch => case branch of
                          RawList [pattern, body] =>
                            (validate_pattern pattern; validate_raw body)
                        | _ => raw_error
                            "match branch must have pattern and body")
                          branches)
                 | _ => raw_error
                     "match expects a scrutinee and parenthesized branches")
              else if special_head "set.comprehension" then
                (case rest of
                   [binders as RawList (RawList _ :: _), predicate, value] =>
                     (validate_binders binders;
                      validate_raw predicate;
                      validate_raw value)
                 | _ =>
                     (validate_identifier_symbol
                        "application head" marked_head;
                      validate_application_arity head rest;
                      List.app validate_raw rest))
              else if special_head "@list" then List.app validate_raw rest
              else if special_head "@" then
                (case rest of
                   rator :: arguments =>
                     if List.null arguments then
                       raw_error "'@' expects a rator and at least one operand"
                     else
                       (validate_raw rator; List.app validate_raw arguments)
                 | [] => raw_error
                     "'@' expects a rator and at least one operand")
              else if special_head "@var" then
                (case rest of
                   [RawAtom name, sort] => validate_cpc_var name sort
                 | _ => raw_error "@var expects a name and sort")
              else if special_head "is" then
                (case rest of
                   [RawAtom constructor, scrutinee] =>
                     (validate_symbol "tester constructor" constructor;
                      validate_raw scrutinee)
                 | _ => raw_error
                     "CPC datatype tester expects a constructor and scrutinee")
              else
                (validate_identifier_symbol "application head" marked_head;
                 if special then validate_application_arity head rest else
                   if List.null rest then
                     raw_error
                       "function application requires at least one argument"
                   else ();
                 List.app validate_raw rest)
            end
        | RawList (head :: operands) =>
            (validate_identifier head;
             if List.null operands then
               raw_error "function application requires at least one argument"
             else List.app validate_raw operands)
        | RawList [] => raw_error "empty term"
      fun structural_premises () =
        let
          val _ = if structural_token "while reading :premises" = "("
            then ()
            else raise ERR "parse_step"
              ("expected parenthesized :premises in unsupported CPC step " ^
               id)
          fun ids () =
            case structural_token "while reading :premises" of
              ")" => ()
            | "(" => raise ERR "parse_step"
                ("invalid premise ID in unsupported CPC step " ^ id)
            | raw_premise =>
                let
                  val premise =
                    cpc_id_key "parse_step" "premise ID" raw_premise
                in
                  if HOLset.member (!known_ids, premise) then
                    ids ()
                  else raise ERR "parse_step"
                    ("unknown premise ID '" ^
                     SmtLib_Parser.proof_symbol_text raw_premise ^
                     "' in unsupported CPC step " ^ id)
                end
        in
          ids ()
        end
      fun structural_args () =
        let
          val _ = if structural_token "while opening :args" = "(" then ()
            else raise ERR "parse_step"
              ("expected parenthesized :args in unsupported CPC step " ^ id)
          fun terms () =
            case structural_token "while reading :args" of
              ")" => ()
            | token =>
                (validate_raw (read_raw_term
                   (Library.undo_look_ahead [token]
                     (fn () => structural_token "while reading :args")));
                 terms ())
        in
          terms ()
        end
      fun consume_unsupported seen_premises seen_args diagnostic =
        case structural_token "before its closing delimiter" of
          ")" => ()
        | ":premises" =>
            if seen_premises then raise ERR "parse_step"
              ("duplicate :premises in unsupported CPC step " ^ id)
            else (structural_premises ();
              consume_unsupported true seen_args diagnostic)
        | ":args" =>
            if seen_args then raise ERR "parse_step"
              ("duplicate :args in unsupported CPC step " ^ id)
            else (structural_args ();
              consume_unsupported seen_premises true diagnostic)
        | attribute => raise ERR "parse_step"
            ("unknown CPC step attribute " ^ attribute ^
             " in cvc5 version " ^ version)
      fun parse_supported () =
      let
      fun parse_buffered raw =
        parse_located_term dicts_ref
          (Library.undo_look_ahead (raw_tokens raw) (fn () =>
            raise ERR "parse_step"
              ("buffered conclusion ended early in CPC step " ^ id)))
      val conclusion = Option.map parse_buffered raw_conclusion
      fun attrs seen_premises seen_args premises args =
        case get_token () of
          ")" => {id = id,
                   conclusion = Option.map intern_located conclusion,
                   rule = rule, premises = premises,
                   args = List.map intern_located args}
        | ":premises" =>
            if seen_premises then raise ERR "parse_step"
              ("duplicate :premises in CPC step " ^ id)
            else
              let
                val premises = parse_premise_ids get_token
                val _ = List.app
                  (require_known_premise id known_ids) premises
              in
                attrs true seen_args premises args
              end
        | ":args" =>
            if seen_args then raise ERR "parse_step"
              ("duplicate :args in CPC step " ^ id)
            else
            let
              val _ = Library.expect_token "(" (get_token ())
              (* Resolution annotations such as @list are proof-search hints,
                 not premises of the kernel replay.  Preserve the rule step
                 while consuming their full s-expression syntax; this avoids
                 pretending that cvc5's private annotation vocabulary is an
                 SMT-LIB term language. *)
              fun ignore_terms () =
                let val token = get_token () in
                  if token = ")" then []
                  else (if token = "(" then skip_sexp get_token else ();
                        ignore_terms ())
                end
              fun resolution_args () =
                let
                  val first = get_token ()
                in
                  if first = ")" then []
                  else
                    let
                      (* ProofRule::RESOLUTION is annotated with the
                         polarity of its pivot in the first premise and the
                         pivot itself.  These are required to reconstruct
                         the (otherwise omitted) resolvent. *)
                      val polarity = parse_located_term dicts_ref
                        (Library.undo_look_ahead [first] get_token)
                      val pivot = parse_located_term dicts_ref get_token
                      val _ = ignore_terms ()
                    in [polarity, pivot] end
                end
              fun macro_resolution_args () =
                let
                  val first = get_token ()
                  fun parse_list_after_open () =
                    let
                      fun entries acc =
                        let val token = get_token () in
                          if token = ")" then List.rev acc
                          else entries (parse_located_term dicts_ref
                            (Library.undo_look_ahead [token] get_token) :: acc)
                        end
                    in entries [] end
                  fun parse_list token =
                    if token = "(" then
                      let
                        val _ = Library.expect_token "@list" (get_token ())
                      in parse_list_after_open () end
                    else
                      case lookup_cpc_list token of
                        SOME terms => List.map
                          (unavailable_term
                            "expanded CPC resolution-list alias") terms
                      | NONE => raise ERR "parse_step"
                          ("undefined CPC resolution @list alias " ^ token)
                in
                  if first = ")" then []
                  else
                    let
                      val target = parse_located_term dicts_ref
                        (Library.undo_look_ahead [first] get_token)
                      val next = get_token ()
                    in
                      if next = ")" then [target]
                      else
                        let
                          val polarities = parse_list next
                          val pivots = parse_list (get_token ())
                          val _ = Library.expect_token ")" (get_token ())
                        in target :: polarities @ pivots end
                    end
                end
              fun and_elim_index () =
                let
                  val text = get_token ()
                  val index =
                    case Int.fromString text of
                      SOME n => if n < 0 then raise ERR "parse_step"
                        "negative CPC and_elim index" else n
                    | NONE => raise ERR "parse_step"
                        ("non-numeral CPC and_elim index '" ^ text ^ "'")
                  val _ = Library.expect_token ")" (get_token ())
                in
                  [unavailable_term "CPC and_elim index metadata"
                    (intSyntax.mk_injected
                      (numSyntax.mk_numeral (Arbnum.fromInt index)))]
                end
              fun not_or_elim_index () =
                let
                  val text = get_token ()
                  val index =
                    case Int.fromString text of
                      SOME n => if n < 0 then raise ERR "parse_step"
                        "negative CPC not_or_elim index" else n
                    | NONE => raise ERR "parse_step"
                        ("non-numeral CPC not_or_elim index '" ^ text ^ "'")
                  val _ = Library.expect_token ")" (get_token ())
                in
                  [unavailable_term "CPC not_or_elim index metadata"
                    (intSyntax.mk_injected
                      (numSyntax.mk_numeral (Arbnum.fromInt index)))]
                end
              fun cnf_and_pos_args () =
                let
                  val first = get_token ()
                  val conjunction = parse_located_term dicts_ref
                    (Library.undo_look_ahead [first] get_token)
                  val text = get_token ()
                  val index =
                    case Int.fromString text of
                      SOME n => if n < 0 then raise ERR "parse_step"
                        "negative CPC cnf_and_pos index" else n
                    | NONE => raise ERR "parse_step"
                        ("non-numeral CPC cnf_and_pos index '" ^ text ^ "'")
                  val _ = Library.expect_token ")" (get_token ())
                in
                  [conjunction,
                   unavailable_term "CPC cnf_and_pos index metadata"
                     (intSyntax.mk_injected
                       (numSyntax.mk_numeral (Arbnum.fromInt index)))]
                end
              fun cnf_or_neg_args () =
                let
                  val first = get_token ()
                  val disjunction = parse_located_term dicts_ref
                    (Library.undo_look_ahead [first] get_token)
                  val text = get_token ()
                  val index =
                    case Int.fromString text of
                      SOME n => if n < 0 then raise ERR "parse_step"
                        "negative CPC cnf_or_neg index" else n
                    | NONE => raise ERR "parse_step"
                        ("non-numeral CPC cnf_or_neg index '" ^ text ^ "'")
                  val _ = Library.expect_token ")" (get_token ())
                in
                  [disjunction,
                   unavailable_term "CPC cnf_or_neg index metadata"
                     (intSyntax.mk_injected
                       (numSyntax.mk_numeral (Arbnum.fromInt index)))]
                end
              fun exists_elim_args () =
                let
                  val _ = Library.expect_token "(" (get_token ())
                  val _ = Library.expect_token "=" (get_token ())
                  val first = get_token ()
                  val (lhs, rhs) = if first = "(" then
                    let
                      val quantifier = get_token ()
                      val _ = if quantifier = "exists" then () else
                        raise ERR "parse_step"
                          "expected existential left side for exists-elim"
                      val binder_name = get_token ()
                      val binders =
                        case lookup_cpc_list binder_name of
                          SOME vars => vars
                        | NONE => raise ERR "parse_step"
                            ("undefined CPC @list alias " ^ binder_name)
                      val body = parse_term dicts_ref get_token
                      val _ = Library.expect_token ")" (get_token ())
                      val rhs = parse_term dicts_ref get_token
                    in (boolSyntax.list_mk_exists (binders, body), rhs) end
                    else
                      (parse_term dicts_ref
                         (Library.undo_look_ahead [first] get_token),
                       parse_term dicts_ref get_token)
                  val _ = Library.expect_token ")" (get_token ())
                  val _ = Library.expect_token ")" (get_token ())
                in
                  [unavailable_term
                    "CPC exists-elim argument reconstructed from metadata"
                    (boolSyntax.mk_eq (lhs, rhs))]
                end
              fun quant_rewrite_args () =
                let val first = get_token () in
                  if first <> "(" then
                    let
                      val proposition = parse_located_term dicts_ref
                        (Library.undo_look_ahead [first] get_token)
                      val _ = Library.expect_token ")" (get_token ())
                    in [proposition] end
                  else
                    let
                      val _ = Library.expect_token "=" (get_token ())
                      val _ = Library.expect_token "(" (get_token ())
                      val quantifier = get_token ()
                      val binder_name = get_token ()
                      val binders =
                        case lookup_cpc_list binder_name of
                          SOME vars => vars
                        | NONE => raise ERR "parse_step"
                            ("undefined CPC @list alias " ^ binder_name)
                      val body = parse_located_term dicts_ref get_token
                      val _ = Library.expect_token ")" (get_token ())
                      val rhs = parse_located_term dicts_ref get_token
                      val _ = Library.expect_token ")" (get_token ())
                      val _ = Library.expect_token ")" (get_token ())
                      val lhs = if quantifier = "forall" then
                        boolSyntax.list_mk_forall (binders, #term body)
                        else if quantifier = "exists" then
                          boolSyntax.list_mk_exists (binders, #term body)
                        else raise ERR "parse_step"
                          "expected quantified left side for CPC quantifier rewrite"
                      val _ = record_cpc_binder_block
                        (quantifier, List.length binders, lhs)
                      val binder_provenance = exact_binders quantifier binders
                        (#provenance body)
                    in
                      [{term = boolSyntax.mk_eq (lhs, #term rhs),
                        provenance = EqualityProvenance
                          (binder_provenance, #provenance rhs)}]
                    end
                end
              (* CPC Set rules carry their set sort as an argument, e.g.
                 [(Set Int)].  This is proof metadata, not a HOL term; retain
                 it only as a variable of the parsed sort so rule-specific
                 replay can ignore it without rejecting a recorded proof. *)
              fun sort_marker tokens =
                let val (tydict, _) = !dicts_ref in
                  Term.mk_var ("@cpc.sort",
                    parse_cpc_type
                      (Library.undo_look_ahead tokens get_token) tydict)
                end
              fun is_set_sort_metadata position =
                (rule_name = "sets-card-emp" andalso position = 2) orelse
                (rule_name = "sets-is-empty-elim" andalso position = 2) orelse
                (rule_name = "sets-member-emp" andalso position = 3) orelse
                (rule_name = "sets-minus-self" andalso position = 2)
              fun terms acc =
                let val token = get_token () in
                  if token = ")" then List.rev acc
                  else if token = "(" then
                    let val head = get_token () in
                      if head = "@list" then
                        (* Lists in CPC arguments carry a homogeneous
                           sequence of object terms (not a HOL list term).
                           Flatten them for handlers such as instantiate. *)
                        terms (List.revAppend
                          (List.map (unavailable_term
                            "expanded CPC argument-list syntax")
                            (list_terms []), acc))
                      else if head = "Set" andalso
                              is_set_sort_metadata (List.length acc + 1) then
                        let
                          val tm = sort_marker ["(", head]
                            handle Feedback.HOL_ERR holerr =>
                              raise ERR "parse_step"
                                ("could not parse Set sort metadata for CPC " ^
                                 "step " ^ id ^ " (rule " ^ rule_name ^ "): " ^
                                 Feedback.message_of holerr)
                        in terms
                          (unavailable_term "CPC Set sort metadata" tm :: acc)
                        end
                      else
                        let
                          val tm = parse_located_term dicts_ref
                            (Library.undo_look_ahead ["(", head] get_token)
                            handle Feedback.HOL_ERR holerr =>
                              raise ERR "parse_step"
                                ("could not parse :args for CPC step " ^ id ^
                                 " (rule " ^ rule_name ^ "): " ^
                                 Feedback.message_of holerr)
                        in terms (tm :: acc) end
                    end
                  else
                    (case lookup_cpc_list token of
                       SOME listed_terms =>
                         terms (List.revAppend
                           (List.map (unavailable_term
                             "expanded CPC argument-list alias") listed_terms,
                            acc))
                     | NONE =>
                         let
                           val tm = parse_located_term dicts_ref
                             (Library.undo_look_ahead [token] get_token)
                             handle Feedback.HOL_ERR holerr =>
                               raise ERR "parse_step"
                                 ("could not parse :args for CPC step " ^ id ^
                                  " (rule " ^ rule_name ^ "): " ^
                                  Feedback.message_of holerr)
                         in terms (tm :: acc) end)
                end
              and list_terms acc =
                let val token = get_token () in
                  if token = ")" then List.rev acc
                  else list_terms (parse_recorded_term dicts_ref
                    (Library.undo_look_ahead [token] get_token) :: acc)
                end
              fun cpc_list_term terms =
                case terms of
                  first :: rest =>
                    let
                      val element_type = Term.type_of first
                      val _ = List.all (fn term =>
                          Type.compare (Term.type_of term, element_type) =
                            EQUAL) rest orelse
                        raise ERR "parse_step"
                          ("CPC structured list has mixed element types in " ^
                           "step " ^ id ^ " (rule " ^ rule_name ^ ")")
                    in
                      listSyntax.mk_list (terms, element_type)
                    end
                | [] => listSyntax.mk_list
                    ([], Type.mk_vartype "'cpc_list")
              fun validate_set_sort_metadata args =
                let
                  fun check (set, marker) =
                    if Type.compare (Term.type_of set, Term.type_of marker) =
                         EQUAL then ()
                    else raise ERR "parse_step"
                      ("CPC Set sort metadata does not match its set argument " ^
                       "in step " ^ id ^ " (rule " ^ rule_name ^ ")")
                in
                  case (rule_name, args) of
                    ("sets-card-emp", [set, marker]) => check (set, marker)
                  | ("sets-is-empty-elim", [set, marker]) =>
                      check (set, marker)
                  | ("sets-member-emp", [_ , set, marker]) =>
                      check (set, marker)
                  | ("sets-minus-self", [set, marker]) => check (set, marker)
                  | _ => ()
                end
              fun structured_terms acc =
                let val token = get_token () in
                  if token = ")" then List.rev acc
                  else if token = "(" then
                    let val head = get_token () in
                      if head = "@list" then
                        structured_terms
                          (unavailable_term "CPC structured-list metadata"
                            (cpc_list_term (list_terms [])) :: acc)
                      else
                        let
                          val tm = parse_located_term dicts_ref
                            (Library.undo_look_ahead ["(", head]
                              get_token)
                        in structured_terms (tm :: acc) end
                    end
                  else
                    (case lookup_cpc_list token of
                       SOME listed_terms => structured_terms
                         (unavailable_term "CPC structured-list alias"
                           (cpc_list_term listed_terms) :: acc)
                     | NONE =>
                         let
                           val tm = parse_located_term dicts_ref
                             (Library.undo_look_ahead [token] get_token)
                         in structured_terms (tm :: acc) end)
                end
            in
              if rule_name = "resolution" then
                attrs seen_premises true premises (resolution_args ())
              else if #replay_handler rule = "resolution" then
                (* Macro/chain resolution gives its result clause first;
                   the remaining arguments only describe its pivots. *)
                attrs seen_premises true premises
                  (macro_resolution_args ())
              else if #replay_handler rule = "and_elim" then
                attrs seen_premises true premises (and_elim_index ())
              else if #replay_handler rule = "not_or_elim" then
                attrs seen_premises true premises (not_or_elim_index ())
              else if #replay_handler rule = "exists_elim" then
                attrs seen_premises true premises (exists_elim_args ())
              else if #replay_handler rule = "quant_rewrite" then
                attrs seen_premises true premises (quant_rewrite_args ())
              else if rule_name = "cnf_and_pos" then
                attrs seen_premises true premises (cnf_and_pos_args ())
              else if rule_name = "cnf_or_neg" then
                attrs seen_premises true premises (cnf_or_neg_args ())
              else if rule_name = "arith-mod-over-mod" orelse
                      rule_name = "arith-mod-over-mod-mult" then
                attrs seen_premises true premises (structured_terms [])
              else if #replay_handler rule = "rare_inventory" then
                (* Declarative RARE recipes distinguish one term from a
                   variadic list formal.  Preserve each CPC @list (and each
                   recorded alias for one) as exactly one HOL list wrapper;
                   the owning replay contract validates and unwraps it. *)
                attrs seen_premises true premises (structured_terms [])
              else
                let val args = terms [] in
                  (validate_set_sort_metadata
                    (List.map (fn (located : located_term) => #term located)
                      args);
                   attrs seen_premises true premises args)
                end
            end
        | attribute => raise ERR "parse_step"
            ("unknown CPC step attribute " ^ attribute ^
             " in cvc5 version " ^ version)
      in
        attrs false false [] []
      end
    in
      case unsupported_diagnostic of
        SOME diagnostic =>
          (Option.app validate_raw raw_conclusion;
           consume_unsupported false false diagnostic;
           record_unsupported (rule_name, diagnostic);
           (id, NONE))
      | NONE => (id, SOME (parse_supported ()))
    end

  fun parse_commands dicts_ref version known_ids scope_snapshots
      seen_steps record_unsupported get_token stop acc =
    let
      fun add_id id =
        (ensure_fresh_id "parse_commands" id known_ids;
         known_ids := HOLset.add (!known_ids, id))
      fun recurse acc =
        parse_commands dicts_ref version known_ids scope_snapshots
          seen_steps record_unsupported get_token stop acc
      fun same_tokens left right =
        ListPair.allEq (op =) (left, right)
      fun normalize_premise_ids tokens =
        let
          fun normal acc [] = List.rev acc
            | normal acc (":premises" :: "(" :: rest) =
                premises ("(" :: ":premises" :: acc) rest
            | normal acc (token :: rest) = normal (token :: acc) rest
          and premises acc [] = List.rev acc
            | premises acc (")" :: rest) = normal (")" :: acc) rest
            | premises acc (_ :: rest) =
                premises ("@premise" :: acc) rest
        in
          normal [] tokens
        end
      fun register_step_signature kind id tokens =
        let
          (* [tokens] starts with the raw command-ID token.  Use its already
             validated semantic key so normalized-identical scoped reuse is
             independent of equivalent quoted/unquoted spelling. *)
          val signature_tokens =
            kind :: id :: normalize_premise_ids (List.tl tokens)
        in
          case Redblackmap.peek (!seen_steps, id) of
            NONE => seen_steps :=
              Redblackmap.insert (!seen_steps, id, signature_tokens)
          | SOME known_tokens =>
              if same_tokens signature_tokens known_tokens then ()
              else raise ERR "parse_commands"
                ("duplicate CPC command ID " ^ id)
        end
      fun parse_recorded_step kind =
        let
          val consumed = ref ([] : string list)
          fun recording_token () =
            let val token = get_token () in
              consumed := token :: !consumed;
              token
            end
          val result as (id, _) =
            parse_step dicts_ref version known_ids record_unsupported
              recording_token
          val _ = register_step_signature kind id (List.rev (!consumed))
        in
          result
        end
      fun close_scope id =
        case !scope_snapshots of
          previous :: rest =>
            (known_ids := previous;
             scope_snapshots := rest;
             add_id id)
        | [] => raise ERR "parse_commands"
            ("step-pop without matching assume-push in CPC step " ^ id)
      val token =
        (SOME (get_token ()))
        handle SmtLib_Parser.CPCProofEOF => NONE
    in
      case token of
        NONE =>
          if stop then raise ERR "parse_commands"
            "unexpected end of nested CPC wrapper"
          else List.rev acc
      | SOME ")" =>
          if stop then List.rev acc
          else raise ERR "parse_commands"
            "unexpected closing delimiter at CPC top level"
      | SOME "(" =>
          let val head = get_token () in
            case head of
              "(" => raise ERR "parse_commands"
                "nested or second CPC proof wrapper is not permitted"
            | other =>
                if not stop then raise ERR "parse_commands"
                  "CPC command found outside a proof wrapper"
                else
                  case other of
                    "declare-const" =>
                      (parse_or_keep_term_declaration parse_declare_const
                         dicts_ref get_token;
                       recurse acc)
                  | "declare-fun" =>
                      (parse_or_keep_term_declaration parse_declare_fun
                         dicts_ref get_token;
                       recurse acc)
                  | "declare-sort" =>
                      (parse_or_keep_sort_declaration dicts_ref get_token;
                       recurse acc)
                  | "declare-datatype" =>
                      (parse_declare_datatype_command dicts_ref get_token;
                       recurse acc)
                  | "declare-datatypes" =>
                      (parse_declare_datatypes_command dicts_ref get_token;
                       recurse acc)
                  | "define" =>
                      (parse_define dicts_ref get_token;
                       recurse acc)
                  | "assume" =>
                      let
                        val id = cpc_id_key "parse_commands" "command ID"
                          (get_token ())
                        val _ = ensure_fresh_id "parse_commands" id known_ids
                        val tm = parse_located_term dicts_ref get_token
                        val _ = Library.expect_token ")" (get_token ())
                        val command = ASSUME (id, tm)
                        val _ = add_id id
                      in
                        recurse (command :: acc)
                      end
                  | "assume-push" =>
                      let
                        val id = cpc_id_key "parse_commands" "command ID"
                          (get_token ())
                        val _ = ensure_fresh_id "parse_commands" id known_ids
                        val tm = parse_located_term dicts_ref get_token
                        val _ = Library.expect_token ")" (get_token ())
                        val command = ASSUME_PUSH (id, tm)
                        val _ = scope_snapshots :=
                          !known_ids :: !scope_snapshots
                        val _ = add_id id
                      in
                        recurse (command :: acc)
                      end
                  | "step" =>
                      let
                        val (id, step) = parse_recorded_step "step"
                        val _ = add_id id
                      in
                        case step of
                          SOME step => recurse (STEP step :: acc)
                        | NONE => recurse acc
                      end
                  | "step-pop" =>
                      let
                        val (id, step) = parse_recorded_step "step-pop"
                        val _ = close_scope id
                      in
                        case step of
                          SOME step => recurse (STEP step :: acc)
                        | NONE => recurse acc
                      end
                  | _ => raise ERR "parse_commands"
                      ("unknown CPC construct " ^ other ^
                       " in cvc5 version " ^ version)
          end
      | SOME other => raise ERR "parse_commands"
          ("unexpected CPC token '" ^
           SmtLib_Parser.proof_symbol_text other ^ "'")
    end
in
  val intern_cpc_term = intern_cpc_term
  val cpc_indexed_term_registry = cpc_indexed_term_registry
  val with_cpc_deindexed_entries = with_cpc_deindexed_entries
  val cpc_parameterized_skolem_names = cpc_parameterized_skolem_names
  val cpc_parameterized_skolem_for_test =
    cpc_parameterized_skolem_for_test
  val cpc_re_unfold_pos_decomposition = cpc_re_unfold_pos_decomposition
  val cpc_re_unfold_pos_regexps = cpc_re_unfold_pos_regexps
  val cpc_re_unfold_pos_component = cpc_re_unfold_pos_component
  type cpc_fp_private_binding = cpc_fp_private_binding
  val cpc_fp_private_bindings = cpc_fp_private_bindings

  fun parse_stream_with_version (dicts : dicts) version instream : proof =
    let
      (* Resolve once, here: everything downstream -- rule lookup, gating and
         diagnostics -- then works with a tested version. *)
      val version = resolve_version version
      val _ = cpc_list_definitions := Redblackmap.mkDict String.compare
      val _ = cpc_list_names := []
      val _ = cpc_fp_private_bindings_ref := []
      val _ = cpc_fp_private_unbound_count := 0
      val _ = cpc_term_provenances := Redblackmap.mkDict String.compare
      val _ = cpc_term_intern :=
        Array.array (term_intern_bucket_count, [])
      val _ = cpc_forall_blocks := []
      fun keys dictionary = Redblackmap.foldl
        (fn (key, _, set) => HOLset.add (set, key))
        (HOLset.empty String.compare) dictionary
      val (all_tydict, all_tmdict) =
        SmtLib_Logics.parsedicts_of_logic "ALL"
      val baseline_dicts = with_cpc_literals
        (all_tydict, Library.union_dict all_tmdict
          SmtLib_Theories.CVC5_Seq.tmdict)
      val baseline = HOLset.union
        (keys (#1 baseline_dicts), keys (#2 baseline_dicts))
      val syntax_names =
        ["_", "!", "as", "let", "forall", "exists", "lambda",
         "match", "par", "declare-const", "declare-fun",
         "declare-sort", "declare-datatype", "declare-datatypes",
         "define", "assume", "assume-push", "step", "step-pop"]
      val _ = cpc_reserved_symbols := HOLset.addList
        (baseline, syntax_names)
      fun source_keys dictionary = HOLset.filter
        (fn key => not (set_member (!cpc_reserved_symbols) key))
        (keys dictionary)
      val _ = cpc_source_sort_symbols := source_keys (#1 dicts)
      val _ = cpc_source_term_symbols := source_keys (#2 dicts)
      val _ = cpc_proof_sort_symbols := HOLset.empty String.compare
      val _ = cpc_proof_term_symbols := HOLset.empty String.compare
      val known_ids = ref (HOLset.empty String.compare)
      val scope_snapshots = ref ([] : string HOLset.set list)
      val seen_steps = ref
        (Redblackmap.mkDict String.compare :
          (string, string list) Redblackmap.dict)
      val pending = ref (NONE : (string * string) option)
      fun record_unsupported diagnostic =
        case !pending of
          NONE => pending := SOME diagnostic
        | SOME _ => ()
      (* CPC conclusions and arguments can contain SMT-LIB string literals.
         Preserve token kind and apply cvc5's proof lexical policy. *)
      val get_token =
        SmtLib_Parser.make_cpc_proof_stream_tokenizer instream
      val _ =
        (Library.expect_token "(" (get_token ()))
        handle SmtLib_Parser.CPCProofEOF =>
          raise ERR "parse_stream_with_version"
            "unexpected end before CPC proof wrapper"
      val commands =
        parse_commands (ref (with_cpc_literals dicts)) version known_ids
          scope_snapshots seen_steps record_unsupported get_token true []
        handle SmtLib_Parser.CPCProofEOF =>
          raise ERR "parse_stream_with_version"
            "unexpected end of CPC proof wrapper"
      val _ = List.null (!scope_snapshots) orelse
        raise ERR "parse_stream_with_version"
          "unclosed assume-push scope at end of CPC proof wrapper"
      val trailing =
        (SOME (get_token ()))
        handle SmtLib_Parser.CPCProofEOF => NONE
      val _ =
        case trailing of
          NONE => ()
        | SOME token => raise ERR "parse_stream_with_version"
            ("second CPC proof wrapper or trailing token '" ^
             SmtLib_Parser.proof_symbol_text token ^ "'")
      val _ =
        case !pending of
          SOME (rule_name, diagnostic) => raise ERR rule_name diagnostic
        | NONE => ()
    in
      {commands = commands, cvc_version = version}
    end

  fun parse_stream dicts instream =
    parse_stream_with_version dicts unknown_cvc_version instream

end

end
