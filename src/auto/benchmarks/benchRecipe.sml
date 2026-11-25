structure benchRecipe :> benchRecipe =
struct

open HolKernel

datatype modifier =
    SimpAdd of string list
  | SimpDelete of string list
  | Split of string list
  | Intro of benchLib.rule_strength * string list
  | Elim of benchLib.rule_strength * string list
  | Dest of benchLib.rule_strength * string list
  | Cong of string list
  | Facts of string list

type method = {
  name : string,
  modifiers : modifier list,
  repeated : bool
}

type parsed = {
  facts : string list,
  unfolded : string list,
  methods : method list
}

exception Unparseable of string * string

(* ------------------------------------------------------------------ *)
(* Scanning                                                            *)
(* ------------------------------------------------------------------ *)

datatype token =
    Word of string | Key of string | LParen | RParen | Plus

fun is_ident_char c =
  Char.isAlphaNum c orelse c = #"_" orelse c = #"." orelse c = #"'"
  orelse c = #"?"

fun drop_comments source =
  let
    fun body [] acc = List.rev acc
      | body (#"(" :: #"*" :: rest) acc = comment rest acc
      | body (c :: rest) acc = body rest (c :: acc)
    and comment (#"*" :: #")" :: rest) acc = body rest acc
      | comment (_ :: rest) acc = comment rest acc
      | comment [] acc = List.rev acc
  in
    body (String.explode source) []
  end

(* An attribute is bracket-balanced and may quote an Isabelle term, so
   brackets inside quotes do not count. *)
fun read_attribute source chars =
  let
    fun go [] _ _ _ = raise Unparseable (source, "unterminated attribute")
      | go (#"\"" :: rest) depth quoted acc =
          go rest depth (not quoted) (#"\"" :: acc)
      | go (c :: rest) depth true acc = go rest depth true (c :: acc)
      | go (#"]" :: rest) 1 _ acc =
          (String.implode (List.rev (#"]" :: acc)), rest)
      | go (#"]" :: rest) depth _ acc = go rest (depth - 1) false (#"]" :: acc)
      | go (#"[" :: rest) depth _ acc = go rest (depth + 1) false (#"[" :: acc)
      | go (c :: rest) depth _ acc = go rest depth false (c :: acc)
  in
    go chars 0 false []
  end

fun collapse text = String.concatWith " " (String.tokens Char.isSpace text)

fun scan source =
  let
    val chars = drop_comments source
    fun skip_spaces (c :: rest) =
          if Char.isSpace c then skip_spaces rest else c :: rest
      | skip_spaces [] = []
    fun attribute_of rest =
      let val trimmed = skip_spaces rest
      in
        case trimmed of
            #"[" :: _ =>
              let val (text, after) = read_attribute source trimmed
              in (collapse text, after)
              end
          | _ => ("", rest)
      end
    fun span (c :: rest) acc =
          if is_ident_char c then span rest (c :: acc)
          else (List.rev acc, c :: rest)
      | span [] acc = (List.rev acc, [])
    (* [list.distinct(1)] indexes one equation of a multi-clause fact.
       Only digits read as an index, so [by(auto ...)] still opens a
       method rather than extending the name [by]. *)
    fun fact_index chars =
      let
        fun digits (c :: rest) acc =
              if Char.isDigit c then digits rest (c :: acc)
              else (List.rev acc, c :: rest)
          | digits [] acc = (List.rev acc, [])
      in
        case chars of
            #"(" :: rest =>
              (case digits rest [] of
                   ([], _) => ("", chars)
                 | (index, #")" :: after) =>
                     ("(" ^ String.implode index ^ ")", after)
                 | _ => ("", chars))
          | _ => ("", chars)
      end
    fun go [] acc = List.rev acc
      | go (c :: rest) acc =
          if Char.isSpace c then go rest acc
          else if c = #"(" then go rest (LParen :: acc)
          else if c = #")" then go rest (RParen :: acc)
          else if c = #"+" then go rest (Plus :: acc)
          else if is_ident_char c then
            let
              val (letters, rest') = span (c :: rest) []
              val name = String.implode letters
            in
              case rest' of
                  #":" :: after => go after (Key (name ^ ":") :: acc)
                | #"!" :: #":" :: after => go after (Key (name ^ "!:") :: acc)
                | _ =>
                    let
                      val (index, rest'') = fact_index rest'
                      val (attribute, after) = attribute_of rest''
                    in go after (Word (name ^ index ^ attribute) :: acc)
                    end
            end
          else
            raise Unparseable
              (source, "unexpected character " ^ Char.toString c)
  in
    go chars []
  end

(* ------------------------------------------------------------------ *)
(* Parsing                                                             *)
(* ------------------------------------------------------------------ *)

(* [by], [using] and [unfolding] are never lemma names, so a name list
   ends where one of them starts. *)
fun is_keyword name =
  name = "by" orelse name = "using" orelse name = "unfolding"

(* [simp] is a lemma name nowhere in the corpus, but it is the first
   half of the two-token [simp add:] and [simp del:] spellings, so a name
   list ends there too. *)
fun starts_modifier (Word "simp" :: Key "add:" :: _) = true
  | starts_modifier (Word "simp" :: Key "del:" :: _) = true
  | starts_modifier (Word "simp" :: Key "flip:" :: _) = true
  | starts_modifier _ = false

fun words tokens =
  let
    fun go (tokens as Word name :: rest) acc =
          if is_keyword name orelse starts_modifier tokens then
            (List.rev acc, tokens)
          else go rest (name :: acc)
      | go rest acc = (List.rev acc, rest)
  in
    go tokens []
  end

(* [add:] is a simpset entry for every method that spells it. *)
fun modifier_of source head key names =
  case key of
      "add:" => SimpAdd names
    | "del:" => SimpDelete names
    | "simp:" => SimpAdd names
    | "split:" => Split names
    | "intro:" => Intro (benchLib.UnsafeRule, names)
    | "intro!:" => Intro (benchLib.SafeRule, names)
    | "elim:" => Elim (benchLib.UnsafeRule, names)
    | "elim!:" => Elim (benchLib.SafeRule, names)
    | "dest:" => Dest (benchLib.UnsafeRule, names)
    | "dest!:" => Dest (benchLib.SafeRule, names)
    | "cong:" => Cong names
    | _ => raise Unparseable (source, "unknown modifier " ^ key)

fun flipped name = name ^ "[symmetric]"

(* A modifier that names nothing is a parse failure, not an empty list. *)
fun named source key tokens =
  let val (names, rest) = words tokens
  in
    if null names then raise Unparseable (source, key ^ " names nothing")
    else (names, rest)
  end

fun parse_modifiers source head tokens =
  let
    fun go tokens acc =
      case tokens of
          [] => raise Unparseable (source, "unclosed method")
        | RParen :: rest => (List.rev acc, rest)
        (* [simp add:] and [simp del:] are the two-token spellings. *)
        | Word "simp" :: Key "add:" :: rest =>
            let val (names, rest') = named source "simp add:" rest
            in go rest' (SimpAdd names :: acc)
            end
        | Word "simp" :: Key "del:" :: rest =>
            let val (names, rest') = named source "simp del:" rest
            in go rest' (SimpDelete names :: acc)
            end
        (* [simp flip: X] is [simp add:] of X read right to left. *)
        | Word "simp" :: Key "flip:" :: rest =>
            let val (names, rest') = named source "simp flip:" rest
            in go rest' (SimpAdd (map flipped names) :: acc)
            end
        | Key key :: rest =>
            let val (names, rest') = named source key rest
            in go rest' (modifier_of source head key names :: acc)
            end
        (* [metis A B] keys nothing: the names are the method's facts. *)
        | Word _ :: _ =>
            let val (names, rest') = named source "the method" tokens
            in go rest' (Facts names :: acc)
            end
        | _ => raise Unparseable (source, "unexpected token in method")
  in
    go tokens []
  end

fun parse_method source tokens =
  let
    fun repetition (Plus :: rest) = (true, rest)
      | repetition rest = (false, rest)
    fun built name modifiers rest =
      let val (repeated, rest') = repetition rest
      in ({name = name, modifiers = modifiers, repeated = repeated}, rest')
      end
  in
    case tokens of
        Word name :: rest => built name [] rest
      | LParen :: Word name :: rest =>
          let val (modifiers, rest') = parse_modifiers source name rest
          in built name modifiers rest'
          end
      | _ => raise Unparseable (source, "expected a method")
  end

fun parse source =
  let
    val tokens = scan source
    fun prefix tokens facts unfolded =
      case tokens of
          Word "using" :: rest =>
            let val (names, rest') = words rest
            in prefix rest' (facts @ names) unfolded
            end
        | Word "unfolding" :: rest =>
            let val (names, rest') = words rest
            in prefix rest' facts (unfolded @ names)
            end
        | Word "by" :: rest => (facts, unfolded, rest)
        | _ => raise Unparseable (source, "no [by] method")
    val (facts, unfolded, rest) = prefix tokens [] []
    fun methods_of [] acc = List.rev acc
      | methods_of tokens acc =
          let val (method, rest) = parse_method source tokens
          in methods_of rest (method :: acc)
          end
    val methods = methods_of rest []
  in
    if null methods then raise Unparseable (source, "[by] names no method")
    else {facts = facts, unfolded = unfolded, methods = methods}
  end

(* ------------------------------------------------------------------ *)
(* Rendering                                                           *)
(* ------------------------------------------------------------------ *)

fun render_modifier head modifier =
  let
    fun spelled key names = key ^ " " ^ String.concatWith " " names
    (* [simp] spells its own simpset modifiers [add:] and [del:]; every
       other method prefixes them with [simp]. *)
    val simp_prefix = if head = "simp" then "" else "simp "
  in
    case modifier of
        SimpAdd names => spelled (simp_prefix ^ "add:") names
      | SimpDelete names => spelled (simp_prefix ^ "del:") names
      | Split names => spelled "split:" names
      | Intro (benchLib.UnsafeRule, names) => spelled "intro:" names
      | Intro (benchLib.SafeRule, names) => spelled "intro!:" names
      | Elim (benchLib.UnsafeRule, names) => spelled "elim:" names
      | Elim (benchLib.SafeRule, names) => spelled "elim!:" names
      | Dest (benchLib.UnsafeRule, names) => spelled "dest:" names
      | Dest (benchLib.SafeRule, names) => spelled "dest!:" names
      | Cong names => spelled "cong:" names
      | Facts names => String.concatWith " " names
  end

fun render_method ({name, modifiers, repeated} : method) =
  (if null modifiers then name
   else
     "(" ^ name ^ " " ^
     String.concatWith " " (map (render_modifier name) modifiers) ^ ")") ^
  (if repeated then "+" else "")

fun render ({facts, unfolded, methods} : parsed) =
  let
    fun clause keyword names =
      if null names then []
      else [keyword ^ " " ^ String.concatWith " " names]
  in
    String.concatWith " "
      (clause "using" facts @ clause "unfolding" unfolded @
       ["by " ^ String.concatWith " " (map render_method methods)])
  end

(* ------------------------------------------------------------------ *)
(* Cited names                                                         *)
(* ------------------------------------------------------------------ *)

fun modifier_names modifier =
  case modifier of
      SimpAdd names => names
    | SimpDelete names => names
    | Split names => names
    | Intro (_, names) => names
    | Elim (_, names) => names
    | Dest (_, names) => names
    | Cong names => names
    | Facts names => names

fun distinct [] = []
  | distinct (item :: rest) =
      item :: distinct (List.filter (not o equal item) rest)

fun cited_names ({facts, unfolded, methods} : parsed) =
  distinct
    (facts @ unfolded @
     List.concat
       (map (List.concat o map modifier_names o #modifiers) methods))

fun method_heads ({methods, ...} : parsed) = map #name methods

(* ------------------------------------------------------------------ *)
(* Recipe construction                                                 *)
(* ------------------------------------------------------------------ *)

type resolver = {
  theorems : string -> benchLib.named_thm list,
  normalised_subject : string -> bool,
  tactic : string -> benchLib.tactic_id,
  ambient : string -> benchLib.method_arg list
}

(* A deletion names a simpset entry, not a theorem: the display name of
   the theorem it resolves to, spelled the way simpLib spells it. *)
fun deletion_names resolve name =
  map (fn ({name = display, ...} : benchLib.named_thm) =>
        String.map (fn c => if c = #"$" then #"." else c) display)
    (resolve name)

(* Which of the two rewrite constructors a citation takes is the
   resolver's answer about the rule, so every goal naming that rule
   installs it the same way, and every place a citation becomes a
   rewrite asks the same question. *)
fun rewritten resolve normalised_subject names =
  let
    fun constructor name =
      if normalised_subject name then benchLib.RewriteAddBottomUp
      else benchLib.RewriteAdd
  in
    List.concat
      (map (fn name => map (constructor name) (resolve name)) names)
  end

fun argument_of resolve normalised_subject modifier =
  let
    fun each build names =
      List.concat (map (fn name => map build (resolve name)) names)
  in
    case modifier of
        SimpAdd names => rewritten resolve normalised_subject names
      | SimpDelete names =>
          map benchLib.RewriteDelete
            (List.concat (map (deletion_names resolve) names))
      | Split names => each benchLib.SplitAdd names
      | Intro (strength, names) =>
          each (fn thm => benchLib.IntroAdd (strength, thm)) names
      | Elim (strength, names) =>
          each (fn thm => benchLib.ElimAdd (strength, thm)) names
      | Dest (strength, names) =>
          each (fn thm => benchLib.DestAdd (strength, thm)) names
      | Cong names => each benchLib.CongruenceAdd names
      | Facts names => each benchLib.FactAdd names
  end

(* Isabelle's [OF assms] cites a fact already resolved against the
   enclosing lemma's assumptions, and that resolution fixes what the
   fact's own statement quantifies: [split_list_prop [OF assms]] is the
   fact at the goal's list and the goal's predicate, where the fact as
   stated quantifies both.  The translation writes a lemma's
   assumptions as its goal's leading antecedents, so the instance is
   read off the goal rather than transcribed -- one rule for every
   citation of the form, and no per-goal field.  Premises and
   antecedents are matched in the order both are written, and the
   longest prefix that matches decides how many of them [assms]
   discharges.

   Isabelle discharges the premises it resolves; they stay here, where
   the goal's own antecedent is what discharges them, so the argument
   says no more than the citation does.  A citation whose first premise
   matches no antecedent is an error naming it: supplying the fact as
   stated instead is the silent fallback B1 forbids. *)
val assumption_resolution = "[OF assms]"

fun leading_implications term =
  if boolSyntax.is_imp_only term then
    let val (left, right) = boolSyntax.dest_imp term
    in left :: leading_implications right end
  else []

fun at_assumptions citation goal theorem =
  let
    val (_, statement) = boolSyntax.strip_forall goal
    val assumptions = leading_implications statement
    val specialised = Drule.SPEC_ALL theorem
    val premises = leading_implications (Thm.concl specialised)
    fun matched count =
      if count <= 0 then NONE
      else
        let
          val subject = boolSyntax.list_mk_conj (List.take (premises, count))
          val object =
            boolSyntax.list_mk_conj (List.take (assumptions, count))
        in
          case Lib.total (Term.match_term subject) object of
              SOME instance => SOME instance
            | NONE => matched (count - 1)
        end
  in
    case matched (Int.min (length premises, length assumptions)) of
        SOME instance => Drule.INST_TY_TERM instance specialised
      | NONE =>
          raise Unparseable
            (citation, "no leading assumption of the goal matches a premise")
  end

fun to_recipe ({theorems, normalised_subject, tactic, ambient} : resolver)
              {goal, source} ({facts, unfolded, methods} : parsed) =
  let
    (* A citation resolved against the goal's assumptions is answered by
       the same table entry as the fact it resolves, at the instance
       that resolution determines; every other citation is the entry as
       it stands. *)
    fun cited name =
      if String.isSuffix assumption_resolution name then
        map
          (fn {name = label, theorem} =>
            {name = label, theorem = at_assumptions name goal theorem})
          (theorems name)
      else
        theorems name
    (* [using] premises enter as facts, [unfolding] names as rewrites.
       Neither becomes a DefinitionAdd: that constructor exists only to
       unlock the escape hatch in [permitted_for], and a derived recipe
       never needs it. *)
    fun resolved build names =
      List.concat (map (fn name => map build (cited name)) names)
    val common =
      resolved benchLib.FactAdd facts @
      rewritten cited normalised_subject unfolded
    (* The ambient context stands in for the simpset and the claset an
       Isabelle method reads without naming them, and each half reaches
       only the methods that consult that half.  Giving the rewrites to
       [blast] or to a decision procedure would hand the HOL4 tactic a
       simplification pass the Isabelle proof never had; giving the
       classical rules to [simp] would hand it a claset Isabelle's
       [simp] does not read.

       It goes last.  Where two arguments rewrite the same constant
       the earlier one wins, and the translation's own wrapper for a
       constant would otherwise override the fact the source method
       named about it -- [source_lexord_def] unfolding [source_lexord]
       to [LLEX] before the cited characterisation of [source_lexord]
       can fire.  A method that names a fact has said which one
       applies; the ambient set is what it did not name.

       [source] is the goal's own Isabelle line, and the ambient set
       answers to it: Isabelle reads a theory in order and sees only
       what it imports, so a declaration below the proof or in a
       theory that imports the proof's was not in that proof's
       context.  The line is mined provenance, so this is still one
       context for the corpus and not a per-goal field. *)
    val in_scope = ambient source
    fun step modifiers identifier =
      let
        val context =
          List.filter (benchLib.argument_reaches identifier) in_scope
      in
        benchLib.Invoke
          (identifier,
           common @
           List.concat
             (map (argument_of cited normalised_subject) modifiers) @
           context)
      end
    fun invoke ({name, modifiers, repeated} : method) =
      let
        val applied = step modifiers (tactic name)
      in
        if repeated then benchLib.Repeat applied else applied
      end
    fun compose [] =
          raise Unparseable (render {facts = facts, unfolded = unfolded,
                                     methods = methods},
                             "[by] names no method")
      | compose [method] = invoke method
      | compose (method :: rest) =
          benchLib.AllGoals (invoke method, compose rest)
  in
    compose methods
  end

end
