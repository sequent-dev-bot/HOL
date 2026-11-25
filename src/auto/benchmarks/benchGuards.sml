structure benchGuards :> benchGuards =
struct

open Abbrev HolKernel

val ERR = mk_HOL_ERR "benchGuards"

type finding = {id : string, detector : string, detail : string}

fun finding_text ({id, detector, detail} : finding) =
  detector ^ " " ^ id ^ ": " ^ detail

(* ------------------------------------------------------------------ *)
(* Shared helpers                                                      *)
(* ------------------------------------------------------------------ *)

fun location_name (DB.Local name) = name
  | location_name (DB.Stored name) = KernelSig.name_toString name

fun registered_definition theorem =
  List.exists
    (fn location =>
      let val name = location_name location
      in String.isSuffix "_def" name orelse String.isSuffix "_DEF" name
      end)
    (DB.revlookup theorem)

fun goal_constants goal =
  map (#1 o dest_const) (find_terms is_const goal)

(* A recipe with more than one component -- [Then] or [AllGoals] --
   repeats its common arguments in each, so the raw argument list names
   one theorem several times. *)
val distinct_by_name =
  listUtil.distinct_by String.compare (#name : benchLib.named_thm -> string)

fun supplied_theorems (entry : benchLib.corpus_goal) =
  distinct_by_name
    (List.mapPartial benchLib.named_theorem
       (benchLib.recipe_arguments (#recipe entry)))

(* ------------------------------------------------------------------ *)
(* A1 -- semantic recognition                                          *)
(* ------------------------------------------------------------------ *)

val recognition_budget = ref (Time.fromSeconds 2)

fun closes tactic goal =
  let
    fun run () =
      case Tactical.VALID tactic ([], goal) (Context.snapshot()) of
          ([], validation) => (ignore (validation []); true)
        | _ => false
  in
    Timeout.apply (!recognition_budget) run ()
    handle Portable.Interrupt => raise Portable.Interrupt
         | _ => false
  end

fun symmetric theorems =
  List.mapPartial
    (fn theorem =>
      (SOME (Conv.GSYM theorem) handle HOL_ERR _ => NONE))
    theorems

(* METIS at its smallest useful budget.  A recognition witness is a
   near-immediate consequence of the supplied theorem; anything that needs
   a real saturation is not recognition. *)
fun metis_route theorems goal =
  let
    val saved = !metisTools.limit
    val _ = metisTools.limit := {time = SOME 0.5, infs = NONE}
    val result =
      closes (metisTools.METIS_TAC theorems) goal
      handle exn => (metisTools.limit := saved; raise exn)
  in
    metisTools.limit := saved; result
  end

val routes :
  (string * (thm list -> term -> bool)) list =
  [("MATCH_ACCEPT_TAC",
    fn theorems =>
      closes (Tactical.FIRST (map Tactic.MATCH_ACCEPT_TAC theorems))),
   ("REWRITE_TAC",
    fn theorems => closes (Rewrite.REWRITE_TAC theorems)),
   ("REWRITE_TAC[GSYM]",
    fn theorems => closes (Rewrite.REWRITE_TAC (symmetric theorems))),
   ("SIMP_TAC bool_ss",
    fn theorems =>
      closes (simpLib.SIMP_TAC boolSimps.bool_ss theorems)),
   ("MATCH_MP_TAC then SAFE_TAC",
    fn theorems =>
      closes
        (Tactical.THEN
           (Tactical.FIRST (map Tactic.MATCH_MP_TAC theorems),
            classicalLib.SAFE_TAC []))),
   ("METIS_TAC", metis_route)]

(* One goal is tested against several supplied theorems, and a route's
   ambient control run does not depend on the theorem.  Once it succeeds,
   the route cannot identify recognition by any theorem for that goal. *)
fun recognition_route_with controls goal theorem =
  if benchLib.theorem_is_goal goal theorem then SOME "syntactic"
  else
    let
      fun control (route, cache) =
        case !cache of
            SOME value => value
          | NONE =>
              let val value = route [] goal
              in cache := SOME value; value
              end
      fun recognises_by (_, route, cache) =
        !cache <> SOME true andalso
        route [theorem] goal andalso not (control (route, cache))
    in
      case List.find recognises_by controls of
          SOME (name, _, _) => SOME name
        | NONE => NONE
    end

fun controls_for () =
  map (fn (name, route) => (name, route, ref NONE)) routes

fun recognition_route goal theorem =
  recognition_route_with (controls_for ()) goal theorem

fun recognises goal theorem = Option.isSome (recognition_route goal theorem)

fun supplied_findings entry =
  let val controls = controls_for ()
  in
    List.mapPartial
      (fn ({name, theorem} : benchLib.named_thm) =>
        case recognition_route_with controls (#goal entry) theorem of
            NONE => NONE
          | SOME route =>
              SOME
                {id = #id entry, detector = "A1",
                 detail = name ^ " closes the goal via " ^ route})
      (supplied_theorems entry)
  end

(* A rule the corpus declares for every goal is not a recipe argument,
   so [supplied_theorems] never sees it -- and a seed that states a goal
   closes it by recognition exactly as a cited fact would.  This is the
   same detector over the ambient context.

   The translation's definitions are ambient too, and a goal wearing
   [source_lexord] needs them before a rule about [LLEX] can reach
   it, so they are supplied to the candidate run and to its control
   alike: what is measured is whether this one further rule turns the
   goal into a triviality. *)
fun defined_head theorem =
  let
    val body = snd (boolSyntax.strip_forall (concl theorem))
    val clause = hd (boolSyntax.strip_conj body)
    val (left, _) = boolSyntax.dest_eq (snd (boolSyntax.strip_forall clause))
  in
    SOME (#1 (dest_const (fst (strip_comb left))))
  end
  handle HOL_ERR _ => NONE | Empty => NONE

fun term_constants term =
  HOLset.addList
    (HOLset.empty String.compare,
     map (#1 o dest_const) (find_terms is_const term))

fun relevant_definitions goal =
  let
    val definitions =
      List.mapPartial
        (fn theorem =>
          Option.map (fn head => (head, theorem)) (defined_head theorem))
        (benchLib.definitional_theorems ())
    (* A wrapper over a wrapper needs the inner definition as well, so
       the set is closed under the constants the kept definitions
       introduce. *)
    fun close names kept 0 = kept
      | close names kept fuel =
          let
            val heads = map #1 kept
            val fresh =
              List.filter
                (fn (head, _) =>
                  HOLset.member (names, head) andalso
                  not (List.exists (equal head) heads))
                definitions
          in
            if null fresh then kept
            else
              close
                (List.foldl
                  (fn ((_, theorem), set) =>
                    HOLset.union (set, term_constants (concl theorem)))
                  names fresh)
                (kept @ fresh) (fuel - 1)
          end
  in
    map #2 (close (term_constants goal) [] 5)
  end

(* Recognition is a rule matching the goal, so the rule's own constants
   are the goal's.  Reading that off is what keeps a sweep over the
   whole ambient context affordable; like the syntactic test above it
   only ever accepts more candidates than it needs to. *)
fun ambient_candidates entry =
  let
    val goal = benchLib.unfolded (#goal entry)
    val logical =
      HOLset.addList
        (HOLset.empty String.compare,
         ["/\\", "\\/", "~", "==>", "=", "!", "?", "?!", "T", "F",
          "COND", "@"])
    val available = HOLset.union (term_constants goal, logical)
    val excluded = map #name (#excl entry)
    fun included name = not (List.exists (equal name) excluded)
    fun unavailable (_, tm) =
      if is_const tm andalso
         not (HOLset.member (available, #1 (dest_const tm))) then SOME ()
      else NONE
    fun within theorem =
      not (Option.isSome (gen_find_term unavailable (concl theorem)))
    val rules =
      List.mapPartial
        (fn ({name, thm, ...} : clasetLib.aesop_rule) =>
          if included name andalso within thm then
            SOME {name = name, theorem = thm}
          else NONE)
        (clasetLib.all_rules (clasetLib.the_claset ()))
    fun named_rewrites theorem =
      if within theorem then
        List.mapPartial
          (fn location =>
            let val name = location_name location in
              if included name then SOME {name = name, theorem = theorem}
              else NONE
            end)
          (DB.revlookup theorem)
      else []
    val rewrites =
      List.concat
        (map named_rewrites
          (List.concat
            (map simpLib.frag_rewrites
              (simpLib.ssfrags_of (clasimpLib.clasimp_ss ())))))
  in
    distinct_by_name (rules @ rewrites)
  end

fun ambient_findings entry =
  let
    val definitions = relevant_definitions (#goal entry)
    fun with_definitions theorems = definitions @ theorems
    val controls =
      map
        (fn (name, route) =>
          (name, fn theorems => route (with_definitions theorems), ref NONE))
        routes
  in
    List.mapPartial
      (fn ({name, theorem} : benchLib.named_thm) =>
        case recognition_route_with controls (#goal entry) theorem of
            NONE => NONE
          | SOME route =>
              SOME
                {id = #id entry, detector = "A1",
                 detail =
                   "ambient " ^ name ^ " closes the goal via " ^ route})
      (ambient_candidates entry)
  end

fun recognition_findings goals =
  List.concat
    (map
      (fn (entry : benchLib.corpus_goal) =>
        supplied_findings entry @ ambient_findings entry)
      goals)

(* ------------------------------------------------------------------ *)
(* A2 -- provenance                                                    *)
(* ------------------------------------------------------------------ *)

val translation_prefix = "parityTranslation$source_"

(* The mined lemma name renders an Isabelle name plus at most one of
   these role markers.  The list is closed: a name that needs a new
   marker is a finding, not a reason to extend it. *)
val documented_suffixes =
  ["D1", "D2", "D", "E", "I", "_iff", "_iffD1", "_iffD2", "_eq",
   "_def", "_conv", "1", "2"]

fun identifier_char character =
  Char.isAlphaNum character orelse character = #"_" orelse
  character = #"." orelse character = #"'"

fun method_names method =
  List.filter (fn name => name <> "")
    (String.tokens (not o identifier_char) method)

fun name_matches candidate name =
  candidate = name orelse
  String.isSuffix ("." ^ candidate) name orelse
  String.isSuffix ("." ^ name) candidate

fun method_names_argument method =
  let
    val names = method_names method
    fun cited value = List.exists (name_matches value) names
    fun omitted_suffix candidate suffix =
      size candidate > size suffix andalso
      String.isSuffix suffix candidate andalso
      cited (String.substring (candidate, 0, size candidate - size suffix))
  in
    fn candidate =>
      cited candidate orelse
      List.exists (omitted_suffix candidate) documented_suffixes
  end

fun translation_base name =
  if String.isPrefix translation_prefix name then
    SOME (String.extract (name, size translation_prefix, NONE))
  else NONE

fun translation_name ({name, ...} : benchLib.named_thm) =
  translation_base name

fun defines_goal_constant goal_names ({theorem, ...} : benchLib.named_thm) =
  registered_definition theorem andalso
  let val constants = Portable.HOLSusp.force goal_names
  in
    List.exists
      (fn constant =>
        List.exists (equal constant) constants)
      (map (#1 o dest_const)
        (find_terms is_const (Thm.concl theorem)))
  end

val distinct = listUtil.distinct_by String.compare I

fun provenance_violations (entry : benchLib.corpus_goal) =
  let
    val method = Portable.HOLSusp.delay
      (fn () => method_names_argument (#source_method entry))
    val goal_names =
      Portable.HOLSusp.delay (fn () => goal_constants (#goal entry))
    fun violation (named as {name, ...} : benchLib.named_thm) =
      case translation_name named of
          NONE => NONE
        | SOME base =>
            if Portable.HOLSusp.force method base orelse
               defines_goal_constant goal_names named
            then NONE
            else SOME name
  in
    distinct (List.mapPartial violation (supplied_theorems entry))
  end

fun provenance_findings goals =
  List.mapPartial
    (fn (entry : benchLib.corpus_goal) =>
      case provenance_violations entry of
          [] => NONE
        | names =>
            SOME
              {id = #id entry, detector = "A2",
               detail =
                 "[" ^ String.concatWith ", " names ^ "] not named by " ^
                 #source_method entry})
    goals

(* ------------------------------------------------------------------ *)
(* A3 -- search-work invariant                                         *)
(* ------------------------------------------------------------------ *)

val search_methods =
  ["blast", "auto", "force", "fastforce", "safe", "clarsimp", "metis"]

(* The method proper is what follows "by"; anything before it is the
   [using] fact list.  A string without "by" is not an Isabelle method
   invocation and has no head. *)
fun method_head method =
  let
    fun after_by [] = NONE
      | after_by ("by" :: name :: _) = SOME name
      | after_by (_ :: rest) = after_by rest
  in
    case method_names method of
        [] => ""
      | names => (case after_by names of SOME name => name | NONE => "")
  end

fun is_search_method method =
  List.exists (equal (method_head method)) search_methods

val work_floor = 1

fun measured_run budget (entry : benchLib.corpus_goal) =
  searchWork.measure
    (fn () => benchLib.run_goal budget (#recipe entry) entry)

fun search_work_findings budget goals =
  List.mapPartial
    (fn (entry : benchLib.corpus_goal) =>
      if not (is_search_method (#source_method entry)) then NONE
      else
        let val (outcome, work) = measured_run budget entry
        in
          if not (benchLib.outcome_solved outcome) then NONE
          else if searchWork.total work >= work_floor then NONE
          else
            SOME
              {id = #id entry, detector = "A3",
               detail =
                 #source_method entry ^ " solved with no search work (" ^
                 searchWork.render work ^ "), " ^
                 Int.toString (length (supplied_theorems entry)) ^
                 " supplied theorem(s)"}
        end)
    goals

(* ------------------------------------------------------------------ *)
(* A4 -- single-use translation lemmas                                 *)
(* ------------------------------------------------------------------ *)

fun translation_uses goals =
  let
    val pairs =
      List.concat
        (map
          (fn (entry : benchLib.corpus_goal) =>
            List.mapPartial
              (fn named =>
                case translation_name named of
                    NONE => NONE
                  | SOME _ => SOME (#name named, #id entry))
              (supplied_theorems entry))
          goals)
    (* Report names in reverse last-use order and IDs in first-use order. *)
    fun add_use ((name, id), (names, uses)) =
      case Symtab.lookup uses name of
          NONE => (name :: names, Symtab.update (name, [id]) uses)
        | SOME ids => (names, Symtab.update (name, id :: ids) uses)
    val (names, uses) = List.foldr add_use ([], Symtab.empty) pairs
  in
    List.foldl
      (fn (name, groups) =>
        (name, distinct (valOf (Symtab.lookup uses name))) :: groups)
      [] names
  end

fun single_use_findings goals =
  let
    val uses = translation_uses goals
    val by_id =
      List.foldr
        (fn (entry : benchLib.corpus_goal, entries) =>
          Symtab.update (#id entry, entry) entries)
        Symtab.empty goals
    fun entry_of id = Symtab.lookup by_id id
  in
    List.mapPartial
      (fn (name, ids) =>
        case ids of
            [id] =>
              (case (translation_base name, entry_of id) of
                   (SOME base, SOME entry) =>
                     if method_names_argument (#source_method entry) base
                     then NONE
                     else
                       SOME
                         {id = id, detector = "A4",
                          detail =
                            name ^ " is used by this goal alone and is " ^
                            "not named by " ^ #source_method entry}
                 | _ => NONE)
          | _ => NONE)
      uses
  end

(* ------------------------------------------------------------------ *)
(* A5 -- alias audit                                                   *)
(* ------------------------------------------------------------------ *)

(* Isabelle attribute forms a display name may legitimately carry.  The
   list is closed: a bracket that is not one of these is a fabricated
   marker, not a rendering of anything in the source. *)
val documented_attributes =
  ["[symmetric]", "[of ", "[where ", "[OF ", "[THEN "]

fun split_attribute name =
  case CharVector.findi (fn (_, character) => character = #"[") name of
      NONE => (name, NONE)
    | SOME (index, _) =>
        (String.substring (name, 0, index),
         SOME (String.extract (name, index, NONE)))

fun documented_attribute attribute =
  List.exists
    (fn form =>
      attribute = form orelse String.isPrefix form attribute)
    documented_attributes

fun goal_shaped name = String.isSubstring "_for_" name

fun resolved name =
  case String.fields (equal #"$") name of
      [theory, theorem] =>
        (SOME (DB.fetch theory theorem)
         handle Portable.Interrupt => raise Portable.Interrupt
              | _ => NONE)
    | _ => NONE

fun same_theorem left right =
  Term.aconv (Thm.concl left) (Thm.concl right) andalso
  HOLset.equal (Thm.hypset left, Thm.hypset right)

fun alias_verdict (display, build) =
  let
    val (base, attribute) = split_attribute display
  in
    if goal_shaped display then SOME "goal-specific alias"
    else
      case attribute of
          SOME text =>
            if documented_attribute text then NONE
            else SOME ("fabricated attribute marker " ^ text)
        | NONE =>
            case resolved base of
                NONE =>
                  SOME "fabricated name that resolves to no theorem"
              | SOME theorem =>
                  if same_theorem theorem (#theorem (build ())) then NONE
                  else
                    SOME
                      ("name resolves to a different theorem than the " ^
                       "one it is mapped to")
  end

fun alias_findings () =
  List.mapPartial
    (fn (special as (display, _)) =>
      case alias_verdict special of
          NONE => NONE
        | SOME detail =>
            SOME {id = display, detector = "A5", detail = detail})
    benchExplicit.special

(* ------------------------------------------------------------------ *)
(* A6 -- goal-term hash pin                                            *)
(* ------------------------------------------------------------------ *)

fun bound_index variable bound =
  let
    fun search _ [] = NONE
      | search index (item :: rest) =
          if Term.aconv item variable then SOME index
          else search (index + 1) rest
  in
    search 0 bound
  end

(* Emit the serialization in order so each consumer sees the same
   bytes without copying the serialized children of each application. *)
fun emit_signature emit goal =
  let
    fun emit_type ty =
      if Type.is_vartype ty then emit ("'" ^ Type.dest_vartype ty)
      else
        let val {Tyop, Thy, Args} = Type.dest_thy_type ty
        in
          emit (Thy ^ "$" ^ Tyop ^ "(");
          (case Args of
               [] => ()
             | first :: rest =>
                 (emit_type first;
                  List.app (fn arg => (emit ","; emit_type arg)) rest));
          emit ")"
        end

    fun emit_term bound term =
      case Term.dest_term term of
          Term.VAR (name, ty) =>
            (case bound_index term bound of
                 SOME index => emit ("b" ^ Int.toString index)
               | NONE => (emit ("v" ^ name ^ ":"); emit_type ty))
        | Term.CONST {Name, Thy, Ty} =>
            (emit ("c" ^ Thy ^ "$" ^ Name ^ ":"); emit_type Ty)
        | Term.COMB (rator, rand) =>
            (emit "("; emit_term bound rator; emit " ";
             emit_term bound rand; emit ")")
        | Term.LAMB (variable, body) =>
            (emit "\\"; emit_type (Term.type_of variable); emit ".";
             emit_term (variable :: bound) body)
  in
    emit_term [] goal
  end

fun goal_signature term =
  let
    val chunks = ref []
    val _ = emit_signature (fn chunk => chunks := chunk :: !chunks) term
  in
    String.concat (List.rev (!chunks))
  end

(* FNV-1a over the concatenated signatures, rendered as hexadecimal. *)
val fnv_offset : Word.word = 0wx811C9DC5
val fnv_prime : Word.word = 0wx01000193
val fnv_mask : Word.word = 0wxFFFFFFFF

fun fnv_step (character, hash) =
  Word.andb
    (Word.* (Word.xorb (hash, Word.fromInt (Char.ord character)), fnv_prime),
     fnv_mask)

fun family_hash goals =
  let
    val hash = ref fnv_offset
    fun emit chunk = hash := CharVector.foldl fnv_step (!hash) chunk
    fun emit_goal ({id, goal, ...} : benchLib.corpus_goal) =
      (emit id; emit "="; emit_signature emit goal)
    val _ =
      case goals of
          [] => ()
        | first :: rest =>
            (emit_goal first;
             List.app (fn entry => (emit "\n"; emit_goal entry)) rest)
  in
    Word.fmt StringCvt.HEX (!hash)
  end

end
