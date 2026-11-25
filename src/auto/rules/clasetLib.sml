structure clasetLib :> clasetLib =
struct

open Abbrev HolKernel boolLib

type rulekind = clasetRules.rulekind
type rulespec = clasetRules.rulespec
type tag = clasetRules.tag
type brl = clasetRules.brl
type info = clasetRules.info

local
  open clasetRules
in

type net_entry = tag * brl
type netpair = net_entry clasetNet.net * net_entry clasetNet.net

(* [info] is the declaration's canonical rule forms, which [make_rule_decl]
   already derived -- with real kernel inferences -- when the rule was
   declared.  Carrying it through retrieval is what keeps an engine from
   deriving it again for every rule that matches a goal. *)
type aesop_rule =
  {name : string, spec : rulespec, thm : thm, info : info}
type aentry = {tag : tag, rule : aesop_rule}
type aesop_index =
  {target : aentry clasetNet.net, hyp : aentry clasetNet.net}

(* Cache schemas built from the generic tyinfo, never from a query's type
   instance or constructor arguments.  Indices belong to the enclosing
   claset and are reassigned when entries are merged into another claset. *)
type distinct_source =
  {name : string, case_def : thm, case_const : term,
   constructors : term vector, cases : thm vector,
   constructor_positions :
     (KernelSig.kernelid, int list) Redblackmap.dict Portable.HOLSusp.susp,
   cache : (int * int, aesop_rule) Redblackmap.dict ref}
type distinct_entry = {source : distinct_source, first : int}
type distinct_table = (string * string, distinct_entry) Redblackmap.dict

val empty_distinct : distinct_table =
  Redblackmap.mkDict (Lib.pair_compare (String.compare, String.compare))

(* The components a claset derives from its declarations; [add_decl] and
   [delete_decl] maintain them together. *)
type cs_index =
  {safe0 : netpair, safep : netpair, unsafe : netpair, dup : netpair,
   aesop_index : aesop_index, norm_decls : decl list}

type cs_wrappers =
  (string * NTactical.wrapper) list * (string * NTactical.wrapper) list

datatype claset =
  CS of {decls : decls, wrappers : cs_wrappers, index : cs_index,
         distinct : distinct_table}

type claset_part = netpair * distinct_table

val empty_netpair = (clasetNet.empty, clasetNet.empty)
val empty_aesop_index =
  {target = clasetNet.empty, hyp = clasetNet.empty}

val empty_index : cs_index =
  {safe0 = empty_netpair, safep = empty_netpair, unsafe = empty_netpair,
   dup = empty_netpair, aesop_index = empty_aesop_index, norm_decls = []}

val empty_cs =
  CS {decls = empty_decls, wrappers = ([], []), index = empty_index,
      distinct = empty_distinct}

fun rule_brl kind th = (is_elim kind, th)

fun rule_pattern kind (form : canonical) =
  {pat = rule_index_of kind form, patvars = #patvars form}

fun theorem_pattern kind th = rule_pattern kind (canonical_form_of kind th)

fun indexed_brl is_elim index th =
  let
    val kind = if is_elim then Elim else Intro
    val form = canonical_form_of kind th
    val tag = {weight = subgoals_of_form is_elim form, index = index}
  in
    (rule_pattern kind form, (tag, (is_elim, th)))
  end

fun insert_brl is_elim index th (inet, enet) =
  let
    val entry = indexed_brl is_elim index th
  in
    if is_elim then (inet, clasetNet.insert entry enet)
    else (clasetNet.insert entry inet, enet)
  end

fun insert_rl kind index (rl : rl) netpair =
  let
    val (th, swapped) = rl
    val netpair' = insert_brl (is_elim kind) (2 * index + 1) th netpair
  in
    case swapped of
        NONE => netpair'
      | SOME th' => insert_brl true (2 * index) th' netpair'
  end

fun filter_indexed by_pattern kind th keep net =
  if by_pattern then clasetNet.filter_at (theorem_pattern kind th) keep net
  else clasetNet.vfilter keep net

fun delete_brl by_pattern kind index th net =
  let
    fun keep ({index = index', ...} : tag, _) = index' <> index
  in
    filter_indexed by_pattern kind th keep net
  end

fun delete_rl by_pattern kind index ((th, swapped) : rl) (inet, enet) =
  let
    val swapped_index = 2 * index
    val main_index = swapped_index + 1
    val elim = is_elim kind
    val enet =
      case swapped of
          NONE => enet
        | SOME swapped_th =>
            delete_brl by_pattern Elim swapped_index swapped_th enet
  in
    if elim then (inet, delete_brl by_pattern Elim main_index th enet)
    else (delete_brl by_pattern Intro main_index th inet, enet)
  end

(* Norm rules are not indexed: the normalisation phase takes the whole list
   (see [norm_rules]), so an entry here would be retrieved, ordered and
   deduplicated on every goal expansion only to be filtered out again. *)
fun insert_aesop_decl (decl : decl)
  ({target, hyp} : aesop_index) =
  let
    val {name, spec, tag, orig, info} = decl
    val kind = #kind spec
    val indexed =
      (theorem_pattern kind orig,
       {tag = tag,
        rule = {name = name, spec = spec, thm = orig, info = info}})
  in
    if kind = Intro then
      {target = clasetNet.insert indexed target, hyp = hyp}
    else
      {target = target, hyp = clasetNet.insert indexed hyp}
  end

fun delete_aesop_decl by_pattern (decl : decl)
  ({target, hyp} : aesop_index) =
  let
    val {spec, tag = {index, ...}, orig, ...} = decl
    val kind = #kind spec
    fun keep ({tag = {index = index', ...}, ...} : aentry) =
      index <> index'
  in
    if kind = Intro then
      {target = filter_indexed by_pattern kind orig keep target, hyp = hyp}
    else
      {target = target, hyp = filter_indexed by_pattern kind orig keep hyp}
  end

(* Norm rules never enter the four classical netpairs, so the claset keeps
   them as an ordered list instead -- the aesop normalisation phase wants
   all of them, not the ones matching one goal.  Held in [dest_decls] order
   so that [norm_rules] agrees with filtering [rules_of], which is the
   tiebreak the penalty sort relies on. *)
fun insert_norm_decl (decl : decl) decls =
  let
    fun insert [] = [decl]
      | insert (current :: rest) =
          case decl_order (decl, current) of
              GREATER => current :: insert rest
            | _ => decl :: current :: rest
  in
    insert decls
  end

fun delete_norm_decl (decl : decl) decls =
  let
    val index = #index (#tag decl)
  in
    List.filter (fn (other : decl) => #index (#tag other) <> index) decls
  end

(* Use the weight recorded at declaration time for safe rule routing. *)
fun update_decl update_rl update_aesop update_norm (decl : decl)
  ({safe0, safep, unsafe, dup, aesop_index, norm_decls} : cs_index) =
  let
    val {spec, tag = {weight, index}, info, ...} = decl
    val kind = #kind spec
  in
    if kind = Norm then
      {safe0 = safe0, safep = safep, unsafe = unsafe, dup = dup,
       aesop_index = aesop_index, norm_decls = update_norm decl norm_decls}
    else
      let
        val aesop_index = update_aesop decl aesop_index
      in
        if kind = Forward then
          {safe0 = safe0, safep = safep, unsafe = unsafe, dup = dup,
           aesop_index = aesop_index, norm_decls = norm_decls}
        else if not (#safe spec) then
          {safe0 = safe0, safep = safep,
           unsafe = update_rl kind index (#rl info) unsafe,
           dup = update_rl kind index (#dup_rl info) dup,
           aesop_index = aesop_index, norm_decls = norm_decls}
        else if weight = 0 then
          {safe0 = update_rl kind index (#rl info) safe0, safep = safep,
           unsafe = unsafe, dup = dup, aesop_index = aesop_index,
           norm_decls = norm_decls}
        else
          {safe0 = safe0, safep = update_rl kind index (#rl info) safep,
           unsafe = unsafe, dup = dup, aesop_index = aesop_index,
           norm_decls = norm_decls}
      end
  end

val add_decl = update_decl insert_rl insert_aesop_decl insert_norm_decl
fun delete_decl by_pattern =
  update_decl (delete_rl by_pattern) (delete_aesop_decl by_pattern)
    delete_norm_decl

fun make_rule_decl spec (name, th) =
  let
    val info = ext_info spec th
    val weight = subgoals_of (rule_brl (#kind spec) (#1 (#rl info)))
  in
    make_decl {name = name, spec = spec, weight = weight,
               info = info, orig = th}
  end

fun add_rule_by extend spec named_th
      (cs as CS {decls, wrappers, index, distinct}) =
  case extend (make_rule_decl spec named_th) decls of
      (NONE, _) => cs
    | (SOME new_decl, decls') =>
        CS {decls = decls', wrappers = wrappers, distinct = distinct,
            index = add_decl new_decl index}

val add_rule = add_rule_by extend_decl

(* Rules a library derives from a user declaration rather than rules the
   user named.  Such a rule belongs to the declaration that produced it, so
   it is installed even when its conclusion duplicates an installed rule,
   and it carries none of the diagnostics add_rule prints. *)
val add_derived_rule = add_rule_by extend_derived_decl

val sintro_spec = {kind = Intro, safe = true, prio = NONE}
val intro_spec = {kind = Intro, safe = false, prio = NONE}
val selim_spec = {kind = Elim, safe = true, prio = NONE}
val elim_spec = {kind = Elim, safe = false, prio = NONE}
val sdest_spec = {kind = Dest, safe = true, prio = NONE}
val dest_spec = {kind = Dest, safe = false, prio = NONE}
val forward_spec = {kind = Forward, safe = false, prio = NONE}
val sforward_spec = {kind = Forward, safe = true, prio = NONE}
val norm_spec = {kind = Norm, safe = false, prio = NONE}

val tyinfo_prefix = "__claset_tyinfo_"

fun tyinfo_stem tyi =
  let val (thy, tyop) = TypeBasePure.ty_name_of tyi
  in tyinfo_prefix ^ thy ^ "_" ^ tyop end

fun add_distinct_source key case_def (make_source : unit -> distinct_source)
      (cs as CS {decls, wrappers, index, distinct}) =
  let
    fun unchanged {source, ...} =
      aconv (concl (#case_def source)) (concl case_def)
  in
    if Option.getOpt (Option.map unchanged
      (Redblackmap.peek (distinct, key)), false) then cs
    else
      let
        val source = make_source ()
        val n = Vector.length (#constructors source)
        val (first, decls') = reserve_decl_indices (n * n) decls
      in
        CS {decls = decls', wrappers = wrappers, index = index,
            distinct = Redblackmap.insert
              (distinct, key, {source = source, first = first})}
      end
  end

fun index_constructors constructors =
  let
    fun add (position, constructor, index) =
      if is_const constructor then
        Redblackmap.insertWith (fn (later, earlier) => earlier @ later)
          (index, #Name (dest_thy_constid constructor), [position])
      else index
  in
    Vector.foldri add (Redblackmap.mkDict KernelSig.id_compare) constructors
  end

fun reconcile_distinct tyi (cs as CS {decls, wrappers, index, distinct}) =
  let val key = TypeBasePure.ty_name_of tyi
  in
    case Lib.total TypeBasePure.constructors_of tyi of
        SOME (constructors as _ :: _ :: _) =>
          let
            val case_def = TypeBasePure.case_def_of tyi
            fun make_source () =
              let val constructors = Vector.fromList constructors
              in
                {name = tyinfo_stem tyi ^ "_distinct",
                 case_def = case_def,
                 case_const = TypeBasePure.case_const_of tyi,
                 constructors = constructors,
                 constructor_positions = Portable.HOLSusp.delay
                   (fn () => index_constructors constructors),
                 cases = Vector.fromList (CONJUNCTS case_def),
                 cache = ref (Redblackmap.mkDict
                   (Lib.pair_compare (Int.compare, Int.compare)))}
              end
          in
            add_distinct_source key case_def make_source cs
          end
      | _ =>
          if Redblackmap.inDomain (distinct, key) then
            CS {decls = decls, wrappers = wrappers, index = index,
                distinct = #1 (Redblackmap.remove (distinct, key))}
          else cs
  end

(* elts: the TypeBase entries caught up against. *)
fun catch_up_distinct elts cs =
  List.foldl (fn (tyi, acc) => reconcile_distinct tyi acc) cs elts

fun distinct_rule_names (CS {distinct, ...}) =
  map (#name o #source o #2) (Redblackmap.listItems distinct)

(* A Boolean case discriminator proves a clash from the two case clauses.
   Unlike distinct_of, case_def_of is linear and exists for wide enums.
   [derive] runs once before each pair not yet in the cache. *)
fun distinct_pair {checkpoint, derive}
      ({source = {name, constructors, cases, case_const, cache, ...},
        first} : distinct_entry) (i, j) =
  let
    val _ = checkpoint ()
    val n = Vector.length constructors
    val rule =
      case Redblackmap.peek (!cache, (i, j)) of
          SOME rule => rule
        | NONE =>
            let
              val _ = derive ()
              fun arguments c =
                map genvar (#1 (boolSyntax.strip_fun (type_of c)))
              fun applied k =
                let val c = Vector.sub (constructors, k)
                in list_mk_comb (c, arguments c) end
              val left = applied i
              val right = applied j
              val equality = boolSyntax.mk_eq (left, right)
              val result_type =
                #2 (boolSyntax.strip_fun (type_of case_const))
              val case_bool = Term.inst [result_type |-> bool] case_const
              val branches = Vector.foldri
                (fn (k, c, rest) =>
                   (checkpoint ();
                    list_mk_abs
                      (arguments c, if k = i then boolSyntax.T
                                    else boolSyntax.F) :: rest))
                [] constructors
              val x = genvar (type_of left)
              val discriminator =
                mk_abs (x, list_mk_comb (case_bool, x :: branches))
              val equal = Conv.CONV_RULE (Conv.BINOP_CONV BETA_CONV)
                (AP_TERM discriminator (ASSUME equality))
              val (l, r) = boolSyntax.dest_eq (concl equal)
              fun reduce k tm =
                Conv.RIGHT_CONV_RULE (Conv.DEPTH_CONV BETA_CONV)
                  (Conv.REWR_CONV (Vector.sub (cases, k)) tm)
              val reduced = TRANS (SYM (reduce i l))
                (TRANS equal (reduce j r))
              val false_th = EQ_MP reduced boolTheory.TRUTH
              val result = genvar bool
              val theorem = GEN_ALL (DISCH equality
                (MP (SPEC result boolTheory.FALSITY) false_th))
              val pair_name = name ^ "_" ^ Int.toString i ^ "_" ^
                Int.toString j
              val decl = make_rule_decl selim_spec (pair_name, theorem)
              val rule =
                {name = pair_name, spec = selim_spec,
                 thm = #orig decl, info = #info decl}
            in
              cache := Redblackmap.insert (!cache, (i, j), rule);
              rule
            end
  in
    ({tag = {weight = 0, index = first - i * n - j}, rule = rule} : aentry)
  end

(* A query at a type variable enumerates every datatype only when that
   variable is schematic ([flexible_type]); a rigid one matches none. *)
fun distinct_candidates_lazy (meter as {checkpoint, ...}) distinct
      {q, qvars, flexible_type} =
  case Lib.total boolSyntax.dest_eq q of
      NONE => []
    | SOME (left, right) =>
      if aconv left right then []
      else
        let
          val ty = type_of left
          val entries =
            if Type.is_vartype ty then
              if flexible_type ty then Redblackmap.listItems distinct
              else []
            else
              let val {Thy, Tyop, ...} = Type.dest_thy_type ty
                  val key = (Thy, Tyop)
              in
                case Redblackmap.peek (distinct, key) of
                    NONE => []
                  | SOME entry => [(key, entry)]
              end
          fun collect [] = []
            | collect entries =
              let
                val left_head = fst (strip_comb left)
                val right_head = fst (strip_comb right)
                val measured =
                  not (Portable.pointer_eq (checkpoint, listUtil.no_checkpoint))
                val metas =
                  if is_var left_head orelse is_var right_head then qvars ()
                  else Term.empty_tmset
                fun candidates (_, entry as {source, ...} : distinct_entry) =
                  let
                    val constructors = #constructors source
                    val n = Vector.length constructors
                    fun positions head =
                      if is_var head andalso HOLset.member (metas, head) then
                        List.tabulate (n, Lib.I)
                      else if is_const head then
                        if measured then
                          Vector.foldri
                            (fn (k, c, rest) =>
                               (checkpoint ();
                                if same_const c head then k :: rest else rest))
                            [] constructors
                        else
                          Option.getOpt
                            (Redblackmap.peek
                              (Portable.HOLSusp.force
                                 (#constructor_positions source),
                               #Name (dest_thy_constid head)), [])
                      else []
                    val ls = positions left_head
                    val rs = positions right_head
                    fun pairs i =
                      List.mapPartial
                        (fn j => (checkpoint ();
                          if i = j then NONE
                          else SOME (distinct_pair meter entry (i, j)))) rs
                  in
                    List.concat (map pairs ls)
                  end
              in
                List.concat (map candidates entries)
              end
        in
          collect entries
        end

fun distinct_candidates meter distinct {q, qvars, flexible_type} =
  distinct_candidates_lazy meter distinct
    {q = q, qvars = K qvars, flexible_type = flexible_type}

fun distinct_brl ({tag = {weight, index}, rule, ...} : aentry) =
  ({weight = weight, index = 2 * index + 1},
   (true, #1 (#rl (#info rule))))

fun add_rules spec rules cs =
  List.foldl (fn (rule, acc) => add_rule spec rule acc) cs rules

val add_sintros = add_rules sintro_spec
val add_intros = add_rules intro_spec
val add_selims = add_rules selim_spec
val add_elims = add_rules elim_spec
val add_sdests = add_rules sdest_spec

fun remove_rule name (CS {decls, wrappers, index, distinct}) =
  let
    val (old_decls, decls') = remove_decl name decls
    (* A small index is cheap to scan without reconstructing the rule's key.
       Use the key as the declaration table grows to limit traversal. *)
    fun delete (decl, index) = delete_decl (decl_count decls > 64) decl index
  in
    CS {decls = decls', wrappers = wrappers,
        distinct =
          if String.isPrefix tyinfo_prefix name then
            Redblackmap.filter (fn {source, ...} => #name source <> name)
              distinct
          else distinct,
        index = List.foldl delete index old_decls}
  end

fun merge_alists left right =
  left @ List.filter
    (fn (name, _) => not (List.exists (fn (name', _) => name = name') left))
    right

(* The left claset's derived components are the accumulator: only the
   declarations the merge newly admits are indexed again. *)
fun merge_cs
  (CS {decls, wrappers = (safe_wrappers, unsafe_wrappers), index, distinct},
   CS {decls = decls2, wrappers = (safe_wrappers2, unsafe_wrappers2),
       distinct = distinct2, ...}) =
  let
    val (new_decls, decls') = merge_decls (decls, decls2)
    val index' =
      List.foldl (fn (decl, index) => add_decl decl index) index new_decls
  in
    Redblackmap.foldl
      (fn (key, {source, ...}, cs) =>
        add_distinct_source key (#case_def source) (fn () => source) cs)
      (CS {decls = decls', distinct = distinct,
           wrappers =
             (merge_alists safe_wrappers safe_wrappers2,
              merge_alists unsafe_wrappers unsafe_wrappers2),
           index = index'}) distinct2
  end

(* Replace an existing entry in place; put a new entry at the front. *)
fun update_alist (entry as (key, _)) entries =
  let
    fun replace [] = NONE
      | replace ((old as (old_key, _)) :: rest) =
          if key = old_key then SOME (entry :: rest)
          else Option.map (fn rest' => old :: rest') (replace rest)
  in
    case replace entries of
        SOME entries' => entries'
      | NONE => entry :: entries
  end

fun delete_wrapper name wrappers =
  List.filter (fn (name', _) => name <> name') wrappers

fun map_wrappers f (CS {decls, wrappers, index, distinct}) =
  CS {decls = decls, wrappers = f wrappers, index = index,
      distinct = distinct}

fun map_safe_wrappers f =
  map_wrappers (fn (safe_wrappers, unsafe_wrappers) =>
                  (f safe_wrappers, unsafe_wrappers))

fun map_unsafe_wrappers f =
  map_wrappers (fn (safe_wrappers, unsafe_wrappers) =>
                  (safe_wrappers, f unsafe_wrappers))

fun add_safe_wrapper wrapper = map_safe_wrappers (update_alist wrapper)
fun add_unsafe_wrapper wrapper = map_unsafe_wrappers (update_alist wrapper)
fun del_safe_wrapper name = map_safe_wrappers (delete_wrapper name)
fun del_unsafe_wrapper name = map_unsafe_wrappers (delete_wrapper name)

fun apply_wrappers wrappers tac =
  List.foldl (fn ((_, wrapper), acc) => wrapper acc) tac wrappers

fun app_safe_wrappers (CS {wrappers = (safe_wrappers, _), ...}) =
  apply_wrappers safe_wrappers

fun app_unsafe_wrappers (CS {wrappers = (_, unsafe_wrappers), ...}) =
  apply_wrappers unsafe_wrappers

fun rule_of_decl ({spec, name, orig, info, ...} : decl) : aesop_rule =
  {spec = spec, name = name, thm = orig, info = info}

fun all_rules (CS {decls, ...}) = map rule_of_decl (dest_decls decls)

fun rules_for_derived_concl (CS {decls, ...}) conclusion =
  map rule_of_decl (decls_for_derived_concl decls conclusion)

(* The name/theorem view of a retrieved declaration: what a caller that has
   no use for the canonicalisation sees, in the [rules_of] shape. *)
fun rules_of (CS {decls, ...}) =
  map (fn {spec, name, orig, ...} => (spec, (name, orig))) (dest_decls decls)

fun norm_rules (CS {index = {norm_decls, ...}, ...}) =
  map rule_of_decl norm_decls

fun pp_claset0
  (CS {decls, wrappers = (safe_wrappers, unsafe_wrappers), ...}) =
  let
    open Portable smpp

    fun has_spec safe kind (decl : decl) =
      #safe (#spec decl) = safe andalso #kind (#spec decl) = kind

    val ordered = dest_decls decls
    fun decls_of safe kind = List.filter (has_spec safe kind) ordered

    fun pp_decl ({name, orig, ...} : decl) =
      block CONSISTENT 0
        (add_string ("[" ^ name ^ "]") >> add_break (1, 2) >>
         lift Parse.pp_thm orig)

    fun pp_section (title, entries) =
      block CONSISTENT 0
        (add_string (title ^ ":") >> add_newline >>
         block CONSISTENT 2 (pr_list pp_decl add_newline entries))

    fun pp_wrappers (title, wrappers) =
      add_string (title ^ ":") >>
      add_break (1, 2) >>
      pr_list (fn (name, _) => add_string name) (add_break (1, 0)) wrappers

    val rule_sections =
      List.filter (fn (_, entries) => not (List.null entries))
        [("Safe introduction rules", decls_of true Intro),
         ("Safe elimination rules", decls_of true Elim),
         ("Safe destruction rules", decls_of true Dest),
         ("Unsafe introduction rules", decls_of false Intro),
         ("Unsafe elimination rules", decls_of false Elim),
         ("Unsafe destruction rules", decls_of false Dest)]
    val wrapper_sections =
      [("Safe wrappers", safe_wrappers),
       ("Unsafe wrappers", unsafe_wrappers)]
  in
    pr_list pp_section (add_newline >> add_newline) rule_sections >>
    (if List.null rule_sections then smpp.nothing else add_newline) >>
    pr_list pp_wrappers add_newline wrapper_sections
  end

val pp_claset = Parse.mlower o pp_claset0

fun safe0_part (CS {index = {safe0, ...}, distinct, ...}) =
  (safe0, distinct)
fun safep_part (CS {index = {safep, ...}, ...}) = (safep, empty_distinct)
fun unsafe_part (CS {index = {unsafe, ...}, ...}) = (unsafe, empty_distinct)
fun dup_part (CS {index = {dup, ...}, ...}) = (dup, empty_distinct)

fun has_distinct_rules ((_, distinct) : claset_part) =
  not (Redblackmap.isEmpty distinct)

fun match_candidates net tm = candidate_order (clasetNet.match tm net)

fun match_intro_candidates (((inet, _), _) : claset_part) =
  match_candidates inet
fun match_elim_candidates (((_, enet), distinct) : claset_part) tm =
  candidate_order (clasetNet.match tm enet @
    map distinct_brl (distinct_candidates
      {checkpoint = listUtil.no_checkpoint,
       derive = listUtil.no_checkpoint} distinct
      {q = tm, qvars = Term.empty_tmset, flexible_type = K true}))

fun unify_candidates checkpoint net tm =
  clasetNet.unifyFreesMeasured checkpoint tm net

fun unify_intro_candidates_measured checkpoint
      (((inet, _), _) : claset_part) tm =
  candidate_order_measured checkpoint (unify_candidates checkpoint inet tm)

(* Static nets retain their historical broad skeleton query; only lazy
   pair generation must distinguish true search metas from rigid frees. *)
fun unify_elim_candidates_lazy (meter as {checkpoint, ...})
      (((_, enet), distinct) : claset_part) tm query =
  let
    val static = unify_candidates checkpoint enet tm
    (* Declaration and constructor-pair indices are disjoint, so one sort
       suffices. Keep the first sort when comparisons are measured. *)
    val static =
      if Portable.pointer_eq (checkpoint, listUtil.no_checkpoint) then static
      else candidate_order_measured checkpoint static
  in
    candidate_order_measured checkpoint
      (static @
       map distinct_brl (distinct_candidates_lazy meter distinct query))
  end

fun unify_elim_candidates_with meter part tm {q, qvars, flexible_type} =
  unify_elim_candidates_lazy meter part tm
    {q = q, qvars = K qvars, flexible_type = flexible_type}

fun unify_elim_candidates_measured checkpoint part tm =
  unify_elim_candidates_lazy
    {checkpoint = checkpoint, derive = listUtil.no_checkpoint} part tm
    {q = tm, qvars = fn () => Term.FVL [tm] Term.empty_tmset,
     flexible_type = K true}

fun unify_intro_candidates part =
  unify_intro_candidates_measured listUtil.no_checkpoint part

fun unify_elim_candidates part =
  unify_elim_candidates_measured listUtil.no_checkpoint part

fun classical_candidates {unify, derive, query_metas, flexible_type}
      (part as ((inet, enet), distinct) : claset_part)
      {conclusion, assumptions} =
  let
    val checkpoint = listUtil.no_checkpoint
    val lookup =
      if unify then unify_candidates checkpoint
      else fn net => fn q => clasetNet.match q net
    val has_distinct = has_distinct_rules part
    val meter = {checkpoint = checkpoint,
                 derive = if unify then derive else checkpoint}
    val metas = if unify then query_metas else K Term.empty_tmset
    val flexible_type = if unify then flexible_type else K true
    fun lookup_elim q =
      let val static = lookup enet q
      in
        if not has_distinct then static
        else
          static @ map distinct_brl
            (distinct_candidates_lazy meter distinct
              {q = q, qvars = fn () => metas q, flexible_type = flexible_type})
      end
    val intros = List.concat (map (lookup inet) conclusion)
    val elims = List.concat (map (List.concat o map lookup_elim) assumptions)
  in
    (* Each tag identifies one indexed rule, even if several spellings
       retrieve it. A single sort gives the same rule order. *)
    candidate_order (intros @ elims)
  end

fun unsafe_percent ({prio, ...} : rulespec) =
  Option.getOpt (prio, 50)

(* The engine consumes phases in this order.  Within a phase, safe rules
   retain claset tag order, and unsafe rules use decreasing success
   percentage before the same tag order. *)
fun aesop_class ({safe = true, ...} : rulespec) = 0
  | aesop_class _ = 1

fun compare_aentry
  ({tag = tag1, rule = {spec = spec1, ...}} : aentry,
   {tag = tag2, rule = {spec = spec2, ...}} : aentry) =
  case Int.compare (aesop_class spec1, aesop_class spec2) of
      EQUAL =>
        if #safe spec1 andalso #safe spec2 then
          compare_tag (tag1, tag2)
        else
          (case Int.compare
                  (unsafe_percent spec2, unsafe_percent spec1) of
               EQUAL => compare_tag (tag1, tag2)
             | order => order)
    | order => order

fun aesop_rules select (CS {index = {aesop_index, ...}, ...}) query =
  map #rule
    (Listsort.sort compare_aentry
      (clasetNet.unify query (select aesop_index)))

val aesop_target_rules = aesop_rules #target
fun aesop_hyp_rules_measured checkpoint
      (CS {distinct, index = {aesop_index, ...}, ...})
      (query as {q, qvars, ...}) =
    map #rule (Listsort.sort compare_aentry
      (clasetNet.unify {q = q, qvars = qvars} (#hyp aesop_index) @
       distinct_candidates
         {checkpoint = checkpoint, derive = listUtil.no_checkpoint}
         distinct query))

fun aesop_hyp_rules cs {q, qvars} =
  aesop_hyp_rules_measured listUtil.no_checkpoint cs
    {q = q, qvars = qvars, flexible_type = K true}

type tyinfo_contribution =
  string * (TypeBasePure.tyinfo -> (rulespec * (string * thm)) list)

type tyinfo_rule =
  {provider : string, tyname : string * string,
   spec : rulespec, named_th : string * thm}

type owned_tyinfo_rule =
  {provider : string, tyname : string * string, decl : decl}

(* An unforced state defers updates until the first demand. *)
datatype pending =
    Modify of (claset -> claset)
  | CatchUpTypeBase of tyinfo_contribution list
  | UpdateTypeInfo of
      {contributions : tyinfo_contribution list,
       tyi : TypeBasePure.tyinfo}
datatype readiness = Ready | Pending of pending list
type cstate = claset * owned_tyinfo_rule list * readiness

val state0 : cstate = (empty_cs, [], Pending [])

fun decl_is_live (CS {decls, ...}) (wanted : decl) =
  case find_decl decls (#name wanted) of
      SOME current => #index (#tag current) = #index (#tag wanted)
    | NONE => false

fun live_owned cs owned =
  List.filter (fn {decl, ...} => decl_is_live cs decl) owned

fun persistent_name name = KernelSig.name_toString name

(* Every theorem-set table spells its keys the same way, so normalise a
   user-written name to that spelling: a bare or "Thy.Name" source name
   becomes the "Thy$Name" key.  A name containing "$" is already a key,
   because theory names cannot contain "$", and a name ThmSetData.toKName
   rejects can spell no key at all; both come back unchanged, leaving
   each table to decide whether a name denoting nothing is a silent
   no-op (our retraction, which tries the source spelling too) or an
   error worth telling the user about (linarithData's, which shares
   this normalisation). *)
fun normalise_rule_name s =
    if String.isSubstring "$" s then s
    else (persistent_name (ThmSetData.toKName s) handle HOL_ERR _ => s)

(* Reconstruction replays deltas recorded by ancestor theories.  A rule that
   is ill-formed for its declared kind makes add_rule/make_rule_decl raise, so
   guard it: warn and drop, as take_looked_up does for a stale theorem,
   rather than letting one bad delta abort every descendant theory's load. *)
fun drop_illformed fname name cs =
  (HOL_WARNING "clasetLib" fname
     ("Dropping ill-formed persistent rule " ^ name); cs)

fun apply_add_delta fname addition cs =
  case take_looked_up addition of
      NONE => cs
    | SOME (name', spec', th) =>
        let val pname = persistent_name name' in
          add_rule spec' (pname, th) cs
          handle HOL_ERR _ => drop_illformed fname pname cs
        end

fun apply_cdelta (ADD addition) cs =
      apply_add_delta "apply_cdelta" addition cs
  | apply_cdelta (RM name) cs = remove_rule name cs

(* Values reconstructed for an ancestry always contain their complete set of
   persistent declarations, so they need no delayed replay. *)
fun apply_delta delta (cs, owned, _) =
  let val cs' = apply_cdelta delta cs
  in (cs', live_owned cs' owned, Ready) end

(* Add all declarations before rebuilding the nets.  Theory loading uses this
   once for a delta batch, rather than extending a net for each declaration. *)
fun update_decls (ADD addition) decls =
      (case take_looked_up addition of
           NONE => decls
         | SOME (name', spec', th) =>
             let val pname = persistent_name name' in
               #2 (extend_decl (make_rule_decl spec' (pname, th)) decls)
               handle HOL_ERR _ => drop_illformed "update_decls" pname decls
             end)
  | update_decls (RM name) decls = #2 (remove_decl name decls)

fun rebuild_claset decls wrappers distinct =
  CS {decls = decls, wrappers = wrappers, distinct = distinct,
      index =
        List.foldl (fn (decl, index) => add_decl decl index)
          empty_index (dest_decls decls)}

fun is_removal (RM _) = true
  | is_removal (ADD _) = false

fun apply_add_batch (ADD addition, cs) =
      apply_add_delta "update_decls" addition cs
  | apply_add_batch (RM _, _) =
      raise Fail "batch_apply: unexpected removal in ADD-only batch"

fun batch_apply deltas (cs as CS {decls, wrappers, distinct, ...}) =
  if List.exists is_removal deltas then
    let
      fun update (delta, (decls, removed)) =
        (update_decls delta decls,
         case delta of
             RM name => HOLset.add (removed, name)
           | ADD _ => removed)
      val (decls', removed) =
        List.foldl update (decls, HOLset.empty String.compare) deltas
      val distinct' = Redblackmap.filter
        (fn {source, ...} => not (HOLset.member (removed, #name source)))
        distinct
    in
      rebuild_claset decls' wrappers distinct'
    end
  else
    List.foldl apply_add_batch cs deltas

(* TypeBase facts are derived data: they are never ancestry deltas.  A
   contribution may decline a tyinfo by raising (as TypeBasePure's datatype
   accessors do for non-datatypes), so make the listener total.  Contributions
   are value providers and must be pure and deterministic: their invocation
   count and timing are deliberately not part of the public API. *)
val tyinfo_contributions = ref ([] : tyinfo_contribution list)

fun same_spec
  ({kind = kind1, safe = safe1, prio = prio1} : rulespec,
   {kind = kind2, safe = safe2, prio = prio2} : rulespec) =
  kind1 = kind2 andalso safe1 = safe2 andalso prio1 = prio2

fun same_tyinfo_rule
  ({provider, tyname, decl} : owned_tyinfo_rule,
   {provider = provider', tyname = tyname', spec,
    named_th = (name, th)} : tyinfo_rule) =
  provider = provider' andalso tyname = tyname' andalso
  #name decl = name andalso same_spec (#spec decl, spec) andalso
  aconv (concl (#orig decl))
    (concl (canonical_rule_of (#kind spec) th))

fun remove_owned ({decl, ...} : owned_tyinfo_rule) cs =
  if decl_is_live cs decl then remove_rule (#name decl) cs else cs

fun extract_matching _ [] = NONE
  | extract_matching owned (candidate :: rest) =
      if same_tyinfo_rule (owned, candidate) then SOME (candidate, rest)
      else
        Option.map
          (fn (found, rest') => (found, candidate :: rest'))
          (extract_matching owned rest)

fun reconcile_owned scope desired (cs, owned) =
  let
    fun reconcile [] remaining current rev_kept =
          ((current, List.rev rev_kept), remaining)
      | reconcile (entry :: rest) remaining current rev_kept =
          if not (scope entry) then
            reconcile rest remaining current (entry :: rev_kept)
          else
            (case extract_matching entry remaining of
                 SOME (_, remaining') =>
                   reconcile rest remaining' current (entry :: rev_kept)
               | NONE =>
                   reconcile rest remaining (remove_owned entry current)
                     rev_kept)
  in
    reconcile owned desired cs []
  end

fun add_tyinfo_rule
  ({provider, tyname, spec, named_th = (name, th)} : tyinfo_rule)
  (cs as CS {decls, wrappers, index, distinct}, owned) =
  let
    fun same_class (decl : decl) =
      #kind (#spec decl) = #kind spec andalso
      #safe (#spec decl) = #safe spec
  in
    if List.exists same_class (get_decls decls th) then (cs, owned)
    else
      let val candidate = make_rule_decl spec (name, th)
      in
        case extend_decl candidate decls of
            (NONE, _) => (cs, owned)
          | (SOME installed, decls') =>
              (CS {decls = decls', wrappers = wrappers, distinct = distinct,
                   index = add_decl installed index},
               {provider = provider, tyname = tyname,
                decl = installed} :: owned)
      end
  end

fun rules_for_tyinfo contributions (tyi : TypeBasePure.tyinfo) =
  let
    val tyname = TypeBasePure.ty_name_of tyi
    fun add_contribution
      ((provider, contribution) : tyinfo_contribution, rev_rules) =
      case Lib.total contribution tyi of
          NONE => rev_rules
        | SOME rules =>
            List.revAppend
              (map
                 (fn (spec, named_th) =>
                   {provider = provider, tyname = tyname,
                    spec = spec, named_th = named_th} : tyinfo_rule)
                 rules,
               rev_rules)
  in
    List.rev (List.foldl add_contribution [] contributions)
  end

fun apply_tyinfo_rules rules cs =
  List.foldl
    (fn (rule, acc) => add_tyinfo_rule rule acc)
    cs rules

fun collect_typebase_rules elts contributions =
  let
    fun collect (tyi, rev_rules) =
      List.revAppend (rules_for_tyinfo contributions tyi, rev_rules)
  in
    List.rev (List.foldl collect [] elts)
  end

fun catch_up_typebase elts cs =
  catch_up_distinct elts (#1
    (apply_tyinfo_rules
      (collect_typebase_rules elts (!tyinfo_contributions)) (cs, [])))

fun reconcile_typebase elts contributions state =
  let
    val (state', remaining) =
      reconcile_owned (fn _ => true)
        (collect_typebase_rules elts contributions) state
  in
    let val (cs, owned) = apply_tyinfo_rules remaining state'
    in (catch_up_distinct elts cs, owned) end
  end

fun reconcile_tyinfo contributions tyi state =
  let
    val tyname = TypeBasePure.ty_name_of tyi
    val (state', remaining) =
      reconcile_owned
        (fn {tyname = owned_name, ...} => owned_name = tyname)
        (rules_for_tyinfo contributions tyi) state
  in
    let val (cs, owned) = apply_tyinfo_rules remaining state'
    in (reconcile_distinct tyi cs, owned) end
  end

fun replay_pending elts typebase_rules [] (cs, owned, caught_up) =
      if caught_up then (cs, owned)
      else
        let val (cs', owned') = apply_tyinfo_rules typebase_rules (cs, owned)
        in (catch_up_distinct elts cs', owned') end
  | replay_pending elts typebase_rules (update :: updates)
      (cs, owned, caught_up) =
      (case update of
           CatchUpTypeBase catchup =>
             let
               val (cs', owned') =
                 reconcile_typebase elts catchup (cs, owned)
             in
               replay_pending elts typebase_rules updates
                 (cs', owned', true)
             end
         | Modify f =>
             let val cs' = f cs
             in
               replay_pending elts typebase_rules updates
                 (cs', live_owned cs' owned, false)
             end
         | UpdateTypeInfo {contributions, tyi} =>
             let
               val (cs', owned') =
                 reconcile_tyinfo contributions tyi (cs, owned)
             in
               replay_pending elts typebase_rules updates
                 (cs', owned', true)
             end)

fun init_state_of _ _ (state as (_, _, Ready)) = state
  | init_state_of elts contributions (cs, owned, Pending pending) =
    let
      val typebase_rules = collect_typebase_rules elts contributions
      val (cs', owned') =
        replay_pending elts typebase_rules (List.rev pending)
          (cs, owned, false)
    in
      (cs', owned', Ready)
    end

fun modify f (cs, owned, Ready) =
      let val cs' = f cs
      in (cs', live_owned cs' owned, Ready) end
  | modify f (cs, owned, Pending pending) =
      (cs, owned, Pending (Modify f :: pending))

fun apply_to_global delta = modify (apply_cdelta delta)

(* Loading invokes this once for all a theory's deltas.  In particular, an
   unforced global state retains the complete batch for one lazy replay. *)
fun batch_finaliser _ deltas = modify (batch_apply deltas)

val adresult : (cdelta, cstate) AncestryData.fullresult =
  AncestryData.fullmake {
    adinfo = {tag = "claset", initial_values = [("min", state0)],
              apply_delta = apply_delta},
    uptodate_delta = uptodate_delta,
    sexps = {dec = decode_delta, enc = encode_delta},
    globinfo = {apply_to_global = apply_to_global,
                thy_finaliser = SOME batch_finaliser,
                initial_value = state0}
  }

fun update_claset f = #update_global_value adresult (modify f)

(* A pending state caught up against a TypeBase.  The replay reads
   nothing but the state, the TypeBase's entries and the recorded
   contributions, all compared by identity, so a context whose own
   state stays pending -- a proof's snapshot -- replays it once rather
   than at every read. *)
val caught_up =
  memoUtil.keyed_memo
    (fn (state, elts, contributions) =>
     fn (state', elts', contributions') =>
       Portable.pointer_eq (state, state') andalso
       Portable.pointer_eq (contributions, contributions') andalso
       Lib.list_eq (Lib.curry Portable.pointer_eq) elts elts')
    (fn (state, elts, contributions) =>
       init_state_of elts contributions state)

(* The claset of the context given.  A state still pending is caught up
   in that context, reading its TypeBase (the theorems its deltas name
   were looked up when they were decoded or recorded).  The result is
   recorded, so that the replay is done once, unless the global state has
   moved on meanwhile, in which case the record is left to the state that
   moved it. *)
fun the_claset_of ctxt =
  case #get_global_value_of adresult ctxt of
      (cs, _, Ready) => cs
    | state =>
        let
          val state' =
            caught_up (state, TypeBase.elts_of ctxt, !tyinfo_contributions)
        in
          #update_global_value adresult
            (fn current =>
               if Portable.pointer_eq (current, state) then state'
               else current);
          #1 state'
        end

fun the_claset () = the_claset_of (Context.snapshot ())

fun temp_add_rule spec named_th = update_claset (add_rule spec named_th)

(* The global claset always carries the rules derived from TypeBase, so a
   global removal of one, under any spelling of its name, is refused rather
   than lasting only until the next TypeBase catch-up. *)
fun is_tyinfo_rule_name name =
  let
    val local_name =
      case String.fields (fn c => c = #"$" orelse c = #".") name of
          [_, local_name] => local_name
        | _ => name
  in
    String.isPrefix tyinfo_prefix local_name
  end

fun refuse_tyinfo_removal fname name =
  HOL_WARNING "clasetLib" fname
    ("Ignoring " ^ name ^ ": rules derived from TypeBase stay in the \
     \global claset; drop one with Del, or with remove_rule and with_claset")

fun temp_delrule name =
  if is_tyinfo_rule_name name then refuse_tyinfo_removal "temp_delrule" name
  else
    update_claset (remove_rule name o remove_rule (normalise_rule_name name))

val augment_claset = update_claset

fun request_typebase_catchup contributions
      (cs, owned, Ready) =
      let
        val (cs', owned') =
          reconcile_typebase (TypeBase.elts_of (Context.snapshot ()))
            contributions (cs, owned)
      in (cs', owned', Ready) end
  | request_typebase_catchup contributions
      (cs, owned, Pending pending) =
      (cs, owned, Pending (CatchUpTypeBase contributions :: pending))

fun register_tyinfo_contribution (entry as (key, _)) =
  let
    val contributions = update_alist entry (!tyinfo_contributions)
  in
    tyinfo_contributions := contributions;
    #update_global_value adresult (request_typebase_catchup contributions)
  end

fun typebase_update tyi =
  let
    fun update (cs, owned, Ready) =
          let
            val (cs', owned') =
              reconcile_tyinfo (!tyinfo_contributions) tyi (cs, owned)
          in
            (cs', owned', Ready)
          end
      | update (cs, owned, Pending pending) =
          (cs, owned,
           Pending
             (UpdateTypeInfo
                {contributions = !tyinfo_contributions, tyi = tyi} ::
              pending))
  in
    #update_global_value adresult update;
    tyi
  end

val _ = TypeBase.register_update_fn typebase_update

fun iff_rules name theorem =
  let
    val (outer_vars, _) = strip_forall (concl theorem)
    val outer_vars' = fresh_forall_vars theorem outer_vars
    val th = Drule.SPECL outer_vars' theorem
    val (prems, final) = boolSyntax.strip_imp_only (concl th)
    val safe = null prems
    fun spec kind = {kind = kind, safe = safe, prio = NONE}

    (* GEN_ALL's set traversal may reverse source binders.  Retain their
       declaration order, then generalise any remaining conclusion-only
       variables in GEN_ALL's established order. *)
    fun gen_all_ordered result =
      let
        val eligible =
          HOLset.difference
            (FVL [concl result] empty_tmset, hyp_frees result)
        val source =
          List.filter (fn variable => HOLset.member (eligible, variable))
            outer_vars'
        val remaining =
          List.foldl
            (fn (variable, variables) =>
              HOLset.delete (variables, variable))
            eligible source
      in
        GENL (source @ HOLset.listItems remaining) result
      end

    (* The derived iff/not rule initially has the source antecedents as
       hypotheses and its new major premise last.  Discharge the source
       antecedents first, then the major, to put the major premise at the
       front as Isabelle's rotate_prems n does. *)
    fun rotate_major major result =
      gen_all_ordered
        (DISCH major (Lib.itlist DISCH prems result))

    (* Move source antecedents into hypotheses so that rotate_major can
       discharge them behind the new major premise. *)
    fun undisch_prems () = Lib.funpow (length prems) Drule.UNDISCH th

    fun equality_rules () =
      let
        val core = undisch_prems ()
        val (left, right) = boolSyntax.dest_eq final
        val (forward, backward) = EQ_IMP_RULE core
        val intro = rotate_major right (MP backward (ASSUME right))
        val dest = rotate_major left (MP forward (ASSUME left))
      in
        [(spec clasetRules.Intro, (name ^ "_intro", intro)),
         (spec clasetRules.Dest, (name ^ "_dest", dest))]
      end

    fun not_rule () =
      let
        val core = undisch_prems ()
        val major = boolSyntax.dest_neg final
        val false_th = MP (NOT_ELIM core) (ASSUME major)
        val result_var =
          variant (free_varsl (concl core :: hyp core))
            (mk_var ("iff_result", Type.bool))
        val result = MP (SPEC result_var boolTheory.FALSITY) false_th
        val elim = rotate_major major result
      in
        [(spec clasetRules.Elim, (name ^ "_elim", elim))]
      end
  in
    if boolSyntax.is_eq final andalso
       type_of (fst (boolSyntax.dest_eq final)) = Type.bool
    then equality_rules ()
    else if boolSyntax.is_neg final then not_rule ()
    else
      [(spec clasetRules.Intro,
        (name ^ "_intro", gen_all_ordered th))]
  end

fun number_contribution make_rule ths =
  List.concat (Lib.mapi make_rule ths)

fun injectivity_contribution tyi =
  case Lib.total TypeBasePure.one_one_of tyi of
      SOME (SOME th) =>
        let
          val stem = tyinfo_stem tyi ^ "_inject_"
          fun make_rule index conjunct =
            iff_rules (stem ^ Int.toString index) conjunct
        in
          number_contribution make_rule (CONJUNCTS th)
        end
    | _ => []

val _ = register_tyinfo_contribution
  ("claset-injectivity", injectivity_contribution)

fun export_rule spec name =
  let
    val thname = ThmSetData.toKName name
    val delta = ADD (look_up {name = thname, spec = spec})
  in
    #record_delta adresult delta;
    #update_global_value adresult (apply_to_global delta)
  end

fun delrule name =
  if is_tyinfo_rule_name name then refuse_tyinfo_removal "delrule" name
  else
    let val delta = RM (normalise_rule_name name)
    in
      #record_delta adresult delta;
      #update_global_value adresult (apply_to_global delta)
    end

(* The DB reconstruction is the raw ancestry-persistent view.  TypeBase facts
   are derived from the caller's ambient state and are never deltas. *)
fun persistent_claset_of_theory thy = Option.map #1 (#DB adresult thy)

(* Preserve the historical effective view by catching the persistent state up
   with the caller's current TypeBase, just as [the_claset] does. *)
fun claset_of_theory thy =
  Option.map (catch_up_typebase (TypeBase.elts_of (Context.snapshot ())))
    (persistent_claset_of_theory thy)
fun merge_clasets thys =
  Option.map (catch_up_typebase (TypeBase.elts_of (Context.snapshot ())) o #1)
    (#merge adresult thys)
fun with_claset cs =
  AncestryData.with_temp_value adresult (cs, [], Ready)

fun priority_error attrname =
  raise mk_HOL_ERR "clasetLib" "attribute"
    ("Invalid priority for attribute " ^ attrname ^
     "; expected one integer from 1 to 100")

fun safe_priority_error attrname =
  raise mk_HOL_ERR "clasetLib" "attribute"
    ("Arguments not allowed for attribute " ^ attrname ^
     "; safe-rule priorities are not supported")

fun penalty_error attrname =
  raise mk_HOL_ERR "clasetLib" "attribute"
    ("Invalid penalty for attribute " ^ attrname ^
     "; expected one integer")

(* Int.fromString both accepts shapes an attribute argument may not take
   (leading whitespace, a "+" sign, trailing text) and raises Overflow
   rather than returning NONE for a numeral too large for a fixed-width
   Int.  The shape is therefore checked first and the conversion itself is
   guarded, so that every malformed argument yields the documented
   HOL_ERR. *)
fun decimal_int arg =
  if size arg > 0 andalso CharVector.all Char.isDigit arg then
    Option.join (Lib.total Int.fromString arg)
  else NONE

fun signed_decimal_int arg =
  if String.isPrefix "~" arg then
    Option.map Int.~ (decimal_int (String.extract (arg, 1, NONE)))
  else decimal_int arg

fun priority_spec attrname (spec : rulespec) args =
  case args of
      [] => spec
    | [arg] =>
        (case decimal_int arg of
             SOME priority =>
               if 1 <= priority andalso priority <= 100 then
                 {kind = #kind spec, safe = false, prio = SOME priority}
               else priority_error attrname
           | NONE => priority_error attrname)
    | _ => priority_error attrname

fun penalty_spec attrname (spec : rulespec) args =
  case args of
      [] => spec
    | [arg] =>
        (case signed_decimal_int arg of
             SOME penalty =>
               {kind = #kind spec, safe = #safe spec, prio = SOME penalty}
           | NONE => penalty_error attrname)
    | _ => penalty_error attrname

fun register_checked_rule_attribute (attrname, checked_spec) =
  let
    fun storedf {name, args, ...} =
      export_rule (checked_spec args) name
    fun localf {name, args, thm, ...} =
      temp_add_rule (checked_spec args) (name, thm)
  in
    ThmAttribute.register_attribute
      (attrname, {storedf = storedf, localf = localf})
  end

fun register_rule_attribute (attrname, spec) =
  register_checked_rule_attribute
    (attrname,
     fn args =>
       if #safe spec then
         if List.null args then spec else safe_priority_error attrname
       else priority_spec attrname spec args)

val _ = List.app register_rule_attribute
  [("intro", intro_spec), ("sintro", sintro_spec),
   ("elim", elim_spec), ("selim", selim_spec),
   ("dest", dest_spec), ("sdest", sdest_spec),
   ("forward", forward_spec), ("sforward", sforward_spec)]

val _ =
  register_checked_rule_attribute
    ("norm", penalty_spec "norm" norm_spec)

(* Structural node count used only to weight rules: each leaf counts 1, an
   application sums its parts, an abstraction adds 1 for the binder.  This is
   a deliberate local metric, not the kernel's Term.term_size. *)
fun default_term_size tm =
  case dest_term tm of
      COMB (rator, rand) =>
        default_term_size rator + default_term_size rand
    | LAMB (_, body) => 1 + default_term_size body
    | _ => 1

fun default_goal_size (asl, w) =
  List.foldl (fn (asm, size) => default_term_size asm + size)
    (default_term_size w) asl

val claset_config =
  {hyp_subst_tac = BasicProvers.VAR_EQ_TAC,
   size_of = default_goal_size}

end

fun mk_marker_const name =
  prim_mk_const {Thy = "clasetMarker", Name = name}

val SIntro_t = mk_marker_const "SIntro"
val Intro_t = mk_marker_const "Intro"
val SElim_t = mk_marker_const "SElim"
val Elim_t = mk_marker_const "Elim"
val SDest_t = mk_marker_const "SDest"
val Dest_t = mk_marker_const "Dest"
val Simp_t = mk_marker_const "Simp"
val Iff_t = mk_marker_const "Iff"
val Norm_t = mk_marker_const "Norm"
val Forward_t = mk_marker_const "Forward"
val SForward_t = mk_marker_const "SForward"
val Del_t = mk_marker_const "Del"

val SIntro = markerLib.genCong clasetMarkerTheory.SIntro_def
val Intro = markerLib.genCong clasetMarkerTheory.Intro_def
val SElim = markerLib.genCong clasetMarkerTheory.SElim_def
val Elim = markerLib.genCong clasetMarkerTheory.Elim_def
val SDest = markerLib.genCong clasetMarkerTheory.SDest_def
val Dest = markerLib.genCong clasetMarkerTheory.Dest_def
val Simp = markerLib.genCong clasetMarkerTheory.Simp_def
val Iff = markerLib.genCong clasetMarkerTheory.Iff_def
val Norm = markerLib.genCong clasetMarkerTheory.Norm_def
val Forward = markerLib.genCong clasetMarkerTheory.Forward_def
val SForward = markerLib.genCong clasetMarkerTheory.SForward_def

val destSIntro =
  markerLib.genUnCong SIntro_t clasetMarkerTheory.SIntro_def
val destIntro = markerLib.genUnCong Intro_t clasetMarkerTheory.Intro_def
val destSElim = markerLib.genUnCong SElim_t clasetMarkerTheory.SElim_def
val destElim = markerLib.genUnCong Elim_t clasetMarkerTheory.Elim_def
val destSDest = markerLib.genUnCong SDest_t clasetMarkerTheory.SDest_def
val destDest = markerLib.genUnCong Dest_t clasetMarkerTheory.Dest_def
val destSimp = markerLib.genUnCong Simp_t clasetMarkerTheory.Simp_def
val destIff = markerLib.genUnCong Iff_t clasetMarkerTheory.Iff_def
val destNorm = markerLib.genUnCong Norm_t clasetMarkerTheory.Norm_def
val destForward =
  markerLib.genUnCong Forward_t clasetMarkerTheory.Forward_def
val destSForward =
  markerLib.genUnCong SForward_t clasetMarkerTheory.SForward_def

val Del = markerLib.genmktagged clasetMarkerTheory.Del_def
val destDel = markerLib.gendest_tagged Del_t

datatype marker_payload = Theorem of thm | DeleteName of string
type marker_info =
  {name : string, spec : rulespec option, payload : marker_payload}

type marker_registration =
  {spec : rulespec option, dest : thm -> marker_payload option}

fun theorem_marker name spec dest : string * marker_registration =
  (name, {spec = spec, dest = Option.map Theorem o dest})

val marker_registry = Symtab.make
  [theorem_marker "SIntro" (SOME sintro_spec) destSIntro,
   theorem_marker "Intro" (SOME intro_spec) destIntro,
   theorem_marker "SElim" (SOME selim_spec) destSElim,
   theorem_marker "Elim" (SOME elim_spec) destElim,
   theorem_marker "SDest" (SOME sdest_spec) destSDest,
   theorem_marker "Dest" (SOME dest_spec) destDest,
   theorem_marker "Simp" NONE destSimp,
   theorem_marker "Iff" NONE destIff,
   theorem_marker "Norm" (SOME norm_spec) destNorm,
   theorem_marker "Forward" (SOME forward_spec) destForward,
   theorem_marker "SForward" (SOME sforward_spec) destSForward,
   ("Del", {spec = NONE, dest = Option.map DeleteName o destDel})]

fun marker_of theorem =
  let val conclusion = concl theorem
  in
    if not (is_comb conclusion) then NONE
    else
      let val head = rator conclusion
      in
        if not (is_const head) then NONE
        else
          case dest_thy_const head of
              {Thy = "clasetMarker", Name = name, ...} =>
                (case Symtab.lookup marker_registry name of
                     NONE => NONE
                   | SOME {spec, dest} =>
                       Option.map
                         (fn payload =>
                           {name = name, spec = spec, payload = payload})
                         (dest theorem))
            | _ => NONE
      end
  end

val marker_prefix = "__claset_marker_"

fun invocation_marker_rules cs =
  List.filter
    (fn (_, (name, _)) => String.isPrefix marker_prefix name)
    (rules_of cs)

(* The first "<prefix><n>" with n at least [from] that no declaration
   already uses.  Invocation-scoped rules are named this way so that a
   marker argument can never collide with a user declaration. *)
fun fresh_rule_name_indexed {prefix, from} (CS {decls, ...}) =
  let
    fun find index =
      let val name = prefix ^ Int.toString index
      in
        if clasetRules.decl_name_member decls name then find (index + 1)
        else (name, index)
      end
  in
    find from
  end

fun fresh_rule_name options cs = #1 (fresh_rule_name_indexed options cs)

fun classical_rule ({kind=clasetRules.Intro,...} : rulespec) = true
  | classical_rule {kind=clasetRules.Elim,...} = true
  | classical_rule {kind=clasetRules.Dest,...} = true
  | classical_rule _ = false

fun process_claset_tags thms cs =
  let
    fun process (cs, rest, _) [] = (cs, List.rev rest)
      | process (cs, rest, from) (th :: ths) =
          case marker_of th of
              SOME {spec=SOME spec,payload=Theorem rule,...} =>
                if classical_rule spec then
                  let
                    val (name, index) = fresh_rule_name_indexed
                      {prefix = marker_prefix, from = from} cs
                  in
                    process (add_rule spec (name, rule) cs, rest, index) ths
                  end
                else
                  process (cs, th :: rest, from) ths
            | SOME {payload=DeleteName name,...} =>
                let
                  val next =
                    if String.isPrefix marker_prefix name then 0 else from
                in
                  process (remove_rule name cs, rest, next) ths
                end
            | _ => process (cs, th :: rest, from) ths
  in
    process (cs, [], 0) thms
  end

type simp_arg_split =
  {simp_rules : thm list,
   iff_rules : thm list,
   simp_controls : thm list,
   rest : thm list}

datatype simp_arg_bucket = SimpRule | IffRule | SimpControl | Plain

fun simp_arg_bucket theorem =
  case marker_of theorem of
      SOME {name="Simp",payload=Theorem rule,...} => (SimpRule,rule)
    | SOME {name="Iff",payload=Theorem rule,...} => (IffRule,rule)
    | _ =>
        if markerLib.is_directive theorem
        then (SimpControl, theorem)
        else (Plain, theorem)

(* Each bucket keeps the arguments in the order they were given. *)
fun classify_simp_args theorems =
  let
    val tagged = map simp_arg_bucket theorems
    fun bucket wanted =
      List.mapPartial
        (fn (tag, theorem) => if tag = wanted then SOME theorem else NONE)
        tagged
  in
    {simp_rules = bucket SimpRule,
     iff_rules = bucket IffRule,
     simp_controls = bucket SimpControl,
     rest = bucket Plain}
  end

(* Markers naming a rule class only the aesop front end installs (see its
   own marker pass).  They survive process_claset_tags and mean nothing to
   a plain classical tactic, so they are reported rather than assumed. *)
fun aesop_marker_name theorem =
  case marker_of theorem of
      SOME {name="Norm",...} => SOME "Norm"
    | SOME {name="Forward",...} => SOME "Forward"
    | SOME {name="SForward",...} => SOME "SForward"
    | _ => NONE

(* Checked wherever arguments become assumptions, not only where the
   classical engines collect them: assuming a marker would leave a
   nonsense hypothesis on the goal with no diagnostic. *)
fun check_aesop_markers function theorems =
  case List.mapPartial aesop_marker_name theorems of
      [] => ()
    | name :: _ =>
        raise mk_HOL_ERR "clasetLib" function
          (name ^ " marker requires an Aesop-aware tactic")

(* process_claset_tags consumes the classical marker vocabulary.  Plain
   leftovers become inserted facts; generic simplifier controls are either
   unwrapped to their theorem payload or discarded as inert here. *)
fun invocation_facts theorems =
  let
    val {simp_rules, iff_rules, rest, ...} =
      classify_simp_args (map markerLib.strip_wrappers theorems)
  in
    if not (null simp_rules) then
      raise mk_HOL_ERR "clasetLib" "invocation_facts"
        "Simp marker requires a tactic with a simpset"
    else if not (null iff_rules) then
      raise mk_HOL_ERR "clasetLib" "invocation_facts"
        "Iff marker requires a tactic with a simpset"
    else (check_aesop_markers "invocation_facts" rest; rest)
  end

(* Matching uses applications with a constant head. After crossing an
   abstraction on the fact's side, check that the site's variables also
   occur free in the whole fact. *)
fun matchable_subterms_with charge under_abstraction term =
  let
    fun head_name sub =
      if is_comb sub then head_name (rator sub)
      else if is_const sub then SOME (fst (dest_const sub))
      else NONE

    (* Visit in [find_terms] order, returning the sites in reverse.  Every
       operator in an application spine has the same head. *)
    fun visit head under_binder sub sites =
      let val _ = charge searchBudget.Candidate
      in
        if is_comb sub then
          let
            val (operator, operand) = dest_comb sub
            val name =
              case head of
                  NONE => head_name operator
                | SOME known => known
            val sites' =
              case name of
                  SOME key =>
                    if not under_binder orelse under_abstraction sub
                    then (key, sub) :: sites else sites
                | NONE => sites
          in
            visit NONE under_binder operand
              (visit (SOME name) under_binder operator sites')
          end
        else if is_abs sub then visit NONE true (body sub) sites
        else sites
      end
  in
    visit NONE false term []
  end

fun matching_pairs_with charge goal_terms patterns =
  let
    val sites =
      List.concat
        (map (matchable_subterms_with charge (fn _ => true)) goal_terms)
  in
    List.concat
      (map
        (fn (pattern_head, pattern) =>
          List.mapPartial
            (fn (site_head, site) =>
              if (charge searchBudget.Candidate; pattern_head = site_head)
              then SOME (pattern, site)
              else NONE)
            sites)
        patterns)
  end

fun match_indexed_sites goal_terms =
  let
    (* Prepend from the right to preserve the original order within a head. *)
    val sites =
      Portable.HOLSusp.delay
        (fn () =>
          List.foldr
            (fn ((head, site), index) =>
              Redblackmap.insertWith
                (fn (later, earlier) => earlier @ later)
                (index, head, [site]))
            (Redblackmap.mkDict String.compare)
            (List.concat
              (map (matchable_subterms_with (fn _ => ()) (fn _ => true))
                 goal_terms)))
  in
    (* Match within each bucket without collecting the candidate pairs. *)
    fn match =>
      fn [] => []
       | patterns =>
           let val index = Portable.HOLSusp.force sites
           in
             List.concat
               (map
                 (fn (head, pattern) =>
                   List.mapPartial (fn site => match (pattern, site))
                     (Option.getOpt (Redblackmap.peek (index, head), [])))
                 patterns)
           end
  end

fun compare_type_binding ({redex, residue}, {redex = other, residue = value}) =
  Lib.pair_compare (Type.compare, Type.compare)
    ((redex, residue), (other, value))

val compare_type_substitution = List.collate compare_type_binding

(* The inputs are ordered by redex, with each variable bound once. *)
fun sorted_types_compatible
      ((left as {redex, residue} :: ls) : (hol_type, hol_type) Lib.subst)
      (right as {redex = other, residue = value} :: rs) =
      (case Type.compare (redex, other) of
           LESS => sorted_types_compatible ls right
         | GREATER => sorted_types_compatible left rs
         | EQUAL =>
             Type.compare (residue, value) = EQUAL andalso
             sorted_types_compatible ls rs)
  | sorted_types_compatible _ _ = true

(* If every binding agrees, the compatibility graph is complete and its
   sole maximal clique is the full input. Preserve the first occurrence
   of each binding, as in the general clique union. *)
fun complete_type_join substitutions =
  let
    exception Conflict
    fun add (binding as {redex, residue}, state as (seen, reversed)) =
      case Redblackmap.peek (seen, redex) of
          NONE => (Redblackmap.insert (seen, redex, residue),
                   binding :: reversed)
        | SOME earlier =>
            if Type.compare (earlier, residue) = EQUAL then state
            else raise Conflict
    val (_, reversed) = List.foldl
      (fn (types, state) => List.foldl add state types)
      (Redblackmap.mkDict Type.compare, []) substitutions
  in SOME (List.rev reversed) end
  handle Conflict => NONE

(* Maximal compatible unions avoid enumerating every compatible subset. *)
fun maximal_type_joins_with budgeted charge ordered substitutions =
  case substitutions of
      [] => []
    | [_] => []
    | _ =>
        let
          fun compatible
                (left : (hol_type, hol_type) Lib.subst) right =
            (charge searchBudget.Candidate;
             List.all
               (fn {redex, residue} =>
                 case List.find
                        (fn {redex = other, residue = _} =>
                          Type.compare (redex, other) = EQUAL) right of
                     NONE => true
                   | SOME {redex = _, residue = other} =>
                       Type.compare (residue, other) = EQUAL)
               left)
          fun same_types left right =
            length left = length right andalso
            (charge searchBudget.Candidate;
             List.all
               (fn {redex, residue} =>
                 List.exists
                   (fn {redex = other, residue = value} =>
                     Type.compare (redex, other) = EQUAL andalso
                     Type.compare (residue, value) = EQUAL)
                   right)
               left)
          val unique =
            if budgeted then
              List.foldl
                (fn (types, kept) =>
                  if List.exists (same_types types) kept then kept
                  else kept @ [types]) [] substitutions
            else substitutions
          val direct =
            case unique of
                [] => SOME []
              | [_] => SOME []
              | _ =>
                  if budgeted then NONE
                  else Option.map (fn joined => [joined])
                         (complete_type_join unique)
        in
          case direct of
              SOME joins => joins
            | NONE =>
                let
                  val parts = Vector.fromList unique
                  val count = Vector.length parts
                  val neighbors = Array.array (count, [])
                  fun connect i =
                    let
                      val matches =
                        case ordered of
                            NONE =>
                              let val left = Vector.sub (parts, i)
                              in fn j => compatible left (Vector.sub (parts, j))
                              end
                          | SOME keyed =>
                              let val left = Vector.sub (keyed, i)
                              in fn j => sorted_types_compatible left
                                           (Vector.sub (keyed, j))
                              end
                      fun visit j =
                        if j = count then ()
                        else
                          (if matches j then
                             (Array.update (neighbors, i,
                                j :: Array.sub (neighbors, i));
                              Array.update (neighbors, j,
                                i :: Array.sub (neighbors, j)))
                           else ();
                           visit (j + 1))
                    in
                      visit (i + 1)
                    end
                  val _ = List.app connect (List.tabulate (count, I))
                  (* The connection loop visits each vertex's neighbors in
                     increasing order, so each list is already descending.
                     Store only edges, with binary search within each row. *)
                  val rows = Vector.tabulate (count,
                    fn i => Vector.fromList (Array.sub (neighbors, i)))
                  fun adjacent i j =
                    let
                      val _ = charge searchBudget.Candidate
                      val row = Vector.sub (rows, i)
                      fun find low high =
                        if low >= high then false
                        else
                          let val mid = low + (high - low) div 2 in
                            case Int.compare (j, Vector.sub (row, mid)) of
                                LESS => find (mid + 1) high
                              | EQUAL => true
                              | GREATER => find low mid
                          end
                    in find 0 (Vector.length row) end
                  fun intersect i candidates =
                    List.filter (adjacent i) candidates
                  fun score i pending =
                    List.foldl
                      (fn (j, size) => if adjacent i j then size + 1
                                      else size)
                      0 pending
                  fun pivot pending first rest excluded =
                    let
                      fun consider (i, (best, best_score)) =
                        let val size = score i pending
                        in
                          if size > best_score then (i, size)
                          else (best, best_score)
                        end
                    in
                      #1 (List.foldl consider
                        (List.foldl consider
                          (first, score first pending) rest)
                        excluded)
                    end
                  val found = ref []
                  fun visit chosen [] [] =
                        (charge searchBudget.Candidate;
                         found := Listsort.sort Int.compare chosen :: !found)
                    | visit _ [] _ = ()
                    | visit chosen (pending as first :: rest) excluded =
                      let
                        val selected = pivot pending first rest excluded
                        val candidates =
                          List.filter (fn j => not (adjacent selected j))
                            pending
                        fun branches [] _ _ = ()
                          | branches (i :: rest) available seen =
                              (visit (i :: chosen)
                                 (intersect i available) (intersect i seen);
                               branches rest
                                 (List.filter (fn j => i <> j) available)
                                 (i :: seen))
                      in
                        branches candidates pending excluded
                      end
                  val _ = visit [] (List.tabulate (count, fn i => i)) []
                  val cliques =
                    Listsort.sort (List.collate Int.compare) (!found)
                  fun union_measured indices =
                    List.foldl
                      (fn (i, joined) =>
                        List.foldl
                          (fn ({redex, residue}, kept) =>
                            if List.exists
                                 (fn {redex = other, residue = _} =>
                                   (charge searchBudget.Candidate;
                                    Type.compare (redex, other) = EQUAL))
                                 kept then kept
                            else kept @ [{redex = redex, residue = residue}])
                          joined (Vector.sub (parts, i))) [] indices
                in
                  List.mapPartial
                    (fn indices =>
                      case indices of
                          [] => NONE
                        | [_] => NONE
                        | _ =>
                            if budgeted then SOME (union_measured indices)
                            else
                              (* The clique's substitutions agree pairwise. *)
                              complete_type_join
                                (map (fn i => Vector.sub (parts, i)) indices))
                    cliques
                end
        end

(* A fact reaches a goal as an assumption, and the kernel fixes an
   assumption's type variables.  The same statement declared to the
   claset is instantiated freely, so a fact stated at [:'a -> 'b] is
   unusable exactly where a rule at that statement would apply:
   [bijI] at [INJ f s t ==> SURJ f s t ==> BIJ f s t] says nothing
   about a goal at one type until its [:'b] is [:'a].  Isabelle's
   [using] leaves a fact's type variables schematic and instantiates
   them per use; the instances a goal determines are built here
   instead.

   A fact carrying a type variable the goal never mentions says
   nothing the goal can use as written: its atoms are at a type no
   term of the goal is at, so nothing it states can meet anything the
   goal states.  Such a fact is replaced by the instances the goal
   determines for it.

   A fact whose type variables the goal does mention is kept and the
   instances are offered beside it.  Mentioning is by name and what
   decides the fact is where the goal applies it:
   [source_sorted_all_distinct_unique] is at [:'a] and a goal about
   sorted mapped lists mentions [:'a] and [:'b] both, needing the fact
   at the second, so reading the name as cover leaves it assumed at a
   type the goal never states it at -- measured under that reading, the
   goal fails at 0.698s with the fact as written and closes at 0.019s
   with it at the goal's types.  Keeping the fact is what the guesswork
   an instance risks asks for, and it costs nothing: [image_cong] meets
   an equality at the goal's element type and one at its image type,
   where the instance the goal needs is the citation itself, and the
   citation still stands.

   A match then contributes only where it leaves alone the type
   variables the fact shares with the goal through a genuine free
   variable of its own, and the types of its support hypotheses.
   Quantified variables are specialized freshly after that
   classification, and loose type variables are freshened apart from
   the goal before matching.  Thus neither binder nor type-variable
   spelling determines which instances are offered. *)
fun goal_variables goal_terms =
  (Term.FVL goal_terms Term.empty_tmset,
   List.foldl (fn (term, seen) => Lib.union (type_vars_in_term term) seen)
     [] goal_terms)

fun polymorphic_instances_with budgeted charge
      get_goal_variables match_sites fact original_types =
  let
    val quantified = fst (boolSyntax.strip_forall (Thm.concl fact))
    val specialized =
      Drule.SPECL (map (Term.genvar o Term.type_of) quantified) fact
    val body = Thm.concl specialized
    val (goal_variables, goal_type_variables) = get_goal_variables ()
    val fact_variables =
      Term.free_varsl (Thm.concl fact :: Thm.hyp fact)
    val alien = Lib.set_diff original_types goal_type_variables
    val support_types =
      List.foldl
        (fn (term, seen) => Lib.union (type_vars_in_term term) seen)
        [] (Thm.hyp fact)
    val fixed =
      List.foldl
        (fn (variable, seen) =>
          if HOLset.member (goal_variables, variable) then
            Lib.union (Type.type_vars (Term.type_of variable)) seen
          else
            seen)
        support_types fact_variables
    val loose = Lib.set_diff (type_vars_in_term body) fixed
    val fresh_types =
      map (fn ty => {redex = ty, residue = Type.gen_tyvar ()}) loose
    fun same_support left right =
      List.all
        (fn term =>
          List.exists
            (fn other =>
              (charge searchBudget.Candidate;
               Term.aconv term other)) right) left andalso
      List.all
        (fn term =>
          List.exists
            (fn other =>
              (charge searchBudget.Candidate;
               Term.aconv term other)) left) right
  in
    if null loose then [fact]
    else
      let
        val _ = charge searchBudget.Normalization
        val match_fact = Thm.INST_TYPE fresh_types fact
        val _ = charge searchBudget.Normalization
        val match_body =
          Thm.concl
            (Drule.SPECL
              (map (Term.genvar o Term.type_of)
                (fst (boolSyntax.strip_forall (Thm.concl match_fact))))
              match_fact)
        val match_loose = map #residue fresh_types
        val schematic = Portable.HOLSusp.delay
          (fn () => Term.FVL [match_body] Term.empty_tmset)
        fun eligible sub =
          case free_vars sub of
              [] => true
            | variables =>
                let val free = Portable.HOLSusp.force schematic
                in List.all (fn v => HOLset.member (free, v)) variables end
        val patterns =
          matchable_subterms_with charge eligible match_body
        fun instance_of (pattern, site) =
          (charge searchBudget.Candidate;
           case Lib.total (Term.match_term pattern) site of
              NONE => NONE
            | SOME (_, types) =>
                let
                  (* A match reports the type variables it leaves where
                     they are as well; those bind nothing. *)
                  val proper =
                    List.filter
                      (fn {redex, residue} =>
                        not (Type.compare (redex, residue) = EQUAL))
                      types
                in
                  if null proper then NONE
                  else if List.all
                            (fn {redex, ...} => Lib.mem redex match_loose)
                            proper
                  then SOME proper
                  else NONE
                end)
        val matched = match_sites instance_of patterns
        (* Retain each original binding order for INST_TYPE proof records.
           The ordered deduplication keys also serve the compatibility scan. *)
        val (substitutions, ordered) =
          case (budgeted, match_loose) of
              (true, _) => (matched, NONE)
            | (false, [_]) =>
                (listUtil.distinct_by compare_type_substitution I matched,
                 NONE)
            | _ =>
                let
                  val keyed = map
                    (fn types =>
                      (types, Listsort.sort compare_type_binding types))
                    matched
                  val unique = listUtil.distinct_by compare_type_substitution
                    #2 keyed
                in
                  (map #1 unique, SOME (Vector.fromList (map #2 unique)))
                end
        fun instantiate types =
          (charge searchBudget.Normalization;
           Thm.INST_TYPE types match_fact)
        fun add_measured_instance (types, kept) =
          let
            val instance = instantiate types
          in
            if List.exists
                 (fn earlier =>
                   (charge searchBudget.Candidate;
                    aconv (Thm.concl earlier) (Thm.concl instance))
                   andalso same_support (Thm.hyp earlier)
                     (Thm.hyp instance))
                 kept
            then kept
            else kept @ [instance]
          end
        fun add_indexed_instance (types, state as (seen, kept)) =
          let
            val instance = instantiate types
            (* The kernel returns hypotheses in Term.compare order. *)
            val key = (Thm.concl instance, Thm.hyp instance)
          in
            if HOLset.member (seen, key) then state
            else (HOLset.add (seen, key), instance :: kept)
          end
        fun collect add initial =
          let val singles = List.foldl add initial substitutions
          in
            (* Distinct proper substitutions for one type variable are
               incompatible. Measured search still charges for the pairs. *)
            case (budgeted, match_loose) of
                (false, [_]) => singles
              | _ =>
                  List.foldl add singles
                    (maximal_type_joins_with budgeted charge ordered
                       substitutions)
          end
        val instances =
          if budgeted then collect add_measured_instance []
          else
            List.rev (#2 (collect add_indexed_instance
              (HOLset.empty (Lib.pair_compare
                (Term.compare, List.collate Term.compare)), [])))
      in
        if null instances then [fact]
        else if null alien then fact :: instances
        else instances
      end
  end

fun goal_type_instances_with budgeted charge
      get_goal_variables match_sites fact =
  (charge searchBudget.Normalization;
   case type_vars_in_term (Thm.concl fact) of
       [] => [fact]
     | original_types =>
         polymorphic_instances_with budgeted charge
           get_goal_variables match_sites fact original_types)

(* ASSUME_TAC conses onto the assumption list, so the facts are assumed
   back-to-front to leave them in declaration order.  Order is observable:
   it is the recency tie-break the classical engines use when scanning
   assumptions, and what FIRST_ASSUM and friends see in the residue.
   The marker check stays where the tactic is built; the instances a
   fact is inserted at are the goal's, so they are taken when it runs. *)
fun insert_facts_tac_with budget facts =
  (check_aesop_markers "INSERT_FACTS_TAC" facts;
   fn goal as (assumptions, target) =>
     let
       val terms = target :: assumptions
       val variables = Portable.HOLSusp.delay (fn () => goal_variables terms)
       fun get_goal_variables () = Portable.HOLSusp.force variables
       val (budgeted, charge, match_sites) =
         case budget of
             NONE =>
               (false, fn _ => (), match_indexed_sites terms)
           | SOME owned =>
               let val charge = searchBudget.charge owned
                   fun match_sites match patterns =
                     List.mapPartial match
                       (matching_pairs_with charge terms patterns)
               in (true, charge, match_sites) end
       val instances =
         List.rev
           (List.concat
             (map
               (goal_type_instances_with budgeted charge
                 get_goal_variables match_sites)
               facts))
       fun assume fact inner ctxt =
         (charge searchBudget.Application;
          Tactic.ASSUME_TAC fact inner ctxt)
     in
       Tactical.MAP_EVERY assume instances goal
     end)

fun INSERT_FACTS_TAC facts =
  insert_facts_tac_with NONE facts

fun INSERT_FACTS_TAC_BUDGETED budget facts =
  insert_facts_tac_with (SOME budget) facts

(* A supplied fact that is an implication is declared to the invocation
   claset and left out of the assumptions.  Isabelle's [using] chains a
   fact whose type variables stay schematic and whose premises its
   reasoner resolves where the proof wants a rule; an assumption here
   is type-fixed -- the instances [goal_type_instances] offers are the
   eager approximation of the first half -- and is a rule only where
   the search makes one of it, through the quantifier and implication
   eliminations, which is the expensive route to the same step.

   The assumption is not merely redundant beside the rule: it enlarges
   the search the rule was meant to shorten, because both routes stay
   open at every node.  Measured on the sorted-unique chain of
   list_L6138, its two citations being the facts the source method
   names: inserted only, the goal fails at 75.2s; inserted and
   declared, it does not return inside 300s; declared and not
   inserted, it closes at 1.140s.

   Only an implication is declared instead of being inserted.  A fact
   that is not one stays an assumption: its shape can serve as a premise
   or occur under a connective.  Tableau search also gets a safe
   introduction view when such a fact has loose type variables, because
   an inserted assumption fixes them before a later goal exposes their
   useful carrier.  A negation is not an
   implication here: [is_imp_only] keeps [~P] opaque, which is what
   leaves a negated fact where the tableau reads it as a literal.  A
   fact the claset declines -- an implication whose shape makes no
   destruction rule -- stays an assumption too, so no fact is lost by
   the routing. *)
val invocation_fact_spec : rulespec =
  {kind = clasetRules.Dest, safe = false, prio = NONE}

val invocation_fact_prefix = "__invocation_fact_"

datatype fact_consumer = SafeFacts | SearchFacts | TableauFacts

(* Returns the claset the consumer runs against and the facts owed to
   the assumptions, in the order they were given. *)
fun declare_invocation_facts_with_charge charge
    consumer environment cs =
  let
    fun step (entry, (cs, assumed, from)) =
      let
        val _ = charge searchBudget.Candidate
        val fact = #theorem (clasetFacts.literal_view entry)
        fun install spec view keep_assumption =
          let
            val (name, index) = fresh_rule_name_indexed
              {prefix = invocation_fact_prefix, from = from} cs
            val theorem = #theorem (view : clasetFacts.view)
          in
            case Lib.total (add_derived_rule spec (name, theorem)) cs of
                SOME extended =>
                  (charge searchBudget.Application;
                   (extended, keep_assumption, index))
              | NONE => (cs, fact :: assumed, index)
          end
      in
        case
          if consumer <> SafeFacts then
            clasetFacts.implication_rule_view entry
          else NONE
        of
            SOME view => install invocation_fact_spec view assumed
          | NONE =>
              if consumer = TableauFacts andalso
                 clasetFacts.has_schematic_types entry then
                install sintro_spec (clasetFacts.schematic_view entry)
                  (fact :: assumed)
              else (cs, fact :: assumed, from)
      end
    val (declared_cs, reversed, _) =
      List.foldl step (cs, [], 0) (clasetFacts.facts environment)
  in
    (declared_cs, List.rev reversed)
  end

fun invocation_claset base theorems =
  let val (tagged, leftovers) = process_claset_tags theorems base
  in
    (tagged, invocation_facts leftovers)
  end

type 'a invocation_simpset =
  {base : 'a,
   extend :
     {iff_prefix : string, simp_rules : thm list, iff_rules : thm list,
      claset : claset, simpset : 'a, context : Context.t} ->
     claset * 'a}

(* The environment is scoped to the tactic application, where the goal and
   its fixed parameters are known.  Views are demanded by the consumer. *)
fun with_invocation_fact_env_raw create_environment
    {iff_prefix,extra_markers}
    body base_cs simpset =
  markerLib.ABBRS_THEN
    (fn theorems => fn goal => fn ctxt =>
      (let
        val (classical_cs, invocation_ss, simp_controls, leftovers) =
          case simpset of
              NONE =>
                let val (cs, facts) = invocation_claset base_cs theorems
                in (cs, NONE, [], facts)
                end
            | SOME {base,extend} =>
                let
                  val {simp_rules,iff_rules,simp_controls,rest} =
                    classify_simp_args theorems
                  val (extended_cs, extended_ss) =
                    extend
                      {iff_prefix=iff_prefix, simp_rules=simp_rules,
                       iff_rules=iff_rules, claset=base_cs, simpset=base,
                       context=ctxt}
                  val (cs, facts) =
                    process_claset_tags rest extended_cs
                in
                  (cs, SOME extended_ss, simp_controls, facts)
                end
        val (invocation_cs, facts) =
          extra_markers leftovers classical_cs
        val environment = create_environment goal facts
      in
        body invocation_cs invocation_ss simp_controls environment goal
          ctxt
      end))

fun with_invocation_fact_env_using insert create_environment charge
    {iff_prefix,extra_markers,consumer}
    body base_cs simpset =
  with_invocation_fact_env_raw
    create_environment
    {iff_prefix=iff_prefix, extra_markers=extra_markers}
    (fn cs => fn ss => fn controls => fn environment =>
      let
        val (search_cs, assumed) =
          declare_invocation_facts_with_charge charge
            consumer environment cs
      in
        Tactical.THEN
          (insert assumed,
           body search_cs ss controls environment)
      end)
    base_cs simpset

fun with_invocation_fact_env options body base_cs simpset =
  with_invocation_fact_env_using INSERT_FACTS_TAC
    clasetFacts.create (fn _ => ())
    options body base_cs simpset

fun with_invocation_fact_env_budgeted budget options body base_cs simpset =
  with_invocation_fact_env_using (INSERT_FACTS_TAC_BUDGETED budget)
    (clasetFacts.create_with_charge (searchBudget.charge budget))
    (searchBudget.charge budget)
    options body base_cs simpset

fun no_extra_markers theorems cs = (cs, theorems)

fun with_context_claset consumer body theorems goal ctxt =
  with_invocation_fact_env
    {iff_prefix="", extra_markers=no_extra_markers, consumer=consumer}
    (fn cs => fn _ => fn _ => fn _ => body cs)
    (the_claset_of ctxt)
    (NONE : unit invocation_simpset option) theorems goal ctxt

fun with_invocation_args {iff_prefix,extra_markers} body =
  with_invocation_fact_env
    {iff_prefix=iff_prefix, extra_markers=extra_markers,
     consumer=SearchFacts}
    (fn cs => fn ss => fn controls => fn _ =>
      body cs ss controls)

end
