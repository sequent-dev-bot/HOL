structure linarithData :> linarithData =
struct

open Abbrev HolKernel

val ERR = mk_HOL_ERR "linarithData"

fun same_type (left : hol_type) right = left = right

fun dest_divmod {dest_div,dest_mod} tm =
  case Lib.total dest_div tm of
      SOME args => SOME args
    | NONE => Lib.total dest_mod tm

fun injected_nonneg dest theorem tm =
  Option.map (fn numeral => Thm.SPEC numeral theorem) (Lib.total dest tm)

type linarith_instance = {
  ty : hol_type,
  discrete : {lessD : thm list} option,
  dest : {
    dest_plus : term -> term * term,
    dest_minus : (term -> term * term) option,
    dest_neg : (term -> term) option,
    dest_mult : term -> term * term,
    dest_div : (term -> term * term) option,
    dest_suc : (term -> term) option,
    dest_lit : term -> Arbrat.rat,
    mk_lit : Arbrat.rat -> term,
    dest_less : term -> term * term,
    dest_leq : term -> term * term
  },
  kit : {
    add_mono : thm list,
    mult_mono : thm list,
    not_less : thm,
    not_le : thm,
    neqE : thm,
    nonneg : term -> thm option
  },
  norm_conv : conv,
  nnf_rules : thm list,
  pre_split : thm list,
  atom_facts : term -> thm list
}

(* The dest record is matched whole, without a ... wildcard, so that a
   new destructor is a compile error here instead of a silently wrong
   complement at the sites that reason about it. *)
fun build_compound_ops
      ({dest = {dest_plus = _, dest_minus, dest_neg, dest_mult = _,
                dest_div, dest_suc, dest_lit = _, mk_lit = _,
                dest_less = _, dest_leq = _}, ...} : linarith_instance) =
  let
    fun recognises f tm = Option.isSome (Lib.total f tm)
  in
    List.mapPartial Lib.I
      [Option.map recognises dest_minus,
       Option.map recognises dest_neg,
       Option.map recognises dest_div,
       Option.map recognises dest_suc]
  end

type linarith_injection = {
  from_ty : hol_type,
  to_ty : hol_type,
  inj : term,
  hom : {le : thm, lt : thm, eq : thm, add : thm, mul : thm}
}

(* The registries below are the only mutable state a derivation can be
   read out of, and register_instance and register_injection are their
   only mutators, so one counter bumped there is an exact change signal
   for anything derived from them. *)
val registry_generation = Sref.new 0

fun generation () = Sref.value registry_generation

fun bump_generation () =
  Sref.update registry_generation (fn count => count + 1)

(* A memo whose key is read from the session rather than passed in:
   compute takes no argument, and each call reads key for itself. *)
fun memo_on key compute =
  let
    val cached = memoUtil.keyed_memo Lib.equal (fn _ => compute ())
  in
    fn () => cached (key ())
  end

fun memo compute = memo_on generation compute

(* Both directions of an equivalence, or an implication as it stands.
   Replay MATCH_MPs against the result, so a rule that is neither is
   offered unchanged and simply fails to match. *)
fun implications theorem =
  if boolSyntax.is_imp
       (snd (boolSyntax.strip_forall (Thm.concl theorem)))
  then [theorem]
  else
    let
      val (forward, backward) =
        Thm.EQ_IMP_RULE (Drule.SPEC_ALL theorem)
    in
      [Drule.GEN_ALL forward, Drule.GEN_ALL backward]
    end
    handle HOL_ERR _ => [theorem]

type instance_implications = {
  add_mono : thm list,
  mult_mono : thm list list,
  not_less : thm list,
  not_le : thm list,
  neqE : thm list,
  lessD : thm list
}

type instance_derived = {
  implications : instance_implications,
  compound_ops : (term -> bool) list
}

(* The kit is matched whole, for the reason dest is: a rule added to it
   is then a compile error here rather than a rule replay re-derives
   per certificate node.  Only a discrete carrier can strengthen a
   strict inequality to the non-strict one about its successor, so
   lessD is empty for a dense one and the LessD and NotLeDD
   justifications never arise for it. *)
fun derive_implications (instance : linarith_instance) =
  let
    val {add_mono, mult_mono, not_less, not_le, neqE, nonneg = _} =
      #kit instance
    val lessD =
      case #discrete instance of
          SOME {lessD} => lessD
        | NONE => []
  in
    {add_mono = List.concat (map implications add_mono),
     mult_mono = map implications mult_mono,
     not_less = implications not_less,
     not_le = implications not_le,
     neqE = implications neqE,
     lessD = List.concat (map implications lessD)}
  end

fun derive_instance instance =
  {implications = derive_implications instance,
   compound_ops = build_compound_ops instance}

val instance_registry =
  Sref.new ([] : (linarith_instance * instance_derived) list)

fun instance_entries () = Sref.value instance_registry

fun register_instance instance =
  let
    val ty = #ty instance
    fun same_carrier (entry, _) = same_type ty (#ty entry)
    val entry = (instance, derive_instance instance)
    val replaced =
      Sref.gen_update instance_registry
        (fn entries =>
          (entry :: List.filter (not o same_carrier) entries,
           List.exists same_carrier entries))
    val _ = bump_generation ()
  in
    if replaced then
      HOL_WARNING "linarithData" "register_instance"
        ("replacing the linarith instance for type " ^
         Parse.type_to_string ty)
    else
      ()
  end

(* Decomposition asks for the carrier of every subterm it examines, so
   the registry is indexed rather than scanned; register_instance keeps
   one entry per carrier, so the index loses nothing. *)
val instance_table =
  memo
    (fn () =>
      List.foldl
        (fn (entry as (instance, _), table) =>
          Redblackmap.insert (table, #ty instance, entry))
        (Redblackmap.mkDict Type.compare)
        (instance_entries ()))

fun instance_entry ty = Redblackmap.peek (instance_table (), ty)

fun instance_for ty = Option.map #1 (instance_entry ty)

val all_instances = memo (fn () => map #1 (instance_entries ()))

(* The entry itself is the key, not just its carrier type: an instance
   built and handed straight to replay, or one that has since been
   replaced, must get its own derivation rather than the registered
   instance's.  Identity is what decides that -- the carrier only says
   which entry could possibly be it -- and a comparison that says "not
   this one" when it is costs a recomputation, never a wrong answer. *)
fun derived_instance instance =
  case instance_entry (#ty instance) of
      SOME (entry, derived) =>
        if Portable.pointer_eq (entry, instance) then derived
        else derive_instance instance
    | NONE => derive_instance instance

fun instance_implications instance = #implications (derived_instance instance)

fun compound_ops instance = #compound_ops (derived_instance instance)

fun same_injection left right =
  (same_type (#from_ty left) (#from_ty right) andalso
   same_type (#to_ty left) (#to_ty right)) orelse
  Term.aconv (#inj left) (#inj right)

fun injection_at_top injection tm =
  case Lib.total Term.dest_comb tm of
      SOME (operator, _) => Term.aconv operator (#inj injection)
    | NONE => false

fun orient_injection_hom injection theorem =
  let
    val opened = Drule.SPEC_ALL theorem
    val (left, right) = boolSyntax.dest_eq (Thm.concl opened)
  in
    if injection_at_top injection left then opened
    else if injection_at_top injection right then Thm.SYM opened
    else opened
  end

fun injection_rewrites injection =
  let
    val hom = #hom injection
  in
    List.mapPartial
      (Lib.total (orient_injection_hom injection))
      [#add hom, #mul hom]
  end

(* REWR_CONV precomputes a pattern per rewrite, which is the work this
   whole derivation exists to do once.  No rewrites means nothing to
   do, which is what UNCHANGED says. *)
fun rewrites_conv [] = Conv.ALL_CONV
  | rewrites_conv rewrites =
      Conv.TOP_DEPTH_CONV
        (Conv.FIRST_CONV (map Conv.REWR_CONV rewrites))

(* The order homomorphisms decide that a relation lifts along the
   injection, and replay matches against their implications once per
   injection per theorem of a conversion closure, so they are derived
   here beside the rewrites that push the injection inwards again. *)
type derived_injection = {
  injection : linarith_injection,
  relation_imps : thm list,
  rewrites : thm list,
  rewrite_conv : conv
}

fun derive_injection injection =
  let
    val hom = #hom injection
    val rewrites = injection_rewrites injection
  in
    {injection = injection,
     relation_imps =
       List.concat (map implications [#le hom, #lt hom, #eq hom]),
     rewrites = rewrites,
     rewrite_conv = rewrites_conv rewrites}
  end

(* The registry holds the derivations themselves, so walking every
   injection's derivation costs no lookup at all. *)
val injection_registry = Sref.new ([] : derived_injection list)

fun injection_entries () = Sref.value injection_registry

fun register_injection injection =
  let
    val entry = derive_injection injection
  in
    Sref.update injection_registry
      (fn entries =>
        entry ::
        List.filter
          (not o same_injection injection o #injection) entries);
    bump_generation ()
  end

val derived_injections = injection_entries

val injections = memo (fn () => map #injection (injection_entries ()))

(* Indexed like the instances, and for the same reason: decomposition
   asks about the head of every application it meets and about the type
   of every factor whose injection it has to restore.  Registration
   keeps one entry per injected constant and one per ordered pair of
   types, so neither index loses an entry. *)
val injection_tables =
  memo
    (fn () =>
      let
        val entries = injection_entries ()
        fun add_typed (entry : derived_injection, table) =
          Redblackmap.insert
            (table,
             (#from_ty (#injection entry), #to_ty (#injection entry)),
             entry)
        fun add_const (entry : derived_injection, table) =
          Redblackmap.insert (table, #inj (#injection entry), entry)
        val by_types =
          Redblackmap.mkDict (Lib.pair_compare (Type.compare, Type.compare))
        val by_const = Redblackmap.mkDict Term.compare
      in
        (List.foldl add_typed by_types entries,
         List.foldl add_const by_const entries)
      end)

fun injection_for from_ty to_ty =
  Option.map #injection
    (Redblackmap.peek (#1 (injection_tables ()), (from_ty, to_ty)))

fun injection_by_const constant =
  Option.map #injection
    (Redblackmap.peek (#2 (injection_tables ()), constant))

val all_injection_rewrite_conv =
  memo
    (fn () =>
      rewrites_conv
        (List.concat (map #rewrites (injection_entries ()))))

(* The P-form test is the whole of split validation; the two channels
   differ only in how they name what they rejected. *)
fun check_asm_split function what theorem =
  (ignore (splitLib.is_asm_split theorem)
   handle HOL_ERR _ => raise ERR function ("Malformed " ^ what))

fun apply_arith_split_delta delta table =
  case delta of
      ThmSetData.ADD (name, theorem) =>
        (check_asm_split "apply_arith_split_delta"
           ("[arith_split] theorem " ^ KernelSig.name_toString name)
           theorem;
         thmTable.apply_delta delta table)
    | ThmSetData.REMOVE _ => thmTable.apply_delta delta table

val arith_data =
  thmTable.register
    {settype = "arith", initial_value = Symtab.empty,
     apply_delta = thmTable.apply_delta,
     apply_to_global = thmTable.apply_delta}

val arith_split_data =
  thmTable.register
    {settype = "arith_split", initial_value = Symtab.empty,
     apply_delta = apply_arith_split_delta,
     apply_to_global = apply_arith_split_delta}

val arith_facts_of = thmTable.thms_of arith_data
val arith_split_thms_of = thmTable.thms_of arith_split_data
fun arith_facts () = thmTable.thms arith_data
fun arith_split_thms () = thmTable.thms arith_split_data

fun remove_arith name =
  thmTable.remove
    {data = arith_data, apply_to_global = thmTable.apply_delta,
     error = ERR "remove_arith"} name

fun remove_arith_split name =
  thmTable.remove
    {data = arith_split_data, apply_to_global = apply_arith_split_delta,
     error = ERR "remove_arith_split"} name

(* The table's own theorems are the key, compared by pointer.  Its key
   set is not enough: an add under a name the table already holds --
   the re-declaration of an edited rule, in the session that edited it
   -- replaces the theorem in place and leaves the key set exactly as
   it was.  Nor would a counter bumped at the delta sites be, because
   AncestryData's set_ancestry installs a whole table without applying
   a delta to the old one.  The theorems move under all three, and a
   table rebuilt into equal but fresh theorems recomputes rather than
   answering out of the old one -- which costs a recomputation and
   nothing else.  Reading and comparing them costs a fraction of the
   split-net build it guards. *)
fun same_splits (left_generation, left_thms) (right_generation, right_thms) =
  left_generation = right_generation andalso
  Lib.list_eq (Lib.curry Portable.pointer_eq) left_thms right_thms

fun memo_with_splits compute =
  let
    val cached =
      memoUtil.keyed_memo same_splits (fn (_, splits) => compute splits)
  in
    fn ctxt => cached (generation (), arith_split_thms_of ctxt)
  end

type linarith_config = {neq_limit : int, split_limit : int}

val default_config : linarith_config = {neq_limit = 9, split_limit = 9}

val tracer =
  traceUtil.create {group = "linarith", max = 3,
                    emit = fn message => print ("linarith: " ^ message ^ "\n")}

(* Rendering a theorem or a term list costs more than the test that
   decides whether anyone will read it, so the message is a thunk. *)
fun trace_thm level threshold label theorem =
  traceUtil.trace level threshold
    (fn () => label ^ "\n" ^ Parse.thm_to_string theorem)

fun trace_items level threshold label render items =
  traceUtil.trace level threshold
    (fn () =>
       label ^
       (if null items then " <none>"
        else "\n" ^ String.concatWith "\n" (map render items)))

fun trace_terms level threshold label terms =
  trace_items level threshold label Parse.term_to_string terms

end
