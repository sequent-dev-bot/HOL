structure iffTestSupport =
struct

open HolKernel

(* Scripts name their own scenario rather than each shadowing [fail]. *)
fun failer scenario message = raise Fail (scenario ^ ": " ^ message)

fun fail message = failer "iff theory test" message

fun fetch_persistent name =
  case String.fields (equal #"$") name of
      [thy, theorem] => DB.fetch thy theorem
    | _ => raise Fail ("malformed persistent theorem name: " ^ name)

fun rewrite_changes_with simp_conv name ss =
  let
    val rewrite = Drule.SPEC_ALL (fetch_persistent name)
    val (_, final) = boolSyntax.strip_imp_only (concl rewrite)
    val source =
      if boolSyntax.is_eq final then fst (boolSyntax.dest_eq final)
      else if boolSyntax.is_neg final then boolSyntax.dest_neg final
      else final
    val result = Conv.QCONV (simp_conv ss []) source
  in
    not (aconv (snd (boolSyntax.dest_eq (concl result))) source)
  end

val rewrite_changes = rewrite_changes_with simpLib.SIMP_CONV
val extension_rewrite_changes = rewrite_changes_with simpLib.SIMP_CONV

fun has_iff_rewrite name =
  rewrite_changes name (BasicProvers.srw_ss ()) andalso
  extension_rewrite_changes name (clasimpLib.clasimp_ss ())

fun has_rule name =
  List.exists
    (fn (_, (name', _)) => name = name')
    (clasetLib.rules_of (clasetLib.the_claset ()))

fun has_named_rule name theorem =
  List.exists
    (fn (_, (name', theorem')) =>
      name = name' andalso aconv (concl theorem) (concl theorem'))
    (clasetLib.rules_of (clasetLib.the_claset ()))

(* Each shape of [iff] declaration derives its own rules, so a test names
   the shape it expects and the check is exact: a rule of another shape left
   behind is as much a defect as a missing one. *)
datatype iff_shape = IffShape | NegShape | PlainShape

val iff_rule_suffixes = ["_intro", "_dest", "_elim"]

fun shape_suffixes IffShape = ["_intro", "_dest"]
  | shape_suffixes NegShape = ["_elim"]
  | shape_suffixes PlainShape = ["_intro"]

fun iff_rule_stem name = name ^ ".__clasimp_iff"

fun has_iff_rules_of shape name =
  let
    val stem = iff_rule_stem name
    val expected = shape_suffixes shape
  in
    List.all
      (fn suffix =>
        has_rule (stem ^ suffix) = Lib.mem suffix expected)
      iff_rule_suffixes
  end

val has_iff_rules = has_iff_rules_of IffShape

(* The complement of every shape at once: what a retraction must leave. *)
fun has_any_iff_rules name =
  List.exists (fn suffix => has_rule (iff_rule_stem name ^ suffix))
    iff_rule_suffixes

(* How many fragments of [ss] carry one of the named iff rewrites.  Counting
   by fragment name would not do: ssfrag_names_of de-duplicates, and one
   theory can contribute several iff batches. *)
fun iff_fragment_count names ss =
  let
    val wanted =
      map (concl o Drule.SPEC_ALL o fetch_persistent) names
    fun carries fragment =
      List.exists
        (fn rewrite => List.exists (aconv (concl rewrite)) wanted)
        (simpLib.frag_rewrites fragment)
  in
    length (List.filter carries (simpLib.ssfrags_of ss))
  end

fun rewrites_to source target =
  let
    fun changes simp_conv ss =
      let
        val result = Conv.QCONV (simp_conv ss []) source
      in
        aconv (snd (boolSyntax.dest_eq (concl result))) target
      end
  in
    changes simpLib.SIMP_CONV (BasicProvers.srw_ss ()) andalso
    changes simpLib.SIMP_CONV (clasimpLib.clasimp_ss ())
  end

end
