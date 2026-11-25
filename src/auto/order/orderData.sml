structure orderData :> orderData =
struct

open HolKernel boolLib relationTheory orderRulesTheory

type axioms =
  {reflexive : thm option,
   transitive : thm option,
   antisymmetric : thm option,
   total : thm option}

type context =
  {relation : term,
   axioms : axioms,
   reduction : conv}

datatype literal =
    Weak of term * term
  | Strict of term * term
  | Equal of term * term
  | Distinct of term * term

type fact = {literal : literal, theorem : thm}

type meter = searchBudget.charger

fun candidate (meter : meter) = #candidate meter ()
fun application (meter : meter) = #application meter ()
fun normalization (meter : meter) = #normalization meter ()

(* ------------------------------------------------------------------ *)
(* Reading an atom                                                     *)
(* ------------------------------------------------------------------ *)

val strord_tm = prim_mk_const {Thy = "relation", Name = "STRORD"}

fun combination tm =
  if is_comb tm then SOME (dest_comb tm) else NONE

(* Exactly two arguments come off, and what is left is compared with the
   relation.  Peeling by [strip_comb] instead would break a relation
   that is itself an application -- [RC R] is one, and that is the shape
   a strict primitive is read in. *)
fun dest_pair tm =
  case combination tm of
      NONE => NONE
    | SOME (left, right) =>
        (case combination left of
             NONE => NONE
           | SOME (head, argument) => SOME (head, argument, right))

fun at_domain domain tm = Type.compare (type_of tm, domain) = EQUAL

fun equality_of domain (head, x, y) =
  if same_const equality head andalso at_domain domain x
  then SOME (x, y)
  else NONE

fun positive_literal relation domain atom =
  case dest_pair atom of
      NONE => NONE
    | SOME (pair as (head, x, y)) =>
        if aconv head relation then SOME (Weak (x, y))
        else
          case combination head of
              SOME (strord, argument) =>
                if same_const strord strord_tm andalso aconv argument relation
                then SOME (Strict (x, y))
                else NONE
            | NONE => Option.map Equal (equality_of domain pair)

fun negated_body tm =
  case combination tm of
      SOME (head, body) =>
        if same_const negation head then SOME body else NONE
    | NONE => NONE

(* ------------------------------------------------------------------ *)
(* Discovering the contexts a goal supplies                            *)
(* ------------------------------------------------------------------ *)

val order_definitions =
  [PreOrder, Order, WeakOrder, StrongOrder,
   LinearOrder, StrongLinearOrder, WeakLinearOrder]

val order_names =
  List.map
    (#Name o dest_thy_const o rator o lhs o snd o strip_forall o concl)
    order_definitions

fun names_order names tm =
  case dest_term tm of
      COMB (rator, rand) =>
        names_order names rator orelse names_order names rand
    | LAMB (_, body) => names_order names body
    | CONST {Thy = "relation", Name, ...} => Lib.mem Name names
    | _ => false

val expand_order_axioms = PURE_REWRITE_RULE order_definitions

val expand_weak_order = PURE_REWRITE_RULE [WeakOrder]

val axiom_names =
  ["reflexive", "irreflexive", "transitive", "antisymmetric",
   "total", "trichotomous"]

fun conjuncts_with meter theorem =
  let
    fun collect theorem reversed =
      (normalization meter;
       case Lib.total dest_conj (concl theorem) of
           SOME _ =>
             let val left = collect (CONJUNCT1 theorem) reversed
             in collect (CONJUNCT2 theorem) left end
         | NONE => theorem :: reversed)
  in
    List.rev (collect theorem [])
  end

(* One atomic axiom: the predicate's name and the relation it is about. *)
fun dest_axiom theorem =
  case Lib.total dest_comb (concl theorem) of
      NONE => NONE
    | SOME (predicate, relation) =>
        (case Lib.total dest_thy_const predicate of
             SOME {Thy = "relation", Name, ...} =>
               if Lib.mem Name axiom_names then SOME (Name, relation, theorem)
               else NONE
           | _ => NONE)

fun axioms_of_with meter theorems =
  let
    (* The named-order rewrites all need their defining constant.
       Ordinary relational facts can go straight to conjunct collection. *)
    fun atoms theorem =
      (normalization meter;
       List.mapPartial
         (fn atom => (candidate meter; dest_axiom atom))
         (conjuncts_with meter
           (if names_order order_names (concl theorem) then
              expand_order_axioms theorem
            else theorem)))
  in
    List.concat (List.map atoms theorems)
  end

(* Group by relation, keeping the order the goal presents them in so a
   run is reproducible. *)
fun group_with meter atoms =
  let
    fun add ((name, relation, theorem), groups) =
      let
        fun place [] = [(relation, [(name, theorem)])]
          | place ((r, entries) :: rest) =
              if (candidate meter; aconv r relation) then
                (r, (name, theorem) :: entries) :: rest
              else (r, entries) :: place rest
      in
        place groups
      end
  in
    List.map (fn (relation, entries) => (relation, List.rev entries))
      (List.foldl add [] atoms)
  end

fun group_unmetered [] = []
  | group_unmetered ((name, first, theorem) :: atoms) =
      let
        fun add ((name, relation, theorem), (keys, groups)) =
          (if Termtab.defined groups relation then keys else relation :: keys,
           Termtab.cons_list (relation, (name, theorem)) groups)
        fun many entries atoms =
          let
            val (keys, groups) = List.foldl add
              ([first], Termtab.update (first, entries) Termtab.empty) atoms
            (* The separate keys preserve the first spelling and input
               order of alpha-equivalent relations. *)
            fun collect (relation, ordered) =
              (relation, List.rev (Termtab.lookup_list groups relation)) ::
              ordered
          in
            List.foldl collect [] keys
          end
        fun one entries [] = [(first, List.rev entries)]
          | one entries (atoms as (name, relation, theorem) :: rest) =
              if aconv first relation then one ((name, theorem) :: entries) rest
              else many entries atoms
      in
        one [(name, theorem)] atoms
      end

fun lookup_with meter entries name =
  Option.map snd
    (List.find (fn (n, _) => (candidate meter; n = name)) entries)

(* The two derived axioms.  Totality is not usually stated: HOL4's linear
   orders carry [trichotomous], which with reflexivity is the same thing. *)
fun derive_total_with meter entries =
  case lookup_with meter entries "total" of
      SOME theorem => SOME theorem
    | NONE =>
        (case (lookup_with meter entries "reflexive",
               lookup_with meter entries "trichotomous") of
             (SOME r, SOME t) =>
               (application meter;
                SOME (MATCH_MP (MATCH_MP order_total_of_trichotomous r) t))
           | _ => NONE)

fun weak_context_with meter relation entries reduction =
  {relation = relation,
   axioms =
     {reflexive = lookup_with meter entries "reflexive",
      transitive = lookup_with meter entries "transitive",
      antisymmetric = lookup_with meter entries "antisymmetric",
      total = derive_total_with meter entries},
   reduction = reduction}

(* A strict primitive is turned into its reflexive closure on the way in.
   [order_strict_of_strong] states [R = STRORD (RC R)], whose right side
   contains its own left, so it is applied at the outermost position it
   matches and not underneath -- rewriting to a fixpoint would not
   terminate. *)
fun strict_reduction equation =
  Conv.QCONV (ONCE_DEPTH_CONV (REWR_CONV equation))

fun strict_context_with meter relation entries irreflexive transitive =
  let
    val _ = application meter
    val strong =
      MATCH_MP (MATCH_MP order_strong_of_parts irreflexive) transitive
    val _ = application meter
    val weak = MATCH_MP order_weak_of_strong strong
    val closure = rand (concl weak)
    val _ = application meter
    val equation = MATCH_MP order_strict_of_strong strong
    val _ = normalization meter
    val closure_atoms =
      List.mapPartial
        (fn atom => (candidate meter; dest_axiom atom))
        (conjuncts_with meter (expand_weak_order weak))
    val closure_entries = List.map (fn (n, _, th) => (n, th)) closure_atoms
    val trichotomous_entries =
      case lookup_with meter entries "trichotomous" of
          NONE => []
        | SOME theorem =>
            (application meter;
             [("trichotomous", MATCH_MP order_trichotomous_of_RC theorem)])
  in
    weak_context_with meter closure
      (closure_entries @ trichotomous_entries)
      (strict_reduction equation)
  end

fun context_of_with meter (relation, entries) =
  case lookup_with meter entries "transitive" of
      NONE => NONE
    | SOME transitive =>
        (case (lookup_with meter entries "irreflexive",
               lookup_with meter entries "reflexive") of
             (SOME irreflexive, NONE) =>
               SOME
                 (strict_context_with meter relation entries
                   irreflexive transitive)
           | _ =>
               SOME (weak_context_with meter relation entries Conv.ALL_CONV))

fun contexts_using group meter theorems =
  List.mapPartial (context_of_with meter)
    (group (axioms_of_with meter theorems))

fun contexts meter = contexts_using (group_with meter) meter

val contexts_unmetered =
  contexts_using group_unmetered searchBudget.free_charger

val all_order_names = axiom_names @ order_names

fun has_order_axiom theorems =
  List.exists (fn theorem => names_order all_order_names (concl theorem))
    theorems

(* ------------------------------------------------------------------ *)
(* Reading a fact                                                      *)
(* ------------------------------------------------------------------ *)

fun negated_rule_with meter rule {reflexive, total, ...} =
  case (reflexive, total) of
      (SOME r, SOME t) =>
        let
          val pending =
            Portable.HOLSusp.delay (fn () => MATCH_MP (MATCH_MP rule r) t)
        in
          (* Each use retains its original charge and cutoff point. *)
          fn () => (application meter; SOME (Portable.HOLSusp.force pending))
        end
    | _ => (fn () => NONE)

fun classify_with meter (context : context) =
  let
    val relation = #relation context
    val (domain, _) = Type.dom_rng (type_of relation)
    val positive = positive_literal relation domain
    val not_weak = negated_rule_with meter order_not_weak (#axioms context)
    val not_strict = negated_rule_with meter order_not_strict (#axioms context)
    fun classify theorem =
      let
        val statement = concl theorem
        fun proved literal = SOME {literal = literal, theorem = theorem}
        fun reverse_order derive literal =
          case derive () of
              SOME rule =>
                (application meter;
                 SOME {literal = literal, theorem = MATCH_MP rule theorem})
            | NONE => NONE
      in
        case positive statement of
            SOME literal => proved literal
          | NONE =>
              (case Option.mapPartial positive (negated_body statement) of
                   SOME (Weak (x, y)) =>
                     reverse_order not_weak (Strict (y, x))
                 | SOME (Strict (x, y)) =>
                     reverse_order not_strict (Weak (y, x))
                 | SOME (Equal pair) => proved (Distinct pair)
                 | _ => NONE)
      end
  in
    classify
  end

fun literal_of_term (context : context) tm =
  let
    val relation = #relation context
    val (domain, _) = Type.dom_rng (type_of relation)
  in
    case positive_literal relation domain tm of
        SOME literal => SOME literal
      | NONE =>
          Option.map Distinct
            (Option.mapPartial (equality_of domain)
              (Option.mapPartial dest_pair (negated_body tm)))
  end

fun is_literal context tm =
  let
    val tm =
      rhs (concl (#reduction (context : context) tm))
      handle Conv.UNCHANGED => tm
    fun positive t = Option.isSome (literal_of_term context t)
  in
    positive tm orelse
    (case Lib.total dest_neg tm of
         SOME body => positive body
       | NONE => false)
  end

fun reduce (context : context) tm = Conv.QCONV (#reduction context) tm

(* An unchanged fact already has the theorem the reader needs. *)
fun normalise (context : context) = Conv.CONV_RULE (#reduction context)

fun facts_of meter context =
  let
    val classify = classify_with meter context
  in
    fn theorem =>
      (normalization meter;
       List.mapPartial
         (fn atom => (candidate meter; classify atom))
         (conjuncts_with meter (normalise context theorem)))
  end

fun facts_of_all meter context theorems =
  List.concat (List.map (facts_of meter context) theorems)

end
