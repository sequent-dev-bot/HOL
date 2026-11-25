structure clasetFacts :> clasetFacts =
struct

open Abbrev HolKernel

type fact =
  {id : int,
   original : thm,
   hypotheses : term list,
   fixed_terms : term list Portable.HOLSusp.susp,
   fixed_term_set : term HOLset.set Portable.HOLSusp.susp,
   fixed_types : hol_type list,
   loose_terms : term list,
   loose_types : hol_type list,
   charge : searchBudget.kind -> unit,
   schematic : thm option ref}

type environment = fact list

type view =
  {source_id : int, source : thm, theorem : thm,
   support : term list}

fun ordered_fixed_terms [] shared = shared
  | ordered_fixed_terms hypotheses shared =
  let val supported = Term.free_varsl hypotheses
  in
    if null supported then shared
    else if null shared then supported
    else
      let
        val shared_set = HOLset.fromList Term.compare shared
        (* The supported variables are distinct. Prepend those absent
           from shared in the same order as Lib.op_union. *)
        fun add (variable, terms) =
          if HOLset.member (shared_set, variable) then terms
          else variable :: terms
      in
        List.foldl add shared supported
      end
  end

fun create_with_charge _ _ [] = []
  | create_with_charge charge (assumptions, target) theorems =
  let
    val goal_variables = Term.FVL (target :: assumptions) Term.empty_tmset

    fun prepare (id, original) =
      let
        val _ = charge searchBudget.Candidate
        val hypotheses = Thm.hyp original
        val genuine = Term.free_vars (Thm.concl original)
        val (shared, unshared) =
          List.partition
            (fn variable => HOLset.member (goal_variables, variable))
            genuine
        (* Matching uses the set. Only the list accessor needs the
           historical variable order. *)
        val fixed_terms = Portable.HOLSusp.delay
          (fn () => ordered_fixed_terms hypotheses shared)
        val fixed_term_set = Portable.HOLSusp.delay
          (fn () => Term.FVL hypotheses (HOLset.fromList Term.compare shared))
        val loose_terms =
          if null hypotheses orelse null unshared then unshared
          else
            let val fixed = Portable.HOLSusp.force fixed_term_set
            in List.filter (fn tm => not (HOLset.member (fixed, tm))) unshared
            end
        val support_types =
          List.foldl
            (fn (term, types) =>
              Lib.union (type_vars_in_term term) types)
            [] hypotheses
        val fixed_types =
          List.foldl
            (fn (variable, types) =>
              Lib.union (Type.type_vars (Term.type_of variable)) types)
            support_types shared
        val loose_types =
          Lib.set_diff
            (type_vars_in_term (Thm.concl original)) fixed_types
      in
        {id = id, original = original, hypotheses = hypotheses,
         fixed_terms = fixed_terms,
         fixed_term_set = fixed_term_set,
         fixed_types = fixed_types,
         loose_terms = loose_terms, loose_types = loose_types,
         charge = charge,
         schematic = ref NONE}
      end
  in
    map prepare (Lib.enumerate 0 theorems)
  end

fun create goal theorems =
  create_with_charge (fn _ => ()) goal theorems

fun facts environment = environment
fun source_id ({id, ...} : fact) = id
fun source ({original, ...} : fact) = original
fun support ({hypotheses, ...} : fact) = hypotheses
fun fixed_terms ({fixed_terms, ...} : fact) =
  Portable.HOLSusp.force fixed_terms
fun fixed_types ({fixed_types, ...} : fact) = fixed_types
fun has_schematic_types ({loose_types, ...} : fact) =
  not (null loose_types)

fun literal_view ({id, original, hypotheses, ...} : fact) =
  {source_id = id, source = original, theorem = original,
   support = hypotheses} : view

fun literal_views environment = map literal_view environment

fun schematic_view
      ({id, original, hypotheses, loose_terms, loose_types,
        charge, schematic, ...} : fact) =
  let
    val theorem =
      case !schematic of
          SOME theorem => theorem
        | NONE =>
            let
              val _ = charge searchBudget.Normalization
              val term_fresh =
                map
                  (fn variable =>
                    {redex = variable,
                     residue = Term.genvar (Term.type_of variable)})
                  loose_terms
              val type_fresh =
                map
                  (fn ty =>
                    {redex = ty, residue = Type.gen_tyvar ()})
                  loose_types
              val theorem =
                Thm.INST_TYPE type_fresh
                  (Thm.INST term_fresh original)
            in
              schematic := SOME theorem; theorem
            end
  in
    {source_id = id, source = original, theorem = theorem,
     support = hypotheses}
  end

fun schematic_views environment =
  map schematic_view environment

fun transport_view conversion
      ({source_id, source, theorem, ...} : view) =
  let
    val derived = Conv.CONV_RULE conversion theorem
  in
    {source_id = source_id, source = source,
     theorem = derived,
     support = Thm.hyp derived} : view
  end

fun match_view (entry : fact) pattern site =
  let
    val {source_id, source, theorem, support} = schematic_view entry
    val substitution =
      Term.match_terml
        (#fixed_types entry)
        (Portable.HOLSusp.force (#fixed_term_set entry))
        pattern site
    val instance = Drule.INST_TY_TERM substitution theorem
  in
    SOME
      {source_id = source_id, source = source,
       theorem = instance, support = support}
  end
  handle HOL_ERR _ => NONE
       | Match => NONE

fun quantified_body term =
  if boolSyntax.is_forall term then #2 (boolSyntax.strip_forall term) else term

fun implication_rule_view entry =
  if boolSyntax.is_imp_only (quantified_body (Thm.concl (source entry))) then
    SOME (schematic_view entry)
  else NONE

fun equational term =
  boolSyntax.is_eq (#2 (boolSyntax.strip_imp_only (quantified_body term)))

datatype conjunct_selection =
    Skip
  | Select
  | Branch of conjunct_selection * conjunct_selection

(* Schematic freshening preserves the shape of the original conclusion.
   Classify once and omit subtrees with no equational leaves. *)
fun select_equational term =
  case total boolSyntax.dest_conj term of
      SOME (left, right) =>
        (case (select_equational left, select_equational right) of
             (Skip, Skip) => Skip
           | children => Branch children)
    | NONE => if equational term then Select else Skip

fun equational_views environment =
  List.concat
    (map
      (fn entry =>
        case select_equational (Thm.concl (source entry)) of
            Skip => []
          | selection =>
              let
                val {source_id, source, support, theorem} =
                  schematic_view entry
                fun collect Skip _ views = views
                  | collect Select piece views =
                      {source_id = source_id, source = source,
                       theorem = piece, support = support} :: views
                  | collect (Branch (left, right)) piece views =
                      descend Thm.CONJUNCT1 left piece
                        (descend Thm.CONJUNCT2 right piece views)
                and descend _ Skip _ views = views
                  | descend project child piece views =
                      collect child (project piece) views
              in
                collect selection theorem []
              end)
      environment)

end
