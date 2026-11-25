structure clasetMeta :> clasetMeta =
struct

open HolKernel

type meta = term
type tymeta = hol_type

val meta_prefix = "%%claset_meta%%"
val tymeta_prefix = "'claset_tymeta_"

fun marked prefix name = String.isPrefix prefix name

fun is_meta tm =
  case dest_term tm of
    VAR (name, _) => marked meta_prefix name
  | _ => false

fun is_tymeta ty =
  is_vartype ty andalso marked tymeta_prefix (dest_vartype ty)

fun meta_name tm =
  case dest_term tm of
    VAR (name, _) => if marked meta_prefix name then SOME name else NONE
  | _ => NONE

fun tymeta_name ty =
  if is_tymeta ty then SOME (dest_vartype ty) else NONE

fun string_compare (left : string, right) = String.compare (left, right)

(* Metavariables come first and are ordered by name, so the two spellings a
   type binding gives one metavariable compare equal; everything else keeps
   [Term.compare].  Discriminating on being a metavariable before comparing
   keeps the whole thing a total order on terms. *)
fun meta_compare (left, right) =
  case (meta_name left, meta_name right) of
      (SOME left_name, SOME right_name) =>
        String.compare (left_name, right_name)
    | (SOME _, NONE) => LESS
    | (NONE, SOME _) => GREATER
    | (NONE, NONE) => Term.compare (left, right)

(* The equality [meta_compare] induces, for the list-shaped metavariable
   collections that do not warrant a set: two spellings of one metavariable
   are the same metavariable, and a non-metavariable is never equal to
   anything. *)
fun same_meta left right =
  case (meta_name left, meta_name right) of
      (SOME left_name, SOME right_name) => left_name = right_name
    | _ => false

fun same_tymeta left right =
  case (tymeta_name left, tymeta_name right) of
      (SOME left_name, SOME right_name) => left_name = right_name
    | _ => false

(* [occurring] is every variable that stands in a binding's residue.
   Expansion only substitutes one residue into another, so no variable
   outside it can appear in any normalized residue, and registering an
   eigenvariable the set does not hold cannot invalidate a binding.  The
   check it replaces normalizes every binding in the store at every
   eigenvariable introduction, which is quadratic in the bindings a
   branch has made. *)
type store =
  {allows : (string, term list) Redblackmap.dict,
   eigens : (string, term list) Redblackmap.dict,
   metas : (string, meta) Redblackmap.dict,
   tm_bindings : (string, term) Redblackmap.dict,
   tymetas : (string, tymeta) Redblackmap.dict,
   ty_bindings :
     (string, tymeta * hol_type) Redblackmap.dict,
   occurring : string Redblackset.set}

val empty =
  {allows = Redblackmap.mkDict string_compare,
   eigens = Redblackmap.mkDict string_compare,
   metas = Redblackmap.mkDict string_compare,
   tm_bindings = Redblackmap.mkDict string_compare,
   tymetas = Redblackmap.mkDict string_compare,
   ty_bindings = Redblackmap.mkDict string_compare,
   occurring = Redblackset.empty string_compare}

fun merge_table table equal (left, right) =
  let
    fun merge (key, value1, value2) =
      if equal value1 value2 then value1
      else
        raise mk_HOL_ERR "clasetMeta" "absorb"
          ("conflicting " ^ table ^ " entry for key " ^ key)
  in
    Redblackmap.unionWithi merge (left, right)
  end

fun absorb {base, extensions} =
  let
    fun merge (extension : store, store : store) =
      {allows =
         merge_table "allow-set" (Lib.list_eq aconv)
           (#allows store, #allows extension),
       eigens =
         merge_table "eigenvariable" (Lib.list_eq aconv)
           (#eigens store, #eigens extension),
       metas =
         merge_table "term metavariable" aconv
           (#metas store, #metas extension),
       tm_bindings =
         merge_table "term binding" aconv
           (#tm_bindings store, #tm_bindings extension),
       tymetas =
         merge_table "type metavariable" (Lib.curry op =)
           (#tymetas store, #tymetas extension),
       ty_bindings =
         merge_table "type binding" (Lib.curry op =)
           (#ty_bindings store, #ty_bindings extension),
       occurring =
         Redblackset.union (#occurring store, #occurring extension)}
  in
    List.foldl merge base extensions
  end

fun fresh_meta ty =
  let
    val generated = genvar ty
    val (name, _) = dest_var generated
  in
    mk_var (meta_prefix ^ name, ty)
  end

fun fresh_tymeta () =
  let
    val generated = dest_vartype (gen_tyvar ())
    val suffix =
      String.implode (List.filter Char.isDigit (String.explode generated))
  in
    mk_vartype (tymeta_prefix ^ suffix)
  end

fun new_meta {allow, ty} store =
  let
    fun add_eigen (eigen, eigens) =
      let
        val name = #1 (dest_var eigen)
        val bucket =
          case Redblackmap.peek (eigens, name) of
              NONE => []
            | SOME entries => entries
      in
        if boolSyntax.tmem eigen bucket then eigens
        else Redblackmap.insert (eigens, name, eigen :: bucket)
      end

    val m = fresh_meta ty
    val name = valOf (meta_name m)
    val allows = Redblackmap.insert (#allows store, name, allow)
    val eigens = List.foldl add_eigen (#eigens store) allow
    val metas = Redblackmap.insert (#metas store, name, m)
  in
    (m,
     {allows = allows,
      eigens = eigens,
      metas = metas,
      tm_bindings = #tm_bindings store,
      tymetas = #tymetas store,
      ty_bindings = #ty_bindings store,
      occurring = #occurring store})
  end

fun new_tymeta store =
  let
    val ty = fresh_tymeta ()
    val name = valOf (tymeta_name ty)
    val tymetas = Redblackmap.insert (#tymetas store, name, ty)
  in
    (ty,
     {allows = #allows store,
      eigens = #eigens store,
      metas = #metas store,
      tm_bindings = #tm_bindings store,
      tymetas = tymetas,
      ty_bindings = #ty_bindings store,
      occurring = #occurring store})
  end

(* A normalisation that changes nothing returns what it was given.
   Rebuilding regardless costs a fresh node for every subterm of every
   term the engine looks at, and [mk_thy_type] and [mk_comb] each re-check
   what the original already satisfied.  The engine normalises the same
   terms repeatedly -- a unification walks a pair node by node, a goal is
   rendered once per rule query -- so the terms that changed are the rare
   ones. *)
fun unchanged_list (originals, results) =
  ListPair.allEq Portable.pointer_eq (originals, results)

fun norm_ty store ty =
  let
    fun recurse current =
      case tymeta_name current of
        SOME name =>
          (case Redblackmap.peek (#ty_bindings store, name) of
             SOME (_, residue) => recurse residue
           | NONE => current)
      | NONE =>
          if is_vartype current then current
          else
            let
              val {Thy, Tyop, Args} = dest_thy_type current
              val args = map recurse Args
            in
              if unchanged_list (Args, args) then current
              else mk_thy_type {Thy = Thy, Tyop = Tyop, Args = args}
            end
  in
    if Redblackmap.numItems (#ty_bindings store) = 0 then ty
    else recurse ty
  end

val norm_type = norm_ty

fun owned_meta store tm =
  case meta_name tm of
    NONE => false
  | SOME name =>
      (case Redblackmap.peek (#metas store, name) of
         NONE => false
       | SOME registered =>
           norm_ty store (type_of tm) =
           norm_ty store (type_of registered))

fun owned_tymeta store ty =
  case tymeta_name ty of
    NONE => false
  | SOME name => Redblackmap.inDomain (#tymetas store, name)

fun type_substitution store =
  map
    (fn (_, (redex, residue)) =>
      {redex = redex, residue = norm_ty store residue})
    (Redblackmap.listItems (#ty_bindings store))

(* A replay store retains fresh variables from earlier proof steps.  Most
   terms mention only the few type variables created by their own step, so
   rebuilding a substitution for the complete historical store on every
   walk makes long proofs quadratic in dead bindings.  Instantiate exactly
   the type variables reachable from the term instead. *)
fun inst_types store tm =
  let
    fun binding ty =
      case tymeta_name ty of
          NONE => NONE
        | SOME name =>
            (case Redblackmap.peek (#ty_bindings store, name) of
                 NONE => NONE
               | SOME (redex, residue) =>
                   SOME {redex = redex, residue = norm_ty store residue})
  in
    if Redblackmap.numItems (#ty_bindings store) = 0 then tm
    else Term.inst (List.mapPartial binding (type_vars_in_term tm)) tm
  end

fun walk_with store instantiate tm =
  let
    fun recurse current =
      let
        val current' = instantiate current
      in
        case meta_name current' of
          SOME name =>
            if owned_meta store current' then
              (case Redblackmap.peek (#tm_bindings store, name) of
                 SOME residue => recurse residue
               | NONE => current')
            else current'
        | NONE => current'
      end
  in
    recurse tm
  end

fun walk store tm = walk_with store (inst_types store) tm

type normalization_operations =
  {inspect : term -> lambda,
   combination : term * term -> term,
   abstraction : term * term -> term,
   beta : term -> term,
   eta : term -> term,
   abstraction_operator : term -> bool}

fun beta_eta_normalize
      ({inspect, combination, abstraction, beta, eta,
        abstraction_operator} : normalization_operations) tm =
  let
    fun recurse current =
      case inspect current of
          COMB (rator, rand) =>
            let
              val rator' = recurse rator
              val rand' = recurse rand
              val combined =
                if Portable.pointer_eq (rator', rator) andalso
                   Portable.pointer_eq (rand', rand)
                then current
                else combination (rator', rand')
            in
              if abstraction_operator rator' then recurse (beta combined)
              else combined
            end
        | LAMB (bvar, body) =>
            let
              val body' = recurse body
            in
              eta
                (if Portable.pointer_eq (body', body) then current
                 else abstraction (bvar, body'))
            end
        | _ => current
  in
    recurse tm
  end

val ordinary_normalization : normalization_operations =
  {inspect = dest_term,
   combination = mk_comb,
   abstraction = mk_abs,
   beta = beta_conv,
   eta = fn abs => Term.eta_conv abs handle HOL_ERR _ => abs,
   abstraction_operator = is_abs}

type expansion_operations =
  {instantiate : term -> term,
   binding : term -> (string * term * term) option,
   variables : term -> term list,
   new_memo :
     unit -> (string, term * term) Redblackmap.dict ref,
   memo_lookup :
     (string, term * term) Redblackmap.dict ref * string ->
     (term * term) option,
   cycle_member : string * string list -> bool,
   traverse_dependencies :
     (term -> (term * term) option) -> term list -> (term * term) list,
   make_substitution : (term * term) list -> (term, term) subst,
   memo_update :
     (string, term * term) Redblackmap.dict ref * string * (term * term) ->
     unit,
   substitute : (term, term) subst -> term -> term,
   normalize : term -> term}

(* Expand a binding only through bound metavariables that occur free in its
   residue.  Substituting a dependency into the whole residue is essential:
   [Term.subst] alpha-variants enclosing binders when necessary, whereas a
   recursive walk that replaces a node below a binder can capture the
   dependency's free variables. *)
fun dependency_expander function_name
      ({instantiate, binding, variables, new_memo, memo_lookup,
        cycle_member, traverse_dependencies, make_substitution,
        memo_update, substitute, normalize} :
        expansion_operations) =
  let
    val memo = new_memo ()

    fun cycle name =
      raise mk_HOL_ERR "clasetMeta" function_name
        ("cyclic persistent term binding for " ^ name)

    fun expand active variable =
      case binding variable of
          NONE => NONE
        | SOME (name, redex, raw_residue) =>
            (case memo_lookup (memo, name) of
                 SOME result => SOME result
               | NONE =>
                   if cycle_member (name, active)
                   then cycle name
                   else
                     let
                       val residue = instantiate raw_residue
                       val dependencies =
                         traverse_dependencies (expand (name :: active))
                           (variables residue)
                       val expanded =
                         normalize (substitute
                           (make_substitution dependencies)
                           residue)
                       val result = (instantiate redex, expanded)
                       val _ = memo_update (memo, name, result)
                     in
                       SOME result
                     end)

    fun substitution tm =
      let
        val instantiated = instantiate tm
        val expanded =
          traverse_dependencies (expand []) (variables instantiated)
      in
        (instantiated, make_substitution expanded)
      end
  in
    {expand = expand, substitution = substitution}
  end

fun ordinary_binding store variable =
  case meta_name variable of
      NONE => NONE
    | SOME name =>
        if not (owned_meta store variable) then NONE
        else
          case Redblackmap.peek (#tm_bindings store, name) of
              NONE => NONE
            | SOME residue =>
                (case Redblackmap.peek (#metas store, name) of
                     NONE =>
                       raise mk_HOL_ERR "clasetMeta"
                         "ordinary_binding"
                         "a term binding has no registered metavariable"
                   | SOME redex => SOME (name, redex, residue))

fun ordinary_expansion normalize store =
  {instantiate = inst_types store,
   binding = ordinary_binding store,
   variables = free_vars,
   new_memo = fn () => ref (Redblackmap.mkDict string_compare),
   memo_lookup = fn (memo, name) => Redblackmap.peek (!memo, name),
   cycle_member =
     fn (name, active) =>
       List.exists (fn active_name => active_name = name) active,
   traverse_dependencies = List.mapPartial,
   make_substitution =
     map
       (fn (redex, residue) =>
         {redex = redex, residue = residue}),
   memo_update =
     fn (memo, name, result) =>
       memo := Redblackmap.insert (!memo, name, result),
   substitute = Term.subst,
   normalize = normalize}

fun ordinary_expander function_name normalize store =
  dependency_expander function_name (ordinary_expansion normalize store)

fun instantiate_with function_name store tm =
  if Redblackmap.numItems (#tm_bindings store) = 0 then inst_types store tm
  else
    let
      val {substitution, ...} =
        ordinary_expander function_name Lib.I store
      val (instantiated, expanded) = substitution tm
    in
      Term.subst expanded instantiated
    end

val instantiate = instantiate_with "instantiate"

fun norm store tm =
  beta_eta_normalize ordinary_normalization (instantiate_with "norm" store tm)

fun insert_meta store (m, metas) =
  case meta_name m of
    SOME name =>
      if owned_meta store m then Redblackmap.insert (metas, name, m)
      else metas
  | NONE => metas

fun collect_metas store tm =
  Redblackmap.listItems' (List.foldl (insert_meta store)
    (Redblackmap.mkDict string_compare) (free_vars tm))

fun has_term_metas (store : store) =
  Redblackmap.numItems (#metas store) <> 0

fun metas_of_normalized store tm =
  if has_term_metas store then collect_metas store tm else []

fun metas_of store tm =
  if has_term_metas store then collect_metas store (norm store tm) else []

fun same_var left right = aconv left right

fun is_eigen store variable =
  if not (is_var variable) then false
  else
    case Redblackmap.peek (#eigens store, #1 (dest_var variable)) of
        NONE => false
      | SOME entries =>
          let val normalized = inst_types store variable
          in
            List.exists
              (same_var normalized o inst_types store) entries
          end

fun eigen_allowed store allow variable =
  not (is_eigen store variable) orelse
  let val normalized = inst_types store variable
  in List.exists (same_var normalized o inst_types store) allow end

fun binding_respects_allow store (name, residue) =
  let
    val allow = valOf (Redblackmap.peek (#allows store, name))
  in
    List.all (eigen_allowed store allow)
      (free_vars (norm store residue))
  end

fun register_eigen eigen store =
  if not (is_var eigen) orelse is_meta eigen
  then NONE
  else
    let
      val name = #1 (dest_var eigen)
      val bucket =
        case Redblackmap.peek (#eigens store, name) of
            NONE => []
          | SOME entries => entries
    in
      if boolSyntax.tmem eigen bucket then NONE
      else
        let
          val candidate =
            {allows = #allows store,
             eigens =
               Redblackmap.insert (#eigens store, name, eigen :: bucket),
             metas = #metas store,
             tm_bindings = #tm_bindings store,
             tymetas = #tymetas store,
             ty_bindings = #ty_bindings store,
             occurring = #occurring store}
          (* No residue can normalize to a term mentioning a variable no
             residue holds, so a name outside [occurring] leaves every
             binding's allow-set exactly as it was. *)
          val permitted =
            not (Redblackset.member (#occurring candidate, name)) orelse
            List.all (binding_respects_allow candidate)
              (Redblackmap.listItems (#tm_bindings candidate))
        in
          if permitted then SOME candidate else NONE
        end
    end

fun bind (m, tm) store =
  case meta_name m of
    NONE => NONE
  | SOME name =>
      if not (owned_meta store m) orelse
         Redblackmap.inDomain (#tm_bindings store, name)
      then NONE
      else
        let
          val residue = norm store tm
          val variables = free_vars residue
          fun valid_variable variable =
            case meta_name variable of
                NONE => true
              | SOME other => other <> name andalso owned_meta store variable
          val same_type =
            norm_ty store (type_of m) = norm_ty store (type_of residue)
        in
          if not (List.all valid_variable variables) orelse
             not same_type orelse
             not (List.all
               (fn ty => not (is_tymeta ty) orelse owned_tymeta store ty)
               (type_vars_in_term residue))
          then NONE
          else
            let
              val candidate =
                {allows = #allows store,
                 eigens = #eigens store,
                 metas = #metas store,
                 tm_bindings =
                   Redblackmap.insert
                     (#tm_bindings store, name, residue),
                 tymetas = #tymetas store,
                 ty_bindings = #ty_bindings store,
                 occurring =
                   List.foldl
                     (fn (variable, known) =>
                       Redblackset.add (known, #1 (dest_var variable)))
                     (#occurring store) variables}
              (* Adding a binding whose normalized residue contains no
                 eigenvariable cannot invalidate the eigen scopes of any
                 existing binding.  A later binding which does introduce an
                 eigenvariable still performs the complete transitive check,
                 so this fast path preserves the store invariant while
                 avoiding a quadratic rescan for rigid propositional
                 structure. *)
              (* The occurs check excludes the new binding's redex
                 from this already normalized residue. *)
              val introduces_eigen =
                List.exists (is_eigen store) variables
              val permitted =
                not introduces_eigen orelse
                List.all (binding_respects_allow candidate)
                  (Redblackmap.listItems (#tm_bindings candidate))
            in
              if permitted then SOME candidate else NONE
            end
        end

fun bind_ty (tymeta, ty) store =
  case tymeta_name tymeta of
    NONE => NONE
  | SOME name =>
      if not (owned_tymeta store tymeta) orelse
         Redblackmap.inDomain (#ty_bindings store, name)
      then NONE
      else
        let
          val residue = norm_ty store ty
          val occurs = List.exists
            (fn variable => tymeta_name variable = SOME name)
            (type_vars residue)
          val owned = List.all
            (fn variable =>
              not (is_tymeta variable) orelse
              owned_tymeta store variable)
            (type_vars residue)
        in
          if occurs orelse not owned then NONE
          else
            SOME
              {allows = #allows store,
               eigens = #eigens store,
               metas = #metas store,
               tm_bindings = #tm_bindings store,
               tymetas = #tymetas store,
               ty_bindings =
                 Redblackmap.insert
                   (#ty_bindings store, name, (tymeta, residue)),
               occurring = #occurring store}
        end

fun ground_types store =
  let
    fun ground_one ((name, tymeta), current) =
      if Redblackmap.inDomain (#ty_bindings current, name) then current
      else valOf (bind_ty (tymeta, Type.bool) current)
  in
    List.foldl ground_one store (Redblackmap.listItems (#tymetas store))
  end

fun ground_terms store =
  let
    fun ground_one ((name, m), current) =
      if Redblackmap.inDomain (#tm_bindings current, name) then current
      else
        let
          val ty = norm_ty current (type_of m)
        in
          valOf (bind (m, boolSyntax.mk_arb ty) current)
        end
  in
    List.foldl ground_one store (Redblackmap.listItems (#metas store))
  end

fun ground store = ground_terms (ground_types store)

fun term_residue (store : store) meta =
  Option.mapPartial (fn name => Redblackmap.peek (#tm_bindings store, name))
    (meta_name meta)

fun type_residue (store : store) meta =
  Option.map (#2 : tymeta * hol_type -> hol_type)
    (Option.mapPartial (fn name => Redblackmap.peek (#ty_bindings store, name))
      (tymeta_name meta))

fun bindings store =
  let
    fun term_binding (name, residue) =
      case Redblackmap.peek (#metas store, name) of
          SOME redex => SOME (redex, residue)
        | NONE => NONE
    fun type_binding (_, binding) = binding
  in
    {terms =
       List.mapPartial term_binding
         (Redblackmap.listItems (#tm_bindings store)),
     types =
       map type_binding
         (Redblackmap.listItems (#ty_bindings store))}
  end

fun new_bindings old new =
  let
    fun add_term (name, _, terms) =
      if Redblackmap.inDomain (#tm_bindings old, name) then terms
      else
        case Redblackmap.peek (#metas new, name) of
            NONE => terms
          | SOME meta => meta :: terms
    fun add_type (name, (tymeta, _), types) =
      if Redblackmap.inDomain (#ty_bindings old, name) then types
      else tymeta :: types
    fun added select add =
      if Portable.pointer_eq (select old, select new) then []
      else Redblackmap.foldr add [] (select new)
  in
    {terms = added #tm_bindings add_term, types = added #ty_bindings add_type}
  end

fun collapse store =
  let
    val ty_subst = type_substitution store
    val {expand, ...} =
      ordinary_expander "collapse"
        (beta_eta_normalize ordinary_normalization) store

    fun term_binding (name, _) =
      case Redblackmap.peek (#metas store, name) of
        SOME redex =>
          (case expand [] redex of
               SOME (expanded_redex, expanded_residue) =>
                 SOME
                   {redex = expanded_redex,
                    residue = expanded_residue}
             | NONE =>
                 raise mk_HOL_ERR "clasetMeta" "collapse"
                   "a listed term binding cannot be expanded")
      | NONE =>
          raise mk_HOL_ERR "clasetMeta" "collapse"
            "a term binding has no registered metavariable"

    val tm_subst = List.mapPartial term_binding
      (Redblackmap.listItems (#tm_bindings store))
  in
    (ty_subst, tm_subst)
  end

end
