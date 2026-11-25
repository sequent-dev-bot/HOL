(* Traverse's engine over the extended reducer type. *)
structure TraverseExt :> TraverseExt =
struct
open HolKernel Drule Conv Abbrev;

  type context = Traverse.context
  type reducer_config_data =
    {name : string option, initial : context,
     addcontext : context * thm list -> context,
     apply : {solver : term list -> term -> thm,
              conv : term list -> term -> thm, context : context,
              stack : term list, cond_depth : int option,
              term_ord : term * term -> order,
              relation : term * (term -> thm)} -> conv}
  type reducer_context_data =
    {name : string option, initial : context,
     addcontext : context * thm list -> context,
     apply : {solver : term list -> term -> thm,
              conv : term list -> term -> thm, context : context,
              stack : term list, cond_depth : int,
              term_ord : term * term -> order,
              relation : term * (term -> thm)} -> conv}
  datatype reducer = LIFTED of Traverse.reducer
                   | CONTEXT_REDUCER of reducer_context_data
                   | CONFIG_REDUCER of reducer_config_data
  val lift = LIFTED
  datatype reducer_kind = LiftedReducer | ContextReducer | ConfigReducer
  fun reducer_kind (LIFTED _) = LiftedReducer
    | reducer_kind (CONTEXT_REDUCER _) = ContextReducer
    | reducer_kind (CONFIG_REDUCER _) = ConfigReducer
  fun reducer_config_data (CONFIG_REDUCER r) = r
    | reducer_config_data (LIFTED r) =
      let val {name,initial,addcontext,apply} = Traverse.dest_reducer r
      in
        {name=name, initial=initial, addcontext=addcontext,
         apply=fn {solver,conv,context,stack,relation,...} =>
           apply {solver=solver,conv=conv,context=context,stack=stack,
                  relation=relation}}
      end
    | reducer_config_data
        (CONTEXT_REDUCER {name,initial,addcontext,apply}) =
      {name=name, initial=initial, addcontext=addcontext,
       apply=fn {solver,conv,context,stack,relation,cond_depth,term_ord} =>
         apply {solver=solver,conv=conv,context=context,stack=stack,
                relation=relation,term_ord=term_ord,
                cond_depth=case cond_depth of NONE => !Cond_rewr.stack_limit
                                           | SOME n => n}}
  fun reducer_data r =
    let val {name,initial,addcontext,apply} = reducer_config_data r
    in
      {name=name, initial=initial, addcontext=addcontext,
       apply=fn {solver,conv,context,stack,relation,cond_depth,term_ord} =>
         apply {solver=solver,conv=conv,context=context,stack=stack,
                relation=relation,term_ord=term_ord,
                cond_depth=SOME cond_depth}}
    end
  fun addctxt ths (LIFTED r) = LIFTED (Traverse.addctxt ths r)
    | addctxt ths (CONTEXT_REDUCER {name,initial,addcontext,apply}) =
      CONTEXT_REDUCER {name=name,initial=addcontext (initial,ths),
                       addcontext=addcontext,apply=apply}
    | addctxt ths (CONFIG_REDUCER {name,initial,addcontext,apply}) =
      CONFIG_REDUCER {name=name,initial=addcontext (initial,ths),
                      addcontext=addcontext,apply=apply}

type simp_prover_ctxt = Traverse.simp_prover_ctxt
type ssolver = Traverse.ssolver
type subgoaler = Traverse.subgoaler

type traverse_data = {limit : int option,
                      rewriters: reducer list,
                      dprocs: reducer list,
                      travrules: Travrules.travrules,
                      relation: term};

type traverse_config = {subgoaler: subgoaler option,
                        solvers: ssolver list,
                        cond_depth: int option,
                        term_ord: (term * term -> order) option};

type xtraverse_data = traverse_data * traverse_config

val default_config : traverse_config =
  {subgoaler=NONE, solvers=[], cond_depth=NONE, term_ord=NONE};

type child_first_policy = Traverse.child_first_policy
datatype traversal_policy = datatype Traverse.traversal_policy

fun charge_only charge = {charge=charge, keep_abstraction=fn _ => false}

fun keep_abstraction (policy : child_first_policy) tm =
  #keep_abstraction policy tm

val eta_argument = Traverse.eta_argument

fun NORMALIZE_ARGUMENTS (policy : child_first_policy) child tm =
  let
    (* TRY_CONV and eta fallback treat HOL_ERR as conversion failure, not
       as a policy abort. Keep policy failures across those combinators.
       This state belongs to one application, including reentrant calls. *)
    val aborted = ref (NONE : exn option)
    fun protected callback argument =
      case !aborted of
          SOME e => raise e
        | NONE => callback argument
            handle e => (aborted := SOME e; raise e)
    val policy = {charge=protected (#charge policy),
                  keep_abstraction=protected (#keep_abstraction policy)}
    fun check_abort () =
      case !aborted of NONE => () | SOME e => raise e
    fun guarded_child tm = (check_abort (); child tm)
    fun arguments tm =
      (check_abort ();
       if is_comb tm then
         Conv.THENC (RATOR_CONV arguments,
                     RAND_CONV (TRY_CONV guarded_child)) tm
       else if is_abs tm then ABS_CONV (TRY_CONV guarded_child) tm
       else REFL tm)
    fun normalize tm =
      let
        val _ = #charge policy ()
        val eta = QCONV (TRY_CONV (eta_argument policy)) tm
        val result = TRANS eta (QCONV arguments (rand (concl eta)))
        val next = rand (concl result)
      in
        if aconv tm next then result
        else TRANS result (normalize next)
      end
  in
    let val theorem = normalize tm
    in case !aborted of NONE => theorem | SOME e => raise e end
    handle e =>
      (case !aborted of NONE => raise e | SOME original => raise original)
  end

(* ---------------------------------------------------------------------
 * The extended reducers as Traverse sees them
 * ---------------------------------------------------------------------*)

(* Lifted ordinary callbacks receive exactly their original record.
   CONFIG_REDUCER transports NONE unchanged: native candidates read the
   live default themselves.  Older CONTEXT_REDUCER clients need an int. *)
fun ordinary_reducer _ _ (LIFTED r) = r
  | ordinary_reducer cond_depth term_ord
      (CONTEXT_REDUCER {name,initial,addcontext,apply}) =
      Traverse.REDUCER
        {name=name, initial=initial, addcontext=addcontext,
         apply=fn {solver,conv,context,stack,relation} =>
           apply {solver=solver, conv=conv, context=context, stack=stack,
                  cond_depth=(case cond_depth of
                                  NONE => !Cond_rewr.stack_limit
                                | SOME n => n),
                  term_ord=term_ord, relation=relation}}
  | ordinary_reducer cond_depth term_ord
      (CONFIG_REDUCER {name,initial,addcontext,apply}) =
      Traverse.REDUCER
        {name=name, initial=initial, addcontext=addcontext,
         apply=fn {solver,conv,context,stack,relation} =>
           apply {solver=solver, conv=conv, context=context, stack=stack,
                  cond_depth=cond_depth, term_ord=term_ord,
                  relation=relation}}

fun ordinary_data
      ({limit,rewriters,dprocs,travrules,relation} : traverse_data,
       {cond_depth,term_ord,...} : traverse_config) : Traverse.traverse_data =
  let
    val term_ord = Option.getOpt (term_ord, Cond_rewr.ac_term_ord)
    val convert = map (ordinary_reducer cond_depth term_ord)
  in
    {rewriters=convert rewriters, dprocs=convert dprocs, limit=limit,
     travrules=travrules, relation=relation}
  end

(* ---------------------------------------------------------------------
 * TRAVERSE
 *
 * ---------------------------------------------------------------------*)
(* The explicit extended entry points refresh supplied reducer contexts
   for every application.  Legacy TRAVERSE retains its construction-time
   context, including mutable rewrite controls and user callback results. *)
fun GEN_TRAVERSE_WITH_CONTEXT check_abort observer policy root_only
      (xdata as (_, {subgoaler,solvers,...} : traverse_config)) =
  Traverse.TRAVERSE_WITH_CONTEXT
    {policy=policy, subgoaler=subgoaler, solvers=solvers,
     root_only=root_only, check_abort=check_abort, observer=observer}
    (ordinary_data xdata)

fun GEN_TRAVERSE policy root_only xdata thms =
  GEN_TRAVERSE_WITH_CONTEXT NONE NONE policy root_only xdata
    {reducer_context=thms,solver_context=[]}

val XTRAVERSE = GEN_TRAVERSE ParentFirst false
val ROOT_REWRITE = GEN_TRAVERSE ParentFirst true
fun TRAVERSE_WITH_CONTEXT policy =
  GEN_TRAVERSE_WITH_CONTEXT NONE NONE policy false
fun CHILD_FIRST_WITH_ABORT check_abort observer policy =
  GEN_TRAVERSE_WITH_CONTEXT (SOME check_abort) observer (ChildFirst policy)
    false
fun CHILD_FIRST_WITH_OBSERVER observe policy =
  GEN_TRAVERSE_WITH_CONTEXT NONE (SOME observe) (ChildFirst policy) false
val ROOT_REWRITE_WITH_CONTEXT =
  GEN_TRAVERSE_WITH_CONTEXT NONE NONE ParentFirst true

(* Unlike the explicit extended entries, default TRAVERSE collects once
   before returning a reusable conversion and constructs factories eagerly. *)
fun TRAVERSE data = Traverse.TRAVERSE (ordinary_data (data,default_config))

end
