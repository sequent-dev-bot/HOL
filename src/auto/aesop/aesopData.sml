structure aesopData :> aesopData =
struct

open HolKernel

val ERR = mk_HOL_ERR "aesopData"

fun apply_aesop_simp_delta delta rewrites =
  case delta of
      ThmSetData.ADD (_, theorem) => theorem :: rewrites
    | ThmSetData.REMOVE _ =>
        raise ERR "apply_aesop_simp_delta"
          "aesop_simp is an additive theorem set"

val aesop_simp_data =
  thmTable.register
    {settype = "aesop_simp", initial_value = [],
     apply_delta = apply_aesop_simp_delta,
     apply_to_global = apply_aesop_simp_delta}

fun aesop_simp_rewrites_of ctxt =
  #get_global_value_of aesop_simp_data ctxt

(* Start from the lifted srw_ss, NOT clasimp_ss: aesop leaves splitting
   to search.  The unsafe solver is set per context, in aesop_derived_of
   below. *)
fun aesop_base ss =
  ss
  |> clasimpLib.weaken_cond_congruence
  |> simpLib.set_cond_depth clasimpLib.cond_depth
  |> (fn ss' => simpLib.++ (ss', boolSimps.ETA_ss))
  |> simpLib.set_safe_solvers [clasimpLib.safe_solver]

(* The simpset is a function of srw_ss, the aesop_simp rewrites and the
   [arith] facts.  The srw_ss state keys the stored value through the
   derived-value mechanism, independently of clasimp's derivation, so
   restoring a context that changes srw_ss restores the exact simpset.
   The base is derived from srw_ss without its bottom-up declarations,
   which go on top of it as a layer of their own
   (clasimpLib.layered_srw_derivation), so a declaration does not derive
   it again.  The rewrites, compared by identity (an immutable value a
   context owns), and the facts, compared element-wise by identity, key a
   single-entry memo on that: a window that changes only [arith] or
   [aesop_simp] replaces the entry, and an equal but new simpset is built
   after the restore.  Linarith is aesop's only unsafe solver, and
   set_unsafe_solvers replaces rather than appends: a solver installed in
   the base must not precede aesop's choice during safe normalisation's
   side-condition traversal. *)
val aesop_value_of_srw =
  clasimpLib.layered_srw_derivation
    {base = aesop_base,
     layered = fn derived => fn add =>
       let val base = Susp.delay (fn () => add (Susp.force derived))
       in
         memoUtil.keyed_memo
           (fn (rewrites, facts) => fn (rewrites', facts') =>
              Portable.pointer_eq (rewrites, rewrites') andalso
              Lib.list_eq (Lib.curry Portable.pointer_eq) facts facts')
           (fn (rewrites, facts) =>
              (case rewrites of
                   [] => Susp.force base
                 | _ => simpLib.++ (Susp.force base,
                                       simpLib.rewrites rewrites))
              |> simpLib.set_unsafe_solvers
                   [linarithLib.linarith_solver_with_facts facts])
       end}

val {get = _, get_of = aesop_derived_of} =
  BasicProvers.make_simpset_derived_value
    "aesopData.aesop_ss"
    (fn ss => fn _ => aesop_value_of_srw ss)
    (fn _ => simpLib.empty_ss)

fun aesop_ss_of ctxt =
  aesop_derived_of ctxt
    (aesop_simp_rewrites_of ctxt, linarithData.arith_facts_of ctxt)

fun aesop_ss () = aesop_ss_of (Context.snapshot ())

val tracer =
    traceUtil.create
      {group = "aesop", max = 3,
       emit = fn message => Feedback.HOL_MESG ("Aesop: " ^ message)}

end
