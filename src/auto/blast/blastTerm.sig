signature blastTerm =
sig
  (* This destructive term representation is private to the blast
     implementation.  In particular, it must not be put in clasetMeta's
     persistent stores or shared with the classical search engine. *)
  datatype term =
      Const of KernelSig.kernelname * term list
    | Skolem of string * term option ref list
    | Fvar of string
    | Goal
    | False
    | Var of term option ref
    | Bound of int
    | Abs of string * term
    | $ of term * term

  type var = term option ref
  type state

  val mkGoal : term -> term
  val isGoal : term -> bool

  val newState : unit -> state
  val trailSize : state -> int
  (* Newest assignment first; used by blast's pruning test. *)
  val trailVars : state -> var list
  val clearTo : state -> int -> unit
  (* As clearTo, calling the hook once after each restored assignment.  This
     is used only by measured exception cleanup; ordinary state and rollback
     carry no instrumentation. *)
  val clearToWith : (unit -> unit) -> state -> int -> unit
  (* Normal measured rollback polls before each trail item.  If a poll raises,
     the remaining rollback is completed without callbacks before the exact
     exception is propagated. *)
  val clearToMeasured :
    (unit -> unit) -> state -> int -> unit
  (* Internal ownership-aware variant.  The cleanup callback receives the
     exception, state and target mark after a checkpoint raises.  It may
     decline restoration only when every term reachable from the state is
     owned by the abandoning caller. *)
  val clearToMeasuredWith :
    (exn -> state -> int -> unit) ->
    (unit -> unit) -> state -> int -> unit

  val rand : term -> term
  val list_comb : term * term list -> term
  val strip_comb : term -> term * term list
  val head_of : term -> term

  val aconv : term * term -> bool
  val aconvMeasured : (unit -> unit) -> term * term -> bool
  val mem_var : var * var list -> bool
  val add_term_vars : term * var list -> var list
  val add_terms_vars : term list * var list -> var list
  val vars_in_vars : var list -> var list
  val add_term_vars_measured :
    (unit -> unit) -> term * var list -> var list
  val add_terms_vars_measured :
    (unit -> unit) -> term list * var list -> var list
  val vars_in_vars_measured : (unit -> unit) -> var list -> var list

  val incr_boundvars : int -> term -> term
  val loose_bnos : term -> int list
  val subst_bound : term * term -> term
  val incr_boundvars_measured : (unit -> unit) -> int -> term -> term
  val loose_bnos_measured : (unit -> unit) -> term -> int list
  val subst_bound_measured :
    (unit -> unit) -> term * term -> term

  val norm : term -> term
  val normMeasured : (unit -> unit) -> term -> term
  val wkNorm : term -> term
  val varOccur : var -> term -> bool
  val varOccurMeasured : (unit -> unit) -> var -> term -> bool

  (* [vars] are variables local to the freshly converted rule.  Their
     assignments are deliberately off-trail; branch-variable assignments
     are trailed and are rolled back if unification fails. *)
  val unify : state -> var list * term * term -> bool
  val unifyMeasuredWith :
    (exn -> state -> int -> unit) ->
    (unit -> unit) -> state -> var list * term * term -> bool
end
