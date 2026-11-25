(* Operational work admitted by one automation invocation.  A budget is
   passed explicitly to nested consumers; it is not a diagnostic meter. *)
signature searchBudget =
sig
  datatype kind = Candidate | Application | Normalization

  type limits =
    {candidates : int option,
     applications : int option,
     normalization : int option}

  type usage =
    {candidates : int,
     applications : int,
     normalization : int}

  type budget
  exception LimitReached of kind * usage

  val create : limits -> budget
  val unbounded : unit -> budget
  (* A child has its own turn limits and charges the same work to every
     ancestor. A local limit can be extended without resetting usage. *)
  val child : budget -> limits -> budget
  val usage : budget -> usage
  val available : budget -> kind -> bool
  (* Charge before work starts.  A zero limit rejects its first unit. *)
  val charge : budget -> kind -> unit
  (* Add an explicit allocation to a finite limit.  An unbounded
     dimension remains unbounded.  This preserves usage and lets a
     suspended invocation resume with its existing cursors. *)
  val extend : budget -> kind -> int -> unit

  (* One charge callback per kind; [free_charger] charges nothing. *)
  type charger =
    {candidate : unit -> unit,
     application : unit -> unit,
     normalization : unit -> unit}
  val free_charger : charger
  val charger : budget -> charger
end
