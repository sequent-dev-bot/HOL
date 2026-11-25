(*
  Cumulative search-work meter shared by the automation engines.

  Each engine already keeps counters for its own last search, but those
  cannot answer "how much work did this proof do?".  An iteratively
  deepened or staged run overwrites them, and a run whose first stage
  succeeds leaves the previous run's value in place.  This meter
  accumulates instead, so a caller can bracket a whole tactic invocation.
*)
signature searchWork =
sig
  type work = {
    expansions : int,
    tableau_depth : int,
    tableau_branches : int,
    inferences : int,
    rule_applications : int
  }

  val zero : work
  (* Expansions, branches, inferences and rule applications summed;
     the deepest tableau bound is a level, not an amount, so it is not
     part of the sum. *)
  val total : work -> int
  val render : work -> string

  val reset : unit -> unit
  val read : unit -> work
  (* Reports the work of this run alone; work accumulated by an enclosing
     [measure] is preserved. *)
  val measure : (unit -> 'a) -> 'a * work

  val note_expansion : unit -> unit
  val note_tableau :
    {depth : int, branches : int, inferences : int} -> unit
  val note_rule_applications : int -> unit
end
