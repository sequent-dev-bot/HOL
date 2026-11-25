signature forceScheduler =
sig
  datatype 'a outcome = Proved of 'a | Yielded | Exhausted

  (* Visit each live engine once per round, in declaration order.  A
     yielded engine keeps its own cursor and returns in the next round;
     an exhausted engine is removed.  Exceptions, including budget limits
     and interrupts, propagate without being reclassified. *)
  val run : (unit -> 'a outcome) list -> 'a option
end
