signature clasetNet =
sig
  type term = Term.term
  type 'a net

  val empty : 'a net
  val insert : {pat : term, patvars : term HOLset.set} * 'a ->
               'a net -> 'a net
  (* Filter only values entered under the given pattern's labels. *)
  val filter_at : {pat : term, patvars : term HOLset.set} ->
                  ('a -> bool) -> 'a net -> 'a net
  val match : term -> 'a net -> 'a list
  val unify : {q : term, qvars : term HOLset.set} -> 'a net -> 'a list
  (* The callback may raise to interrupt a measured traversal; the net is
     persistent, so every checkpoint is safe.  The result has the same
     order as an ordinary query. *)
  val unifyMeasured :
    (unit -> unit) ->
    {q : term, qvars : term HOLset.set} -> 'a net -> 'a list
  (* Treat every free variable of the query as schematic. *)
  val unifyFreesMeasured : (unit -> unit) -> term -> 'a net -> 'a list
  val vfilter : ('a -> bool) -> 'a net -> 'a net
  val listItems : 'a net -> 'a list
end
