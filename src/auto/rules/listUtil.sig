(* List helpers of the automation layer.  A Measured traversal calls its
   checkpoint once per element visited, before the element's own work;
   the checkpoint may raise to interrupt. *)
signature listUtil =
sig
  (* The checkpoint of an unmeasured traversal. *)
  val no_checkpoint : unit -> unit

  val mapMeasured : (unit -> unit) -> ('a -> 'b) -> 'a list -> 'b list
  val appMeasured : (unit -> unit) -> ('a -> unit) -> 'a list -> unit
  val existsMeasured :
    (unit -> unit) -> ('a -> bool) -> 'a list -> bool
  val findMeasured :
    (unit -> unit) -> ('a -> bool) -> 'a list -> 'a option
  val appendMeasured :
    (unit -> unit) -> 'a list -> 'a list -> 'a list
  (* Tests the elements last to first. *)
  val partitionMeasured :
    (unit -> unit) -> ('a -> bool) -> 'a list -> 'a list * 'a list
  val mapPartialMeasured :
    (unit -> unit) -> ('a -> 'b option) -> 'a list -> 'b list
  (* An element's result is appended, one checkpoint per appended item,
     after the remaining elements are mapped. *)
  val concatMapMeasured :
    (unit -> unit) -> ('a -> 'b list) -> 'a list -> 'b list

  (* distinct_by compare key items keeps one item per key, in order of
     first occurrence.  Keys are kept in a set ordered by compare, so a
     long list costs no quadratic number of comparisons. *)
  val distinct_by : ('b * 'b -> order) -> ('a -> 'b) -> 'a list -> 'a list
end
