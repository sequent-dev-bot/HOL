(* A trace flag, its level in a context, and the messages shown at it. *)
signature traceUtil =
sig
  type tracer
  type level

  (* create {group, max, emit} registers the trace {group, name =
     "trace"} with initial value 0 and maximum max.  emit writes one
     message. *)
  val create :
    {group : string, max : int, emit : string -> unit} -> tracer
  val flag : tracer -> HOLFlags.flag

  (* The tracer's level in the given context.  It is read once; pass
     the level on, rather than the context. *)
  val level_of : tracer -> Context.t -> level

  (* The level at which nothing is shown. *)
  val silent : level

  (* enabled level k: a message at threshold k would be shown. *)
  val enabled : level -> int -> bool

  (* trace level k message emits message () when enabled level k, and
     never forces message otherwise. *)
  val trace : level -> int -> (unit -> string) -> unit
end
