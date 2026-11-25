structure traceUtil :> traceUtil =
struct

type tracer = {flag : HOLFlags.flag, emit : string -> unit}
type level = {level : int, emit : string -> unit}

fun create {group, max, emit} =
  let
    val {flag, ...} =
      HOLFlags.create_trace ({group = group, name = "trace"},
                             {initial = 0, max = max})
  in
    {flag = flag, emit = emit}
  end

fun flag ({flag, ...} : tracer) = flag

fun level_of ({flag, emit} : tracer) ctxt : level =
  {level = HOLFlags.get_flagC ctxt flag, emit = emit}

(* Below every threshold, so even a threshold-0 message is not built. *)
val silent : level = {level = ~1, emit = fn _ => ()}

fun enabled ({level, ...} : level) k = k <= level

fun trace (lvl as {emit, ...} : level) k message =
  if enabled lvl k then emit (message ()) else ()

end
