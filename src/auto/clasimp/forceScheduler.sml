structure forceScheduler :> forceScheduler =
struct

datatype 'a outcome = Proved of 'a | Yielded | Exhausted

fun run engines =
  let
    fun round [] [] = NONE
      | round [] pending = round (List.rev pending) []
      | round (turn :: rest) pending =
          case turn () of
              Proved result => SOME result
            | Yielded => round rest (turn :: pending)
            | Exhausted => round rest pending
  in
    round engines []
  end

end
