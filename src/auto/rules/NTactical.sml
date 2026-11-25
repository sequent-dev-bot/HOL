structure NTactical :> NTactical =
struct

open Abbrev


type nresult = goal list * validation
type ntactic = goal -> Context.t -> nresult seq.seq
type wrapper = ntactic -> ntactic

fun LIFT tac g ctxt =
  seq.delay
    (fn () =>
       seq.result (tac g ctxt) handle Feedback.HOL_ERR _ => seq.empty)

fun DETERM ntac g ctxt =
  case seq.cases (ntac g ctxt) of
      NONE => Tactical.NO_TAC g ctxt
    | SOME (result, _) => result

val NNO_TAC : ntactic = fn _ => fn _ => seq.empty
val NALL_TAC : ntactic = LIFT Tactical.ALL_TAC

fun NTHEN (tac1, tac2) g ctxt =
  let
    fun all_goals ([] : goal list) :
          (goal list * int list * validation list) seq.seq =
          seq.result ([], [], [])
      | all_goals (g0 :: gs0) =
          seq.delay
            (fn () =>
               seq.bind (tac2 g0 ctxt)
                 (fn (gs1, v1) =>
                    seq.map
                      (fn (gs2, lengths, vs) =>
                         (gs1 @ gs2, length gs1 :: lengths, v1 :: vs))
                      (all_goals gs0)))
  in
    seq.delay
      (fn () =>
         seq.bind (tac1 g ctxt)
           (fn (gs, v) =>
              seq.map
                (fn (gs', lengths, vs) =>
                   (gs', v o Lib.mapshape lengths vs))
                (all_goals gs)))
  end

fun NORELSE (tac1, tac2) g ctxt =
  seq.delay
    (fn () =>
       case seq.cases (tac1 g ctxt) of
           NONE => tac2 g ctxt
         | SOME (result, rest) => seq.cons result rest)

fun NAPPEND (tac1, tac2) g ctxt =
  seq.append (seq.delay (fn () => tac1 g ctxt))
             (seq.delay (fn () => tac2 g ctxt))

fun NTRY tac = NORELSE (tac, NALL_TAC)

fun NREPEAT tac = LIFT (Tactical.REPEAT (DETERM tac))

fun NCHANGED tac g ctxt =
  seq.delay
    (fn () =>
       seq.filter
         (fn (gs, _) =>
            case gs of
                [g'] => not (boolSyntax.goal_eq g g')
              | _ => true)
         (tac g ctxt))

end
