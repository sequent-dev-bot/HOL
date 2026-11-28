(* A bare [hol run] script sets no current theory, and TAC_PROOF then
   refuses every proof: the case lifts and the unwinding are left
   undone, so narrowing is stuck on a choice.  The call says so, in its
   output and among its reasons, instead of answering a plain Unknown.
   No [Thm.setCT] here, on purpose. *)
local open Refute in end
open HolKernel Parse boolLib testutils

fun check name predicate = (tprint name; if predicate then OK () else die name)

val config = Refute.default_config
  |> Refute.upd_search (Refute.Only [Refute.Narrowing])
  |> Refute.upd_substrate Refute.NativeSML
  |> Refute.upd_sequential true
  |> Refute.upd_size 10

val _ = check "there is no current theory"
  (not (Lib.can Theory.current_theory ()))

val (result, output) =
  let
    val chunks = ref ([] : string list)
    fun collect text = chunks := text :: !chunks
    val result =
      Lib.with_flag (Feedback.MESG_outstream, collect)
        (Lib.with_flag (Feedback.WARNING_outstream, collect)
          (Refute.refute config))
        ``!xs. case oHD (xs : num list) of
                 NONE => T | SOME x => x < 3 ==> ?z. z < x``
  in
    (result, String.concat (rev (!chunks)))
  end

val _ = check "a call with no current theory gives Unknown with the reason"
  (case result of
       Refute.Unknown reasons =>
         List.exists (String.isPrefix "no current theory") reasons
     | _ => false)

val _ = check "a call with no current theory prints the reason"
  (String.isSubstring "Refute: no current theory" output)
