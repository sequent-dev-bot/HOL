structure benchTactics :> benchTactics =
struct

open HolKernel

(* Isabelle's [arith] and [presburger] decide more than linear
   arithmetic, but [LINARITH_TAC] is the layer's one arithmetic tactic,
   so it is what every arithmetic method stands for. *)
val table : (string * benchLib.tactic_id) list =
  [("simp", benchLib.Simp),
   ("simp_all", benchLib.Simp),
   ("auto", benchLib.Auto),
   ("blast", benchLib.Blast),
   ("force", benchLib.Force),
   ("fastforce", benchLib.Fastforce),
   ("safe", benchLib.Safe),
   ("clarify", benchLib.Clarify),
   ("clarsimp", benchLib.Clarsimp),
   ("metis", benchLib.Metis),
   ("meson", benchLib.Metis),
   ("arith", benchLib.Linarith),
   ("linarith", benchLib.Linarith),
   ("presburger", benchLib.Linarith)]

fun tactic name =
  case List.find (fn (covered, _) => covered = name) table of
      SOME (_, identifier) => identifier
    | NONE =>
        raise mk_HOL_ERR "benchTactics" "tactic"
          ("no HOL4 tactic for the Isabelle method " ^ name)

val methods = map #1 table

end
