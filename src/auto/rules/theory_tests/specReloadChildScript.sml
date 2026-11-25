Theory specReloadChild
Ancestors
  specReloadBase
Libs
  clasetLib

fun fail message = raise Fail ("claset spec reload test: " ^ message)

fun find_rule name =
  List.find (fn (_, (name', _)) => name = name') (rules_of (the_claset ()))

fun has_spec name kind safe prio =
  case find_rule name of
      SOME ({kind = kind', safe = safe', prio = prio'}, _) =>
        kind = kind' andalso safe = safe' andalso prio = prio'
    | NONE => false

val _ =
  List.app
    (fn (name, kind, safe, prio, what) =>
       if has_spec ("specReloadBase$" ^ name) kind safe prio then ()
       else fail ("the " ^ what ^ " delta did not reload"))
    [("spec_intro", clasetRules.Intro, false, SOME 64, "intro"),
     ("spec_elim", clasetRules.Elim, false, SOME 37, "elim"),
     ("spec_dest", clasetRules.Dest, false, SOME 82, "dest"),
     ("spec_forward", clasetRules.Forward, false, SOME 73,
      "unsafe Forward"),
     ("spec_sforward", clasetRules.Forward, true, NONE, "safe Forward"),
     ("spec_norm_default", clasetRules.Norm, false, NONE, "default Norm"),
     ("spec_norm_negative", clasetRules.Norm, false, SOME ~7,
      "negative Norm")]
