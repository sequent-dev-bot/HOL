open HolKernel

fun required_environment name =
  case OS.Process.getEnv name of
      SOME value => value
    | NONE => raise Fail (name ^ " must be set")

val family = required_environment "HOLBENCHFAMILY"

(* Only the HOLBENCHOVERRIDE path needs a single goal named; without it
   this runs the family, which HOLBENCHGOAL then narrows if it is set. *)
val goal_id =
  case OS.Process.getEnv "HOLBENCHGOAL" of
      SOME id => id
    | NONE => ""
val level = benchLib.selftest_level ()
fun set_trace_from_environment environment trace =
  case OS.Process.getEnv environment of
      NONE => ()
    | SOME text =>
        (case Int.fromString text of
             SOME trace_level =>
               HOLFlags.set_trace trace trace_level
           | NONE =>
               raise Fail (environment ^ " must be an integer"))

val _ = set_trace_from_environment "HOLBENCHBLASTTRACE" "blast.trace"
val _ = set_trace_from_environment "HOLBENCHCLASSICALTRACE" "classical.trace"
val _ = set_trace_from_environment "HOLBENCHLINARITHTRACE" "linarith.trace"

fun family_goals () =
  case family of
      "sets" => benchSets.goals
    | "listmap" => benchListMap.goals
    | "classical" => benchClassical.goals
    | "linarith" => benchLinarith.goals
    | _ => raise Fail ("unknown HOLBENCHFAMILY: " ^ family)

fun selected_goal () =
  case List.filter
         (fn (goal : benchLib.corpus_goal) =>
           goal_id <> "" andalso #id goal = goal_id)
         (family_goals ()) of
      [goal] => goal
    | [] =>
        raise Fail
          (if goal_id = "" then "HOLBENCHGOAL must be set"
           else "unknown HOLBENCHGOAL: " ^ goal_id)
    | _ => raise Fail ("duplicate HOLBENCHGOAL: " ^ goal_id)

fun first_arguments recipe =
  case recipe of
      benchLib.Invoke (_, arguments) => arguments
    | benchLib.Then (left, _) => first_arguments left
    | benchLib.AllGoals (left, _) => first_arguments left
    | benchLib.Repeat inner => first_arguments inner

fun override_tactic name =
  case name of
      "simp" => benchLib.Simp
    | "auto" => benchLib.Auto
    | "blast" => benchLib.Blast
    | "force" => benchLib.Force
    | "fastforce" => benchLib.Fastforce
    | "metis" => benchLib.Metis
    | _ => raise Fail ("unknown HOLBENCHOVERRIDE: " ^ name)

fun print_outcome outcome =
  case outcome of
      benchLib.SOLVED elapsed =>
        print ("solved: " ^ Time.toString elapsed ^ "\n")
    | benchLib.TIMEOUT => print "timeout\n"
    | benchLib.FAILED message => print ("failed: " ^ message ^ "\n")

val _ =
  case OS.Process.getEnv "HOLBENCHOVERRIDE" of
      SOME name =>
        let
          val goal = selected_goal ()
          val recipe =
            benchLib.Invoke
              (override_tactic name, first_arguments (#recipe goal))
        in
          print_outcome
            (benchLib.run_goal benchLib.default_budget recipe goal)
        end
    | NONE =>
        case family of
            "sets" => ignore (benchSets.run level)
          | "listmap" => ignore (benchListMap.run level)
          | "classical" => ignore (benchClassical.run level)
          | "linarith" => ignore (benchLinarith.run level)
          | _ => raise Fail ("unknown HOLBENCHFAMILY: " ^ family)
