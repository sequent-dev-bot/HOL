(*
  Whole-corpus detector sweep.  Writes the findings list named by
  HOLGUARDSOUT, or guards-findings.md here.

  HOLGUARDSSKIP takes a comma-separated detector list, HOLGUARDSFAMILY one
  family name, HOLGUARDSGOAL a comma-separated goal id list, and
  HOLGUARDSLIMIT a per-family goal cap; each makes the report partial, so
  the header records it.  HOLGUARDSPROGRESS=1 names each goal as it is
  swept.  A3 runs every search-method goal, so it is the expensive
  detector; A1 costs upwards of a minute a goal, which is what
  HOLGUARDSGOAL is for.

  A family name that matches none is not an error: the sweep covers no
  goal and every count is zero, which only the Goals column
  distinguishes from a clean report.
*)
val output_path =
  case OS.Process.getEnv "HOLGUARDSOUT" of
      SOME path => path
    | NONE => "guards-findings.md"

val skipped =
  case OS.Process.getEnv "HOLGUARDSSKIP" of
      NONE => []
    | SOME text => String.tokens (fn c => c = #",") text

fun runs detector = not (List.exists (fn name => name = detector) skipped)

val only_family = OS.Process.getEnv "HOLGUARDSFAMILY"

fun selected ({name, ...} : parityLib.family) =
  case only_family of
      NONE => true
    | SOME wanted => name = wanted

val only_goals =
  case OS.Process.getEnv "HOLGUARDSGOAL" of
      NONE => NONE
    | SOME text => SOME (String.tokens (fn c => c = #",") text)

val goal_limit =
  Option.mapPartial Int.fromString (OS.Process.getEnv "HOLGUARDSLIMIT")

val progress = OS.Process.getEnv "HOLGUARDSPROGRESS" = SOME "1"

fun chosen goals =
  case only_goals of
      NONE => goals
    | SOME wanted =>
        List.filter
          (fn (entry : benchLib.corpus_goal) =>
            List.exists (fn id => id = #id entry) wanted)
          goals

fun truncated goals =
  case goal_limit of
      NONE => goals
    | SOME limit =>
        if length goals <= limit then goals else List.take (goals, limit)

fun detector_findings detector body =
  if runs detector then body () else []

(* Per goal, so a sweep that has to be abandoned still says how far it
   got and which goal is slow. *)
fun per_goal detector body goals =
  List.concat
    (map
      (fn (entry : benchLib.corpus_goal) =>
        let
          val started = Time.now ()
          val findings = body [entry]
          val elapsed = Time.- (Time.now (), started)
          val _ =
            if progress then
              TextIO.print
                (detector ^ " " ^ #id entry ^ " " ^
                 Time.toString elapsed ^ "s\n")
            else ()
        in
          findings
        end)
      goals)

type family_findings = {
  name : string,
  goals : int,
  hash : string,
  a1 : benchGuards.finding list,
  a2 : benchGuards.finding list,
  a3 : benchGuards.finding list,
  a4 : benchGuards.finding list
}

fun sweep ({name, goals, ...} : parityLib.family) : family_findings =
  let
    val goals = truncated (chosen goals)
    val _ = TextIO.print ("sweeping " ^ name ^ "\n")
  in
    {name = name, goals = length goals,
     hash = benchGuards.family_hash goals,
     a1 = detector_findings "A1"
            (fn () => per_goal "A1" benchGuards.recognition_findings goals),
     a2 = detector_findings "A2"
            (fn () => benchGuards.provenance_findings goals),
     a3 = detector_findings "A3"
            (fn () =>
              per_goal "A3"
                (benchGuards.search_work_findings benchLib.default_budget)
                goals),
     a4 = detector_findings "A4"
            (fn () => benchGuards.single_use_findings goals)}
  end

fun bullet ({id, detail, ...} : benchGuards.finding) =
  "- `" ^ id ^ "` — " ^ detail ^ "\n"

fun section title findings =
  "### " ^ title ^ " (" ^ Int.toString (length findings) ^ ")\n\n" ^
  (if null findings then "None.\n\n"
   else String.concat (map bullet findings) ^ "\n")

fun number value = Int.toString value

fun summary_row ({name, goals, a1, a2, a3, a4, ...} : family_findings) =
  "| " ^ name ^ " | " ^ number goals ^ " | " ^ number (length a1) ^
  " | " ^ number (length a2) ^ " | " ^ number (length a3) ^ " | " ^
  number (length a4) ^ " |\n"

fun total field rows =
  List.foldl (fn (row, sum) => length (field row) + sum) 0 rows

fun summary rows alias =
  "## Summary\n\n" ^
  "| Family | Goals | A1 recognition | A2 provenance | A3 search work " ^
  "| A4 single-use |\n|---|---:|---:|---:|---:|---:|\n" ^
  String.concat (map summary_row rows) ^
  "| **Total** | **" ^
  number (List.foldl (fn (row, sum) => #goals row + sum) 0 rows) ^
  "** | **" ^ number (total #a1 rows) ^ "** | **" ^
  number (total #a2 rows) ^ "** | **" ^ number (total #a3 rows) ^
  "** | **" ^ number (total #a4 rows) ^ "** |\n\n" ^
  "A5 alias audit: " ^ number (length alias) ^ " hand-mapped display " ^
  "names reported.\n\n"

fun family_report ({name, goals, hash, a1, a2, a3, a4} : family_findings) =
  "## " ^ name ^ " (" ^ number goals ^ " goals)\n\n" ^
  "Goal-term hash (A6): `" ^ hash ^ "`\n\n" ^
  section "A1 recognition" a1 ^
  section "A2 provenance" a2 ^
  section "A3 search work" a3 ^
  section "A4 single-use translation lemmas" a4

val header =
  "# Phase A detector findings\n\n" ^
  "Generated by `guards.exe` in `src/auto/benchmarks/` over the " ^
  "unchanged corpus.  Skipped detectors: " ^
  (if null skipped then "none" else String.concatWith ", " skipped) ^
  (case only_family of
       NONE => ""
     | SOME name => "; restricted to family " ^ name) ^
  (case only_goals of
       NONE => ""
     | SOME wanted =>
         "; restricted to goals " ^ String.concatWith ", " wanted) ^
  (case goal_limit of
       NONE => ""
     | SOME limit =>
         "; first " ^ number limit ^ " goals of each family only") ^
  ".\n\n"

val _ =
  let
    val rows = map sweep (List.filter selected parityLib.families)
    val alias = detector_findings "A5" benchGuards.alias_findings
    val body =
      header ^ summary rows alias ^
      "## A5 alias audit\n\n" ^
      section "Hand-mapped display names" alias ^
      String.concat (map family_report rows)
    val stream = TextIO.openOut output_path
  in
    TextIO.output (stream, body);
    TextIO.closeOut stream;
    TextIO.print ("wrote " ^ output_path ^ "\n")
  end
