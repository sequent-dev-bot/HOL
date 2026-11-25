structure parityLib =
struct

fun solved outcomes =
  length (List.filter (benchLib.outcome_solved o #2) outcomes)

fun count_cause cause shortfalls =
  length
    (List.filter
      (fn ({cause = item, ...} : benchLib.shortfall) => item = cause)
      shortfalls)

(* A battery tactic is run on every goal whose recipe does not already
   use it, solved goals included, so most of what it closes the
   assigned tactic closed too.  Reporting that total under the word
   "additional" invites the reader to add the columns to the
   assigned-tactic count.  Counted here instead are the goals the
   battery tactic closed and the assigned tactic did not: the goals
   where the choice of tactic, not HOL4, is what the corpus measured. *)
fun battery_counts assigned battery =
  let
    fun count ((id, tactic_id, outcome), totals as (auto, blast, aesop)) =
      if benchLib.outcome_solved outcome then
        case Symtab.lookup assigned id of
            SOME (true, _) => totals
          | _ =>
              case tactic_id of
                  benchLib.Auto => (auto + 1, blast, aesop)
                | benchLib.Blast => (auto, blast + 1, aesop)
                | benchLib.Aesop => (auto, blast, aesop + 1)
                | _ => totals
      else totals
  in
    List.foldl count (0, 0, 0) battery
  end

type family = {
  name : string,
  size : int,
  slice : int,
  goals : benchLib.corpus_goal list,
  shortfalls : benchLib.shortfall list,
  run : int -> benchLib.family_result
}

type measured_family = {
  name : string,
  size : int,
  slice : int,
  shortfalls : benchLib.shortfall list,
  gated : (string * benchLib.outcome) list,
  work : (string * searchWork.work) list,
  battery : (string * benchLib.tactic_id * benchLib.outcome) list
}

fun representative_count goals =
  length
    (List.filter
      (fn ({representative, ...} : benchLib.corpus_goal) =>
        representative)
      goals)

val families : family list =
  [{name = "Classical", size = length benchClassical.goals,
    slice = representative_count benchClassical.goals,
    goals = benchClassical.goals,
    shortfalls = benchClassical.shortfalls, run = benchClassical.run},
   {name = "Sets", size = length benchSets.goals,
    slice = representative_count benchSets.goals,
    goals = benchSets.goals,
    shortfalls = benchSets.shortfalls, run = benchSets.run},
   {name = "List/map", size = length benchListMap.goals,
    slice = representative_count benchListMap.goals,
    goals = benchListMap.goals,
    shortfalls = benchListMap.shortfalls, run = benchListMap.run},
   {name = "Linarith", size = length benchLinarith.goals,
    slice = representative_count benchLinarith.goals,
    goals = benchLinarith.goals,
    shortfalls = benchLinarith.shortfalls, run = benchLinarith.run}]

fun measure_family ({name, size, slice, shortfalls, run, ...} : family) =
  let
    val _ = PolyML.fullGC ()
    val result = run 2
    val _ = PolyML.fullGC ()
  in
    {name = name, size = size, slice = slice,
     shortfalls = shortfalls, gated = #gated result,
     work = #work result, battery = #battery result}
  end

(* Milliseconds each solved goal took.  A goal that overran the budget
   is not here: [benchLib.run_goal] reports it as a timeout, so the
   distribution below is bounded by the budget by construction and the
   tail sits in the limitations table instead. *)
fun solved_milliseconds outcomes =
  List.mapPartial
    (fn (_, benchLib.SOLVED elapsed) =>
          SOME (Int.fromLarge (Time.toMilliseconds elapsed))
      | _ => NONE)
    outcomes

fun median [] = 0
  | median values =
      let val ordered = Listsort.sort Int.compare values
      in List.nth (ordered, length ordered div 2) end

fun largest [] = 0
  | largest (value :: values) = List.foldl Int.max value values

fun within lower upper values =
  length (List.filter (fn value => lower <= value andalso value < upper)
           values)

fun seconds milliseconds =
  Real.fmt (StringCvt.FIX (SOME 1)) (Real.fromInt milliseconds / 1000.0)

(* Search work for the goals that solved.  A goal that failed did work
   too, but reporting it would mix "this took a lot of search" with
   "this searched the whole space and found nothing". *)
fun solved_work assigned work =
  List.mapPartial
    (fn (id, item) =>
      case Symtab.lookup assigned id of
          SOME (_, true) => SOME (searchWork.total item)
        | _ => NONE)
    work

fun assigned_outcomes gated =
  let
    (* Battery counts consult the first outcome for an ID. Work samples
       include an ID if any of its outcomes solved. *)
    fun index ((id, outcome), assigned) =
      let
        val first = benchLib.outcome_solved outcome
        val any = first orelse
          (case Symtab.lookup assigned id of SOME (_, true) => true
                                             | _ => false)
      in
        Symtab.update (id, (first, any)) assigned
      end
  in
    List.foldr index Symtab.empty gated
  end

fun samples ({name, gated, work, battery, ...} : measured_family) =
  let val assigned = assigned_outcomes gated
  in
    ((name, solved_milliseconds gated, solved_work assigned work),
     (name, battery_counts assigned battery))
  end

fun cost_row (name, times, work) =
  let
    fun number value = Int.toString value
  in
    "| " ^ name ^ " | " ^ number (length times) ^ " | " ^
    number (within 0 100 times) ^ " | " ^
    number (within 100 1000 times) ^ " | " ^
    number (within 1000 10000 times) ^ " | " ^
    number (within 10000 1000000000 times) ^ " | " ^
    seconds (largest times) ^ " | " ^
    number (median work) ^ " | " ^
    number (largest work) ^ " |\n"
  end

fun primary_row
      ({name, size, slice, gated, ...} : measured_family) =
  let
    fun number value = Int.toString value
  in
    "| " ^ name ^ " | " ^ number size ^ " | " ^
    number (solved gated) ^ " | " ^ number slice ^ " |\n"
  end

fun accounting_row
      ({name, shortfalls, ...} : measured_family) =
  let
    val accepted = count_cause benchLib.AcceptedGap shortfalls
    val engine = count_cause benchLib.EngineLimitation shortfalls
    val translation = count_cause benchLib.TranslationGap shortfalls
    val under = count_cause benchLib.UnderIteration shortfalls
    fun number value = Int.toString value
  in
    "| " ^ name ^ " | " ^ number accepted ^ " | " ^
    number engine ^ " | " ^ number translation ^ " | " ^
    number under ^ " |\n"
  end

fun observation_row (name, (auto, blast, aesop)) =
  let
    fun number value = Int.toString value
  in
    "| " ^ name ^ " | " ^
    number auto ^ " | " ^ number blast ^ " | " ^ number aesop ^ " |\n"
  end

fun total_size rows =
  List.foldl
    (fn ({size, ...} : measured_family, total) => size + total)
    0 rows

fun total_solved rows =
  List.foldl
    (fn ({gated, ...} : measured_family, total) =>
      solved gated + total)
    0 rows

fun total_slice rows =
  List.foldl
    (fn ({slice, ...} : measured_family, total) => slice + total)
    0 rows

fun total_cause cause rows =
  List.foldl
    (fn ({shortfalls, ...} : measured_family, total) =>
      count_cause cause shortfalls + total)
    0 rows

fun total_battery observations =
  List.foldl
    (fn ((_, (auto, blast, aesop)), (autos, blasts, aesops)) =>
      (auto + autos, blast + blasts, aesop + aesops))
    (0, 0, 0) observations

(* A goal whose Isabelle method names a fact that translates onto the
   goal's own HOL4 statement is measured without that fact.  Naming
   those goals is the report's job: the alternative is a solved count
   that rests on a citation no reader could check. *)
fun dropped_citations ({goals, ...} : family) =
  List.mapPartial
    (fn ({id, goal, source_method, provenance, ...}
           : benchLib.corpus_goal) =>
      case benchDerive.self_supplied_of
             (#file provenance ^ ":" ^ Int.toString (#line provenance))
             goal source_method of
          [] => NONE
        | names => SOME (id ^ " (" ^ String.concatWith ", " names ^ ")"))
    goals

(* A citation the name table answers with [Unrepresented] names an
   Isabelle fact HOL4 has no counterpart for, in the library or in the
   translation theory.  The recipe supplies nothing for it, so the goal
   is measured without a fact its source proof had -- the same
   under-crediting the section above reports, reached the other way.
   The table is what knows which citations those are, so the list is
   read out of it. *)
fun unrepresented_citations ({goals, ...} : family) =
  let
    fun absent name =
      case benchNames.lookup name of
          SOME benchNames.Unrepresented => true
        | _ => false
    fun once (name, kept) =
      if List.exists (fn item => item = name) kept then kept
      else kept @ [name]
  in
    List.mapPartial
      (fn ({id, source_method, ...} : benchLib.corpus_goal) =>
        case List.foldl once []
               (List.filter absent
                 (benchRecipe.cited_names
                   (benchRecipe.parse source_method))) of
            [] => NONE
          | names => SOME (id ^ " (" ^ String.concatWith ", " names ^ ")"))
      goals
  end

fun unrepresented_section () =
  let
    val absent = List.concat (map unrepresented_citations families)
  in
    ["## Facts the translation does not render\n\n",
     "An Isabelle proof can name a fact HOL4 states nowhere -- neither ",
     "in a library nor in the translation theory.  The recipe has ",
     "nothing to supply for such a citation, so the goal below is ",
     "measured without it. As above, that can only under-credit HOL4, ",
     "and the goals are named rather than left implicit in a shortfall ",
     "count.\n\n"] @
    (if null absent then ["No goal was measured that way.\n\n"]
     else map (fn text => "- `" ^ text ^ "`\n") absent @ ["\n"])
  end

fun withheld_section () =
  let
    val dropped = List.concat (map dropped_citations families)
  in
    ["## Facts the measurement withheld\n\n",
     "Two distinct Isabelle facts can translate onto one HOL4 theorem, ",
     "and a proof citing one of them then reads as if it assumed what ",
     "it proves. The citation is dropped rather than the goal, so HOL4 ",
     "is asked to close the goal without a fact the Isabelle proof had. ",
     "That can only under-credit HOL4, and it is named here rather ",
     "than left for the reader to discover.\n\n"] @
    (if null dropped then ["No goal was measured that way.\n\n"]
     else map (fn text => "- `" ^ text ^ "`\n") dropped @ ["\n"])
  end

(* The report carries measured elapsed times, and two runs of the same
   corpus do not agree on them to the digit.  A committed report is
   still checked against a fresh one, but with that one section cut
   out of both: what the check is for is drift between the corpus and
   the report, and a solve that took 0.31 s rather than 0.28 s is not
   drift.  Every claim about the corpus -- counts, accounting, scope,
   the withheld citations -- is made outside the cut and stays checked;
   the cut section's own solved column repeats the table above it. *)
val cost_heading = "## Cost of the solutions"

(* The date the run was made is measurement as much as the times are,
   and it was a literal in the prose above until it went stale: the
   thirty-two re-measures since it was last written changed the numbers
   and left the sentence dating them eleven days early.  It is written
   by the clock now, which puts it outside what two reports of the same
   corpus have to agree on -- so the comparison replaces it on both
   sides rather than reading it.  The written form is fixed, so its
   length is. *)
val date_prefix = "The report was generated on "
val date_size = size "2026-08-28"

fun generation_date () =
  Date.fmt "%Y-%m-%d" (Date.fromTimeLocal (Time.now ()))

fun without_date text =
  let
    val (kept, rest) = Substring.position date_prefix (Substring.full text)
  in
    if Substring.isEmpty rest then text
    else
      Substring.concat
        [kept, Substring.full date_prefix, Substring.full "<measured>",
         Substring.triml (size date_prefix + date_size) rest]
  end

fun without_costs text =
  let
    val (kept, rest) =
      Substring.position cost_heading (Substring.full text)
  in
    if Substring.isEmpty rest then text
    else
      let
        val after = Substring.triml (size cost_heading) rest
        val (_, tail) = Substring.position "\n## " after
      in
        Substring.concat [kept, tail]
      end
  end

(* What two reports of the same corpus have to agree on. *)
fun without_measurement text = without_date (without_costs text)

fun render () =
  let
    val rows = map measure_family families
    val (costs, observations) = ListPair.unzip (map samples rows)
    val times = List.concat (map #2 costs)
    val work = List.concat (map #3 costs)
    val (auto, blast, aesop) = total_battery observations
    fun number value = Int.toString value
    val executable = number (total_size rows)
    val assigned_solved = number (total_solved rows)
    val routine = number (total_slice rows)
    val accepted = number (total_cause benchLib.AcceptedGap rows)
    val limitations =
      number (total_cause benchLib.EngineLimitation rows)
    val unavailable =
      number (total_cause benchLib.TranslationGap rows)
    val unaccounted =
      number (total_cause benchLib.UnderIteration rows)
  in
    String.concat
    (["# Automation benchmark results\n\n",
      "## What this report measures\n\n",
      "Each benchmark entry contains a HOL4 theorem statement, the ",
      "Isabelle method used for the corresponding source result, and ",
      "the HOL4 tactic chosen as that method's closest counterpart. ",
      "This report calls that HOL4 tactic the **assigned tactic**.\n\n",
      "The assigned tactic and its arguments are derived from the ",
      "recorded Isabelle method string rather than authored per goal, ",
      "so a goal cannot be handed a fact its source proof did not name. ",
      "One context is added on top of that: the definitions the ",
      "translation introduces whose equations Isabelle's own simpset ",
      "would carry, as rewrites, and only ",
      "to the methods that consult a simpset. This stands in for the ",
      "ambient simpset an Isabelle method reads without naming it. ",
      "Which definitions those are is recorded per constant against the ",
      "Isabelle source line that introduces it: a `fun`, a `primrec`, a ",
      "datatype's selectors and predicator, and a `definition` whose ",
      "characterisation Isabelle separately declares simp are in; a ",
      "plain `definition` is out. A few results Isabelle declares ",
      "`simp` or `iff` about a constant whose definition it withholds ",
      "are carried alongside, each citing the declaration it ",
      "transplants. Two Isabelle facts can translate onto one HOL4 ",
      "theorem, so one of them can be a corpus goal's statement; the ",
      "measurement then withholds it on that goal, as it withholds a ",
      "citation that states its goal, and the selftest checks that it ",
      "does. A second, smaller half stands in for the ambient claset: ",
      "the rules Isabelle declares `intro`, `elim` or `dest` about a ",
      "constant whose definition it withholds, carried with the safety ",
      "Isabelle gives them and only to the methods that consult a ",
      "claset, which is a different set -- `simp` reads none.\n\n",
      "Both halves are cut by Isabelle's theory order. Isabelle reads a ",
      "theory in order and sees only the theories it imports, so a ",
      "result declared below a proof, or in a theory that imports the ",
      "proof's rather than the other way round, was not in that ",
      "proof's simpset or claset: `Pow_Compl` is proved at ",
      "`Set.thy:1610` and knows nothing of `Sigma`, which ",
      "`Product_Type.thy` introduces. The cut reads the goal's mined ",
      "source line and nothing about its statement, so the context is ",
      "one set for the whole corpus rather than a per-goal choice. It ",
      "is a formality on neither side: an out-of-scope rewrite is a ",
      "fact the source proof did not have, and an out-of-scope ",
      "classical rule is search the source proof was not paying for -- ",
      "given the two `Sigma` rules, `Pow_Compl`'s tableau goes from 88 ",
      "branches to 1181 and the proof is lost.\n\n",
      "The comparison data was mined from Isabelle/HOL commit ",
      "`f7e02b7e`. Each in-repository benchmark entry records its source ",
      "file, line, method, and commit. The report was generated on ",
      generation_date (),
      " with a 30-second limit for each tactic attempt. The ",
      "limit is an asynchronous interrupt, so a goal can overrun it by ",
      "the time its search takes to reach an interruptible point; the ",
      "times below are wall-clock and record the overrun where it ",
      "happened.\n\n",
      "## Scope\n\n",
      "The corpus covers six Isabelle theories at one commit -- ",
      "`Set.thy`, `List.thy`, `Product_Type.thy`, `Map.thy`, ",
      "`Option.thy` and `String.thy` -- plus a handful of `ex/` files. ",
      "That is Isabelle's base library, not Isabelle/HOL. What follows ",
      "says what these HOL4 tactics do on those goals at that budget. ",
      "It is not a claim about Isabelle automation in general, and it ",
      "is not a claim about goals outside the six theories.\n\n"] @
     withheld_section () @
     unrepresented_section () @
     ["## Source accounting\n\n",
      "Source mining identified 1,036 relevant Isabelle results. Seven ",
      "pairs translated to the same HOL4 statement except for bound ",
      "variable names, so they are tested once. This leaves 1,029 ",
      "distinct source-derived results:\n\n",
      "- ", executable, " are executable HOL4 benchmark goals.\n",
      "- ", unavailable, " could not be translated faithfully and are ",
      "listed by identifier and reason in the benchmark files.\n",
      "- ", unaccounted, " source results are missing from both groups.\n\n",
      "The selftest checks this accounting in both directions. An ",
      "unexpected failure is an error, but so is an expected failure ",
      "that starts succeeding without its record being updated.\n\n",
      "## Results from the assigned tactics\n\n",
      "**Executable goals** is the number of runnable HOL4 statements. ",
      "**Solved by assigned tactic** counts statements proved by the ",
      "HOL4 counterpart selected for their Isabelle method, with the ",
      "ambient context described above. ",
      "**Routine selftest goals** is a fixed, explicitly marked ",
      "subset run when `HOLSELFTESTLEVEL=1`; it is not a random ",
      "sample. At level 2 or higher, all executable goals run.\n\n",
      "A **family** is a subject-area group:\n\n",
      "- **Classical** contains propositional and first-order logic.\n",
      "- **Sets** contains set and relation reasoning.\n",
      "- **List/map** contains lists, finite maps, options, strings, ",
      "and product types.\n",
      "- **Linarith** contains linear arithmetic over natural numbers, ",
      "integers, real numbers, and rational numbers.\n\n",
      "| Family | Executable goals | Solved by assigned tactic | ",
      "Routine selftest goals |\n",
      "|---|---:|---:|---:|\n"] @
     map primary_row rows @
     ["| **Total** | **", executable, "** | **", assigned_solved,
      "** | **", routine, "** |\n\n",
      "## Cost of the solutions\n\n",
      "A solve at 28 seconds is not the same result as a solve in ",
      "milliseconds, and the count above cannot tell them apart. The ",
      "columns below split the solved goals by elapsed time and report ",
      "the search work the engines metered while solving them: node ",
      "expansions, tableau branches, inferences and rule applications, ",
      "summed. Zero search work means the goal was closed by rewriting ",
      "rather than by search. The time is the tactic's alone: deriving ",
      "the goal's invocation-local simpset is the harness reading its ",
      "own declarations, and it happens before the clock starts. Goals ",
      "that overran the budget are counted as limitations, not here, ",
      "so this distribution is bounded by the budget by ",
      "construction.\n\n",
      "| Family | Solved | < 0.1 s | 0.1-1 s | 1-10 s | > 10 s | ",
      "Slowest | Median search work | Largest search work |\n",
      "|---|---:|---:|---:|---:|---:|---:|---:|---:|\n"] @
     map cost_row costs @
     ["| **Total** | **", number (length times), "** | **",
      number (within 0 100 times), "** | **",
      number (within 100 1000 times), "** | **",
      number (within 1000 10000 times), "** | **",
      number (within 10000 1000000000 times), "** | **",
      seconds (largest times), "** | **",
      number (median work), "** | **",
      number (largest work), "** |\n\n",
      "## Documented results not solved by the assigned tactic\n\n",
      "- **Accepted scope exclusions** are executable goals deliberately ",
      "outside the supported tactic scope, with a recorded reason.\n",
      "- **Assigned-tactic limitations** are executable goals for which ",
      "the assigned tactic failed or exceeded 30 seconds. Each one has ",
      "a dated record naming its root cause, in ",
      "`benchmarks/benchSetShortfalls.sml` or ",
      "`benchmarks/benchLibraryShortfalls.sml`.\n",
      "- **Unavailable translations** are source results that could not ",
      "be represented faithfully as HOL4 goals. They are not included ",
      "in the executable-goal count.\n",
      "- **Unaccounted source results** would be source results that are ",
      "neither executable nor documented as unavailable. This number ",
      "must remain zero.\n\n",
      "| Family | Accepted scope exclusions | Assigned-tactic ",
      "limitations | Unavailable translations | Unaccounted source ",
      "results |\n",
      "|---|---:|---:|---:|---:|\n"] @
     map accounting_row rows @
     ["| **Total** | **", accepted, "** | **", limitations,
      "** | **", unavailable, "** | **", unaccounted, "** |\n\n",
      "For every family, executable goals equal assigned-tactic ",
      "solutions plus accepted scope exclusions plus assigned-tactic ",
      "limitations.\n\n",
      "## Goals another tactic would have closed\n\n",
      "The exhaustive run also tries three general-purpose HOL4 ",
      "tactics on every goal whose recipe does not already use them. A ",
      "goal is counted below when that tactic closed it and the ",
      "assigned tactic did not, so each column measures what the ",
      "method-to-tactic mapping cost rather than what HOL4 cannot do. ",
      "The columns overlap one another and are disjoint from the ",
      "solved count. They are not strength scores: a tactic is never ",
      "counted on a goal it was assigned. They do not affect whether ",
      "the benchmark selftest passes.\n\n",
      "| Family | `AUTO_TAC` | `BLAST_TAC` | `AESOP_TAC` |\n",
      "|---|---:|---:|---:|\n"] @
     map observation_row observations @
     ["| **Total** | **",
      number auto, "** | **", number blast, "** | **",
      number aesop, "** |\n\n",
      "## Seed-rule safety check\n\n",
      "A rule is classified as **safe** when applying it cannot discard ",
      "a possible proof of the goal. The automated seed-rule check ",
      "proves the required reverse direction for every such rule. It ",
      "currently passes with no exceptions.\n\n",
      "## Reproducing the report\n\n",
      "From `src/auto/benchmarks/`:\n\n",
      "```sh\n",
      "Holmake\n",
      "./selftest.exe\n",
      "HOLSELFTESTLEVEL=2 ./selftest.exe\n",
      "./genparity.exe\n",
      "```\n\n",
      "The first selftest command runs the fixed routine subset. The ",
      "second runs every executable goal and the other-tactic ",
      "observations. The final command regenerates `../PARITY.md`.\n"])
  end

(* [render] measures the whole corpus and takes hours, so it runs to
   completion before the file is opened.  Opening first truncates the
   committed report, and a run that dies then leaves an empty one. *)
fun write path =
  let
    val text = render ()
    val stream = TextIO.openOut path
    val _ = TextIO.output (stream, text)
  in
    TextIO.closeOut stream
  end

end
