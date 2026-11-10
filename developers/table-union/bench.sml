(* Benchmark and validation of the TableUnion prototype.
   Env: TARGET = theory path to load (e.g. .../bodySimMainTheory),
        OUT = output directory, SINGLE_SEED = "1" to also time (c').
   Run: bin/hol run --noconfig developers/table-union/bench.sml *)

fun env s = valOf (OS.Process.getEnv s);
val outdir = env "OUT";
fun openf n = TextIO.openOut (outdir ^ "/" ^ n);
val summ = openf "bench.txt";
fun sout s = (TextIO.output (summ, s ^ "\n"); TextIO.flushOut summ;
              TextIO.output (TextIO.stdErr, s ^ "\n"));

open HolKernel boolLib;

val loadorder = ref ([] : string list);
val _ = Theory.register_hook
          ("tableunion.order",
           fn TheoryDelta.TheoryLoaded s => loadorder := s :: !loadorder
            | _ => ());
val g0 = (Parse.type_grammar (), Parse.term_grammar ());
val tb0 = TypeBase.theTypeBase ();
val target = env "TARGET";
val top = OS.Path.file target
          |> (fn s => String.substring (s, 0, size s - size "Theory"));
val _ = load target;
val loaded = List.rev (!loadorder);
val _ = use (OS.Path.concat (OS.Path.dir (env "SCRIPT"), "TableUnion.sml"));
open TableUnion;

val all = top :: Theory.ancestry top;
val _ = set_ranks all;
val _ = sout ("theories: " ^ Int.toString (length all) ^
              ", loaded by this process: " ^ Int.toString (length loaded));

fun secs t = Real.fmt (StringCvt.FIX (SOME 3)) (Time.toReal t);
fun timeit f x =
    let val _ = PolyML.fullGC ()
        val t = Timer.startRealTimer ()
        val r = f x
    in (r, Timer.checkRealTimer t) end;
fun stats (times : (string * Time.time) list) =
    let
      val xs = Listsort.sort Real.compare (map (Time.toReal o #2) times)
      val n = length xs
      fun pct p = List.nth (xs, Int.min (n - 1, (n * p) div 100))
      val tot = List.foldl op+ 0.0 xs
      fun f r = Real.fmt (StringCvt.FIX (SOME 4)) r
    in
      "n=" ^ Int.toString n ^ " total=" ^ f tot ^ "s median=" ^ f (pct 50) ^
      " p90=" ^ f (pct 90) ^ " max=" ^ f (List.last xs)
    end;
fun top5 (times : (string * Time.time) list) =
    String.concatWith ", "
      (map (fn (t, d) => t ^ " " ^ secs d)
           (List.take (Listsort.sort (fn ((_, a), (_, b)) => Time.compare (b, a)) times,
                       Int.min (5, length times))));

(* ---- grammar dumps ---- *)
fun gdump (tyg, tmg) =
    let
      val tmprint = fn g' => smpp.lift (#2 (Parse.print_from_grammars (tyg, g')))
      val rules = HOLPP.pp_to_string 160
                    (fn () => Parse.mlower (term_grammar.prettyprint_grammar tmprint tmg)) ()
      val tys = HOLPP.pp_to_string 160 (fn () => type_grammar.prettyprint_grammar tyg) ()
      val (p, pm) = Overload.dest_oinfo (term_grammar.overload_info tmg)
      val ovl = Symtab.fold (fn (n, {actual_ops, base_type, ...}) => fn acc =>
                   ("OVL " ^ n ^ " : " ^ tystr (normty base_type) ^ " := " ^
                    String.concatWith " | " (map tmstr actual_ops)) :: acc) p []
      val pms = PM.fold (fn (k, (c, s, ts), acc) => (tmstr (#2 k) ^ " ~ " ^ tmstr c ^ " ~ " ^ s, ts) :: acc) [] pm
      val tss = Listsort.sort Int.compare (map #2 pms)
      val rank = #2 (List.foldl (fn (ts, (i, m)) => (i + 1, Inttab.update (ts, i) m))
                                (0, Inttab.empty) tss)
      val pml = Listsort.sort String.compare
                  (map (fn (s, ts) => "PM " ^ s ^ " @" ^ Int.toString (valOf (Inttab.lookup rank ts))) pms)
    in
      String.fields (fn c => c = #"\n") rules @ ["---- types"] @
      String.fields (fn c => c = #"\n") tys @ ["---- overloads"] @ List.rev ovl @
      ["---- print map"] @ pml
    end;
fun cmp_dumps name (a, b) =
    let
      fun w file ls = let val f = openf file
                      in List.app (fn l => TextIO.output (f, l ^ "\n")) ls; TextIO.closeOut f end
      val same = a = b
    in
      if same then () else (w (name ^ "-union.txt") a; w (name ^ "-replay.txt") b);
      same
    end;

(* ---- per table ---- *)
fun gparents t =
    List.filter (fn p => p <> t)
      (case Parse.grammar_ancestry {thyname = t} of [] => Theory.parents t | l => l);

val tbspec = {parents = thy_parents, base = {tb = valOf (TypeBase.thy_typebase {thyname = "min"}), st = Symtab.empty : stamps},
              union = tb_union, own = tb_own};
val ssspec = {parents = thy_parents, base = {ss = initial_simpset, st = Symtab.empty : stamps},
              union = ss_union, own = ss_own};
val gspec = {parents = gparents,
             base = {tyg = #1 Parse.min_grammars, tmg = #2 Parse.min_grammars,
                     st = Symtab.empty : stamps,
                     small = [] : (estamp * GrammarDeltas.gdelta) list},
             union = g_union, own = g_own};

fun report name (spec : {parents : string -> string list, base : 'v,
                         union : 'v * 'v -> 'v, own : string -> 'v -> 'v})
           (same : 'v * 'v -> bool) (check : 'v * string list -> bool) =
    let
      val thys = cone (#parents spec) top
      val _ = sout ("== " ^ name ^ ": cone " ^ Int.toString (length thys))
      (* (c) every value bottom-up *)
      val ((tab, times), dt) = timeit (build spec) thys
      val _ = sout ("(c) bottom-up union, all values: " ^ secs dt ^ "s; per theory " ^
                    stats times ^ "; slowest: " ^ top5 times)
      val v = valOf (Symtab.lookup tab top)
      (* (b) the top theory alone, given its parents' values *)
      fun at_top () =
          let val ps = Listsort.sort (fn (a, b) => canon_cmp (b, a)) (#parents spec top)
              fun value t = valOf (Symtab.lookup tab t)
              val u = List.foldl (fn (q, u) => #union spec (u, value q))
                                 (value (hd ps)) (tl ps)
          in #own spec top u end
      val bs = List.tabulate (5, fn _ => #2 (timeit at_top ()))
      val _ = sout ("(b) " ^ top ^ " from its " ^ Int.toString (length (#parents spec top)) ^
                    " parents' values: " ^ String.concatWith " " (map secs bs) ^ "s")
      (* idempotence and parent order *)
      val idem = same (#union spec (v, v), v)
      val ps = #parents spec top
      fun value t = valOf (Symtab.lookup tab t)
      val rev_v = #own spec top (List.foldl (fn (q, u) => #union spec (u, value q))
                                             (value (List.last ps)) (List.rev (List.take (ps, length ps - 1))))
      val _ = sout ("union (v, v) == v: " ^ Bool.toString idem)
      val ok = check (v, thys)
      val okrev = check (rev_v, thys)
      val _ = sout ("matches canonical replay: " ^ Bool.toString ok ^
                    "; with parents in reverse order: " ^ Bool.toString okrev)
    in
      (tab, thys)
    end;

(* ---- checks against canonical replay ---- *)
fun tbcheck ({tb, st} : tbv, thys) =
    let
      val thys = List.filter (fn t => t <> "min") thys
      val r = tb_replay thys (valOf (TypeBase.thy_typebase {thyname = "min"}))
      val names = Listsort.sort String.compare o map tbkey o TypeBasePure.listItems
      val winners = List.foldl (fn (t, m) => List.foldl (fn (tyi, m) => Symtab.update (tbkey tyi, t) m)
                                                        m (TypeBase.thy_updates {thyname = t}))
                               Symtab.empty thys
      val wdiff = Symtab.fold (fn (k, t) => fn acc =>
                     case Symtab.lookup st k of
                         SOME ((_, t', _), _) => if t = t' then acc else (k ^ ":" ^ t ^ "/" ^ t') :: acc
                       | NONE => (k ^ ":" ^ t ^ "/none") :: acc) winners []
      val nu = names tb and nr = names r
      val _ = sout ("   types: union " ^ Int.toString (length nu) ^ ", replay " ^
                    Int.toString (length nr) ^ ", same " ^ Bool.toString (nu = nr) ^
                    "; last writer differs: " ^ Int.toString (length wdiff) ^ " " ^
                    String.concatWith " " (List.take (wdiff, Int.min (5, length wdiff))) ^
                    "; only in replay: " ^ String.concatWith " " (List.filter (fn x => not (Lib.mem x nu)) nr) ^
                    "; only in union: " ^ String.concatWith " " (List.filter (fn x => not (Lib.mem x nr)) nu))
    in
      nu = nr andalso null wdiff
    end;
fun sscheck ({ss, ...} : ssv, thys) =
    let
      val (r, dt) = timeit (ss_replay (List.filter (fn t => t <> "min") thys)) initial_simpset
      val _ = sout ("   canonical replay of the cone: " ^ secs dt ^ "s")
      val a = simpLib.net_entries ss and b = simpLib.net_entries r
      val fa = Listsort.sort String.compare (simpLib.ssfrag_names_of ss)
      val fb = Listsort.sort String.compare (simpLib.ssfrag_names_of r)
      fun ne (SOME t, n) = t ^ "." ^ n | ne (NONE, n) = n
      val _ = if a = b then ()
              else let val f = openf "simp-entries.txt"
                   in TextIO.output (f, "union " ^ Int.toString (length a) ^ " replay " ^
                                        Int.toString (length b) ^ "\n");
                      ListPair.app (fn (x, y) => if x = y then ()
                                                 else TextIO.output (f, ne x ^ "  /  " ^ ne y ^ "\n")) (a, b);
                      TextIO.closeOut f
                   end
      val _ = sout ("   net entries: union " ^ Int.toString (length a) ^ ", replay " ^
                    Int.toString (length b) ^ ", same order " ^ Bool.toString (a = b) ^
                    "; frags same " ^ Bool.toString (fa = fb) ^ "; dprocs " ^
                    Int.toString (simpLib.num_dprocs ss))
    in
      a = b andalso fa = fb
    end;
val gcheck_n = ref 0;
fun gcheck ({tyg, tmg, ...} : gv, thys) =
    let
      val (r, dt) = timeit (g_replay (List.filter (fn t => t <> "min") thys)) Parse.min_grammars
      val _ = sout ("   canonical replay of the cone: " ^ secs dt ^ "s")
      val _ = gcheck_n := !gcheck_n + 1
    in
      cmp_dumps ("grammar" ^ Int.toString (!gcheck_n)) (gdump (tyg, tmg), gdump r)
    end;

val _ = report "TypeBase" tbspec tb_same tbcheck;
val (sstab, ssthys) = report "srw simpset" ssspec ss_same sscheck;
val (gtab, gthys) = report "grammar" gspec g_same gcheck;

(* ---- load order vs canonical order, structural dumps ---- *)
val _ =
    let
      fun raw thys = List.foldl (fn (t, g) => List.foldl (fn (d, g) => gapply d g) g (g_deltas t))
                                Parse.min_grammars thys
      val gl = List.filter (fn t => Lib.mem t gthys) loaded
      val baseo = List.filter (fn t => not (Lib.mem t loaded) andalso t <> "min") gthys
      fun w file ls = let val f = openf file
                      in List.app (fn l => TextIO.output (f, l ^ "\n")) ls; TextIO.closeOut f end
    in
      w "grammar-load.txt" (gdump (raw (baseo @ gl)));
      w "grammar-canon.txt" (gdump (raw (List.filter (fn t => t <> "min") gthys)))
    end;

(* ---- (a) today's work: load-order replay of the loaded theories' deltas
   onto the start state of this process ---- *)
val _ = sout "== (a) load-order replay of the loaded theories onto the hol.state tables";
val (_, dt) = timeit (List.foldl (fn (t, g) => List.foldl (fn (d, g) => gapply d g) g (g_deltas t)) g0) loaded;
val _ = sout ("grammar: " ^ secs dt ^ "s");
val (_, dt) = timeit (tb_replay loaded) tb0;
val _ = sout ("TypeBase: " ^ secs dt ^ "s");
val ssbase = ss_replay (List.filter (fn t => not (Lib.mem t loaded) andalso t <> "min") ssthys) initial_simpset;
val (_, dt) = timeit (ss_replay loaded) ssbase;
val _ = sout ("srw frags: " ^ secs dt ^ "s");

(* ---- (c') single seed: each value from its latest parent's value plus a
   replay of the deltas of the ancestors that parent lacks ---- *)
val _ =
    if OS.Process.getEnv "SINGLE_SEED" = SOME "1" then
      let
        fun single name parents replay base tab =
            let
              val thys = cone parents top
              val cones = ref (Symtab.empty : string HOLset.set Symtab.table)
              fun anc t = case Symtab.lookup (!cones) t of
                              SOME s => s
                            | NONE => let val s = HOLset.addList (HOLset.empty String.compare,
                                                                  cone parents t)
                                      in cones := Symtab.update (t, s) (!cones); s end
              fun step (t, (vs, times)) =
                  if t = "min" then (Symtab.update (t, base) vs, times)
                  else
                    let
                      val ps = Listsort.sort (fn (a, b) => canon_cmp (b, a)) (parents t)
                      val seed = case ps of [] => "min" | p :: _ => p
                      val sa = anc seed
                      val missing = List.filter (fn x => not (HOLset.member (sa, x)))
                                                (cone parents t)
                      val tm = Timer.startRealTimer ()
                      val v = replay missing (valOf (Symtab.lookup vs seed))
                      val d = Timer.checkRealTimer tm
                    in
                      (Symtab.update (t, v) vs, (t, d) :: times)
                    end
              val ((_, times), dt) = timeit (List.foldl step (Symtab.empty, [])) thys
            in
              sout ("(c') single-seed " ^ name ^ ": " ^ secs dt ^ "s; per theory " ^ stats times ^
                    "; slowest: " ^ top5 times)
            end
      in
        single "TypeBase" thy_parents tb_replay
               (valOf (TypeBase.thy_typebase {thyname = "min"})) ();
        single "srw" thy_parents ss_replay initial_simpset ();
        single "grammar" gparents g_replay Parse.min_grammars ()
      end
    else ();
val _ = TextIO.closeOut summ;
