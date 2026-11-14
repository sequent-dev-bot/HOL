(* Isolated processes let the transcript regressions override the launcher. *)
val _ = Thm.setCT "scratch"
open Refute_Forl
val mode = Option.getOpt (OS.Process.getEnv "FORL_LIMIT_CASE", "cnf")
val (_, solver) =
  Refute_ForlSat.sat_solver_spec (Time.fromSeconds 60) "MiniSat"
val problem : problem =
  {comment = "file limit regression",
   settings = [("solver", String.concatWith ", " (map Lib.quote solver)),
               ("symmetry_breaking", "0")],
   univ_card = 500, tuple_assigns = [],
   bounds = [([((2, 0), "")], [TupleSet [],
     TupleProduct (TupleAtomSeq (500, 0), TupleAtomSeq (500, 0))])],
   int_bounds = [], expr_assigns = [],
   formula = Function ((2, 0), Univ, Univ)}
(* The batch is a solver session, drained here:
   the results in the order they arrived, then how the solver ended. *)
fun session_for seconds limit problems =
  submit {debug = false, overlord = false,
          deadline = Time.now () + Time.fromSeconds seconds,
          max_threads = 1, max_file_size = limit, max_solutions = 1,
          problems = problems}
fun collect (session : session) =
  let
    fun loop events =
      case #next session () of
          Ended ended => (rev events, ended)
        | event => loop (event :: events)
  in loop [] end
fun solve_for seconds limit problems =
  let val session = session_for seconds limit problems
  in
    Portable.finally (fn () => ignore (#close session ()))
      (fn () => collect session) ()
  end
fun solve limit problems = solve_for 60 limit problems
fun check name condition =
  if condition then print (name ^ ": PASS\n") else raise Fail name
val pidfile = Option.getOpt (OS.Process.getEnv "FORL_PIDFILE", "")
fun alive () =
  let
    val stream = TextIO.openIn pidfile
    val pid = TextIO.inputLine stream
    val _ = TextIO.closeIn stream
  in
    OS.Process.isSuccess (OS.Process.system
      ("kill -0 " ^ String.translate
         (fn #"\n" => "" | c => String.str c) (Option.getOpt (pid, "0")) ^
       " 2>/dev/null"))
  end
fun seconds_since start = Time.toReal (Time.now () - start)
val _ =
  if mode = "cnf" then
    let
      val limit = #max_file_size (#mf Refute_Core.default_config)
      (* Kodkodi 1.5.7 writes 24,862,426 bytes for this function relation.
         The model pins that the external solver actually ran. *)
      val accepted = case solve limit [problem] of
          ([Sat (_, [((2, 0), rows)])],
           {ending = Finished, message = "", ...}) => length rows = 500
        | _ => false
      val low = #max_file_size (#mf
        (Refute_Core.upd_max_file_size 16 Refute_Core.default_config))
      (* Same problem, same session: a cached success must not hide the
         smaller file limit. Kodkodi reports the write error with exit 0. *)
      val refused = case solve low [problem] of
          ([], {ending = Finished, message, ...}) =>
            String.isSubstring "File too large" message
        | ([], {ending = Failed message, ...}) =>
            String.isSubstring "File too large" message
        | _ => false
    in
      check "CNF above 16 MiB reaches external MiniSat" accepted;
      check "lower file limit is enforced after cached success" refused
    end
  else if mode = "inherited" then
    check "inherited hard limit returns a solver error"
      (case solve 256 [problem] of
           ([], {ending = Failed message, ...}) =>
             String.isSubstring "ulimit" message
         | _ => false)
  else if mode = "stream" then
    (* The first problem's result arrives while the solver still runs, and
       cancelling stops the solver. *)
    let
      val start = Time.now ()
      val session = session_for 60 256 [problem, problem]
      val first = #next session ()
      val early = seconds_since start < 20.0
      val running = alive ()
      val _ = #cancel session ()
      val leftover = #close session ()
    in
      check "a finished problem is delivered while the solver still runs"
        (first = Unsat 0 andalso early andalso running);
      check "cancel stops the solver" (not (alive ()) andalso leftover = 0)
    end
  else if mode = "deadline" then
    let
      val start = Time.now ()
      val (events, ended) = solve_for 4 256 [problem, problem]
      val elapsed = seconds_since start
    in
      check "everything finished before the deadline counts, then the batch is cut"
        (events = [Unsat 0] andalso #ending ended = Cut andalso
         elapsed >= 3.0 andalso elapsed < 20.0 andalso not (alive ()))
    end
  else if mode = "errors" then
    let
      val (events, ended) = solve 256 [problem, problem, problem]
    in
      check "errors are counted by message and the batch ended by itself"
        (events = [Unsat 0] andalso #ending ended = Finished andalso
         #errors ended = [("boom", 2), ("other", 1)])
    end
  else if mode = "limit" then
    let
      val limitfile = valOf (OS.Process.getEnv "FORL_LIMITFILE")
      fun limit_of file =
        let val stream = TextIO.openIn file
            val text = TextIO.inputLine stream
            val _ = TextIO.closeIn stream
        in String.translate (fn #"\n" => "" | c => String.str c)
             (Option.getOpt (text, "")) end
      val _ = solve 77 [problem]
      val small = limit_of limitfile
      val _ = solve 256 [problem]
      val default = limit_of limitfile
    in
      check "the child's file-size limit is the option's value, in 512-byte blocks"
        (small = Int.toString (77 * 2048) andalso
         default = Int.toString (256 * 2048))
    end
  else
    let
      val expected = if mode = "stderr" then "stderr" else "output"
      val bounded = case solve 256 [problem, problem] of
          ([Unsat 0], {message, ...}) =>
            String.isSubstring ("Kodkodi " ^ expected ^ " was truncated")
              message andalso not (String.isSubstring "AFTER_LIMIT" message)
        | _ => false
    in
      check (mode ^ " keeps only complete outcomes within 16 MiB") bounded
    end
