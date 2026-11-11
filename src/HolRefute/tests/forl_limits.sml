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
fun solve limit problems = solve_any_problem false false
  (Time.now () + Time.fromSeconds 60) 1 limit 1 problems
fun check name condition =
  if condition then print (name ^ ": PASS\n") else raise Fail name
val _ =
  if mode = "cnf" then
    let
      val limit = #max_file_size (#mf Refute_Core.default_config)
      (* Kodkodi 1.5.7 writes 24,862,426 bytes for this function relation.
         The model pins that the external solver actually ran. *)
      val accepted = case solve limit [problem] of
          Normal ([(_, [((2, 0), rows)])], [], "") => length rows = 500
        | _ => false
      val low = #max_file_size (#mf
        (Refute_Core.upd_max_file_size 16 Refute_Core.default_config))
      (* Same problem, same session: a cached success must not hide the
         smaller file limit. Kodkodi reports the write error with exit 0. *)
      val refused = case solve low [problem] of
          Normal ([], [], message) =>
            String.isSubstring "File too large" message
        | Error (message, []) => String.isSubstring "File too large" message
        | _ => false
    in
      check "CNF above 16 MiB reaches external MiniSat" accepted;
      check "lower file limit is enforced after cached success" refused
    end
  else
    let
      val expected = if mode = "stdout" then "output" else "stderr"
      val bounded = case solve 256 [problem, problem] of
          Normal ([], [0], message) =>
            String.isSubstring ("Kodkodi " ^ expected ^ " was truncated")
              message andalso not (String.isSubstring "AFTER_LIMIT" message)
        | _ => false
    in
      check (mode ^ " keeps only complete outcomes within 16 MiB") bounded
    end
