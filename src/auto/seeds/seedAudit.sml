structure seedAudit :> seedAudit =
struct

open Abbrev HolKernel

val ERR = mk_HOL_ERR "seedAudit"

type waiver = {rule : string, reason : string, date : string}

datatype obligation_kind =
    SafeZero
  | IntroInversion
  | ElimExhaustiveness
  | ElimPreservation of int
  | KernelPreservation
  | SplitShape

type obligation = {kind : obligation_kind, term : term}

datatype result =
    Proved of {rule : string, kind : obligation_kind,
               prover : string, elapsed : Time.time}
  | Waived of {rule : string, kind : obligation_kind,
               waiver : waiver, detail : string}
  | Failed of {rule : string, kind : obligation_kind,
               detail : string}

type report = {
  checked : int,
  proved : int,
  waivers : waiver list,
  results : result list,
  split_checked : int
}

val default_budget = Time.fromSeconds 5

fun conjunction [] = boolSyntax.T
  | conjunction terms = boolSyntax.list_mk_conj terms

fun disjunction [] = boolSyntax.F
  | disjunction terms = boolSyntax.list_mk_disj terms

fun safe_zero form =
  [{kind = SafeZero, term = Thm.concl (#thm form)}]

fun intro_obligations theorem =
  let
    val form = clasetRules.canonical_form_of clasetRules.Intro theorem
    val prems = #prems form
  in
    if null prems then safe_zero form
    else
      let
        val premise_vars = free_varsl prems
        val extras =
          Lib.op_set_diff Term.aconv premise_vars (free_vars (#concl form))
        val recovered =
          boolSyntax.list_mk_exists (extras, conjunction prems)
        val implication = boolSyntax.mk_imp (#concl form, recovered)
      in
        [{kind = IntroInversion, term = boolSyntax.gen_all implication}]
      end
  end

type branch = {eigen : term list, hyps : term list}

fun minor_branch final minor =
  let
    fun peel eigen hyps term =
      if Term.aconv term final then
        {eigen = List.rev eigen, hyps = List.rev hyps}
      else
        case Lib.total boolSyntax.dest_forall term of
            SOME (variable, body) => peel (variable :: eigen) hyps body
          | NONE =>
              (case Lib.total boolSyntax.dest_imp_only term of
                  SOME (antecedent, body) =>
                    if Term.aconv antecedent (boolSyntax.mk_neg final) then
                      peel eigen hyps body
                    else
                      peel eigen (antecedent :: hyps) body
                | NONE =>
                    raise ERR "minor_branch"
                      ("elimination minor concludes " ^
                       Parse.term_to_string term ^ ", not " ^
                       Parse.term_to_string final))
  in
    peel [] [] minor
  end

fun branch_exists ({eigen, hyps} : branch) =
  boolSyntax.list_mk_exists (eigen, conjunction hyps)

fun preservation major ({eigen, hyps} : branch) =
  let
    val implication = boolSyntax.mk_imp (conjunction hyps, major)
  in
    boolSyntax.list_mk_forall (eigen, boolSyntax.gen_all implication)
  end

fun elim_obligations theorem =
  let
    val form = clasetRules.canonical_form_of clasetRules.Elim theorem
  in
    case #prems form of
        [] => raise ERR "elim_obligations" "elimination rule has no major"
      | [major] => safe_zero form
      | major :: minors =>
          let
            val branches = map (minor_branch (#concl form)) minors
            val exhaustive =
              boolSyntax.gen_all
                (boolSyntax.mk_imp
                  (major, disjunction (map branch_exists branches)))
            val preservation_obligations =
              Portable.mapi
                (fn index => fn branch =>
                  {kind = ElimPreservation (index + 1),
                   term = preservation major branch})
                branches
          in
            {kind = ElimExhaustiveness, term = exhaustive} ::
            preservation_obligations
          end
  end

fun obligations ({spec, info, ...} : clasetLib.aesop_rule) =
  if not (#safe spec) then []
  else
    let
      val theorem = #1 (#rl info)
    in
      case #kind spec of
          clasetRules.Intro => intro_obligations theorem
        | clasetRules.Elim => elim_obligations theorem
        | clasetRules.Dest => elim_obligations theorem
        | clasetRules.Forward =>
            [{kind = KernelPreservation, term = Thm.concl theorem}]
        | clasetRules.Norm =>
            [{kind = KernelPreservation, term = Thm.concl theorem}]
    end

fun remaining budget timer =
  Time.toReal budget - Time.toReal (Timer.checkRealTimer timer)

fun run_tactic budget timer name tactic term =
  let
    val seconds = remaining budget timer
  in
    if seconds <= 0.0 then NONE
    else
      (Timeout.apply (Time.fromReal seconds)
         (fn () =>
           let
             val started = Timer.startRealTimer ()
             val (goals, validation) =
               Tactical.VALID tactic ([], term) (Context.snapshot())
             val elapsed = Timer.checkRealTimer started
           in
             if null goals then SOME (name, elapsed, validation []) else NONE
           end) ()
       handle Timeout.TIMEOUT _ => NONE
            | Portable.Interrupt => raise Portable.Interrupt
            | _ => NONE)
  end

fun metis_tactic seconds =
  let
    val parameters =
      metisTools.update_limit
        (fn {time = _, infs} =>
          {time = SOME (Real.max (0.001, seconds)), infs = infs})
        metisTools.defaults
  in
    metisTools.GEN_METIS_TAC parameters []
  end

fun prove_obligation budget term =
  let
    val timer = Timer.startRealTimer ()
    fun attempt name tactic = run_tactic budget timer name tactic term
  in
    case attempt "meson" (BasicProvers.GEN_PROVE_TAC 0 30 1 []) of
        SOME answer => SOME answer
      | NONE =>
          (case attempt "metis" (metis_tactic (remaining budget timer)) of
              SOME answer => SOME answer
            | NONE =>
                (case attempt "simp+meson"
                        (Tactical.THEN
                          (simpLib.SIMP_TAC (BasicProvers.srw_ss ()) [],
                           BasicProvers.GEN_PROVE_TAC 0 30 1 [])) of
                    SOME answer => SOME answer
                  | NONE => attempt "auto" (clasimpLib.AUTO_TAC [])))
  end

fun waiver_for name waivers =
  List.find (fn ({rule, ...} : waiver) => rule = name) waivers

fun validate_waivers waivers =
  let
    fun valid ({rule, reason, date} : waiver) =
      rule <> "" andalso reason <> "" andalso date <> ""
    val distinct =
      length (listUtil.distinct_by String.compare #rule waivers) =
      length waivers
  in
    if List.all valid waivers andalso distinct
    then ()
    else
      raise ERR "validate_waivers"
        "waivers need unique non-empty rule, reason, and date fields"
  end

fun inspect_rule budget waivers
      ({name, ...} : clasetLib.aesop_rule) obligation =
  let
    val {kind, term} = obligation
  in
    case kind of
        SafeZero =>
          Proved {rule = name, kind = kind, prover = "kernel",
                  elapsed = Time.zeroTime}
      | KernelPreservation =>
          Proved {rule = name, kind = kind, prover = "kernel",
                  elapsed = Time.zeroTime}
      | _ =>
          (case prove_obligation budget term of
              SOME (prover, elapsed, _) =>
                Proved {rule = name, kind = kind, prover = prover,
                        elapsed = elapsed}
            | NONE =>
                (case waiver_for name waivers of
                    SOME waiver =>
                      Waived {rule = name, kind = kind, waiver = waiver,
                              detail = "fixed prover stack did not close"}
                  | NONE =>
                      Failed {rule = name, kind = kind,
                              detail =
                                "fixed prover stack did not close within " ^
                                Time.toString budget}))
  end

fun split_results waivers =
  let
    fun inspect_split (name, theorem) =
      ((ignore (splitLib.split_forms theorem);
        Proved {rule = name, kind = SplitShape, prover = "splitLib",
                elapsed = Time.zeroTime})
       handle Portable.Interrupt => raise Portable.Interrupt
            | exn =>
                (case waiver_for name waivers of
                    SOME waiver =>
                      Waived {rule = name, kind = SplitShape,
                              waiver = waiver,
                              detail = Feedback.exn_to_string exn}
                  | NONE =>
                      Failed {rule = name, kind = SplitShape,
                              detail = Feedback.exn_to_string exn}))
    fun inspect_arith (index, theorem) =
      let
        val name = "arith_split#" ^ Int.toString index
      in
        ((linarithData.check_asm_split "audit" name theorem;
          Proved {rule = name, kind = SplitShape,
                  prover = "linarithData", elapsed = Time.zeroTime})
         handle Portable.Interrupt => raise Portable.Interrupt
              | exn =>
                  (case waiver_for name waivers of
                      SOME waiver =>
                        Waived {rule = name, kind = SplitShape,
                                waiver = waiver,
                                detail = Feedback.exn_to_string exn}
                    | NONE =>
                        Failed {rule = name, kind = SplitShape,
                                detail = Feedback.exn_to_string exn}))
      end
    val splits = map inspect_split (splitLib.named_split_thms ())
    val arith = Lib.mapi (fn i => fn theorem =>
      inspect_arith (i + 1,theorem)) (linarithData.arith_split_thms ())
  in
    splits @ arith
  end

fun result_rule result =
  case result of
      Proved {rule, ...} => rule
    | Waived {rule, ...} => rule
    | Failed {rule, ...} => rule

fun result_summary result =
  case result of
      Failed {rule, detail, ...} => rule ^ " (" ^ detail ^ ")"
    | _ => result_rule result

fun is_proved (Proved _) = true
  | is_proved _ = false

fun is_bad (Failed _) = true
  | is_bad _ = false

fun inspect {claset, budget, waivers} =
  let
    val _ = validate_waivers waivers
    val rules = clasetLib.all_rules claset
    fun inspect_one (rule as {name, ...} : clasetLib.aesop_rule) =
      (map (inspect_rule budget waivers rule) (obligations rule)
       handle Portable.Interrupt => raise Portable.Interrupt
            | exn =>
                (case waiver_for name waivers of
                    SOME waiver =>
                      [Waived {rule = name, kind = KernelPreservation,
                               waiver = waiver,
                               detail = "obligation synthesis: " ^
                                 Feedback.exn_to_string exn}]
                  | NONE =>
                      [Failed {rule = name, kind = KernelPreservation,
                               detail = "obligation synthesis: " ^
                                 Feedback.exn_to_string exn}]))
    val rule_results = List.concat (map inspect_one rules)
    val splits = split_results waivers
    val results = rule_results @ splits
    val used =
      List.filter
        (fn ({rule, ...} : waiver) =>
          List.exists
            (fn Waived {rule = used_rule, ...} => rule = used_rule
              | _ => false)
            results)
        waivers
    val stale =
      List.filter
        (fn waiver =>
          not
            (List.exists
              (fn used_waiver => #rule waiver = #rule used_waiver) used))
        waivers
    val stale_results =
      map
        (fn ({rule, ...} : waiver) =>
          Failed {rule = rule, kind = KernelPreservation,
                  detail = "stale waiver: rule passes or no longer exists"})
        stale
    val results = results @ stale_results
  in
    {checked = length results,
     proved = length (List.filter is_proved results),
     waivers = used,
     results = results,
     split_checked = length splits}
  end

fun failures ({results, ...} : report) = List.filter is_bad results

fun audit_with args =
  let
    val report = inspect args
    val bad = failures report
  in
    if null bad then report
    else
      raise ERR "audit_with"
        ("unwaivered or stale audit failures: " ^
         String.concatWith ", " (map result_summary bad))
  end

fun audit {waivers} =
  audit_with
    {claset = clasetLib.the_claset (), budget = default_budget,
     waivers = waivers}

end
