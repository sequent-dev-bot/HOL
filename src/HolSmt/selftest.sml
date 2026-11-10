(* Copyright (c) 2009-2012 Tjark Weber. All rights reserved. *)

(* HolSmtLib tests *)
open HolKernel Parse boolLib bossLib;

val _ =
  case Thm.getCT () of
    NONE => new_theory "scratch"
  | SOME _ => ()

val _ = print "Testing HolSmtLib\n"

(*****************************************************************************)
(* tracing/pretty-printing options useful for debugging                      *)
(*****************************************************************************)

(*
val _ = Globals.show_tags := true
val _ = Globals.show_assums := true
val _ = Globals.show_types := true
val _ = wordsLib.add_word_cast_printer ()
*)
val _ = Feedback.set_trace "PP.avoid_unicode" 1
val _ = Feedback.set_trace "HolSmtLib" 0
(*
val _ = Feedback.set_trace "HolSmtLib" 4
*)

(*****************************************************************************)
(* check whether SMT solvers are installed                                   *)
(*****************************************************************************)

val _ = if CVC.is_configured () then () else
  print "(cvc5 not configured, some tests will be skipped.)\n"

val _ = if Yices.is_configured () then () else
  print "(Yices not configured, some tests will be skipped.)\n"

val _ = if Z3.is_configured () then () else
  print "(Z3 not configured, some tests will be skipped.)\n"

(*****************************************************************************)
(* utility functions                                                         *)
(*****************************************************************************)

local

val die = Unittest.die

fun term_with_types t = Lib.with_flag(show_types, true) Hol_pp.term_to_string t

(* provable terms: theorem expected *)
fun expect_thm check_oracles name smt_tac t =
  let
    open boolLib
    val thm = Tactical.TAC_PROOF (([], t), smt_tac)
      handle Feedback.HOL_ERR holerr =>
         die ("Test of solver '" ^ name ^ "' failed on term '" ^
          term_with_types t ^ "': exception HOL_ERR (in " ^
          top_structure_of holerr ^ "." ^ top_function_of holerr ^
          " " ^ locn.toString (top_location_of holerr) ^
          ", message: " ^ message_of holerr ^ ")")
    val (oracles, _) = Tag.dest_tag (Thm.tag thm)
    val oracle_tags = List.filter (String.isPrefix "CPC_") oracles
  in
    if not (null oracle_tags) then
      die ("Test of solver '" ^ name ^ "' failed on term '" ^
        term_with_types t ^ "': proof replay produced oracle tag(s): " ^
        String.concatWith ", " oracle_tags)
    else if null (Thm.hyp thm) andalso Thm.concl thm ~~ t then ()
    else
      die ("Test of solver '" ^ name ^ "' failed on term '" ^
        term_with_types t ^ "': theorem differs (" ^
        Hol_pp.thm_to_string thm ^ ")");
    if check_oracles then
      Library.check_oracle_tags (Option.getOpt (Thm.getCT (), "-")) name thm
    else ()
  end

(* unprovable terms: satisfiability expected *)
fun expect_sat name smt_tac t =
  let
    (* Unfortunately, we need to disable `include_theorems` when expecting a
       `sat` answer. This is needed because certain theorems (such as
       `integerTheory.INT`) which we need to add to solve certain goals (e.g.
       those containing `num` terms) also completely prevent SMT solvers from
       finding a satisfiable model for unprovable goals. *)
    val () = SmtLib.include_theorems := false
    val _ = Tactical.TAC_PROOF (([], t), smt_tac)
  in
    die ("Test of solver '" ^ name ^ "' failed on term '" ^
      term_with_types t ^ "': exception expected")
  end handle Feedback.HOL_ERR holerr =>
    if top_structure_of holerr = "HolSmtLib" andalso
       (top_function_of holerr = "GENERIC_SMT_TAC" orelse
        top_function_of holerr = "ORACLE_SMT_TAC") andalso
       (message_of holerr = "solver reports negated term to be 'satisfiable'" orelse
        message_of holerr = "solver reports negated term to be 'satisfiable' (model returned)")
    then
      (* re-enable inclusion of theorems, i.e. restore the default setting *)
      SmtLib.include_theorems := true
    else
      die ("Test of solver '" ^ name ^ "' failed on term '" ^
        term_with_types t ^
        "': exception HOL_ERR has unexpected argument values (in " ^
        top_structure_of holerr ^ "." ^
        top_function_of holerr ^
        " " ^ locn.toString (top_location_of holerr) ^
        ", message: " ^ message_of holerr ^ ")")

fun mk_test_fun is_configured expect_fun name smt_tac =
  if is_configured then
    (fn g =>
      let
        val _ =
          if OS.Process.getEnv "HOL4_SELFTEST_PROGRESS" = SOME "1" then
            print ("\n" ^ name ^ ": " ^ term_with_types g ^ "\n")
          else
            ()
      in
        expect_fun name smt_tac g; print "."
      end)
  else
    Lib.K ()

(* This is intentionally a public translation-path check rather than a
   solver check: no SMT-LIB may be emitted for a residual smtfloat head. *)
fun reject_unsupported_smtfloat t =
  (ignore (SmtLib.goal_to_SmtLib_translation NONE ([], t));
   die ("unsupported smtfloat constant reached SMT-LIB emission"))
  handle Feedback.HOL_ERR holerr =>
    if Feedback.top_structure_of holerr = "SmtLib" andalso
       Feedback.top_function_of holerr = "translate_term" andalso
       String.isSubstring SmtLib.unsupported_smtfloat_constant_diagnostic
         (Feedback.message_of holerr)
    then print "."
    else
      die ("unsupported smtfloat constant raised the wrong diagnostic: " ^
        Feedback.exn_to_string (Feedback.HOL_ERR holerr))

(*****************************************************************************)
(* a built-in automated semi-decision procedure that *very* loosely          *)
(* resembles SMT solvers (in terms of coverage; not so much in terms of      *)
(* performance)                                                              *)
(*****************************************************************************)

fun auto_tac (_, t) (_ : Context.t) =
  let
    val simpset = bossLib.++ (bossLib.srw_ss (), wordsLib.WORD_ss)
    val simp_thms =
    let
      open arithmeticTheory integerTheory realTheory
    in
      [
        (* arithmeticTheory *)
        EXP, EXP_1, EXP_2,
        (* integerTheory *)
        EDIV_DEF, EMOD_DEF, INT_ABS, INT_MAX, INT_MIN, int_exp, int_quot,
        int_rem,
        (* realTheory *)
        EXP_2, POW_2, REAL_POW_LT,
        (* others *)
        boolTheory.LET_THM
      ]
    end
    val t_eq_t' =
      simpLib.SIMP_CONV simpset simp_thms t
      handle Conv.UNCHANGED =>
        Thm.REFL t
    val t' = boolSyntax.rhs (Thm.concl t_eq_t')
    fun quiet f x = Feedback.quiet_messages f x
    val t'_thm = quiet bossLib.DECIDE t'
      handle Feedback.HOL_ERR _ =>
        quiet (bossLib.METIS_PROVE []) t'
      handle Feedback.HOL_ERR _ =>
        quiet intLib.ARITH_PROVE t'
      handle Feedback.HOL_ERR _ =>
        quiet realLib.REAL_ARITH t'
      handle Feedback.HOL_ERR _ =>
        quiet wordsLib.WORD_DECIDE t'
      handle Feedback.HOL_ERR _ =>
        quiet Tactical.TAC_PROOF (([], t'), blastLib.BBLAST_TAC)
      handle Feedback.HOL_ERR _ =>
        Drule.EQT_ELIM (bossLib.EVAL t')
    val thm = Thm.EQ_MP (Thm.SYM t_eq_t') t'_thm
  in
    ([], fn _ => thm)
  end

val thm_AUTO =
  mk_test_fun true (expect_thm true) "AUTO"
    (Tactical.THEN (Library.SET_SIMP_TAC, auto_tac))

fun mk_CVC expect_fun =
  mk_test_fun (CVC.is_configured ()) expect_fun "cvc5" HolSmtLib.CVC_ORACLE_TAC

val thm_CVC = mk_CVC (expect_thm false)
val sat_CVC = mk_CVC expect_sat

fun mk_Yices expect_fun =
  mk_test_fun (Yices.is_configured ()) expect_fun "Yices"
    HolSmtLib.YICES_ORACLE_TAC

val thm_YO = mk_Yices (expect_thm false)
val sat_YO = mk_Yices expect_sat

fun mk_Z3 expect_fun =
  mk_test_fun (Z3.is_configured ()) expect_fun "Z3" HolSmtLib.Z3_ORACLE_TAC

val thm_Z3 = mk_Z3 (expect_thm false)
val sat_Z3 = mk_Z3 expect_sat

fun mk_Z3p expect_fun =
  mk_test_fun (Z3.is_configured ()) expect_fun "Z3 (proofs)" HolSmtLib.Z3_TAC

val thm_Z3p = mk_Z3p (expect_thm true)
val sat_Z3p = mk_Z3p expect_sat

fun mk_Z3_v4 expect_fun =
  mk_test_fun (Z3.is_v4_configured ()) expect_fun "Z3" HolSmtLib.Z3_ORACLE_TAC

val thm_Z3_v4 = mk_Z3_v4 (expect_thm false)
val sat_Z3_v4 = mk_Z3_v4 expect_sat

fun mk_Z3p_v4 expect_fun =
  mk_test_fun (Z3.is_v4_configured ()) expect_fun "Z3 (proofs)" HolSmtLib.Z3_TAC

val thm_Z3p_v4 = mk_Z3p_v4 (expect_thm true)
val sat_Z3p_v4 = mk_Z3p_v4 expect_sat

(* Z3 4.12--4.15 report "proof is not available" on the proof-enabled
   command for the genuine satisfiable HO witness below.  Z3 4.11 returns
   SAT, so retain that boundary check without treating later versions'
   missing proof response as a reconstruction failure. *)
fun is_z3_411 () =
  Z3.is_configured () andalso
  String.isPrefix "4.11." Z3.Z3version

val sat_Z3p_v411 =
  mk_test_fun (is_z3_411 ()) expect_sat
    "Z3 (proofs, 4.11)" HolSmtLib.Z3_TAC

fun mk_CVCp expect_fun =
  mk_test_fun (CVC.is_configured ())
    (fn name => fn tac => fn goal =>
      (* cvc5 CPC proofs for numeric and word goals are routinely much larger
         than corresponding checked Z3 proofs and can spend minutes in
         Poly/ML's replay engine.  CVC oracle rows still cover those goals;
         retain checked CVC coverage for the remaining fragments. *)
      if List.exists (fn variable =>
          let val ty = Term.type_of variable in
            Type.compare (ty, intSyntax.int_ty) = EQUAL orelse
            Type.compare (ty, realSyntax.real_ty) = EQUAL orelse
            Type.compare (ty, numSyntax.num) = EQUAL orelse
            Lib.can wordsSyntax.dest_word_type ty
          end) (Term.free_vars goal) orelse
         Lib.can (HolKernel.find_term
          (fn tm =>
            let val ty = Term.type_of tm in
              Library.type_contains_word ty orelse
              Library.type_contains_int ty orelse
              Library.type_contains_real ty orelse
              Library.type_contains
                (fn candidate =>
                  Type.compare (candidate, numSyntax.num) = EQUAL) ty
            end)) goal then ()
      else expect_fun name tac goal)
    "cvc5 (proofs)" HolSmtLib.CVC_TAC

val thm_CVCp = mk_CVCp (expect_thm true)

(* These small higher-order regressions need checked replay even though
   their function domains contain integers. *)
val thm_CVCp_ho =
  mk_test_fun (CVC.is_configured ()) (expect_thm true)
    "cvc5 (higher-order proofs)"
    (REPEAT STRIP_TAC THEN HolSmtLib.CVC_TAC)
val sat_CVCp = mk_CVCp expect_sat

(*****************************************************************************)
(* HOL definitions (e.g., user-defined data types)                           *)
(*****************************************************************************)

val _ = bossLib.Hol_datatype `dt1 = foo | bar | baz`

val _ = bossLib.Hol_datatype `dirn = NS | EW`

val flc_def = Define `flc d = case d of NS => EW | EW => NS`

fun expect_flc_checked name solver goal =
  let
    val solver_calls = ref 0
    fun counted_solver subgoal =
      (solver_calls := !solver_calls + 1; solver subgoal)
    val tactic = Tactical.THEN
      (Rewrite.PURE_REWRITE_TAC [flc_def], counted_solver)
    val _ = expect_thm true name tactic goal
  in
    if !solver_calls = 1 then ()
    else die (name ^ " did not receive the unfolded flc goal exactly once")
  end

val thm_flc_Z3p =
  mk_test_fun (Z3.is_v4_configured ()) expect_flc_checked
    "Z3 (proofs)" HolSmtLib.Z3_TAC

val thm_flc_CVCp =
  mk_test_fun (CVC.is_configured ()) expect_flc_checked
    "cvc5 (proofs)" HolSmtLib.CVC_TAC

val _ = bossLib.Hol_datatype `person = <| employed :bool; age :num |>`

val _ = bossLib.Hol_datatype `
  dt_tree = dtLeaf | dtNode of dt_forest ;
  dt_forest = dtNilF | dtConsF of dt_tree => dt_forest`

in

(*****************************************************************************)
(* test cases                                                                *)
(*****************************************************************************)

  val tests = [

    (* propositional logic *)
    (``T``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (* Seq/Set/Bag checked-replay smoke tests.  `bool` has finite carrier,
       so the cvc5 rows exercise its native finite Set/Bag guard.  The MAP
       row is deliberately Z3-only: seq.map is unavailable in cvc5. *)
    (``LENGTH ((xs : int list) ++ ys) = LENGTH xs + LENGTH ys``,
      [thm_Z3p_v4, thm_CVCp]),
    (``MAP (\x : int. x + 1) ((xs : int list) ++ ys) =
        MAP (\x. x + 1) xs ++ MAP (\x. x + 1) ys``, [thm_Z3p_v4]),
    (* Set preprocessing smoke tests.  Native and fallback translation and
       CPC replay have dedicated coverage in Unittest. *)
    (``(x : bool) IN (s UNION t) <=> x IN (t UNION s)``,
      [thm_Z3p_v4, thm_CVCp]),
    (``(x : int) IN (s UNION t) <=> x IN s \/ x IN t``,
      [thm_CVC, thm_CVCp]),
    (* Z3 proves this through an array lemma outside its checked Bag replay
       ladder; cvc5 supplies the native checked Bag certificate. *)
    (``BAG_IN (x : bool) (BAG_INSERT y EMPTY_BAG) <=> x = y``, [thm_CVCp]),
    (* Sets in cvc5's array encoding: a singleton, an applied set and an
       applied bound set must all stay Arrays, in the assumptions too. *)
    (``(x : num) = y /\ P {x} ==> (P : (num -> bool) -> bool) {y}``,
      [thm_CVC, thm_CVCp_ho]),
    (``(a : num) IN s ==> s a``, [thm_CVC, thm_CVCp_ho]),
    (``(!x : num. x IN s ==> x IN t) /\ s b ==> t b``, [thm_CVC, thm_CVCp_ho]),
    (``(a : num) IN (if c then s else t) /\ c ==> a IN s``, [thm_CVC]),
    (* A record selector and EMPTY must share the conditional's Array sort;
       checked replay reconstructs the normalized selector under the UF. *)
    (``(r : smt_set_rec) = q /\
       P (if p then r.smt_set else {}) ==>
       (P : (int -> bool) -> bool) (if p then q.smt_set else {})``,
      [thm_CVC, thm_CVCp_ho]),

    (* Shared set arguments mark UPDATE as an Array.  Set equality keeps
       that marker in checked mode; membership is expanded there. *)
    (``f (s:bool set) /\ T IN s /\ f (\x:bool. x) ==>
       f ((T =+ T) s)``, [thm_CVC]),
    (``(s:bool set) = t /\ f s /\ f (\x:bool. x) /\
       f ((T =+ T) s) ==> f ((T =+ T) t)``, [thm_CVC, thm_CVCp_ho]),

    (``F``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``p = (p:bool)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``p ==> p``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``p \/ ~ p``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``p /\ q ==> q /\ p``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(p ==> q) /\ (q ==> p) ==> (p = q)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(p ==> q) /\ (q ==> p) <=> (p = q)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``p \/ q ==> p /\ q``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``if p then (q ==> p) else (p ==> q)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``case p of T => p | F => ~ p``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``case p of T => (q ==> p) | F => (p ==> q)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (* Native HOL strings are proved through the smtstring injection.  The
       oracle path only: Z3 discharges the injected goals with seq
       th-lemmas over the str_inj image and cvc5 with the trust and
       str-substr-full-eq CPC rules, none of which replay.  The checked
       tactics are covered by the ground smtstr goals below. *)
    (``STRCAT (STRCAT (s:string) t) u = STRCAT s (STRCAT t u)``,
      [thm_Z3]),
    (``isPREFIX (s:string) s``, [thm_Z3]),
    (``~((s:string) < s)``, [thm_Z3]),
    (``(s:string) <= s``, [thm_Z3]),

    (* Native SMT-LIB Unicode strings exercise checked Z3 replay end to end. *)
    (``smtstring$smtstr_len
         (smtstring$smtstr_concat
            (smtstring$SmtStr [97]) (smtstring$SmtStr [98])) =
       smtstring$smtstr_len (smtstring$SmtStr [97]) +
       smtstring$smtstr_len (smtstring$SmtStr [98])``,
      [thm_Z3p_v4, thm_CVCp]),
    (``smtstring$smtstr_prefixof (smtstring$SmtStr [97])
         (smtstring$smtstr_concat
            (smtstring$SmtStr [97]) (smtstring$SmtStr [98]))``,
      [thm_Z3p_v4, thm_CVCp]),
    (``smtstring$smt_in_re (smtstring$SmtStr [97])
       (smtstring$reglan_to_re (smtstring$SmtStr [97]))``,
      [thm_Z3p_v4, thm_CVCp]),
    (``smtstring$smtstr_to_int (smtstring$SmtStr [49; 50]) = 12``,
      [thm_Z3p_v4]),
    (``smtstring$smtstr_lt
         (smtstring$SmtStr [97; 98]) (smtstring$SmtStr [97; 99])``,
      [thm_Z3p_v4, thm_CVCp]),

    (* numerals *)

    (* FIXME: SMT-LIB 2 does not provide a theory of natural numbers, but only
              integers and reals.  We should add support for naturals (via an
              embedding into integers), but for now, they are treated as
              uninterpreted. *)

    (* num *)

    (``0n = 0n``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``1n = 1n``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``0n = 1n``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``42n = 42n``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (* int *)

    (``0i = 0i``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``1i = 1i``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``0i = 1i``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``42i = 42i``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``0i = ~0i``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``~0i = 0i``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``~0i = ~0i``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``~42i = ~42i``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (* Live D3 regression: checked Z3 must replay the full quant-intro chain
       through relation complementation, ite polarity, and additive order. *)
    (``(!a:int. f a = if a < 30 then p (a + 1) else q a) =
       (!a. f a = if 30 <= a then q a else p (1 + a))``,
      [thm_Z3p_v4]),

    (* real *)

    (``0r = 0r``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``1r = 1r``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``0r = 1r``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``42r = 42r``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``0r = ~0r``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``~0r = 0r``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``~0r = ~0r``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``~42r = ~42r``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``~42r = 42r``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``42r = ~42r``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),

    (* arithmetic operators: SUC, +, -, *, /, DIV, MOD, ABS, MIN, MAX *)

    (* num *)

    (``SUC 0 = 1``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``SUC x = x + 1``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``x < SUC x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(SUC x = SUC y) = (x = y)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``SUC (x + y) = (SUC x + SUC y)``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),

    (``(x:num) + 0 = x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``0 + (x:num) = x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:num) + y = y + x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:num) + (y + z) = (x + y) + z``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``((x:num) + y = 0) <=> (x = 0) /\ (y = 0)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),

    (* Completeness guards for the proved num-to-int transfer.  These checked
       Z3 rows use genuine free num variables that previously depended on the
       retired num bridge axioms. *)
    (``(v:num) <= v + 1``, [thm_Z3p, thm_CVC, thm_CVCp]),
    (``!n:num. v <= n + v``, [thm_Z3p, thm_CVC, thm_CVCp]),
    (``(v:num) - (w + 1) <= v``, [thm_Z3p, thm_CVC, thm_CVCp]),

    (``(x:num) - 0 = x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:num) - y = y - x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:num) - y - z = x - (y + z)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:num) <= y ==> (x - y = 0)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4]),
    (``((x:num) - y = 0) \/ (y - x = 0)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4]),

    (* thm_CVCp omitted: CPC parsing fails on
       ``(x:num) <= y ==> (x - y = 0)`` and
       ``((x:num) - y = 0) \/ (y - x = 0)`` (unknown arith-max-geq2). *)

    (``(x:num) * 0 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``0 * (x:num) = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:num) * 1 = x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``1 * (x:num) = x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:num) * 42 = 42 * x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),

    (* thm_CVCp omitted: bounded checked replay times out on
       ``(0:num) DIV 1 = 0`` and ``(0:num) DIV 42 = 0``. *)
    (``(0:num) DIV 1 = 0``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p]),
    (``(1:num) DIV 1 = 1``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(42:num) DIV 1 = 42``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(0:num) DIV 42 = 0``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p]),
    (``(1:num) DIV 42 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(42:num) DIV 42 = 1``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``((v:num) = v DIV 1 * 1 + v MOD 1) /\ v MOD 1 < 1``,
      [thm_Z3p, thm_CVC, thm_CVCp]),
    (``(x:num) DIV 1 = x``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVC, thm_CVCp]),
    (``(x:num) DIV 42 <= x``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVC, thm_CVCp]),
    (``((x:num) DIV 42 = x) = (x = 0)``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVC, thm_CVCp]),
    (``(x:num) DIV 0 = x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:num) DIV 0 = 0``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(0:num) DIV 0 = 0``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(0:num) DIV 0 = 1``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:num) DIV 0 = x DIV 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``(0:num) MOD 1 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(1:num) MOD 1 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(42:num) MOD 1 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(0:num) MOD 42 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(1:num) MOD 42 = 1``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(42:num) MOD 42 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:num) MOD 1 = 0``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVC, thm_CVCp]),
    (``(x:num) MOD 42 < 42``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVC, thm_CVCp]),
    (``((x:num) MOD 42 = x) = (x < 42)``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVC, thm_CVCp]),
    (``(x:num) MOD 0 = x``, [thm_AUTO, thm_Z3, thm_Z3p_v4, thm_CVC, thm_CVCp]),
    (``(x:num) MOD 0 = 0``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(0:num) MOD 0 = 0``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(0:num) MOD 0 = 1``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:num) MOD 0 = x MOD 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (* cf. arithmeticTheory.DIVISION *)
    (``((x:num) = x DIV 1 * 1 + x MOD 1) /\ x MOD 1 < 1``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``((x:num) = x DIV 42 * 42 + x MOD 42) /\ x MOD 42 < 42``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),

    (``(x:num) ** 0 = 1``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:num) ** 0 = 0``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:num) ** 1 = x``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(0:num) ** 1 = 1``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(1:num) ** x = 1``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(1:num) ** x = 0``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:num) ** 2 = x * x``,
      [thm_AUTO, thm_Z3, thm_Z3p_v4, thm_CVC, thm_CVCp]),
    (``(x:num) ** 2 = 2``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:num) ** 3 = x * x * x``, [(*thm_AUTO, thm_CVC, thm_Z3, thm_Z3p*)]),
    (``(x:num) ** 3 = 4``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``0 < (x:num) ** y``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``0 <= (x:num) ** y``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``0 < (1:num) ** y``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``0 < (2:num) ** y``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``0 < (42:num) ** y``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),

    (``MIN (x:num) y <= x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``MIN (x:num) y <= y``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(z:num) < x /\ z < y ==> z < MIN x y``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4]),
    (``MIN (x:num) y < x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``MIN (x:num) 0 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``MIN (x:num) y = a ==> MIN a z <= x``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_CVCp
       (*, thm_Z3p_v4: Z3 4.11 proof replay can leave ite-expansion
          definition hypotheses after the num-to-int MIN lowering. *)
       ]),

    (``MAX (x:num) y >= x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``MAX (x:num) y >= y``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(z:num) > x /\ z > y ==> z > MAX x y``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``MAX (x:num) y > x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``MAX (x:num) 0 = x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``MAX (x:num) y = a ==> x <= MAX a z``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_CVCp
       (*, thm_Z3p_v4: Z3 4.11 proof replay can leave ite-expansion
          definition hypotheses after the num-to-int MAX lowering. *)
       ]),

    (* int *)

    (``(x:int) + 0 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``0 + (x:int) = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:int) + y = y + x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:int) + (y + z) = (x + y) + z``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:int) + y = 0 <=> x = 0 /\ y = 0``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``((x:int) + y = 0) = (x = ~y)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``(x:int) - 0 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:int) - y = y - x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:int) - y - z = x - (y + z)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:int) <= y ==> (x - y = 0)``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``((x:int) - y = 0) \/ (y - x = 0)``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:int) - y = x + ~y``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``(x:int) * 0 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``0 * (x:int) = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:int) * 1 = x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``1 * (x:int) = x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:int) * ~1 = ~x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``~1 * (x:int) = ~x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:int) * 42 = 42 * x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (* Direct checked-proof coverage for totalized division and modulus. *)
    (``(x:int) >= 0 ==> x / 2 <= x``,
      [thm_CVC, thm_CVCp, thm_Z3, thm_Z3p]),
    (``(x:int) % 2 < 2``,
      [thm_CVC, thm_CVCp, thm_Z3, thm_Z3p]),
    (``(y:int) <> 0 ==>
       ediv 0 y = 0``,
      [thm_CVC, thm_CVCp, thm_Z3, thm_Z3p]),
    (``(y:int) <> 0 ==>
       emod 0 y = 0``,
      [thm_CVC, thm_CVCp, thm_Z3, thm_Z3p]),
    (``(y:real) <> 0 ==> ((x:real) / y) * y = x``,
      [thm_CVC, thm_CVCp, thm_Z3, thm_Z3p]),
    (``ediv (~7) (~2) = (4:int)``,
      [thm_CVC, thm_CVCp, thm_Z3, thm_Z3p]),
    (``emod (~7) (~2) = (1:int)``,
      [thm_CVC, thm_CVCp, thm_Z3, thm_Z3p]),

    (* thm_CVCp omitted after bounded probes:
       timeouts on ``(0:int) / ~42 = 0``, ``(0:int) / ~1 = 0``,
       ``(0:int) / 1 = 0``, and ``(0:int) / 42 = 0``;
       CPC replay failures on ``(1:int) / ~1 = ~1`` and
       ``(~1:int) / 42 = ~1``. *)
    (``(~42:int) / ~42 = 1``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~1:int) / ~42 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(0:int) / ~42 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4]),
    (``(1:int) / ~42 = ~1``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(42:int) / ~42 = ~1``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~42:int) / ~1 = 42``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~1:int) / ~1 = 1``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(0:int) / ~1 = 0``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4]),
    (``(1:int) / ~1 = ~1``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4]),
    (``(42:int) / ~1 = ~42``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~42:int) / 1 = ~42``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~1:int) / 1 = ~1``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(0:int) / 1 = 0``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4]),
    (``(1:int) / 1 = 1``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(42:int) / 1 = 42``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~42:int) / 42 = ~1``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~1:int) / 42 = ~1``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4]),
    (``(0:int) / 42 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4]),
    (``(1:int) / 42 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(42:int) / 42 = 1``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:int) / 1 = x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:int) / ~1 = ~x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:int) / 42 <= x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:int) / 42 <= ABS x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3_v4, thm_Z3p_v4, thm_CVCp]),
    (``((x:int) / 42 = x) = (x = 0)``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:int) / 42 = x <=> x = 0 \/ x = ~1``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:int) / 0 = x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:int) / 0 = 0``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(0:int) / 0 = 0``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(0:int) / 0 = 1``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(0:int) / 0 = 1 / 0``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:int) / 0 = x / 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (* cf. integerTheory.int_div; checked replay is omitted because the
       bounded Z3/CVC replay spends minutes on the 42-denominator clauses:
       ``(x:int) < 0 ==>
         (x / 42 = ~(~x / 42) + if ~x % 42 = 0 then 0 else ~1)`` and
       ``0 <= (x:int) ==>
         (x / ~42 = ~(x / 42) + if x % 42 = 0 then 0 else ~1)``.
       The oracle rows above still cover the same arithmetic path. *)
    (``(x:int) < 0 ==> (x / 1 = ~(~x / 1) + if ~x % 1 = 0 then 0 else ~1)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:int) < 0 ==> (x / 42 = ~(~x / 42) + if ~x % 42 = 0 then 0 else ~1)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3]),
    (``0 <= (x:int) ==> (x / ~42 = ~(x / 42) + if x % 42 = 0 then 0 else ~1)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3]),
    (``0 <= (x:int) ==> (x / ~1 = ~(x / 1) + if x % 1 = 0 then 0 else ~1)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:int) < 0 ==> (x / ~42 = ~x / 42)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:int) < 0 ==> (x / ~1 = ~x / 1)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),

    (* thm_CVCp omitted after bounded probes:
       timeouts on ``(0:int) quot ~42 = 0``,
       ``(0:int) quot ~1 = 0``, ``(0:int) quot 1 = 0``, and
       ``(0:int) quot 42 = 0``; CPC replay failures on
       ``(1:int) quot ~1 = ~1``, ``(x:int) quot 1 = x``, and
       ``(x:int) quot ~1 = ~x``. *)
    (``(~42:int) quot ~42 = 1``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~1:int) quot ~42 = 0``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(0:int) quot ~42 = 0``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),
    (``(1:int) quot ~42 = 0``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(42:int) quot ~42 = ~1``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~42:int) quot ~1 = 42``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~1:int) quot ~1 = 1``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(0:int) quot ~1 = 0``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),
    (``(1:int) quot ~1 = ~1``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),
    (``(42:int) quot ~1 = ~42``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~42:int) quot 1 = ~42``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~1:int) quot 1 = ~1``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(0:int) quot 1 = 0``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),
    (``(1:int) quot 1 = 1``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(42:int) quot 1 = 42``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~42:int) quot 42 = ~1``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~1:int) quot 42 = 0``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(0:int) quot 42 = 0``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),
    (``(1:int) quot 42 = 0``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(42:int) quot 42 = 1``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:int) quot 1 = x``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),
    (``(x:int) quot ~1 = ~x``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),
    (``(x:int) quot 42 <= x``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:int) quot 42 <= ABS x``,
      [thm_AUTO, thm_CVC, thm_Z3_v4, thm_Z3p_v4, thm_CVCp]),
    (``((x:int) quot 42 = x) = (x = 0)``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:int) quot 42 = x <=> x = 0 \/ x = ~1``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:int) quot 0 = x``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:int) quot 0 = 0``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(0:int) quot 0 = 0``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(0:int) quot 0 = 1``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(0:int) quot 0 = 1 quot 0``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:int) quot 0 = x quot 0``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p, thm_CVCp]),

    (* cf. integerTheory.int_quot; thm_CVCp omitted after CPC failures on
       ``(x:int) < 0 ==> (x quot 1 = ~(~x quot 1))``,
       ``0 <= (x:int) ==> (x quot ~1 = ~(x quot 1))``, and
       ``(x:int) < 0 ==> (x quot ~1 = ~x quot 1)``. *)
    (``(x:int) < 0 ==> (x quot 1 = ~(~x quot 1))``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),
    (``(x:int) < 0 ==> (x quot 42 = ~(~x quot 42))``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``0 <= (x:int) ==> (x quot ~42 = ~(x quot 42))``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``0 <= (x:int) ==> (x quot ~1 = ~(x quot 1))``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),
    (``(x:int) < 0 ==> (x quot ~42 = ~x quot 42)``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:int) < 0 ==> (x quot ~1 = ~x quot 1)``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),

    (* thm_CVCp omitted after CPC replay failures on
       ``(~1:int) % ~42 = ~1``, ``(0:int) % ~42 = 0``,
       ``(0:int) % ~1 = 0``, ``(0:int) % 1 = 0``,
       ``(0:int) % 42 = 0``, and ``(1:int) % 42 = 1``. *)
    (``(~42:int) % ~42 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~1:int) % ~42 = ~1``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4]),
    (``(0:int) % ~42 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4]),
    (``(1:int) % ~42 = ~41``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(42:int) % ~42 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~42:int) % ~1 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~1:int) % ~1 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(0:int) % ~1 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4]),
    (``(1:int) % ~1 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(42:int) % ~1 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~42:int) % 1 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~1:int) % 1 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(0:int) % 1 = 0``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4]),
    (``(1:int) % 1 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(42:int) % 1 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~42:int) % 42 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~1:int) % 42 = 41``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(0:int) % 42 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4]),
    (``(1:int) % 42 = 1``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4]),
    (``(42:int) % 42 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:int) % 1 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:int) % ~1 = 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:int) % 42 < 42``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``((x:int) % 42 = x) = (x < 42)``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``((x:int) % 42 = x) <=> (0 <= x) /\ (x < 42)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:int) % 0 = x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:int) % 0 = 0``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(0:int) % 0 = 0``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(0:int) % 0 = 1``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:int) % 0 = x % 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (* cf. integerTheory.int_mod *)
    (``(x:int) % ~42 = x - x / ~42 * ~42``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:int) % ~1 = x - x / ~1 * ~1``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:int) % 1 = x - x / 1 * 1``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:int) % 42 = x - x / 42 * 42``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),

    (* thm_CVCp omitted after CPC replay failures on
       ``(~1:int) rem ~42 = ~1``, ``(0:int) rem ~42 = 0``,
       ``(1:int) rem ~42 = 1``, ``(0:int) rem ~1 = 0``,
       ``(0:int) rem 1 = 0``, ``(~1:int) rem 42 = ~1``,
       ``(0:int) rem 42 = 0``, ``(1:int) rem 42 = 1``,
       ``(x:int) rem 1 = 0``, ``(x:int) rem ~1 = 0``,
       ``(x:int) rem 42 < 42``, and
       ``((x:int) rem 42 = x) <=> (-42 < x) /\ (x < 42)``. *)
    (``(~42:int) rem ~42 = 0``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~1:int) rem ~42 = ~1``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),
    (``(0:int) rem ~42 = 0``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),
    (``(1:int) rem ~42 = 1``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),
    (``(42:int) rem ~42 = 0``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~42:int) rem ~1 = 0``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~1:int) rem ~1 = 0``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(0:int) rem ~1 = 0``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),
    (``(1:int) rem ~1 = 0``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(42:int) rem ~1 = 0``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~42:int) rem 1 = 0``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~1:int) rem 1 = 0``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(0:int) rem 1 = 0``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),
    (``(1:int) rem 1 = 0``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(42:int) rem 1 = 0``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~42:int) rem 42 = 0``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~1:int) rem 42 = ~1``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),
    (``(0:int) rem 42 = 0``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),
    (``(1:int) rem 42 = 1``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),
    (``(42:int) rem 42 = 0``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:int) rem 1 = 0``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),
    (``(x:int) rem ~1 = 0``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),
    (``(x:int) rem 42 < 42``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),
    (``((x:int) rem 42 = x) = (x < 42)``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``((x:int) rem 42 = x) <=> (0 <= x) /\ (x < 42)``,
      [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``((x:int) rem 42 = x) <=> (-42 < x) /\ (x < 42)``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),
    (``(x:int) rem 0 = x``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:int) rem 0 = 0``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(0:int) rem 0 = 0``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(0:int) rem 0 = 1``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:int) rem 0 = x rem 0``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p, thm_CVCp]),

    (* cf. integerTheory.int_rem; thm_CVCp omitted after CPC failures on
       ``(x:int) rem ~42 = x - x quot ~42 * ~42``,
       ``(x:int) rem ~1 = x - x quot ~1 * ~1``,
       ``(x:int) rem 1 = x - x quot 1 * 1``, and
       ``(x:int) rem 42 = x - x quot 42 * 42``. *)
    (``(x:int) rem ~42 = x - x quot ~42 * ~42``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),
    (``(x:int) rem ~1 = x - x quot ~1 * ~1``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),
    (``(x:int) rem 1 = x - x quot 1 * 1``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),
    (``(x:int) rem 42 = x - x quot 42 * 42``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4]),

    (``(x:int) ** 0 = 1``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:int) ** 0 = 0``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:int) ** 1 = x``,
      [(*thm_AUTO,*) thm_Z3(*, thm_Z3p*), thm_CVC, thm_CVCp]),
    (``(0:int) ** 1 = 1``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(1:int) ** x = 1``,
      [thm_AUTO, thm_CVC, thm_CVCp (*, thm_Z3, thm_Z3p*)]),
    (``(1:int) ** x = 0``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(-1:int) ** 1 = -1``,
      [thm_AUTO, thm_Z3, thm_Z3p_v4, thm_CVC, thm_CVCp]),
    (``(-1:int) ** 2 = 1``,
      [thm_AUTO, thm_Z3, thm_Z3p_v4, thm_CVC, thm_CVCp]),
    (``(-3:int) ** 1 = -3``,
      [thm_AUTO, thm_Z3, thm_Z3p_v4, thm_CVC, thm_CVCp]),
    (``(-3:int) ** 2 = 9``,
      [thm_AUTO, thm_Z3, thm_Z3p_v4, thm_CVC, thm_CVCp]),
    (``(x:int) ** 2 = x * x``,
      [(*thm_AUTO,*) thm_Z3(*, thm_Z3p*), thm_CVC, thm_CVCp]),
    (``(x:int) ** 2 = 2``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:int) ** 3 = x * x * x``,
      [(*thm_AUTO,*) thm_Z3(*, thm_Z3p*), thm_CVC, thm_CVCp]),
    (``(x:int) ** 3 = 4``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``0 < (x:int) ** y``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``0 <= (x:int) ** y``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``0 < (1:int) ** y``,
      [thm_AUTO, thm_CVC, thm_CVCp (*, thm_Z3, thm_Z3p*)]),
    (* thm_CVCp omitted after CPC failures on ``0 < (2:int) ** y`` and
       ``0 < (42:int) ** y``. *)
    (``0 < (2:int) ** y``, [thm_AUTO(*, thm_CVC, thm_Z3, thm_Z3p*)]),
    (``0 < (-2:int) ** y``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``0 < (42:int) ** y``, [thm_AUTO(*, thm_CVC, thm_Z3, thm_Z3p*)]),
    (``0 < (-42:int) ** y``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),

    (``ABS (x:int) >= 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3_v4, thm_Z3p_v4, thm_CVCp]),
    (``(ABS (x:int) = 0) = (x = 0)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3_v4, thm_Z3p_v4, thm_CVCp]),
    (``(x:int) >= 0 ==> (ABS x = x)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3_v4, thm_Z3p_v4, thm_CVCp]),
    (``(x:int) <= 0 ==> (ABS x = ~x)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3_v4, thm_Z3p_v4, thm_CVCp]),
    (``ABS (ABS (x:int)) = ABS x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3_v4, thm_Z3p_v4, thm_CVCp]),
    (``ABS (x:int) = x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),

    (``int_min (x:int) y <= x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``int_min (x:int) y <= y``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(z:int) < x /\ z < y ==> z < int_min x y``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``int_min (x:int) y < x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``int_min (x:int) 0 = 0``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:int) >= 0 ==> (int_min x 0 = 0)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``int_min (x:int) y = a ==> int_min a z <= x``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp
       ]),

    (``int_max (x:int) y >= x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``int_max (x:int) y >= y``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(z:int) > x /\ z > y ==> z > int_max x y``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``int_max (x:int) y > x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:int) >= 0 ==> (int_max x 0 = x)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``int_max (x:int) y = a ==> x <= int_max a z``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),

    (* arithmetic goals with disjunctive hypotheses: the num-to-int transfer
       must not case-split them (SolverSpec.simplify accepts at most one
       subgoal) *)
    (``(x:int) + 2 <= y \/ y + 3 <= x ==> x <> y``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p, thm_CVCp]),
    (``0 <= (t1:int) /\ 0 <= t2 /\ 0 <= t3 /\
       (t1 + 2 <= t2 \/ t2 + 3 <= t1) /\
       (t1 + 2 <= t3 \/ t3 + 2 <= t1) /\
       (t2 + 3 <= t3 \/ t3 + 2 <= t2) ==>
       7 <= t1 + 2 \/ 7 <= t2 + 3 \/ 7 <= t3 + 2``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p, thm_CVCp]),

    (* real *)

    (``(x:real) + 0 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``0 + (x:real) = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:real) + y = y + x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:real) + (y + z) = (x + y) + z``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:real) + y = 0 <=> x = 0 /\ y = 0``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``((x:real) + y = 0) = (x = ~y)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``(x:real) - 0 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:real) - y = y - x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:real) - y - z = x - (y + z)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:real) <= y ==> (x - y = 0)``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``((x:real) - y = 0) \/ (y - x = 0)``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:real) - y = x + ~y``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``(x:real) * 0 = 0``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``0 * (x:real) = 0``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:real) * 1 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``1 * (x:real) = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:real) * 42 = 42 * x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``(~42:real) / ~42 = 1``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~1:real) / ~42 = 0``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(0:real) / ~42 = 0``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(1:real) / ~42 = ~1``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(42:real) / ~42 = ~1``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~42:real) / ~1 = 42``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~1:real) / ~1 = 1``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(0:real) / ~1 = 0``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(1:real) / ~1 = ~1``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(42:real) / ~1 = ~42``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~42:real) / 1 = ~42``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~1:real) / 1 = ~1``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(0:real) / 1 = 0``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(1:real) / 1 = 1``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(42:real) / 1 = 42``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~42:real) / 42 = ~1``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(~1:real) / 42 = ~1``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(0:real) / 42 = 0``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(1:real) / 42 = 0``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(42:real) / 42 = 1``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:real) / 1 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:real) / ~1 = ~x``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:real) / 42 <= x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:real) / 42 <= abs x``,
      [thm_AUTO, thm_CVC, thm_Z3_v4, thm_Z3p_v4, thm_CVCp]),

    (``((x:real) / 42 = x) = (x = 0)``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:real) / 0 = x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:real) / 0 = 0``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(0:real) / 0 = 0``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(0:real) / 0 = 1``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(0:real) / 0 = 1 / 0``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:real) / 0 = x / 0``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``x > 0 ==> (x:real) / 42 < x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``x < 0 ==> (x:real) / 42 > x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),

    (``realinv 0 = 0``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``realinv 1 = 1``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``realinv (-1) = -1``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``realinv 42 = 1 / 42``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``realinv (-42) = -1 / 42``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (* cvc5: realinv is uninterpreted, returns wrong model *)
    (``realinv (1 / 42) = 42``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4 (*, thm_CVCp *)]),
    (``realinv (-1 / 42) = -42``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4 (*, thm_CVCp *)]),
    (``realinv x = 1 / x``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``realinv (-x) = -1 / x``, [(*thm_AUTO,*) thm_CVC, thm_Z3(*, thm_Z3p_v4*)]),
    (``realinv (1 / x) = x``, [(*thm_AUTO,*) thm_CVC, thm_Z3(*, thm_Z3p_v4*)]),
    (``realinv (abs x) = 1 / (abs x)``, [thm_AUTO, thm_CVC, thm_Z3(*, thm_Z3p_v4*)]),
    (``realinv (abs x) = abs (1 / x)``, [(*thm_AUTO,*) thm_CVC, thm_Z3(*, thm_Z3p_v4*)]),

    (``(x:real) pow 0 = 1``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:real) pow 0 = 0``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:real) pow 1 = x``, [thm_AUTO, (*thm_CVC,*) thm_Z3, thm_Z3p_v4 (*, thm_CVCp *)]),
    (``(0:real) pow 1 = 1``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(1:real) pow x = 1``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(1:real) pow x = 0``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(-1:real) pow 1 = -1``, [thm_AUTO, (*thm_CVC,*) thm_Z3, thm_Z3p_v4 (*, thm_CVCp *)]),
    (``(-1:real) pow 2 = 1``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(-3:real) pow 1 = -3``, [thm_AUTO, (*thm_CVC,*) thm_Z3, thm_Z3p_v4 (*, thm_CVCp *)]),
    (``(-3:real) pow 2 = 9``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:real) pow 2 = x * x``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:real) pow 3 = x * x * x``,
      [thm_AUTO, (*thm_CVC,*) thm_Z3_v4, thm_Z3p_v4 (*, thm_CVCp *)]),
    (``0 < (x:real) pow y``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``0 <= (x:real) pow y``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``0 < (1:real) pow y``, [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``0 < (2:real) pow y``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``0 < (-2:real) pow y``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),
    (``0 < (42:real) pow y``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``0 < (-42:real) pow y``, [sat_CVC, sat_Z3, sat_Z3p, sat_CVCp]),

    (``abs (x:real) >= 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(abs (x:real) = 0) = (x = 0)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:real) >= 0 ==> (abs x = x)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:real) <= 0 ==> (abs x = ~x)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``abs (abs (x:real)) = abs x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``abs (x:real) = x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),

    (``min (x:real) y <= x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``min (x:real) y <= y``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(z:real) < x /\ z < y ==> z < min x y``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``min (x:real) y < x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``min (x:real) 0 = 0``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:real) >= 0 ==> (min x 0 = 0)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``min (x:real) y = a ==> min a z <= x``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),

    (``max (x:real) y >= x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``max (x:real) y >= y``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(z:real) > x /\ z > y ==> z > max x y``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``max (x:real) y > x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:real) >= 0 ==> (max x 0 = x)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``max (x:real) y = a ==> x <= max a z``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp
       ]),

    (* nonlinear arithmetic *)

    (* NIA: product of nonneg *)
    (``(x:int) >= 0 /\ (y:int) >= 0 ==> x * y >= 0``,
      [thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (* NIA: square nonneg *)
    (``(x:int) * x >= 0``, [thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (* NIA: bounded product *)
    (``(x:int) >= 5 /\ (y:int) >= 5 ==> x * y >= 25``,
      [thm_Z3, thm_CVCp
       (*, thm_Z3p_v4: Z3 4.11 emits an arithmetic th-lemma proof step
          outside the checked nonlinear replay fragment. *)]),
    (* NRA: product of nonneg *)
    (``(x:real) >= 0 /\ (y:real) >= 0 ==> x * y >= 0``,
      [thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (* NRA: square nonneg *)
    (``(x:real) * x >= 0``, [thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (* NRA: strict SOS polynomial, REAL_SOS/CSDP fallback in checked replay *)
    (``0r < 1r + 2r * (x:real) * x * x * x +
              2r * x * x * x * y - x * x * y * y +
              5r * y * y * y * y``,
      [(* thm_Z3p_v4: checked replay needs CSDP for this SOS proof. *)]),

    (* arithmetic inequalities: <, <=, >, >= *)

    (* num *)

    (``0n < 1n``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``1n < 0n``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:num) < x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:num) < y ==> 42 * x < 42 * y``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4
       (*, thm_CVCp: cvc5 proof generation very slow for num multiplication *)]),

    (``0n <= 1n``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``1n <= 0n``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:num) <= x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:num) <= y ==> 42 * x <= 42 * y``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4 (*, thm_CVCp *)]),

    (``1n > 0n``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``0n > 1n``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:num) > x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:num) > y ==> 42 * x > 42 * y``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4 (*, thm_CVCp *)]),

    (``1n >= 0n``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``0n >= 1n``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:num) >= x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:num) >= y ==> 42 * x >= 42 * y``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4 (*, thm_CVCp *)]),

    (``((x:num) < y) = (y > x)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``((x:num) <= y) = (y >= x)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:num) < y /\ y <= z ==> x < z``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:num) <= y /\ y <= z ==> x <= z``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:num) > y /\ y >= z ==> x > z``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:num) >= y /\ y >= z ==> x >= z``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),

    (``(x:num) >= 0``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``0 < (x:num) /\ x <= 1 ==> (x = 1)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),

    (* int *)

    (``0i < 1i``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``1i < 0i``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:int) < x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:int) < y ==> 42 * x < 42 * y``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``0i <= 1i``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``1i <= 0i``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:int) <= x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:int) <= y ==> 42 * x <= 42 * y``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``1i > 0i``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``0i > 1i``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:int) > x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:int) > y ==> 42 * x > 42 * y``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``1i >= 0i``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``0i >= 1i``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:int) >= x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:int) >= y ==> 42 * x >= 42 * y``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``((x:int) < y) = (y > x)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``((x:int) <= y) = (y >= x)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:int) < y /\ y <= z ==> x < z``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:int) <= y /\ y <= z ==> x <= z``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:int) > y /\ y >= z ==> x > z``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:int) >= y /\ y >= z ==> x >= z``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),

    (``(x:int) >= 0``, [sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``0 < (x:int) /\ x <= 1 ==> (x = 1)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (* real *)

    (``0r < 1r``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``1r < 0r``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:real) < x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:real) < y ==> 42 * x < 42 * y``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``0r <= 1r``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``1r <= 0r``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:real) <= x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:real) <= y ==> 42 * x <= 42 * y``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),

    (``1r > 0r``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``0r > 1r``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:real) > x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:real) > y ==> 42 * x > 42 * y``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``1r >= 0r``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``0r >= 1r``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:real) >= x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:real) >= y ==> 42 * x >= 42 * y``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),

    (``((x:real) < y) = (y > x)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``((x:real) <= y) = (y >= x)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:real) < y /\ y <= z ==> x < z``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:real) <= y /\ y <= z ==> x <= z``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:real) > y /\ y >= z ==> x > z``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:real) >= y /\ y >= z ==> x >= z``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),

    (``(x:real) >= 0``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``0 < (x:real) /\ x <= 1 ==> (x = 1)``,
      [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),

    (* conversions between numeric types *)

    (``(x:num) < 42 ==> &x < (42:int)``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(x:num) < 42 ==> &x < (42:real)``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_CVCp (*, thm_Z3p_v4*)
       ]),
    (``(42:int) < x ==> (42:num) < Num x``,
      [thm_AUTO, thm_CVC, thm_CVCp
       (*, thm_Z3, thm_Z3p_v4: after retiring the num bridge axioms,
          Z3 no longer receives enough local facts about integer Num. *)]),
    (``(x:int) < 42 ==> real_of_int x < (42:real)``,
      [(*thm_AUTO,*) thm_CVC, thm_Z3(*, thm_Z3p*), thm_CVCp]),
    (``(x:int) < -42 ==> real_of_int x < (-42:real)``,
      [(*thm_AUTO,*) thm_CVC, thm_Z3(*, thm_Z3p*), thm_CVCp]),

    (``flr (42:real) = (42:num)``,
      [thm_AUTO, thm_CVC, thm_CVCp]),
    (``flr (-42:real) = (0:num)``,
      [thm_AUTO, thm_CVC, thm_CVCp]),
    (``flr (4/3:real) = (1:num)``,
      [thm_AUTO, thm_CVC, thm_CVCp]),
    (``flr (-4/3:real) = (0:num)``,
      [thm_AUTO, thm_CVC, thm_CVCp]),
    (``flr (0:real) = (0:num)``,
      [thm_AUTO, thm_CVC, thm_CVCp]),
    (``(x:real) < 0 ==> flr x = (0:num)``,
      [(*thm_AUTO,*) thm_CVC, thm_CVCp]),
    (``(x:real) <= 0 ==> flr x = (0:num)``,
      [(*thm_AUTO,*) thm_CVC, thm_CVCp]),

    (``clg (42:real) = (42:num)``,
      [thm_AUTO, thm_CVC, thm_CVCp]),
    (``clg (-42:real) = (0:num)``,
      [thm_AUTO, thm_CVC, thm_CVCp]),
    (``clg (4/3:real) = (2:num)``,
      [thm_AUTO, thm_CVC, thm_CVCp]),
    (``clg (-4/3:real) = (0:num)``,
      [thm_AUTO, thm_CVC, thm_CVCp]),
    (``clg (0:real) = (0:num)``,
      [thm_AUTO, thm_CVC, thm_CVCp]),
    (``(x:real) < 0 ==> clg x = (0:num)``,
      [(*thm_AUTO,*) thm_CVC, thm_CVCp]),
    (``(x:real) <= 0 ==> clg x = (0:num)``,
      [(*thm_AUTO,*) thm_CVC, thm_CVCp]),

    (``flrtoks (42:real) = (42:int)``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p, thm_CVCp]),
    (``flrtoks (-42:real) = (-42:int)``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p, thm_CVCp]),
    (``flrtoks (4/3:real) = (1:int)``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp
       ]),
    (``flrtoks (-4/3:real) = (-2:int)``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp
       ]),
    (``0 < (x:real) ==> ((flrtoks x): int) = &((flr x): num)``,
      [(*thm_AUTO,*) thm_CVC, thm_Z3(*, thm_Z3p_v4*)]),
    (``0 <= (x:real) ==> ((flrtoks x): int) = &((flr x): num)``,
      [(*thm_AUTO,*) thm_CVC, thm_Z3(*, thm_Z3p_v4*)]),

    (``clgtoks (42:real) = (42:int)``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``clgtoks (-42:real) = (-42:int)``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``clgtoks (4/3:real) = (2:int)``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp
       ]),
    (``clgtoks (-4/3:real) = (-1:int)``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp
       ]),
    (``0 < (x:real) ==> ((clgtoks x): int) = &((clg x): num)``,
      [(*thm_AUTO,*) thm_CVC, thm_Z3(*, thm_Z3p_v4*)]),
    (``0 <= (x:real) ==> ((clgtoks x): int) = &((clg x): num)``,
      [(*thm_AUTO,*) thm_CVC, thm_Z3(*, thm_Z3p_v4*)]),

    (* uninterpreted functions *)

    (``(x = y) ==> (f x = f y)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x = y) ==> (f x y = f y x)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(f (f x) = x) /\ (f (f (f (f (f x)))) = x) ==> (f x = x)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(f x = f y) ==> (x = y)``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),

    (* arrays as function updates *)

    (``i <> j ==> ((i =+ e) (a :int -> int)) j = a j``,
      [thm_Z3p, thm_Z3p_v4, thm_CVCp]),
    (``i <> j ==>
        (j =+ f) ((i =+ e) (a :int -> int)) =
        (i =+ e) ((j =+ f) a)``,
      [thm_Z3p, thm_Z3p_v4, thm_CVCp]),
    (``(!i. (a :int -> int) i = b i) ==> (a = b)``,
      [thm_Z3p, thm_Z3p_v4, thm_CVCp]),

    (* predicates *)

    (``P x ==> P x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``P x ==> Q x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``P x ==> P y``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``P x y ==> P x x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``P x y ==> P y x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``P x y ==> P y y``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),

    (* quantifiers *)

    (``!x. x = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (* Yices 1.0.28 reports `unknown' for the next goal, while Z3 2.13
       (somewhat surprisingly, as SMT-LIB does not seem to require
       non-empty sorts) can prove it *)
    (``?x. x = x``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``(?y. !x. P x y) ==> (!x. ?y. P x y)``,
      [thm_AUTO, (*thm_CVC,*) thm_YO, thm_Z3, thm_Z3p_v4 (*, thm_CVCp *)]),
    (* CVC5 1.0.8 and Yices 1.0.28 report `unknown' for the next goal *)
    (``(!x. ?y. P x y) ==> (?y. !x. P x y)``,
      [(* sat_Z3, sat_Z3p: Z3 4.11 returns unknown on this polymorphic
          quantified satisfiability check. *)
       (*, sat_CVCp: cvc5 returns unknown *)]),
    (``(?x. P x) ==> !x. P x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``?x. P x ==> !x. P x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (``~(?x. P x ==> Q) <=> ~?x. ~P x \/ Q``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),
    (* D15: cvc5 skolems for a multi-binder negated goal must use the same
       whole-block choice terms in the CPC parser and checked replay. *)
    (``!x y:int. x <= (if x < y then y else x)``, [thm_CVCp]),
    (``!x y:int.
        x <= (if x < y then y else x) /\
        y <= (if x < y then y else x)``, [thm_CVCp]),

    (* let binders *)

    (``let x = y in let x = (x /\ z) in x <=> y /\ z``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``let x = u in let x = x in let y = v in x /\ y <=> u /\ v``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (* lambda abstractions *)

    (``(\x. x) = (\y. y)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(\x. \x. x) x x = (\y. \y. y) y x``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(\x. x (\x. x)) = (\y. y (\x. x))``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(\x. x (\x. x)) = (\y. y x)``,
      [sat_Z3p_v411, sat_CVCp]),
    (``x = (\x. x) ==>
        ((\x. x (\x. x)) = (\y. y x))``,
      [thm_Z3p, thm_Z3p_v4, thm_CVCp]),
    (``f x = (\x. f x) x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``f x = (\y. f y) x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (* higher-order logic *)

    (``(H:(int -> int) -> bool) (\x. x + 1) /\ p ==>
        H (\y. y + 1)``, [thm_Z3p, thm_Z3p_v4, thm_CVCp]),
    (``(\x:int. f (g x)) = (\y. f (g y))``,
      [thm_Z3p, thm_Z3p_v4, thm_CVCp]),
    (``(\x:int. f x) = f``, [thm_Z3p, thm_Z3p_v4, thm_CVCp]),
    (``(H:(bool -> int) -> bool) (smtlib_ho_rank2 x) ==>
        H (\p. smtlib_ho_rank2 x p)``,
      [thm_Z3p, thm_Z3p_v4, thm_CVCp]),
    (``(H:(int -> int) -> bool) ($+ 1) ==> H (\x. 1 + x)``,
      [thm_CVCp]),
    (``(P (f x) ==> Q f) ==> P (f x) ==> Q f``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(Q f ==> P (f x)) ==> Q f ==> P (f x)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (* tuples, FST, SND *)

    (``(x, y) = (x, z)``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x, y) = (z, y)``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x, y) = (y, x)``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``((x, y) = (y, x)) = (x = y)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``((x, y, z) = (y, z, x)) <=> (x = y) /\ (y = z)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``((x, y) = (u, v)) <=> (x = u) /\ (y = v)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``y = FST (x, y)``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``x = FST (x, y)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(FST (x, y, z) = FST (u, v, w)) = (x = u)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(FST (x, y, z) = FST (u, v, w)) <=> (x = u) /\ (y = w)``,
      [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),

    (``y = SND (x, y)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x = SND (x, y)``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(SND (x, y, z) = SND (u, v, w)) = (y = v)``,
       [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(SND (x, y, z) = SND (u, v, w)) = (z = w)``,
       [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(SND (x, y, z) = SND (u, v, w)) <=> (y = v) /\ (z = w)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``(FST (x, y) = SND (x, y)) = (x = y)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(FST p = SND p) = (p = (SND p, FST p))``,
      [thm_CVC, thm_YO, thm_Z3, thm_Z3p]),
    (``((\p. FST p) (x, y) = (\p. SND p) (x, y)) = (x = y)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3p, thm_Z3p_v4]),

    (* Symbolic list destruction must use native datatype selectors rather
       than an unconstrained unary HD symbol. *)
    (``l = [1; 2] ==> HD l = 1``,
      [thm_CVC, thm_Z3, thm_Z3p, thm_CVCp]),

    (* words (i.e., bit vectors) *)

    (``x:word2 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word3 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word4 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word5 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word6 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word7 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word8 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word12 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word16 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word20 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word24 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word28 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word30 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word32 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word64 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``x:word32 && x = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word32 && y = y && x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:word32 && y) && z = x && (y && z)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word32 && 0w = 0w``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word32 && 0w = x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),

    (``x:word32 || x = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word32 || y = y || x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:word32 || y) || z = x || (y || z)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word32 || 0w = 0w``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``x:word32 || 0w = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``x:word32 ?? x = 0w``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word32 ?? y = y ?? x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:word32 ?? y) ?? z = x ?? (y ?? z)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word32 ?? 0w = 0w``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``x:word32 ?? 0w = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (* CVC5's proof for this bit-vector complement identity is
       pathologically large; the checked Z3 proof row above supplies the
       proof-replay coverage while the CVC oracle remains exercised. *)
    (``~ ~ x:word32 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p]),
    (``~ 0w = 0w:word32``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),

    (* Yices does not support bit-vector division *)

    (``x:word32 / 4w = x / 2w / 2w``, [(*thm_AUTO, thm_YO,*) thm_CVC, thm_Z3(*, thm_Z3p*)]),
    (``x:word32 / 6w = x / 2w / 3w``, [(*thm_AUTO, thm_YO,*) thm_CVC, thm_Z3(*, thm_Z3p*)]),
    (``x:word32 / x = 1w``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``x:word32 <> 0w ==> (x / x = 1w)``, [(*thm_AUTO, thm_YO,*) thm_CVC, thm_Z3(*, thm_Z3p*)]),
    (``y:word8 <> 0w ==> (x / y = -x / -y)``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``y:word8 <> 0w ==> (x / y = -(-x / y))``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``y:word8 <> 0w ==> (x / y = -(x / -y))``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``x:word8 <> 0x80w /\ y <> 0w ==> (x / y = -x / -y)``,
      [(*thm_AUTO, thm_YO,*) thm_CVC, thm_Z3(*, thm_Z3p*)]),
    (``x:word8 <> 0x80w /\ y <> 0w ==> (x / y = -(-x / y))``,
      [(*thm_AUTO, thm_YO,*) thm_CVC, thm_Z3(*, thm_Z3p*)]),
    (``x:word8 <> 0x80w /\ y <> 0w ==> (x / y = -(x / -y))``,
      [(*thm_AUTO, thm_YO,*) thm_CVC, thm_Z3(*, thm_Z3p*)]),

    (``x:word32 // 4w = x // 2w // 2w``, [thm_AUTO, thm_CVC, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 // 6w = x // 2w // 3w``, [(*thm_AUTO, thm_YO,*) thm_CVC, thm_Z3(*, thm_Z3p*)]),
    (``x:word32 // x = 1w``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``x:word32 <> 0w ==> (x // x = 1w)``, [(*thm_AUTO, thm_YO,*) thm_CVC, thm_Z3(*, thm_Z3p*)]),

    (``y:word8 <> 0w ==> (x = x // y * y + word_mod x y)``,
      [(*thm_AUTO, thm_YO,*) thm_CVC, thm_Z3(*, thm_Z3p*)]),
    (``y:word8 <> 0w ==> word_mod x y <+ y``,
      [(*thm_AUTO, thm_YO,*) thm_CVC, thm_Z3(*, thm_Z3p*)]),

    (``y:word8 <> 0w ==> (x = x / y * y + word_rem x y)``,
      [(*thm_AUTO, thm_YO,*) thm_CVC, thm_Z3(*, thm_Z3p*)]),

    (``x:word8 < 0w /\ y < 0w  ==> (word_rem x y = -word_mod (-x) (-y))``,
      [(*thm_AUTO, thm_YO,*)thm_CVC, thm_Z3(*, thm_Z3p*)]),
    (``x:word8 < 0w /\ y >= 0w ==> (word_rem x y = -word_mod (-x) y)``,
      [thm_CVC (*thm_AUTO, thm_YO, thm_Z3, thm_Z3p*)]),
    (``x:word8 >= 0w /\ y < 0w ==> (word_rem x y = word_mod x (-y))``,
      [(*thm_AUTO, thm_YO,*)thm_CVC, thm_Z3(*, thm_Z3p*)]),
    (``x:word8 >= 0w /\ y >= 0w ==> (word_rem x y = word_mod x y)``,
      [thm_CVC, (*thm_AUTO, thm_YO,*) thm_Z3_v4(*, thm_Z3p_v4*)]),

    (``x:word8 < 0w /\ y < 0w  ==> (word_smod x y = -word_mod (-x) (-y))``,
      [(*thm_AUTO, thm_YO,*)thm_CVC, thm_Z3(*, thm_Z3p*)]),
    (``x:word8 < 0w /\ y >= 0w ==> (word_smod x y = -word_mod (-x) y + y)``,
      [sat_CVC, (*sat_YO,*) sat_Z3, sat_Z3p, sat_CVCp]),
    (``x:word8 >= 0w /\ y < 0w ==> (word_smod x y = word_mod x (-y) + y)``,
      [sat_CVC, (*sat_YO,*) sat_Z3_v4, sat_Z3p_v4, sat_CVCp]),
    (``x:word8 >= 0w /\ y >= 0w ==> (word_smod x y = word_mod x y)``,
      [thm_CVC, (*thm_AUTO, thm_YO,*) thm_Z3_v4(*, thm_Z3p_v4*)]),

    (``x:word32 << 0 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word32 << 31 = 0w``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:word32 << 31 = 0w) \/ (x << 31 = 1w << 31)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3(*, thm_Z3p*)]),

    (* Yices does not support shifting by more than the word length *)

    (``x:word32 << 99 = 0w``, [thm_AUTO, thm_CVC, (*thm_YO,*) thm_Z3, thm_Z3p, thm_CVCp]),

    (* Yices does not support shifting by a non-constant *)

    (``x:word32 << n = x``, [sat_CVC, (*sat_YO,*) sat_Z3, sat_Z3p, sat_CVCp]),

    (``x:word32 <<~ 0w = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word32 <<~ 31w = 0w``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:word32 <<~ 31w = 0w) \/ (x <<~ 31w = 1w <<~ 31w)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``(x:word32 <<~ x) && 1w = 0w``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``x:word32 <<~ y = y <<~ x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:word32 <<~ y) <<~ z = x <<~ (y <<~ z)``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),

    (``x:word32 >>> 0 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word32 >>> 31 = 0w``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:word32 >>> 31 = 0w) \/ (x >>> 31 = 1w)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3(*, thm_Z3p*)]),

    (* Yices does not support right-shift by a (non-constant) bit-vector
       amount *)

    (``x:word32 >>>~ 0w = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word32 >>>~ 31w = 0w``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:word32 >>>~ 31w = 0w) \/ (x >>>~ 31w = 1w)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``(x:word32 >>>~ x) = 0w``, [thm_AUTO, thm_CVC, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 >>>~ y = y >>>~ x``, [sat_CVC, (*sat_YO,*) sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:word32 >>>~ y) >>>~ z = x >>>~ (y >>>~ z)``,
      [sat_CVC, (*sat_YO,*) sat_Z3, sat_Z3p, sat_CVCp]),

    (* Yices does not support arithmetical shift-right *)

    (``x:word32 >> 0 = x``, [thm_AUTO, thm_CVC, (*thm_YO,*) thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word32 >> 31 = 0w``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:word32 >> 31 = 0w) \/ (x >> 31 = 0xFFFFFFFFw)``,
      [thm_AUTO, thm_CVC, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),

    (``x:word32 >>~ 0w = x``, [thm_AUTO, thm_CVC, (*thm_YO,*) thm_Z3, thm_Z3p, thm_CVCp]),
    (``x:word32 >>~ 31w = 0w``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:word32 >>~ 31w = 0w) \/ (x >>~ 31w = 0xFFFFFFFFw)``,
      [thm_AUTO, thm_CVC, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``(x:word32 >>~ x = 0w) \/ (x >>~ x = 0xFFFFFFFFw)``,
      [thm_AUTO, thm_CVC, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 >>~ y = y >>~ x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:word32 >>~ y) >>~ z = x >>~ (y >>~ z)``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),

    (* Yices does not support bit-vector rotation *)

    (``x:word32 #<< 0 = x``, [thm_AUTO, thm_CVC, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 #<< 32 = x``, [thm_AUTO, thm_CVC, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 #<< 64 = x``, [thm_AUTO, thm_CVC, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 #<< 1 <> x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),

    (``x:word32 #<<~ 0w = x``, [thm_AUTO, thm_CVC, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 #<<~ 32w = x``, [thm_AUTO, thm_CVC, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 #<<~ 64w = x``, [thm_AUTO, thm_CVC, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 #<<~ 1w = x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),

    (``x:word32 #>> 0 = x``, [thm_AUTO, thm_CVC, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 #>> 32 = x``, [thm_AUTO, thm_CVC, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 #>> 64 = x``, [thm_AUTO, thm_CVC, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 #>> 1 <> x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),

    (``x:word32 #>>~ 0w = x``, [thm_AUTO, thm_CVC, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 #>>~ 32w = x``, [thm_AUTO, thm_CVC, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 #>>~ 64w = x``, [thm_AUTO, thm_CVC, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 #>>~ 1w = x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),

    (``1w:word2 @@ 1w:word2 = 5w:word4``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``((x @@ y):word32 = y @@ x) = (x:word16 = y)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p (*, thm_CVCp: @bit_of parse error *)]),

    (``(31 >< 0) x:word32 = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(1 >< 0) (0w:word32) = 0w:word2``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(32 >< 0) (x:word32) :bool[33] = w2w x``,
      [thm_AUTO, (*thm_CVC,*) thm_YO(*, thm_Z3, thm_Z3p*)]),
    (``(0 >< 1) (x:word32) = 0w:word32``,
      [thm_AUTO, (*thm_CVC,*) thm_YO(*, thm_Z3, thm_Z3p*)]),

    (``(x:word2 = y) <=> (x ' 0 = y ' 0) /\ (x ' 1 = y ' 1)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3(*, thm_Z3p*)]),

    (``0w:word32 = w2w (0w:word16)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``0w:word32 = w2w (0w:word32)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``0w:word32 = w2w (0w:word64)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``x:word32 = w2w x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3(*, thm_Z3p*)]),

    (``0w:word32 = sw2sw (0w:word16)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``0w:word32 = sw2sw (0w:word32)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``0w:word32 = sw2sw (0w:word64)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``x:word32 = sw2sw x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3(*, thm_Z3p*)]),

    (``(x:word32) + x = x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:word32) + y = y + x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``((x:word32) + y) + z = x + (y + z)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:word32) + 0w = 0w``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:word32) + 0w = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``(x:word32) - x = x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:word32) - x = 0w``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:word32) - y = y - x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``((x:word32) - y) - z = x - (y - z)``,
      [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:word32) - 0w = 0w``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:word32) - 0w = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``(x:word32) * x = x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:word32) * y = y * x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``((x:word32) * y) * z = x * (y * z)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:word32) * 0w = 0w``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``(x:word32) * 0w = x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``(x:word32) * 1w = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``- (x:word32) = x``, [sat_CVC, sat_YO, sat_Z3, sat_Z3p, sat_CVCp]),
    (``- 0w = 0w:word32``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``- - (x:word32) = x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``0w < 1w:word32``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``~ 0w < 0w:word32``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``0w <= 1w:word32``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x <= y:word32 <=> x < y \/ (x = y)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``~ 0w <= 0w:word32``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``1w > 0w:word32``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``0w > ~ 0w:word32``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``1w >= 0w:word32``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x >= y:word32 <=> x > y \/ (x = y)``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``0w >= ~ 0w:word32``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``0w <+ 1w:word32``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``0w <+ ~ 0w:word32``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``0w <=+ 1w:word32``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x <=+ y:word32 <=> x <+ y \/ (x = y)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``0w <=+ ~ 0w:word32``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``1w >+ 0w:word32``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``~ 0w >+ 0w:word32``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``1w >=+ 0w:word32``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x >=+ y:word32 <=> x >+ y \/ (x = y)``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``~ 0w >=+ 0w:word32``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (* A word atom must not stop the num-to-int transfer when the naturals it
       guards never meet the word theory: `DIV` is only in the SMT-LIB
       fragment once `x` has been transferred to an integer. *)
    (``((w:word8) && v = v && w) /\ ((x:num) DIV 2 <= x)``,
      [thm_CVC, thm_CVCp, thm_Z3, thm_Z3p]),

    (* from Magnus Myreen *)
    (``!(a:word32) b.
     (((word_msb (a - b) <=>
        (word_msb a <=/=> word_msb b) /\
        (word_msb a <=/=> word_msb (a - b))) <=> b <= a) /\
      ((word_msb (a - b) <=>
        (word_msb b <=/=> word_msb a) /\
        (word_msb a <=/=> word_msb (a - b))) <=> b <= a) /\
      ((word_msb (a - b) <=>
        (word_msb a <=/=> word_msb b) /\
        (word_msb (a - b) <=/=> word_msb a)) <=> b <= a) /\
      ((word_msb (a - b) <=>
        (word_msb b <=/=> word_msb a) /\
        (word_msb (a - b) <=/=> word_msb a)) <=> b <= a) /\
      ((word_msb (a - b) <=>
        (word_msb a <=/=> word_msb (a - b)) /\
        (word_msb a <=/=> word_msb b)) <=> b <= a) /\
      ((word_msb (a - b) <=>
        (word_msb a <=/=> word_msb (a - b)) /\
        (word_msb b <=/=> word_msb a)) <=> b <= a) /\
      ((word_msb (a - b) <=>
        (word_msb (a - b) <=/=> word_msb a) /\
        (word_msb a <=/=> word_msb b)) <=> b <= a) /\
      ((word_msb (a - b) <=>
        (word_msb (a - b) <=/=> word_msb a) /\
        (word_msb b <=/=> word_msb a)) <=> b <= a) /\
      (((word_msb a <=/=> word_msb b) /\
        (word_msb a <=/=> word_msb (a - b)) <=> word_msb (a - b)) <=>
       b <= a) /\
      (((word_msb b <=/=> word_msb a) /\
        (word_msb a <=/=> word_msb (a - b)) <=> word_msb (a - b)) <=>
       b <= a) /\
      (((word_msb a <=/=> word_msb b) /\
        (word_msb (a - b) <=/=> word_msb a) <=> word_msb (a - b)) <=>
       b <= a) /\
      (((word_msb b <=/=> word_msb a) /\
        (word_msb (a - b) <=/=> word_msb a) <=> word_msb (a - b)) <=>
       b <= a) /\
      (((word_msb a <=/=> word_msb (a - b)) /\
        (word_msb a <=/=> word_msb b) <=> word_msb (a - b)) <=>
       b <= a) /\
      (((word_msb a <=/=> word_msb (a - b)) /\
        (word_msb b <=/=> word_msb a) <=> word_msb (a - b)) <=>
       b <= a) /\
      (((word_msb (a - b) <=/=> word_msb a) /\
        (word_msb a <=/=> word_msb b) <=> word_msb (a - b)) <=>
       b <= a) /\
      (((word_msb (a - b) <=/=> word_msb a) /\
        (word_msb b <=/=> word_msb a) <=> word_msb (a - b)) <=>
       b <= a)) /\ (a >= b <=> b <= a) /\ (a > b <=> b < a) /\
     (~(a <=+ b) <=> b <+ a) /\ (~(a <+ b) <=> b <=+ a) /\
     (a <+ b \/ (a = b) <=> a <=+ b) /\ (~(a < b) <=> b <= a) /\
     (~(a <= b) <=> b < a) /\ (a < b \/ (a = b) <=> a <= b) /\
     ((a = b) \/ a < b <=> a <= b) /\ (a <+ b \/ (a = b) <=> a <=+ b) /\
     ((a = b) \/ a <+ b <=> a <=+ b) /\
     (b <=+ a /\ a <> b <=> b <+ a) /\ (a <> b /\ b <=+ a <=> b <+ a) /\
     (b <= a /\ a <> b <=> b < a) /\ (a <> b /\ b <= a <=> b < a) /\
     (((v:word32) - w = 0w) <=> (v = w)) /\ (w - 0w = w)``,
      [(*thm_AUTO,*) thm_CVC, thm_YO, thm_Z3(*, thm_Z3p*)]),

    (* from Yogesh Mahajan *)
    (``!(w: 18 word). (sw2sw w): 32 word = w2w ((16 >< 0) w: 17 word) +
     0xfffe0000w + ((0 >< 0) (~(17 >< 17) w: bool[unit]) << 17): 32 word``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3(*, thm_Z3p*)]),

    (* The Yices translation currently rejects polymorphic-width bit
       vectors; the SMT-LIB translation treats their type -- and
       operations on them -- as uninterpreted. *)

    (``x <=+ x``, [thm_AUTO(*, thm_CVC, thm_YO, thm_Z3, thm_Z3p*)]),

    (* data types: constructors *)

    (``foo <> bar``, [thm_AUTO, thm_CVCp, thm_YO, thm_Z3p, thm_Z3p_v4]),
    (``foo <> baz``, [thm_AUTO, thm_YO, thm_Z3p, thm_Z3p_v4]),
    (``bar <> baz``, [thm_AUTO, thm_YO, thm_Z3p, thm_Z3p_v4]),
    (``[] <> x::xs``, [thm_AUTO, thm_YO, thm_Z3p, thm_Z3p_v4]),
    (``NONE <> SOME (x:'a)``, [thm_AUTO, thm_Z3p, thm_Z3p_v4]),
    (``h::l <> l``, [thm_Z3p, thm_Z3p_v4]),
    (``dtConsF t f <> f``, [thm_Z3p, thm_Z3p_v4]),
    (``xs <> x::xs``, [thm_AUTO, thm_YO, thm_Z3p, thm_Z3p_v4]),
    (``(x::xs = y::ys) <=> (x = y) /\ (xs = ys)``,
      [thm_AUTO, thm_YO, thm_Z3p, thm_Z3p_v4]),
    (``(SOME x = SOME y) <=> (x = y)``, [thm_AUTO]),

    (* data types: case constants *)

    (``dt1_CASE foo f b z = f``, [thm_AUTO, thm_YO, thm_Z3p, thm_Z3p_v4]),
    (``dt1_CASE bar f b z = b``, [thm_AUTO, thm_YO, thm_Z3p, thm_Z3p_v4]),
    (``dt1_CASE baz f b z = z``, [thm_AUTO, thm_YO, thm_Z3p, thm_Z3p_v4]),
    (``dt1_CASE x c c c = c``, [(*thm_AUTO,*) thm_YO, thm_Z3p, thm_Z3p_v4]),
    (``!d. flc (flc d) = d``, [thm_flc_Z3p, thm_flc_CVCp]),
    (``list_CASE [] n c = n``, [thm_AUTO, thm_YO, thm_Z3p, thm_Z3p_v4]),
    (``list_CASE (x::xs) n c = c x xs``,
      [thm_AUTO, thm_YO, thm_Z3p, thm_Z3p_v4]),
    (``option_CASE (SOME x) n s = s x``, [thm_AUTO, thm_Z3p, thm_Z3p_v4]),
    (``option_CASE NONE n s = n``, [thm_AUTO, thm_Z3p, thm_Z3p_v4]),

    (* Z3 4.14.x array+datatype compatibility coverage.  The SAT siblings
       ensure the version policy cannot accidentally collapse these queries
       into an always-UNSAT result. *)
    (``list_CASE [] (n:bool) c = c x xs``, [sat_Z3, sat_Z3p]),
    (``list_CASE (x::xs) (n:bool) c = n``, [sat_Z3, sat_Z3p]),
    (``option_CASE (SOME x) (n:bool) s = n``, [sat_Z3, sat_Z3p]),
    (``option_CASE NONE (n:bool) s = s x``, [sat_Z3, sat_Z3p]),
    (``option_CASE ov (n:bool) s = n ==>
       ov = NONE \/ ?x. ov = SOME x``,
      [thm_Z3, thm_Z3p]),

    (* records: field selectors *)

    (``(x = y) <=> (x.employed = y.employed) /\ (x.age = y.age)``,
      [(*thm_AUTO,*) thm_YO, thm_Z3p, thm_Z3p_v4]),

    (* records: field updates *)

    (``(x with employed := e).employed = e``,
      [thm_AUTO, thm_YO, thm_Z3p, thm_Z3p_v4]),
    (``(x with age := a).employed = x.employed``,
      [thm_AUTO, thm_Z3p, thm_Z3p_v4]),

    (``x with <| employed := e; age := a |> =
     y with <| employed := e; age := a |>``,
      [thm_AUTO, thm_YO, thm_Z3p, thm_Z3p_v4]),

    (* records: literals *)

    (``(<| employed := e1; age := a1 |> = <| employed := e2; age := a2 |>)
     <=> (e1 = e2) /\ (a1 = a2)``,
      [thm_AUTO, thm_YO]),

    (* sets (as predicates -- every set expression must be applied to an
       argument!) *)

    (``x IN P <=> P x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``x IN {x | P x} <=> P x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``x NOTIN {}``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x IN UNIV``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``x IN P UNION Q <=> P x \/ Q x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x IN P UNION {} <=> x IN P``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x IN P UNION UNIV``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x IN P UNION Q <=> x IN Q UNION P``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x IN P UNION (Q UNION R) <=> x IN (P UNION Q) UNION R``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (``x IN P INTER Q <=> P x /\ Q x``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x NOTIN P INTER {}``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x IN P INTER UNIV <=> x IN P``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x IN P INTER Q <=> x IN Q INTER P``, [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),
    (``x IN P INTER (Q INTER R) <=> x IN (P INTER Q) INTER R``,
      [thm_AUTO, thm_CVC, thm_YO, thm_Z3, thm_Z3p, thm_CVCp]),

    (* Native smtfp reaches the official FP surface.  These checked Z3 4.x
       rows cover every ground arithmetic class plus comparison, canonical
       NaN equality, conversion, and a Float16 symbolic atom.  The functional
       harness rejects every oracle tag, which also pins native_ieeeLib off. *)
    (``smtfp_add RNE
         (smtfp_bits 0w 3w 0w : (4,3) smtfp)
         (smtfp_bits 0w 3w 0w : (4,3) smtfp) =
       smtfp_bits 0w 4w 0w``, [thm_Z3p_v4]),
    (``smtfp_sub RNE
         (smtfp_bits 0w 4w 0w : (4,3) smtfp)
         (smtfp_bits 0w 3w 0w : (4,3) smtfp) =
       smtfp_bits 0w 3w 0w``, [thm_Z3p_v4]),
    (``smtfp_mul RNE
         (smtfp_bits 0w 4w 0w : (4,3) smtfp)
         (smtfp_bits 0w 4w 0w : (4,3) smtfp) =
       smtfp_bits 0w 5w 0w``, [thm_Z3p_v4]),
    (``smtfp_div RNE
         (smtfp_bits 0w 4w 0w : (4,3) smtfp)
         (smtfp_bits 0w 4w 0w : (4,3) smtfp) =
       smtfp_bits 0w 3w 0w``, [thm_Z3p_v4]),
    (``smtfp_sqrt RNE (smtfp_bits 0w 5w 0w : (4,3) smtfp) =
       smtfp_bits 0w 4w 0w``, [thm_Z3p_v4]),
    (``smtfp_fma RNE
         (smtfp_bits 0w 3w 0w : (4,3) smtfp)
         (smtfp_bits 0w 3w 0w : (4,3) smtfp)
         (smtfp_bits 0w 3w 0w : (4,3) smtfp) =
       smtfp_bits 0w 4w 0w``, [thm_Z3p_v4]),
    (``smtfp_rem
         (smtfp_bits 0w 5w 4w : (4,3) smtfp)
         (smtfp_bits 0w 4w 0w : (4,3) smtfp) =
       smtfp_bits 0w 3w 0w``, [thm_Z3p_v4]),
    (``smtfp_round_to_integral RNA
         (smtfp_bits 1w 4w 4w : (4,3) smtfp) =
       smtfp_bits 1w 4w 8w``, [thm_Z3p_v4]),
    (``smtfp_round_to_integral RNE
         (smtfp_bits 0w 14w 0w : (3,5) smtfp) = smtfp_pzero``,
      [thm_Z3p_v4]),
    (``smtfp_round_to_integral RNE
         (smtfp_bits 1w 14w 0w : (3,5) smtfp) = smtfp_nzero``,
      [thm_Z3p_v4]),
    (``smtfp_lt
         (smtfp_bits 0w 3w 0w : (4,3) smtfp)
         (smtfp_bits 0w 4w 0w : (4,3) smtfp)``, [thm_Z3p_v4]),
    (``(smtfp_bits 1w 7w 1w : (4,3) smtfp) = smtfp_nan``,
      [thm_Z3p_v4]),
    (``(smtfp_to_ubv RTZ
         (smtfp_bits 0w 4w 8w : (4,3) smtfp) : word4) = 3w``,
      [thm_Z3p_v4]),
    (* TASK_17 public parser/replay pin: Z3 lowers this symbolic FP relation
       to a packed word plus its coherent Boolean bit allocation. *)
    (``smtfp_lt (x : (4,3) smtfp) y ==> ~smtfp_lt y x``,
      [thm_Z3p_v4]),
    (``!x : (4,3) smtfp. ~smtfp_lt x x``,
      [thm_Z3p_v4, thm_CVCp]),

    (* Tiny symbolic add/sub uses the checked Tier-3 circuit rung.  The add
       row exercises symbolic finite/exceptional dispatch against +0; the
       sub row covers symbolic exceptional dispatch. *)
    (``smtfp_add RTN (x : (1,2) smtfp) smtfp_pzero = x``,
      [thm_Z3p_v4]),
    (``smtfp_sub RNA (x : (1,2) smtfp) smtfp_nan = smtfp_nan``,
      [thm_Z3p_v4]),

    (* A native binary_ieee comparison is rewritten through the proved
       transfer kit and then replays over the SMT FloatingPoint sort.  This
       is the evidence for the support record's checked-replay claim. *)
    (``float_less_than (x : (4,3) binary_ieee$float) y ==>
       ~float_less_than y x``, [thm_Z3p_v4]),

    (* TASK_11: each proved expansion/transfer family reaches a checked
       solver verdict through the public native-float preprocessing path. *)
    (``float_is_finite (x : (4,3) binary_ieee$float) <=>
       ~float_is_nan x /\ ~float_is_infinite x``, [thm_Z3p_v4]),
    (``float_unordered (x : (4,3) binary_ieee$float) y <=>
       float_is_nan x \/ float_is_nan y``, [thm_Z3p_v4]),
    (``~float_is_signalling
         (canon (x : (4,3) binary_ieee$float))``, [thm_Z3p_v4]),
    (``float_is_integral (x : (4,3) binary_ieee$float) <=>
       ((~smtfp_is_nan (smtfp_intro x) /\
         ~smtfp_is_infinite (smtfp_intro x)) /\
        smtfp_round_to_integral RTZ (smtfp_intro x) = smtfp_intro x)``,
      [thm_Z3p_v4]),
    (``~float_is_zero
         (float_round_to_integral roundTowardZero
           (x : (4,3) binary_ieee$float)) ==>
       smtfp_intro (float_round_to_integral roundTowardZero x) =
       smtfp_round_to_integral RTZ (smtfp_intro x)``, [thm_Z3p_v4]),
    (``float_is_finite (x : (4,3) binary_ieee$float) ==>
       float_to_real x = smtfp_to_real (smtfp_intro x)``,
      [thm_Z3p_v4]),
    (``(toneg <=> (r : real) < 0) ==>
       (smtfp_intro
          (float_round roundTowardZero toneg r) : (4,3) smtfp) =
       smtfp_from_real RTZ r``, [thm_Z3p_v4]),
    (``((roundTowardZero = roundTowardNegative) <=> (r : real) < 0) ==>
       (smtfp_intro (real_to_float roundTowardZero r) : (4,3) smtfp) =
       smtfp_from_real RTZ r``, [thm_Z3p_v4]),
    (``(smtfp_intro
          (float_round roundTowardZero T (3r / 2) :
            (3,5) binary_ieee$float)) =
       (smtfp_from_real RTZ (3r / 2) : (3,5) smtfp)``, [thm_Z3p_v4]),
    (``(smtfp_intro
          (float_round roundTowardZero F (-3r / 2) :
            (3,5) binary_ieee$float)) =
       (smtfp_from_real RTZ (-3r / 2) : (3,5) smtfp)``, [thm_Z3p_v4]),
    (``(smtfp_intro
          (real_to_float roundTowardNegative (3r / 2) :
            (3,5) binary_ieee$float)) =
       (smtfp_from_real RTN (3r / 2) : (3,5) smtfp)``, [thm_Z3p_v4]),
    (``(smtfp_intro
          (real_to_float roundTowardZero (-3r / 2) :
            (3,5) binary_ieee$float)) =
       (smtfp_from_real RTZ (-3r / 2) : (3,5) smtfp)``, [thm_Z3p_v4]),
    (``(smtfp_intro (float_min x y) : (4,3) smtfp) =
         smtfp_min (smtfp_intro x) (smtfp_intro y) /\
       smtfp_intro (float_max x y) =
         smtfp_max (smtfp_intro x) (smtfp_intro y) /\
       smtfp_intro (float_rem x y) =
         smtfp_rem (smtfp_intro x) (smtfp_intro y)``, [thm_Z3p_v4]),
    (``(smtfp_intro
          (float_from_ieee_bv (v : (1 + (3 + 4)) word)) : (4,3) smtfp) =
         smtfp_from_ieee_bv v /\
       float_pack_ieee_bv (canon (x : (4,3) binary_ieee$float)) =
         smtfp_pack_ieee_bv (smtfp_intro x)``, [thm_Z3p_v4]),
    (``((float_to_ubv RTZ (x : (4,3) binary_ieee$float) : word8) =
          smtfp_to_ubv RTZ (smtfp_intro x)) /\
       ((float_to_sbv RTZ x : word8) =
          smtfp_to_sbv RTZ (smtfp_intro x))``, [thm_Z3p_v4]),

    (* TASK_12: a raw residual smtfloat semantic head is rejected by the
       public translation entry point before an SMT-LIB program exists. *)
    (``smtfp_unordered (x : (4,3) smtfp) y``,
      [reject_unsupported_smtfloat]),

    (* Native comparison plus arithmetic is first rewritten by the proved
       transfer kit, then answered by Z3 over the SMT FloatingPoint sort. *)
    (``float_less_than
         (SND (float_add roundTiesToEven
           (x:(4,3) binary_ieee$float) y)) z ==>
       ~float_less_equal z
         (SND (float_add roundTiesToEven x y))``,
      [thm_Z3_v4]),

    (* prove that `ediv` and `emod` match Boute's Euclidean definition, i.e.
       that they match SMT-LIB's `Ints` theory's definition of integer div and
       mod *)
    (``!m n. n <> 0 ==>
         let q = ediv m n
         and r = emod m n
         in
           (m = n * q + r /\ 0 <= r /\ r <= (ABS n) - 1)``,
      [(*thm_AUTO,*) thm_CVC, thm_Z3_v4(*, thm_Z3p*)]),

    (* regression tests *)

    (``!(n:num) z y a. (3 * n + 1) * z <= y * a ==> 3 * (n * z) <= 2 * (y * a)``,
      [thm_AUTO, (*thm_CVC,*) thm_Z3(*, thm_Z3p*)]),

    (``Abbrev ((x:num) = 5) ==> x = 5``,
      [thm_AUTO, thm_CVC, thm_Z3, thm_Z3p_v4, thm_CVCp]),

    (``!(x:real). 2 <= x /\ x <= 3 ==>
      0 < x - (x pow 3) / 6 + (x pow 5) / 120 - (x pow 7) / 5040``,
        [(*thm_AUTO, thm_CVC,*) thm_Z3_v4(*, thm_Z3p_v4*)]),

    (* Nested CPC applications in congruence sources. *)
    (``(if c then (f:int->int) else g) a = 1 ==> c ==> f a = 1``,
      [thm_CVCp_ho]),
    (``(r:smt_fun_rec).smt_fun a b = 1 ==> r = q ==>
       (q:smt_fun_rec).smt_fun a b = 1``, [thm_CVCp_ho])


  ]  (* tests *)
end

(*****************************************************************************)
(* actually perform tests                                                    *)
(*****************************************************************************)

(* Optional sharding.  HOL4_SELFTEST_SHARD="k/N" runs only the k-th (0-based)
   slice of the functional tests; N fresh `selftest.exe` processes then cover
   the whole suite in parallel.  Each process keeps its Poly/ML heap to a
   single shard's working set instead of accumulating the entire suite (the
   whole-suite run reaches >200 GB RSS unbounded; a shard stays a few GB).
   Tests are assigned round-robin by index (i mod N = k) so slow cases are
   spread across shards rather than piling into one contiguous block.  The
   fast unit tests run once, in shard 0 (or whenever unsharded). *)
val (shard_k, shard_n) =
  case OS.Process.getEnv "HOL4_SELFTEST_SHARD" of
    NONE => (0, 1)
  | SOME s =>
    (case String.tokens (fn c => c = #"/") s of
       [ks, ns] =>
         (case (Int.fromString ks, Int.fromString ns) of
            (SOME k, SOME n) =>
              if n >= 1 andalso 0 <= k andalso k < n then (k, n)
              else Unittest.die ("Invalid HOL4_SELFTEST_SHARD='" ^ s ^
                "' (need 0 <= k < N, N >= 1)")
          | _ => Unittest.die ("Invalid HOL4_SELFTEST_SHARD='" ^ s ^ "'"))
     | _ => Unittest.die ("Invalid HOL4_SELFTEST_SHARD='" ^ s ^ "'"))

fun keep_shard k n xs =
  let
    fun go _ [] = []
      | go i (x :: rest) =
          if i mod n = k then x :: go (i + 1) rest else go (i + 1) rest
  in
    go 0 xs
  end

val () = if shard_k = 0 then Unittest.run_unittests () else ()

(* Unit tests deliberately reset Profile counters around every case.  Start
   the functional interval explicitly so profiling never depends on which
   unit test happened to run last (and do the same on non-zero shards). *)
val () = Profile.reset_all ()

val functional_profile =
  OS.Process.getEnv "HOL4_SELFTEST_PROFILE" = SOME "1"

val sharded_tests = keep_shard shard_k shard_n tests

val () =
  if shard_n = 1 then print "Running functional tests...\n"
  else print ("Running functional tests (shard " ^ Int.toString shard_k ^
    "/" ^ Int.toString shard_n ^ ", " ^
    Int.toString (length sharded_tests) ^ " cases)...\n")

(* Continue-on-failure.  With HOL4_SELFTEST_KEEP_GOING=1 the suite records
   every failing goal and reports them all at the end, instead of aborting at
   the first failure.  This is what lets a single (sharded) pass enumerate the
   full set of failures.  We enable it by making `Unittest.die` raise `Fail`
   rather than exit (it does so when `Globals.interactive` is set), then catch
   per test.  Default behaviour (fail-fast) is unchanged. *)
val keep_going = OS.Process.getEnv "HOL4_SELFTEST_KEEP_GOING" = SOME "1"
val () = if keep_going then Globals.interactive := true else ()

val failures = ref ([] : string list)

fun run_test term test_fun =
  if keep_going then
    (test_fun term
       handle e =>
         (* A failed `expect_sat` may have left `include_theorems` disabled;
            restore it so the failure does not cascade into later tests. *)
         (SmtLib.include_theorems := true;
          let val msg = exnMessage e in
            failures := msg :: !failures;
            (* Emit the full failure record inline and immediately (not only in
               the end-of-run summary) so a shard later killed mid-run - e.g. by
               a wall-clock timeout - still leaves its failures on disk. *)
            print ("\nFAILED: " ^ msg ^ "\n")
          end);
     (* Flush after every test so a killed shard leaves a complete record of the
        tests it finished, rather than losing block-buffered stdout. *)
     TextIO.flushOut TextIO.stdOut)
  else
    test_fun term

val () =
  List.app
    (fn (term, test_funs) =>
       List.app (fn test_fun => run_test term test_fun) test_funs)
    sharded_tests

(* arith_poly_norm_rel has one E1 coverage terminal.  Keep aggregate handler
   accounting exact so a green suite cannot hide a bypass or a lost family;
   this assertion runs in both normal and no-fastpath modes. *)
fun functional_profile_count name =
  case List.find (fn (candidate, _) => candidate = name)
      (Profile.results ()) of
    SOME (_, info) => #n info
  | NONE => 0

val () =
  let
    val handlers = functional_profile_count
      "CPC(handler:ProofRule/arith_poly_norm_rel)_OK"
    val terminals = functional_profile_count
      "CPC(rung:arith_rel/general)_OK"
    val fragments = functional_profile_count
        "CPC(arith_rel:fragment/cast)_OK" +
      functional_profile_count "CPC(arith_rel:fragment/plain)_OK"
    val dispatches = functional_profile_count
        "CPC(arith_rel:dispatch/declared)" +
      functional_profile_count "CPC(arith_rel:dispatch/omitted)"
  in
    Unittest.assert
      (handlers = terminals andalso handlers = fragments andalso
       handlers = dispatches,
       "arith_poly_norm_rel terminal coverage mismatch: handlers=" ^
       Int.toString handlers ^ ", terminals=" ^ Int.toString terminals ^
       ", fragments=" ^ Int.toString fragments ^ ", dispatches=" ^
       Int.toString dispatches)
  end

fun json_escape s =
  let
    fun escape #"\"" = "\\\""
      | escape #"\\" = "\\\\"
      | escape #"\n" = "\\n"
      | escape #"\r" = "\\r"
      | escape #"\t" = "\\t"
      | escape c = str c
  in
    String.translate escape s
  end

fun profile_json (name, {usr, sys, gc, real, n}) =
  "{\"name\":\"" ^ json_escape name ^ "\",\"usr\":" ^
  Time.toString usr ^ ",\"sys\":" ^ Time.toString sys ^ ",\"gc\":" ^
  Time.toString gc ^ ",\"real\":" ^ Time.toString real ^ ",\"n\":" ^
  Int.toString n ^ "}"

val () =
  if functional_profile then
    (print ("\nHOL4_SELFTEST_PROFILE {\"shard\":{\"index\":" ^
       Int.toString shard_k ^ ",\"count\":" ^ Int.toString shard_n ^
       "},\"profiles\":[" ^
       String.concatWith "," (List.map profile_json (Profile.results ())) ^
       "]}\n");
     TextIO.flushOut TextIO.stdOut)
  else ()

(*****************************************************************************)

val () =
  case List.rev (!failures) of
    [] => print "\n done, all tests successful.\n"
  | fs =>
    (print ("\n\n==== " ^ Int.toString (length fs) ^
      " FUNCTIONAL TEST FAILURE(S) (shard " ^ Int.toString shard_k ^ "/" ^
      Int.toString shard_n ^ ") ====\n");
     (* The individual `FAILED:` lines were already emitted inline as each
        failure occurred (see `run_test`), so we only print the summary count
        here to avoid duplicating them. *)
     OS.Process.exit OS.Process.failure)

val _ = OS.Process.exit OS.Process.success
