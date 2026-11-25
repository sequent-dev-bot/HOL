open HolKernel testutils

(* Fixtures are tracked from construction, before installing any rewrites.
   Keep the independent ordinary engine explicit at comparison sites. *)
structure boolSimps =
struct
  val bool_ss = boolSimps.bool_ss
  val ETA_ss = boolSimps.ETA_ss
end
structure pureSimps =
struct
  val pure_ss = pureSimps.pure_ss
end

(* The ambient default, lifted into the extension engine.  Updates go to
   the ordinary srw_ss, which also invalidates clasimp's derived caches. *)
fun lifted_srw_ss () = (BasicProvers.srw_ss ())

structure SelfTestTactical = Tactical
structure Tactical =
struct
  open SelfTestTactical
  fun VALID tactic goal =
    SelfTestTactical.VALID tactic goal (Context.snapshot())
end
open listTheory optionTheory pred_setTheory

(* check, residual, valid_closes and tactic_fails come from
   linarithCorpus, which states the assertion helpers once for the
   suites that reach linear arithmetic; with_arith_fact below is from
   there too. *)
open linarithCorpus

(* Native pattern indexing preserves the parallel converse predicate. *)
local
  open boolLib boolSyntax
in
fun converse_index_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = new_theory "converseIndexFixture"
        val _ = new_constant ("ci_support",bool)
        val support = ``ci_support``
        val _ = Datatype.Datatype `ci_one = CiOne`
        val singleton = Tactical.prove
          (``!v:ci_one. v = CiOne``,Tactical.EVERY
            [Tactic.GEN_TAC,bossLib.Cases_on `v`,Rewrite.REWRITE_TAC []])
        val x = mk_var ("x",bool)
        fun unary prefix n result = new_definition
          (prefix ^ Int.toString n ^ "_def",
           mk_eq (mk_comb (mk_var (prefix ^ Int.toString n,
                                   bool --> bool),x),result))
        val identity = List.tabulate (8,fn n => unary "ci_i" n x)
        val junk = unary "ci_j" 0 x
        val k = new_definition ("ci_k_def",``ci_k (x:bool) (y:bool) = T``)
        val junk_head = fst (dest_comb (lhs (concl (SPEC x junk))))
        fun chain 0 = x
          | chain n = mk_comb (junk_head,chain (n-1))
        val leaves = map (fn th =>
          let val head = fst (dest_comb (lhs (concl (SPEC x th))))
          in mk_comb (head,chain 80) end) identity
        fun pair [] = []
          | pair [item] = [item]
          | pair (left::right::rest) =
              list_mk_comb (``ci_k``,[left,right])::pair rest
        fun tree [item] = item
          | tree items = tree (pair items)
        val rhs = tree leaves
        val definitions = List.tabulate (50,fn n => unary "ci_g" n T)
        val citations = map (fn th =>
          Tactical.prove (mk_forall (x,mk_eq
            (lhs (concl (SPEC x th)),rhs)),
            Rewrite.REWRITE_TAC (k::definitions))) definitions
        val rigid_arguments = List.tabulate (20,fn n => new_definition
          ("ci_arg" ^ Int.toString n ^ "_def",mk_eq
            (mk_var ("ci_arg" ^ Int.toString n,bool),T)))
        val rigid_rhs = new_definition
          ("ci_rigid_rhs_def",``ci_rigid_rhs = T``)
        val rigid = map (fn argument => Tactical.prove
          (mk_eq (mk_comb (junk_head,lhs (concl argument)),
                  lhs (concl rigid_rhs)),
           Rewrite.REWRITE_TAC [junk,argument,rigid_rhs])) rigid_arguments
        val ambient = simpLib.++
          (pureSimps.pure_ss,simpLib.rewrites
            (singleton::identity @ rigid))
        val rules = clasimpLib.prepare_supplied_rules ambient citations
        val cache = clasimpLib.make_supplied_converse_cache ()
        fun bounded () =
          let val budget = searchBudget.create
                {normalization=SOME 30000,candidates=NONE,applications=NONE}
          in cache
              (fn () => searchBudget.charge budget searchBudget.Normalization)
              ambient rules
          end
        val result = (SOME (bounded (),bounded ()))
          handle searchBudget.LimitReached _ => NONE
        val budget_checks = case result of NONE => [false,false,false]
          | SOME (cold,warm) =>
              let
                val cold_stats = clasimpLib.supplied_converse_stats cold
                val warm_stats = clasimpLib.supplied_converse_stats warm
                val _ = print ("CONVERSE_INDEX_UNITS " ^
                  Int.toString (#normalization cold_stats) ^ " " ^
                  Int.toString (#normalization warm_stats) ^ "\n")
                val state = clasimpLib.make_bound_simplification I
                  (fn () => raise Fail "unexpected view construction") cold
                val head = fst (dest_comb
                  (lhs (concl (SPEC x (hd identity)))))
                val goal = ([support],mk_comb (head,support))
                val (remaining,validate) = SelfTestTactical.VALID
                  (clasimpLib.asm_full_simp_bound false state []) goal
                  (Context.snapshot ())
                val theorem = validate (map (fn residual =>
                  Tactical.prove_goal
                    (residual,Rewrite.REWRITE_TAC identity THEN
                     Tactical.FIRST_ASSUM Tactic.ACCEPT_TAC)) remaining)
                val valid = List.all (fn tm => tmem tm [support])
                  (hyp theorem) andalso
                  aconv (concl theorem) (#2 goal)
              in
                [null (clasimpLib.supplied_converse_suspended cold) andalso
                 null (clasimpLib.supplied_converse_suspended warm),
                 #normalization cold_stats = #normalization warm_stats andalso
                 #derived cold_stats = 50 andalso #memoized warm_stats = 50,
                 valid]
              end
        val abs_rule = Tactical.prove
          (``(\x:bool. ci_g0 (ci_i0 x)) = (\x:bool. ci_k x x)``,
           Rewrite.REWRITE_TAC (k::definitions @ identity))
        val abs_ss = simpLib.++ (simpLib.empty_ss,simpLib.rewrites [abs_rule])
        val abs_sources = simpLib.rewrite_source_handles abs_ss
        val reverse = GSYM abs_rule
        val applied = AP_THM reverse ``ci_support``
        fun linear ss arguments =
          let
            val supplied = List.concat (map #2
              (simpLib.rewrite_bundle_rules
                (simpLib.prepare_rewrite_bundle ss arguments)))
            fun matches origin source =
              let
                val theorem = SPEC_ALL (#2 (simpLib.source_rewrite origin))
                val provided = SPEC_ALL (#2 (simpLib.source_rewrite source))
                val (left,right) = dest_eq
                  (#2 (strip_imp_only (concl provided)))
                val result = Conv.QCONV
                  (Conv.ONCE_DEPTH_CONV (Conv.REWR_CONV theorem)) right
              in null (hyp theorem) andalso is_eq (concl theorem) andalso
                 aconv (boolSyntax.rhs (concl result)) left end
              handle HOL_ERR _ => false
          in List.filter (fn origin => List.exists
               (matches origin) supplied) (simpLib.rewrite_source_handles ss) end
        fun indexed ss arguments =
          clasimpLib.supplied_converse_suspended
            ((clasimpLib.make_supplied_converse_cache ()) (fn () => ())
              ss (clasimpLib.prepare_supplied_rules ss arguments))
        fun agrees ss arguments =
          let val expected = linear ss arguments
              val actual = indexed ss arguments
              val _ = print ("CONVERSE_ORACLE " ^
                Int.toString (length expected) ^ " " ^
                Int.toString (length actual) ^ "\n")
          in length expected = length actual andalso List.all
               (fn origin => List.exists
                  (fn other => simpLib.same_rewrite_source (origin,other))
                  actual) expected end
        val shape_checks =
          [List.exists (fn source => is_abs (lhs (concl
             (SPEC_ALL (#2 (simpLib.source_rewrite source)))))) abs_sources,
           not (null (indexed abs_ss [reverse])) andalso agrees abs_ss [reverse],
           agrees abs_ss [applied]]
        val rigid_checks =
          [agrees ambient citations,
           not (null (indexed ambient [GSYM (hd rigid)])) andalso
             agrees ambient [GSYM (hd rigid)],
           let val ss = simpLib.++
                 (simpLib.empty_ss,simpLib.rewrites [singleton])
           in not (null (indexed ss [GSYM singleton])) andalso
                agrees ss [GSYM singleton] end]
        val checks = budget_checks @ shape_checks @ rigid_checks
        val _ = print ("CONVERSE_INDEX_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all I checks end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ = (tprint "native converse detection reuses RHS subtree inventories";
         if converse_index_fixture () then OK ()
         else die "converse detection exhausted an indexed binding budget");

end

(* Prepared inputs retain tactic controls without turning them into rules. *)
fun bound_input_controls_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
  let
    val _ = new_theory "inputControlsFixture"
    val _ = new_constant ("input_control_p",bool)
    val _ = new_constant ("input_control_q",bool)
    val f = new_definition
      ("input_control_f_def", ``input_control_f (x:bool) = T``)
    val g = new_definition
      ("input_control_g_def", ``input_control_g (x:bool) (y:bool) = T``)
    val i = new_definition
      ("input_control_i_def", ``input_control_i (x:bool) = T``)
    val o_def = new_definition
      ("input_control_o_def", ``input_control_o (x:bool) = T``)
    val proposition = Parse.Term [QUOTE "input_control_p"]
    val target = ``input_control_f input_control_p``
    val rewritten = ``input_control_f T``
    val goal = ([proposition],target)
    val ss = pureSimps.pure_ss
    fun checked tactic (original as (assumptions,target)) =
      let
        val (goals,validate) = SelfTestTactical.VALID tactic original
          (Context.snapshot ())
        val theorem = validate (map (fn residual =>
          Tactical.prove_goal
            (residual,Rewrite.REWRITE_TAC [f,g,i,o_def])) goals)
        val _ = if aconv (concl theorem) target andalso
                   List.all (fn tm => boolSyntax.tmem tm assumptions)
                     (hyp theorem) then ()
                else raise Fail "input control validation"
      in goals end
    fun retained tactic = case checked tactic goal of
        [(assumptions,result)] => aconv result target andalso
          boolSyntax.tmem proposition assumptions
      | _ => false
    val ordinary = case checked (clasimpLib.asm_full_simp ss []) goal of
        [(_,result)] => aconv result rewritten
      | _ => false
    val ignored = markerLib.IgnAsm [QUOTE "input_control_p"]
    val unsafe = retained
      (clasimpLib.asm_full_simp ss [markerLib.NoAsms])
    val safe = retained
      (clasimpLib.safe_asm_full_simp ss [markerLib.NoAsms])
    val bound = clasimpLib.prepare_bound_simplification
      traceUtil.silent I (fn () => ()) ss [markerLib.NoAsms]
    val raw = retained (clasimpLib.asm_full_simp_bound false bound [])
    val selected = retained (clasimpLib.asm_full_simp ss [ignored])
    val viewed = retained (clasimpLib.asm_full_simp_bound true bound [])
    val extra = retained (clasimpLib.asm_full_simp_bound false
      (clasimpLib.prepare_bound_simplification
        traceUtil.silent I (fn () => ()) ss [])
      [markerLib.NoAsms])
    val selective_goal = ([proposition,``input_control_q``],
      ``input_control_g input_control_p input_control_q``)
    val selective = case checked
      (clasimpLib.asm_full_simp ss [ignored]) selective_goal of
        [(_,result)] => aconv result ``input_control_g input_control_p T``
      | _ => false
    val mutual_goal = ([proposition,
      ``input_control_g input_control_p input_control_q``],
      ``input_control_f input_control_q``)
    val mutual = case checked
      (clasimpLib.asm_full_simp ss [markerLib.NoAsms]) mutual_goal of
        [(asms,result)] => aconv result (#2 mutual_goal) andalso
          boolSyntax.tmem (hd (tl (#1 mutual_goal))) asms
      | _ => false
    val conditional = DISCH proposition
      (SPEC ``input_control_q`` f)
    val conditional_goal = ([proposition],``input_control_f input_control_q``)
    val supplied = case checked (clasimpLib.asm_full_simp ss
      [markerLib.NoAsms,conditional]) conditional_goal of
        [(_,result)] => aconv result (#2 conditional_goal)
      | _ => false
    val conditional_control = null
      (checked (clasimpLib.asm_full_simp ss [conditional]) conditional_goal)
    val name = "input_control_abbreviated"
    val abbreviation = markerSyntax.mk_abbrev (name,proposition)
    val abbr_goal = ([abbreviation],
      mk_comb (``input_control_f``,mk_var (name,bool)))
    val abbreviated = case checked (clasimpLib.asm_full_simp ss
      [markerLib.Abbr [QUOTE name],markerLib.NoAsms]) abbr_goal of
        [(_,result)] => aconv result target
      | _ => false
    val forward = Tactical.prove
      (``!x. input_control_i x = input_control_o x``,
       Rewrite.REWRITE_TAC [i,o_def])
    val labelled = markerLib.MK_LABEL ("input-control",forward)
    val labelled_goal = ([concl labelled],
      ``input_control_f (input_control_i input_control_p)``)
    val label_ss = simpLib.++ (ss,simpLib.rewrites [boolLib.GSYM forward])
    val label = (case checked (clasimpLib.asm_full_simp label_ss
      [markerLib.L "input-control",markerLib.NoAsms]) labelled_goal of
        [(_,result)] => aconv result
          ``input_control_f (input_control_o input_control_p)``
      | _ => false) handle searchBudget.LimitReached _ => false
    val safe_label = (case checked (clasimpLib.safe_asm_full_simp label_ss
      [markerLib.L "input-control",markerLib.NoAsms]) labelled_goal of
        [(_,result)] => aconv result
          ``input_control_f (input_control_o input_control_p)``
      | _ => false) handle searchBudget.LimitReached _ => false
    val checks = [ordinary,unsafe,safe,raw,selected,viewed,extra,selective,
                  mutual,supplied,conditional_control,abbreviated,label,
                  safe_label]
    val _ = print ("INPUT_CONTROL_RESULTS " ^
      String.concatWith " " (map Bool.toString checks) ^ "\n")
  in List.all I checks end;

  in Portable.finally (fn () => Context.restore saved) run () end;

val _ =
  (tprint "bound public simplification retains tactic directives";
   if bound_input_controls_fixture () then OK ()
   else die "a bound tactic directive was lost");

(* Public citations retain their direction against an ambient converse. *)
fun public_binding_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = new_theory "publicBindingFixture"
        val g = new_definition ("pb_g_def", ``pb_g (x:bool) = T``)
        val h = new_definition ("pb_h_def", ``pb_h (x:bool) = T``)
        val p = new_definition ("pb_p_def", ``pb_p (x:bool) = T``)
        val _ = new_constant ("pb_support",bool)
        fun proof tm = Tactical.prove
          (tm,Rewrite.REWRITE_TAC [g,h,p])
        val forward = proof ``!x. pb_g x = pb_h x``
        val backward = proof ``!x. pb_h x = pb_g x``
        val fact = Drule.ADD_ASSUM ``pb_support:bool``
          (proof ``!x. pb_p (pb_h x)``)
        val goal = ([``pb_support:bool``],``pb_p (pb_g x)``)
        val compiles = ref 0
        fun record (item as (theorem,_)) =
          let
            val (_,equation) = boolSyntax.strip_imp_only
              (concl (Drule.SPEC_ALL theorem))
            val (left,right) = boolSyntax.dest_eq equation
            val _ = if null (hyp theorem) andalso
                       aconv (fst (strip_comb left)) ``pb_g`` andalso
                       aconv (fst (strip_comb right)) ``pb_h``
                    then compiles := !compiles + 1 else ()
          in [item] end handle HOL_ERR _ => [item]
        val _ = BasicProvers.augment_srw_ss
          [simpLib.named_rewrites "public_binding_converse" [backward],
           simpLib.SSFRAG
             {name=SOME "public_binding_compile",convs=[],rewrs=[],
              ac=[],dprocs=[],congs=[],filter=SOME record}]
        val checked_valid = ref false
        fun checked tactic (original as (assumptions,target)) =
          let
            val _ = checked_valid := false
            val (remaining,validate) = Tactical.VALID tactic original
            val proofs = map
              (fn residual => Tactical.prove_goal
                (residual,Rewrite.REWRITE_TAC [g,h,p])) remaining
            val theorem = validate proofs
            val _ = if aconv (concl theorem) target andalso
                       List.all (fn tm => boolSyntax.tmem tm assumptions)
                         (hyp theorem) then ()
                    else raise Fail "public binding validation"
            val _ = checked_valid := true
          in null remaining end
          handle HOL_ERR _ => false | searchBudget.LimitReached _ => false
        fun budget () = searchBudget.create
          {candidates=SOME 10000,applications=SOME 1000,
           normalization=SOME 10000}
        fun exercise (make_tactic,wrap) =
          let val prefix = !compiles
              val closed = checked (make_tactic (budget ())
                [wrap forward,fact]) goal
          in [closed,!compiles = prefix + 1] end
        val budgeted = List.concat (map exercise
          [(clasimpLib.FORCE_TAC_BUDGETED,I),
           (clasimpLib.CLARSIMP_TAC_BUDGETED,I),
           (clasimpLib.FORCE_TAC_BUDGETED,clasetLib.Simp),
           (clasimpLib.CLARSIMP_TAC_BUDGETED,clasetLib.Simp)])
        fun public make_tactic =
          let val prefix = !compiles
              val closed = checked
                (make_tactic [clasetLib.Simp forward,fact]) goal
          in [closed,!compiles = prefix + 1] end
        val defaults = List.concat (map public
          [clasimpLib.AUTO_TAC,clasimpLib.FORCE_TAC,
           clasimpLib.FASTFORCE_TAC,clasimpLib.SLOWSIMP_TAC,
           clasimpLib.BESTSIMP_TAC,clasimpLib.CLARSIMP_TAC])
        fun observed ss = simpLib.++ (ss,simpLib.SSFRAG
          {name=NONE,convs=[],rewrs=[],ac=[],dprocs=[],congs=[],
           filter=SOME record})
        val converse = observed (simpLib.++
          (boolSimps.bool_ss,simpLib.rewrites [backward]))
        fun direct make_tactic =
          let val prefix = !compiles
              val closed = checked (make_tactic converse [forward,fact]) goal
          in [closed,!compiles = prefix + 1] end
        val standalone = List.concat (map direct
          [clasimpLib.asm_full_simp,clasimpLib.safe_asm_full_simp])
        fun explicit make_tactic =
          let
            val ss = simpLib.++ (observed boolSimps.bool_ss,
              simpLib.rewrites [BoundedRewrites.Once forward,fact])
            val closed = checked (make_tactic clasetLib.empty_cs ss) goal
            val exhausted = not (checked (simpLib.SIMP_TAC ss [])
              ([``pb_support:bool``],``pb_g x = pb_h x``))
          in [closed,exhausted] end
        val contextual = List.concat (map explicit
          [clasimpLib.CS_AUTO_TAC {blast=0,depth=0},clasimpLib.CS_FORCE_TAC,
           clasimpLib.CS_FASTFORCE_TAC,clasimpLib.CS_SLOWSIMP_TAC,
           clasimpLib.CS_BESTSIMP_TAC,clasimpLib.CS_CLARSIMP_TAC])
        fun quota make_tactic =
          let
            val prefix = !compiles
            val closed = checked (make_tactic
              [clasetLib.Simp (BoundedRewrites.Once forward),fact])
              ([``pb_support:bool``],``pb_p (pb_g x) /\ pb_p (pb_g y)``)
          in [!checked_valid andalso not closed,!compiles = prefix + 1] end
        val limited = List.concat (map quota
          [clasimpLib.AUTO_TAC,clasimpLib.CLARSIMP_TAC])
        fun adapter make_tactic arguments =
          clasimpLib.process_clasimp_args
            (fn cs => fn ss => fn _ => make_tactic cs ss)
            clasetLib.empty_cs converse arguments
        fun bridge make_tactic =
          let val prefix = !compiles
              val closed = checked (adapter make_tactic
                [clasetLib.Simp forward,fact]) goal
          in [closed,!compiles = prefix + 1] end
        val adapters = List.concat (map bridge
          [clasimpLib.CS_AUTO_TAC {blast=0,depth=0},clasimpLib.CS_FORCE_TAC,
           clasimpLib.CS_FASTFORCE_TAC,clasimpLib.CS_SLOWSIMP_TAC,
           clasimpLib.CS_BESTSIMP_TAC,clasimpLib.CS_CLARSIMP_TAC])
        fun bridge_quota make_tactic =
          let val prefix = !compiles
              val closed = checked (adapter make_tactic
                [clasetLib.Simp (BoundedRewrites.Once forward),fact])
                ([``pb_support:bool``],``pb_p (pb_g x) /\ pb_p (pb_g y)``)
          in [!checked_valid andalso not closed,!compiles = prefix + 1] end
        val adapter_limits = List.concat (map bridge_quota
          [clasimpLib.CS_AUTO_TAC {blast=0,depth=0},
           clasimpLib.CS_CLARSIMP_TAC])
        fun control_bridge arguments target =
          let val prefix = !compiles
              val closed = checked (adapter clasimpLib.CS_CLARSIMP_TAC
                arguments) target
          in [!checked_valid,closed,!compiles = prefix + 1] end
        val control_use = control_bridge
          [BoundedRewrites.Once forward,fact] goal
        val control_limit = control_bridge
          [BoundedRewrites.Once forward,fact]
          ([``pb_support:bool``],``pb_p (pb_g x) /\ pb_p (pb_g y)``)
        val replay_prefix = !compiles
        val replay_closed = checked
          (adapter (fn cs => fn ss => Tactical.THEN
            (Tactical.TRY (clasimpLib.CS_CLARSIMP_TAC cs ss),
             Tactical.TRY (clasimpLib.CS_CLARSIMP_TAC cs ss)))
            [BoundedRewrites.Once forward,fact])
          ([``pb_support:bool``],``pb_p (pb_g x) /\ pb_p (pb_g y)``)
        val replay = [!checked_valid andalso not replay_closed,
                      !compiles = replay_prefix + 1]
        fun nested exception_case =
          clasimpLib.process_clasimp_args
            (fn cs => fn ss => fn _ => fn inner => fn ctxt =>
              let
                val child = clasimpLib.process_clasimp_args
                  (fn _ => fn _ => fn _ =>
                    if exception_case then
                      (fn _ => fn _ => raise Fail "adapter child")
                    else Tactical.ALL_TAC)
                  clasetLib.empty_cs boolSimps.bool_ss []
                val _ = (ignore (child inner ctxt)
                         handle Fail "adapter child" => ())
              in clasimpLib.CS_CLARSIMP_TAC cs ss inner ctxt end)
            clasetLib.empty_cs converse [clasetLib.Simp forward,fact]
        fun escaped exception_case =
          let
            val captured = ref converse
            val packaging = clasimpLib.process_clasimp_args
              (fn _ => fn ss => fn _ =>
                (captured := ss;
                 if exception_case then
                   (fn _ => fn _ => raise Fail "adapter escape")
                 else Tactical.ALL_TAC))
              clasetLib.empty_cs converse [clasetLib.Simp forward,fact]
            val _ = (ignore (residual packaging goal)
                     handle Fail "adapter escape" => ())
          in not (checked
               (clasimpLib.CS_CLARSIMP_TAC clasetLib.empty_cs (!captured))
               goal) end
        val scopes = [checked (nested false) goal,checked (nested true) goal,
                      escaped false,escaped true]
        val bridge_checks = adapters @ adapter_limits @
          control_use @ [hd control_limit,not (hd (tl control_limit)),
                         List.last control_limit] @ replay @ scopes
        val _ = print ("ADAPTER_BINDING_RESULTS " ^
          String.concatWith " " (map Bool.toString bridge_checks) ^ "\n")
        val checks = budgeted @ defaults @ standalone @ contextual @ limited
        val _ = print ("PUBLIC_BINDING_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all I (checks @ bridge_checks) end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ = (tprint "public tactics bind citations before converse reduction";
         if public_binding_fixture () then OK ()
         else die "public citation loses direction or compiles again");


(* A selftest binary starts with no theory segment open, so a datatype
   has nowhere to be declared until one is. *)
val _ = Theory.new_theory "clasimpHookSelftest"

val budget_cycle_left_def =
  new_definition
    ("budget_cycle_left_def", ``budget_cycle_left = T``)
val budget_cycle_right_def =
  new_definition
    ("budget_cycle_right_def", ``budget_cycle_right = T``)
val budget_cycle_lr =
  Tactical.prove
    (``budget_cycle_left <=> budget_cycle_right``,
     Rewrite.REWRITE_TAC
       [budget_cycle_left_def, budget_cycle_right_def])
val budget_cycle_rl =
  Tactical.prove
    (``budget_cycle_right <=> budget_cycle_left``,
     Rewrite.REWRITE_TAC
       [budget_cycle_left_def, budget_cycle_right_def])

(* clasimpLib is loaded before this selftest unit, so this datatype exercises
   the live TypeBase hook rather than the registration catch-up sweep. *)
val _ = Datatype.Datatype
  `clasimp_hook_after_load = ClasimpHookAfter bool bool`

fun same_goals left right =
  ListPair.allEq
    (fn (goal1, goal2) => boolSyntax.goal_eq goal1 goal2)
    (left, right)

val solver_ss = simpLib.clear_rules (clasimpLib.clasimp_ss ())
val safe_simp = clasimpLib.safe_asm_full_simp solver_ss []

val _ =
  check
    ("CLARSIMP reports a zero normalization budget before traversal",
     fn () =>
       let
         val budget =
           searchBudget.create
             {candidates = NONE, applications = NONE,
              normalization = SOME 0}
       in
         ((ignore
             (Tactical.VALID
                (clasimpLib.CLARSIMP_TAC_BUDGETED budget [])
                ([], ``T ∧ T``));
           false)
          handle searchBudget.LimitReached
                   (searchBudget.Normalization, used) =>
                   #normalization used = 0
               | _ => false)
       end)

val _ =
  check
    ("CLARSIMP charges its invocation normalization budget",
     fn () =>
       let
         val budget = searchBudget.unbounded ()
         val _ =
           Tactical.VALID
             (clasimpLib.CLARSIMP_TAC_BUDGETED budget [])
             ([], ``T ∧ T``)
       in
         #normalization (searchBudget.usage budget) > 0
       end)

val nested_arith_budget_goal : Abbrev.goal =
  ([``(budget_a:num) <= budget_b``,
    ``budget_b <= budget_c``],
   ``budget_a <= budget_c``)

val _ =
  check
    ("CLARSIMP charges nested arithmetic to its invocation",
     fn () =>
       let
         val funded = searchBudget.unbounded ()
         val closed =
           valid_closes
             (clasimpLib.CLARSIMP_TAC_BUDGETED funded [])
             nested_arith_budget_goal
         val used = searchBudget.usage funded
         val zero =
           searchBudget.create
             {candidates = SOME 0, applications = NONE,
              normalization = NONE}
         val cutoff =
           ((ignore
               (Tactical.VALID
                 (clasimpLib.CLARSIMP_TAC_BUDGETED zero [])
                 nested_arith_budget_goal);
             false)
            handle searchBudget.LimitReached
                     (searchBudget.Candidate, usage) =>
                     #candidates usage = 0
                 | _ => false)
       in
         closed andalso #candidates used > 0 andalso cutoff
       end)

val _ =
  check
    ("CLARSIMP charges literal fact insertion to its invocation",
     fn () =>
       let
         val budget =
           searchBudget.create
             {candidates = NONE, applications = SOME 0,
              normalization = NONE}
       in
         ((ignore
             (Tactical.VALID
                (clasimpLib.CLARSIMP_TAC_BUDGETED budget
                   [boolTheory.TRUTH])
                ([], ``T``));
           false)
          handle searchBudget.LimitReached
                   (searchBudget.Application, used) =>
                   #applications used = 0
               | _ => false)
       end)

val _ =
  check
    ("cyclic simp rules report a typed normalization limit",
     fn () =>
       let
         val budget =
           searchBudget.create
             {candidates = NONE, applications = NONE,
              normalization = SOME 100}
       in
         ((ignore
             (Tactical.VALID
                (clasimpLib.CLARSIMP_TAC_BUDGETED budget
                   [budget_cycle_lr, budget_cycle_rl])
                ([], ``budget_cycle_left``));
           false)
          handle searchBudget.LimitReached
                   (searchBudget.Normalization, used) =>
                   #normalization used = 100
               | _ => false)
       end)

val _ =
  check
    ("safe solver accepts an alpha-matching assumption",
     fn () =>
       valid_closes safe_simp
         ([``(\x:'a. P x) a : bool``], ``(\y:'a. P y) a : bool``))

val _ =
  check
    ("safe solver proves an alpha-reflexive equality",
     fn () =>
       valid_closes safe_simp
         ([], ``(\x:'a. f x) = (\y:'a. f y)``))

val _ =
  check
    ("safe solver proves truth",
     fn () => valid_closes safe_simp ([], boolSyntax.T))

val _ =
  check
    ("safe solver closes from a false assumption",
     fn () =>
       valid_closes safe_simp
         ([boolSyntax.F], ``clasimp_false_goal:bool``))

val _ =
  check
    ("safe solver does not instantiate an existential witness",
     fn () =>
       case residual safe_simp
         ([``P (clasimp_witness:'a) : bool``], ``?x:'a. P x``) of
           [goal] =>
             boolSyntax.goal_eq
               goal
                 ([``P (clasimp_witness:'a) : bool``], ``?x:'a. P x``)
         | _ => false)

val _ =
  check
    ("conditional witnesses retain every context theorem's support",
     fn () =>
       let
         val left = ``clasimp_witness_p (3:num) : bool``
         val right = ``clasimp_witness_q (3:num) : bool``
         val condition =
           ``?n:num. clasimp_witness_p n /\ clasimp_witness_q n``
         fun prove context_thms =
           clasimpLib.witness_subgoaler
             {stack = [],
              context_thms = context_thms,
              recurse = Thm.REFL} condition
         val proved = prove [Thm.ASSUME left, Thm.ASSUME right]
         val missing = prove [Thm.ASSUME left]
         val hypotheses = Thm.hyp proved
       in
         Term.aconv (Thm.concl proved)
           (boolSyntax.mk_eq (condition, boolSyntax.T)) andalso
         length hypotheses = 2 andalso
         List.exists (Term.aconv left) hypotheses andalso
         List.exists (Term.aconv right) hypotheses andalso
         Term.aconv (Thm.concl missing)
           (boolSyntax.mk_eq (condition, condition))
       end)

val _ =
  check
    ("conditional witness matching follows nested conjunctions",
     fn () =>
       let
         val condition =
           ``((?n:num. witness_p n) /\ witness_q) /\ witness_r``
         val assumption =
           ``(witness_p (3:num) /\ witness_q) /\ witness_r``
         val result =
           clasimpLib.witness_subgoaler
             {stack = [], context_thms = [Thm.ASSUME assumption],
              recurse = Thm.REFL} condition
       in
         Term.aconv (Thm.concl result)
           (boolSyntax.mk_eq (condition, boolSyntax.T))
       end)

val _ =
  check
    ("eta-short applications alone do not trigger witness matching",
     fn () =>
       let
         val condition =
           ``($? (witness_p : num -> bool)) /\ ($? (witness_q : num -> bool))``
         val context =
           {stack = [], recurse = Thm.REFL,
            context_thms =
              [Thm.ASSUME ``witness_p (3:num) /\ witness_q (4:num)``]}
         val budget = searchBudget.unbounded ()
         val result =
           clasimpLib.witness_subgoaler_budgeted budget context condition
         val usage = searchBudget.usage budget
       in
         not (Lib.can (HolKernel.find_term boolSyntax.is_exists) condition)
         andalso Term.aconv (Thm.concl result)
           (boolSyntax.mk_eq (condition, condition))
         andalso #normalization usage = 1 andalso #candidates usage = 0
       end)

val _ =
  check
    ("opaque conditional witnesses retain the normalization charge",
     fn () =>
       let
         val condition = ``witness_q \/ ((?n:num. witness_p n) /\ witness_r)``
         val context = {stack = [], context_thms = [], recurse = Thm.REFL}
         val used = searchBudget.unbounded ()
         val zero =
           searchBudget.create
             {candidates = NONE, applications = NONE,
              normalization = SOME 0}
         val result =
           clasimpLib.witness_subgoaler_budgeted used context condition
         val usage = searchBudget.usage used
       in
         Term.aconv (Thm.concl result)
           (boolSyntax.mk_eq (condition, condition)) andalso
         #normalization usage = 1 andalso #candidates usage = 0 andalso
         #applications usage = 0 andalso
         ((ignore
             (clasimpLib.witness_subgoaler_budgeted zero context condition);
           false)
          handle searchBudget.LimitReached
                   (searchBudget.Normalization, usage) =>
                   #normalization usage = 0
               | _ => false)
       end)

val _ =
  check
    ("witness matching charges candidates inside one condition",
     fn () =>
       let
         val condition = ``?n:num. witness_budget_p n : bool``
         val context =
           {stack = [],
            context_thms =
              [Thm.ASSUME ``witness_budget_p (3:num) : bool``],
            recurse = Thm.REFL}
         val zero =
           searchBudget.create
             {candidates = SOME 0, applications = NONE,
              normalization = NONE}
         val used = searchBudget.unbounded ()
         val _ =
           clasimpLib.witness_subgoaler_budgeted used
             context condition
       in
         #candidates (searchBudget.usage used) > 0 andalso
         #normalization (searchBudget.usage used) > 0 andalso
         #applications (searchBudget.usage used) > 0 andalso
         ((ignore
             (clasimpLib.witness_subgoaler_budgeted zero
                context condition);
           false)
          handle searchBudget.LimitReached
                   (searchBudget.Candidate, usage) =>
                   #candidates usage = 0
               | _ => false)
       end)

val _ =
  check
    ("witness matching skips plain conditions without charging candidates",
     fn () =>
       let
         val condition = ``witness_budget_p (4:num) : bool``
         val context =
           {stack = [],
            context_thms =
              [Thm.ASSUME ``witness_budget_p (3:num) : bool``],
            recurse = Thm.REFL}
         val budget =
           searchBudget.create
             {candidates = SOME 0, applications = NONE,
              normalization = NONE}
         val reduction =
           clasimpLib.witness_subgoaler_budgeted budget context condition
       in
         Term.aconv (Thm.concl reduction)
           (boolSyntax.mk_eq (condition, condition)) andalso
         #candidates (searchBudget.usage budget) = 0
       end)

(* A plain conditional citation must remain available to the safe
   simplifier even if unsafe search also compiles a rule view of it. *)
val invocation_q_def =
  new_definition
    ("invocation_q_def", ``invocation_q (x:'a) <=> T``)
val invocation_implication =
  Tactical.prove
    (``!x:'a. invocation_p x ==> invocation_q x``,
     Rewrite.REWRITE_TAC [invocation_q_def])
val invocation_goal =
  ([``invocation_p (a:'a):bool``], ``invocation_q (a:'a)``)
fun invocation_closes tactic =
  null (residual tactic invocation_goal) handle HOL_ERR _ => false

val _ =
  check
    ("CLARSIMP_TAC uses a directly supplied conditional fact",
     fn () =>
       invocation_closes
         (Tactical.THEN
           (Tactic.ASSUME_TAC invocation_implication,
            clasimpLib.CLARSIMP_TAC [])) andalso
       invocation_closes
         (clasimpLib.CLARSIMP_TAC [invocation_implication]))

val _ =
  check
    ("the conditional citation does not add unsafe CLARSIMP search",
     fn () =>
       let
         val target = ``invocation_q (a:'a)``
         val result =
           SOME
             (residual
               (clasimpLib.CLARSIMP_TAC [invocation_implication])
               ([], target))
           handle HOL_ERR _ => NONE
       in
         case result of
             SOME [(assumptions, remaining)] =>
               null assumptions andalso aconv remaining target
           | _ => false
       end)

val _ =
  check
    ("AUTO_DEPTH_TAC simplifies with a supplied conditional fact",
     fn () =>
       invocation_closes
         (clasimpLib.AUTO_DEPTH_TAC {blast = 0, depth = 0}
            [invocation_implication]))

(* The first cited rewrite exposes the bool-typed application of the
   second.  The initial target has no application of invocation_id, so
   an initial-goal-only literal specialization cannot supply that view. *)
val invocation_id_def =
  new_definition ("invocation_id_def", ``invocation_id (x:'a) = x``)
val invocation_bridge_def =
  new_definition
    ("invocation_bridge_def",
     ``invocation_bridge (n:num) = invocation_id T``)
val invocation_id_fact =
  Tactical.prove
    (``!x:'a. invocation_id x = x``,
     Rewrite.REWRITE_TAC [invocation_id_def])
val invocation_bridge_fact =
  Tactical.prove
    (``!n:num. invocation_bridge n = invocation_id T``,
     Rewrite.REWRITE_TAC [invocation_bridge_def])

val _ =
  check
    ("CLARSIMP_TAC uses a fact after another fact exposes its type",
     fn () =>
       let
         val goal = ([], ``invocation_bridge 0 = T``)
         fun closes facts =
           valid_closes (clasimpLib.CLARSIMP_TAC facts) goal
             handle HOL_ERR _ => false
       in
         not (closes [invocation_bridge_fact]) andalso
         not (closes [invocation_id_fact]) andalso
         closes [invocation_bridge_fact, invocation_id_fact]
       end)

val _ =
  check
    ("AUTO simplification uses a fact at a type exposed by another",
     fn () =>
       let
         val goal = ([], ``invocation_bridge 0 = T``)
         fun closes facts =
           valid_closes
             (clasimpLib.AUTO_DEPTH_TAC {blast = 0, depth = 0} facts)
             goal
             handle HOL_ERR _ => false
       in
         not (closes [invocation_bridge_fact]) andalso
         not (closes [invocation_id_fact]) andalso
         closes [invocation_bridge_fact, invocation_id_fact]
       end)

val _ =
  check
    ("clasimpset fixes conditional-rewrite depth at forty",
     fn () =>
       #cond_depth
         (simpLib.traverseconfig_for_ss (clasimpLib.clasimp_ss ())) =
       SOME 40)

val _ =
  check
    ("clasimpset carries the splitter",
     fn () =>
       let
         val original =
           ``P (if clasimp_split_b then clasimp_split_x:'a
               else clasimp_split_y) : bool``
       in
         case residual
           (simpLib.SIMP_TAC (clasimpLib.clasimp_ss ()) [])
           ([], original) of
             [([], result)] =>
               not (aconv result original) andalso
               not (can (find_term boolSyntax.is_cond) result)
           | _ => false
       end)

val derived_lhs = ``clasimp_derived_lhs:'a``
val derived_rhs = ``clasimp_derived_rhs:'a``
val derived_rule = ASSUME (boolSyntax.mk_eq (derived_lhs, derived_rhs))
val derived_before =
  Conv.QCONV
    (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) []) derived_lhs

(* The extra rewrite is scoped to this one probe: the tests below run
   against the ambient simpsets, and a rewrite with a live hypothesis left
   in srw_ss would make an unrelated one fail for an unrelated reason. *)
val derived_after =
  BasicProvers.with_simpset_updates
    (fn ss =>
      simpLib.++
        (ss, simpLib.named_rewrites "clasimp-selftest-derived"
               [derived_rule]))
    (fn () =>
      Conv.QCONV
        (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) []) derived_lhs)
    ()

val derived_restored =
  Conv.QCONV
    (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) []) derived_lhs

val _ =
  check
    ("clasimpset cache recomputes around a simpset update",
     fn () =>
       aconv (snd (boolSyntax.dest_eq (concl derived_before)))
         derived_lhs andalso
       aconv (snd (boolSyntax.dest_eq (concl derived_after)))
         derived_rhs andalso
       aconv (snd (boolSyntax.dest_eq (concl derived_restored)))
         derived_lhs)

(* A recursive equation whose right-hand side is a conditional is the
   ordinary way to state an interval or an iteration.  Under HOL4's
   COND_CONG the simplifier enters the then-branch with the test
   assumed, and the test is exactly what licenses the next unfolding, so
   the rewriting never stops.  The weak congruence this layer installs
   simplifies the test alone, so one unfolding is the normal form: the
   expected right-hand side below still carries the recursive call.  The
   budget is what keeps a regression a failure rather than a hang. *)
val recursion =
  ASSUME
    ``!item.
        clasimp_iterate item =
          if clasimp_test item then clasimp_iterate (clasimp_step item)
          else clasimp_base``

val recursion_step = Drule.SPEC_ALL recursion

val recursion_unfolded =
  Lib.total
    (Timeout.apply (Time.fromSeconds 30)
       (Conv.QCONV
          (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) [recursion])))
    (boolSyntax.lhs (concl recursion_step))

val _ =
  check
    ("a conditional recursion unfolds once, not forever",
     fn () =>
       case recursion_unfolded of
           NONE => false
         | SOME theorem =>
             aconv (boolSyntax.rhs (concl theorem))
               (boolSyntax.rhs (concl recursion_step)))

(* And it reports an absent CONG fragment rather than replacing nothing:
   a simpset that kept the strong congruence under the weakened name
   would unfold forever again, silently. *)
val _ =
  check
    ("weakening reports a simpset with no conditional congruence",
     fn () =>
       (ignore (clasimpLib.weaken_cond_congruence simpLib.empty_ss);
        false)
       handle HOL_ERR error =>
                Feedback.top_function_of error = "weaken_cond_congruence"
            | Conv.UNCHANGED => false)

val mutual_goal =
  ([``P (a:'a) : bool``, ``a:'a = b``], ``mutual_q:bool``)
val mutual_expected =
  [([``P (b:'a) : bool``, ``a:'a = b``], ``mutual_q:bool``)]

val _ =
  check
    ("asm_full_simp uses later assumptions mutually",
     fn () =>
       same_goals
         (residual
            (clasimpLib.asm_full_simp boolSimps.bool_ss [])
            mutual_goal)
         mutual_expected)

val chain_goal =
  ([``(f:'a -> 'b) x = g x``, ``(g:'a -> 'b) x = z``,
    ``R ((f:'a -> 'b) x) : bool``], ``chain_s:bool``)
val chain_expected =
  [([``(f:'a -> 'b) x = z``, ``(g:'a -> 'b) x = z``,
     ``R (z:'b) : bool``], ``chain_s:bool``)]

val _ =
  check
    ("asm_full_simp closes a three-assumption mutual chain",
     fn () =>
       same_goals
         (residual
            (clasimpLib.asm_full_simp boolSimps.bool_ss [])
            chain_goal)
         chain_expected)

(* A source result states its premises as the antecedents of its
   conclusion, and mut_impc is mutual over exactly those.  Here the
   first antecedent is the one [LENGTH_TAKE] applies to and the second
   is its side condition, so the implication congruence -- which offers
   an antecedent only the ones before it -- leaves the goal standing. *)
val antecedent_goal =
  ([] : term list,
   ``LENGTH (TAKE n (l:'a list)) = k ==> n <= LENGTH l ==> n = k``)

val _ =
  check
    ("asm_full_simp simplifies an antecedent with the ones after it",
     fn () =>
       valid_closes
         (clasimpLib.asm_full_simp (clasimpLib.clasimp_ss ()) [])
         antecedent_goal)

val _ =
  check
    ("the ambient simplifier alone leaves that goal standing",
     fn () =>
       same_goals
         (residual
            (Tactical.TRY
               (simpLib.FULL_SIMP_TAC (clasimpLib.clasimp_ss ()) []))
            antecedent_goal)
         [antecedent_goal])

(* Isabelle simplifies the body of a bounded existential with its bound
   in context, [bex_cong_simp] being a default congruence there.  HOL4
   spells a bounded existential unfolded, so the fragment that carries
   the bound in is the congruence over the conjunction it unfolds to;
   with the fragment gone nothing offers the body its bound and the
   equivalence stands. *)
val bounded_goal =
  ([``!b:'a. MEM b zs ==> (p b <=> q b)``],
   ``(?e:'a. MEM e zs /\ p e) <=> (?e:'a. MEM e zs /\ q e)``)

val _ =
  check
    ("asm_full_simp simplifies a bounded body with its bound in context",
     fn () =>
       valid_closes
         (clasimpLib.asm_full_simp (clasimpLib.clasimp_ss ()) [])
         bounded_goal)

val _ =
  check
    ("without the congruence fragment that equivalence stands",
     fn () =>
       same_goals
         (residual
            (Tactical.TRY
               (clasimpLib.asm_full_simp
                  (simpLib.remove_ssfrags ["CONGWEAK"]
                     (clasimpLib.clasimp_ss ())) []))
            bounded_goal)
         [bounded_goal])

(* The rule hands the rebuilt conjunction back to the traversal, so the
   conjunction a bounded existential binds is still a term the rewrites
   reach -- the bound included.  A congruence that kept the node would
   leave the membership as it found it, this goal unchanged. *)
val _ =
  check
    ("the bound of a bounded existential is still rewritten",
     fn () =>
       aconv
         (boolSyntax.rhs
            (Thm.concl
               (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) []
                  ``?w:'a. MEM w (v::vs) /\ bounded_c w``)))
         ``?w:'a. ((w = v) \/ MEM w vs) /\ bounded_c (w:'a)``)

fun local_clasimp body base_cs base_ss controls =
  clasimpLib.process_clasimp_args body base_cs base_ss controls

fun probe_goal tactic =
  not
    (tactic_fails tactic
       ([], ``clasimp_argument_processor_probe:bool``))

fun same_thm left right =
  Term.aconv (concl left) (concl right)

fun same_spec
      ({kind = kind1, safe = safe1, prio = prio1} :
        clasetRules.rulespec)
      ({kind = kind2, safe = safe2, prio = prio2} :
        clasetRules.rulespec) =
  kind1 = kind2 andalso safe1 = safe2 andalso prio1 = prio2

datatype iff_test_shape = IffShape | NegShape | PlainShape

val iff_test_x = mk_var ("clasimp_iff_x", Type.ind)
val iff_test_pred =
  mk_var ("clasimp_iff_pred", Type.ind --> Type.bool)
val iff_test_left = mk_comb (iff_test_pred, iff_test_x)
val iff_test_right = mk_var ("clasimp_iff_right", Type.bool)
val iff_test_condition =
  boolSyntax.mk_eq (iff_test_x, iff_test_x)

fun iff_test_theorem conditional proposition =
  if conditional then
    DISCH iff_test_condition
      (Drule.ADD_ASSUM iff_test_condition (ASSUME proposition))
  else ASSUME proposition

fun install_iff name theorem =
  let
    val {rules, rewrite} =
      clasimpLib.iff_declaration name theorem
    val cs = clasimpLib.add_iff_rules rules clasetLib.empty_cs
    val ss =
      simpLib.++
        (BasicProvers.bool_ss, simpLib.rewrites [rewrite])
  in
    (rules, cs, ss)
  end

fun simp_rewrites_to ss source target =
  let
    val theorem =
      Conv.QCONV (simpLib.SIMP_CONV ss []) source
  in
    Term.aconv
      (snd (boolSyntax.dest_eq (concl theorem))) target
  end

fun rule_body theorem =
  snd (boolSyntax.strip_forall (concl theorem))

fun rule_has_shape expected_prems expected_conclusion (_, (_, theorem)) =
  let
    val (prems, conclusion) =
      boolSyntax.strip_imp_only (rule_body theorem)
  in
    ListPair.allEq
      (fn (left, right) => Term.aconv left right)
      (prems, expected_prems) andalso
    Term.aconv conclusion expected_conclusion
  end

fun iff_derivation_case
      (name, shape, conditional, proposition, rewrite_target) =
  let
    val theorem = iff_test_theorem conditional proposition
    val (rules, cs, ss) = install_iff name theorem
    val safe = not conditional
    val condition_tail =
      if conditional then [iff_test_condition] else []
    val installed = clasetLib.rules_of cs

    fun has_spec kind (spec, _) =
      same_spec spec {kind = kind, safe = safe, prio = NONE}

    val rules_ok =
      case (shape, rules) of
          (IffShape, [intro, dest]) =>
            has_spec clasetRules.Intro intro andalso
            has_spec clasetRules.Dest dest andalso
            rule_has_shape
              (iff_test_right :: condition_tail)
              iff_test_left intro andalso
            rule_has_shape
              (iff_test_left :: condition_tail)
              iff_test_right dest
        | (NegShape, [elim as (_, (_, theorem))]) =>
            let
              val (prems, conclusion) =
                boolSyntax.strip_imp_only (rule_body theorem)
            in
              has_spec clasetRules.Elim elim andalso
              ListPair.allEq
                (fn (left, right) => Term.aconv left right)
                (prems, iff_test_left :: condition_tail) andalso
              is_var conclusion andalso type_of conclusion = Type.bool
            end
        | (PlainShape, [intro]) =>
            has_spec clasetRules.Intro intro andalso
            rule_has_shape condition_tail iff_test_left intro
        | _ => false
  in
    rules_ok andalso length installed = length rules andalso
    simp_rewrites_to ss iff_test_left rewrite_target
  end

val iff_derivation_cases =
  [("iff-unconditional", IffShape, false,
    boolSyntax.mk_eq (iff_test_left, iff_test_right),
    iff_test_right),
   ("iff-conditional", IffShape, true,
    boolSyntax.mk_eq (iff_test_left, iff_test_right),
    iff_test_right),
   ("neg-unconditional", NegShape, false,
    boolSyntax.mk_neg iff_test_left, boolSyntax.F),
   ("neg-conditional", NegShape, true,
    boolSyntax.mk_neg iff_test_left, boolSyntax.F),
   ("plain-unconditional", PlainShape, false,
    iff_test_left, boolSyntax.T),
   ("plain-conditional", PlainShape, true,
    iff_test_left, boolSyntax.T)]

val _ =
  List.app
    (fn case_info as (name, _, _, _, _) =>
      check
        ("iff decision tree: " ^ name,
         fn () => iff_derivation_case case_info))
    iff_derivation_cases

val has_named_claset_rule = iffTestSupport.has_rule

(* The theory tests probe the persistent views the same way. *)
val has_iff_rewrite = iffTestSupport.rewrite_changes
val has_extension_iff_rewrite = iffTestSupport.extension_rewrite_changes

fun persistent_iff_rule_name name suffix =
  name ^ ".__clasimp_iff_" ^ suffix

val clasimp_iff_attribute_probe_def =
  new_definition
    ("clasimp_iff_attribute_probe_def",
     ``clasimp_iff_attribute_probe (p : bool) = p``)

val _ =
  check
    ("iff settype and attribute are registered without collision",
     fn () =>
       List.exists (equal "iff") (ThmSetData.all_set_types ()) andalso
       ThmAttribute.is_attribute "iff")

val _ =
  check
    ("Theorem [iff] immediately updates and remove_iff retracts both stores",
     fn () =>
       let
         val local_name = "clasimp_iff_attribute_test"
         val persistent_name =
           KernelSig.name_toString (ThmSetData.toKName local_name)
         val theorem = clasimp_iff_attribute_probe_def
         val _ = boolLib.save_thm (local_name ^ "[iff]", theorem)
         val added =
           has_named_claset_rule
             (persistent_iff_rule_name persistent_name "intro") andalso
           has_named_claset_rule
             (persistent_iff_rule_name persistent_name "dest") andalso
           has_iff_rewrite persistent_name (BasicProvers.srw_ss ()) andalso
           has_extension_iff_rewrite persistent_name (clasimpLib.clasimp_ss ())
         val _ = clasimpLib.remove_iff local_name
       in
         added andalso
         not
           (has_named_claset_rule
             (persistent_iff_rule_name persistent_name "intro")) andalso
         not
           (has_named_claset_rule
             (persistent_iff_rule_name persistent_name "dest")) andalso
         not
           (has_iff_rewrite persistent_name (BasicProvers.srw_ss ())) andalso
         not
           (has_extension_iff_rewrite persistent_name
              (clasimpLib.clasimp_ss ()))
       end)

val _ =
  check
    ("a rejected remove_iff leaves a colliding claset rule installed",
     fn () =>
       let
         val local_name = "clasimp_absent_iff_test"
         val persistent_name =
           KernelSig.name_toString (ThmSetData.toKName local_name)
         val rule_name = persistent_name ^ "_intro"
         val spec =
           {kind = clasetRules.Intro, safe = false, prio = NONE}
         val theorem =
           ASSUME (mk_var ("clasimp_absent_iff_rule", Type.bool))
         val _ = clasetLib.temp_add_rule spec (rule_name, theorem)
         val rejected =
           (clasimpLib.remove_iff local_name; false)
             handle HOL_ERR _ => true
         val preserved =
           List.exists
             (fn (_, (name, rule)) =>
               name = rule_name andalso same_thm theorem rule)
             (clasetLib.rules_of (clasetLib.the_claset ()))
         val _ = clasetLib.temp_delrule rule_name
       in
         rejected andalso preserved
       end)

(* A name that denotes no installed declaration would be recorded as a
   delta that this theory, and every descendant of it, replays as a silent
   no-op -- and a malformed one would make them fail to load outright. *)
val _ =
  check
    ("remove_iff rejects an unresolvable name before recording a delta",
     fn () =>
       let
         fun deltas () =
           length (ThmSetData.current_data {settype = "iff"})
         val before_delta = deltas ()
         fun rejects name =
           (clasimpLib.remove_iff name; false) handle HOL_ERR _ => true
       in
         rejects "clasimp.absent.iff" andalso
         rejects "clasimp_absent_iff_name" andalso
         deltas () = before_delta
       end)

(* Two declarations may derive the same rule; each still owns its copy, so
   retracting one cannot disarm the other.  Neither is a declaration the
   user could correct, so neither warns. *)
val _ =
  check
    ("a derived iff rule duplicating an installed one is kept, unannounced",
     fn () =>
       let
         val theorem = clasimp_iff_attribute_probe_def
         val {rules = first, ...} =
           clasimpLib.iff_declaration "clasimp_iff_duplicate_first" theorem
         val {rules = second, ...} =
           clasimpLib.iff_declaration "clasimp_iff_duplicate_second" theorem
         val cs = clasimpLib.add_iff_rules first clasetLib.empty_cs
         val warnings = ref ([] : string list)
         val saved = !Feedback.WARNING_outstream
         val _ =
           Feedback.WARNING_outstream :=
             (fn message => warnings := message :: !warnings)
         val cs' =
           clasimpLib.add_iff_rules second cs
             handle e => (Feedback.WARNING_outstream := saved; raise e)
         val _ = Feedback.WARNING_outstream := saved
         val retracted =
           List.foldl
             (fn ((_, (name, _)), current) =>
               clasetLib.remove_rule name current)
             cs' first
         fun installed cs (_, (name, _)) =
           List.exists (fn (_, (name', _)) => name = name')
             (clasetLib.rules_of cs)
       in
         null (!warnings) andalso
         length (clasetLib.rules_of cs') =
           length (clasetLib.rules_of cs) + length second andalso
         List.all (installed cs') second andalso
         List.all (installed retracted) second andalso
         not (List.exists (installed retracted) first)
       end)

(* [iff_bottom_up] is [iff] with its simpset half installed as a
   low-priority reducer, which the traversal reaches only once the rewrites
   and the descent have both left a node alone.  The probe below is the
   shape that distinguishes the two: a declared rule reading its subject
   through [clasimp_bu_wrap], and an ordinary rewrite about a subject whose
   head is [clasimp_bu_step]. *)
val clasimp_bu_wrap_def =
  new_definition
    ("clasimp_bu_wrap_def", ``clasimp_bu_wrap (n:num) = (n = 0)``)

val clasimp_bu_view_def =
  new_definition
    ("clasimp_bu_view_def", ``clasimp_bu_view (n:num) = ~(n = 0)``)

val clasimp_bu_step_def =
  new_definition
    ("clasimp_bu_step_def", ``clasimp_bu_step (n:num) = SUC n``)

val clasimp_bu_rule =
  Tactical.prove
    (``!n. ~clasimp_bu_wrap n <=> clasimp_bu_view n``,
     Rewrite.REWRITE_TAC [clasimp_bu_wrap_def, clasimp_bu_view_def])

val clasimp_bu_head =
  Tactical.prove
    (``!n. clasimp_bu_wrap (clasimp_bu_step n) <=> F``,
     Rewrite.REWRITE_TAC
       [clasimp_bu_wrap_def, clasimp_bu_step_def, numTheory.NOT_SUC])

fun clasimp_bu_normalise term =
  let
    val ss = simpLib.++
      (BasicProvers.srw_ss (), simpLib.rewrites [clasimp_bu_head])
  in
    boolSyntax.rhs (concl (Conv.QCONV (simpLib.SIMP_CONV ss []) term))
  end

fun clasimp_bu_child_normalise term =
  let
    val ss =
      simpLib.++ (lifted_srw_ss (),
                  simpLib.rewrites [clasimp_bu_head])
  in
    boolSyntax.rhs
      (concl
        (Conv.QCONV
          (simpLib.SIMP_CONV_CHILD_FIRST
             (Traverse.charge_only (fn () => ())) ss []) term))
  end

(* Declared and retracted around the probe, so neither store keeps the
   rule once the check that needs it has run. *)
fun with_declaration (attribute, retract) local_name body =
  let
    val _ = boolLib.save_thm (local_name ^ "[" ^ attribute ^ "]",
                              clasimp_bu_rule)
    val result = body () handle e => (retract local_name; raise e)
    val _ = retract local_name
  in
    result
  end

(* A theory holds each name once, so every declaration takes its own. *)
fun with_bottom_up name body =
  with_declaration ("iff_bottom_up", clasimpLib.remove_iff_bottom_up) name body

fun with_plain_iff name body =
  with_declaration ("iff", clasimpLib.remove_iff) name body

val _ =
  check
    ("Theorem [iff_bottom_up] immediately updates and " ^
     "remove_iff_bottom_up retracts both stores",
     fn () =>
       let
         val local_name = "clasimp_bottom_up_attribute_test"
         val persistent_name =
           KernelSig.name_toString (ThmSetData.toKName local_name)
         val _ =
           boolLib.save_thm (local_name ^ "[iff_bottom_up]", clasimp_bu_rule)
         val added =
           has_named_claset_rule
             (persistent_iff_rule_name persistent_name "intro") andalso
           has_named_claset_rule
             (persistent_iff_rule_name persistent_name "dest") andalso
           has_iff_rewrite persistent_name (BasicProvers.srw_ss ()) andalso
           has_extension_iff_rewrite persistent_name (clasimpLib.clasimp_ss ())
         val _ = clasimpLib.remove_iff_bottom_up local_name
       in
         added andalso
         not
           (has_named_claset_rule
             (persistent_iff_rule_name persistent_name "intro")) andalso
         not
           (has_named_claset_rule
             (persistent_iff_rule_name persistent_name "dest")) andalso
         not
           (has_iff_rewrite persistent_name (BasicProvers.srw_ss ())) andalso
         not
           (has_extension_iff_rewrite persistent_name
              (clasimpLib.clasimp_ss ()))
       end)

(* The same theorem declared [iff] reaches the term first and leaves the
   subject in a form its own rule no longer addresses. *)
val _ =
  check
    ("an [iff_bottom_up] rewrite waits for a rule about the subject",
     fn () =>
       let
         val term = ``~clasimp_bu_wrap (clasimp_bu_step m)``
       in
         aconv
           (with_bottom_up "clasimp_bottom_up_masked"
              (fn () => clasimp_bu_normalise term))
           boolSyntax.T andalso
         aconv
           (with_plain_iff "clasimp_bottom_up_as_iff"
              (fn () => clasimp_bu_normalise term))
           ``clasimp_bu_view (clasimp_bu_step m)``
       end)

val _ =
  check
    ("child-first traversal handles the same subject rewrite",
     fn () =>
       let
         val term = ``~clasimp_bu_wrap (clasimp_bu_step m)``
       in
         aconv
           (with_bottom_up "clasimp_child_bottom_up"
              (fn () => clasimp_bu_child_normalise term))
           boolSyntax.T andalso
         aconv
           (with_plain_iff "clasimp_child_plain_iff"
              (fn () => clasimp_bu_child_normalise term))
           boolSyntax.T
       end)

val _ =
  check
    ("an [iff_bottom_up] rewrite reduces a subject no rule addresses",
     fn () =>
       aconv
         (with_bottom_up "clasimp_bottom_up_bare"
            (fn () => clasimp_bu_normalise ``~clasimp_bu_wrap v``))
         ``clasimp_bu_view v``)

(* The same order for a rewrite a single invocation installs rather than
   a declaration: added plainly it reaches the term first and leaves the
   subject in a form the rule about that subject's head no longer
   addresses. *)
val clasimp_bu_head_ss = simpLib.++
  (BasicProvers.srw_ss (), simpLib.rewrites [clasimp_bu_head])
val clasimp_bu_head_ext_ss =
  simpLib.++ (lifted_srw_ss (), simpLib.rewrites [clasimp_bu_head])

fun clasimp_bu_reduce_with simp_conv ss term =
  boolSyntax.rhs (concl (Conv.QCONV (simp_conv ss []) term))
val clasimp_bu_reduce = clasimp_bu_reduce_with simpLib.SIMP_CONV
val clasimp_bu_reduce_ext = clasimp_bu_reduce_with simpLib.SIMP_CONV

val _ =
  check
    ("a rewrite installed for one invocation waits the same way",
     fn () =>
       let
         val term = ``~clasimp_bu_wrap (clasimp_bu_step m)``
       in
         aconv
           (clasimp_bu_reduce_ext
              (simpLib.++
                 (clasimp_bu_head_ext_ss,
                  clasimpLib.normalised_subject_fragment [clasimp_bu_rule]))
              term)
           boolSyntax.T andalso
         aconv
           (clasimp_bu_reduce
              (simpLib.++ (clasimp_bu_head_ss,
                                simpLib.rewrites [clasimp_bu_rule]))
              term)
           ``clasimp_bu_view (clasimp_bu_step m)``
       end)

val _ =
  check
    ("a rewrite installed for one invocation reduces a bare subject",
     fn () =>
       aconv
         (clasimp_bu_reduce_ext
            (simpLib.++
               (clasimp_bu_head_ext_ss,
                clasimpLib.normalised_subject_fragment [clasimp_bu_rule]))
            ``~clasimp_bu_wrap v``)
         ``clasimp_bu_view v``)

val _ =
  check
    ("a bottom-up fragment with an invalid rule declines reduction",
     fn () =>
       let
         val term = ``~clasimp_bu_wrap v``
         val fragment = clasimpLib.normalised_subject_fragment
           [clasimp_bu_rule, boolTheory.TRUTH]
         val simpset = simpLib.++ (lifted_srw_ss (), fragment)
       in
         aconv (clasimp_bu_reduce_ext simpset term) term
       end)

(* [simp_bottom_up] is the same order without the claset halves: a law the
   source declares [simp] and not [iff] may not seed the reasoner. *)
fun with_simp_bottom_up name body =
  with_declaration ("simp_bottom_up", clasimpLib.remove_simp_bottom_up)
    name body

val _ =
  check
    ("a [simp_bottom_up] rewrite waits for a rule about the subject",
     fn () =>
       aconv
         (with_simp_bottom_up "clasimp_simp_bottom_up_masked"
            (fn () => clasimp_bu_normalise
                        ``~clasimp_bu_wrap (clasimp_bu_step m)``))
         boolSyntax.T andalso
       aconv
         (with_simp_bottom_up "clasimp_simp_bottom_up_bare"
            (fn () => clasimp_bu_normalise ``~clasimp_bu_wrap v``))
         ``clasimp_bu_view v``)

val _ =
  check
    ("Theorem [simp_bottom_up] declares no claset rule and " ^
     "remove_simp_bottom_up retracts the rewrite",
     fn () =>
       let
         val local_name = "clasimp_simp_bottom_up_attribute_test"
         val persistent_name =
           KernelSig.name_toString (ThmSetData.toKName local_name)
         val _ =
           boolLib.save_thm
             (local_name ^ "[simp_bottom_up]", clasimp_bu_rule)
         val declared =
           has_iff_rewrite persistent_name (BasicProvers.srw_ss ()) andalso
           has_extension_iff_rewrite persistent_name (clasimpLib.clasimp_ss ())
         val claset_rules =
           List.exists
             (fn suffix =>
                has_named_claset_rule
                  (persistent_iff_rule_name persistent_name suffix))
             ["intro", "dest", "elim"]
         val _ = clasimpLib.remove_simp_bottom_up local_name
       in
         declared andalso not claset_rules andalso
         not (has_iff_rewrite persistent_name (BasicProvers.srw_ss ())) andalso
         not (has_extension_iff_rewrite persistent_name
                (clasimpLib.clasimp_ss ()))
       end)

(* The matcher the reducer uses.  A law stated as a higher-order pattern --
   Isabelle's miniscoping laws read a quantifier's body as [P x] -- fires
   on a body that is not literally a variable applied to the bound one only
   if the reducer matches the way the simplifier's own rewrites do. *)
val clasimp_bu_higher_order =
  Tactical.prove
    (``!P Q. (!x:num. P x ==> Q) <=> ((?x:num. P x) ==> Q)``,
     Rewrite.REWRITE_TAC [boolTheory.LEFT_FORALL_IMP_THM])

val _ =
  check
    ("a bottom-up rewrite is matched as a higher-order pattern",
     fn () =>
       aconv
         (clasimp_bu_reduce_ext
            (simpLib.++
               (lifted_srw_ss (),
                clasimpLib.normalised_subject_fragment
                  [clasimp_bu_higher_order]))
            ``!n:num.
                clasimp_bu_wrap (clasimp_bu_step n) ==> clasimp_bu_probe``)
         ``(?n:num. clasimp_bu_wrap (clasimp_bu_step n)) ==>
           clasimp_bu_probe``)

fun tyinfo_named tyop =
  case List.filter
    (fn tyi => #2 (TypeBasePure.ty_name_of tyi) = tyop)
    (TypeBase.elts ()) of
      [tyi] => tyi
    | _ => raise Fail ("missing or ambiguous TypeBase entry for " ^ tyop)

fun rules_named name =
  List.filter
    (fn (_, (name', _)) => name = name')
    (clasetLib.rules_of (clasetLib.the_claset ()))

val constructor_sintro_spec =
  {kind = clasetRules.Intro, safe = true, prio = NONE}

fun constructor_rule_names tyi index =
  let
    val (thy, tyop) = TypeBasePure.ty_name_of tyi
    val base =
      "__claset_tyinfo_" ^ thy ^ "_" ^ tyop ^
      "_inject_" ^ Int.toString index
  in
    {dest = base ^ "_dest", intro = base ^ "_intro"}
  end

fun has_constructor_intro tyi index =
  let
    val {intro, ...} = constructor_rule_names tyi index
  in
    case rules_named intro of
        [(spec, _)] => same_spec spec constructor_sintro_spec
      | _ => false
  end

val hook_tyinfo = tyinfo_named "clasimp_hook_after_load"
val list_tyinfo = tyinfo_named "list"

val _ =
  check
    ("constructor intro arrives through the post-load TypeBase hook",
     fn () => has_constructor_intro hook_tyinfo 0)

val _ =
  check
    ("constructor intro arrives through the TypeBase catch-up sweep",
     fn () => has_constructor_intro list_tyinfo 0)

val _ =
  check
    ("constructor intros do not duplicate Phase 0 injectivity seeds",
     fn () =>
       let
         val {dest, intro} = constructor_rule_names hook_tyinfo 0
       in
         length (rules_named dest) = 1 andalso
         length (rules_named intro) = 1
       end)

val {intro = hook_intro_name, ...} =
  constructor_rule_names hook_tyinfo 0

val (hook_intro_spec, (_, hook_intro_theorem)) =
  case rules_named hook_intro_name of
      [rule] => rule
    | _ => raise Fail "missing constructor intro"

val component_equality =
  CONJUNCT2 (CONJUNCT2 boolTheory.NOT_CLAUSES)

val component_equality_cs =
  clasetLib.add_sintros
    [("clasimp-component-equality", component_equality),
     ("clasimp-component-reflexivity", boolTheory.EQ_REFL)]
    clasetLib.empty_cs

val constructor_intro_cs =
  clasetLib.add_rule hook_intro_spec
    (hook_intro_name, hook_intro_theorem) component_equality_cs

val constructor_intro_goal : Abbrev.goal =
  ([],
   ``ClasimpHookAfter (~F) clasimp_hook_b =
     ClasimpHookAfter T clasimp_hook_b``)

fun constructor_safe cs =
  NTactical.DETERM (classicalLib.CS_SAFE_TAC cs)

val _ =
  check
    ("classical search cannot prove constructor equality without the intro",
     fn () =>
       tactic_fails
         (constructor_safe component_equality_cs)
         constructor_intro_goal)

val _ =
  check
    ("classical search proves constructor equality with the new intro",
     fn () =>
       valid_closes
         (constructor_safe constructor_intro_cs)
         constructor_intro_goal)

val _ =
  check
    ("the base claset proves constructor equality with its safe intro",
     fn () =>
       valid_closes
         (constructor_safe (clasetLib.the_claset ()))
         constructor_intro_goal)

val marker_rule_cases :
    (string * thm * clasetRules.rulespec) list =
  [("SIntro", clasetLib.SIntro boolTheory.AND_INTRO_THM,
    {kind = clasetRules.Intro, safe = true, prio = NONE}),
   ("Intro", clasetLib.Intro boolTheory.AND_INTRO_THM,
    {kind = clasetRules.Intro, safe = false, prio = NONE}),
   ("SElim", clasetLib.SElim boolTheory.OR_ELIM_THM,
    {kind = clasetRules.Elim, safe = true, prio = NONE}),
   ("Elim", clasetLib.Elim boolTheory.OR_ELIM_THM,
    {kind = clasetRules.Elim, safe = false, prio = NONE}),
   ("SDest", clasetLib.SDest boolTheory.OR_ELIM_THM,
    {kind = clasetRules.Dest, safe = true, prio = NONE}),
   ("Dest", clasetLib.Dest boolTheory.OR_ELIM_THM,
    {kind = clasetRules.Dest, safe = false, prio = NONE})]

fun claset_marker_routed (_, marker, expected_spec) =
  let
    fun inspect cs _ simp_args =
      case (clasetLib.rules_of cs, simp_args) of
          ([(spec, _)], []) =>
            if same_spec spec expected_spec then Tactical.ALL_TAC
            else Tactical.NO_TAC
        | _ => Tactical.NO_TAC
    val tactic =
      local_clasimp inspect clasetLib.empty_cs simpLib.empty_ss [marker]
  in
    probe_goal tactic
  end

val _ =
  check
    ("argument processor routes every claset theorem marker",
     fn () => List.all claset_marker_routed marker_rule_cases)

val _ =
  check
    ("argument processor consumes Del in the claset partition",
     fn () =>
       let
         val base =
           clasetLib.add_sintros
             [("clasimp-delete", boolTheory.AND_INTRO_THM)]
             clasetLib.empty_cs
         fun inspect cs _ simp_args =
           if null (clasetLib.rules_of cs) andalso null simp_args
           then Tactical.ALL_TAC
           else Tactical.NO_TAC
         val tactic =
           local_clasimp inspect base simpLib.empty_ss
             [clasetLib.Del "clasimp-delete"]
       in
         probe_goal tactic
       end)

val _ =
  check
    ("Simp marker adds its theorem to the invocation simpset",
     fn () =>
       let
         fun simplify _ ss simp_args =
           simpLib.SIMP_TAC ss simp_args
         val tactic =
           local_clasimp simplify clasetLib.empty_cs simpLib.empty_ss
             [clasetLib.Simp
                (CONJUNCT2 (CONJUNCT2 boolTheory.NOT_CLAUSES))]
       in
         valid_closes tactic ([], ``~F``)
       end)

(* [inj_onD]'s shape.  HOL4's rewrite preparation refuses a bare-variable
   left-hand side and rewrites the conclusion to T instead, existentially
   closing the condition variables the conclusion does not carry
   (src/simp/src/Cond_rewr.sml), so the prepared rewrite matches every
   equation in the goal and nothing determines its condition: the simpset
   is not where this fact can reach a goal.  The invocation declares it as
   an unsafe destruction rule instead. *)
local
  (* [inj_onD]'s own form: the premises are separate, which is what lets a
     destruction rule fire on the first of them. *)
  val undetermined_fact =
    Tactical.prove
      (``!f s t x y.
           INJ f s t ==> x IN s ==> y IN s ==> (f x = f y) ==> (x = y)``,
       Tactical.THEN
         (Rewrite.REWRITE_TAC [pred_setTheory.INJ_DEF],
          Tactical.THEN
            (Tactical.REPEAT Tactic.STRIP_TAC, Tactic.RES_TAC)))
  val undetermined_goal : Abbrev.goal =
    ([``INJ (undetermined_f : 'a -> 'b) undetermined_s undetermined_t``,
      ``(undetermined_x : 'a) IN undetermined_s``,
      ``(undetermined_y : 'a) IN undetermined_s``,
      ``(undetermined_f : 'a -> 'b) undetermined_x =
          undetermined_f undetermined_y``],
     ``(undetermined_x : 'a) = undetermined_y``)
in

(* The rewrite that cannot fire is not merely inert: it matches every
   equation and calls the solver on an existential at each, and the search
   that carries it does not come back, so a regression here stops the
   suite rather than failing a row.  There is no budget to bound it with
   -- [Timeout.apply] around this tactic never fired inside the selftest
   binary, where the same call preempts in an interactive session. *)

val _ =
  check
    ("a simp argument no rewrite of which can fire reaches the search",
     fn () =>
       valid_closes
         (clasimpLib.FORCE_TAC [clasetLib.Simp undetermined_fact])
         undetermined_goal)

(* The argument is what closes it: the ambient context does not. *)
val _ =
  check
    ("the goal that argument closes is not closed without it",
     fn () => tactic_fails (clasimpLib.FORCE_TAC []) undetermined_goal)

end

(* The other half of an undetermined condition variable.  [EVERY2_LENGTH]
   does carry a left-hand side to match -- [LENGTH l1 = LENGTH l2] -- and
   only its relation is undetermined, so the prepared rewrite is one the
   simpset can hold; what it needs is the witness the assumption names.
   [LIST_REL_APPEND_EQ] asks for that length equation as its own
   condition, which is where Isabelle's proof of [list_all2_appendI]
   sends it. *)
local
  val lifted_goal : Abbrev.goal =
    ([], ``!relation a b c d.
             LIST_REL relation a b ==> LIST_REL relation c d ==>
             LIST_REL relation (a ++ c) (b ++ d)``)
  val lifting_arguments =
    [clasetLib.Simp listTheory.LIST_REL_APPEND_EQ,
     clasetLib.Simp listTheory.EVERY2_LENGTH]
in

val _ =
  check
    ("a condition variable the left-hand side leaves open is read off " ^
     "an assumption",
     fn () => valid_closes (clasimpLib.AUTO_TAC lifting_arguments)
                lifted_goal)

(* The arguments are what close it; neither is ambient. *)
val _ =
  check
    ("the goal those arguments close is not closed without them",
     fn () => not (valid_closes (clasimpLib.AUTO_TAC []) lifted_goal))

end

(* The same witness, once the simpset has miniscoped the closure it sits
   in.  The closed condition is a conjunction over the rewrite's premises,
   and Isabelle's [ex_simps] -- ambient there, declared here -- leaves the
   quantifier over the one conjunct its variable occurs in, which is not
   where the assumption naming the witness can be read off.  The law is
   declared below in the form the seeds declare it; neither the goal nor
   the rule is a benchmark entry. *)
local
  val clasimp_pull_p_def =
    new_definition
      ("clasimp_pull_p_def", ``clasimp_pull_p (n:num) <=> (n MOD 2 = 0)``)
  val clasimp_pull_q_def =
    new_definition
      ("clasimp_pull_q_def", ``clasimp_pull_q (n:num) <=> clasimp_pull_p n``)
  val clasimp_pull_link_def =
    new_definition
      ("clasimp_pull_link_def",
       ``clasimp_pull_link (r:num -> num -> bool) x y <=> r x y``)
  (* Two premises, so that the closure is a conjunction, and a relation the
     conclusion does not carry, so that there is a witness to name at all:
     the conclusion determines the subject and nothing else. *)
  val clasimp_pull_fact =
    Tactical.prove
      (``!relation x y.
           (!a b. relation (a:num) (b:num) ==> clasimp_pull_p a) ==>
           clasimp_pull_link relation x y ==> clasimp_pull_q x``,
       Tactical.THEN
         (Rewrite.REWRITE_TAC [clasimp_pull_q_def, clasimp_pull_link_def],
          Tactical.THEN
            (Tactical.REPEAT Tactic.STRIP_TAC,
             Tactical.THEN (Tactic.RES_TAC, Rewrite.ASM_REWRITE_TAC []))))
  (* The assumption that names the witness is the goal's own antecedent, as
     it is in the corpus: the traversal has it in context only once it has
     descended through the quantifiers and the implication, and by then the
     condition has been left to the reducer. *)
  val clasimp_pull_goal : Abbrev.goal =
    ([``!a b. (clasimp_pull_r : num -> num -> bool) a b ==>
              clasimp_pull_p a``],
     ``!x y. clasimp_pull_link clasimp_pull_r x y ==> clasimp_pull_q x``)
  (* A theory holds each name once, so each declaration takes its own. *)
  fun with_miniscoping local_name body =
    let
      val _ =
        boolLib.save_thm
          (local_name ^ "[simp_bottom_up]", boolTheory.RIGHT_EXISTS_AND_THM)
      val result =
        body ()
        handle e => (clasimpLib.remove_simp_bottom_up local_name; raise e)
      val _ = clasimpLib.remove_simp_bottom_up local_name
    in
      result
    end
  fun closes local_name arguments =
    with_miniscoping local_name
      (fn () =>
         valid_closes
           (clasimpLib.asm_full_simp (clasimpLib.clasimp_ss ()) arguments)
           clasimp_pull_goal)
in

val _ =
  check
    ("a witness the simpset has miniscoped out of reach is still read " ^
     "off an assumption",
     fn () => closes "clasimp_pull_supplied" [clasimp_pull_fact])

(* The argument is what closes it: the assumptions alone do not. *)
val _ =
  check
    ("the goal that argument closes is not closed without it",
     fn () => not (closes "clasimp_pull_bare" []))

end

(* How a citation reaches the search.  An implication becomes a rule of
   the invocation claset and is kept out of the assumptions; both routes
   close the goal below, so what the routing changes is how much search
   that takes.  Reached as an assumption, the fact is taken apart a
   quantifier and an implication at a time; reached as a rule it is one
   application.  The work meter is the measurement, not the clock.

   The predicates are defined here and declared nowhere, and neither the
   rule nor the goal is a benchmark entry.  Their heads have to be
   constants: a rule concluding an applied variable is indexed under no
   constant and reaches nothing, which is a fact about the rule net and
   not about the routing. *)
local
  val routing_ord_def =
    new_definition
      ("routing_ord_def", ``routing_ord (r : 'a -> 'a -> bool) <=> T``)
  val routing_srt_def =
    new_definition
      ("routing_srt_def",
       ``routing_srt (r : 'a -> 'a -> bool) (x : 'a) <=> T``)
  val routing_dst_def =
    new_definition ("routing_dst_def", ``routing_dst (x : 'a) <=> T``)
  val routing_same_def =
    new_definition
      ("routing_same_def", ``routing_same (x : 'a) (y : 'a) <=> T``)
  (* Five premises, so that the assumption route has something to peel:
     the rule's own subjects are determined by the premises and not by
     its conclusion. *)
  val routing_fact =
    Tactical.prove
      (``!r x y.
           routing_ord r ==>
           routing_srt r x ==> routing_srt r y ==>
           routing_dst x ==> routing_dst y ==>
           routing_same x y``,
       Rewrite.REWRITE_TAC [routing_same_def])
  val routing_goal : Abbrev.goal =
    ([``routing_ord (routing_le : 'a -> 'a -> bool)``,
      ``routing_srt (routing_le : 'a -> 'a -> bool) (routing_a : 'a)``,
      ``routing_srt (routing_le : 'a -> 'a -> bool) (routing_b : 'a)``,
      ``routing_dst (routing_a : 'a)``,
      ``routing_dst (routing_b : 'a)``],
     ``routing_same (routing_a : 'a) (routing_b : 'a)``)
  fun search tactic =
    searchWork.measure (fn () => valid_closes tactic routing_goal)
in

val _ =
  check
    ("a supplied implication shortens the search it is given to",
     fn () =>
       let
         val (assumed_closed, assumed_work) =
           search
             (Tactical.THEN
                (Tactic.ASSUME_TAC routing_fact, classicalLib.FAST_TAC []))
         val (supplied_closed, supplied_work) =
           search (classicalLib.FAST_TAC [routing_fact])
       in
         assumed_closed andalso supplied_closed andalso
         #expansions supplied_work < #expansions assumed_work
       end)

end

val generic_simp_markers =
  [markerLib.AC boolTheory.AND_CLAUSES boolTheory.OR_CLAUSES,
   markerLib.Cong boolTheory.AND_CLAUSES,
   simpLib.Split boolTheory.OR_CLAUSES,
   markerLib.Excl "clasimp-selftest",
   markerLib.ExclSF "clasimp-selftest",
   markerLib.FRAG "clasimp-selftest",
   markerLib.mk_Req0 boolTheory.TRUTH,
   markerLib.mk_ReqD boolTheory.TRUTH,
   BoundedRewrites.Once boolTheory.TRUTH,
   BoundedRewrites.Ntimes boolTheory.IMP_CLAUSES 2,
   markerLib.NoAsms,
   markerLib.IgnAsm [QUOTE "clasimp_ignored"]]

val _ =
  check
    ("argument processor preserves every generic simp control",
     fn () =>
       let
         fun inspect cs _ simp_args =
           if null (clasetLib.rules_of cs) andalso
              ListPair.allEq (fn (left, right) => same_thm left right)
                (simp_args, generic_simp_markers)
           then Tactical.ALL_TAC
           else Tactical.NO_TAC
         val tactic =
           local_clasimp inspect clasetLib.empty_cs simpLib.empty_ss
             generic_simp_markers
       in
         probe_goal tactic
       end)

val _ =
  check
    ("Once reaches the simp argument list without being unwrapped",
     fn () =>
       let
         val once = BoundedRewrites.Once boolTheory.IMP_CLAUSES
         fun inspect _ _ [theorem] =
               let val (payload, bound) =
                 BoundedRewrites.DEST_BOUNDED theorem
               in
                 if bound = 1 andalso
                    same_thm payload boolTheory.IMP_CLAUSES
                 then Tactical.ALL_TAC
                 else Tactical.NO_TAC
               end
           | inspect _ _ _ = Tactical.NO_TAC
         val tactic =
           local_clasimp inspect clasetLib.empty_cs simpLib.empty_ss [once]
       in
         probe_goal tactic
       end)

val _ =
  check
    ("plain theorems are inserted before the clasimp script",
     fn () =>
       let
         val fact = Thm.REFL ``clasimp_insert_x:'a``
         fun leave_residue _ _ _ = Tactical.ALL_TAC
         val tactic =
           local_clasimp leave_residue clasetLib.empty_cs
             simpLib.empty_ss [fact]
       in
         case residual tactic ([], ``clasimp_insert_goal:bool``) of
             [([assumption], _)] => Term.aconv assumption (concl fact)
           | _ => false
       end)

(* A citation that is an implication takes the other route: it is a rule
   of the claset the script is handed, and the goal it runs on does not
   carry it as well. *)
val _ =
  check
    ("a supplied implication reaches the script as a rule instead",
     fn () =>
       let
         val p = ``clasimp_insert_p:bool``
         val fact = DISCH p (ASSUME p)
         val seen = ref ~1
         fun leave_residue cs _ _ =
           (seen := length (clasetLib.rules_of cs); Tactical.ALL_TAC)
         val tactic =
           local_clasimp leave_residue clasetLib.empty_cs
             simpLib.empty_ss [fact]
       in
         case residual tactic ([], ``clasimp_insert_goal:bool``) of
             [([], _)] => !seen = 1
           | _ => false
       end)

val _ =
  check
    ("Iff marker is temporary and solves through a clasimp tactic",
     fn () =>
       let
         val equivalence =
           CONJUNCT2 (CONJUNCT2 boolTheory.NOT_CLAUSES)
         val (left, right) =
           boolSyntax.dest_eq (concl equivalence)
         val goal = ([right], left)
         fun search cs ss _ =
           clasimpLib.CS_FASTFORCE_TAC cs ss
         fun tactic controls =
           local_clasimp search clasetLib.empty_cs simpLib.empty_ss controls
         val rules_before =
           length (clasetLib.rules_of (clasetLib.the_claset ()))
         val rewrite_before =
           Conv.QCONV
             (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) [])
             iff_test_left
         val unavailable_before =
           tactic_fails (tactic []) goal
         val available =
           valid_closes
             (tactic
               [clasetLib.Iff equivalence]) goal
         val rules_after =
           length (clasetLib.rules_of (clasetLib.the_claset ()))
         val rewrite_after =
           Conv.QCONV
             (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) [])
             iff_test_left
       in
         unavailable_before andalso available andalso
         tactic_fails (tactic []) goal andalso
         rules_before = rules_after andalso
         Term.aconv (concl rewrite_before) (concl rewrite_after)
       end)

val _ =
  check
    ("argument processor honors Abbr before partitioning",
     fn () =>
       let
         val name = "clasimp_abbreviated"
         val abbreviated = Term.mk_var (name, Type.bool)
         val proposition = ``clasimp_abbreviation_p:bool``
         val goal =
           ([markerSyntax.mk_abbrev (name, proposition), proposition],
            abbreviated)
         fun accept _ _ _ =
           Tactical.FIRST_ASSUM Tactic.ACCEPT_TAC
         fun tactic controls =
           local_clasimp accept clasetLib.empty_cs simpLib.empty_ss controls
       in
         tactic_fails (tactic []) goal andalso
         valid_closes
           (tactic [markerLib.Abbr [QUOTE name]]) goal
       end)

val wrapper_ss =
  simpLib.++
    (simpLib.clear_rules (clasimpLib.clasimp_ss ()),
     simpLib.rewrites
       [CONJUNCT2 (CONJUNCT2 boolTheory.NOT_CLAUSES)])

val wrapper_goal : Abbrev.goal = ([], ``~F``)

val wrapper_rungs =
  [("add_simp_wrapper reaches the FAST unsafe rung",
    fn cs => NTactical.DETERM (classicalLib.CS_FAST_TAC cs),
    clasimpLib.add_simp_wrapper),
   ("add_simp_wrapper reaches the bounded depth rung",
    fn cs =>
      NTactical.DETERM
        (classicalLib.CS_DEPTH_SOLVE_TAC {dup = false} 1 cs),
    clasimpLib.add_simp_wrapper),
   ("add_safe_simp_wrapper reaches the SAFE rung",
    fn cs => NTactical.DETERM (classicalLib.CS_SAFE_TAC cs),
    clasimpLib.add_safe_simp_wrapper),
   ("add_safe_simp_wrapper reaches the CLARIFY rung",
    fn cs => NTactical.DETERM (classicalLib.CS_CLARIFY_TAC cs),
    clasimpLib.add_safe_simp_wrapper)]

fun wrapper_rung (name, rung, add_wrapper) =
  check
    (name,
     fn () =>
       tactic_fails (rung clasetLib.empty_cs) wrapper_goal andalso
       valid_closes
         (rung (add_wrapper wrapper_ss [] clasetLib.empty_cs))
         wrapper_goal)

val _ = List.app wrapper_rung wrapper_rungs

val wrapper_control_name =
  {Thy = "clasimpSelftest", Name = "wrapper_control"}

val wrapper_spare_name =
  {Thy = "clasimpSelftest", Name = "wrapper_spare"}

(* An atom the empty claset has no rule for, so that only its own rewrite
   can turn it into T. *)
val wrapper_spare_goal : Abbrev.goal =
  ([], ``EMPTY SUBSET (clasimp_wrapper_set : 'a set)``)

val wrapper_control_ss =
  simpLib.++
    (simpLib.clear_rules (clasimpLib.clasimp_ss ()),
     simpLib.named_rewrites_with_names "clasimp-wrapper-control"
       [(wrapper_control_name,
         CONJUNCT2 (CONJUNCT2 boolTheory.NOT_CLAUSES)),
        (wrapper_spare_name, pred_setTheory.EMPTY_SUBSET)])

(* [clasimpSelftest] names no loaded theory, and that is the point: the
   explicit [ExclX "rule:..."] control excludes the installed source name
   without interpreting its theory part as a loaded ancestor.

   Failing to close the goal is how the search reports both a control that
   took effect and a control the simp step refused -- [NTactical.LIFT]
   turns the refusal into the same "no result" -- so neither direction is
   asserted on its own.  Each name is excluded in turn, and each run must
   still close the other name's goal: a control that raised, or that never
   reached the embedded simp step, could not close one goal while losing
   the other. *)
val _ =
  check
    ("add_simp_wrapper passes controls to its embedded simp step",
     fn () =>
       let
         fun fast controls =
           NTactical.DETERM
             (classicalLib.CS_FAST_TAC
                (clasimpLib.add_simp_wrapper wrapper_control_ss controls
                   clasetLib.empty_cs))
         val without_control =
           [markerLib.ExclX "rule:clasimpSelftest.wrapper_control"]
         val without_spare =
           [markerLib.ExclX "rule:clasimpSelftest.wrapper_spare"]
       in
         valid_closes (fast []) wrapper_goal andalso
         valid_closes (fast []) wrapper_spare_goal andalso
         valid_closes (fast without_control) wrapper_spare_goal andalso
         tactic_fails (fast without_control) wrapper_goal andalso
         valid_closes (fast without_spare) wrapper_goal andalso
         tactic_fails (fast without_spare) wrapper_spare_goal
       end)

val _ =
  check
    ("re-adding a simp wrapper overwrites its named slot",
     fn () =>
       let
         val inert_ss =
           simpLib.clear_rules (clasimpLib.clasimp_ss ())
         val unsafe_cs =
           clasimpLib.add_simp_wrapper inert_ss []
             (clasimpLib.add_simp_wrapper wrapper_ss []
               clasetLib.empty_cs)
         val safe_cs =
           clasimpLib.add_safe_simp_wrapper inert_ss []
             (clasimpLib.add_safe_simp_wrapper wrapper_ss []
               clasetLib.empty_cs)
         val unsafe =
           NTactical.DETERM (classicalLib.CS_FAST_TAC unsafe_cs)
         val safe =
           NTactical.DETERM (classicalLib.CS_SAFE_TAC safe_cs)
       in
         tactic_fails unsafe wrapper_goal andalso
         tactic_fails safe wrapper_goal
       end)

val _ =
  check
    ("safe simp wrapper preserves rigid engine metavariables",
     fn () =>
       let
         val (meta, store) =
           clasetMeta.new_meta {allow = [], ty = Type.bool}
             clasetMeta.empty
         val target = combinSyntax.mk_I meta
         val node =
           clasetGoal.create
             {goals = [{params = [], asl = [], w = target}],
              store = store, level = 0}
         val ss =
           simpLib.++
             (simpLib.clear_rules (clasimpLib.clasimp_ss ()),
              simpLib.rewrites [combinTheory.I_THM])
         val cs =
           clasimpLib.add_safe_simp_wrapper ss [] clasetLib.empty_cs
       in
         case seq.cases (clasetStep.safe_step_in (Context.snapshot ())
                           cs (node, 1)) of
             NONE => false
           | SOME ((_, next), _) =>
               (case clasetGoal.goals next of
                    [{w, ...}] =>
                      Term.aconv w meta andalso
                      not
                        (null
                          (clasetMeta.metas_of
                            (clasetGoal.store next) w))
                  | _ => false)
       end)

val force_logic_goals : Abbrev.goal list =
  [([], ``((P ==> Q) /\ P) ==> Q``),
   ([], ``(!x:'a. P x ==> Q x) ==> P a ==> Q a``),
   ([], ``(P \/ Q) ==> (P ==> R) ==> (Q ==> R) ==> R``)]

val force_native_goals : Abbrev.goal list =
  [([], ``MEM (x:'a) (x :: xs)``),
   ([], ``THE (SOME (x:'a)) = x``),
   ([],
    ``((x:'a) IN (s UNION t)) =
      (x IN s \/ x IN t)``)]

val force_goals = force_logic_goals @ force_native_goals

val beta_force_goal : Abbrev.goal =
  ([], ``(\proposition. proposition)
          (((P ==> Q) /\ P) ==> Q)``)

val nested_beta_force_goal : Abbrev.goal =
  ([],
   ``((\left : 'a -> 'b option.
         \right : 'a -> 'b option.
         !key value.
           left key = SOME value ==> right key = SOME value)
       (\query. if query = x then NONE else f query)
       f)``)

val force_tactics =
  [("FASTFORCE_TAC", clasimpLib.FASTFORCE_TAC []),
   ("SLOWSIMP_TAC", clasimpLib.SLOWSIMP_TAC []),
   ("BESTSIMP_TAC", clasimpLib.BESTSIMP_TAC [])]

fun force_battery (name, tactic) =
  check
    (name ^ " solves logical and set/list/option batteries",
     fn () => List.all (valid_closes tactic) force_goals)

val _ = List.app force_battery force_tactics

val _ =
  check
    ("FORCE_TAC restores a beta-normalized target",
     fn () =>
       List.all
         (valid_closes (clasimpLib.FORCE_TAC []))
         [beta_force_goal, nested_beta_force_goal])

val _ =
  check
    ("AUTO_TAC restores an eta-normalized target",
     fn () =>
       case Tactical.VALID (clasimpLib.AUTO_TAC [])
              ([], ``(\value : bool. predicate value) = predicate``) of
           ([], validation) => (ignore (validation []); true)
         | _ => false)

(* Isabelle's higher-order patterns are matched modulo eta, so a rewrite
   rule about a partial application fires on a goal spelled as its
   eta-expansion.  HOL4 matches up to alpha and beta only, so the
   clasimpset carries ETA_ss to contract the goal first.  The rule is
   assumed here rather than taken from a seed, and it is handed to the
   simpset rather than to a tactic, because a search that sees the rule
   as an assumption closes such a goal without any eta step -- it is the
   rewriting that stops at the mismatch. *)
val eta_matching_rule =
  Thm.ASSUME
    ``!start count. EVERY eta_matching_p (GENLIST ($+ start) count)``

val eta_matching_goal =
  ``EVERY eta_matching_p (GENLIST (\offset. eta_matching_base + offset) len)``

val _ =
  check
    ("the clasimpset matches a rule across an eta step",
     fn () =>
       let
         val rewritten =
           simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) [eta_matching_rule]
             eta_matching_goal
       in
         Term.aconv (boolSyntax.rhs (Thm.concl rewritten)) boolSyntax.T
       end
       handle Conv.UNCHANGED => false)

val transport_p_def =
  new_definition
    ("transport_p_def", ``transport_p (n:num) <=> n = 0``)
val transport_q_def =
  new_definition
    ("transport_q_def", ``transport_q (n:num) <=> n = 0``)
val transport_r_def =
  new_definition
    ("transport_r_def", ``transport_r (n:num) <=> n = 0``)
val transport_bridge =
  Tactical.prove
    (``!n. transport_p n <=> transport_q n``,
     Rewrite.REWRITE_TAC
       [transport_p_def, transport_q_def])
val transport_fact =
  Tactical.prove
    (``!n. transport_p n ==> transport_r n``,
     Rewrite.REWRITE_TAC
       [transport_p_def, transport_r_def])
val transport_safe_intro =
  Tactical.prove
    (``!n. transport_r n ==> transport_p n``,
     Rewrite.REWRITE_TAC
       [transport_p_def, transport_r_def])
val transport_poly_p_def =
  new_definition
    ("transport_poly_p_def",
     ``transport_poly_p (x:'a) <=> (x = x)``)
val transport_poly_q_def =
  new_definition
    ("transport_poly_q_def",
     ``transport_poly_q (x:'a) <=> (x = x)``)
val transport_poly_r_def =
  new_definition
    ("transport_poly_r_def",
     ``transport_poly_r (x:'a) <=> (x = x)``)
val transport_poly_bridge =
  Tactical.prove
    (``!x:'a. transport_poly_p x <=> transport_poly_q x``,
     Rewrite.REWRITE_TAC
       [transport_poly_p_def, transport_poly_q_def])
val transport_poly_fact =
  Tactical.prove
    (``!x:'a. transport_poly_p x ==> transport_poly_r x``,
     Rewrite.REWRITE_TAC
       [transport_poly_p_def, transport_poly_r_def])

val _ =
  check
    ("certified tagged rule view crosses an invocation normal form",
     fn () =>
       let
         val goal =
           ([``transport_q (n:num)``], ``transport_r n``)
       in
         tactic_fails (clasimpLib.AUTO_TAC [transport_fact]) goal andalso
         valid_closes
           (clasimpLib.AUTO_TAC
              [clasetLib.Simp transport_bridge,
               clasetLib.Dest transport_fact])
           goal
       end)

val _ =
  check
    ("safe tagged introduction retains its role after transport",
     fn () =>
       let
         val goal =
           ([``transport_r (n:num)``], ``transport_q n``)
         val without =
           not
             (valid_closes
                (clasimpLib.AUTO_TAC
                   [clasetLib.SIntro transport_safe_intro]) goal
              handle Feedback.HOL_ERR _ => false)
         val with_bridge =
           valid_closes
             (clasimpLib.AUTO_TAC
                [clasetLib.Simp transport_bridge,
                 clasetLib.SIntro transport_safe_intro]) goal
           handle Feedback.HOL_ERR _ => false
       in
         without andalso with_bridge
       end)

val _ =
  check
    ("persistent destruction rule crosses a supplied normal form",
     fn () =>
       let
         val goal =
           ([``transport_q (n:num)``], ``transport_r n``)
         val cs =
           clasetLib.add_sdests
             [("persistent_transport", transport_fact)]
             clasetLib.empty_cs
         val ss =
           simpLib.++
             (clasimpLib.clasimp_ss (),
              simpLib.rewrites [transport_bridge])
         val without =
           clasimpLib.CS_AUTO_TAC {blast = 4, depth = 2}
             cs (clasimpLib.clasimp_ss ())
         val public =
           clasetLib.with_claset cs
             (fn () =>
               valid_closes
                 (clasimpLib.AUTO_TAC
                    [clasetLib.Simp transport_bridge]) goal) ()
       in
         tactic_fails without goal andalso
         valid_closes
           (clasimpLib.CS_AUTO_TAC {blast = 4, depth = 2}
              cs ss) goal andalso public
       end)

val _ =
  check
    ("persistent safe introduction reaches CLARSIMP's normal form",
     fn () =>
       let
         val goal =
           ([``transport_r (n:num)``], ``transport_q n``)
         val cs =
           clasetLib.add_sintros
             [("persistent_safe_transport", transport_safe_intro)]
             clasetLib.empty_cs
         val ss =
           simpLib.++
             (clasimpLib.clasimp_ss (),
              simpLib.rewrites [transport_bridge])
       in
         tactic_fails
           (clasimpLib.CS_CLARSIMP_TAC cs
              (clasimpLib.clasimp_ss ())) goal andalso
         valid_closes
           (clasimpLib.CS_CLARSIMP_TAC cs ss) goal
       end)

val _ =
  check
    ("rule transport follows a reverse-ordered chain of rewrite heads",
     fn () =>
       let
         val x = ``x:bool``
         fun define name =
           new_definition
             (name ^ "_def",
              boolSyntax.mk_eq
                (mk_comb (mk_var (name, ``:bool -> bool``), x), boolSyntax.T))
         val definitions = List.tabulate
           (10, fn i => define ("transport_chain_" ^ Int.toString i))
         val terms =
           map (boolSyntax.lhs o snd o boolSyntax.strip_forall o concl)
             definitions
         fun proof term =
           Tactical.prove (boolSyntax.mk_forall (x, term),
                           Rewrite.REWRITE_TAC definitions)
         val bridges =
           ListPair.map (proof o boolSyntax.mk_eq)
             (terms, tl terms)
         val cs = clasetLib.add_sintros
           [("chain_intro", proof (hd terms))] clasetLib.empty_cs
         val base = clasimpLib.clasimp_ss ()
         val ss = simpLib.++ (base, simpLib.rewrites bridges)
         val goal = ([], List.last terms)
         val auto = clasimpLib.CS_AUTO_TAC {blast = 4, depth = 2} cs
       in
         tactic_fails (auto base) goal andalso valid_closes (auto ss) goal
       end)

val _ =
  check
    ("contextual FORCE uses a persistent rule's certified view",
     fn () =>
       let
         val goal =
           ([``transport_q (n:num)``], ``transport_r n``)
         val cs =
           clasetLib.add_sdests
             [("force_persistent_transport", transport_fact)]
             clasetLib.empty_cs
         val ss =
           simpLib.++
             (clasimpLib.clasimp_ss (),
              simpLib.rewrites [transport_bridge])
         val saved = !clasimpLib.force_schedule
         val best_only =
           {best = #best saved, tableau = #tableau saved,
            depth = #depth saved, blast_depth = 0,
            classical_depth = 0}
       in
         Lib.with_flag (clasimpLib.force_schedule, best_only)
           (fn () =>
             tactic_fails
               (clasimpLib.CS_FORCE_TAC cs
                  (clasimpLib.clasimp_ss ())) goal andalso
             valid_closes (clasimpLib.CS_FORCE_TAC cs ss) goal) ()
       end)

val _ =
  check
    ("persistent rule transport is independent of the carrier type",
     fn () =>
       let
         val cs =
           clasetLib.add_sdests
             [("polymorphic_persistent_transport",
               transport_poly_fact)]
             clasetLib.empty_cs
         val ss =
           simpLib.++
             (clasimpLib.clasimp_ss (),
              simpLib.rewrites [transport_poly_bridge])
         val goals =
           [([``transport_poly_q (n:num)``],
             ``transport_poly_r (n:num)``),
            ([``transport_poly_q (b:bool)``],
             ``transport_poly_r (b:bool)``)]
       in
         tactic_fails
           (clasimpLib.CS_AUTO_TAC {blast = 4, depth = 2}
              cs (clasimpLib.clasimp_ss ()))
           (hd goals) andalso
         List.all
           (valid_closes
              (clasimpLib.CS_AUTO_TAC {blast = 4, depth = 2}
                 cs ss)) goals
       end)

val _ =
  check
    ("an iff-derived rule cannot normalize using its own source",
     fn () =>
       let
         val source =
           CONJUNCT2 (CONJUNCT2 boolTheory.NOT_CLAUSES)
         val cs =
           List.foldl
             (fn ((spec, named), current) =>
               clasetLib.add_derived_rule spec named current)
             clasetLib.empty_cs
             (clasetLib.iff_rules "transport_iff_source"
                source)
         val ss =
           simpLib.++
             (clasimpLib.clasimp_ss (),
              simpLib.rewrites [source])
       in
         Lib.total
           (Timeout.apply (Time.fromSeconds 5)
              (tactic_fails
                 (clasimpLib.CS_AUTO_TAC {blast = 2, depth = 1}
                    cs ss)))
           ([], ``unrelated_transport_goal:bool``) = SOME true
       end)

(* The same mismatch one spelling further on.  Isabelle normalises the
   numeral 1 to [Suc 0] -- One_nat_def is simp there -- so a rule stated
   on SUC fires against a goal that spells the number as a numeral.
   HOL4 normalises the other way, and the clasimpset carries
   SUC_FILTER_ss to derive the numeral-matching variant of a SUC rule as
   it enters.  The rule is assumed and handed to the simpset for the
   same reason as the eta case above. *)
val suc_matching_rule =
  Thm.ASSUME ``!count. suc_matching_f (SUC count) = suc_matching_g count``

val suc_matching_goal = ``suc_matching_f 3 = suc_matching_g 2``

val _ =
  check
    ("the clasimpset matches a rule across a numeral and SUC",
     fn () =>
       let
         val rewritten =
           simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) [suc_matching_rule]
             suc_matching_goal
       in
         Term.aconv (boolSyntax.rhs (Thm.concl rewritten)) boolSyntax.T
       end
       handle Conv.UNCHANGED => false)

val extensional_search_goals : Abbrev.goal list =
  [([],
    ``(\value : 'a. left value /\ right value) =
      (\value. right value /\ left value)``),
   ([],
    ``(\first : 'a. \second : 'b.
          relation first second /\ guard first second) =
      (\first. \second.
          guard first second /\ relation first second)``)]

val _ =
  check
    ("AUTO and FORCE normalize nested function equality once",
     fn () =>
       List.all
         (valid_closes (clasimpLib.AUTO_TAC []))
         extensional_search_goals andalso
       List.all
         (valid_closes (clasimpLib.FORCE_TAC []))
         extensional_search_goals)

val context_force_tactics =
  [("CS_FASTFORCE_TAC", clasimpLib.CS_FASTFORCE_TAC),
   ("CS_SLOWSIMP_TAC", clasimpLib.CS_SLOWSIMP_TAC),
   ("CS_BESTSIMP_TAC", clasimpLib.CS_BESTSIMP_TAC)]

fun context_force_battery (name, tactic) =
  check
    (name ^ " uses the supplied claset and simpset",
     fn () =>
       List.all
         (valid_closes
            (tactic (clasetLib.the_claset ())
              (clasimpLib.clasimp_ss ())))
         force_logic_goals)

val _ = List.app context_force_battery context_force_tactics

val force_negative_goal : Abbrev.goal =
  ([], ``clasimp_force_unprovable:bool``)

fun force_must_close (name, tactic) =
  check
    (name ^ " fails instead of returning an open residue",
     fn () => tactic_fails tactic force_negative_goal)

val _ = List.app force_must_close force_tactics

val _ =
  List.app
    (fn (name, tactic) =>
      force_must_close
        (name,
         tactic (clasetLib.the_claset ())
           (clasimpLib.clasimp_ss ())))
    context_force_tactics

val _ =
  check
    ("CLARSIMP_TAC returns an exact non-closing residue",
     fn () =>
       let
         val goal = ([], ``clasimp_p ==> clasimp_q``)
         val expected =
           [([], ``clasimp_q:bool``)]
         val actual =
           residual (clasimpLib.CLARSIMP_TAC []) goal
       in
         same_goals actual expected
       end)

val _ =
  check
    ("CS_CLARSIMP_TAC uses the supplied claset and simpset",
     fn () =>
       valid_closes
         (clasimpLib.CS_CLARSIMP_TAC
            (clasetLib.the_claset ())
            (clasimpLib.clasimp_ss ()))
         ([], ``THE (SOME (clasimp_cs_x:'a)) =
                clasimp_cs_x``))

val _ =
  check
    ("CLARSIMP_TAC accepts simplification-only progress",
     fn () =>
       let
         val goal =
           ([], ``T /\ clasimp_simp_residue``)
         val expected =
           [([], ``clasimp_simp_residue:bool``)]
       in
         same_goals
           (residual (clasimpLib.CLARSIMP_TAC []) goal)
           expected
       end)

val _ =
  check
    ("CLARSIMP_TAC solves set/list/option simplification goals",
     fn () =>
       List.all
         (valid_closes (clasimpLib.CLARSIMP_TAC []))
         force_native_goals)

val _ =
  check
    ("CLARSIMP_TAC fails exactly when its script changes nothing",
     fn () =>
       tactic_fails
         (clasimpLib.CLARSIMP_TAC [])
         ([], ``clasimp_clarsimp_unchanged:bool``))

val _ =
  check
    ("CS_CLARSIMP_TAC fails exactly when its script changes nothing",
     fn () =>
       tactic_fails
         (clasimpLib.CS_CLARSIMP_TAC
            (clasetLib.the_claset ())
            (clasimpLib.clasimp_ss ()))
         ([], ``clasimp_cs_clarsimp_unchanged:bool``))

val _ =
  check
    ("CLARSIMP_TAC still splits a conditional assumption",
     fn () =>
       let
         val goal =
           ([``P (if b then x:'a else y) : bool``],
            ``clasimp_split_residue:bool``)
         val residues =
           residual (clasimpLib.CLARSIMP_TAC []) goal
         fun clean (assumptions, conclusion) =
           not
             (List.exists
                (can (find_term boolSyntax.is_cond))
                (conclusion :: assumptions))
       in
         length residues = 2 andalso List.all clean residues
       end)

val auto_logic_goals : Abbrev.goal list =
  [([], ``((P ==> Q) /\ P) ==> Q``),
   ([], ``(!x:'a. P x ==> Q x) ==> P a ==> Q a``),
   ([], ``(P \/ Q) ==> (P ==> R) ==> (Q ==> R) ==> R``),
   ([], ``(~P ==> P) ==> P``)]

val auto_native_goals : Abbrev.goal list =
  [([], ``MEM (x:'a) (x :: xs)``),
   ([], ``THE (SOME (x:'a)) = x``),
   ([],
    ``((x:'a) IN (s UNION t)) =
      (x IN s \/ x IN t)``)]

val auto_goals = auto_logic_goals @ auto_native_goals

val _ =
  check
    ("AUTO_TAC solves translated auto regressions and HOL4 goals",
     fn () =>
       List.all
         (valid_closes (clasimpLib.AUTO_TAC []))
         auto_goals)

(* A commuting assumption applied in the direction the term order does
   not take downwards.  Read schematically the rule is permutative and is
   refused; with its condition discharged from the goal's own assumption
   the terms it speaks of are local constants to matching, and what is
   left is an ordinary rewrite at one redex.  Only after it has fired
   does the conditional assumption close the goal -- the condition holds
   of [clasimp_perm_a], which the commutation moves into the argument
   that assumption reads.  Dropping the condition's assumption takes the
   instance away and nothing else closes the goal, which is what says the
   rewrite is doing the work.  Nothing here is a benchmark entry. *)
val permutation_rule =
  ``!x y : num. clasimp_perm_R x y ==> (x - y = y - x)``

val permutation_condition =
  ``clasimp_perm_R (clasimp_perm_a : num) (clasimp_perm_b : num) : bool``

val permutation_context =
  [``EVEN (clasimp_perm_a : num)``,
   ``!x y : num. EVEN y ==> EVEN (x - y)``]

val permutation_target =
  ``EVEN ((clasimp_perm_a : num) - (clasimp_perm_b : num))``

val _ =
  check
    ("AUTO_TAC commutes an assumption at the redex its condition pins",
     fn () =>
       valid_closes (clasimpLib.AUTO_TAC [])
         (permutation_rule :: permutation_condition :: permutation_context,
          permutation_target))

val _ =
  check
    ("AUTO_TAC leaves a commuting assumption alone with nothing to pin it",
     fn () =>
       let
         val goal = (permutation_rule :: permutation_context,
                     permutation_target)
       in
         tactic_fails (clasimpLib.AUTO_TAC []) goal orelse
         not (valid_closes (clasimpLib.AUTO_TAC []) goal)
       end)

val _ =
  check
    ("AUTO_TAC instantiates one commuting assumption at distinct redexes",
     fn () =>
       valid_closes (clasimpLib.AUTO_TAC [])
         (permutation_rule :: permutation_condition :: permutation_context @
          [``clasimp_perm_R (clasimp_perm_e : num)
                            (clasimp_perm_f : num) : bool``,
           ``EVEN (clasimp_perm_e : num)``,
           ``(clasimp_perm_Q : num -> bool)
              ((clasimp_perm_c : num) - (clasimp_perm_d : num))``],
          boolSyntax.mk_conj
            (permutation_target,
             ``EVEN ((clasimp_perm_e : num) - (clasimp_perm_f : num))``)))

val auto_linarith_rewrite =
  hd (Drule.CONJUNCTS arithmeticTheory.MIN_EQ_LE)

val auto_linarith_tactic =
  clasimpLib.AUTO_TAC
    [clasetLib.Simp auto_linarith_rewrite]

val auto_linarith_goal : Abbrev.goal =
  ([``(x:num) <= y``, ``y <= z``], ``MIN x z = x``)

val _ =
  check
    ("AUTO_TAC discharges a linear-arithmetic rewrite condition",
     fn () => valid_closes auto_linarith_tactic auto_linarith_goal)

val auto_arith_fact_goal : Abbrev.goal =
  ([``(x:num) ** 2 <= y``], ``MIN x y = x``)

val _ =
  check
    ("AUTO_TAC reads [arith] facts dynamically and leaves the set clean",
     fn () =>
       tactic_fails auto_linarith_tactic auto_arith_fact_goal andalso
       with_arith_fact
         (fn () =>
           valid_closes auto_linarith_tactic auto_arith_fact_goal) andalso
       tactic_fails auto_linarith_tactic auto_arith_fact_goal)

fun unbudgeted_in ctxt =
  simpLib.ASM_SIMP_TAC (clasimpLib.clasimp_ss_of ctxt)
    [auto_linarith_rewrite]

val _ =
  check
    ("the unbudgeted clasimp simpset reads the [arith] set of its context",
     fn () => follows_arith_context unbudgeted_in
                 auto_arith_fact_goal)

val _ =
  check
    ("AUTO_TAC reads the [arith] set of its context",
     fn () => follows_arith_context (fn _ => auto_linarith_tactic)
                 auto_arith_fact_goal)

(* A proof's clasimp.trace setting is that of the context its tactic is
   applied in, which here differs from the ambient one both ways.  Only
   the stage that solves the goal reports, so a goal no stage solves
   reports nothing. *)
fun auto_trace_messages ambient level goal =
  let
    val messages = ref ([] : string list)
    val ctxt =
      HOLFlags.set_flagC (traceUtil.flag clasimpLib.tracer, level)
        (Context.snapshot ())
    fun run () =
      SOME (#1 (SelfTestTactical.VALID (clasimpLib.AUTO_TAC []) goal ctxt))
      handle HOL_ERR _ => NONE
    val residues =
      HOLFlags.with_flags [(traceUtil.flag clasimpLib.tracer, ambient)]
        (Lib.with_flag (Feedback.MESG_outstream,
           fn message => messages := message :: !messages)
           (Context.in_proof run)) ()
  in
    (residues,
     List.filter (String.isSubstring "search solved at stage")
       (!messages))
  end

val _ =
  check
    ("AUTO_TAC traces at the level of the context it is applied in",
     fn () =>
       let
         val witnessed =
           ([], ``(?x:'a. P x) /\ (!x. P x ==> Q x) ==> ?x. Q x``)
         val unwitnessed = ([], ``?x:'a. P x``)
       in
         (case auto_trace_messages 0 1 witnessed of
              (SOME [], [_]) => true
            | _ => false) andalso
         (case auto_trace_messages 1 0 witnessed of
              (SOME [], []) => true
            | _ => false) andalso
         (case auto_trace_messages 0 1 unwitnessed of
              (NONE, []) => true
            | _ => false)
       end)

(* Isabelle's arithmetic simprocs answer an atom wherever the traversal
   meets one, so the layer's simpset carries a decision procedure beside
   its rewrites.  An implication between two bounds is a rewrite for
   nothing: only that procedure closes it. *)
val auto_arith_atom = ``~((m:num) < n) ==> ~(SUC m < n)``

val _ =
  check
    ("the simpset decides an arithmetic atom rewriting leaves standing",
     fn () =>
       aconv
         (boolSyntax.rhs (concl
            (Conv.QCONV
              (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) [])
              auto_arith_atom)))
         boolSyntax.T)

(* The other half of that layer: deciding an atom is not normalising a
   term, and two spellings of one sum must not be left side by side for
   the search to rediscover. *)
val auto_arith_spellings =
  (``(x:num) + (y + z)``, ``(z:num) + (y + x)``)

val _ =
  check
    ("the simpset gives two spellings of a sum one normal form",
     fn () =>
       let
         fun normal_form tm =
           boolSyntax.rhs (concl
             (Conv.QCONV
               (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) []) tm))
       in
         aconv (normal_form (fst auto_arith_spellings))
               (normal_form (snd auto_arith_spellings))
       end)

val _ =
  check
    ("CS_AUTO_TAC uses the supplied claset and simpset",
     fn () =>
       List.all
         (valid_closes
            (clasimpLib.CS_AUTO_TAC {blast = 4, depth = 2}
              (clasetLib.the_claset ())
              (clasimpLib.clasimp_ss ())))
         auto_logic_goals)

val _ =
  check
    ("AUTO_DEPTH_TAC accepts explicit blast and depth bounds",
     fn () =>
       let
         val x = mk_var ("clasimp_auto_depth_x", Type.ind)
         val y = mk_var ("clasimp_auto_depth_y", Type.ind)
         val body =
           boolSyntax.mk_conj
             (boolSyntax.mk_eq (x, x), boolSyntax.mk_eq (y, y))
         val goal =
           ([], boolSyntax.mk_exists
             (x, boolSyntax.mk_exists (y, body)))
         fun auto blast =
           clasimpLib.CS_AUTO_TAC {blast = blast, depth = 0}
             (clasetLib.the_claset ()) simpLib.empty_ss
         val witness = mk_var ("clasimp_auto_witness", Type.ind)
         val constant = mk_var ("clasimp_auto_constant", Type.ind)
         val predicate =
           mk_var
             ("clasimp_auto_predicate", Type.ind --> Type.bool)
         val fact = mk_comb (predicate, constant)
         val depth_goal =
           ([fact], boolSyntax.mk_exists
             (witness, mk_comb (predicate, witness)))
         fun depth_auto depth =
           clasimpLib.CS_AUTO_TAC {blast = 0, depth = depth}
             (clasetLib.the_claset ()) simpLib.empty_ss
       in
         tactic_fails (auto 1) goal andalso
         valid_closes (auto 2) goal andalso
         tactic_fails (depth_auto 0) depth_goal andalso
         valid_closes (depth_auto 1) depth_goal andalso
         valid_closes
           (clasimpLib.AUTO_DEPTH_TAC {blast = 4, depth = 2} [])
           ([], ``(~clasimp_auto_bound_p ==>
                    clasimp_auto_bound_p) ==>
                   clasimp_auto_bound_p``)
       end)

val _ =
  check
    ("AUTO_TAC returns an exact non-closing residue",
     fn () =>
       let
         val goal =
           ([], ``clasimp_auto_p ==> clasimp_auto_q``)
         val expected =
           [([], ``clasimp_auto_q:bool``)]
       in
         same_goals
           (residual (clasimpLib.AUTO_TAC []) goal)
           expected
       end)

val _ =
  check
    ("AUTO_TAC fails exactly when its script changes nothing",
     fn () =>
       tactic_fails
         (clasimpLib.AUTO_TAC [])
         ([], ``clasimp_auto_unchanged:bool``))

val _ =
  check
    ("CS_AUTO_TAC fails exactly when its script changes nothing",
     fn () =>
       tactic_fails
         (clasimpLib.CS_AUTO_TAC {blast = 4, depth = 2}
            (clasetLib.the_claset ())
            (clasimpLib.clasimp_ss ()))
         ([], ``clasimp_cs_auto_unchanged:bool``))

val auto_idempotence_goals : Abbrev.goal list =
  [([], ``T /\ clasimp_auto_stable_a``),
   ([], ``clasimp_auto_stable_b ==> clasimp_auto_stable_c``),
   ([``P (if clasimp_auto_stable_b then x:'a else y) : bool``],
    ``clasimp_auto_stable_d:bool``)]

val _ =
  check
    ("AUTO_TAC residues are idempotent without blast instantiations",
     fn () =>
       List.all
         (fn goal =>
           let
             val residues =
               residual (clasimpLib.AUTO_TAC []) goal
           in
             not (null residues) andalso
             List.all
               (tactic_fails (clasimpLib.AUTO_TAC []))
               residues
           end)
         auto_idempotence_goals)

fun goal_has_cond (assumptions, conclusion) =
  List.exists
    (can (find_term boolSyntax.is_cond))
    (conclusion :: assumptions)

val _ =
  check
    ("AUTO_TAC splits if where srw_ss simplification does not",
     fn () =>
       let
         val goal =
           ([``P (if clasimp_auto_split_b then
                    clasimp_auto_split_x:'a
                  else clasimp_auto_split_y) : bool``],
            ``clasimp_auto_split_result:bool``)
         val plain =
           residual
             (simpLib.SIMP_TAC (BasicProvers.srw_ss ()) [])
             goal
         val automatic =
           residual (clasimpLib.AUTO_TAC []) goal
       in
         case plain of
             [residue] =>
               goal_has_cond residue andalso
               length automatic = 2 andalso
               not (List.exists goal_has_cond automatic)
           | _ => false
       end)

val _ =
  check
    ("AUTO_TAC splits datatype cases where srw_ss does not",
     fn () =>
       let
         val goal =
           ([``P (case xs:'a list of
                    [] => clasimp_auto_case_x
                  | h::t => clasimp_auto_case_y) : bool``],
            ``clasimp_auto_case_result:bool``)
         val plain =
           residual
             (simpLib.SIMP_TAC (BasicProvers.srw_ss ()) [])
             goal
         val automatic =
           residual (clasimpLib.AUTO_TAC []) goal
         fun has_case (assumptions, conclusion) =
           List.exists
             (can (find_term TypeBase.is_case))
             (conclusion :: assumptions)
       in
         case plain of
             [residue] =>
               has_case residue andalso
               length automatic = 2 andalso
               not (List.exists has_case automatic)
           | _ => false
       end)

val _ =
  check
    ("FORCE_TAC solves translated force regressions and HOL4 goals",
     fn () =>
       List.all
         (valid_closes (clasimpLib.FORCE_TAC []))
         force_goals)

val _ =
  check
    ("CS_FORCE_TAC uses the supplied claset and simpset",
     fn () =>
       List.all
         (valid_closes
            (clasimpLib.CS_FORCE_TAC
              (clasetLib.the_claset ())
              (clasimpLib.clasimp_ss ())))
         force_goals)

val _ =
  check
    ("FORCE_TAC and CS_FORCE_TAC fail unless they close the goal",
     fn () =>
       tactic_fails
         (clasimpLib.FORCE_TAC [])
         force_negative_goal andalso
       tactic_fails
         (clasimpLib.CS_FORCE_TAC
            (clasetLib.the_claset ())
            (clasimpLib.clasimp_ss ()))
         force_negative_goal)

val force_witness_goals : (string * tactic * Abbrev.goal) list =
  [("complement",
    clasimpLib.FORCE_TAC [],
    ([``value = COMPL (candidate : 'a set)``],
     ``?witness : 'a set. value = COMPL witness``)),
   ("option case",
    clasimpLib.FORCE_TAC [],
    ([],
     ``(if flag then NONE else SOME (value : 'a)) = NONE \/
       ?witness.
         (if flag then NONE else SOME value) = SOME witness``))]

val _ =
  List.app
    (fn (name, tactic, goal) =>
      check
        ("FORCE synthesizes a " ^ name ^ " witness",
         fn () => valid_closes tactic goal))
    force_witness_goals

(* Isabelle's force_tac ends in first_best_tac alone: the method carries
   no tableau leg at all (src/Provers/clasimp.ML:167 @ Isabelle2025-2).
   Ours keeps one, but behind the parity leg rather than in front of it.
   The goal below is a partial map read at two points -- the shape
   Isabelle closes with force and with nothing weaker, neither simp nor
   fastforce nor blast.  Best-first closes it in milliseconds; the
   tableau does not return on it, so with the legs the other way round
   the budget is spent before the leg that carries the parity is
   reached.  The bound is what makes that a failure rather than a hang. *)
val force_partial_map_goal : Abbrev.goal =
  ([``(force_m : 'a -> 'b option) force_x = SOME force_e``,
    ``(force_m : 'a -> 'b option) force_a = NONE``],
   ``?k. (k = force_a ==> force_b = force_e) /\
         (k <> force_a ==> (force_m : 'a -> 'b option) k = SOME force_e)``)

val _ =
  check
    ("FORCE closes a partial-map goal its tableau leg does not return on",
     fn () =>
       Lib.total
         (Timeout.apply (Time.fromSeconds 30)
            (valid_closes (clasimpLib.FORCE_TAC [])))
         force_partial_map_goal = SOME true)

val _ =
  check
    ("FORCE preserves first-best expansions across small turns",
     fn () =>
       let
         val saved = !clasimpLib.force_schedule
         val small =
           {candidates = 1, applications = 1,
            normalization = 1}
         val large =
           {candidates = 5000, applications = 500,
            normalization = 5000}
         fun run slice =
           let
             val budget = searchBudget.unbounded ()
             val _ =
               clasimpLib.force_schedule :=
                 {best = slice, tableau = slice, depth = slice,
                  blast_depth = 0, classical_depth = 0}
             val closed =
               valid_closes
                 (clasimpLib.FORCE_TAC_BUDGETED budget [])
                 force_partial_map_goal
           in
             (closed, searchBudget.usage budget)
           end
         val ((small_closed, small_used),
              (large_closed, large_used)) =
           (run small, run large)
           handle exn =>
             (clasimpLib.force_schedule := saved; raise exn)
         val _ = clasimpLib.force_schedule := saved
       in
         small_closed andalso large_closed andalso
         #applications small_used > 1 andalso
         #applications small_used = #applications large_used
       end)

fun scripted_force_engine name calls outcomes =
  let
    val pending = ref outcomes
  in
    fn () =>
      (calls := !calls @ [name];
       case !pending of
           [] => forceScheduler.Exhausted
         | outcome :: rest =>
             (pending := rest; outcome))
  end

val _ =
  check
    ("FORCE scheduler gives yielding engines one turn per round",
     fn () =>
       let
         val calls = ref []
         val best =
           scripted_force_engine "best" calls
             [forceScheduler.Yielded, forceScheduler.Yielded]
         val tableau =
           scripted_force_engine "tableau" calls
             [forceScheduler.Yielded, forceScheduler.Proved 7]
         val depth =
           scripted_force_engine "depth" calls
             [forceScheduler.Yielded]
       in
         forceScheduler.run [best, tableau, depth] = SOME 7 andalso
         !calls = ["best", "tableau", "depth", "best", "tableau"]
       end)

val _ =
  check
    ("each FORCE engine can be the sole scripted finisher",
     fn () =>
       let
         val names = ["best", "tableau", "depth"]
         fun winner name =
           let
             val calls = ref []
             fun engine candidate =
               scripted_force_engine candidate calls
                 [forceScheduler.Yielded,
                  if candidate = name then forceScheduler.Proved candidate
                  else forceScheduler.Exhausted]
           in
             forceScheduler.run (map engine names) = SOME name andalso
             List.take (!calls, 3) = names
           end
       in
         List.all winner names
       end)

val _ =
  check
    ("FORCE scheduler observes exhaustion of every engine",
     fn () =>
       let
         val calls = ref []
         fun exhausted name =
           scripted_force_engine name calls [forceScheduler.Exhausted]
       in
         forceScheduler.run
           [exhausted "best", exhausted "tableau", exhausted "depth"] =
           NONE andalso
         !calls = ["best", "tableau", "depth"]
       end)

val _ =
  check
    ("FORCE scheduler propagates a shared limit after fair turns",
     fn () =>
       let
         val budget =
           searchBudget.create
             {candidates = NONE, applications = SOME 3,
              normalization = NONE}
         val calls = ref []
         fun yielding name () =
           (calls := !calls @ [name];
            searchBudget.charge budget searchBudget.Application;
            forceScheduler.Yielded)
         val limited =
           ((ignore (forceScheduler.run
              [yielding "best", yielding "tableau", yielding "depth"]);
             false)
            handle searchBudget.LimitReached
                     (searchBudget.Application, usage) =>
                     #applications usage = 3
                 | _ => false)
       in
         limited andalso
         !calls = ["best", "tableau", "depth", "best"]
       end)

val _ =
  check
    ("FORCE reports a shared candidate limit before search",
     fn () =>
       let
         val budget =
           searchBudget.create
             {candidates = SOME 0, applications = NONE,
              normalization = NONE}
       in
         ((ignore
             (Tactical.VALID
                (clasimpLib.FORCE_TAC_BUDGETED budget [])
                force_partial_map_goal);
           false)
          handle searchBudget.LimitReached
                   (searchBudget.Candidate, used) =>
                   #candidates used = 0
               | _ => false)
       end)

val _ =
  check
    ("FORCE rejects an invalid schedule before simplification",
     fn () =>
       let
         val saved = !clasimpLib.force_schedule
         val invalid =
           {best =
              {candidates = 0, applications = 1,
               normalization = 1},
            tableau = #tableau saved, depth = #depth saved,
            blast_depth = #blast_depth saved,
            classical_depth = #classical_depth saved}
         fun run () =
           (clasimpLib.force_schedule := invalid;
            (ignore
               (Tactical.VALID
                  (clasimpLib.FORCE_TAC [])
                  ([], ``T``));
             false)
            handle HOL_ERR _ => true)
         val rejected =
           run ()
           handle exn =>
             (clasimpLib.force_schedule := saved; raise exn)
         val _ = clasimpLib.force_schedule := saved
       in
         rejected
       end)

val staged_branch_goal : Abbrev.goal =
  ([``branch_a1 \/ branch_b1``,
    ``branch_a2 \/ branch_b2``,
    ``branch_a3 \/ branch_b3``,
    ``branch_a4 \/ branch_b4``,
    ``decision ==> result``, ``~decision ==> result``],
   ``result:bool``)

val _ =
  check
    ("staged AUTO and FORCE bypass irrelevant satisfiable branches",
     fn () =>
       valid_closes (clasimpLib.AUTO_TAC []) staged_branch_goal andalso
       valid_closes (clasimpLib.FORCE_TAC []) staged_branch_goal)

val _ =
  check
    ("AUTO_TAC arguments are temporary and leave no state behind",
     fn () =>
       let
         val lhs = ``clasimp_temporary_lhs:'a``
         val goal =
           ([], ``clasimp_temporary_goal:bool``)
         val rules_before =
           length (clasetLib.rules_of (clasetLib.the_claset ()))
         val before_conv =
           Conv.QCONV
             (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) [])
             lhs
         val failed =
           tactic_fails
             (clasimpLib.AUTO_TAC
               [clasetLib.Simp boolTheory.IMP_CLAUSES])
             goal
         val after_conv =
           Conv.QCONV
             (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) [])
             lhs
         val rules_after =
           length (clasetLib.rules_of (clasetLib.the_claset ()))
       in
         failed andalso rules_before = rules_after andalso
         aconv (concl before_conv) (concl after_conv)
       end)

(* An assumption the safe cascade has just stripped must not be rebuilt
   into the conclusion.  The cascade's negation introduction turns a
   goal [~p] into [p |- F], and a simplification that re-forms [p ==> F]
   as [~p] hands the two steps a cycle; safe saturation repeats while
   any step applies, so it never leaves that cycle.  The goal below is
   unprovable -- what is asserted is that the tactic returns at all. *)
val cascade_cycle_goal : goal =
  ([] : term list, ``!x. cycle_q (x:'a) ==> ~cycle_p x``)

val _ =
  check
    ("safe simplification does not undo the cascade's negation step",
     fn () =>
       let
         fun run () =
           (ignore (clasimpLib.AUTO_TAC [] cascade_cycle_goal); true)
           handle HOL_ERR _ => true
       in
         Timeout.apply (Time.fromSeconds 30) run ()
         handle Timeout.TIMEOUT _ => false
       end)

(* The order procedure is in the stack.  This goal is closed by
   chaining two steps the assumptions state through an order the goal
   itself supplies, and nothing else in the stack chains: HOL4 carries
   no order reasoning ambiently, and the premise gives the axioms
   rather than the step.  It is not a benchmark entry. *)
val order_chaining_goal : goal =
  ([] : term list,
   ``!le a b c.
       relation$WeakLinearOrder le ==> le a b ==> le b c ==> le a c``)

val _ =
  check
    ("AUTO_TAC chains a step in an order the goal supplies",
     fn () => valid_closes (clasimpLib.AUTO_TAC []) order_chaining_goal)

val _ =
  check
    ("CLARSIMP charges nested order to its invocation",
     fn () =>
       let
         val funded = searchBudget.unbounded ()
         val closed =
           valid_closes
             (clasimpLib.CLARSIMP_TAC_BUDGETED funded [])
             order_chaining_goal
         val used = searchBudget.usage funded
         val zero =
           searchBudget.create
             {candidates = SOME 0, applications = NONE,
              normalization = NONE}
         val cutoff =
           ((ignore
               (Tactical.VALID
                 (clasimpLib.CLARSIMP_TAC_BUDGETED zero [])
                 order_chaining_goal);
             false)
            handle searchBudget.LimitReached
                     (searchBudget.Candidate, usage) =>
                     #candidates usage = 0
                 | _ => false)
       in
         closed andalso #candidates used > 0 andalso cutoff
       end)

(* The second position the same procedure is asked about: the rewrite
   in the assumptions fires on the conclusion only once its order
   premise is discharged, and the chain that discharges it is the one
   above.  A side condition is simplified with this simpset, so the
   decision procedure reaches it and no separate solver is wired. *)
val order_condition_goal : goal =
  ([] : term list,
   ``!le a b c.
       relation$WeakLinearOrder le ==>
       (!x y. le x y ==> (clasimp_order_f x y <=> T)) ==>
       le a b ==> le b c ==> clasimp_order_f a c``)

val _ =
  check
    ("a conditional rewrite's order premise is discharged",
     fn () => valid_closes (clasimpLib.AUTO_TAC []) order_condition_goal)

(* A first-order step meets a goal the simplification before it left in
   the ambient normal form, and a fact stated some other way misses it.
   The two constants below are the same function, and the rewrite
   between them is the normal form; the fact is stated in the spelling
   the normal form leaves behind, and the goal in the one it produces. *)
val ambient_form_left =
  Definition.new_definition
    ("clasimp_ambient_left_def", ``clasimp_ambient_left (x:'a) = x``)

val ambient_form_right =
  Definition.new_definition
    ("clasimp_ambient_right_def", ``clasimp_ambient_right (x:'a) = x``)

val ambient_variable = mk_var ("x", alpha)

val ambient_normal_form =
  GEN ambient_variable
    (TRANS (SPEC ambient_variable ambient_form_left)
       (SYM (SPEC ambient_variable ambient_form_right)))

val ambient_normalized_goal : goal =
  ([] : term list, ``clasimp_ambient_right (a:'a) = a``)

val _ =
  BasicProvers.augment_srw_ss
    [simpLib.named_rewrites "clasimpAmbientProbe" [ambient_normal_form]]

val _ =
  check
    ("a fact reaches the goal its own spelling misses",
     fn () =>
       tactic_fails (metisLib.METIS_TAC [ambient_form_left])
         ambient_normalized_goal andalso
       valid_closes (clasimpLib.AMBIENT_METIS_TAC [ambient_form_left])
         ambient_normalized_goal)

val _ = BasicProvers.diminish_srw_ss ["clasimpAmbientProbe"]

(* A first-order search instantiates a function variable with an
   abstraction and then has no rule to reduce the redex that leaves, so
   the fact below is unusable in its own goal until the abstraction is
   named.  The constant is local and the goal is not a benchmark entry:
   what is asserted is that naming the abstraction is what closes it. *)
val lifted_application_def =
  Definition.new_definition
    ("clasimp_lifted_application_def",
     ``clasimp_lifted_application (predicate:'a -> bool) (element:'a) =
         predicate element``)

val lifted_application_goal : goal =
  ([], ``clasimp_lifted_application (\y. p y /\ q y) (a:'a) ==> p a``)

val _ =
  check
    ("naming an abstraction lets a fact instantiate a function variable",
     fn () =>
       tactic_fails (metisLib.METIS_TAC [lifted_application_def])
         lifted_application_goal andalso
       valid_closes
         (Tactical.THEN
            (clasimpLib.LAMBDA_LIFT_TAC,
             metisLib.METIS_TAC [lifted_application_def]))
         lifted_application_goal andalso
       valid_closes
         (clasimpLib.AMBIENT_METIS_TAC [lifted_application_def])
         lifted_application_goal)

val _ =
  check
    ("lambda lifting preserves definition order and skips alpha duplicates",
     fn () =>
       let
         val goal =
           ([], ``(!q. f (\x. x /\ q)) /\ f (\x. p x) /\
                  f (\x. x /\ q) /\ f (\y. y /\ q) /\ f (\x. x \/ q)``)
         fun lifted_head definition =
           rator (boolSyntax.lhs (#2 (boolSyntax.dest_forall definition)))
       in
         case residual clasimpLib.LAMBDA_LIFT_TAC goal of
             [([], conclusion)] =>
               (case boolSyntax.strip_imp conclusion of
                    ([first, second], _) =>
                      let
                        val conj_name = lifted_head first
                        val disj_name = lifted_head second
                      in
                        not (aconv conj_name disj_name) andalso
                        aconv conclusion
                          ``(!x. ^conj_name x = (x /\ q)) ==>
                            (!x. ^disj_name x = (x \/ q)) ==>
                            (!q. f (\x. x /\ q)) /\ f (\x. p x) /\
                            f ^conj_name /\ f ^conj_name /\ f ^disj_name``
                      end
                  | _ => false)
           | _ => false
       end)

(* Nothing stands in an argument position, so there is nothing to name
   and the step refuses rather than reproducing the goal. *)
val _ =
  check
    ("the lifting step refuses a goal with no argument abstraction",
     fn () =>
       tactic_fails clasimpLib.LAMBDA_LIFT_TAC
         ([], ``!x:'a. p x ==> q x ==> p x``))

(* What the exclusion drops is a cancellation step the source's simpset
   also takes, so the layer runs HOL4's procedure and respells what it
   returns.  None of the terms below is a benchmark entry. *)
fun simplifies term =
  SOME (boolSyntax.rhs
          (Thm.concl (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) [] term)))
  handle Conv.UNCHANGED => NONE

val _ =
  check
    ("the layer does not renest an append the way HOL4 does",
     fn () =>
       let
         val term = ``(as:'a list) ++ (bs ++ cs)``
         fun renests simp_conv ss =
           (ignore (simp_conv ss [] term); true)
           handle Conv.UNCHANGED => false
       in
         renests simpLib.SIMP_CONV (BasicProvers.srw_ss ()) andalso
         not (renests simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()))
       end)

val _ =
  check
    ("an equation with nothing to cancel is left as it stands",
     fn () =>
       not (isSome (simplifies ``(as:'a list) ++ (bs ++ cs) = ds``)))

(* A common prefix cancels by APPEND_11, which is ambient; matching two
   equations up by their last element is the procedure's own step and
   no rewrite reaches it. *)
val _ =
  check
    ("two equations are still matched up by their last element",
     fn () =>
       case simplifies ``(xs:'a list) ++ [x] = ys ++ [y]`` of
           SOME result =>
             aconv result ``(xs:'a list) = ys /\ (x:'a) = y``
         | NONE => false)

(* The cancellation is HOL4's and leaves what it returns left-nested;
   what this asserts is the respelling that follows it. *)
val _ =
  check
    ("what cancelling leaves is spelled the way the source states it",
     fn () =>
       case simplifies
              ``((as:'a list) ++ (bs ++ cs)) ++ [x] = ds ++ [y]`` of
           SOME result =>
             aconv result
               ``((as:'a list) ++ (bs ++ cs) = ds) /\ (x:'a) = y``
         | NONE => false)

(* One statement written twice.  The HOL4 result answering an Isabelle
   one states the same fact in its own conjunct order and on its own
   side of an equation, and the residual is then an equivalence between
   a term and a permutation of itself.  The decision closes it; it does
   not reorder anything, which is what the two assertions above depend
   on.  None of the terms below is a benchmark entry. *)
val _ =
  check
    ("an equivalence between two permutations of one statement closes",
     fn () =>
       List.all
         (fn term =>
           case simplifies term of
               SOME result => aconv result boolSyntax.T
             | NONE => false)
         [``(clasimp_perm_y = clasimp_perm_x) /\ 0 < clasimp_perm_n <=>
            (clasimp_perm_x = clasimp_perm_y) /\ 0 < clasimp_perm_n``,
          ``0 < clasimp_perm_n /\ clasimp_perm_p clasimp_perm_a <=>
            clasimp_perm_p clasimp_perm_a /\ 0 < clasimp_perm_n``,
          ``(?value.
               clasimp_perm_opt = SOME value /\
               clasimp_perm_y = clasimp_perm_f value) <=>
            ?value.
              clasimp_perm_opt = SOME value /\
              clasimp_perm_f value = clasimp_perm_y``])

val _ =
  check
    ("an equivalence that is not a permutation is left alone",
     fn () =>
       not (isSome (simplifies
         ``(clasimp_perm_p /\ clasimp_perm_q) <=>
           (clasimp_perm_p \/ clasimp_perm_q)``)))

(* src/HOL/HOL.thy declares [disj_not1] simp and HOL4 declares nothing
   in either direction, so a negated existential arrives at a source
   rule as a disjunction where the source states it as an implication.
   The rule below is hypothetical rather than proved: what is under
   test is the shape the simplifier hands its condition solver, and the
   goal is not a benchmark entry. *)
val membership_condition_rule =
  Thm.ASSUME
    ``!xs. (!i. MEM i xs ==> q i) ==> walk (xs:'a list) = xs``

val _ =
  check
    ("a negated existential premise reads as an implication",
     fn () =>
       case simplifies ``~(?i. MEM i (xs:'a list) /\ P i)`` of
           SOME result =>
             aconv result ``!i. MEM i (xs:'a list) ==> ~P i``
         | NONE => false)

val _ =
  check
    ("a side condition is discharged from a negated existential",
     fn () =>
       let
         val (subgoals, _) =
           clasimpLib.asm_full_simp (clasimpLib.clasimp_ss ())
             [membership_condition_rule]
             ([``~(?i. MEM i (as:'a list) /\ ~q i)``],
              ``walk (as:'a list) = as``)
             (Context.snapshot())
       in
         null subgoals
       end)

(* HOL4's simplifier rewrites outermost-first and Isabelle's the other way
   round, and the two differ wherever an ambient rule matches a whole term
   whose subterm the context has already settled.  Below the context
   settles [TAKE n l] to the empty list while the ambient identity matches
   the whole [TAKE n l ++ DROP n l]: taken outermost-first the inserted
   instance collapses to T and the goal loses the equation that would
   close it.  The simpset carries the identity and the empty append and
   nothing else, so no case analysis on the assumption stands in for the
   equation, and the goal is not a benchmark entry. *)
val traversal_ss =
  simpLib.++
    (simpLib.empty_ss,
     simpLib.rewrites [listTheory.TAKE_DROP, CONJUNCT1 listTheory.APPEND])

val traversal_goal : Abbrev.goal =
  ([``TAKE n (l:'a list) ++ DROP n l = l``, ``TAKE n (l:'a list) = []``],
   ``DROP n (l:'a list) = l``)

val _ =
  check
    ("a context equation refines a term the ambient rule would collapse",
     fn () =>
       valid_closes
         (clasimpLib.CS_AUTO_TAC {blast = 4, depth = 2}
            clasetLib.empty_cs traversal_ss)
         traversal_goal)

(* The same divergence the other way round: here the redex the ambient
   rule swallows is one a rule the invocation named would have refined.
   [MEM x (REPLICATE n a)] is a membership the ambient decomposition
   matches whole, and [set (REPLICATE n a)] -- what the rule below is
   stated on -- is a subterm of it, so outermost-first the rule never
   fires and the [if] it would have built is never there to split.  With
   it built the case split carries [n = 0] across the whole goal, which
   is what settles the disjunct on the other side of it.  The goal is
   not a benchmark entry. *)
val replicate_set_rule =
  Tactical.prove
    (``!n (value : 'a).
         LIST_TO_SET (REPLICATE n value) =
         if n = 0 then {} else {value}``,
     Tactical.THEN
       (bossLib.Induct,
        Tactical.THEN
          (BasicProvers.SRW_TAC []
             [rich_listTheory.REPLICATE, pred_setTheory.EXTENSION],
           bossLib.metis_tac [])))

val supplied_subterm_goal : Abbrev.goal =
  ([], ``(!clasimp_replicate_x.
            MEM clasimp_replicate_x
                (REPLICATE clasimp_replicate_n (clasimp_replicate_a : 'a)) ==>
            clasimp_replicate_P clasimp_replicate_x) ==>
         clasimp_replicate_n = 0 \/
         clasimp_replicate_P clasimp_replicate_a``)

val _ =
  check
    ("a supplied rewrite refines a subterm the ambient rule would swallow",
     fn () =>
       let
         val (subgoals, _) =
           clasimpLib.asm_full_simp (clasimpLib.clasimp_ss ())
             [replicate_set_rule] supplied_subterm_goal
             (Context.snapshot())
       in
         null subgoals
       end)

(* A tactic that reports no proof has come back, which is what the bound
   below is about; only the timeout distinguishes the two outcomes. *)
fun terminates_within seconds tactic goal =
  (Timeout.apply (Time.fromSeconds seconds)
     (fn () => (ignore (Tactical.VALID tactic goal) handle HOL_ERR _ => ()))
     ();
   true)
  handle Timeout.TIMEOUT _ => false

(* A case analysis on a walk leaves an equation that reproduces its own
   left-hand side among the assumptions.  Read as the invocation's own
   simpset reads it the pass stands it down, the canonicalisation
   recognising a rewrite that would loop; read raw -- an empty simpset
   keeps an assumption as it finds it -- the same equation rewrites
   forever.  The goal is not a benchmark entry and what is asserted is
   that the tactic comes back at all. *)
val self_referential_goal : Abbrev.goal =
  ([``(clasimp_walk_P : 'a -> bool) clasimp_walk_x``,
    ``(clasimp_walk_xs : 'a list) =
        takeWhile ($~ o clasimp_walk_P) clasimp_walk_xs ++
        clasimp_walk_x::clasimp_walk_rest``],
   ``?clasimp_walk_value.
       MEM clasimp_walk_value (clasimp_walk_xs : 'a list) /\
       clasimp_walk_P clasimp_walk_value``)

val _ =
  check
    ("a context equation that reproduces itself does not rewrite forever",
     fn () =>
       terminates_within 30
         (clasimpLib.CS_AUTO_TAC {blast = 4, depth = 2}
            clasetLib.empty_cs (clasimpLib.clasimp_ss ()))
         self_referential_goal)

(* The library states [FUNPOW f 0 x = x] where the source states
   [f ^^ 0 = id], so the goal below and the rule that settles it are the
   same fact at different arities and no rewrite brings them together.
   Neither goal is a benchmark entry.  The first is put to simplification
   alone, which is the method the source's own [simp] names; the search
   tactics reach the same goal through their own root-only
   normalisation, so it says nothing about them. *)
val extensional_goal : Abbrev.goal =
  ([], ``FUNPOW SUC 0 = (I : num -> num)``)

val _ =
  check
    ("an equation between functions meets the applied law that settles it",
     fn () =>
       valid_closes
         (clasimpLib.with_extensionality (clasimpLib.clasimp_ss ())
            (clasimpLib.asm_full_simp (clasimpLib.clasimp_ss ()) []))
         extensional_goal)

(* Simplification leaves the equation under whatever quantifiers and
   implications the goal carried, so the step is looked for there and
   not only at the conclusion's root.  The goal below arrives as neither
   -- it is a quantified implication, which the root-only normalisation
   the search tactics run first declines -- and the equation appears
   only once simplification has stripped it. *)
val nested_extensional_goal : Abbrev.goal =
  ([], ``!clasimp_ext_k.
           (!n. (clasimp_ext_f : num -> num -> num) clasimp_ext_k n =
                clasimp_ext_g clasimp_ext_k n) ==>
           clasimp_ext_f clasimp_ext_k = clasimp_ext_g clasimp_ext_k``)

val _ =
  check
    ("the equation is found under the quantifiers the goal carries",
     fn () =>
       valid_closes
         (clasimpLib.CS_AUTO_TAC {blast = 4, depth = 2}
            clasetLib.empty_cs (clasimpLib.clasimp_ss ()))
         nested_extensional_goal)

(* HOL4 states its set and list facts on [x IN s] -- [x IN set l] is
   [MEM x l] itself -- while an equation taken pointwise as an application
   produces [set (FILTER P xs) x], which none of those facts meet.  Neither
   reading below is a benchmark entry.  The first is put to simplification
   alone, which is the method the source's own [simp] names; the second
   reaches the same reading through the root-only normalisation the search
   tactics run first.  MEM_FILTER is named because it is not ambient in the
   bare simpset the layer's own tests run against; what is under test is
   the reading the equation is given, not which membership facts are
   declared. *)
val membership_goal : Abbrev.goal =
  ([], ``(\clasimp_member. clasimp_ext_p clasimp_member /\
                           MEM clasimp_member clasimp_ext_xs) =
         set (FILTER clasimp_ext_p clasimp_ext_xs)``)

val membership_ss =
  simpLib.++ (lifted_srw_ss (),
              simpLib.rewrites [listTheory.MEM_FILTER])

val _ =
  check
    ("membership inventory reads quantified conjunctive rewrites",
     fn () =>
       let
         val guard = Term.mk_var ("membership_guard", Type.bool)
         val source = Thm.GEN guard
           (Thm.CONJ (Thm.DISCH guard IN_UNION)
              (Thm.CONJ NOT_IN_EMPTY IN_INTER))
         val ss = simpLib.++
           (pureSimps.pure_ss, simpLib.rewrites [source])
         val reads = clasimpLib.reads_as_membership ss
       in
         reads ``(s UNION t : num -> bool) = u`` andalso
         reads ``(EMPTY : num -> bool) = u`` andalso
         reads ``(s INTER t : num -> bool) = u`` andalso
         not (reads ``(s DIFF t : num -> bool) = u``) andalso
         not (reads ``(s : num -> bool) = u``)
       end)

val _ =
  check
    ("an equation between sets meets the rules stated on membership",
     fn () =>
       valid_closes
         (clasimpLib.with_extensionality membership_ss
            (clasimpLib.asm_full_simp membership_ss []))
         membership_goal)

val _ =
  check
    ("the search tactics reach the membership reading as well",
     fn () =>
       valid_closes
         (clasimpLib.CS_AUTO_TAC {blast = 4, depth = 2}
            clasetLib.empty_cs membership_ss)
         membership_goal)

(* The other side of the same choice: where neither side of the equation
   is a set HOL4 states facts about, the applied reading is the one the
   goal's own context is in.  The goal is not a benchmark entry; the
   source's [Collect_cong] is the shape it stands for. *)
val applied_goal : Abbrev.goal =
  ([``!clasimp_ext_element.
        clasimp_ext_p clasimp_ext_element <=>
        clasimp_ext_q clasimp_ext_element /\
        clasimp_ext_r clasimp_ext_element``],
   ``(clasimp_ext_p : 'a -> bool) =
     \clasimp_member.
       clasimp_ext_q clasimp_member /\ clasimp_ext_r clasimp_member``)

val _ =
  check
    ("an equation between predicates keeps the reading its context has",
     fn () =>
       valid_closes
         (clasimpLib.with_extensionality (lifted_srw_ss ())
            (clasimpLib.asm_full_simp (lifted_srw_ss ()) []))
         applied_goal)

(* The reading is this layer's default and not the invocation's.
   [EVERY clasimp_ext_p] is constant-headed at [-> bool] and is no set:
   it is a predicate short of an argument, and every fact about it is
   stated applied, so the default membership reading leaves
   [clasimp_member IN EVERY clasimp_ext_p], which nothing meets.  The
   rewrites below are what a method naming [fun_eq_iff] and
   [list_all_iff] supplies, and they say which reading the equation is
   to be taken in; taken first, the default would put the equation out
   of their reach for good.  Neither the goal nor the rewrites are a
   benchmark entry. *)
val supplied_reading_goal : Abbrev.goal =
  ([], ``EVERY (clasimp_ext_p : 'a -> bool) =
         \clasimp_member.
           !clasimp_element.
             MEM clasimp_element clasimp_member ==>
             clasimp_ext_p clasimp_element``)

val supplied_reading_ss =
  simpLib.++ (lifted_srw_ss (),
              simpLib.rewrites
                [boolTheory.FUN_EQ_THM, listTheory.EVERY_MEM])

val _ =
  check
    ("a supplied rewrite decides the reading of an equation",
     fn () =>
       let
         val target = snd supplied_reading_goal
         val rewrites = [Thm.CONJ listTheory.EVERY_MEM boolTheory.FUN_EQ_THM]
       in
         clasimpLib.reads_as_supplied rewrites target andalso
         not (clasimpLib.reads_as_supplied rewrites (boolSyntax.mk_eq
           (boolSyntax.T, boolSyntax.F))) andalso
         valid_closes
           (clasimpLib.CS_AUTO_TAC {blast = 4, depth = 2}
              clasetLib.empty_cs supplied_reading_ss)
           supplied_reading_goal
       end)

(* Which reading the default takes is decided by the head, not by the
   head being a constant.  [EVERY clasimp_ext_q] is constant-headed at
   [-> bool] and is no set: the simpset states no membership fact about
   it -- no rewrite of its own has [_ IN EVERY ...] for a left-hand side
   -- and every fact it does state is applied, so read as a membership
   the equation meets none of them.  The rewrite below is what a method
   naming [list_all_iff] supplies, and it says nothing about the
   reading; the applied one has to be the default's own choice.  Neither
   the goal nor the rewrite is a benchmark entry. *)
val predicate_reading_goal : Abbrev.goal =
  ([], ``EVERY (clasimp_ext_q : 'a -> bool) =
         \clasimp_subject.
           !clasimp_item.
             MEM clasimp_item clasimp_subject ==>
             clasimp_ext_q clasimp_item``)

val predicate_reading_ss =
  simpLib.++ (lifted_srw_ss (),
              simpLib.rewrites [listTheory.EVERY_MEM])

val _ =
  check
    ("a predicate short of an argument is read applied, not as a set",
     fn () =>
       valid_closes
         (clasimpLib.CS_AUTO_TAC {blast = 4, depth = 2}
            clasetLib.empty_cs predicate_reading_ss)
         predicate_reading_goal)

(* Private opaque rules isolate the atomic wrapper from other engines. *)
fun force_atomic_fixture body =
  let
    val saved_context = Context.snapshot ()
    val saved_schedule = !clasimpLib.force_schedule
    fun restore () =
      (clasimpLib.force_schedule := saved_schedule;
       Context.restore saved_context)
    fun run () =
      let
        val _ = Theory.new_theory "forceAtomicFixture"
        val q_def =
          new_definition
            ("fixture_q_def", ``fixture_q (xs:num list) = T``)
        val r_def =
          new_definition ("fixture_r_def", ``fixture_r = T``)
        val c_def =
          new_definition ("fixture_c_def", ``fixture_c = (0:num)``)
        val q =
          fst (strip_comb (boolSyntax.lhs (concl (Drule.SPEC_ALL q_def))))
        val r = boolSyntax.lhs (concl r_def)
        val c = boolSyntax.lhs (concl c_def)
        val values =
          listSyntax.mk_list
            (c :: List.tabulate (399, fn _ => ``0:num``), numSyntax.num)
        val premise = mk_comb (q, values)
        val intro =
          Tactical.prove
            (boolSyntax.mk_imp (premise, r),
             Rewrite.REWRITE_TAC [q_def, r_def])
        val calls = ref 0
        val counting =
          simpLib.name_ss "FORCE_ATOMIC_FIXTURE"
          (simpLib.std_conv_ss
            {name = "FORCE_ATOMIC_FIXTURE", pats = [c],
             conv = fn tm =>
               (calls := !calls + 1; Conv.REWR_CONV c_def tm)})
        val small =
          {candidates = 5000, applications = 500, normalization = 200}
        val _ =
          clasimpLib.force_schedule :=
            {best = small, tableau = small, depth = small,
             blast_depth = 0, classical_depth = 0}
        fun apply budget =
          Tactical.VALID
            (clasimpLib.FORCE_TAC_BUDGETED budget
               [clasetLib.Intro intro, q_def, simpLib.SF counting])
            ([], r)
      in
        body (calls, apply, r)
      end
  in
    Portable.finally restore run ()
  end;

val _ =
  check
    ("an atomic FORCE wrapper respects the invocation limit",
     fn () =>
       force_atomic_fixture
         (fn (calls, apply, _) =>
           let
             val budget =
               searchBudget.create
                 {candidates = NONE, applications = NONE,
                  normalization = SOME 2000}
             val stopped =
               ((apply budget; false)
                handle searchBudget.LimitReached
                         (searchBudget.Normalization, used) =>
                  #normalization used = 2000)
           in
             stopped andalso !calls > 0 andalso
             #normalization (searchBudget.usage budget) = 2000
           end))

val _ =
  check
    ("an atomic FORCE wrapper runs once across a slice",
     fn () =>
       force_atomic_fixture
         (fn (calls, apply, target) =>
           let
             val budget = searchBudget.unbounded ()
             val (remaining, validate) = apply budget
             val theorem = validate []
           in
             null remaining andalso aconv (concl theorem) target andalso
             null (hyp theorem) andalso !calls = 1 andalso
             #normalization (searchBudget.usage budget) > 200
           end))

(* Generic abstraction rules consume arguments at distinct positions. *)
fun eta_rule_fixture body =
  let
    open boolLib
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = Theory.new_theory "etaRuleFixture"
        val c_def =
          new_definition
            ("eta_c_def", ``eta_c (f:'a -> 'b) (x:'a) = f x``)
        val d_def =
          new_definition
            ("eta_d_def",
             ``eta_d (f:'a -> 'b) (g:'b -> 'c) (x:'a) = g (f x)``)
        val _ = new_constant ("eta_p", Type.bool --> Type.bool)
        val _ = new_constant ("eta_q", Type.bool --> Type.bool)
        val _ = new_constant ("eta_x", Type.bool)
        fun prove_local target =
          Tactical.prove
            (target,
             Tactical.EVERY
               [Rewrite.REWRITE_TAC [c_def, d_def], Tactic.BETA_TAC,
                Rewrite.REWRITE_TAC []])
        val rule =
          prove_local ``!(P:'a -> 'b) x. eta_c (\v. P v) x = P x``
        val target = ``eta_c (\v. eta_p v) eta_x = eta_p eta_x``
        val double_rule =
          prove_local
            ``!(P:'a -> 'b) (Q:'b -> 'c) x.
                eta_d (\v. P v) (\v. Q v) x = Q (P x)``
        val double_target =
          ``eta_d (\v. eta_p v) (\v. eta_q v) eta_x =
            eta_q (eta_p eta_x)``
        fun checked tactic target =
          let
            val (remaining, validate) = Tactical.VALID tactic ([], target)
            val proofs =
              map
                (fn residual =>
                  Tactical.prove_goal
                    (residual,
                     Tactical.EVERY
                       [Tactic.RULE_ASSUM_TAC
                          (Rewrite.REWRITE_RULE [c_def, d_def]),
                        Rewrite.ASM_REWRITE_TAC [c_def, d_def],
                        Tactic.BETA_TAC, Rewrite.ASM_REWRITE_TAC []]))
                remaining
            val theorem = validate proofs
            val _ =
              if aconv (concl theorem) target andalso null (hyp theorem)
              then () else raise Fail "eta fixture validation"
          in remaining end
        val base = clasimpLib.clasimp_ss ()
        fun apply_at ss rules = checked (clasimpLib.asm_full_simp ss rules)
        val apply = apply_at base
        val named =
          simpLib.++
            (base, simpLib.named_rewrites "eta_fixture_fragment" [rule])
        val removed = simpLib.remove_ssfrags ["eta_fixture_fragment"] named
        val filtered = simpLib.filter_rewrites
          (fn (_, th) => not (aconv (concl th) (concl rule))) named
        val plain = ``eta_c eta_p eta_x = eta_p eta_x``
        fun contracted result =
          case result of [([], tm)] => aconv tm plain | _ => false
        val specific_rule = Drule.ISPEC ``eta_p`` rule
        val proper_rule = prove_local
          ``!P x. eta_c (\v:bool. P (~v)) x = P (~x)``
        fun bound_apply viewed arguments =
          let val bound = clasimpLib.prepare_bound_simplification
              traceUtil.silent I (fn () => ()) base arguments
          in checked (clasimpLib.asm_full_simp_bound viewed bound []) end
        fun controls () =
          let
            (* A concrete lambda contracts in a raw F2 pass. F1 may then
               match its certified reduced-LHS view and close the goal. *)
            val scope_results =
              [null (apply_at named [] target),
               contracted (apply_at removed [] target),
               contracted (apply_at filtered [] target),
               contracted (apply_at named
                 [simpLib.ExclSF "eta_fixture_fragment"] target),
               contracted (bound_apply false [specific_rule] target),
               contracted (apply [proper_rule] target),
               null (bound_apply true [specific_rule] target)]
            val _ = print ("ETA_SCOPE_RESULTS " ^ String.concatWith " "
              (map Bool.toString scope_results) ^ "\n")
            val scope_checks = List.all I scope_results
            val public_checks =
              List.all
                (fn tactic =>
                  null (checked (tactic [clasetLib.Simp rule]) target))
                [clasimpLib.AUTO_TAC, clasimpLib.FORCE_TAC,
                 clasimpLib.CLARSIMP_TAC] andalso
              List.all
                (fn tactic => null (checked tactic target))
                [clasimpLib.CS_AUTO_TAC {blast=4, depth=2}
                   (clasetLib.the_claset ()) named,
                 clasimpLib.CS_FORCE_TAC (clasetLib.the_claset ()) named,
                 clasimpLib.CS_CLARSIMP_TAC (clasetLib.the_claset ()) named,
                 clasimpLib.safe_asm_full_simp named []] andalso
              List.all
                (fn tactic => null (checked tactic target))
                [NTactical.DETERM
                   (clasetLib.app_unsafe_wrappers
                      (clasimpLib.add_simp_wrapper base [rule]
                         clasetLib.empty_cs) NTactical.NNO_TAC),
                 NTactical.DETERM
                   (clasetLib.app_safe_wrappers
                      (clasimpLib.add_safe_simp_wrapper base [rule]
                         clasetLib.empty_cs) NTactical.NNO_TAC)]
            fun budget_run () =
              let
                val budget = searchBudget.unbounded ()
                val result = checked
                  (clasimpLib.CLARSIMP_TAC_BUDGETED budget
                     [clasetLib.Simp rule]) target
              in
                (null result, searchBudget.usage budget)
              end
            val (first_closed, first_work) = budget_run ()
            val (second_closed, second_work) = budget_run ()
            val zero = searchBudget.create
              {candidates=NONE, applications=NONE, normalization=SOME 0}
            val cutoff =
              ((ignore (checked
                  (clasimpLib.CLARSIMP_TAC_BUDGETED zero
                     [clasetLib.Simp rule]) target); false)
               handle searchBudget.LimitReached
                 (searchBudget.Normalization, _) => true)
            val budget_checks =
              first_closed andalso second_closed andalso
              first_work = second_work andalso #normalization first_work > 0
              andalso cutoff andalso
              #normalization (searchBudget.usage zero) = 0
          in scope_checks andalso public_checks andalso budget_checks end
      in
        body (apply, rule, target, double_rule, double_target,
              controls)
      end
  in
    Portable.finally (fn () => Context.restore saved) run ()
  end;

val eta_fixture_result =
  eta_rule_fixture
    (fn (apply, rule, target, double_rule, double_target, controls) =>
      let
        val absent = apply [] target
        val installed = apply [rule] target
        val double_absent = apply [] double_target
        val double_installed = apply [double_rule] double_target
      in
        not (null absent) andalso null installed andalso
        not (null double_absent) andalso null double_installed andalso
        controls ()
      end);

val _ =
  (tprint "an installed generic abstraction rule retains its argument";
   if eta_fixture_result then OK ()
   else die "generic abstraction rule lost to eta");

(* A restored context may reuse a name for a different constant identity. *)
fun eta_identity_fixture () =
  let
    open boolLib
    val saved = Context.snapshot ()
    fun declaration () =
      (Theory.new_theory "etaIdentityFixture";
       new_definition
         ("identity_c_def", ``identity_c (f:'a -> 'b) (x:'a) = f x``))
    fun head definition =
      fst (strip_comb (lhs (concl (Drule.SPEC_ALL definition))))
    val (old_head, old_ss) =
      Portable.finally (fn () => Context.restore saved)
        (fn () =>
          let
            val definition = declaration ()
            val rule = Tactical.prove
              (``!P x. identity_c (\v. P v) x = P x``,
               Rewrite.REWRITE_TAC [definition] THEN Tactic.BETA_TAC THEN
               Rewrite.REWRITE_TAC [])
            val ss = simpLib.++
              (simpLib.++ (boolSimps.bool_ss, boolSimps.ETA_ss),
               simpLib.rewrites [rule])
          in (head definition, ss) end) ()
    fun run () =
      let
        val definition = declaration ()
        val _ = new_constant ("identity_p", bool --> bool)
        val new_head = head definition
        val {Thy=old_thy, Name=old_name, ...} = dest_thy_const old_head
        val {Thy=new_thy, Name=new_name, ...} = dest_thy_const new_head
        val distinct = old_thy = new_thy andalso old_name = new_name
                       andalso not (same_const old_head new_head)
        val target =
          ``identity_c (\v. identity_p v) = identity_c identity_p``
        fun checked tactic =
          let
            val (remaining, validate) = Tactical.VALID tactic ([], target)
            val proofs = map
              (fn residual => Tactical.prove_goal
                (residual,
                 Tactic.CONV_TAC
                   (Conv.QCONV (Conv.REDEPTH_CONV Drule.ETA_CONV)) THEN
                 Tactic.REFL_TAC)) remaining
            val theorem = validate proofs
            val _ = if null (hyp theorem) andalso
                       aconv (concl theorem) target then ()
                    else raise Fail "identity fixture validation"
          in null remaining end
        val parent = checked (simpLib.SIMP_TAC old_ss [])
        val child = checked (clasimpLib.asm_full_simp old_ss [])
      in distinct andalso parent andalso child end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ =
  (tprint "abstraction positions distinguish reused constant names";
   if eta_identity_fixture () then OK ()
   else die "abstraction positions conflate retired constants");

(* An unchanged LHS can still depend on a failed condition's reducers. *)
fun lhs_dependency_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = new_theory "viewDependencyFixture"
        val g = new_definition ("dep_g_def", ``dep_g (x:bool) = T``)
        val h = new_definition ("dep_h_def", ``dep_h (x:bool) = T``)
        val c = new_definition ("dep_c_def", ``dep_c (x:bool) = T``)
        val k = new_definition ("dep_k_def", ``dep_k (x:bool) = T``)
        val q = new_definition ("dep_q_def", ``dep_q = T``)
        val opaque = new_definition ("dep_opaque_def", ``dep_opaque = T``)
        fun proof tm = Tactical.prove
          (tm, Rewrite.REWRITE_TAC [g,h,c,k,q,opaque])
        val source = proof ``!x. dep_c (dep_g x) = dep_k x``
        val reducer = proof ``!x. dep_q ==> (dep_g x = dep_h x)``
        val bridge = proof ``!x. dep_k x = dep_c (dep_h x)``
        val blocks = proof ``dep_q = dep_opaque``
        val permits = proof ``dep_q = T``
        fun named name theorem ss = simpLib.++ (ss,
          simpLib.rewrites_with_names
            [({Thy=Theory.current_theory (),Name=name},theorem)])
        fun source_entry ss =
          let
            val charged = ref 0
            val entries = clasimpLib.derive_lhs_view_entries
              (fn () => charged := !charged + 1) ss
            val _ = if List.foldl
              (fn (entry, n) => #normalization entry + n) 0 entries = !charged
              then () else raise Fail "entry charges are incomplete"
            val entry = List.find (fn entry => Option.getOpt
              (Option.map (String.isPrefix "dep_source" o #Name)
                (#1 (#source entry)),false)) entries
          in valOf entry end
        val bare = named "dep_source" source simpLib.empty_ss
        val reducing = named "dep_reduce" reducer
          (named "dep_permit" permits bare)
        val blocked = named "dep_block" blocks reducing
        val attempted = source_entry blocked
        val restored_ss = simpLib.remove_simps ["dep_block"] blocked
        val restored = source_entry restored_ss
        val joined = source_entry (named "dep_bridge" bridge reducing)
        val irreducible = source_entry bare
        fun visited entry tm = List.exists (aconv tm) (#footprint entry)
        val expected = ``!x. dep_c (dep_h x) = dep_k x``
        val view = valOf (#view restored)
        val working = simpLib.++
          (restored_ss,simpLib.rewrite_views [(#origin restored,view)])
        val working_theorem = Conv.QCONV
          (simpLib.SIMP_CONV_CHILD_FIRST
             (Traverse.charge_only (fn () => ())) working [])
          ``dep_c (dep_h (x:bool))``
        val working_entries = clasimpLib.derive_lhs_view_entries
          (fn () => ()) working
        val checks =
          [#rejection attempted = SOME clasimpLib.UnchangedLHS,
           not (Option.isSome (#view attempted)),
           visited attempted ``dep_q``, visited attempted ``dep_opaque``,
           visited attempted ``dep_k (x:bool)``,
           #normalization attempted > 0,
           #rejection restored = NONE,
           null (hyp view) andalso
             aconv (concl (Drule.SPEC_ALL view))
               (#2 (boolSyntax.strip_forall expected)),
           #rejection joined = SOME clasimpLib.JoinableLHS,
           not (Option.isSome (#view joined)),
           #rejection irreducible = SOME clasimpLib.NoReducibleArguments,
           #normalization irreducible = 0,
           visited irreducible ``dep_k (x:bool)``,
           null (hyp working_theorem) andalso
             aconv (boolSyntax.rhs (concl working_theorem)) ``dep_k (x:bool)``,
           length working_entries =
             length (simpLib.rewrite_source_handles restored_ss)]
        val _ = print ("DEPENDENCY_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all (fn ok => ok) checks end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ =
  (tprint "LHS view dependencies include failed conditional attempts";
   if lhs_dependency_fixture () then OK ()
   else die "LHS view dependency inventory or rejection is incomplete");

fun lhs_cache_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = new_theory "viewCacheFixture"
        val g = new_definition ("cache_g_def", ``cache_g (x:bool) = T``)
        val h = new_definition ("cache_h_def", ``cache_h (x:bool) = T``)
        val c = new_definition ("cache_c_def", ``cache_c (x:bool) = T``)
        val k = new_definition ("cache_k_def", ``cache_k (x:bool) = T``)
        val u = new_definition ("cache_u_def", ``cache_u (x:bool) = T``)
        val v = new_definition ("cache_v_def", ``cache_v (x:bool) = T``)
        val q = new_definition ("cache_q_def", ``cache_q = T``)
        val opaque = new_definition ("cache_opaque_def", ``cache_opaque = T``)
        fun proof tm = Tactical.prove
          (tm,Rewrite.REWRITE_TAC [g,h,c,k,u,v,q,opaque])
        val original = proof ``!x. cache_c (cache_g x) = cache_k x``
        val reducer = proof ``!x. cache_g x = cache_h x``
        val unrelated = proof ``!x. cache_u x = cache_v x``
        val bridge = proof ``!x. cache_k x = cache_c (cache_h x)``
        val conditional = proof ``!x. cache_q ==> (cache_g x = cache_h x)``
        val permits = proof ``cache_q = T``
        val blocks = proof ``cache_q = cache_opaque``
        fun named name theorem ss = simpLib.++ (ss,
          simpLib.name_ss name (simpLib.rewrites_with_names
            [({Thy=Theory.current_theory (),Name=name},theorem)]))
        val charged = ref 0
        val raw_get = clasimpLib.make_lhs_view_cache
          (fn () => charged := !charged + 1)
        val generations = ref (HOLset.empty Int.compare)
        fun get ss =
          let
            val charge_before = !charged
            val table = raw_get ss
            val generation = clasimpLib.lhs_view_table_generation table
            val stats = clasimpLib.lhs_view_table_stats table
            val expected = if HOLset.member (!generations,generation) then 0
                           else #normalization stats
            val _ = if !charged - charge_before = expected then ()
                    else raise Fail "cache derivation charge accounting"
            val _ = generations := HOLset.add (!generations,generation)
          in table end
        fun same_theorem (a,b) = aconv (concl a) (concl b) andalso
          HOLset.equal (hypset a,hypset b)
        fun same_view (NONE,NONE) = true
          | same_view (SOME a,SOME b) = same_theorem (a,b)
          | same_view _ = false
        fun same_entry (a : clasimpLib.lhs_view_entry,
                        b : clasimpLib.lhs_view_entry) =
          simpLib.same_rewrite_source (#origin a,#origin b) andalso
          #1 (#source a) = #1 (#source b) andalso
          same_theorem (#2 (#source a),#2 (#source b)) andalso
          same_view (#view a,#view b) andalso
          #rejection a = #rejection b andalso
          #normalization a = #normalization b andalso
          ListPair.allEq (fn (a,b) => aconv a b)
            (#footprint a,#footprint b) andalso
          ListPair.allEq
            (fn (a,b) => Lib.pair_compare
               (KernelSig.id_compare,Int.compare) (a,b) = EQUAL)
            (#abstraction_positions a,#abstraction_positions b)
        fun checked ss =
          let
            val table = get ss
            val entries = clasimpLib.lhs_view_table_entries table
            val fresh = clasimpLib.derive_lhs_view_entries (fn () => ()) ss
            val _ = if ListPair.allEq same_entry (entries,fresh) then ()
                    else raise Fail
                      "incremental table differs from fresh table"
          in table end
        fun source_entry table = valOf (List.find
          (fn entry => Option.getOpt
            (Option.map (String.isPrefix "cache_source" o #Name)
              (#1 (#source entry)),false))
          (clasimpLib.lhs_view_table_entries table))
        fun has_view table = Option.isSome (#view (source_entry table))
        fun stats table = clasimpLib.lhs_view_table_stats table
        val bare = named "cache_source" original simpLib.empty_ss
        val initial = checked bare
        val initial_rejected =
          #rejection (source_entry initial) =
            SOME clasimpLib.NoReducibleArguments
        val reducing = named "cache_reduce" reducer bare
        val reduced = checked reducing
        val active = has_view reduced andalso #derived (stats reduced) = 2
        val extended = named "cache_unrelated" unrelated reducing
        val unrelated_table = checked extended
        val unrelated_reused = #derived (stats unrelated_table) = 1 andalso
          #reused (stats unrelated_table) = 2
        val removed = checked
          (simpLib.remove_ssfrags ["cache_reduce"] extended)
        val removal = not (has_view removed) andalso
          #reused (stats removed) = 1
        val joined_ss = named "cache_bridge" bridge reducing
        val joined = checked joined_ss
        val joinable = #rejection (source_entry joined) =
          SOME clasimpLib.JoinableLHS
        val unjoined = checked
          (simpLib.remove_simps ["cache_bridge"] joined_ss)
        val rejected_removal = has_view unjoined
        val filtered = checked (simpLib.filter_rewrites
          (fn (_,th) => not (aconv (concl th) (concl reducer))) reducing)
        val filter_removed = not (has_view filtered)
        val guarded = named "cache_conditional" conditional
          (named "cache_permit" permits bare)
        val blocked_ss = named "cache_block" blocks guarded
        val blocked = checked blocked_ss
        val failed_condition = #rejection (source_entry blocked) =
          SOME clasimpLib.UnchangedLHS
        val unblocked = checked
          (simpLib.remove_simps ["cache_block"] blocked_ss)
        val condition_removal = has_view unblocked
        fun converter key = simpLib.conv_ss
          {name="cache_keyed",key=key,trace=100,
           conv=fn _ => fn _ => Conv.REWR_CONV (Drule.SPEC_ALL reducer)}
        val pattern = ``cache_g (x:bool)``
        val _ = ignore (get bare)
        val keyed_ss = simpLib.++ (bare,converter (SOME ([],pattern)))
        val keyed = checked keyed_ss
        val keyed_update = has_view keyed andalso not (#rebuild (stats keyed))
        val unkeyed = checked (simpLib.remove_simps ["cache_keyed"] keyed_ss)
        val keyed_removal = not (has_view unkeyed)
        val keyless = checked (simpLib.++ (bare,converter NONE))
        val keyless_rebuild = has_view keyless andalso #rebuild (stats keyless)
        val depth_ss = simpLib.set_cond_depth 2 reducing
        val conditional_depth = checked depth_ss
        val strategy_rebuild = #rebuild (stats conditional_depth)
        val gen_before = clasimpLib.lhs_view_table_generation conditional_depth
        val work_before = !charged
        val again = get depth_ss
        val memo_hit = gen_before = clasimpLib.lhs_view_table_generation again
          andalso !charged = work_before
        val evicted = clasimpLib.lhs_view_table_generation (get bare) <>
          clasimpLib.lhs_view_table_generation initial
        val wildcard = checked
          (simpLib.++ (bare,converter (SOME ([],``x:bool``))))
        val wildcard_rebuild = has_view wildcard andalso
          #rebuild (stats wildcard)
        val _ = ignore (get reducing)
        val unchanged = checked (simpLib.++ (reducing,simpLib.empty_ssfrag))
        val empty_reused = #derived (stats unchanged) = 0 andalso
          #reused (stats unchanged) = 2
        val op_def = new_definition
          ("cache_op_def", ``cache_op (x:bool) (y:bool) = T``)
        val comm = Tactical.prove
          (``!x y. cache_op x y = cache_op y x``,
           Rewrite.REWRITE_TAC [op_def])
        val assoc = Tactical.prove
          (``!x y z. cache_op (cache_op x y) z = cache_op x (cache_op y z)``,
           Rewrite.REWRITE_TAC [op_def])
        val ac_table = checked
          (simpLib.++ (reducing,simpLib.ac_ss [(comm,assoc)]))
        val ac_rebuilt = #rebuild (stats ac_table)
        val congruence = Tactical.prove
          (``!x y. (x = y) ==> (cache_g x = cache_g y)``,
           Rewrite.REWRITE_TAC [g])
        val congruence_table = checked
          (simpLib.++ (reducing,simpLib.SSFRAG
            {name=NONE,convs=[],rewrs=[],ac=[],filter=NONE,dprocs=[],
             congs=[congruence]}))
        val congruence_rebuilt = #rebuild (stats congruence_table)
        val app_def = new_definition
          ("cache_app_def", ``cache_app (f:bool -> bool) x = f x``)
        val consumes_abstraction = Tactical.prove
          (``!P x. cache_app (\v. P v) x = P x``,
           Tactical.EVERY
             [Rewrite.REWRITE_TAC [app_def],Tactic.BETA_TAC,
              Rewrite.REWRITE_TAC []])
        val abstraction_table = checked
          (named "cache_abstraction" consumes_abstraction reducing)
        val abstraction_rebuilt = #rebuild (stats abstraction_table)
        exception CacheCutoff
        val stop = ref true
        val recovered_charges = ref 0
        val recover = clasimpLib.make_lhs_view_cache
          (fn () => if !stop then raise CacheCutoff
                    else recovered_charges := !recovered_charges + 1)
        val cutoff = ((ignore (recover reducing); false)
                      handle CacheCutoff => true)
        val _ = stop := false
        val recovered = recover reducing
        val fresh = clasimpLib.derive_lhs_view_entries (fn () => ()) reducing
        val recovered_work = !recovered_charges
        val recovery = cutoff andalso
          ListPair.allEq same_entry
            (clasimpLib.lhs_view_table_entries recovered,fresh) andalso
          #derived (stats recovered) = 2 andalso recovered_work > 0
        val _ = ignore (recover reducing)
        val recovery_hit = !recovered_charges = recovered_work
        exception FixtureContext of thm list
        val unrelated_head = fst (strip_comb ``cache_u (x:bool)``)
        fun has_trigger th =
          aconv (fst (strip_comb (boolSyntax.lhs
            (#2 (boolSyntax.strip_forall (concl th)))))) unrelated_head
          handle HOL_ERR _ => false
        val decision = Traverse.CONTEXT_REDUCER
          {name=SOME "cache context",initial=FixtureContext [],
           addcontext=fn (FixtureContext old,added) =>
             FixtureContext (added @ old) | _ => raise Fail "fixture context",
           apply=fn {context,...} =>
             case context of
                 FixtureContext rules =>
                   (fn tm => if List.exists has_trigger rules then
                       Conv.REWR_CONV (Drule.SPEC_ALL reducer) tm
                     else raise Conv.UNCHANGED)
               | _ => raise Fail "fixture context"}
        val opaque_ss = named "cache_source" original
          (simpLib.++ (simpLib.empty_ss,simpLib.dproc_ss decision))
        val opaque_initial = checked opaque_ss
        val opaque_added = checked
          (named "cache_unrelated" unrelated opaque_ss)
        val opaque_rebuilt = not (has_view opaque_initial) andalso
          has_view opaque_added andalso #rebuild (stats opaque_added)
        fun source_named ss prefix = valOf (List.find
          (fn source => Option.getOpt
            (Option.map (String.isPrefix prefix o #Name)
              (#1 (simpLib.source_rewrite source)),false))
          (simpLib.rewrite_source_handles ss))
        val _ = ignore (checked reducing)
        val masked_reduce = checked (simpLib.suspend_rewrite_sources
          [source_named reducing "cache_reduce"] reducing)
        val suspended_reducer = not (has_view masked_reduce) andalso
          #derived (stats masked_reduce) = 1
        val _ = ignore (checked joined_ss)
        val masked_bridge = checked (simpLib.suspend_rewrite_sources
          [source_named joined_ss "cache_bridge"] joined_ss)
        val suspended_rejection = has_view masked_bridge
        val opaque_extended = named "cache_unrelated" unrelated opaque_ss
        val _ = ignore (checked opaque_extended)
        val opaque_masked = checked (simpLib.suspend_rewrite_sources
          [source_named opaque_extended "cache_unrelated"] opaque_extended)
        val suspended_context = not (has_view opaque_masked) andalso
          #rebuild (stats opaque_masked)
        val checks =
          [initial_rejected,active,unrelated_reused,removal,joinable,
           rejected_removal,filter_removed,failed_condition,condition_removal,
           keyed_update,keyed_removal,keyless_rebuild,strategy_rebuild,
           memo_hit,
           opaque_rebuilt,evicted,wildcard_rebuild,empty_reused,ac_rebuilt,
           congruence_rebuilt,abstraction_rebuilt,recovery,recovery_hit,
           suspended_reducer,suspended_rejection,suspended_context]
        val _ = print ("CACHE_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all I checks end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ = (tprint "incremental LHS view tables equal fresh derivations";
         if lhs_cache_fixture () then OK ()
         else die "LHS view cache invalidation or reuse is incomplete");

(* Supplied views share one binding and charge equally on cold/warm memos. *)
fun supplied_view_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = new_theory "suppliedViewFixture"
        val g = new_definition ("sup_g_def", ``sup_g (x:bool) = T``)
        val h = new_definition ("sup_h_def", ``sup_h (x:bool) = T``)
        val c = new_definition ("sup_c_def", ``sup_c (x:bool) = T``)
        val k = new_definition ("sup_k_def", ``sup_k (x:bool) = T``)
        fun proof tm = Tactical.prove
          (tm,Rewrite.REWRITE_TAC [g,h,c,k])
        val original = proof ``!x. sup_c (sup_g x) = sup_k x``
        val reducer = proof ``!x. sup_g x = sup_h x``
        val ambient = simpLib.++ (simpLib.empty_ss,simpLib.rewrites [reducer])
        val get = clasimpLib.make_lhs_view_cache (fn () => ())
        val table = get ambient
        val bare_table = get simpLib.empty_ss
        val bind = clasimpLib.prepare_supplied_rules
        val cache = clasimpLib.make_supplied_view_cache ()
        val rules = bind ambient [original]
        fun derive table rules = cache (fn () => ()) table rules
        val cold = derive table rules
        val warm = derive table (bind ambient [original])
        val entries = clasimpLib.supplied_view_entries
        val stats = clasimpLib.supplied_view_stats
        fun same_theorem (a,b) = aconv (concl a) (concl b) andalso
          HOLset.equal (hypset a,hypset b)
        fun same_view (NONE,NONE) = true
          | same_view (SOME a,SOME b) = same_theorem (a,b)
          | same_view _ = false
        fun same_entry (a : clasimpLib.lhs_view_entry,
                        b : clasimpLib.lhs_view_entry) =
          #1 (#source a) = #1 (#source b) andalso
          same_theorem (#2 (#source a),#2 (#source b)) andalso
          same_view (#view a,#view b) andalso
          #rejection a = #rejection b andalso
          #normalization a = #normalization b andalso
          ListPair.allEq (fn (a,b) => aconv a b)
            (#footprint a,#footprint b) andalso
          ListPair.allEq
            (fn (a,b) => Lib.pair_compare
              (KernelSig.id_compare,Int.compare) (a,b) = EQUAL)
            (#abstraction_positions a,#abstraction_positions b)
        fun same_entries a b = ListPair.allEq same_entry (entries a,entries b)
        val view = valOf (#view (hd (entries cold)))
        val view_tm = ``sup_c (sup_h x)``
        val original_tm = ``sup_c (sup_g x)``
        val result_tm = ``sup_k x``
        fun converted ss input expected =
          let val theorem = Conv.QCONV (simpLib.SIMP_CONV ss []) input
          in null (hyp theorem) andalso
             aconv (boolSyntax.lhs (concl theorem)) input andalso
             aconv (boolSyntax.rhs (concl theorem)) expected andalso
             valid_closes (Tactic.ACCEPT_TAC theorem)
               ([],boolSyntax.mk_eq (input,expected)) end
        val certified = null (hyp view) andalso
          aconv (concl view) ``!x. sup_c (sup_h x) = sup_k x`` andalso
          converted (clasimpLib.install_supplied_views cold simpLib.empty_ss)
            view_tm result_tm
        val memo_hit = same_entries cold warm andalso
          #derived (stats cold) = 1 andalso #memoized (stats cold) = 0 andalso
          #derived (stats warm) = 0 andalso #memoized (stats warm) = 1 andalso
          #normalization (stats cold) = #normalization (stats warm)
        val units = #normalization (stats cold)
        fun limited warm limit =
          let
            val memo = clasimpLib.make_supplied_view_cache ()
            val _ = if warm then ignore (memo (fn () => ()) table rules)
                    else ()
            val budget = searchBudget.create
              {candidates=NONE,applications=NONE,normalization=SOME limit}
            val completed =
              ((ignore (memo (#normalization (searchBudget.charger budget))
                              table rules); true)
               handle searchBudget.LimitReached
                 (searchBudget.Normalization,used) =>
                   if #normalization used = limit then false
                   else raise Fail "supplied cutoff usage")
            val used = searchBudget.usage budget
          in (completed,#normalization used,#candidates used,
              #applications used) end
        val cutoffs = units > 1 andalso List.all
          (fn limit => limited false limit = limited true limit andalso
             #1 (limited true limit) = (limit >= units))
          [0,1,units div 2,units-1,units,units+5]
        val interrupted = clasimpLib.make_supplied_view_cache ()
        val budget = searchBudget.create
          {candidates=NONE,applications=NONE,normalization=SOME (units-1)}
        val failed =
          ((ignore (interrupted
                      (#normalization (searchBudget.charger budget))
                                table rules); false)
           handle searchBudget.LimitReached
             (searchBudget.Normalization,_) => true)
        val recovered = interrupted (fn () => ()) table rules
        val recovery = failed andalso #derived (stats recovered) = 1 andalso
          #memoized (stats recovered) = 0 andalso same_entries cold recovered
        val isolated = derive bare_table
          (bind simpLib.empty_ss [original,reducer])
        val isolation = List.all
          (fn entry => not (Option.isSome (#view entry))) (entries isolated)
        val installed = simpLib.++
          (simpLib.empty_ss,simpLib.rewrites [original])
        val ambient_original = get installed
        val supplied_reducer = derive ambient_original (bind installed [reducer])
        val no_ambient_view = not (Option.isSome (#view
          (hd (clasimpLib.lhs_view_table_entries ambient_original)))) andalso
          null (List.mapPartial #view (entries supplied_reducer))
        val changed = get (simpLib.set_cond_depth 2 ambient)
        val regenerated = derive changed rules
        val generation = #derived (stats regenerated) = 1 andalso
          #memoized (stats regenerated) = 0 andalso
          same_entries cold regenerated
        val specialised = Drule.SPEC_ALL original
        val another = Drule.GEN_ALL (Thm.TRANS
          (Thm.REFL (boolSyntax.lhs (concl specialised))) specialised)
        val other_proof = derive table (bind ambient [another])
        val proof_identity = not (Portable.pointer_eq (original,another))
          andalso same_theorem (original,another) andalso
          #derived (stats other_proof) = 1 andalso
          #memoized (stats other_proof) = 0
        val once = BoundedRewrites.Once original
        fun bounded_views theorem = derive table (bind ambient [theorem])
        val eager = clasimpLib.install_supplied_views (bounded_views once)
          simpLib.empty_ss
        val shared_once = converted eager view_tm result_tm andalso
          converted eager original_tm original_tm
        val twice = clasimpLib.install_supplied_views
          (bounded_views (BoundedRewrites.Ntimes original 2)) simpLib.empty_ss
        val shared_twice = converted twice original_tm result_tm andalso
          converted twice view_tm result_tm andalso
          converted twice view_tm view_tm
        val first_rules = bind ambient [once]
        val first_ss = clasimpLib.install_supplied_rules first_rules
          simpLib.empty_ss
        val consumed = converted first_ss original_tm result_tm
        val late = derive table first_rules
        val late_ss = clasimpLib.add_supplied_views late first_ss
        val late_exhausted = consumed andalso
          converted late_ss view_tm view_tm andalso
          converted late_ss original_tm original_tm
        val available_rules = bind ambient [once]
        val available_ss = clasimpLib.install_supplied_rules available_rules
          simpLib.empty_ss
        val available_views = derive table available_rules
        val available_ss = clasimpLib.add_supplied_views available_views
          available_ss
        val late_available = converted available_ss view_tm result_tm andalso
          converted available_ss original_tm original_tm
        val duplicate = derive table (bind ambient [once,once])
        val duplicate_ss = clasimpLib.install_supplied_views duplicate
          simpLib.empty_ss
        val independent = length (entries duplicate) = 2 andalso
          not (simpLib.same_rewrite_source
            (#origin (hd (entries duplicate)),
             #origin (hd (tl (entries duplicate))))) andalso
          converted duplicate_ss view_tm result_tm andalso
          converted duplicate_ss original_tm result_tm andalso
          converted duplicate_ss view_tm view_tm
        val missing = simpLib.remove_ssfrags ["PREPARED_REWRITES"]
          (clasimpLib.install_supplied_rules rules simpLib.empty_ss)
        val removed = converted (clasimpLib.add_supplied_views cold missing)
          view_tm view_tm
        val unique_install =
          ((ignore (clasimpLib.install_supplied_rules first_rules first_ss);
            false) handle HOL_ERR _ => true)
        val controls =
          [markerLib.Excl "supplied",markerLib.ExclSF "supplied",
           markerLib.FRAG "supplied",markerLib.Cong original,
           simpLib.Split original,markerLib.AC reducer original,
           markerLib.mk_Req0 original,markerLib.mk_ReqD original,
           markerLib.NoAsms,markerLib.IgnAsm [QUOTE "supplied"],
           clasetLib.Simp original,clasetLib.Iff original,
           BoundedRewrites.Once (markerLib.Excl "supplied")]
        val marked = bind ambient (original::controls @ [once])
        val marker_views = derive table marked
        val markers = ListPair.allEq same_theorem
          (controls,clasimpLib.supplied_rule_controls marked) andalso
          ListPair.allEq same_theorem
            ([original,once],clasimpLib.supplied_rule_originals marked)
          andalso length (entries marker_views) = 2
        exception SuppliedContext of thm list
        val primed = ref ([] : thm list list)
        val decision = Traverse.CONTEXT_REDUCER
          {name=SOME "supplied fixture context",initial=SuppliedContext [],
           addcontext=fn (SuppliedContext old,added) =>
             (if null added then () else primed := added :: !primed;
              SuppliedContext (added @ old))
             | _ => raise Fail "supplied context",
           apply=fn _ => Conv.NO_CONV}
        val with_context = simpLib.++
          (simpLib.empty_ss,simpLib.dproc_ss decision)
        val prepared = bind with_context [once]
        val unprimed = null (!primed)
        val context_ss = clasimpLib.install_supplied_rules prepared with_context
        fun only_original () =
          case !primed of [[th]] => same_theorem (th,original) | _ => false
        val one_priming = unprimed andalso only_original ()
        val extended_context = simpLib.++
          (context_ss,simpLib.name_ss "supplied unrelated"
             (simpLib.rewrites [reducer]))
        val _ = primed := []
        val replayed = simpLib.filter_rewrites
          (fn (_,th) => not (aconv (concl th) (concl reducer)))
          extended_context
        val replay_priming = only_original ()
        val replay_th = Conv.QCONV (simpLib.SIMP_CONV replayed []) original_tm
        val replay_conversion = null (hyp replay_th) andalso
          aconv (boolSyntax.rhs (concl replay_th)) result_tm
        val context_replay = replay_priming andalso replay_conversion
        val _ = if context_replay then () else
          print ("SUPPLIED_CONTEXT " ^ Bool.toString replay_priming ^ " " ^
            Bool.toString replay_conversion ^ " " ^
            Parse.term_to_string (concl replay_th) ^ " " ^
            String.concatWith "; " (map (fn group =>
              String.concatWith ", " (map (fn th =>
                Parse.term_to_string (concl th) ^ "/" ^
                Int.toString (length (hyp th))) group)) (!primed)) ^ "\n")
        val app = new_definition
          ("sup_app_def", ``sup_app (f:bool -> bool) x = f x``)
        val eta_rule = Tactical.prove
          (``!x. sup_app (\v. sup_g v) x = sup_k x``,
           Tactical.EVERY [Rewrite.REWRITE_TAC [app,g,k],Tactic.BETA_TAC,
                           Rewrite.REWRITE_TAC []])
        val eta_consumer = Tactical.prove
          (``!P x. sup_app (\v. P v) x = P x``,
           Tactical.EVERY [Rewrite.REWRITE_TAC [app],Tactic.BETA_TAC,
                           Rewrite.REWRITE_TAC []])
        val eta_ss = simpLib.++ (ambient,boolSimps.ETA_ss)
        val eta_table = get eta_ss
        val contracted = derive eta_table (bind eta_ss [eta_rule])
        val retained_rules = bind eta_ss [eta_rule,eta_consumer]
        val retained = derive eta_table retained_rules
        val fresh_retained = clasimpLib.make_supplied_view_cache ()
          (fn () => ()) eta_table retained_rules
        fun view_lhs binding = boolSyntax.lhs
          (concl (Drule.SPEC_ALL (valOf (#view (hd (entries binding))))))
        val policy_key = aconv (view_lhs contracted) ``sup_app sup_g x``
          andalso aconv (view_lhs retained) ``sup_app (\v. sup_h v) x``
          andalso same_entries retained fresh_retained andalso
          #derived (stats retained) = 2 andalso #memoized (stats retained) = 0
        val _ = if policy_key then () else
          print ("SUPPLIED_POLICY " ^ Parse.term_to_string
            (view_lhs contracted) ^ " | " ^ Parse.term_to_string
            (view_lhs retained) ^ " | " ^
            Int.toString (#derived (stats retained)) ^ " " ^
            Int.toString (#memoized (stats retained)) ^ "\n")
        val siblings = bind ambient [once]
        val left = clasimpLib.install_supplied_rules siblings simpLib.empty_ss
        val right = clasimpLib.install_supplied_rules siblings simpLib.empty_ss
        val same_binding = converted left original_tm result_tm andalso
          converted right original_tm original_tm
        val compilations = ref 0
        val counted_ss = simpLib.++ (ambient,simpLib.SSFRAG
          {name=NONE,convs=[],rewrs=[],ac=[],dprocs=[],congs=[],
           filter=SOME (fn rule =>
             (compilations := !compilations + 1; [rule]))})
        val compiled_rules = bind counted_ss [once]
        val compilation_work = !compilations
        val compiled_ss = clasimpLib.install_supplied_rules compiled_rules
          counted_ss
        val compiled_once = compilation_work = 1 andalso
          !compilations = compilation_work andalso
          converted compiled_ss view_tm view_tm
        val bounded_memo = clasimpLib.make_supplied_view_cache ()
        fun bounded theorem = bounded_memo (fn () => ()) table
          (bind ambient [theorem])
        val _ = ignore (bounded original)
        val _ = List.app (fn _ => ignore (bounded (Drule.GEN_ALL (Thm.TRANS
          (Thm.REFL (boolSyntax.lhs (concl specialised))) specialised))))
          (List.tabulate (256,I))
        val after_eviction = bounded original
        val memo_eviction = #derived (stats after_eviction) = 1 andalso
          #memoized (stats after_eviction) = 0
        val checks =
          [certified,memo_hit,cutoffs,recovery,isolation,no_ambient_view,
           generation,proof_identity,shared_once,shared_twice,late_exhausted,
           late_available,independent,removed,unique_install,markers,
           one_priming,context_replay,policy_key,same_binding,memo_eviction,
           compiled_once]
        val _ = print ("SUPPLIED_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all I checks end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ = (tprint "supplied LHS views retain controls and memo budget usage";
         if supplied_view_fixture () then OK ()
         else die "supplied LHS binding or charge replay is incomplete");

(* A supplied converse uses one parallel ambient rewrite, then keeps its way. *)
fun supplied_converse_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = new_theory "suppliedConverseFixture"
        val l = new_definition ("cx_l_def", ``cx_l (x:bool) = T``)
        val r = new_definition ("cx_r_def", ``cx_r (x:bool) = T``)
        val s = new_definition ("cx_s_def", ``cx_s (x:bool) = T``)
        val t = new_definition ("cx_t_def", ``cx_t (x:bool) = T``)
        val box = new_definition ("cx_box_def", ``cx_box (x:bool) = T``)
        val dst = new_definition ("cx_dst_def", ``cx_dst (x:bool) = T``)
        val pair = new_definition
          ("cx_pair_def", ``cx_pair (x:bool) (y:bool) = T``)
        val p = new_definition ("cx_p_def", ``cx_p = T``)
        fun proof tm = Tactical.prove
          (tm,Rewrite.REWRITE_TAC [l,r,s,t,box,dst,pair,p])
        val forward = proof ``!x. cx_l x = cx_r x``
        val sibling = proof ``!x. cx_s x = cx_t x``
        val reverse = boolLib.GSYM forward
        val parallel = proof
          ``!x y. cx_pair (cx_r x) (cx_r y) = cx_pair (cx_l x) (cx_l y)``
        val conditional = proof ``!x. cx_p ==> (cx_l x = cx_r x)``
        val dependent = proof ``!x. cx_box (cx_l x) = cx_dst x``
        fun named name theorem ss = simpLib.++ (ss,simpLib.name_ss name
          (simpLib.rewrites_with_names
            [({Thy=current_theory (),Name=name},theorem)]))
        val ambient = named "cx_source" (CONJ forward sibling)
          pureSimps.pure_ss
        val get = clasimpLib.make_lhs_view_cache (fn () => ())
        val table = get ambient
        val memo = clasimpLib.make_supplied_view_cache ()
        val rules = clasimpLib.prepare_supplied_rules ambient [reverse]
        fun bind table rules = memo (fn () => ()) table rules
        val cold = bind table rules
        val warm = bind table
          (clasimpLib.prepare_supplied_rules ambient [reverse])
        val selected = clasimpLib.supplied_view_suspended
        val stats = clasimpLib.supplied_view_stats
        fun source_name source = Option.map #Name
          (#1 (simpLib.source_rewrite source))
        val detection = map source_name (selected cold) = [SOME "cx_source.1"]
        fun result binding ss input expected =
          let
            val budget = searchBudget.create
              {candidates=NONE,applications=NONE,normalization=SOME 2000}
            val working = clasimpLib.install_supplied_views binding ss
            val policy = clasimpLib.supplied_view_policy
              (#normalization (searchBudget.charger budget)) binding
            val theorem = Conv.QCONV
              (simpLib.SIMP_CONV_CHILD_FIRST policy working []) input
          in null (hyp theorem) andalso
             aconv (boolSyntax.rhs (concl theorem)) expected andalso
             valid_closes (Tactic.ACCEPT_TAC theorem)
               ([],boolSyntax.mk_eq (input,expected))
          end handle searchBudget.LimitReached _ => false
        val orientation = result cold ambient ``cx_r x`` ``cx_l x``
        val sibling_stays = result warm ambient ``cx_s x`` ``cx_t x``
        val no_arguments = bind table
          (clasimpLib.prepare_supplied_rules ambient [])
        val scoped = null (selected no_arguments) andalso
          result no_arguments ambient ``cx_l x`` ``cx_r x``
        val memo_hit = #derived (stats warm) = 0 andalso
          #memoized (stats warm) = 1 andalso
          #normalization (stats warm) = #normalization (stats cold) andalso
          ListPair.allEq simpLib.same_rewrite_source
            (selected cold,selected warm)
        val two_sites = bind table
          (clasimpLib.prepare_supplied_rules ambient [parallel])
        val parallel_sites = map source_name (selected two_sites) =
          [SOME "cx_source.1"] andalso result two_sites ambient
            ``cx_pair (cx_r x) (cx_r y)`` ``cx_pair (cx_l x) (cx_l y)``
        val guarded = named "cx_conditional" conditional pureSimps.pure_ss
        val guarded_binding = bind (get guarded)
          (clasimpLib.prepare_supplied_rules guarded [reverse])
        val conditional_stays = null (selected guarded_binding)
        val chain = named "cx_chain" (proof ``!x. cx_r x = cx_s x``)
          (named "cx_first" forward pureSimps.pure_ss)
        val closes_cycle = proof ``!x. cx_s x = cx_l x``
        val cycle = bind (get chain)
          (clasimpLib.prepare_supplied_rules chain [closes_cycle])
        val budget = searchBudget.create
          {candidates=NONE,applications=NONE,normalization=SOME 2000}
        val longer_cycle = null (selected cycle) andalso
          ((ignore (simpLib.SIMP_CONV_CHILD_FIRST
             (clasimpLib.supplied_view_policy
               (#normalization (searchBudget.charger budget)) cycle)
             (clasimpLib.install_supplied_views cycle chain) [] ``cx_s x``);
            false)
           handle searchBudget.LimitReached (searchBudget.Normalization,used) =>
             #normalization used = 2000)
        val excluded = simpLib.remove_simps ["cx_source.1"] ambient
        val excluded_binding = bind (get excluded)
          (clasimpLib.prepare_supplied_rules excluded [reverse])
        val exclusion = null (selected excluded_binding) andalso
          result excluded_binding excluded ``cx_r x`` ``cx_l x``
        val bare_dependent = bind table
          (clasimpLib.prepare_supplied_rules ambient [dependent])
        val mixed = bind table
          (clasimpLib.prepare_supplied_rules ambient [dependent,reverse])
        val restored = bind table
          (clasimpLib.prepare_supplied_rules ambient [dependent])
        fun first_view binding = #view
          (hd (clasimpLib.supplied_view_entries binding))
        val removal_policy = Option.isSome (first_view bare_dependent) andalso
          not (Option.isSome (first_view mixed)) andalso
          Option.isSome (first_view restored) andalso
          #memoized (stats restored) = 1
        val effective = simpLib.suspend_rewrite_sources (selected mixed) ambient
        val fresh = clasimpLib.make_supplied_view_cache () (fn () => ())
          (get effective) (clasimpLib.prepare_supplied_rules effective
            [dependent,reverse])
        fun same_entry (a : clasimpLib.lhs_view_entry,
                        b : clasimpLib.lhs_view_entry) =
          #rejection a = #rejection b andalso
          #normalization a = #normalization b andalso
          ListPair.allEq (fn (a,b) => aconv a b) (#footprint a,#footprint b)
          andalso (case (#view a,#view b) of
              (NONE,NONE) => true
            | (SOME a,SOME b) => aconv (concl a) (concl b) andalso
                HOLset.equal (hypset a,hypset b)
            | _ => false)
        val post_removal = ListPair.allEq same_entry
          (clasimpLib.supplied_view_entries mixed,
           clasimpLib.supplied_view_entries fresh)
        val units = #normalization (stats cold)
        fun limited warm limit =
          let
            val memo = clasimpLib.make_supplied_view_cache ()
            val _ = if warm then ignore (memo (fn () => ()) table rules) else ()
            val budget = searchBudget.create
              {candidates=NONE,applications=NONE,normalization=SOME limit}
            val success =
              ((ignore (memo (#normalization (searchBudget.charger budget))
                              table rules); true)
               handle searchBudget.LimitReached
                 (searchBudget.Normalization,used) =>
                   if #normalization used = limit then false
                   else raise Fail "converse cutoff usage")
          in (success,#normalization (searchBudget.usage budget)) end
        val budget_replay = units > 0 andalso List.all
          (fn limit => limited false limit = limited true limit andalso
             #1 (limited true limit) = (limit >= units))
          [0,units div 2,units-1,units,units+1]
        val _ = Datatype.Datatype `cx_one = CxOne`
        val wildcard = Tactical.prove
          (``!x:cx_one. x = CxOne``,Tactical.EVERY
            [Tactic.GEN_TAC,bossLib.Cases_on `x`,Rewrite.REWRITE_TAC []])
        val wildcard_ss = named "cx_wildcard" wildcard simpLib.empty_ss
        val wildcard_binding = bind (get wildcard_ss)
          (clasimpLib.prepare_supplied_rules wildcard_ss [boolLib.GSYM wildcard])
        val wildcard_index = map source_name (selected wildcard_binding) =
          [SOME "cx_wildcard.1"]
        (* Independent linear oracle: no head/footprint index or memo. *)
        fun linear ss rules =
          let
            val supplied = simpLib.rewrite_source_handles
              (clasimpLib.install_supplied_rules rules simpLib.empty_ss)
            fun is_converse ambient source =
              let
                val theorem = Drule.SPEC_ALL
                  (#2 (simpLib.source_rewrite ambient))
                val provided = Drule.SPEC_ALL
                  (#2 (simpLib.source_rewrite source))
                val (left,right) = boolSyntax.dest_eq
                  (#2 (boolSyntax.strip_imp_only (concl provided)))
                val result = Conv.QCONV
                  (Conv.ONCE_DEPTH_CONV (Conv.REWR_CONV theorem)) right
              in null (hyp theorem) andalso
                 boolSyntax.is_eq (concl theorem) andalso
                 aconv (boolSyntax.rhs (concl result)) left
              end handle HOL_ERR _ => false
          in List.filter
               (fn ambient => List.exists (is_converse ambient) supplied)
               (simpLib.rewrite_source_handles ss)
          end
        fun agrees (ss,arguments) =
          let
            val rules = clasimpLib.prepare_supplied_rules ss arguments
            val actual = selected (bind (get ss) rules)
          in ListPair.allEq simpLib.same_rewrite_source
               (actual,linear ss rules) end
        val linear_oracle = List.all agrees
          [(ambient,[reverse]),(ambient,[parallel]),(ambient,[]),
           (guarded,[reverse]),(chain,[closes_cycle]),(excluded,[reverse]),
           (ambient,[dependent,reverse]),
           (wildcard_ss,[boolLib.GSYM wildcard])]
        val error_cache = clasimpLib.make_supplied_view_cache ()
        val sticky_callback =
          ((ignore (error_cache
              (fn () => raise mk_HOL_ERR "converse fixture" "charge"
                "probe callback") table rules); false)
           handle HOL_ERR error =>
             Feedback.top_structure_of error = "converse fixture" andalso
             Feedback.top_function_of error = "charge" andalso
             Feedback.message_of error = "probe callback")
        val after_failure = error_cache (fn () => ()) table rules
        val transactional = #derived (stats after_failure) = 1 andalso
          #memoized (stats after_failure) = 0 andalso
          ListPair.allEq simpLib.same_rewrite_source
            (selected cold,selected after_failure)
        val zero = searchBudget.create
          {candidates=NONE,applications=NONE,normalization=SOME 0}
        val empty = memo (#normalization (searchBudget.charger zero)) table
          (clasimpLib.prepare_supplied_rules ambient
            [markerLib.Excl "cx_control",markerLib.NoAsms])
        val empty_cost = null (selected empty) andalso
          #normalization (searchBudget.usage zero) = 0 andalso
          clasimpLib.lhs_view_table_generation
            (clasimpLib.supplied_view_table empty) =
          clasimpLib.lhs_view_table_generation table
        val masked_generation = clasimpLib.lhs_view_table_generation
          (clasimpLib.supplied_view_table cold)
        val masked_memo = masked_generation <>
          clasimpLib.lhs_view_table_generation table andalso
          masked_generation = clasimpLib.lhs_view_table_generation
            (clasimpLib.supplied_view_table warm)
        val bounded_ss = named "cx_once" (BoundedRewrites.Ntimes forward 2)
          pureSimps.pure_ss
        val bounded_binding = bind (get bounded_ss)
          (clasimpLib.prepare_supplied_rules bounded_ss
            [BoundedRewrites.Once reverse])
        fun original_result expected =
          let val theorem = Conv.QCONV
                (simpLib.SIMP_CONV bounded_ss []) ``cx_l x``
          in aconv (boolSyntax.rhs (concl theorem)) expected end
        val quotas = not (null (selected bounded_binding)) andalso
          original_result ``cx_r x`` andalso original_result ``cx_r x``
          andalso original_result ``cx_l x`` andalso
          result bounded_binding bounded_ss ``cx_r x`` ``cx_l x`` andalso
          result bounded_binding bounded_ss ``cx_r x`` ``cx_r x``
        val conditional_reverse = proof
          ``!x. cx_p ==> (cx_r x = cx_l x)``
        val conditional_ss = simpLib.++ (ambient,simpLib.rewrites [p])
        val conditional_supplied = bind (get conditional_ss)
          (clasimpLib.prepare_supplied_rules conditional_ss
            [conditional_reverse])
        val conditional_priority = map source_name
          (selected conditional_supplied) = [SOME "cx_source.1"] andalso
          result conditional_supplied conditional_ss ``cx_r x`` ``cx_l x``
        val conditional_oracle = agrees
          (conditional_ss,[conditional_reverse])
        val nested_calls = ref 0
        fun nested_charge () =
          (nested_calls := !nested_calls + 1;
           if !nested_calls = 4 then
             raise mk_HOL_ERR "converse fixture" "nested charge" "probe"
           else ())
        val sticky_nested =
          ((ignore (clasimpLib.make_supplied_view_cache ()
              nested_charge table rules); false)
           handle HOL_ERR error =>
             Feedback.top_structure_of error = "converse fixture" andalso
             Feedback.top_function_of error = "nested charge" andalso
             Feedback.message_of error = "probe")
        val checks =
          [detection,orientation,sibling_stays,scoped,memo_hit,parallel_sites,
           conditional_stays,longer_cycle,exclusion,removal_policy,
           post_removal,budget_replay,wildcard_index,linear_oracle,
           sticky_callback,transactional,empty_cost,masked_memo,quotas,
           conditional_priority,sticky_nested,conditional_oracle]
        val _ = print ("CONVERSE_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all I checks end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ = (tprint "supplied converses retain orientation and memo budget usage";
         if supplied_converse_fixture () then OK ()
         else die "supplied converse lookup or binding is incomplete");

(* Default and explicit working states retain views and decision bases. *)
fun working_simpset_fixture () =
  let
    val saved = Context.snapshot ()
    val saved_state = clasimpLib.clasimp_working_simpset ()
    fun run () =
      let
        val _ = new_theory "workingSimpsetFixture"
        val g = new_definition ("work_g_def", ``work_g (x:bool) = T``)
        val h = new_definition ("work_h_def", ``work_h (x:bool) = T``)
        val c = new_definition ("work_c_def", ``work_c (x:bool) = T``)
        val k = new_definition ("work_k_def", ``work_k (x:bool) = T``)
        val u = new_definition ("work_u_def", ``work_u (x:bool) = T``)
        val v = new_definition ("work_v_def", ``work_v (x:bool) = T``)
        fun proof tm = Tactical.prove
          (tm,Rewrite.REWRITE_TAC [g,h,c,k,u,v])
        val original = proof ``!x. work_c (work_g x) = work_k x``
        val reducer = proof ``!x. work_g x = work_h x``
        val unrelated = proof ``!x. work_u x = work_v x``
        fun named name theorem ss = simpLib.++ (ss,simpLib.name_ss name
          (simpLib.rewrites_with_names
            [({Thy=current_theory (),Name=name},theorem)]))
        val ambient = named "work_source" original
          (named "work_reducer" reducer simpLib.empty_ss)
        val charged = ref 0
        val get = clasimpLib.make_working_simpset_cache
          (fn () => charged := !charged + 1)
        val full = clasimpLib.working_full_simpset
        val table = clasimpLib.working_view_table
        val decisions = clasimpLib.working_decision_base
        val plain = clasimpLib.working_plain_decision_base
        val state = get ambient
        val lazy_state = !charged = 0 andalso
          Portable.pointer_eq (state,get ambient) andalso
          Portable.pointer_eq (ambient,clasimpLib.working_original state)
        val raw_decisions = plain state
        val lazy_plain = !charged = 0 andalso
          not (#order raw_decisions orelse #linarith raw_decisions) andalso
          Portable.pointer_eq (#stripped raw_decisions,ambient)
        val first = table state
        val units = !charged
        val construction = units > 0 andalso
          units = #normalization (clasimpLib.lhs_view_table_stats first)
        val table_hit = clasimpLib.lhs_view_table_generation first =
          clasimpLib.lhs_view_table_generation (table (get ambient)) andalso
          !charged = units
        fun converted ss input expected =
          let val theorem = Conv.QCONV (simpLib.SIMP_CONV ss []) input
          in null (hyp theorem) andalso
             aconv (boolSyntax.rhs (concl theorem)) expected andalso
             valid_closes (Tactic.ACCEPT_TAC theorem)
               ([],boolSyntax.mk_eq (input,expected)) end
        val viewed = full state
        val installed = converted viewed ``work_c (work_h x)`` ``work_k x``
        val raw_unchanged = converted ambient
          ``work_c (work_h x)`` ``work_c (work_h x)``
        val one_fragment = length (List.filter
          (fn name => name = "CLASIMP_REWRITE_VIEWS")
          (simpLib.ssfrag_names_of viewed)) = 1
        val full_hit = Portable.pointer_eq (viewed,full (get ambient)) andalso
          !charged = units
        val decision = decisions state
        val decision_hit = Portable.pointer_eq
          (#stripped decision,#stripped (decisions (get ambient))) andalso
          !charged = units andalso
          converted (#stripped decision) ``work_c (work_h x)`` ``work_k x``
        val with_decisions = simpLib.++
          (simpLib.++ (ambient,orderLib.ORDER_ext_ss),
           linarithLib.LINARITH_ext_ss)
        val decision_state = get with_decisions
        val prior = !charged
        val original_decision = plain decision_state
        val stripping = #order original_decision andalso
          #linarith original_decision andalso !charged = prior andalso
          not (List.exists
            (fn name => name = "ORDER" orelse name = "LINARITH")
            (simpLib.ssfrag_names_of (#stripped original_decision)))
        val viewed_decision = decisions decision_state
        val retained = #order viewed_decision andalso
          #linarith viewed_decision andalso
          converted (#stripped viewed_decision)
            ``work_c (work_h x)`` ``work_k x`` andalso
          List.exists (fn name => name = "CLASIMP_REWRITE_VIEWS")
            (simpLib.ssfrag_names_of (#stripped viewed_decision))
        val decision_memo = Portable.pointer_eq
          (#stripped viewed_decision,#stripped (decisions decision_state))
        val excluded = get (simpLib.remove_simps ["work_source"] ambient)
        val source_exclusion = converted (full excluded)
          ``work_c (work_h x)`` ``work_c (work_h x)``
        val absent = get (simpLib.remove_simps ["work_reducer"] ambient)
        val reducer_exclusion = converted (full absent)
          ``work_c (work_h x)`` ``work_c (work_h x)``
        val extended = get (named "work_unrelated" unrelated ambient)
        val update = clasimpLib.lhs_view_table_stats (table extended)
        val _ = print ("WORKING_UPDATE " ^ Int.toString (#derived update) ^
          " " ^ Int.toString (#reused update) ^ " " ^
          Bool.toString (#rebuild update) ^ "\n")
        val incremental = #derived update = 1 andalso #reused update = 2
          andalso not (#rebuild update) andalso converted (full extended)
            ``work_c (work_h x)`` ``work_k x``
        val bounded = named "work_once" (BoundedRewrites.Once original)
          (named "work_reducer" reducer simpLib.empty_ss)
        val bounded_working = full (get bounded)
        val shared_quota = converted bounded_working
          ``work_c (work_h x)`` ``work_k x`` andalso
          converted bounded ``work_c (work_g x)`` ``work_c (work_h x)``
        val exhausted = named "work_twice" (BoundedRewrites.Ntimes original 2)
          (named "work_reducer" reducer simpLib.empty_ss)
        val used = converted exhausted ``work_c (work_g x)`` ``work_k x``
          andalso converted exhausted ``work_c (work_g x)`` ``work_k x``
        val exhausted_state = get exhausted
        val exhausted_view = List.exists
          (fn entry => Option.isSome (#view entry))
          (clasimpLib.lhs_view_table_entries (table exhausted_state))
        val exhausted_quota = used andalso exhausted_view andalso
          converted (full exhausted_state)
            ``work_c (work_h x)`` ``work_c (work_h x)``
        val decision_once = named "work_decision_once"
          (BoundedRewrites.Once original)
          (named "work_reducer" reducer simpLib.empty_ss)
        val once_state = get (simpLib.++
          (simpLib.++ (decision_once,orderLib.ORDER_ext_ss),
           linarithLib.LINARITH_ext_ss))
        val once_decision = #stripped (decisions once_state)
        val decision_quota = converted once_decision
          ``work_c (work_h x)`` ``work_k x`` andalso
          converted (#stripped (decisions once_state))
            ``work_c (work_h x)`` ``work_c (work_h x)``
        exception WorkingFailure
        val deny = ref true
        val retry_get = clasimpLib.make_working_simpset_cache
          (fn () => if !deny then raise WorkingFailure else ())
        val retry_state = retry_get ambient
        val failed = ((ignore (full retry_state); false)
                      handle WorkingFailure => true)
        val _ = deny := false
        val retry = failed andalso Portable.pointer_eq
          (retry_state,retry_get ambient) andalso
          converted (full retry_state) ``work_c (work_h x)`` ``work_k x``
        val held = get ambient
        val held_generation = clasimpLib.lhs_view_table_generation (table held)
        val _ = List.app
          (fn n => ignore (get (simpLib.set_cond_depth (n+1) ambient)))
          (List.tabulate (8,I))
        val returned = get ambient
        val bounded_cache = not (Portable.pointer_eq (held,returned)) andalso
          held_generation = clasimpLib.lhs_view_table_generation (table returned)
        val previous_raw = clasimpLib.clasimp_ss ()
        val before_state = clasimpLib.clasimp_working_simpset ()
        val before_identity = Portable.pointer_eq
          (before_state,clasimpLib.working_simpset_of previous_raw)
        val _ = BasicProvers.augment_srw_ss
          [simpLib.name_ss "work_default"
             (simpLib.rewrites_with_names
               [({Thy=current_theory (),Name="work_default_source"},original),
                ({Thy=current_theory (),Name="work_default_reducer"},
                 reducer)])]
        val default_raw = clasimpLib.clasimp_ss ()
        val default_state = clasimpLib.clasimp_working_simpset ()
        val default_identity = before_identity andalso
          not (Portable.pointer_eq (previous_raw,default_raw)) andalso
          not (Portable.pointer_eq (before_state,default_state)) andalso
          Portable.pointer_eq
            (default_state,clasimpLib.working_simpset_of default_raw)
        val default_views = converted (full default_state)
          ``work_c (work_h x)`` ``work_k x`` andalso
          converted default_raw ``work_c (work_h x)`` ``work_c (work_h x)``
        val _ = List.app (fn n => ignore (clasimpLib.working_simpset_of
          (simpLib.set_cond_depth (n+10) simpLib.empty_ss)))
          (List.tabulate (8,I))
        val default_owned = Portable.pointer_eq
          (default_state,clasimpLib.working_simpset_of default_raw) andalso
          Portable.pointer_eq
            (full default_state,full (clasimpLib.working_simpset_of default_raw))
        val default_generation = clasimpLib.lhs_view_table_generation
          (table default_state)
        (* The views do not depend on [arith] facts: a context with a
           probe fact answers its own simpset and working state, but its
           view table derives nothing and is no rebuild, and returning to
           the context without it answers the objects it had. *)
        val (arith_ctxt,plain_ctxt) = contexts_with_and_without_fact ()
        val plain_ss = clasimpLib.clasimp_ss_of plain_ctxt
        val plain_state = clasimpLib.clasimp_working_simpset_of plain_ctxt
        val _ = table plain_state
        val arith_state = clasimpLib.clasimp_working_simpset_of arith_ctxt
        val arith_stats = clasimpLib.lhs_view_table_stats (table arith_state)
        val arith_shares_views = #derived arith_stats = 0 andalso
          not (#rebuild arith_stats) andalso
          not (Portable.pointer_eq
                 (plain_ss,clasimpLib.clasimp_ss_of arith_ctxt))
        val arith_return =
          Portable.pointer_eq (plain_state,default_state) andalso
          Portable.pointer_eq
            (plain_ss,clasimpLib.clasimp_ss_of plain_ctxt) andalso
          Portable.pointer_eq
            (plain_state,clasimpLib.clasimp_working_simpset_of plain_ctxt)
        val _ = BasicProvers.diminish_srw_ss ["work_default"]
        val removed = clasimpLib.clasimp_working_simpset ()
        val stateful_removal = clasimpLib.lhs_view_table_generation
          (table removed) <> default_generation andalso
          converted (full removed)
            ``work_c (work_h x)`` ``work_c (work_h x)``
        fun same_theorem (a,b) = aconv (concl a) (concl b) andalso
          HOLset.equal (hypset a,hypset b)
        fun same_entry (a : clasimpLib.lhs_view_entry,
                        b : clasimpLib.lhs_view_entry) =
          simpLib.same_rewrite_source (#origin a,#origin b) andalso
          #1 (#source a) = #1 (#source b) andalso
          same_theorem (#2 (#source a),#2 (#source b)) andalso
          #rejection a = #rejection b andalso
          #normalization a = #normalization b andalso
          ListPair.allEq (fn (a,b) => aconv a b) (#footprint a,#footprint b)
          andalso ListPair.allEq
            (fn (a,b) => Lib.pair_compare
              (KernelSig.id_compare,Int.compare) (a,b) = EQUAL)
            (#abstraction_positions a,#abstraction_positions b) andalso
          (case (#view a,#view b) of
               (NONE,NONE) => true
             | (SOME a,SOME b) => same_theorem (a,b)
             | _ => false)
        fun oracle state = ListPair.allEq same_entry
          (clasimpLib.lhs_view_table_entries (table state),
           clasimpLib.derive_lhs_view_entries (fn () => ())
             (clasimpLib.working_original state))
        val exact_metadata = List.all oracle
          [state,decision_state,excluded,absent,extended,exhausted_state,
           once_state,retry_state,default_state,arith_state,
           removed]
        val default_restore =
          let val _ = Context.restore saved
          in Portable.pointer_eq
               (saved_state,clasimpLib.clasimp_working_simpset ()) end
        val default_compiles = ref 0
        val instrumented = simpLib.++
          (BasicProvers.srw_ss (),simpLib.SSFRAG
            {name=NONE,convs=[],rewrs=[],ac=[],dprocs=[],congs=[],
             filter=SOME (fn theorem =>
               (default_compiles := !default_compiles + 1; [theorem]))})
        val _ = BasicProvers.temp_setsimpset instrumented
        val _ = default_compiles := 0
        val explicit_independent = valid_closes
          (clasimpLib.asm_full_simp pureSimps.pure_ss []) ([],``T``)
          andalso !default_compiles = 0
        val checks =
          [lazy_state,lazy_plain,construction,table_hit,installed,raw_unchanged,
           one_fragment,full_hit,decision_hit,stripping,retained,
           source_exclusion,reducer_exclusion,incremental,shared_quota,
           exhausted_quota,retry,bounded_cache,default_identity,default_views,
           stateful_removal,default_restore,arith_shares_views,arith_return,
           default_owned,explicit_independent,
           decision_memo,decision_quota,exact_metadata]
        val _ = print ("WORKING_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all I checks end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ = (tprint "working simpsets cache views, decisions and native controls";
         if working_simpset_fixture () then OK ()
         else die "working simpset cache or stateful invalidation is incomplete");

(* Supplied abstraction consumers also govern the ambient view table. *)
fun binding_policy_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = new_theory "bindingPolicyFixture"
        val g = new_definition ("pol_g_def", ``pol_g (x:bool) = T``)
        val h = new_definition ("pol_h_def", ``pol_h (x:bool) = T``)
        val k = new_definition ("pol_k_def", ``pol_k (x:bool) = T``)
        val app = new_definition
          ("pol_app_def", ``pol_app (f:bool -> bool) x = f x``)
        fun proof tm = Tactical.prove
          (tm,Tactical.EVERY [Rewrite.REWRITE_TAC [app,g,h,k],
                             Tactic.BETA_TAC,Rewrite.REWRITE_TAC []])
        val source = proof ``!x. pol_app (\v. pol_g v) x = pol_k x``
        val reducer = proof ``!x. pol_g x = pol_h x``
        val consumer = proof ``!P x. pol_app (\v. P v) x = P x``
        val supplied_reducer = proof ``!x. pol_h x = pol_k x``
        fun named name theorem ss = simpLib.++ (ss,simpLib.name_ss name
          (simpLib.rewrites_with_names
            [({Thy=current_theory (),Name=name},theorem)]))
        val ambient = named "pol_source" source
          (named "pol_reducer" reducer
            (simpLib.++ (simpLib.empty_ss,boolSimps.ETA_ss)))
        val get = clasimpLib.make_lhs_view_cache (fn () => ())
        val base = get ambient
        val cache = clasimpLib.make_supplied_view_cache ()
        fun bind arguments = cache (fn () => ()) base
          (clasimpLib.prepare_supplied_rules ambient arguments)
        val cold = bind [consumer]
        val warm = bind [consumer]
        val both = bind [source,consumer]
        val isolated = bind [consumer,supplied_reducer]
        val bare = bind []
        val table = clasimpLib.supplied_view_table
        val generation = clasimpLib.lhs_view_table_generation
        val entries = clasimpLib.lhs_view_table_entries
        fun source_entry table = valOf (List.find
          (fn (entry : clasimpLib.lhs_view_entry) =>
            Option.getOpt (Option.map (String.isPrefix "pol_source." o #Name)
              (#1 (#source entry)),false)) (entries table))
        fun view_lhs entry = boolSyntax.lhs
          (concl (Drule.SPEC_ALL (valOf (#view entry))))
        val contracted = ``pol_app pol_g x``
        val retained = ``pol_app (\v. pol_h v) x``
        val base_shape = aconv (view_lhs (source_entry base)) contracted
        val ambient_policy = aconv
          (view_lhs (source_entry (table cold))) retained
        val supplied_policy = aconv
          (view_lhs (hd (clasimpLib.supplied_view_entries both))) retained
        fun converted binding input expected =
          let
            val associations = List.mapPartial
              (fn (entry : clasimpLib.lhs_view_entry) =>
                Option.map (fn th => (#origin entry,th)) (#view entry))
              (entries (table binding))
            val ss = simpLib.++ (ambient,simpLib.rewrite_views associations)
            val policy = clasimpLib.supplied_view_policy (fn () => ()) binding
            val theorem = Conv.QCONV
              (simpLib.SIMP_CONV_CHILD_FIRST policy ss []) input
          in null (hyp theorem) andalso
             aconv (boolSyntax.rhs (concl theorem)) expected andalso
             valid_closes (Tactic.ACCEPT_TAC theorem)
               ([],boolSyntax.mk_eq (input,expected)) end
        val certified = converted cold retained ``pol_k x``
        val hit = generation (table cold) = generation (table warm) andalso
          generation (table cold) <> generation base andalso
          #normalization (clasimpLib.supplied_view_stats cold) =
          #normalization (clasimpLib.supplied_view_stats warm)
        val scoped = generation (table bare) = generation base andalso
          #normalization (clasimpLib.supplied_view_stats bare) = 0 andalso
          aconv (view_lhs (source_entry (table bare))) contracted
        val isolation = aconv
          (view_lhs (source_entry (table isolated))) retained
        val unchanged = generation (get ambient) = generation base andalso
          aconv (view_lhs (source_entry base)) contracted
        (* Independent normalization certifies the expected ambient view. *)
        val policy = clasimpLib.supplied_view_policy (fn () => ()) cold
        val prepared = simpLib.prepare_child_first_observed (fn _ => ())
          policy ambient
        val raw = Drule.SPEC_ALL source
        val normal = #arguments prepared [] (boolSyntax.lhs (concl raw))
        val expected = Thm.TRANS (Thm.SYM normal) raw
        val actual = Drule.SPEC_ALL (valOf (#view (source_entry (table cold))))
        val oracle = aconv (concl expected) (concl actual) andalso
          HOLset.equal (hypset expected,hypset actual)
        fun same_theorem (a,b) = aconv (concl a) (concl b) andalso
          HOLset.equal (hypset a,hypset b)
        fun same_view (NONE,NONE) = true
          | same_view (SOME a,SOME b) = same_theorem (a,b)
          | same_view _ = false
        fun same_entry (a : clasimpLib.lhs_view_entry,
                        b : clasimpLib.lhs_view_entry) =
          simpLib.same_rewrite_source (#origin a,#origin b) andalso
          #1 (#source a) = #1 (#source b) andalso
          same_theorem (#2 (#source a),#2 (#source b)) andalso
          same_view (#view a,#view b) andalso
          #rejection a = #rejection b andalso
          #normalization a = #normalization b andalso
          ListPair.allEq (fn (a,b) => aconv a b)
            (#footprint a,#footprint b) andalso
          ListPair.allEq
            (fn (a,b) => Lib.pair_compare
              (KernelSig.id_compare,Int.compare) (a,b) = EQUAL)
            (#abstraction_positions a,#abstraction_positions b)
        val {Name=app_id,...} = Term.dest_thy_constid
          (fst (strip_comb retained))
        val positions = [(app_id,1)]
        fun exact ss positions binding = ListPair.allEq same_entry
          (entries (table binding),
           clasimpLib.derive_lhs_view_entries_with_positions
             (fn () => ()) ss positions)
        val exact_metadata = List.all (exact ambient positions)
          [cold,warm,both,isolated] andalso exact ambient [] bare
        val shared_table = generation (table cold) = generation (table both)
          andalso generation (table cold) = generation (table isolated)
        (* Equal input policies can differ after the keeper is suspended. *)
        val reverse = boolLib.GSYM consumer
        val keeper_ss = named "pol_keeper" consumer ambient
        val keeper_table = get keeper_ss
        fun keeper arguments = cache (fn () => ()) keeper_table
          (clasimpLib.prepare_supplied_rules keeper_ss arguments)
        val removed = keeper [reverse]
        val restored = keeper [reverse,consumer]
        val removed_again = keeper [reverse]
        val restored_again = keeper [reverse,consumer]
        fun keeper_selected binding =
          case clasimpLib.supplied_view_suspended binding of
              [origin] => Option.map #Name
                (#1 (simpLib.source_rewrite origin)) = SOME "pol_keeper.1"
            | _ => false
        val post_mask_policy = keeper_selected removed andalso
          keeper_selected restored andalso
          aconv (view_lhs (source_entry (table removed))) contracted andalso
          aconv (view_lhs (source_entry (table restored))) retained andalso
          generation (table removed) <> generation (table restored)
        val post_mask_hit =
          generation (table removed) = generation (table removed_again)
          andalso generation (table restored) =
                  generation (table restored_again)
        fun masked_exact binding positions = exact
          (simpLib.suspend_rewrite_sources
            (clasimpLib.supplied_view_suspended binding) keeper_ss)
          positions binding
        val masked_metadata = masked_exact removed [] andalso
          masked_exact restored positions
        val checks = [base_shape,ambient_policy,supplied_policy,certified,
                      hit,scoped,isolation,unchanged,oracle,exact_metadata,
                      shared_table,post_mask_policy,post_mask_hit,
                      masked_metadata]
        val _ = print ("BINDING_POLICY_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all I checks end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ = (tprint "ambient and supplied views share abstraction policy";
         if binding_policy_fixture () then OK ()
         else die "ambient and supplied view policies disagree");

(* Bound working states retain the adjusted table and consumed controls. *)
fun bound_working_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = new_theory "boundWorkingFixture"
        val g = new_definition ("bw_g_def", ``bw_g (x:bool) = T``)
        val h = new_definition ("bw_h_def", ``bw_h (x:bool) = T``)
        val k = new_definition ("bw_k_def", ``bw_k (x:bool) = T``)
        val app = new_definition
          ("bw_app_def", ``bw_app (f:bool -> bool) x = f x``)
        fun proof tm = Tactical.prove
          (tm,Tactical.EVERY [Rewrite.REWRITE_TAC [app,g,h,k],
                             Tactic.BETA_TAC,Rewrite.REWRITE_TAC []])
        val source = proof ``!x. bw_app (\v. bw_g v) x = bw_k x``
        val reducer = proof ``!x. bw_g x = bw_h x``
        val consumer = proof ``!P x. bw_app (\v. P v) x = P x``
        fun named name theorem ss = simpLib.++ (ss,simpLib.name_ss name
          (simpLib.rewrites_with_names
            [({Thy=current_theory (),Name=name},theorem)]))
        val reducing = named "bw_reducer" reducer
          (simpLib.++ (simpLib.empty_ss,boolSimps.ETA_ss))
        val ambient = named "bw_source" source reducing
        val get = clasimpLib.make_working_simpset_cache (fn () => ())
        val initial = get ambient
        val full = clasimpLib.working_full_simpset
        val decisions = clasimpLib.working_decision_base
        val table = clasimpLib.working_view_table
        val generation = clasimpLib.lhs_view_table_generation
        val old_full = full initial
        val cache = clasimpLib.make_supplied_view_cache ()
        fun bind state arguments = cache (fn () => ()) (table state)
          (clasimpLib.prepare_supplied_rules
            (clasimpLib.working_original state) arguments)
        val binding = bind initial [consumer]
        val state = clasimpLib.working_simpset_for binding
        val warm = clasimpLib.working_simpset_for (bind initial [consumer])
        val bare = clasimpLib.working_simpset_for (bind initial [])
        val contracted = ``bw_app bw_g x``
        val retained = ``bw_app (\v. bw_h v) x``
        val result = ``bw_k x``
        fun converted binding ss input expected =
          let
            val theorem = Conv.QCONV (simpLib.SIMP_CONV_CHILD_FIRST
              (clasimpLib.supplied_view_policy (fn () => ()) binding) ss [])
              input
          in null (hyp theorem) andalso
             aconv (boolSyntax.rhs (concl theorem)) expected andalso
             valid_closes (Tactic.ACCEPT_TAC theorem)
               ([],boolSyntax.mk_eq (input,expected)) end
        fun has_lhs ss wanted = List.exists
          (fn (_,theorem) => aconv wanted (boolSyntax.lhs
            (concl (Drule.SPEC_ALL theorem))) handle HOL_ERR _ => false)
          (#1 (simpLib.rewrite_sources ss []))
        val exact_table = generation (table state) = generation
          (clasimpLib.supplied_view_table binding)
        val installed = converted binding (full state) retained result
        val no_old_view = has_lhs old_full contracted andalso
          not (has_lhs (full state) contracted) andalso
          has_lhs (full state) retained
        val one_fragment = length (List.filter
          (fn name => name = "CLASIMP_REWRITE_VIEWS")
          (simpLib.ssfrag_names_of (full state))) = 1
        val full_hit = Portable.pointer_eq (full state,full warm)
        val decision_hit = Portable.pointer_eq
          (#stripped (decisions state),#stripped (decisions warm))
        val unchanged = Portable.pointer_eq (old_full,full initial) andalso
          has_lhs old_full contracted andalso
          not (has_lhs old_full retained)
        val no_arguments = generation (table bare) = generation (table initial)
          andalso Portable.pointer_eq (full bare,old_full)
        val with_dp = simpLib.++
          (simpLib.++ (ambient,orderLib.ORDER_ext_ss),
           linarithLib.LINARITH_ext_ss)
        val dp_binding = bind (get with_dp) [consumer]
        val dp_state = clasimpLib.working_simpset_for dp_binding
        val dp = decisions dp_state
        val dp_warm = clasimpLib.working_simpset_for
          (bind (get with_dp) [consumer])
        val dp_hit = Portable.pointer_eq
          (#stripped dp,#stripped (decisions dp_warm))
        val stripped = #order dp andalso #linarith dp andalso
          not (List.exists (fn name => name = "ORDER" orelse name = "LINARITH")
            (simpLib.ssfrag_names_of (#stripped dp))) andalso
          converted dp_binding (#stripped dp) retained result
        (* An earlier plain pass must not regain a consumed ambient rule. *)
        val once_ss = named "bw_once" (BoundedRewrites.Once source) reducing
        val once_dp = simpLib.++
          (simpLib.++ (once_ss,orderLib.ORDER_ext_ss),
           linarithLib.LINARITH_ext_ss)
        val first = Conv.QCONV (simpLib.SIMP_CONV once_dp [])
          ``bw_app (\v. bw_g v) x``
        val consumed = aconv (boolSyntax.rhs (concl first)) result
        val once_binding = bind (get once_dp) [consumer]
        val once_state = clasimpLib.working_simpset_for once_binding
        val no_revival = consumed andalso converted once_binding
          (#stripped (decisions once_state)) retained retained
        val twice_ss = named "bw_twice" (BoundedRewrites.Ntimes source 2)
          reducing
        val twice_dp = simpLib.++
          (simpLib.++ (twice_ss,orderLib.ORDER_ext_ss),
           linarithLib.LINARITH_ext_ss)
        val twice_binding = bind (get twice_dp) [consumer]
        val twice_state = clasimpLib.working_simpset_for twice_binding
        val shared = converted twice_binding (full twice_state) retained result
          andalso converted twice_binding (#stripped (decisions twice_state))
            retained result andalso
          converted twice_binding (full twice_state) retained retained
        val reverse = boolLib.GSYM consumer
        val keeper_ss = named "bw_keeper" consumer with_dp
        val keeper = bind (get keeper_ss) [reverse,consumer]
        val keeper_state = clasimpLib.working_simpset_for keeper
        val masked = length (clasimpLib.supplied_view_suspended keeper) = 1
          andalso has_lhs (full keeper_state) retained andalso
          not (List.exists
            (fn source => Option.map #Name (#1 (simpLib.source_rewrite source))
              = SOME "bw_keeper.1")
            (simpLib.rewrite_source_handles
              (#stripped (decisions keeper_state))))
        val empty_binding = bind (get simpLib.empty_ss) []
        val empty = clasimpLib.working_simpset_for empty_binding
        val no_fragment = Portable.pointer_eq (full empty,simpLib.empty_ss)
        val checks = [exact_table,installed,no_old_view,one_fragment,full_hit,
                      decision_hit,unchanged,no_arguments,stripped,no_revival,
                      shared,masked,no_fragment,dp_hit]
        val _ = print ("BOUND_WORKING_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all I checks end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ = (tprint "bound working states retain policy, decisions and controls";
         if bound_working_fixture () then OK ()
         else die "bound working state loses policy or revives controls");

(* An initial binding detects converses without constructing ambient views. *)
fun early_binding_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = new_theory "earlyBindingFixture"
        val l = new_definition ("early_l_def", ``early_l (x:bool) = T``)
        val r = new_definition ("early_r_def", ``early_r (x:bool) = T``)
        val box = new_definition ("early_box_def", ``early_box (x:bool) = T``)
        val dst = new_definition ("early_dst_def", ``early_dst (x:bool) = T``)
        val app = new_definition
          ("early_app_def", ``early_app (f:bool -> bool) x = f x``)
        fun proof tm = Tactical.prove
          (tm,Tactical.EVERY [Rewrite.REWRITE_TAC [app,l,r,box,dst],
                             Tactic.BETA_TAC,Rewrite.REWRITE_TAC []])
        val forward = proof ``!x. early_l x = early_r x``
        val reverse = BoundedRewrites.Once (boolLib.GSYM forward)
        val dependent = proof ``!x. early_box (early_l x) = early_dst x``
        val consumer = proof ``!P x. early_app (\v. P v) x = P x``
        val argument = ``early_app (\v. early_l v)``
        val drop = simpLib.++ (simpLib.empty_ss,simpLib.SSFRAG
          {name=NONE,convs=[],rewrs=[],ac=[],dprocs=[],congs=[],
           filter=SOME (K [])})
        val dropped_rules = clasimpLib.prepare_supplied_rules drop [consumer]
        val compiled_policy = not (#keep_abstraction
          (clasimpLib.supplied_rule_policy (fn () => ()) drop dropped_rules)
          argument)
        exception EarlyContext of thm list
        val queries = ref 0
        val primed = ref ([] : thm list)
        val decision = Traverse.CONTEXT_REDUCER
          {name=SOME "early opaque",initial=EarlyContext [],
           addcontext=fn (EarlyContext old,added) =>
             (primed := added @ !primed; EarlyContext (added @ old))
             | _ => raise Fail "early context",
           apply=fn _ => fn tm =>
             (queries := !queries + 1; Conv.NO_CONV tm)}
        fun named name theorem ss = simpLib.++ (ss,simpLib.name_ss name
          (simpLib.rewrites_with_names
            [({Thy=current_theory (),Name=name},theorem)]))
        val base = named "early_forward" forward
          (named "early_dependent" dependent
            (simpLib.++ (pureSimps.pure_ss,simpLib.dproc_ss decision)))
        val compiles = ref 0
        val ambient = simpLib.++ (base,simpLib.SSFRAG
          {name=NONE,convs=[],rewrs=[],ac=[],dprocs=[],congs=[],
           filter=SOME (fn theorem =>
             (compiles := !compiles + 1; [theorem]))})
        val _ = queries := 0
        val _ = primed := []
        val rules = clasimpLib.prepare_supplied_rules ambient [reverse,consumer]
        val charges = ref 0
        val cache = clasimpLib.make_supplied_converse_cache ()
        val early = cache (fn () => charges := !charges + 1) ambient rules
        val stats = clasimpLib.supplied_converse_stats
        val n = !charges
        val no_queries = !queries = 0
        val selected = clasimpLib.supplied_converse_suspended early
        val detection = case selected of
            [source] => Option.map #Name (#1 (simpLib.source_rewrite source))
              = SOME "early_forward.1"
          | _ => false
        val owner = n > 0 andalso #normalization (stats early) = n
        val working = clasimpLib.supplied_converse_working early
        val raw_only = length (simpLib.rewrite_source_handles working) + 1 =
          length (simpLib.rewrite_source_handles ambient) andalso
          not (List.exists (fn name => name = "CLASIMP_REWRITE_VIEWS")
            (simpLib.ssfrag_names_of working))
        val compile_once = !compiles = 2
        val retained = #keep_abstraction
          (clasimpLib.supplied_converse_policy early) argument
        fun same_reverse theorem = aconv
          (concl (Drule.SPEC_ALL theorem))
          (concl (Drule.SPEC_ALL (boolLib.GSYM forward)))
          handle HOL_ERR _ => false
        val no_priming = not (List.exists same_reverse (!primed))
        val installed = clasimpLib.install_supplied_rules
          (clasimpLib.supplied_converse_rules early) working
        fun converted ss input expected =
          let val theorem = Conv.QCONV (simpLib.SIMP_CONV_CHILD_FIRST
            (clasimpLib.supplied_converse_policy early) ss []) input
          in null (hyp theorem) andalso
             aconv (boolSyntax.rhs (concl theorem)) expected andalso
             valid_closes (Tactic.ACCEPT_TAC theorem)
               ([],boolSyntax.mk_eq (input,expected)) end
        val oriented = converted installed ``early_r x`` ``early_l x``
        val once = converted installed ``early_r x`` ``early_r x``
        val prefix = !charges
        val table = clasimpLib.make_lhs_view_cache (fn () => ()) ambient
        val after = clasimpLib.make_supplied_view_cache_after ()
        val late = after table early
        val late_work = !charges > prefix andalso
          #normalization (clasimpLib.supplied_view_stats late) =
          n + !charges-prefix
        val late_policy = #keep_abstraction
          (clasimpLib.supplied_view_policy (fn () => ()) late) argument
        val warm_charges = ref 0
        val warm = cache (fn () => warm_charges := !warm_charges + 1) ambient
          (clasimpLib.prepare_supplied_rules ambient [reverse,consumer])
        val warm_hit = !warm_charges = n andalso
          #normalization (stats warm) = n andalso
          #derived (stats warm) = 0 andalso #memoized (stats warm) = 2
        val _ = queries := 0
        val empty = clasimpLib.make_supplied_converse_cache () (fn () => ())
          ambient (clasimpLib.prepare_supplied_rules ambient [])
        val empty_work = !queries = 0 andalso
          #normalization (stats empty) = 0 andalso
          Portable.pointer_eq
            (ambient,clasimpLib.supplied_converse_working empty)
        val _ = queries := 0
        val cutoff = ((ignore (clasimpLib.make_supplied_converse_cache ()
          (fn () => raise mk_HOL_ERR "early" "charge" "stopped")
          ambient rules); false)
          handle HOL_ERR error => Feedback.message_of error = "stopped")
        val no_cutoff_queries = cutoff andalso !queries = 0
        fun same_entry (a : clasimpLib.lhs_view_entry,
                        b : clasimpLib.lhs_view_entry) =
          simpLib.same_rewrite_source (#origin a,#origin b) andalso
          #rejection a = #rejection b andalso
          #normalization a = #normalization b andalso
          ListPair.allEq (fn (a,b) => aconv a b) (#footprint a,#footprint b)
          andalso ListPair.allEq
            (fn (a,b) => Lib.pair_compare
              (KernelSig.id_compare,Int.compare) (a,b) = EQUAL)
            (#abstraction_positions a,#abstraction_positions b)
          andalso (case (#view a,#view b) of
              (NONE,NONE) => true
            | (SOME a,SOME b) => aconv (concl a) (concl b) andalso
                HOLset.equal (hypset a,hypset b)
            | _ => false)
        val entries = clasimpLib.supplied_view_entries
        val direct = clasimpLib.make_supplied_view_cache () (fn () => ())
          table rules
        val total = #normalization (clasimpLib.supplied_view_stats late)
        val oracle = ListPair.allEq same_entry (entries late,entries direct)
          andalso #normalization (clasimpLib.supplied_view_stats direct) = total
          andalso ListPair.allEq simpLib.same_rewrite_source
            (clasimpLib.supplied_view_suspended late,
             clasimpLib.supplied_view_suspended direct)
        val warm_late = after table warm
        val late_hit = !warm_charges = total andalso
          #normalization (clasimpLib.supplied_view_stats warm_late) = total
          andalso #derived (clasimpLib.supplied_view_stats warm_late) = 0
          andalso #memoized (clasimpLib.supplied_view_stats warm_late) = 2
        val masked_table = clasimpLib.make_lhs_view_cache (fn () => ()) working
        val masked_late = clasimpLib.make_supplied_view_cache_after ()
          masked_table early
        val masked_bridge = ListPair.allEq same_entry
          (entries late,entries masked_late) andalso
          Portable.pointer_eq
            (working,clasimpLib.working_original
              (clasimpLib.working_simpset_for masked_late))
        val wrong_basis =
          ((ignore (after (clasimpLib.make_lhs_view_cache (fn () => ())
                            pureSimps.pure_ss) early); false)
           handle HOL_ERR error => Feedback.message_of error =
             "ambient table belongs to another binding")
        fun limited warm limit =
          let
            val detect = clasimpLib.make_supplied_converse_cache ()
            val complete = clasimpLib.make_supplied_view_cache_after ()
            val _ = if warm then ignore
              (complete table (detect (fn () => ()) ambient rules)) else ()
            val budget = searchBudget.create
              {candidates=NONE,applications=NONE,normalization=SOME limit}
            val charge = #normalization (searchBudget.charger budget)
          in
            ((ignore (complete table (detect charge ambient rules));
              SOME (#normalization (searchBudget.usage budget)))
             handle searchBudget.LimitReached
               (searchBudget.Normalization,used) =>
                 if #normalization used = limit then NONE
                 else raise Fail "early binding cutoff usage")
          end
        val cutoffs = total > n andalso List.all
          (fn limit => limited false limit = limited true limit andalso
            limited false limit = (if limit < total then NONE else SOME total))
          [0,1,n div 2,n-1,n,n+1,total-1,total,total+5]
        fun charger limit = #normalization (searchBudget.charger
          (searchBudget.create
            {candidates=NONE,applications=NONE,normalization=SOME limit}))
        val interrupted = clasimpLib.make_supplied_converse_cache ()
        val stopped =
          ((ignore (interrupted (charger (n-1)) ambient rules); false)
           handle searchBudget.LimitReached
             (searchBudget.Normalization,used) => #normalization used = n-1)
        val recovered = interrupted (charger n) ambient rules
        val raw_recovery = stopped andalso
          #normalization (stats recovered) = n andalso
          #derived (stats recovered) = 1 andalso
          #memoized (stats recovered) = 1
        val complete = clasimpLib.make_supplied_view_cache_after ()
        val detect = clasimpLib.make_supplied_converse_cache ()
        val late_stopped =
          ((ignore (complete table
            (detect (charger (total-1)) ambient rules)); false)
           handle searchBudget.LimitReached
             (searchBudget.Normalization,used) =>
               #normalization used = total-1)
        val retry = complete table (detect (charger total) ambient rules)
        val late_recovery = late_stopped andalso
          #normalization (clasimpLib.supplied_view_stats retry) = total
          andalso #derived (clasimpLib.supplied_view_stats retry) = 1
          andalso #memoized (clasimpLib.supplied_view_stats retry) = 1
          andalso ListPair.allEq same_entry (entries late,entries retry)
        val checks = [compiled_policy,no_queries,detection,owner,raw_only,
                      compile_once,retained,no_priming,oriented,once,late_work,
                      late_policy,warm_hit,empty_work,no_cutoff_queries,
                      oracle,late_hit,masked_bridge,wrong_basis,cutoffs,
                      raw_recovery,late_recovery]
        val _ = print ("EARLY_BINDING_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all I checks end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ = (tprint "early supplied binding avoids ambient view construction";
         if early_binding_fixture () then OK ()
         else die "early binding forces views or loses compiled policy");

(* Initial and nested consumers keep one installed bundle when views arrive. *)
fun invocation_state_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = new_theory "invocationStateFixture"
        val g = new_definition ("iv_g_def", ``iv_g (x:bool) = T``)
        val h = new_definition ("iv_h_def", ``iv_h (x:bool) = T``)
        val c = new_definition ("iv_c_def", ``iv_c (x:bool) = T``)
        val d = new_definition ("iv_d_def", ``iv_d (x:bool) = T``)
        val k = new_definition ("iv_k_def", ``iv_k (x:bool) = T``)
        val a = new_definition ("iv_a_def", ``iv_a (x:bool) = T``)
        val b = new_definition ("iv_b_def", ``iv_b (x:bool) = T``)
        val definitions = [g,h,c,d,k,a,b]
        fun proof tm = Tactical.prove (tm,Rewrite.REWRITE_TAC definitions)
        val source = proof ``!x. iv_c (iv_g x) = iv_k x``
        val ambient_source = proof ``!x. iv_d (iv_g x) = iv_k x``
        val reducer = proof ``!x. iv_g x = iv_h x``
        val sibling = proof ``!x. iv_a x = iv_b x``
        val ambient = simpLib.++ (pureSimps.pure_ss,simpLib.name_ss
          "invocation ambient" (simpLib.rewrites
            [boolTheory.REFL_CLAUSE,reducer,ambient_source]))
        val get = clasimpLib.make_lhs_view_cache (fn () => ())
        val detect = clasimpLib.make_supplied_converse_cache ()
        val tables = ref 0
        val runtimes = ref 0
        val charges = ref 0
        fun charge () = charges := !charges + 1
        fun early arguments = detect charge ambient
          (clasimpLib.prepare_supplied_rules ambient arguments)
        fun runtime ss = (runtimes := !runtimes + 1; ss)
        fun provide () = (tables := !tables + 1; get ambient)
        val once_source = BoundedRewrites.Once source
        val state = clasimpLib.make_bound_simplification runtime provide
          (early [once_source])
        val ss = clasimpLib.bound_simplification_simpset
        val lazy = !tables = 0 andalso !runtimes = 1
        val raw = ss false state
        val target = ``iv_c (iv_h x) = iv_k x``
        val ambient_target = ``iv_d (iv_h x) = iv_k x``
        fun checked tactic goal =
          let
            val (goals,validation) = Tactical.VALID tactic goal
            val proofs = map (fn residual => Tactical.prove_goal
              (residual,Rewrite.REWRITE_TAC definitions)) goals
            val theorem = validation proofs
            val _ = if aconv (concl theorem) (#2 goal) then ()
                    else raise Fail "invocation state validation"
          in goals end
        val raw_pass = not (null (checked
          (clasimpLib.asm_full_simp_bound false state []) ([],target)))
        val prefix = !charges
        val viewed = ss true state
        val derived = !tables = 1 andalso !runtimes = 1 andalso
          !charges > prefix andalso
          List.exists (fn name => name = "CLASIMP_REWRITE_VIEWS")
            (simpLib.ssfrag_names_of viewed)
        val supplied = null (checked
          (clasimpLib.asm_full_simp_bound true state []) ([],target))
        val ambient_view = null (checked
          (clasimpLib.safe_asm_full_simp_bound true state [])
          ([],ambient_target))
        val exhausted = not (null (checked
          (clasimpLib.cascade_safe_simp_bound true state []) ([],target)))
        val prefix = !charges
        val cached = Portable.pointer_eq (viewed,ss true state) andalso
          !tables = 1 andalso !charges = prefix
        val raw_stays = Portable.pointer_eq (raw,ss false state) andalso
          not (List.exists (fn name => name = "CLASIMP_REWRITE_VIEWS")
            (simpLib.ssfrag_names_of raw))
        val sibling_state = clasimpLib.make_bound_simplification I
          (fn () => get ambient)
          (early [BoundedRewrites.Once (CONJ source sibling)])
        val sibling_used = null (checked
          (clasimpLib.asm_full_simp_bound false sibling_state [])
          ([],``iv_a x = iv_b x``))
        val sibling_quota = sibling_used andalso not (null (checked
          (clasimpLib.asm_full_simp_bound true sibling_state []) ([],target)))
        val eager = clasimpLib.make_bound_simplification I
          (fn () => get ambient) (early [BoundedRewrites.Once source])
        val eager_view = ignore (ss true eager)
        val cross_stage = null (checked
          (clasimpLib.asm_full_simp_bound true eager []) ([],target)) andalso
          aconv (boolSyntax.rhs (concl (Conv.QCONV
            (simpLib.SIMP_CONV (ss false eager) []) ``iv_c (iv_g x)``)))
            ``iv_c (iv_h x)``
        val empty = simpLib.empty_ss
        val empty_early = clasimpLib.make_supplied_converse_cache () charge
          empty (clasimpLib.prepare_supplied_rules empty [])
        val empty_state = clasimpLib.make_bound_simplification I
          (fn () => get empty) empty_early
        val empty_shared = Portable.pointer_eq (empty,ss false empty_state)
          andalso Portable.pointer_eq (empty,ss true empty_state)
        val no_markers = not (List.exists
          (fn name => name = "PREPARED_REWRITES")
          (simpLib.ssfrag_names_of (ss true empty_state)))
        val priority_ambient = simpLib.++
          (ambient,simpLib.rewrites [source])
        val priority_rule = proof ``!x. iv_c (iv_h x) = iv_a x``
        val priority_early = detect charge priority_ambient
          (clasimpLib.prepare_supplied_rules priority_ambient [priority_rule])
        val priority_state = clasimpLib.make_bound_simplification I
          (fn () => get priority_ambient) priority_early
        val priority = null (checked
          (clasimpLib.asm_full_simp_bound true priority_state [])
          ([],``iv_c (iv_h x) = iv_a x``))
        val compiles = ref 0
        val compile_base = simpLib.++ (ambient,simpLib.SSFRAG
          {name=NONE,convs=[],rewrs=[],ac=[],dprocs=[],congs=[],
           filter=SOME (fn theorem =>
             (compiles := !compiles + 1; [theorem]))})
        val compile_early = detect charge compile_base
          (clasimpLib.prepare_supplied_rules compile_base
            [BoundedRewrites.Once source])
        val compile_state = clasimpLib.make_bound_simplification I
          (fn () => get compile_base) compile_early
        val prefix = !compiles
        val _ = checked
          (clasimpLib.asm_full_simp_bound false compile_state []) ([],target)
        val _ = checked
          (clasimpLib.asm_full_simp_bound true compile_state []) ([],target)
        val _ = checked
          (clasimpLib.safe_asm_full_simp_bound true compile_state [])
          ([],target)
        val compile_once = prefix = 1 andalso !compiles = prefix
        val raw_used_state = clasimpLib.make_bound_simplification I
          (fn () => get ambient) (early [BoundedRewrites.Once source])
        val raw_used = Conv.QCONV
          (simpLib.SIMP_CONV (ss false raw_used_state) []) ``iv_c (iv_g x)``
        val raw_then_view =
          aconv (boolSyntax.rhs (concl raw_used)) ``iv_k x`` andalso
          not (null (checked
            (clasimpLib.asm_full_simp_bound true raw_used_state [])
            ([],target)))
        val retry_count = ref 0
        fun retry_table () =
          (retry_count := !retry_count + 1;
           if !retry_count = 1 then raise Fail "invocation provider"
           else get ambient)
        val retry_state = clasimpLib.make_bound_simplification I retry_table
          (early [BoundedRewrites.Once source])
        val interrupted = ((ignore (ss true retry_state); false)
          handle Fail message => message = "invocation provider")
        val retry = interrupted andalso null (checked
          (clasimpLib.asm_full_simp_bound true retry_state []) ([],target))
          andalso !retry_count = 2
        val budget = searchBudget.unbounded ()
        val current_budget = ref budget
        fun shared_charge () = searchBudget.charge (!current_budget)
          searchBudget.Normalization
        val budget_early = detect shared_charge ambient
          (clasimpLib.prepare_supplied_rules ambient [source])
        val budget_state = clasimpLib.make_bound_simplification I
          (fn () => get ambient) budget_early
        val _ = ignore (ss true budget_state)
        val _ = current_budget := searchBudget.create
          {candidates=NONE,applications=NONE,normalization=SOME 0}
        fun cutoff tactic = ((ignore (checked tactic ([],target)); false)
          handle searchBudget.LimitReached (searchBudget.Normalization,used) =>
            #normalization used = 0)
        val shared_budget = List.all cutoff
          [clasimpLib.asm_full_simp_bound true budget_state [],
           clasimpLib.safe_asm_full_simp_bound true budget_state [],
           clasimpLib.cascade_safe_simp_bound true budget_state []]
        val dummy_base = simpLib.++ (ambient,simpLib.name_ss
          "invocation dummy" (simpLib.rewrites [REFL ``iv_sentinel:bool``]))
        val marker_early = detect charge dummy_base
          (clasimpLib.prepare_supplied_rules dummy_base
            [BoundedRewrites.Once source])
        val marker_state = clasimpLib.make_bound_simplification I
          (fn () => get dummy_base) marker_early
        val _ = checked
          (clasimpLib.asm_full_simp_bound true marker_state []) ([],target)
        val marker = concl (simpLib.ExclSF "invocation dummy")
        val marker_quota = not (null (checked
          (clasimpLib.safe_asm_full_simp_bound true marker_state [])
          ([marker],target)))
        val checks = [lazy,raw_pass,derived,supplied,ambient_view,exhausted,
                      cached,raw_stays,sibling_quota,cross_stage,
                      empty_shared,no_markers,priority,compile_once,
                      raw_then_view,retry,shared_budget,marker_quota]
        val _ = print ("INVOCATION_STATE_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all I checks end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ = (tprint "invocation consumers share installed originals and views";
         if invocation_state_fixture () then OK ()
         else die "invocation state loses views or revives originals");

(* Classical search consumers retain the prepared invocation's controls. *)
fun bound_pipeline_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = new_theory "boundPipelineFixture"
        val g = new_definition ("bp_g_def", ``bp_g (x:bool) = T``)
        val h = new_definition ("bp_h_def", ``bp_h (x:bool) = T``)
        val c = new_definition ("bp_c_def", ``bp_c (x:bool) = T``)
        val k = new_definition ("bp_k_def", ``bp_k (x:bool) = T``)
        val i = new_definition ("bp_i_def", ``bp_i (x:bool) = T``)
        val o_def = new_definition ("bp_o_def", ``bp_o (x:bool) = T``)
        val definitions = [g,h,c,k,i,o_def]
        fun proof tm = Tactical.prove (tm,Rewrite.REWRITE_TAC definitions)
        val source = proof ``!x. bp_c (bp_g x) = bp_k x``
        val direct = proof ``!x. bp_i x = bp_o x``
        val reducer = proof ``!x. bp_g x = bp_h x``
        val name = {Thy=Theory.current_theory (),Name="reducer"}
        val base = simpLib.++ (boolSimps.bool_ss,
          simpLib.rewrites_with_names [(name,reducer)])
        fun ambient () = simpLib.++ (base,simpLib.name_ss
          "bound pipeline dummy"
            (simpLib.rewrites [REFL ``bp_sentinel:bool``]))
        val charges = ref 0
        val runtimes = ref 0
        fun charge () = charges := !charges + 1
        fun runtime ss = (runtimes := !runtimes + 1; ss)
        fun state arguments = clasimpLib.prepare_bound_simplification
          traceUtil.silent runtime charge (ambient ()) arguments
        val target = ([],``bp_c (bp_h x) = bp_k x``)
        val direct_target = ([],``bp_i x = bp_o x``)
        val arguments = [simpLib.ExclSF "bound pipeline dummy",
          BoundedRewrites.Once (CONJ source direct)]
        val steps =
          [(fn cs => NTactical.DETERM (classicalLib.CS_FAST_TAC cs),
            clasimpLib.add_simp_wrapper_bound),
           (fn cs => NTactical.DETERM
              (classicalLib.CS_DEPTH_SOLVE_TAC {dup=false} 1 cs),
            clasimpLib.add_simp_wrapper_bound),
           (fn cs => NTactical.DETERM (classicalLib.CS_SAFE_TAC cs),
            clasimpLib.add_safe_simp_wrapper_bound),
           (fn cs => NTactical.DETERM (classicalLib.CS_CLARIFY_TAC cs),
            clasimpLib.add_safe_simp_wrapper_bound)]
        fun check (rung,wrap) =
          let
            val bound = state arguments
            val configured = wrap true bound [] clasetLib.empty_cs
            val baseline = not (valid_closes
              (Tactical.TRY (rung clasetLib.empty_cs)) target)
            val first = valid_closes (rung configured) target
            val remaining = not (valid_closes
              (Tactical.TRY (rung configured)) direct_target)
          in [baseline andalso first,remaining] end
        val rungs = List.concat (map check steps)
        val bound = state [simpLib.ExclX "rule:boundPipelineFixture.reducer",
          source]
        val controlled = not (valid_closes
          (clasimpLib.asm_full_simp_bound true bound []) target)
        val replacement = clasimpLib.prepare_bound_simplification
          traceUtil.silent I charge
          boolSimps.bool_ss [simpLib.SF (simpLib.name_ss
            "bound pipeline replacement" (simpLib.rewrites [reducer])),source]
        val fragment = valid_closes
          (clasimpLib.asm_full_simp_bound true replacement []) target
        val raw = clasimpLib.bound_simplification_simpset false bound
        val excluded = not (List.exists
          (fn (SOME named,_) => #Name named = "reducer" | _ => false)
          (#1 (simpLib.rewrite_sources raw [])))
        val once_runtime = !runtimes = 5
        val checks = rungs @ [controlled,fragment,excluded,once_runtime]
        val _ = print ("BOUND_PIPELINE_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all I checks end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ = (tprint "prepared bindings reach classical search wrappers";
         if bound_pipeline_fixture () then OK ()
         else die "search wrapper reinstalls bound original arguments");

(* Runtime decision procedures receive the originals installed afterward. *)
fun bound_runtime_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = new_theory "boundRuntimeFixture"
        val definition = new_definition ("br_goal_def", ``br_goal = T``)
        val sentinel = REFL ``br_sentinel:bool``
        val primed = ref 0
        val untagged = ref true
        val queries = ref 0
        val runtimes = ref 0
        exception RuntimeContext of bool
        val decision = Traverse.CONTEXT_REDUCER
          {name=SOME "bound runtime context",
           initial=RuntimeContext false,
           addcontext=fn (context,theorems) =>
             let
               val enabled = (raise context) handle RuntimeContext flag => flag
               val found = List.filter
                 (fn th => aconv (concl th) (concl sentinel)) theorems
               val _ = if null found then () else primed := !primed + 1
               val _ = untagged := (!untagged andalso List.all
                 (not o can BoundedRewrites.DEST_BOUNDED) found)
             in RuntimeContext (enabled orelse not (null found)) end,
           apply=fn {context,...} => fn tm =>
             let
               val enabled = (raise context) handle RuntimeContext flag => flag
               val _ = queries := !queries + 1
             in if enabled andalso aconv tm ``br_goal`` then definition
                else Conv.NO_CONV tm end}
        fun runtime ss =
          (runtimes := !runtimes + 1;
           simpLib.++ (ss,simpLib.dproc_ss decision))
        val bound = clasimpLib.prepare_bound_simplification
          traceUtil.silent runtime (fn () => ()) simpLib.empty_ss
          [BoundedRewrites.Once sentinel]
        val prepared = !runtimes = 1 andalso !primed = 1 andalso !untagged
        val used = valid_closes
          (clasimpLib.asm_full_simp_bound false bound []) ([],``br_goal``)
        val queried = !queries > 0
        val viewed = valid_closes
          (clasimpLib.safe_asm_full_simp_bound true bound []) ([],``br_goal``)
        val retained = !runtimes = 1 andalso !primed = 1 andalso !untagged
        val checks = [prepared,used,queried,viewed,retained]
        val _ = print ("BOUND_RUNTIME_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all I checks end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ = (tprint "runtime decision procedures receive bound original context";
         if bound_runtime_fixture () then OK ()
         else die "runtime decision context misses bound originals");

(* Argument roles enter one binding without becoming ambient reducers. *)
fun bound_argument_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = new_theory "boundArgumentFixture"
        val g = new_definition ("ba_g_def", ``ba_g (x:bool) = T``)
        val h = new_definition ("ba_h_def", ``ba_h (x:bool) = T``)
        val c = new_definition ("ba_c_def", ``ba_c (x:bool) = T``)
        val d = new_definition ("ba_d_def", ``ba_d (x:bool) = T``)
        val k = new_definition ("ba_k_def", ``ba_k (x:bool) = T``)
        val i = new_definition ("ba_i_def", ``ba_i (x:bool) = T``)
        val o_def = new_definition ("ba_o_def", ``ba_o (x:bool) = T``)
        fun proof tm = Tactical.prove
          (tm,Rewrite.REWRITE_TAC [g,h,c,d,k,i,o_def])
        val reducer = proof ``!x. ba_g x = ba_h x``
        val ambient_source = proof ``!x. ba_d (ba_g x) = ba_k x``
        val supplied_source = proof ``!x. ba_c (ba_g x) = ba_k x``
        val sibling = proof ``!x. ba_i x = ba_o x``
        val base = simpLib.++ (pureSimps.pure_ss,simpLib.rewrites
          [boolTheory.REFL_CLAUSE,ambient_source])
        fun pipeline budget runtime body ss args =
          clasimpLib.process_clasimp_bound_args clasetLib.SafeFacts budget
            runtime body clasetLib.empty_cs ss args
        fun simplify viewed bound _ _ =
          clasimpLib.asm_full_simp_bound viewed bound []
        fun tactic viewed ss args = pipeline (searchBudget.unbounded ())
          I (simplify viewed) ss args
        val ambient_target = ([],``ba_d (ba_h x) = ba_k x``)
        fun separate wrap = not (valid_closes
          (tactic true base [wrap reducer]) ambient_target)
        val simp_separate = separate clasetLib.Simp
        val iff_separate = separate clasetLib.Iff
        fun direct wrap = valid_closes
          (tactic false base [wrap reducer]) ([],``ba_g x = ba_h x``)
        val simp_direct = direct clasetLib.Simp
        val iff_direct = direct clasetLib.Iff
        val legacy = ref []
        val actual = ref []
        fun remember cell cs =
          (cell := clasetLib.rules_of cs; Tactical.ALL_TAC)
        val declarations = [clasetLib.Iff reducer,clasetLib.Simp reducer]
        val _ = residual
          (clasimpLib.process_clasimp_args
            (fn cs => fn _ => fn _ => remember legacy cs)
            clasetLib.empty_cs base declarations) ([],``ba_open:bool``)
        val _ = residual (pipeline (searchBudget.unbounded ()) I
          (fn _ => fn cs => fn _ => remember actual cs) base declarations)
          ([],``ba_open:bool``)
        val roles = not (null (!legacy)) andalso ListPair.allEq
          (fn ((spec,(name,th)),(other,(other_name,other_th))) =>
            same_spec spec other andalso name = other_name andalso
            same_thm th other_th) (!legacy,!actual)
        val raw_fact = ASSUME ``ba_support:bool``
        val environment_ok = ref false
        fun inspect_environment _ _ environment =
          let
            val first = clasetFacts.schematic_views environment
            val second = clasetFacts.schematic_views environment
          in
            environment_ok := (case (first,second) of
                ([left],[right]) =>
                  same_thm (#source left) raw_fact andalso
                  #source_id left = #source_id right andalso
                  Portable.pointer_eq (#theorem left,#theorem right) andalso
                  List.exists (aconv ``ba_support:bool``) (#support left)
              | _ => false);
            Tactical.ALL_TAC
          end
        val remaining = residual (pipeline (searchBudget.unbounded ()) I
          inspect_environment base [raw_fact])
          ([``ba_support:bool``],``ba_open:bool``)
        val facts = !environment_ok andalso (case remaining of
            [(assumptions,_)] =>
              List.exists (aconv ``ba_support:bool``) assumptions
          | _ => false)
        val with_reducer = simpLib.++ (base,simpLib.rewrites [reducer])
        val quota_ok = ref false
        fun quota bound _ _ =
          (quota_ok := (valid_closes
              (clasimpLib.asm_full_simp_bound true bound [])
              ([],``ba_c (ba_h x) = ba_k x``) andalso
            not (valid_closes
              (clasimpLib.asm_full_simp_bound false bound [])
              ([],``ba_i x = ba_o x``)));
           Tactical.ALL_TAC)
        val _ = residual (pipeline (searchBudget.unbounded ()) I quota
          with_reducer [BoundedRewrites.Once
            (CONJ supplied_source sibling)]) ([],``ba_open:bool``)
        val label = markerLib.MK_LABEL ("bound_argument",reducer)
        val labelled = valid_closes
          (tactic false base [markerLib.L "bound_argument"])
          ([concl label],``ba_g x = ba_h x``)
        val required = valid_closes
          (tactic false base [markerLib.mk_Req0 reducer])
          ([],``ba_g x = ba_h x``)
        val exhausted = BoundedRewrites.Ntimes reducer 0
        val rejected = tactic_fails
          (tactic false base [markerLib.mk_Req0 exhausted])
          ([],``ba_g x = ba_h x``)
        val zero = searchBudget.create
          {candidates=NONE,applications=NONE,normalization=SOME 0}
        val cutoff = ((ignore (residual
          (pipeline zero I (simplify false) base [clasetLib.Simp reducer])
          ([],``ba_g x = ba_h x``)); false)
          handle searchBudget.LimitReached (searchBudget.Normalization,_) =>
            true)
        val required_view = valid_closes
          (tactic true with_reducer
            [markerLib.mk_Req0 (BoundedRewrites.Once supplied_source)])
          ([],``ba_c (ba_h x) = ba_k x``)
        val required_quota = ref false
        fun required_consumers bound _ _ =
          (required_quota := (valid_closes
              (clasimpLib.asm_full_simp_bound false bound [])
              ([],``ba_g x = ba_h x``) andalso
            tactic_fails (clasimpLib.asm_full_simp_bound true bound [])
              ([],``ba_i x = ba_o x``));
           Tactical.ALL_TAC)
        val _ = residual (pipeline (searchBudget.unbounded ()) I
          required_consumers base
          [markerLib.mk_Req0 (BoundedRewrites.Once (CONJ reducer sibling))])
          ([],``ba_open:bool``)
        val decreased = valid_closes
          (tactic false base [markerLib.mk_ReqD reducer])
          ([],``ba_g x = ba_h x``)
        val undecreased = tactic_fails
          (tactic false base [markerLib.mk_ReqD exhausted])
          ([],``ba_g x = ba_h x``)
        val checks = [simp_separate,iff_separate,simp_direct,iff_direct,
                      roles,facts,!quota_ok,labelled,required,rejected,cutoff,
                      required_view,!required_quota,decreased,undecreased]
        val _ = print ("BOUND_ARGUMENT_PIPELINE_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all I checks end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ = (tprint "public argument binding preserves roles and original sources";
         if bound_argument_fixture () then OK ()
         else die "argument roles become ambient reducers or lose controls");

(* Whole tactic drivers must consume the already compiled occurrences. *)
fun bound_driver_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = new_theory "boundDriverFixture"
        val i = new_definition ("bd_i_def", ``bd_i (x:bool) = T``)
        val o_def = new_definition ("bd_o_def", ``bd_o (x:bool) = T``)
        val p = new_definition ("bd_p_def", ``bd_p (x:bool) = T``)
        val original = Tactical.prove
          (``!x. bd_i x = bd_o x``,Rewrite.REWRITE_TAC [i,o_def])
        val introduction = Tactical.prove
          (``!x. (bd_i x = bd_o x) ==> bd_p x``,
           Rewrite.REWRITE_TAC [p])
        val target = ([],``bd_i x = bd_o x``)
        fun claset safe = clasetLib.add_rule
          {kind=clasetRules.Intro,safe=safe,prio=NONE}
          ("bound driver introduction",introduction) clasetLib.empty_cs
        val drivers =
          [clasimpLib.auto_bound {blast=0,depth=2},
           clasimpLib.force_bound (searchBudget.unbounded ()),
           clasimpLib.fastforce_bound,clasimpLib.slowsimp_bound,
           clasimpLib.bestsimp_bound,clasimpLib.clarsimp_bound]
        fun one driver cs goal =
          let
            val compiles = ref 0
            val base = simpLib.++ (pureSimps.pure_ss,
              simpLib.rewrites [boolTheory.REFL_CLAUSE])
            val ambient = simpLib.++ (base,simpLib.SSFRAG
              {name=NONE,convs=[],rewrs=[],ac=[],dprocs=[],congs=[],
               filter=SOME (fn theorem =>
                 (compiles := !compiles + 1; [theorem]))})
            val state = clasimpLib.prepare_bound_simplification
              traceUtil.silent I (fn () => ()) ambient
              [BoundedRewrites.Once original]
            val compiled = !compiles = 1
            val closed = (valid_closes
              (driver true state cs) goal handle HOL_ERR _ => false)
            val exhausted = not (valid_closes
              (clasimpLib.asm_full_simp_bound false state []) target)
            val retained = compiled andalso !compiles = 1
          in [closed,exhausted,retained] end
        val direct = List.concat (map
          (fn driver => one driver clasetLib.empty_cs target) drivers)
        val nested = List.concat (map
          (fn (index,driver) =>
            one driver (claset (index = 5)) ([],``bd_p x``))
          (Lib.enumerate 0 drivers))
        val schedule = !clasimpLib.force_schedule
        fun depth () =
          (clasimpLib.force_schedule :=
             {best={candidates=1,applications=1,normalization=1},
              tableau={candidates=1,applications=1,normalization=1},
              depth={candidates=5000,applications=500,normalization=500},
              blast_depth=0,classical_depth=1};
           one (clasimpLib.force_bound (searchBudget.unbounded ()))
             (claset false) ([],``bd_p x``))
        val depth_checks = Portable.finally
          (fn () => clasimpLib.force_schedule := schedule) depth ()
        val final_safe = one (clasimpLib.auto_bound {blast=0,depth=0})
          (claset true) ([],``bd_p x``)
        val checks = direct @ nested @ depth_checks @ final_safe
        val _ = print ("BOUND_DRIVER_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all I checks end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ = (tprint "tactic drivers retain supplied compilation and consumption";
         if bound_driver_fixture () then OK ()
         else die "tactic driver reinstalls supplied original occurrences");

(* Extensional steps must read the rewrites their simplifier can use. *)
fun effective_reading_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = new_theory "effectiveReadingFixture"
        val g = new_definition ("er_g_def", ``er_g (x:bool) = T``)
        val h = new_definition ("er_h_def", ``er_h (x:bool) = T``)
        val c = new_definition ("er_c_def", ``er_c (x:bool) y = T``)
        val d = new_definition ("er_d_def", ``er_d (x:bool) y = T``)
        val b = new_definition ("er_b_def", ``er_b (x:bool) = T``)
        val old = new_definition
          ("er_old_def", ``er_old (y:bool) = \(x:bool). T``)
        val new = new_definition
          ("er_new_def", ``er_new (y:bool) = \(x:bool). T``)
        val rhs = new_definition
          ("er_rhs_def", ``er_rhs (y:bool) = \(x:bool). T``)
        val definitions = [g,h,c,d,b,old,new,rhs,
                           boolTheory.IN_DEF,boolTheory.FUN_EQ_THM]
        fun proof tm = Tactical.prove
          (tm,Rewrite.REWRITE_TAC definitions)
        val reading = proof
          ``!x. (er_c (er_g x) = er_d x) <=> er_b x``
        val reducer = proof ``!x. er_g x = er_h x``
        val member = proof ``!x y. x IN er_old y <=> x IN er_rhs y``
        val set_reducer = proof ``!y. er_old y = er_new y``
        fun state ambient supplied =
          clasimpLib.prepare_bound_simplification
            traceUtil.silent I (fn () => ())
            (simpLib.++ (pureSimps.pure_ss,simpLib.rewrites
              (boolTheory.REFL_CLAUSE :: ambient))) supplied
        val root = state [reducer,b] [reading]
        val root_goal = ([],``er_c (er_h x) = er_d x``)
        val sets = state [set_reducer] [member]
        val set_goal = ([],``er_new y = er_rhs y``)
        fun closed tactic goal = valid_closes tactic goal
          handle HOL_ERR _ => false
        fun auto bound goal = closed
          (clasimpLib.auto_bound {blast=0,depth=0} true bound
            clasetLib.empty_cs) goal
        val raw = clasimpLib.bound_simplification_simpset false sets
        val viewed = clasimpLib.bound_simplification_simpset true sets
        val named = simpLib.++
          (simpLib.++ (pureSimps.pure_ss,simpLib.rewrites [set_reducer]),
           simpLib.rewrites_with_names
             [({Thy=Theory.current_theory (),Name="er_member"},member)])
        val named_state = clasimpLib.prepare_bound_simplification
          traceUtil.silent I (fn () => ()) named []
        val named_views =
          clasimpLib.bound_simplification_simpset true named_state
        val removed = simpLib.remove_simps ["er_member"] named_views
        val (excluded,_) = simpLib.prepare_rewrite_arguments named_views
          [simpLib.Excl "er_member"]
        val discard_base = simpLib.++ (pureSimps.pure_ss,simpLib.SSFRAG
          {name=NONE,convs=[],rewrs=[],ac=[],dprocs=[],congs=[],
           filter=SOME (fn _ => [])})
        val discarded = simpLib.++ (discard_base,simpLib.rewrites [member])
        val checks =
          [not (closed (clasimpLib.asm_full_simp_bound false root [])
                  root_goal),
           closed (clasimpLib.asm_full_simp_bound true root []) root_goal,
           auto root root_goal,
           not (clasimpLib.reads_as_membership raw (#2 set_goal)),
           clasimpLib.reads_as_membership viewed (#2 set_goal),
           not (closed (clasimpLib.asm_full_simp_bound true sets [])
                  set_goal),
           auto sets set_goal,
           clasimpLib.reads_as_membership named_views (#2 set_goal),
           not (clasimpLib.reads_as_membership removed (#2 set_goal)),
           not (clasimpLib.reads_as_membership excluded (#2 set_goal)),
           not (clasimpLib.reads_as_membership discarded
                  ``er_old y = er_rhs y``)]
        val _ = print ("EFFECTIVE_READING_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all I checks end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ = (tprint "extensional drivers honor installed rewrite views";
         if effective_reading_fixture () then OK ()
         else die "extensional driver cannot see its effective rewrites");

(* Fact/rule retries retain their environment and installed binding. *)
fun bound_transport_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = new_theory "boundTransportFixture"
        val g = new_definition ("bt_g_def", ``bt_g (x:bool) = T``)
        val h = new_definition ("bt_h_def", ``bt_h (x:bool) = T``)
        val p = new_definition ("bt_p_def", ``bt_p (x:bool) = T``)
        val q = new_definition ("bt_q_def", ``bt_q (x:bool) = T``)
        val r = new_definition ("bt_r_def", ``bt_r (x:bool) = T``)
        fun proof tm = Tactical.prove
          (tm,Rewrite.REWRITE_TAC [g,h,p,q,r])
        val reducer = proof ``!x. bt_g x = bt_h x``
        val bridge = proof ``!x. bt_p x = bt_q x``
        val fact = Drule.ADD_ASSUM ``bt_support:bool``
          (proof ``!x. bt_p (bt_g x)``)
        val conditional = proof ``!x. bt_p (bt_g x) ==> bt_r x``
        val basis = simpLib.++ (pureSimps.pure_ss,simpLib.rewrites
          [boolTheory.REFL_CLAUSE,reducer,bridge])
        fun pipeline_runtime runtime viewed consumer ss args body =
          clasimpLib.process_clasimp_bound_fact_views viewed consumer
            (searchBudget.unbounded ()) runtime body clasetLib.empty_cs ss args
        val pipeline = pipeline_runtime I
        fun closes tactic goal = valid_closes tactic goal
          handle HOL_ERR _ => false
        val compiles = ref 0
        fun fact_rewrite theorem =
          let
            val (_,equation) = boolSyntax.strip_imp_only
              (concl (Drule.SPEC_ALL theorem))
            val (left,right) = boolSyntax.dest_eq equation
            val head = fst (boolSyntax.strip_comb left)
          in aconv right boolSyntax.T andalso
             (aconv head ``bt_p`` orelse aconv head ``bt_q``) end
          handle HOL_ERR _ => false
        fun record (item as (theorem,_)) =
          (if fact_rewrite theorem then compiles := !compiles + 1 else ();
           [item])
        val instrumented = simpLib.++ (basis,simpLib.SSFRAG
          {name=NONE,convs=[],rewrs=[],ac=[],dprocs=[],congs=[],
           filter=SOME record})
        val metadata = ref false
        val native = ref false
        fun simplify viewed bound _ environment =
          let
            val first = clasetFacts.schematic_views environment
            val second = clasetFacts.schematic_views environment
            val _ = metadata := (case (first,second) of
                ([left],[right]) => #source_id left = #source_id right
                  andalso same_thm (#source left) fact
                  andalso Portable.pointer_eq (#theorem left,#theorem right)
                  andalso List.exists (aconv ``bt_support:bool``)
                    (#support right)
              | _ => false)
            val ss = clasimpLib.bound_simplification_simpset viewed bound
            fun is_fact source =
              let val (_,theorem) = simpLib.source_rewrite source
                  val (left,right) = boolSyntax.dest_eq (concl theorem)
              in aconv right boolSyntax.T andalso
                 aconv (fst (boolSyntax.strip_comb left)) ``bt_p`` end
              handle HOL_ERR _ => false
            val _ = native := length (List.filter is_fact
              (simpLib.rewrite_source_handles ss)) = 1
          in
            Tactic.CONV_TAC (simpLib.SIMP_CONV_CHILD_FIRST
              (clasimpLib.bound_simplification_policy bound) ss [])
          end
        val plain = closes
          (pipeline false clasetLib.SearchFacts instrumented [fact]
            (simplify false))
          ([``bt_support:bool``],``bt_q (bt_h x)``)
        val one_compile = !compiles = 1
        val original_metadata = !metadata
        val original_native = !native
        val primed = ref 0
        val runtimes = ref 0
        val untagged = ref true
        exception TransportContext
        val observer = Traverse.CONTEXT_REDUCER
          {name=SOME "bound transport context",initial=TransportContext,
           addcontext=fn (context,theorems) =>
             let
               val facts = List.filter
                 (fn th => aconv (concl th) (concl fact)) theorems
               val _ = if null facts then () else primed := !primed + 1
               val _ = untagged := (!untagged andalso List.all
                 (not o can BoundedRewrites.DEST_BOUNDED) facts)
             in context end,
           apply=fn _ => Conv.NO_CONV}
        fun runtime ss =
          (runtimes := !runtimes + 1;
           simpLib.++ (ss,simpLib.dproc_ss observer))
        val prefix = !compiles
        val viewed_plain = closes
          (pipeline_runtime runtime true clasetLib.SearchFacts
            instrumented [fact] (simplify true))
          ([``bt_support:bool``],``bt_q (bt_h x)``)
        val once_runtime = !runtimes = 1 andalso !primed = 1 andalso
          !untagged andalso !compiles = prefix + 1
        val discarded = simpLib.++ (basis,simpLib.SSFRAG
          {name=NONE,convs=[],rewrs=[],ac=[],dprocs=[],congs=[],
           filter=SOME (fn (item as (th,_)) =>
             if fact_rewrite th then [] else [item])})
        val no_origin = not (closes
          (pipeline false clasetLib.SearchFacts discarded [fact]
            (simplify false)) ([``bt_support:bool``],``bt_q (bt_h x)``))
        val roles = ref false
        fun search _ cs _ =
          (roles := (length (clasetLib.rules_of cs) = 2 andalso
             List.all (fn (spec,_) => same_spec spec
               {kind=clasetRules.Dest,safe=false,prio=NONE})
               (clasetLib.rules_of cs));
           NTactical.DETERM (classicalLib.CS_FAST_TAC cs))
        val searched = closes
          (pipeline false clasetLib.SearchFacts basis [conditional] search)
          ([``bt_q (bt_h x)``],``bt_r x``)
        val further_bridge = proof ``!x. bt_q x = bt_r x``
        val direct_rule = proof ``!x. bt_p x ==> bt_q x``
        val other_rule = proof ``!x. bt_h x ==> bt_r x``
        val own_source_excluded = closes
          (pipeline false clasetLib.SafeFacts
            (simpLib.++ (basis, simpLib.rewrites [further_bridge]))
            [clasetLib.SIntro direct_rule, clasetLib.SIntro other_rule]
            (fn _ => fn cs => fn _ =>
              NTactical.DETERM (classicalLib.CS_FAST_TAC cs)))
          ([``bt_p x``], ``bt_r x``)
        val safe_roles = ref false
        val _ = residual (pipeline false clasetLib.SafeFacts basis
          [conditional] (fn _ => fn cs => fn _ =>
            (safe_roles := null (clasetLib.rules_of cs); Tactical.ALL_TAC)))
          ([``bt_q (bt_h x)``],``bt_r x``)
        val retained = ref NONE
        val same_binding = ref true
        val raw = simpLib.++ (pureSimps.pure_ss,simpLib.rewrites
          [boolTheory.REFL_CLAUSE])
        fun tagged bound cs _ =
          (case !retained of NONE => retained := SOME bound
             | SOME previous => same_binding := (!same_binding andalso
                 Portable.pointer_eq (previous,bound));
           NTactical.DETERM (classicalLib.CS_FAST_TAC cs))
        val marker_closed = closes
          (pipeline false clasetLib.SearchFacts raw
            [BoundedRewrites.Once reducer,clasetLib.SIntro conditional]
            tagged) ([``bt_p (bt_h x)``],``bt_r x``)
        val (private_use,exhausted) = case !retained of
            NONE => (false,false)
          | SOME bound =>
              (closes (clasimpLib.asm_full_simp_bound false bound [])
                 ([],``bt_g x = bt_h x``),
               not (closes (clasimpLib.asm_full_simp_bound false bound [])
                 ([],``bt_g x = bt_h x``)))
        val limited = searchBudget.create
          {candidates=NONE,applications=NONE,normalization=SOME 10000}
        val cutoff_state = ref NONE
        val cutoff_used = ref false
        fun uncharged bound = Tactic.CONV_TAC (simpLib.SIMP_CONV
          (clasimpLib.bound_simplification_simpset false bound) [])
        fun exhaust () =
          if searchBudget.available limited searchBudget.Normalization then
            (searchBudget.charge limited searchBudget.Normalization;
             exhaust ())
          else ()
        fun before_cutoff bound cs _ =
          (cutoff_state := SOME bound;
           cutoff_used := closes (uncharged bound)
             ([],``bt_g x = bt_h x``);
           exhaust ();
           NTactical.DETERM (classicalLib.CS_FAST_TAC cs))
        val cutoff = ((ignore (residual
          (clasimpLib.process_clasimp_bound_fact_views false
            clasetLib.SearchFacts limited I before_cutoff
            clasetLib.empty_cs raw
            [BoundedRewrites.Ntimes reducer 2,clasetLib.SIntro conditional])
          ([``bt_p (bt_h x)``],``bt_r x``)); false)
          handle searchBudget.LimitReached (searchBudget.Normalization,_) =>
            true)
        val cutoff_restores = case !cutoff_state of NONE => false
          | SOME bound => !cutoff_used andalso closes (uncharged bound)
              ([],``bt_g x = bt_h x``) andalso
              not (closes (uncharged bound) ([],``bt_g x = bt_h x``))
        val checks = [plain,one_compile,original_metadata,original_native,
                      searched,!roles,
                      !safe_roles,marker_closed,private_use,exhausted,
                      !same_binding,viewed_plain,once_runtime,no_origin,
                      cutoff,cutoff_restores,own_source_excluded]
        val _ = print ("BOUND_TRANSPORT_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all I checks end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ = (tprint "bound fact/rule transport retains original sources";
         if bound_transport_fixture () then OK ()
         else die "transport loses fact forms or spends original quotas");

(* A rewrite view follows its proper argument's child-first normal form. *)
fun lhs_guard_fixture () =
  let
    open boolLib
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = Theory.new_theory "lhsGuardFixture"
        val g_def = new_definition
          ("lhs_guard_g_def", ``lhs_guard_g (x:bool) = T``)
        val h_def = new_definition
          ("lhs_guard_h_def", ``lhs_guard_h (x:bool) = T``)
        val c_def = new_definition
          ("lhs_guard_c_def", ``lhs_guard_c (f:bool -> bool) x = f x``)
        val k_def = new_definition
          ("lhs_guard_k_def", ``lhs_guard_k (f:bool -> bool) x = f x``)
        val _ = new_constant ("lhs_guard_p", bool --> bool)
        val _ = new_constant ("lhs_guard_x", bool)
        fun prove_local term = Tactical.prove
          (term,
           Rewrite.REWRITE_TAC [g_def, h_def, c_def, k_def] THEN
           Tactic.BETA_TAC THEN Rewrite.REWRITE_TAC [])
        val source = prove_local
          ``!P x. lhs_guard_c (\v. lhs_guard_g v ==> P v) x =
                  lhs_guard_k P x``
        val reducer = prove_local ``!x. lhs_guard_g x = lhs_guard_h x``
        val target =
          ``lhs_guard_c (\v. lhs_guard_h v ==> lhs_guard_p v)
              lhs_guard_x = lhs_guard_k lhs_guard_p lhs_guard_x``
        fun named name theorem ss = simpLib.++
          (ss, simpLib.rewrites_with_names
            [({Thy=Theory.current_theory (), Name=name}, theorem)])
        val reducing = simpLib.++
          (boolSimps.bool_ss, boolSimps.ETA_ss)
          |> named "lhs_guard_reducer" reducer
        val installed = named "lhs_guard_source" source reducing
        fun checked tactic =
          let
            val (remaining, validate) = Tactical.VALID tactic ([], target)
            val proofs = map
              (fn residual => Tactical.prove_goal
                (residual,
                 Rewrite.REWRITE_TAC [g_def, h_def, c_def, k_def] THEN
                 Tactic.BETA_TAC THEN Rewrite.REWRITE_TAC [])) remaining
            val theorem = validate proofs
            val _ = if null (hyp theorem) andalso
                       aconv (concl theorem) target then ()
                    else raise Fail "LHS guard fixture validation"
          in null remaining end
        val ambient = checked (clasimpLib.asm_full_simp installed [])
        val supplied = checked (clasimpLib.asm_full_simp reducing [source])
        fun controls () =
          not (checked (simpLib.SIMP_TAC installed [])) andalso
          not (checked (clasimpLib.asm_full_simp
            (simpLib.remove_simps ["lhs_guard_source"] installed) [])) andalso
          not (checked (clasimpLib.asm_full_simp installed
            [simpLib.Excl "lhs_guard_source"])) andalso
          not (checked (clasimpLib.asm_full_simp
            (named "lhs_guard_source" source boolSimps.bool_ss) [reducer]))
      in ambient andalso supplied andalso controls () end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ =
  (tprint "rewrite views follow a normalized proper guard argument";
   if lhs_guard_fixture () then OK ()
   else die "rewrite LHS is lost after proper-argument normalization");

(* Deferred views must retain raw subproofs and consumed supplied quotas. *)
local
  open boolLib
  val saved = Context.snapshot ()
  fun run () =
    let
      val _ = new_theory "deferredQuotaFixture"
      val g = new_definition ("dq_g_def", ``dq_g (x:bool) = T``)
      val h = new_definition ("dq_h_def", ``dq_h (x:bool) = T``)
      val c = new_definition ("dq_c_def", ``dq_c (f:bool -> bool) x = f x``)
      val k = new_definition ("dq_k_def", ``dq_k (f:bool -> bool) x = f x``)
      val flag = new_definition ("dq_flag_def", ``dq_flag (x:bool) = T``)
      val _ = new_constant ("dq_p", bool --> bool)
      fun proof tm = Tactical.prove
        (tm, Rewrite.REWRITE_TAC [g,h,c,k,flag] THEN Tactic.BETA_TAC THEN
             Rewrite.REWRITE_TAC [])
      val source = proof
        ``!P x. dq_c (\v. dq_g v ==> P v) x = dq_k P x``
      val reducer = proof ``!x. dq_g x = dq_h x``
      val once_rule = proof ``!x. dq_flag x = T``
      fun named name th ss = simpLib.++ (ss,simpLib.rewrites_with_names
        [({Thy=Theory.current_theory (),Name=name},th)])
      val ss = simpLib.++ (boolSimps.bool_ss,boolSimps.ETA_ss)
        |> named "dq_reducer" reducer |> named "dq_source" source
      val guard = ``dq_c (\v. dq_h v ==> dq_p v) x = dq_k dq_p x``
      val one = ``dq_flag x /\ ^guard``
      val two = ``dq_flag x /\ dq_flag y /\ ^guard``
      fun closes args target =
        let
          val (goals,validate) = SelfTestTactical.VALID
            (clasimpLib.asm_full_simp ss args) ([],target) (Context.snapshot ())
          val proofs = map (fn goal => Tactical.prove_goal
            (goal,Rewrite.REWRITE_TAC [g,h,c,k,flag] THEN Tactic.BETA_TAC THEN
                  Rewrite.REWRITE_TAC [])) goals
          val theorem = validate proofs
          val _ = if null (hyp theorem) andalso aconv (concl theorem) target
                  then () else raise Fail "deferred quota validation"
        in null goals end
      val checks =
        [closes [BoundedRewrites.Once once_rule] one,
         closes [BoundedRewrites.Ntimes once_rule 2] two,
         not (closes [BoundedRewrites.Once once_rule] two)]
      val _ = print ("DEFERRED_QUOTA_RESULTS " ^
        String.concatWith " " (map Bool.toString checks) ^ "\n")
    in
      tprint "deferred views retain raw proofs and spent rewrite quotas";
      if List.all I checks then OK ()
      else die "retry discarded a raw proof or refreshed a supplied quota"
    end
in
  val _ = Portable.finally (fn () => Context.restore saved) run ()
end;

(* A proof reads the bottom-up declarations of the context it runs in,
   whatever the global context declares. *)
local
  val saved = Context.snapshot ()
  fun run () =
    let
      val _ = new_theory "bottomUpContextFixture"
      val wrap_def = new_definition
        ("bu_wrap_def", ``bu_wrap (n:num) <=> n = 0``)
      val view_def = new_definition
        ("bu_view_def", ``bu_view (n:num) <=> n <> 0``)
      val rule = Tactical.prove
        (``!n. ~bu_wrap n <=> bu_view n``,
         Rewrite.REWRITE_TAC [wrap_def, view_def])
      val pw_def = new_definition ("Pw_def", ``Pw (b:bool) = T``)
      val pw_rw = Tactical.prove
        (``!y. Pw (~bu_wrap y) = T``, Rewrite.REWRITE_TAC [pw_def])
      fun residue ctxt =
        case BasicProvers.SRW_TAC [] [] ([], ``~bu_wrap x``) ctxt of
            ([(_, w)], _) => w
          | _ => ``F``
      val unfolded = ``bu_view x ==> ~bu_wrap x``
      fun auto_closes args goal ctxt =
        closes_in ctxt (clasimpLib.AUTO_TAC args) ([], goal)
      val _ = boolLib.save_thm ("bu_rule1[iff_bottom_up]", rule)
      val with_rule = Context.snapshot ()
      val _ = clasimpLib.remove_iff_bottom_up "bu_rule1"
      val without_rule = Context.snapshot ()
      val _ = boolLib.save_thm ("bu_rule2[iff_bottom_up]", rule)
      val declared = Context.snapshot ()
      val _ = clasimpLib.remove_iff_bottom_up "bu_rule2"
      fun srw_of ctxt = BasicProvers.srw_ss_of ctxt
      (* The global context declares the rule only while [body] runs. *)
      fun globally_declared name body =
        let
          val _ = boolLib.save_thm (name ^ "[iff_bottom_up]", rule)
          val result = body ()
            handle e => (clasimpLib.remove_iff_bottom_up name; raise e)
          val _ = clasimpLib.remove_iff_bottom_up name
        in result end
      fun views_follow () =
        auto_closes [pw_rw] ``Pw (bu_view x)`` with_rule andalso
        not (auto_closes [pw_rw] ``Pw (bu_view x)`` without_rule) andalso
        auto_closes [pw_rw] ``Pw (bu_view x)`` with_rule
    in
      check ("a bottom-up declaration or retraction gives a new srw_ss",
             fn () =>
               not (Portable.pointer_eq
                      (srw_of with_rule, srw_of without_rule)) andalso
               not (Portable.pointer_eq
                      (srw_of without_rule, srw_of declared)));
      check ("SRW_TAC reads the bottom-up rule of its context, global \
             \retracted",
             fn () => aconv (residue with_rule) ``bu_view x``);
      check ("SRW_TAC ignores the global bottom-up rule its context lacks",
             fn () =>
               globally_declared "bu_rule3"
                 (fn () => aconv (residue without_rule) ``~bu_wrap x``));
      check ("AUTO_TAC closes with the rule of its context, global \
             \retracted",
             fn () => auto_closes [] unfolded with_rule);
      check ("AUTO_TAC does not use the global rule its context lacks",
             fn () =>
               globally_declared "bu_rule4"
                 (fn () => not (auto_closes [] unfolded without_rule)));
      check ("rewrite views follow the context, global retracted",
             views_follow);
      check ("rewrite views follow the context, global declared",
             fn () => globally_declared "bu_rule5" views_follow)
    end
in
  val _ = Portable.finally (fn () => Context.restore saved) run ()
end;
