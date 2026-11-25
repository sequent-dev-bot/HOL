open testutils
open linarithSolve
open linarithCorpus

val two = Arbint.two
val three = Arbint.fromInt 3

fun last xs = hd (rev xs)

val _ =
  check
    ("linarith ships the [arith] and [arith_split] tables empty",
     fn () =>
       null (linarithData.arith_facts ()) andalso
       null (linarithData.arith_split_thms ()))

(* The num split seeds no longer carry [arith_split]: they reach the
   split channel through the instance's pre_split, which is the other
   half of what the split rules union.  Pinned here, where the attribute
   table used to be. *)
val num_split_seeds =
  [linarithSeedTheory.NUM_MIN_SPLIT,
   linarithSeedTheory.NUM_MAX_SPLIT,
   linarithSeedTheory.NUM_SUB_SPLIT]

val _ =
  check
    ("the three num split seeds arrive through the instance channel",
     fn () =>
       let
         val pre_splits =
           List.concat (map #pre_split (linarithData.all_instances ()))
         fun offered seed =
           List.exists
             (fn rule => Term.aconv (Thm.concl rule) (Thm.concl seed))
             pre_splits
       in
         List.all offered num_split_seeds andalso
         List.all (not o splitLib.is_asm_split) num_split_seeds
       end)

val num_instance = linarithNum.instance

val _ =
  check
    ("linarithLib registers the num instance at module load",
     fn () =>
       case linarithData.instance_for numSyntax.num of
           SOME instance => Option.isSome (#discrete instance)
         | NONE => false)

val num_x = Term.mk_var ("linarith_num_x", numSyntax.num)
val num_y = Term.mk_var ("linarith_num_y", numSyntax.num)
val num_z = Term.mk_var ("linarith_num_z", numSyntax.num)
val num_two = numSyntax.mk_numeral (Arbnum.fromInt 2)
val num_three = numSyntax.mk_numeral (Arbnum.fromInt 3)
val num_seven = numSyntax.mk_numeral (Arbnum.fromInt 7)
val num_eight = numSyntax.mk_numeral (Arbnum.fromInt 8)

fun num_plus left right = numSyntax.mk_plus (left, right)
fun num_leq left right = numSyntax.mk_leq (left, right)

(* This directory's suite tests the one carrier it can parse, so the
   shared normalisation helpers are fixed to it here. *)
val normalized_rhs = linarithCorpus.normalized_rhs num_instance
val canonical_form = linarithCorpus.canonical_form num_instance

val _ =
  check
    ("num norm_conv turns a contradictory leq into false",
     fn () =>
       Term.aconv
         (normalized_rhs
            (num_leq (num_plus num_x num_three)
              (num_plus num_x num_two)))
         boolSyntax.F)

val _ =
  check
    ("num norm_conv cancels a common summand",
     fn () =>
       Term.aconv
         (normalized_rhs
            (num_leq (num_plus num_x num_y)
              (num_plus num_y num_z)))
         (num_leq num_x num_z))

(* Cancellation runs once per Added node of every certificate, so it
   removes the whole common multiset of a relation rather than one
   summand per application: normalized_rhs applies norm_conv once, and
   what comes back has all three common summands gone. *)
val _ =
  check
    ("num norm_conv cancels three common summands in one application",
     fn () =>
       let
         val num_u = Term.mk_var ("linarith_num_u", numSyntax.num)
         val num_v = Term.mk_var ("linarith_num_v", numSyntax.num)
         fun sum terms = List.foldl (fn (t, acc) => num_plus acc t)
                           (hd terms) (tl terms)
         val relation =
           num_leq (sum [num_x, num_y, num_z, num_u])
             (sum [num_y, num_z, num_x, num_v])
       in
         Term.aconv (normalized_rhs relation) (num_leq num_u num_v)
       end)

val _ =
  check
    ("num cancellation preserves unmatched copies of repeated summands",
     fn () =>
       let
         val num_w = Term.mk_var ("linarith_num_w", numSyntax.num)
         (* The carrier's expression conversion combines repeated
            summands. Keep them separate to test multiset cancellation. *)
         val normalize =
           linarithCancel.mk_norm_conv
             {ac =
                {dest_less = numSyntax.dest_less,
                 dest_leq = numSyntax.dest_leq,
                 strip_plus = numSyntax.strip_plus,
                 mk_plus = numSyntax.mk_plus,
                 assoc = arithmeticTheory.ADD_ASSOC,
                 comm = arithmeticTheory.ADD_COMM,
                 rid = arithmeticTheory.ADD_0,
                 ac_fallback = SOME numSimps.ADDR_CANON_CONV},
              ty = numSyntax.num,
              leq_cancel = arithmeticTheory.LE_ADD_LCANCEL,
              less_cancel = arithmeticTheory.LT_ADD_LCANCEL,
              eq_cancel = arithmeticTheory.EQ_ADD_LCANCEL,
              expression_conv = Conv.ALL_CONV,
              reduce_conv = Conv.ALL_CONV,
              refl_thms = []}
         val left = num_plus num_x (num_plus num_y (num_plus num_x num_z))
         val right = num_plus num_y (num_plus num_x (num_plus num_y num_w))
         val theorem = normalize (num_leq left right)
         val expected = num_leq (num_plus num_x num_z) (num_plus num_y num_w)
       in
         Term.aconv (boolSyntax.rhs (Thm.concl theorem)) expected
       end)

val _ =
  check
    ("num norm_conv decides a ground relation",
     fn () =>
       Term.aconv
         (normalized_rhs (numSyntax.mk_less (num_seven, num_eight)))
         boolSyntax.T)

(* Replay normalizes the two sides of a derived relation, so norm_conv is
   offered bare expressions as well as relations.  It used to answer
   those by raising UNCHANGED out of the whole conversion, because
   relation_conv signalled "not a relation" that way and ORELSEC catches
   HOL_ERR only. *)
val _ =
  check
    ("num norm_conv canonicalizes a bare expression",
     fn () =>
       Term.aconv
         (canonical_form (num_plus num_three num_x))
         (canonical_form (num_plus num_x num_three)))

val _ =
  check
    ("num literals include SUC towers",
     fn () =>
       let
         val tower = numSyntax.mk_suc (numSyntax.mk_suc numSyntax.zero_tm)
         val dest_lit = #dest_lit (#dest num_instance)
       in
         dest_lit tower = Arbrat.two andalso
         Term.aconv (#mk_lit (#dest num_instance) Arbrat.two) num_two
       end)

val _ =
  check
    ("num divmod facts specialize DIVISION for a positive literal",
     fn () =>
       let
         val facts = #atom_facts num_instance
         val div_tm = numSyntax.mk_div (num_x, num_three)
         val mod_tm = numSyntax.mk_mod (num_x, num_three)
       in
         List.length (facts div_tm) = 2 andalso
         List.length (facts mod_tm) = 2 andalso
         List.length (facts (numSyntax.mk_div
           (num_x, numSyntax.zero_tm))) = 1
       end)

val num_decomp_relation =
  num_leq
    (num_plus (numSyntax.mk_mult (num_two, num_x)) num_three)
    (num_plus num_x num_y)

val _ =
  check
    ("decomp uses the locally registered num instance",
     fn () =>
       case linarithDecomp.decomp num_decomp_relation of
           SOME
             (Decomp
                {lhs, lhs_const, rel = REL_LE, rhs, rhs_const,
                 discrete = true, negated = false}) =>
               List.length lhs = 1 andalso List.length rhs = 2 andalso
               lhs_const = Arbrat.fromInt 3 andalso
               rhs_const = Arbrat.zero
         | _ => false)

val registry_ty = Type.mk_type ("fun", [Type.bool, Type.bool])

fun decline _ = raise Fail "synthetic linarith instance declined"

fun synthetic_instance discrete : linarithData.linarith_instance =
  {ty = registry_ty,
   discrete = discrete,
   dest =
     {dest_plus = decline,
      dest_minus = NONE,
      dest_neg = NONE,
      dest_mult = decline,
      dest_div = NONE,
      dest_suc = NONE,
      dest_lit = decline,
      mk_lit = decline,
      dest_less = decline,
      dest_leq = decline},
   kit =
     {add_mono = [],
      mult_mono = [],
      not_less = boolTheory.TRUTH,
      not_le = boolTheory.TRUTH,
      neqE = boolTheory.TRUTH,
      nonneg = (fn _ => NONE)},
   norm_conv = Conv.ALL_CONV,
   nnf_rules = [],
   pre_split = [],
   atom_facts = (fn _ => [])}

val _ = linarithData.register_instance (synthetic_instance NONE)
val _ =
  linarithData.register_instance
    (synthetic_instance (SOME {lessD = [boolTheory.TRUTH]}))

val _ =
  check
    ("instance registration replaces an existing same-type entry",
     fn () =>
       case linarithData.instance_for registry_ty of
           SOME instance => Option.isSome (#discrete instance)
         | NONE => false)

fun function_ty domain range = Type.mk_type ("fun", [domain, range])
fun binary_ty domain range =
  function_ty domain (function_ty domain range)

val synth_plus =
  Term.mk_var ("linarith_synth_plus", binary_ty registry_ty registry_ty)
val synth_minus =
  Term.mk_var ("linarith_synth_minus", binary_ty registry_ty registry_ty)
val synth_neg =
  Term.mk_var
    ("linarith_synth_neg", function_ty registry_ty registry_ty)
val synth_mult =
  Term.mk_var ("linarith_synth_mult", binary_ty registry_ty registry_ty)
val synth_div =
  Term.mk_var ("linarith_synth_div", binary_ty registry_ty registry_ty)
val synth_less =
  Term.mk_var ("linarith_synth_less", binary_ty registry_ty Type.bool)
val synth_leq =
  Term.mk_var ("linarith_synth_leq", binary_ty registry_ty Type.bool)
val synth_inj =
  Term.mk_var
    ("linarith_synth_inj", function_ty Type.bool registry_ty)

val synth_zero = Term.mk_var ("linarith_synth_zero", registry_ty)
val synth_one = Term.mk_var ("linarith_synth_one", registry_ty)
val synth_two = Term.mk_var ("linarith_synth_two", registry_ty)
val synth_x = Term.mk_var ("linarith_synth_x", registry_ty)
val synth_y = Term.mk_var ("linarith_synth_y", registry_ty)
val synth_z = Term.mk_var ("linarith_synth_z", registry_ty)
val synth_bool_atom =
  Term.mk_var ("linarith_synth_bool_atom", Type.bool)

fun mk_binary operator left right =
  Term.list_mk_comb (operator, [left, right])

fun dest_binary operator tm =
  let
    val (rator, right) = Term.dest_comb tm
    val (actual, left) = Term.dest_comb rator
  in
    if Term.aconv actual operator then (left, right) else decline tm
  end

fun dest_unary operator tm =
  let
    val (actual, arg) = Term.dest_comb tm
  in
    if Term.aconv actual operator then arg else decline tm
  end

fun synth_lit tm =
  if Term.aconv tm synth_zero then Arbrat.zero
  else if Term.aconv tm synth_one then Arbrat.one
  else if Term.aconv tm synth_two then Arbrat.two
  else decline tm

fun make_decomp_instance dest_minus :
    linarithData.linarith_instance =
  {ty = registry_ty,
   discrete = NONE,
   dest =
     {dest_plus = dest_binary synth_plus,
      dest_minus = dest_minus,
      dest_neg = SOME (dest_unary synth_neg),
      dest_mult = dest_binary synth_mult,
      dest_div = SOME (dest_binary synth_div),
      dest_suc = NONE,
      dest_lit = synth_lit,
      mk_lit = decline,
      dest_less = dest_binary synth_less,
      dest_leq = dest_binary synth_leq},
   kit =
     {add_mono = [],
      mult_mono = [],
      not_less = boolTheory.TRUTH,
      not_le = boolTheory.TRUTH,
      neqE = boolTheory.TRUTH,
      nonneg = (fn _ => NONE)},
   norm_conv = Conv.ALL_CONV,
   nnf_rules = [],
   pre_split = [],
   atom_facts = (fn _ => [])}

val decomp_instance =
  make_decomp_instance (SOME (dest_binary synth_minus))

val _ = linarithData.register_instance decomp_instance
val _ =
  linarithData.register_injection
    {from_ty = Type.bool,
     to_ty = registry_ty,
     inj = synth_inj,
     hom =
       {le = boolTheory.TRUTH,
        lt = boolTheory.TRUTH,
        eq = boolTheory.TRUTH,
        add = boolTheory.TRUTH,
        mul = boolTheory.TRUTH}}

fun coefficient atoms atom =
  case List.find (fn (tm, _) => Term.aconv tm atom) atoms of
      SOME (_, value) => value
    | NONE => Arbrat.zero

val synth_linear_lhs =
  mk_binary synth_plus
    (mk_binary synth_mult synth_two synth_x) synth_one
val synth_linear_rhs =
  mk_binary synth_plus synth_x synth_y
val synth_linear_relation =
  mk_binary synth_leq synth_linear_lhs synth_linear_rhs

val _ =
  check
    ("decomp uses synthetic plus, mult, literal, and atom destructors",
     fn () =>
       case linarithDecomp.decomp synth_linear_relation of
           SOME
             (Decomp
                {lhs, lhs_const, rel = REL_LE, rhs, rhs_const,
                 discrete = false, negated = false}) =>
               List.length lhs = 1 andalso List.length rhs = 2 andalso
               coefficient lhs synth_x = Arbrat.two andalso
               coefficient rhs synth_x = Arbrat.one andalso
               coefficient rhs synth_y = Arbrat.one andalso
               lhs_const = Arbrat.one andalso
               rhs_const = Arbrat.zero
         | _ => false)

val synth_signed_expression =
  mk_binary synth_minus
    (Term.mk_comb (synth_neg, synth_x)) synth_y
val synth_signed_relation =
  mk_binary synth_leq synth_signed_expression synth_zero
val synth_cancelled_relation =
  mk_binary synth_leq
    (mk_binary synth_plus synth_x
       (Term.mk_comb (synth_neg, synth_x))) synth_zero

val _ =
  check
    ("poly handles subtraction, negation, and coefficient cancellation",
     fn () =>
       (case linarithDecomp.decomp synth_signed_relation of
            SOME (Decomp {lhs, lhs_const, ...}) =>
              List.length lhs = 2 andalso
              coefficient lhs synth_x = Arbrat.negate Arbrat.one andalso
              coefficient lhs synth_y = Arbrat.negate Arbrat.one andalso
              lhs_const = Arbrat.zero
          | NONE => false) andalso
       (case linarithDecomp.decomp synth_cancelled_relation of
            SOME (Decomp {lhs, lhs_const, ...}) =>
              null lhs andalso lhs_const = Arbrat.zero
          | NONE => false))

val _ =
  check
    ("an atom that cancels and reappears takes a new column position",
     fn () =>
       let
         val plus = mk_binary synth_plus
         val lhs =
           plus synth_x
             (plus synth_y
                (plus synth_x (Term.mk_comb (synth_neg, synth_x))))
       in
         case linarithDecomp.decomp (mk_binary synth_leq lhs synth_zero) of
             SOME (Decomp {lhs = [(first, a), (second, b)], ...}) =>
               Term.aconv first synth_y andalso
               Term.aconv second synth_x andalso
               a = Arbrat.one andalso b = Arbrat.one
           | _ => false
       end)

val _ =
  linarithData.register_instance (make_decomp_instance NONE)

val _ =
  check
    ("poly keeps subtraction atomic when the instance declines it",
     fn () =>
       case linarithDecomp.decomp synth_signed_relation of
           SOME (Decomp {lhs, lhs_const, ...}) =>
             List.length lhs = 1 andalso
             coefficient lhs synth_signed_expression = Arbrat.one andalso
             lhs_const = Arbrat.zero
         | NONE => false)

val _ = linarithData.register_instance decomp_instance

val synth_left_product =
  mk_binary synth_mult
    (mk_binary synth_mult synth_x synth_y) synth_z
val synth_right_product =
  mk_binary synth_mult synth_x
    (mk_binary synth_mult synth_y synth_z)

val _ =
  check
    ("demult normalizes products to right-associated form",
     fn () =>
       case linarithDecomp.demult
              (synth_left_product, Arbrat.one) of
           (SOME atom, multiplier) =>
             Term.aconv atom synth_right_product andalso
             multiplier = Arbrat.one
         | _ => false)

val _ =
  check
    ("demult scales division only by a nonzero literal divisor",
     fn () =>
       let
         val literal_division =
           mk_binary synth_div synth_x synth_two
         val atom_division = mk_binary synth_div synth_x synth_y
         val zero_division = mk_binary synth_div synth_x synth_zero
         val division_relation =
           mk_binary synth_leq literal_division synth_zero
       in
         (case linarithDecomp.demult
                 (literal_division, Arbrat.one) of
              (SOME atom, multiplier) =>
                Term.aconv atom synth_x andalso
                multiplier = Arbrat./ (Arbrat.one, Arbrat.two)
            | _ => false) andalso
         (case linarithDecomp.demult (atom_division, Arbrat.one) of
              (SOME atom, multiplier) =>
                Term.aconv atom atom_division andalso
                multiplier = Arbrat.one
            | _ => false) andalso
         (case linarithDecomp.demult (zero_division, Arbrat.one) of
              (SOME atom, multiplier) =>
                Term.aconv atom zero_division andalso
                multiplier = Arbrat.one
            | _ => false) andalso
         (case linarithDecomp.decomp division_relation of
              SOME (Decomp {lhs, lhs_const, ...}) =>
                List.length lhs = 1 andalso
                coefficient lhs synth_x =
                  Arbrat./ (Arbrat.one, Arbrat.two) andalso
                lhs_const = Arbrat.zero
            | NONE => false)
       end)

(* poly reaches demult through one arm for products and quotients
   alike, and both halves of what that arm does are asked of a quotient
   here.  A quotient demult scales is handed back to poly, which goes on
   decomposing what came out of it; a quotient it leaves alone -- a
   non-literal divisor, or a zero one -- is an atom carrying the
   coefficient it arrived with, and it is the self-check for that case
   that stops the poly/demult recursion, bare or inside a product demult
   did take apart. *)
val _ =
  check
    ("poly decomposes a quotient through demult and stops where it must",
     fn () =>
       let
         val atom_division = mk_binary synth_div synth_x synth_y
         val zero_division = mk_binary synth_div synth_x synth_zero
         val scaled_atom_division =
           mk_binary synth_mult synth_two atom_division
         val sum_division =
           mk_binary synth_div
             (mk_binary synth_plus synth_x synth_y) synth_two
         val half = Arbrat./ (Arbrat.one, Arbrat.two)
         fun atoms_of expression =
           case linarithDecomp.decomp
                  (mk_binary synth_leq expression synth_zero) of
               SOME (Decomp {lhs, lhs_const, ...}) =>
                 if lhs_const = Arbrat.zero then SOME lhs else NONE
             | NONE => NONE
         fun single_atom expression atom value =
           case atoms_of expression of
               SOME lhs =>
                 List.length lhs = 1 andalso
                 coefficient lhs atom = value
             | NONE => false
       in
         single_atom atom_division atom_division Arbrat.one andalso
         single_atom zero_division zero_division Arbrat.one andalso
         single_atom scaled_atom_division atom_division Arbrat.two andalso
         (case atoms_of sum_division of
              SOME lhs =>
                List.length lhs = 2 andalso
                coefficient lhs synth_x = half andalso
                coefficient lhs synth_y = half
            | NONE => false)
       end)

val synth_injected = Term.mk_comb (synth_inj, synth_bool_atom)
val synth_injected_relation =
  mk_binary synth_leq synth_injected synth_zero
val synth_mixed_product =
  mk_binary synth_mult synth_injected synth_x
val synth_scaled_mixed_product =
  mk_binary synth_mult synth_injected
    (mk_binary synth_mult synth_x synth_two)

val _ =
  check
    ("poly and demult unwrap registered injections",
     fn () =>
       (case linarithDecomp.decomp synth_injected_relation of
            SOME (Decomp {lhs, lhs_const, ...}) =>
              List.length lhs = 1 andalso
              coefficient lhs synth_bool_atom = Arbrat.one andalso
              lhs_const = Arbrat.zero
          | NONE => false) andalso
       (case linarithDecomp.demult
               (mk_binary synth_mult synth_injected synth_two,
                Arbrat.one) of
            (SOME atom, multiplier) =>
              Term.aconv atom synth_bool_atom andalso
              multiplier = Arbrat.two
          | _ => false) andalso
       (case linarithDecomp.demult
               (synth_scaled_mixed_product, Arbrat.one) of
            (SOME atom, multiplier) =>
              Term.aconv atom synth_mixed_product andalso
              multiplier = Arbrat.two
          | _ => false))

val synth_negated_less =
  boolSyntax.mk_neg (mk_binary synth_less synth_x synth_y)
val synth_negated_leq =
  boolSyntax.mk_neg (mk_binary synth_leq synth_x synth_y)
val synth_negated_eq =
  boolSyntax.mk_neg (boolSyntax.mk_eq (synth_x, synth_y))

fun relation_flags tm =
  case linarithDecomp.decomp tm of
      SOME (Decomp {rel, negated, ...}) => SOME (rel, negated)
    | NONE => NONE

val _ =
  check
    ("decomp handles positive and negated synthetic relations",
     fn () =>
       relation_flags (mk_binary synth_less synth_x synth_y) =
         SOME (REL_LT, false) andalso
       relation_flags (boolSyntax.mk_eq (synth_x, synth_y)) =
         SOME (REL_EQ, false) andalso
       relation_flags synth_negated_less = SOME (REL_LT, true) andalso
       relation_flags synth_negated_leq = SOME (REL_LE, true) andalso
       relation_flags synth_negated_eq = SOME (REL_NEQ, false))

val _ =
  check
    ("unregistered relation carriers are declined",
     fn () =>
       case linarithDecomp.decomp
              (boolSyntax.mk_eq (synth_bool_atom, boolSyntax.T)) of
           NONE => true
         | SOME _ => false)

val _ =
  check
    ("is_relevant is exactly successful decomposition",
     fn () =>
       linarithDecomp.is_relevant synth_linear_relation andalso
       not (linarithDecomp.is_relevant synth_bool_atom))

val bad_split_name =
  {Thy = "bool", Name = "TRUTH"}

fun bad_split_rejected () =
  case ThmSetData.data_exportfns {settype = "arith_split"} of
      NONE => false
    | SOME export =>
        ((#add export
            {thy = "bool",
             named_thm = (bad_split_name, boolTheory.TRUTH)};
          false)
         handle Feedback.HOL_ERR error =>
           String.isSubstring
             "Malformed [arith_split] theorem bool$TRUTH"
             (Feedback.message_of error))

val _ =
  check
    ("arith_split rejects a named theorem outside the P-form",
     bad_split_rejected)

(* Fourier--Motzkin is reached the way replay reaches it: prove takes
   the hypotheses, a decomposition for each, and the conclusion whose
   negation joins them.  fm_refute states a system as the
   decompositions its rows are built from, so what the checks below
   pin is the certificate the engine derives and not the shape a row
   is held in.

   The conclusion here decomposes to nothing and so contributes no
   row, which leaves the hypothesis in position i as Asm i -- the
   numbering replay resolves against the caller's assumption list. *)
val fm_config : linarithData.linarith_config =
  {neq_limit = 9, split_limit = 9}

val fm_conclusion = Term.mk_var ("linarith_fm_conclusion", Type.bool)

fun fm_refute decomps =
  let
    val hypotheses =
      List.tabulate
        (List.length decomps,
         fn i =>
            Term.mk_var ("linarith_fm_" ^ Int.toString i, Type.bool))
    val table = ListPair.zip (hypotheses, decomps)
    fun decompose tm =
      case List.find (fn (hyp, _) => Term.aconv hyp tm) table of
          SOME (_, decomp) => decomp
        | NONE => NONE
  in
    case prove traceUtil.silent fm_config decompose (fn _ => false) hypotheses
                fm_conclusion of
        (_, SOME [just]) => SOME just
      | _ => NONE
  end

(* A premise as the decomposition a caller would hand prove for it. *)
fun fm_relation rel (lhs, lhs_const) (rhs, rhs_const) =
  Decomp {lhs = lhs, lhs_const = lhs_const, rel = rel, rhs = rhs,
          rhs_const = rhs_const, discrete = true, negated = false}

val fm_le = fm_relation REL_LE
val fm_eq = fm_relation REL_EQ

val fm_x = Term.mk_var ("linarith_fm_x", numSyntax.num)
val fm_z = Term.mk_var ("linarith_fm_z", numSyntax.num)

val fm_rat = Arbrat.fromInt
val no_atoms : (Term.term * Arbrat.rat) list = []
fun fm_scaled_x c = [(fm_x, fm_rat c)]

(* Two-column premises, k <= ax + bz and k = ax + bz.  Both atoms are
   named by every one of them, whatever their coefficients, so
   atoms_of_decomps gives x column 0 and z column 1 throughout and the
   pivot the checks below name is the pivot the system offers. *)
fun fm_columns (a, b) = [(fm_x, fm_rat a), (fm_z, fm_rat b)]

fun fm_row coeffs k = fm_le (no_atoms, fm_rat k) (fm_columns coeffs, fm_rat 0)

fun fm_equation coeffs k =
  fm_eq (no_atoms, fm_rat k) (fm_columns coeffs, fm_rat 0)

val fm_budget_items =
  [(Term.mk_var ("linarith_budget_first", Type.bool),
    SOME (fm_le (no_atoms, fm_rat 0)
            (fm_scaled_x 1, fm_rat 0))),
   (Term.mk_var ("linarith_budget_second", Type.bool),
    SOME (fm_le (no_atoms, fm_rat 1)
            (fm_scaled_x ~1, fm_rat 0)))]

fun fm_budgeted budget items =
  prove_decomposed_budgeted traceUtil.silent budget fm_config
    (fn _ => NONE) (fn _ => false) items fm_conclusion

val _ =
  check
    ("FM input keeps the first contradictory constant row",
     fn () =>
       let
         fun constant n = fm_le (no_atoms, fm_rat n) (no_atoms, fm_rat 0)
         val rows = [constant 0, fm_row (1, 0) 0, constant 1, constant 2]
         val items = map (fn row => (fm_conclusion, SOME row)) rows
         val visited = ref []
         fun nonnegative atom =
           (visited := atom :: !visited; Term.aconv atom fm_x)
       in
         case prove_decomposed traceUtil.silent fm_config (fn _ => NONE)
                nonnegative items fm_conclusion of
             (_, SOME [Asm 2]) =>
               Lib.list_eq Term.aconv (List.rev (!visited)) [fm_x, fm_z]
           | _ => false
       end)

val _ =
  check
    ("FM equation elimination keeps the first constant contradiction",
     fn () =>
       let
         val rows = map (SOME o fm_equation (1, 0)) [0, 0, 1, 2]
         val items =
           map
             (fn (i, row) =>
               (Term.mk_var ("fm_eq_" ^ Int.toString i, Type.bool), row))
             (Lib.enumerate 0 rows)
         fun first (Added (Asm 0, Multiplied (scale, Asm 2))) =
               scale = Arbint.~ Arbint.one
           | first _ = false
         val limited = searchBudget.create
           {candidates = NONE, applications = SOME 2, normalization = NONE}
       in
         Option.getOpt (Option.map first (fm_refute rows), false) andalso
         (case fm_budgeted (searchBudget.unbounded ()) items of
              CertificateFound {justifications = [just], ...} => first just
            | _ => false) andalso
         (case fm_budgeted limited items of
              CertificateLimitReached
                {kind = searchBudget.Application, usage} =>
                  #applications usage = 2
            | _ => false)
       end)

val _ =
  check
    ("FM budget distinguishes a certificate from exhaustion and limits",
     fn () =>
       let
         fun budget candidates applications normalization =
           searchBudget.create
             {candidates = candidates, applications = applications,
              normalization = normalization}
         val funded =
           fm_budgeted (searchBudget.unbounded ()) fm_budget_items
         val exhausted =
           fm_budgeted (searchBudget.unbounded ())
             [hd fm_budget_items]
         val candidate_cut =
           fm_budgeted (budget (SOME 0) NONE NONE) fm_budget_items
         val application_cut =
           fm_budgeted (budget NONE (SOME 0) NONE) fm_budget_items
         val normalization_cut =
           fm_budgeted (budget NONE NONE (SOME 0)) fm_budget_items
       in
         (case funded of
              CertificateFound
                {justifications = [Added (Asm 0, Asm 1)], ...} =>
                  true
            | _ => false) andalso
         (case exhausted of
              CertificateExhausted => true
            | _ => false) andalso
         (case candidate_cut of
              CertificateLimitReached
                {kind = searchBudget.Candidate, usage} =>
                  #candidates usage = 0
            | _ => false) andalso
         (case application_cut of
              CertificateLimitReached
                {kind = searchBudget.Application, usage} =>
                  #applications usage = 0 andalso
                  #candidates usage > 0
            | _ => false) andalso
         (case normalization_cut of
              CertificateLimitReached
                {kind = searchBudget.Normalization, usage} =>
                  #normalization usage = 0
            | _ => false)
       end)

val _ =
  check
    ("FM keeps the first certificate for duplicate derived rows",
     fn () =>
       let
         val width = 12
         (* The pivots tie, so x is eliminated first. Its derived
            copies of 0 <= z must retain the first justification. *)
         val positive = SOME (fm_row (1, 1) 0)
         val negative = SOME (fm_row (~1, 0) 0)
         val opposing = SOME (fm_row (0, ~1) 1)
         val rows =
           List.tabulate (width, fn _ => positive) @
           List.tabulate (width, fn _ => negative) @
           List.tabulate (width, fn _ => opposing)
         val items =
           ListPair.map
             (fn (i, row) =>
               (Term.mk_var ("fm_dup_" ^ Int.toString i, Type.bool), row))
             (List.tabulate (3 * width, Lib.I), rows)
         fun first (Added (Added (Asm 0, Asm second), Asm third)) =
               second = width andalso third = 2 * width
           | first _ = false
       in
         (case fm_refute rows of
              SOME just => first just
            | _ => false) andalso
         (case fm_budgeted (searchBudget.unbounded ()) items of
              CertificateFound {justifications = [just], ...} => first just
            | _ => false)
       end)

val _ =
  check
    ("FM charges each row pair inside a broad elimination round",
     fn () =>
       let
         fun row side index =
           (Term.mk_var
              ("fm_pair_" ^ side ^ "_" ^ Int.toString index,
               Type.bool),
            SOME
              (fm_le (no_atoms, fm_rat 0)
                (fm_scaled_x
                  (if side = "positive" then 1 else ~1),
                 fm_rat 0)))
         val items =
           List.tabulate (8, row "positive") @
           List.tabulate (8, row "negative")
         val limited =
           searchBudget.create
             {candidates = NONE, applications = SOME 5,
              normalization = NONE}
       in
         (case fm_budgeted limited items of
              CertificateLimitReached
                {kind = searchBudget.Application, usage} =>
                  #applications usage = 5 andalso
                  #candidates usage > 0
            | _ => false) andalso
         (case fm_budgeted (searchBudget.unbounded ()) items of
              CertificateExhausted => true
            | _ => false)
       end)

val _ =
  check
    ("FM keeps the first contradictory pair and preserves budget charges",
     fn () =>
       let
         val rows = map (fn (coeffs, k) => SOME (fm_row coeffs k))
           [((1, 0), 0), ((1, 0), 1), ((~1, 0), 0),
            ((~1, 0), 1), ((~1, 0), 2)]
         val items = ListPair.zip
           (List.tabulate
              (List.length rows,
               fn i => Term.mk_var ("fm_first_" ^ Int.toString i, Type.bool)),
            rows)
         val limited = searchBudget.create
           {candidates = NONE, applications = SOME 2, normalization = NONE}
       in
         (case fm_refute rows of
              SOME (Added (Asm 0, Asm 3)) => true
            | _ => false) andalso
         (case fm_budgeted (searchBudget.unbounded ()) items of
              CertificateFound
                {justifications = [Added (Asm 0, Asm 3)], ...} => true
            | _ => false) andalso
         (case fm_budgeted limited items of
              CertificateLimitReached
                {kind = searchBudget.Application, usage} =>
                  #applications usage = 2
            | _ => false)
       end)

val _ =
  check
    ("budgeted certificate search propagates an interrupt",
     fn () =>
       ((ignore
           (prove_budgeted traceUtil.silent (searchBudget.unbounded ())
             fm_config (fn _ => raise Portable.Interrupt) (fn _ => false)
             [] fm_conclusion);
         false)
        handle Portable.Interrupt => true))

(* Opposite coefficients of equal magnitude add directly to 1 <= 0. *)
val _ =
  check
    ("FM adds rows directly for equal pivot magnitudes",
     fn () =>
       List.all
         (fn coefficient =>
           case fm_refute
                  [SOME (fm_le (no_atoms, fm_rat 0)
                           (fm_scaled_x coefficient, fm_rat 0)),
                   SOME (fm_le (no_atoms, fm_rat 1)
                           (fm_scaled_x (~coefficient), fm_rat 0))] of
               SOME (Added (Asm 0, Asm 1)) => true
             | _ => false)
         [1, 2])

(* 0 <= 2x against 1 <= ~3x: eliminating x scales each row up to the
   two coefficients' lcm, and both multipliers reach the certificate,
   which is what replay scales the assumptions by. *)
val _ =
  check
    ("FM records integer scaling in the certificate",
     fn () =>
       case fm_refute
              [SOME (fm_le (no_atoms, fm_rat 0)
                       (fm_scaled_x 2, fm_rat 0)),
               SOME (fm_le (no_atoms, fm_rat 1)
                       (fm_scaled_x ~3, fm_rat 0))] of
           SOME (Added (Multiplied (m, Asm 0), Multiplied (n, Asm 1))) =>
             m = three andalso n = two
         | _ => false)

(* Which column a round eliminates is not reported anywhere, but the
   certificate it derives is, and a refutable system whose two columns
   are reached in either order derives a different one each way.  The
   three checks below are that: each states a system whose certificate
   is the pivot rule's, and would derive some other tree under any
   other rule.

   Equations first, on a coefficient of least magnitude.  0 = 5x + 2z
   with 1 <= x and 1 <= z clears z, the smaller of the equation's two
   coefficients, leaving 2 <= ~5x for 1 <= x to close, so the equation
   is scaled by ~1 and z's bound by 2.  Pivoting on x would scale them
   5 and 1 the other way about; and there is nothing here for the
   inequality rule to eliminate at all, every column being positive
   throughout, so a rule reaching for it first would report no
   refutation. *)
val _ =
  check
    ("equations take priority and use the smallest coefficient",
     fn () =>
       case fm_refute
              [SOME (fm_equation (5, 2) 0),
               SOME (fm_row (1, 0) 1),
               SOME (fm_row (0, 1) 1)] of
           SOME (Added (Multiplied (a, Asm 1),
                        Added (Multiplied (b, Asm 0),
                               Multiplied (c, Asm 2)))) =>
             a = Arbint.fromInt 5 andalso
             b = Arbint.fromInt ~1 andalso c = two
         | _ => false)

(* Equal magnitudes tie, and the entry met first scanning rows outer
   and columns inner wins.  The tie in 0 = 2x - 2z is inside one row:
   x is the earlier column, and clearing it leaves 2 <= 2z against
   0 <= ~z.  The tie between 0 = 3x - 2z and 0 = 2x + 3z is across
   rows, at column 1 of the first against column 0 of the second, and
   taking the first collapses the pair to 0 = 13x, which 1 <= x
   closes.  Either preference reversed pivots on the other entry and
   builds its certificate from the other row. *)
val _ =
  check
    ("an equation pivot tie goes to the first row-then-column entry",
     fn () =>
       (case fm_refute
               [SOME (fm_equation (2, ~2) 0),
                SOME (fm_row (1, 0) 1),
                SOME (fm_row (0, ~1) 0)] of
            SOME (Added (Added (Multiplied (a, Asm 0),
                                Multiplied (b, Asm 1)),
                         Multiplied (c, Asm 2))) =>
              a = Arbint.fromInt ~1 andalso b = two andalso c = two
          | _ => false) andalso
       (case fm_refute
               [SOME (fm_equation (3, ~2) 0),
                SOME (fm_equation (2, 3) 0),
                SOME (fm_row (1, 0) 1)] of
            SOME (Added (Multiplied (a, Added (Multiplied (b, Asm 0),
                                               Multiplied (c, Asm 1))),
                         Multiplied (d, Asm 2))) =>
              a = Arbint.fromInt ~1 andalso b = three andalso
              c = two andalso d = Arbint.fromInt 13
          | _ => false))

(* With no equation left the pivot is the column whose eliminations
   are fewest, one per positive-negative pair.  Column x of the four
   rows below is signed +, +, ~, ~ and so costs four; column z is
   signed + and ~ once each and costs one.  Taking z emits the single
   row 1 <= ~x, which 0 <= x closes in one further step, and the
   certificate is that pair of additions with nothing scaled.  Taking
   x emits four rows -- one of them trivial -- and reaches falsity a
   round later through the doubled 0 <= x + z, so maximising the
   product rather than minimising it is visible in the tree and not
   only in the time. *)
val _ =
  check
    ("inequality pivot minimizes Fourier-Motzkin blowup",
     fn () =>
       case fm_refute
              [SOME (fm_row (1, 1) 0),
               SOME (fm_row (1, 0) 0),
               SOME (fm_row (~2, ~1) 1),
               SOME (fm_row (~1, 0) 0)] of
           SOME (Added (Asm 1, Added (Asm 0, Asm 2))) => true
         | _ => false)

(* 0 <= 0 is trivial and says nothing, so a refutation has to come from
   the rows around it; 1 = 0 is trivial and contradictory by itself,
   and is reported against the premise it was built from. *)
val _ =
  check
    ("trivial rows are discarded and contradictory rows detected",
     fn () =>
       (case fm_refute
               [SOME (fm_le (no_atoms, fm_rat 0) (no_atoms, fm_rat 0)),
                SOME (fm_le (no_atoms, fm_rat 0)
                        (fm_scaled_x 1, fm_rat 0)),
                SOME (fm_le (no_atoms, fm_rat 1)
                        (fm_scaled_x ~1, fm_rat 0))] of
            SOME (Added (Asm 1, Asm 2)) => true
          | _ => false) andalso
       (case fm_refute
               [NONE, NONE,
                SOME (fm_eq (no_atoms, fm_rat 1) (no_atoms, fm_rat 0))] of
            SOME (Asm 2) => true
          | _ => false))

(* Discrete strengthening adds one to the assumption as it stands, and
   the scaling by the denominator lcm is applied outside it -- mklineq
   attaches it to the justification, and replay executes the two in that
   order -- so the constant the strengthening contributes to a row whose
   other constants are already scaled is that lcm, not one.  A row built
   with one instead is weaker by lcm - 1 than the theorem its own
   justification proves, and the system below is exactly that gap:
   x / 2 < 0 strengthens to 2 <= ~x, which ~x <= 1 contradicts, while
   the weaker 1 <= ~x does not.
   The trigger is a discrete carrier whose destructors take division
   apart, which no shipped instance is -- num and int decline division,
   real and rat are dense -- but which the registry admits, so it is
   registered here and taken back out again. *)
val discrete_decomp_instance =
  {ty = #ty decomp_instance,
   discrete = SOME {lessD = [boolTheory.TRUTH]},
   dest = #dest decomp_instance,
   kit = #kit decomp_instance,
   norm_conv = #norm_conv decomp_instance,
   nnf_rules = #nnf_rules decomp_instance,
   pre_split = #pre_split decomp_instance,
   atom_facts = #atom_facts decomp_instance} :
     linarithData.linarith_instance

val synth_halved_negative =
  mk_binary synth_less (mk_binary synth_div synth_x synth_two) synth_zero
val synth_negated_x_bounded =
  mk_binary synth_leq (Term.mk_comb (synth_neg, synth_x)) synth_one

val _ =
  check
    ("discrete strengthening scales by the denominator lcm",
     fn () =>
       let
         val _ = linarithData.register_instance discrete_decomp_instance
         val result =
           Lib.total
             (fn () =>
                prove traceUtil.silent fm_config linarithDecomp.decomp
                  (fn _ => false)
                  [synth_halved_negative, synth_negated_x_bounded]
                  fm_conclusion) ()
         val _ = linarithData.register_instance decomp_instance
       in
         case result of
             SOME (_, SOME [Added (Asm 1,
                                   Multiplied (m, LessD (Asm 0)))]) =>
               m = two
           | _ => false
       end)

(* Elimination that runs out of eliminable columns reports no
   certificate rather than raising, which is how a satisfiable system
   reaches the caller. *)
val _ =
  check
    ("a satisfiable system yields no certificate",
     fn () =>
       case fm_refute
              [SOME (fm_le (no_atoms, fm_rat 0)
                       (fm_scaled_x 1, fm_rat 0))] of
           NONE => true
         | _ => false)

val huge =
  Arbint.fromString "100000000000000000000000000000000000003"
val tiny = Arbrat./ (Arbrat.one, Arbrat.fromAInt huge)

(* A coefficient whose denominator exceeds any machine word is cleared
   by scaling the whole row by that denominator, and the multiplier
   reaches the certificate, where replay owes the assumption exactly
   it. *)
val _ =
  check
    ("row building clears an arbitrary-precision denominator",
     fn () =>
       case fm_refute
              [SOME (fm_le ([(fm_x, tiny)], fm_rat 0)
                       (no_atoms, fm_rat 0)),
               SOME (fm_le (no_atoms, fm_rat 1)
                       (fm_scaled_x 1, fm_rat 0))] of
           SOME (Added (Asm 1, Multiplied (m, Asm 0))) => m = huge
         | _ => false)

(* Rows are built by scattering each side into the columns of one
   shared atom index, so an atom occurring on both sides of a relation
   and again in another premise has to land in the same column
   throughout: 5z + x <= 2z, 1 <= x and 0 <= z is refutable only if it
   does, and only with all three rows.  atoms_of_decomps fixes that
   column order, and replay reads the same ordering. *)
val scattered =
  fm_le ([(fm_z, fm_rat 5), (fm_x, fm_rat 1)], fm_rat 0)
    ([(fm_z, fm_rat 2)], fm_rat 0)

fun rests_on just index =
  let
    fun collect (Asm i) = i = index
      | collect (Nonneg _) = false
      | collect (LessD inner) = collect inner
      | collect (NotLessD inner) = collect inner
      | collect (NotLeD inner) = collect inner
      | collect (NotLeDD inner) = collect inner
      | collect (Multiplied (_, inner)) = collect inner
      | collect (Added (left, right)) =
          collect left orelse collect right
  in
    collect just
  end

val _ =
  check
    ("rows scatter each side into its atom's column",
     fn () =>
       Lib.list_eq Term.aconv (atoms_of_decomps [scattered])
         [fm_z, fm_x] andalso
       (case fm_refute
               [SOME scattered,
                SOME (fm_le (no_atoms, fm_rat 1)
                        (fm_scaled_x 1, fm_rat 0)),
                SOME (fm_le (no_atoms, fm_rat 0)
                        ([(fm_z, fm_rat 1)], fm_rat 0))] of
            SOME just => List.all (rests_on just) [0, 1, 2]
          | NONE => false))

val _ =
  check
    ("alpha-equivalent atoms share one column across premises",
     fn () =>
       let
         val left = ``(f : (num -> num) -> num) (\x. x)``
         val right = ``(f : (num -> num) -> num) (\y. y)``
         val one = numSyntax.mk_numeral Arbnum.one
         val assumptions = [num_leq num_two left, num_leq right one]
         val goal = (assumptions, boolSyntax.F)
         val (remaining, validate) =
           Tactical.VALID (linarithLib.SIMPLE_LINARITH_TAC []) goal
             (Context.snapshot ())
       in
         null remaining andalso
         Term.aconv (Thm.concl (validate [])) boolSyntax.F
       end)

val _ =
  check
    ("row construction keeps the first coefficient on each side",
     fn () =>
       let
         val negative =
           fm_le ([(fm_x, fm_rat 2), (fm_x, fm_rat 1)], fm_rat 0)
             ([(fm_x, fm_rat 1), (fm_x, fm_rat 3)], fm_rat 0)
         val positive =
           fm_le (no_atoms, fm_rat 1) (fm_scaled_x 1, fm_rat 0)
         val rows = [SOME negative, SOME positive]
         val items = ListPair.zip ([boolSyntax.T, boolSyntax.F], rows)
       in
         (case fm_refute rows of
              SOME (Added (Asm 1, Asm 0)) => true
            | _ => false) andalso
         (case fm_budgeted (searchBudget.unbounded ()) items of
              CertificateFound
                {justifications = [Added (Asm 1, Asm 0)], ...} => true
            | _ => false)
       end)

fun const_decomp lhs rel discrete =
  Decomp {
    lhs = [], lhs_const = Arbrat.fromInt lhs,
    rel = rel, rhs = [], rhs_const = Arbrat.zero,
    discrete = discrete, negated = false
  }

val dense_neq_tm =
  Term.mk_var ("linarith_unit_dense_neq", Type.bool)
val discrete_neq_tm =
  Term.mk_var ("linarith_unit_discrete_neq", Type.bool)
val contradiction_tm =
  Term.mk_var ("linarith_unit_contradiction", Type.bool)
val conclusion_tm =
  Term.mk_var ("linarith_unit_conclusion", Type.bool)

val dense_neq = const_decomp 1 REL_NEQ false
val discrete_neq = const_decomp 2 REL_NEQ true
val contradiction = const_decomp 1 REL_LE true

fun unit_decomp tm =
  if Term.aconv tm dense_neq_tm then SOME dense_neq
  else if Term.aconv tm discrete_neq_tm then SOME discrete_neq
  else if Term.aconv tm contradiction_tm then SOME contradiction
  else NONE

(* Splitting a disequality moves its premise to the end of the case it
   generates, so the premises before it move up and the Asm indices of
   the case are the positions in that new order -- which is the order
   replay puts the goal's assumptions in.  Here the contradiction is
   the one premise that survives both splits, so every case is refuted
   by its first premise, and a case that kept the caller's original
   numbering would blame the second instead.  Two disequalities give
   one case per assignment, each with its own justification. *)
val _ =
  check
    ("split premises are renumbered for the case they end up in",
     fn () =>
       case prove traceUtil.silent {neq_limit = 2, split_limit = 9} unit_decomp
                  (fn _ => false)
                  [dense_neq_tm, contradiction_tm, discrete_neq_tm]
                  conclusion_tm of
           (true, SOME justs) =>
             List.length justs = 4 andalso
             List.all
               (fn Asm 0 => true | _ => false) justs
         | _ => false)

val _ =
  check
    ("prove splits at the neq_limit boundary",
     fn () =>
       case prove traceUtil.silent {neq_limit = 1, split_limit = 9} unit_decomp
                  (fn _ => false)
                  [dense_neq_tm, contradiction_tm] conclusion_tm of
           (true, SOME justs) => List.length justs = 2
         | _ => false)

val _ =
  check
    ("prove ignores all disequalities when neq_limit is exceeded",
     fn () =>
       case prove traceUtil.silent {neq_limit = 0, split_limit = 9} unit_decomp
                  (fn _ => false)
                  [dense_neq_tm, contradiction_tm] conclusion_tm of
           (false, SOME [_]) => true
         | _ => false)

val negated_conclusion_tm = boolSyntax.mk_neg conclusion_tm

fun from_negated_conclusion tm =
  if Term.aconv tm negated_conclusion_tm then SOME contradiction
  else NONE

fun from_unwrapped_conclusion tm =
  if Term.aconv tm conclusion_tm then SOME contradiction else NONE

val _ =
  check
    ("prove appends the negated conclusion with its assumption index",
     fn () =>
       case prove traceUtil.silent {neq_limit = 9, split_limit = 9}
                  from_negated_conclusion (fn _ => false) []
                  conclusion_tm of
           (true, SOME [Asm 0]) => true
         | _ => false)

val _ =
  check
    ("prove avoids double negation of an already-negated conclusion",
     fn () =>
       case prove traceUtil.silent {neq_limit = 9, split_limit = 9}
                  from_unwrapped_conclusion (fn _ => false) []
                  negated_conclusion_tm of
           (true, SOME [Asm 0]) => true
         | _ => false)

(* Golden kernel-replay tests.  These construct certificates directly so
   every replay constructor and every currently shipped num kit slot is
   exercised independently of Fourier--Motzkin search. *)

fun num_less left right = numSyntax.mk_less (left, right)
fun num_eq left right = boolSyntax.mk_eq (left, right)
fun num_not tm = boolSyntax.mk_neg tm

val num_zero = numSyntax.zero_tm
val num_one = numSyntax.mk_numeral Arbnum.one

fun replay terms justification =
  linarithReplay.mkthm traceUtil.silent (List.map Thm.ASSUME terms)
    justification

fun replay_is_false terms justification =
  Term.aconv (Thm.concl (replay terms justification)) boolSyntax.F

val _ =
  check
    ("replay golden: Asm",
     fn () => replay_is_false [num_leq num_one num_zero] (Asm 0))

val _ =
  check
    ("replay a shared certificate with the same hypotheses as traced replay",
     fn () =>
       let
         val less = LessD (Asm 0)
         val pair = Added (less, less)
         val certificate = Added (Added (pair, pair), Asm 1)
         val twice = num_plus num_x num_x
         val four = numSyntax.mk_numeral (Arbnum.fromInt 4)
         val premises = List.map Thm.ASSUME
           [num_less num_x num_one, num_leq four (num_plus twice twice)]
         val ordinary = linarithReplay.mkthm traceUtil.silent premises
           certificate
         val tracer = linarithData.tracer
         val level = traceUtil.level_of tracer
           (HOLFlags.set_flagC (traceUtil.flag tracer, 1) (Context.snapshot ()))
         val traced = linarithReplay.mkthm level premises certificate
       in
         Term.aconv (Thm.concl ordinary) boolSyntax.F andalso
         Term.aconv (Thm.concl ordinary) (Thm.concl traced) andalso
         HOLset.equal (Thm.hypset ordinary, Thm.hypset traced)
       end)

val _ =
  check
    ("replay rejects a certificate that does not derive false",
     fn () =>
       ((ignore (replay [num_leq num_x num_x] (Asm 0)); false)
        handle Feedback.HOL_ERR error =>
          Feedback.message_of error =
            "Linear arithmetic should have refuted the assumptions " ^
            "but failed to."))

val _ =
  check
    ("replay golden: Nonneg",
     fn () =>
       replay_is_false
         [num_leq (num_plus num_x num_three) num_two]
         (Added (Nonneg num_x, Asm 0)))

val _ =
  check
    ("replay rejects a Nonneg atom the instance declines",
     fn () =>
       ((ignore (replay [num_leq num_one num_zero] (Nonneg synth_x));
         false)
        handle Feedback.HOL_ERR error =>
          Feedback.message_of error =
            "instance declined nonnegative atom " ^
            Parse.term_to_string synth_x))

val _ =
  check
    ("replay golden: LessD",
     fn () => replay_is_false [num_less num_zero num_zero]
                              (LessD (Asm 0)))

val _ =
  check
    ("replay golden: NotLessD",
     fn () => replay_is_false [num_not (num_less num_zero num_one)]
                              (NotLessD (Asm 0)))

val _ =
  check
    ("replay golden: NotLeD",
     fn () => replay_is_false [num_not (num_leq num_zero num_zero)]
                              (NotLeD (Asm 0)))

val _ =
  check
    ("replay golden: NotLeDD",
     fn () => replay_is_false [num_not (num_leq num_zero num_zero)]
                              (NotLeDD (Asm 0)))

fun add_replay relation1 relation2 =
  replay_is_false
    [relation1 (num_plus num_x num_three)
       (num_plus num_y num_two),
     relation2 num_y num_x]
    (Added (Asm 0, Asm 1))

val _ =
  check
    ("replay golden: Added with le/le add_mono",
     fn () => add_replay num_leq num_leq)

val _ =
  check
    ("replay golden: Added with lt/lt add_mono",
     fn () => add_replay num_less num_less)

val _ =
  check
    ("replay golden: Added with le/lt add_mono",
     fn () => add_replay num_leq num_less)

val _ =
  check
    ("replay golden: Added with lt/le add_mono",
     fn () => add_replay num_less num_leq)

val _ =
  check
    ("replay golden: Multiplied with le mult_mono",
     fn () =>
       replay_is_false [num_leq num_one num_zero]
         (Multiplied (two, Asm 0)))

val _ =
  check
    ("replay golden: Multiplied with positive-premise lt mult_mono",
     fn () =>
       replay_is_false
         [num_less (num_plus num_x num_three)
            (num_plus num_x num_two)]
         (Multiplied (two, Asm 0)))

fun num_instance_with_mult_mono mult_mono =
  let
    val dest = #dest num_instance
    val kit = #kit num_instance
  in
    {ty = #ty num_instance,
     discrete = #discrete num_instance,
     dest = dest,
     kit =
       {add_mono = #add_mono kit,
        mult_mono = mult_mono,
        not_less = #not_less kit,
        not_le = #not_le kit,
        neqE = #neqE kit,
        nonneg = #nonneg kit},
     norm_conv = #norm_conv num_instance,
     nnf_rules = #nnf_rules num_instance,
     pre_split = #pre_split num_instance,
     atom_facts = #atom_facts num_instance} :
      linarithData.linarith_instance
  end

(* Iterated addition builds the multiple by doubling, so a multiplier
   with a set bit above the least significant one -- 12 is 1100, 11 is
   1011 -- exercises more than one arm of the recursion.  The scaled row
   here cancels only against the exact multiple, so a dropped bit is a
   failed replay rather than a differently shaped route to the same
   falsity. *)
val _ =
  check
    ("replay golden: Multiplied falls back to iterated addition",
     fn () =>
       let
         val _ =
           linarithData.register_instance
             (num_instance_with_mult_mono [])
         fun exact n =
           let
             val literal = numSyntax.mk_numeral (Arbnum.fromInt n)
             fun scale tm = numSyntax.mk_mult (literal, tm)
           in
             replay_is_false
               [num_leq (num_plus (scale num_x) num_one) (scale num_y),
                num_leq num_y num_x]
               (Added (Asm 0, Multiplied (Arbint.fromInt n, Asm 1)))
           end
           handle Feedback.HOL_ERR _ => false
         val result =
           replay_is_false [num_less num_zero num_zero]
             (Multiplied (two, Asm 0)) andalso
           List.all exact [2, 11, 12]
         val _ = linarithData.register_instance num_instance
       in
         result
       end)

val _ =
  check
    ("replay scales equality with AP_TERM and no mult_mono lemma",
     fn () =>
       let
         val _ =
           linarithData.register_instance
             (num_instance_with_mult_mono [])
         val result =
           replay_is_false [num_eq num_one num_zero]
             (Multiplied (two, Asm 0))
         val _ = linarithData.register_instance num_instance
       in
         result
       end)

val _ =
  check
    ("replay scales equality by a negative multiplier",
     fn () =>
       replay_is_false [num_eq num_one num_zero]
         (Multiplied (Arbint.~ two, Asm 0)))

(* The injection add-fallback -- summing two assumptions stated in
   different carriers, which mkthm can only do by lifting one of them
   through the conversion closure -- is pinned in instances/, by the
   golden "Added replay sums two carriers through the injection" and by
   the "mixed ... replay uses the registered injection" tactic checks
   that reach it from the surface.  It cannot be pinned here: this
   directory's Holmakefile has no integer, real or rational includes,
   and the one injection it registers is decomposition-only, its
   placeholder hom theorems not being valid replay rules. *)

val split_x = Term.mk_var ("linarith_split_x", numSyntax.num)
val split_y = Term.mk_var ("linarith_split_y", numSyntax.num)
val split_x_neq_one = num_not (num_eq split_x num_one)
val split_y_neq_one = num_not (num_eq split_y num_one)
val split_x_upper = num_leq split_x num_one
val split_x_lower = num_leq num_one split_x
val split_y_upper = num_leq split_y num_one
val split_y_lower = num_leq num_one split_y
val split_conclusion = num_leq split_x num_one

val one_split_config : linarithData.linarith_config =
  {neq_limit = 1, split_limit = 9}
val two_split_config : linarithData.linarith_config =
  {neq_limit = 2, split_limit = 9}

fun forward_with disequalities =
  linarithReplay.fwd_prove_in (Context.snapshot ()) two_split_config
    (List.map Thm.ASSUME
      (disequalities @
        [split_x_upper, split_x_lower,
         split_y_upper, split_y_lower]))
    split_conclusion

fun tactic_replay_succeeds config assumptions conclusion =
  (case linarithReplay.refute traceUtil.silent config assumptions conclusion of
       NONE => false
     | SOME tactic =>
         null
           (#1
              (Tactical.VALID tactic (assumptions, conclusion)
                (Context.snapshot()))))
  handle Feedback.HOL_ERR _ => false

val _ =
  check
    ("sparse replay validates unused premises and retains only its support",
     fn () =>
       let
         val ctxt = Context.snapshot ()
         val unused = Term.mk_var ("unused_replay_premise", Type.bool)
         val assumptions = [split_x_upper, unused]
         val tactic =
           valOf (linarithReplay.refute traceUtil.silent one_split_config
             assumptions split_conclusion)
         val theorem =
           case Tactical.VALID tactic (assumptions, split_conclusion) ctxt of
               ([], validate) => validate []
             | _ => raise Fail "expected the certificate to close the goal"
         fun error work =
           (work (); NONE)
           handle Feedback.HOL_ERR err => SOME (Feedback.message_of err)
         val expected = error (fn () => ignore (Thm.ASSUME num_one))
         val actual =
           error (fn () => ignore
             (tactic ([split_x_upper, num_one], split_conclusion) ctxt))
       in
         (case Thm.hyp theorem of
              [hyp] => Term.aconv hyp split_x_upper
            | _ => false) andalso
         Option.isSome expected andalso actual = expected
       end)

val _ =
  check
    ("forward replay proves a num consequence with one neq split",
     fn () =>
       let
         val theorem =
           linarithReplay.fwd_prove_in (Context.snapshot ()) one_split_config
             (List.map Thm.ASSUME
               [split_x_neq_one, split_x_upper, split_x_lower])
             split_conclusion
       in
         Term.aconv (Thm.concl theorem) split_conclusion andalso
         List.exists (Term.aconv split_x_neq_one) (Thm.hyp theorem)
       end)

val _ =
  check
    ("budgeted forward proof waits for kernel replay",
     fn () =>
       let
         val fact = Thm.ASSUME split_x_upper
         val search_only = searchBudget.unbounded ()
         val certificate =
           prove_budgeted traceUtil.silent search_only one_split_config
             linarithDecomp.decomp linarithDecomp.is_nonnegative
             [split_x_upper] split_conclusion
         val search_normalization =
           #normalization (searchBudget.usage search_only)
         val replay_limited =
           searchBudget.create
             {candidates = NONE, applications = NONE,
              normalization = SOME search_normalization}
         val cutoff =
           linarithReplay.fwd_prove_budgeted_in (Context.snapshot ())
             replay_limited
             one_split_config [fact] split_conclusion
         val funded = searchBudget.unbounded ()
         val proved =
           linarithReplay.fwd_prove_budgeted_in (Context.snapshot ()) funded
             one_split_config [fact] split_conclusion
         val first_usage = searchBudget.usage funded
         val proved_again =
           linarithReplay.fwd_prove_budgeted_in (Context.snapshot ()) funded
             one_split_config [fact] split_conclusion
         val second_usage = searchBudget.usage funded
         val exhausted =
           linarithReplay.fwd_prove_budgeted_in (Context.snapshot ())
             (searchBudget.unbounded ()) one_split_config []
             split_conclusion
       in
         (case certificate of
              CertificateFound _ => true
            | _ => false) andalso
         (case cutoff of
              linarithReplay.ReplayLimitReached
                {kind = searchBudget.Normalization, usage} =>
                  #normalization usage = search_normalization
            | _ => false) andalso
         (case proved of
              linarithReplay.ReplayProved theorem =>
                Term.aconv (Thm.concl theorem) split_conclusion andalso
                List.exists (Term.aconv split_x_upper)
                  (Thm.hyp theorem) andalso
                #normalization first_usage >
                  search_normalization
            | _ => false) andalso
         (case proved_again of
              linarithReplay.ReplayProved _ =>
                #candidates second_usage =
                  2 * #candidates first_usage andalso
                #applications second_usage =
                  2 * #applications first_usage andalso
                #normalization second_usage =
                  2 * #normalization first_usage
            | _ => false) andalso
         (case exhausted of
              linarithReplay.ReplayExhausted => true
            | _ => false)
       end)

val _ =
  check
    ("forward replay handles nested neq splits at the configured limit",
     fn () =>
       let
         val theorem =
           forward_with [split_x_neq_one, split_y_neq_one]
       in
         Term.aconv (Thm.concl theorem) split_conclusion
       end)

val _ =
  check
    ("permuting num neq premises preserves both replay styles",
     fn () =>
       let
         val orders =
           [[split_x_neq_one, split_y_neq_one],
            [split_y_neq_one, split_x_neq_one]]
         fun forward_succeeds assumptions =
           Term.aconv (Thm.concl (forward_with assumptions))
             split_conclusion
         fun tactic_succeeds assumptions =
           tactic_replay_succeeds two_split_config
             (assumptions @
               [split_x_upper, split_x_lower,
                split_y_upper, split_y_lower])
             split_conclusion
       in
         List.all forward_succeeds orders andalso
         List.all tactic_succeeds orders
       end)

val _ =
  check
    ("tactic replay closes an explicit neq goal through Tactical.VALID",
     fn () =>
       tactic_replay_succeeds one_split_config
         [split_x_neq_one, split_x_upper, split_x_lower]
         split_conclusion)

(* The disequality is neither first nor last, so splitting it moves it
   past a premise the certificate then has to name one position
   earlier.  Both replay styles resolve the certificate against the
   assumptions themselves, so a case numbered as the caller wrote it
   rather than as the split left it picks the wrong assumption here and
   derives nothing. *)
val moved_neq_assumptions =
  [split_x_upper, split_x_neq_one, split_y_upper]
val moved_neq_conclusion = num_less split_x num_one

val _ =
  check
    ("a disequality split past a premise still names the right one",
     fn () =>
       let
         val theorem =
           linarithReplay.fwd_prove_in (Context.snapshot ()) one_split_config
             (List.map Thm.ASSUME moved_neq_assumptions)
             moved_neq_conclusion
       in
         Term.aconv (Thm.concl theorem) moved_neq_conclusion andalso
         tactic_replay_succeeds one_split_config moved_neq_assumptions
           moved_neq_conclusion
       end)

(* Which disequalities replay splits has to be the test the search
   split them by, since the search emits one justification per case it
   generated and replay owes each of them a goal.  Answering "not this
   one" where the search said otherwise leaves refute_tac's THENL with
   more tactics than goals, and the arity mismatch is the whole of what
   the user then sees.  So an instance whose neqE does not apply to a
   disequality that passed the test is ill-formed, and is named. *)
fun num_instance_with_neqE neqE =
  let
    val kit = #kit num_instance
  in
    {ty = #ty num_instance,
     discrete = #discrete num_instance,
     dest = #dest num_instance,
     kit =
       {add_mono = #add_mono kit,
        mult_mono = #mult_mono kit,
        not_less = #not_less kit,
        not_le = #not_le kit,
        neqE = neqE,
        nonneg = #nonneg kit},
     norm_conv = #norm_conv num_instance,
     nnf_rules = #nnf_rules num_instance,
     pre_split = #pre_split num_instance,
     atom_facts = #atom_facts num_instance} :
      linarithData.linarith_instance
  end

val _ =
  check
    ("a reused replay tactic reads the current neqE",
     fn () =>
       let
         val assumptions = [split_x_neq_one, split_x_upper, split_x_lower]
         val tactic =
           valOf (linarithReplay.refute traceUtil.silent one_split_config
                    assumptions split_conclusion)
         fun replay () =
           Tactical.VALID tactic (assumptions, split_conclusion)
             (Context.snapshot ())
         val initially_closed = null (#1 (replay ()))
         val _ =
           linarithData.register_instance
             (num_instance_with_neqE boolTheory.TRUTH)
         val failure =
           (ignore (replay ()); NONE)
           handle Feedback.HOL_ERR error =>
                    SOME (Feedback.top_function_of error)
                | e =>
                    (linarithData.register_instance num_instance; raise e)
         val _ = linarithData.register_instance num_instance
       in
         initially_closed andalso failure = SOME "split_assumption" andalso
         null (#1 (replay ()))
       end)

(* Public no-preprocessing surface. *)

val public_x = Term.mk_var ("linarith_public_x", numSyntax.num)
val public_y = Term.mk_var ("linarith_public_y", numSyntax.num)
val public_z = Term.mk_var ("linarith_public_z", numSyntax.num)
val public_x_le_y = num_leq public_x public_y
val public_y_le_z = num_leq public_y public_z
val public_x_le_z = num_leq public_x public_z

val forward_tm =
  boolSyntax.list_mk_forall
    ([public_x, public_y, public_z],
     boolSyntax.mk_imp
       (boolSyntax.mk_conj (public_x_le_y, public_y_le_z),
        public_x_le_z))

val _ =
  check
    ("num norm_conv refutes a successor self-bound",
     fn () =>
       Term.aconv
         (normalized_rhs
           (num_leq (num_plus public_z num_one) public_z))
         boolSyntax.F)

val _ =
  check
    ("LINARITH_PROVE strips universals and atomizes conjunctive premises",
     fn () =>
       let val theorem = linarithLib.LINARITH_PROVE forward_tm
       in
         null (Thm.hyp theorem) andalso
         Term.aconv (Thm.concl theorem) forward_tm
       end)

val _ =
  check
    ("budgeted LINARITH_PROVE reports proof exhaustion and work limits",
     fn () =>
       let
         val funded = searchBudget.unbounded ()
         val proved =
           linarithLib.LINARITH_PROVE_BUDGETED_IN (Context.snapshot ())
             funded forward_tm
         val first_usage = searchBudget.usage funded
         val proved_again =
           linarithLib.LINARITH_PROVE_BUDGETED_IN (Context.snapshot ())
             funded forward_tm
         val second_usage = searchBudget.usage funded
         fun bounded candidates applications normalization =
           searchBudget.create
             {candidates = candidates, applications = applications,
              normalization = normalization}
         val candidate_cut =
           linarithLib.LINARITH_PROVE_BUDGETED_IN (Context.snapshot ())
             (bounded (SOME 0) NONE NONE) forward_tm
         val application_cut =
           linarithLib.LINARITH_PROVE_BUDGETED_IN (Context.snapshot ())
             (bounded NONE (SOME 0) NONE) forward_tm
         val normalization_cut =
           linarithLib.LINARITH_PROVE_BUDGETED_IN (Context.snapshot ())
             (bounded NONE NONE (SOME 0)) forward_tm
         val exhausted =
           linarithLib.LINARITH_PROVE_BUDGETED_IN (Context.snapshot ())
             (searchBudget.unbounded ())
             (Term.mk_var ("linarith_budget_unproved", Type.bool))
       in
         (case proved of
              linarithLib.LinarithProved theorem =>
                null (Thm.hyp theorem) andalso
                Term.aconv (Thm.concl theorem) forward_tm
            | _ => false) andalso
         (case proved_again of
              linarithLib.LinarithProved _ =>
                #candidates second_usage =
                  2 * #candidates first_usage andalso
                #applications second_usage =
                  2 * #applications first_usage andalso
                #normalization second_usage =
                  2 * #normalization first_usage
            | _ => false) andalso
         (case candidate_cut of
              linarithLib.LinarithLimitReached
                {kind = searchBudget.Candidate, usage} =>
                  #candidates usage = 0
            | _ => false) andalso
         (case application_cut of
              linarithLib.LinarithLimitReached
                {kind = searchBudget.Application, usage} =>
                  #applications usage = 0
            | _ => false) andalso
         (case normalization_cut of
              linarithLib.LinarithLimitReached
                {kind = searchBudget.Normalization, usage} =>
                  #normalization usage = 0
            | _ => false) andalso
         (case exhausted of
              linarithLib.LinarithExhausted => true
            | _ => false)
       end)

val budgeted_tactic_goal : Abbrev.goal =
  ([public_x_le_y, public_y_le_z], public_x_le_z)

val _ =
  check
    ("budgeted LINARITH_TAC charges its caller through full search",
     fn () =>
       let
         val funded = searchBudget.unbounded ()
         val closed =
           valid_closes
             (linarithLib.LINARITH_TAC_BUDGETED funded [])
             budgeted_tactic_goal
         val used = searchBudget.usage funded
         val insertion_budget =
           searchBudget.create
             {candidates = SOME 0, applications = SOME 0,
              normalization = NONE}
         val schematic_fact =
           Thm.REFL ``(linarith_budget_fact_value : 'a)``
         val insertion_cut =
           (ignore
              (Tactical.VALID
                 (linarithLib.LINARITH_TAC_BUDGETED
                    insertion_budget [schematic_fact])
                 budgeted_tactic_goal (Context.snapshot ()));
            false)
           handle searchBudget.LimitReached
                    (searchBudget.Candidate, usage) =>
                    #applications usage = 0
                | _ => false
         fun cut kind limits =
           let
             val budget = searchBudget.create limits
             val tactic =
               linarithLib.CFG_LINARITH_TAC_BUDGETED budget
                 linarithLib.default_config []
           in
             (ignore
                (Tactical.VALID tactic budgeted_tactic_goal
                   (Context.snapshot ()));
              false)
             handle searchBudget.LimitReached (actual, usage) =>
               actual = kind andalso usage = searchBudget.usage budget
           end
       in
         closed andalso #candidates used > 0 andalso
         #applications used > 0 andalso #normalization used > 0 andalso
         insertion_cut andalso
         cut searchBudget.Candidate
           {candidates = SOME 0, applications = NONE,
            normalization = NONE} andalso
         cut searchBudget.Application
           {candidates = NONE, applications = SOME 0,
            normalization = NONE} andalso
         cut searchBudget.Normalization
           {candidates = NONE, applications = NONE,
            normalization = SOME 0}
       end)

val nested_budget_context_slot =
  Context.Data.new
    {name = "linarith-selftest-nested-budget-context", empty = 0,
     pp = Int.toString}

val _ =
  check
    ("budgeted linarith proof retains an outer explicit context",
     fn () =>
       let
         val outer =
           Context.Data.put nested_budget_context_slot 1
             (Context.snapshot ())
         val supplied =
           Context.Data.put nested_budget_context_slot 2
             (Context.snapshot ())
         val budget = searchBudget.unbounded ()
       in
         Context.with_context outer
           (fn () =>
             let
               val outcome =
                 linarithLib.LINARITH_PROVE_BUDGETED_IN (Context.snapshot ())
                   budget forward_tm
               val after_proof =
                 Context.Data.get nested_budget_context_slot
                   (Context.snapshot ())
               val replay =
                 linarithReplay.fwd_prove_budgeted_in (Context.snapshot ())
                   (searchBudget.unbounded ()) one_split_config
                   [Thm.ASSUME split_x_upper] split_conclusion
               val after_replay =
                 Context.Data.get nested_budget_context_slot
                   (Context.snapshot ())
               val explicit =
                 linarithLib.LINARITH_PROVE_BUDGETED_IN
                   supplied (searchBudget.unbounded ()) forward_tm
               val explicit_replay =
                 linarithReplay.fwd_prove_budgeted_in supplied
                   (searchBudget.unbounded ()) one_split_config
                   [Thm.ASSUME split_x_upper] split_conclusion
               val after_explicit =
                 Context.Data.get nested_budget_context_slot
                   (Context.snapshot ())
             in
               after_proof = 1 andalso after_replay = 1 andalso
               after_explicit = 1 andalso
               (case outcome of
                    linarithLib.LinarithProved theorem =>
                      Term.aconv (Thm.concl theorem) forward_tm
                  | _ => false) andalso
               (case replay of
                    linarithReplay.ReplayProved theorem =>
                      Term.aconv (Thm.concl theorem) split_conclusion
                  | _ => false) andalso
               (case explicit of
                    linarithLib.LinarithProved theorem =>
                      Term.aconv (Thm.concl theorem) forward_tm
                  | _ => false) andalso
               (case explicit_replay of
                    linarithReplay.ReplayProved theorem =>
                      Term.aconv (Thm.concl theorem) split_conclusion
                  | _ => false)
             end) ()
       end)

val true_conv_tm =
  boolSyntax.mk_imp
    (public_x_le_y,
     num_leq public_x (num_plus public_y num_one))

val _ =
  check
    ("LINARITH_CONV proves a linear implication",
     fn () =>
       let
         val theorem = linarithLib.LINARITH_CONV true_conv_tm
         val (left, right) = boolSyntax.dest_eq (Thm.concl theorem)
       in
         Term.aconv left true_conv_tm andalso
         Term.aconv right boolSyntax.T
       end)

val false_conv_tm = num_less num_three num_two

val _ =
  check
    ("LINARITH_CONV disproves a false arithmetic relation",
     fn () =>
       let
         val theorem = linarithLib.LINARITH_CONV false_conv_tm
         val (left, right) = boolSyntax.dest_eq (Thm.concl theorem)
       in
         Term.aconv left false_conv_tm andalso
         Term.aconv right boolSyntax.F
       end)

val _ =
  check
    ("SIMPLE_LINARITH_TAC uses discreteness through Tactical.VALID",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([num_less public_x public_y],
          num_leq (num_plus public_x num_one) public_y))

val simple_budget_goal : Abbrev.goal =
  ([num_less public_x public_y],
   num_leq (num_plus public_x num_one) public_y)

val _ =
  check
    ("budgeted SIMPLE_LINARITH_TAC shares its refutation budget",
     fn () =>
       let
         val funded = searchBudget.unbounded ()
         val closed =
           valid_closes
             (linarithLib.SIMPLE_LINARITH_TAC_BUDGETED funded [])
             simple_budget_goal
         val used = searchBudget.usage funded
         val limited =
           searchBudget.create
             {candidates = SOME 0, applications = NONE,
              normalization = NONE}
         val cut =
           (ignore
              (Tactical.VALID
                 (linarithLib.SIMPLE_LINARITH_TAC_BUDGETED
                    limited []) simple_budget_goal
                 (Context.snapshot ()));
            false)
           handle searchBudget.LimitReached
                    (searchBudget.Candidate, usage) =>
                    usage = searchBudget.usage limited
                | _ => false
       in
         closed andalso #candidates used > 0 andalso
         #normalization used > 0 andalso cut
       end)

val public_x_neq_one = num_not (num_eq public_x num_one)

val _ =
  check
    ("SIMPLE_LINARITH_TAC splits disequalities through Tactical.VALID",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([public_x_neq_one, num_leq public_x num_one],
          num_less public_x num_one))

val public_fact_positive =
  num_less num_zero (numSyntax.mk_fact public_x)
val public_fact_positive_theorem =
  Thm.SPEC public_x arithmeticTheory.FACT_LESS

val _ =
  check
    ("plain tactic arguments are inserted as arithmetic facts",
     fn () =>
       tactic_fails (linarithLib.SIMPLE_LINARITH_TAC [])
         ([], public_fact_positive) andalso
       valid_closes
         (linarithLib.SIMPLE_LINARITH_TAC
           [public_fact_positive_theorem])
         ([], public_fact_positive))

val _ =
  check
    ("a supplied arithmetic fact retains its theorem hypothesis",
     fn () =>
       let
         val guard =
           Term.mk_var ("linarith_fact_guard", Type.bool)
         val supported =
           Drule.ADD_ASSUM guard public_fact_positive_theorem
         val tactic =
           linarithLib.SIMPLE_LINARITH_TAC [supported]
       in
         valid_closes tactic ([guard], public_fact_positive) andalso
         tactic_fails tactic ([], public_fact_positive)
       end)

fun marker_error_name marker =
  ((ignore (linarithLib.SIMPLE_LINARITH_TAC [marker]); false)
   handle Feedback.HOL_ERR error =>
     String.isSubstring "SIMPLE_LINARITH_TAC"
       (Feedback.message_of error))

val _ =
  check
    ("SIMPLE_LINARITH_TAC loudly rejects foreign argument markers",
     fn () =>
       List.all marker_error_name
         [markerLib.Split (hd (#pre_split num_instance)),
          clasetLib.Intro boolTheory.TRUTH,
          clasetLib.Simp boolTheory.TRUTH,
          clasetLib.Iff boolTheory.TRUTH,
          clasetLib.Norm boolTheory.TRUTH])

(* Full num preprocessing battery.  All positive tactic tests go through
   VALID so the generated proof is checked against the original goal. *)

val irrelevant_premise =
  Term.mk_var ("linarith_irrelevant_premise", Type.bool)
val connective_premise =
  boolSyntax.mk_conj (public_x_le_y, public_y_le_z)
val existential_premise =
  boolSyntax.mk_exists
    (public_z,
     boolSyntax.mk_conj (public_x_le_y, public_y_le_z))
val total_order_goal =
  boolSyntax.mk_disj (public_x_le_y, num_leq public_y public_x)
val iff_premise = boolSyntax.mk_eq (boolSyntax.T, public_x_le_y)

val _ =
  check
    ("full preprocessing filters relevance and flattens connectives",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         ([irrelevant_premise, connective_premise], public_x_le_z) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], total_order_goal) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([existential_premise], public_x_le_y) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([iff_premise], public_x_le_y))

(* Relevance filtering drops every assumption the arithmetic has no row
   for, which is every assumption a purely propositional contradiction
   is made of.  So the immediate-contradiction step runs on the goal as
   given, ahead of the filter: a goal already carrying F, or a literal
   alongside its negation, is closed rather than reported unrefutable. *)
val _ =
  check
    ("a propositional contradiction in the assumptions closes the goal",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         ([boolSyntax.F], num_less public_x num_zero) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([irrelevant_premise,
           boolSyntax.mk_neg irrelevant_premise],
          num_less public_x num_zero))

val _ =
  check
    ("literal indexing closes with the first alpha-equivalent pair",
     fn () =>
       let
         val positive = ``~P (\x : num. x)``
         val negative = ``~(~P (\y : num. y))``
         val later = Term.mk_var ("linarith_later_pair", Type.bool)
         val misses =
           List.tabulate
             (16, fn i =>
                boolSyntax.mk_neg
                  (Term.mk_var ("linarith_unpaired_" ^ Int.toString i,
                                Type.bool)))
         val goal =
           (misses @ [negative, boolSyntax.mk_neg later, later, positive],
            num_less public_x num_zero)
         val (goals, justify) = Tactical.VALID (linarithLib.LINARITH_TAC [])
           goal (Context.snapshot ())
       in
         null goals andalso
         (case Thm.hyp (justify []) of
              [left, right] =>
                (Term.aconv left positive andalso Term.aconv right negative)
                orelse
                (Term.aconv right positive andalso Term.aconv left negative)
            | _ => false)
       end)

(* Connected assumption ordering has to retain a disjunction after a
   chain of literals no disjunct closes on its own, then search every
   branch without losing any of the chain. *)
val chain_vars =
  List.tabulate
    (9, fn i =>
       Term.mk_var ("linarith_chain_" ^ Int.toString i, numSyntax.num))
val chain_target = Term.mk_var ("linarith_chain_target", numSyntax.num)
val chain_literals =
  List.tabulate
    (8, fn i =>
       num_leq (List.nth (chain_vars, i)) (List.nth (chain_vars, i + 1)))
val chain_disjunction =
  boolSyntax.list_mk_disj
    (List.tabulate
       (5, fn i =>
          num_leq
            (num_plus (last chain_vars)
               (numSyntax.mk_numeral (Arbnum.fromInt (i + 1))))
            chain_target))

val _ =
  check
    ("a connected disjunction is eliminated and the chain closed",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         (chain_literals @ [chain_disjunction],
          num_leq (hd chain_vars) chain_target))

(* Arithmetic scoring must select the final decisive disjunction before
   the unrelated total-order choices that precede it. *)
val choice_vars =
  List.tabulate
    (8, fn i =>
       Term.mk_var ("linarith_choice_" ^ Int.toString i, numSyntax.num))
val unrelated_choices =
  map
    (fn y =>
      boolSyntax.mk_disj
        (num_leq public_x y, num_less y public_x))
    choice_vars
val decisive_choice =
  boolSyntax.mk_disj
    (num_less public_x num_one, num_eq public_x num_one)

val _ =
  check
    ("arithmetic scoring avoids unrelated disjunction enumeration",
     fn () =>
       let
         val closes =
           valid_closes (linarithLib.LINARITH_TAC [])
             (num_leq num_one public_x ::
                unrelated_choices @ [decisive_choice],
              num_eq public_x num_one)
         val {disjunction_splits, ...} =
           linarithLib.last_search_stats ()
       in
         closes andalso disjunction_splits = 1
       end)

val _ =
  check
    ("budgeted disjunction scoring shares the invocation budget",
     fn () =>
       let
         val statement =
           boolSyntax.list_mk_imp
             (num_leq num_one public_x ::
                unrelated_choices @ [decisive_choice],
              num_eq public_x num_one)
         val funded = searchBudget.unbounded ()
         val proof =
           linarithLib.LINARITH_PROVE_BUDGETED_IN (Context.snapshot ())
             funded statement
         val used = searchBudget.usage funded
         val {disjunction_splits, ...} =
           linarithLib.last_search_stats ()
         val allowance = #candidates used div 2
         val limited =
           searchBudget.create
             {candidates = SOME allowance, applications = NONE,
              normalization = NONE}
         val cutoff =
           linarithLib.LINARITH_PROVE_BUDGETED_IN (Context.snapshot ())
             limited statement
       in
         (case proof of
              linarithLib.LinarithProved theorem =>
                null (Thm.hyp theorem) andalso
                Term.aconv (Thm.concl theorem) statement
            | _ => false) andalso
         disjunction_splits = 1 andalso allowance > 0 andalso
         (case cutoff of
              linarithLib.LinarithLimitReached
                {kind = searchBudget.Candidate, usage} =>
                  #candidates usage = allowance
            | _ => false)
       end)

(* Conditionals are the propositional form the old six-theorem rewrite
   list could not reach; normalForms.NNF_CONV splits them on both sides
   of the turnstile. *)
val cond_condition =
  Term.mk_var ("linarith_cond_condition", Type.bool)
val cond_premise =
  boolSyntax.mk_cond
    (cond_condition, public_x_le_y, num_less public_x public_y)
val cond_goal =
  boolSyntax.mk_cond
    (cond_condition, public_x_le_y,
     num_leq public_x (numSyntax.mk_suc public_y))

val _ =
  check
    ("full preprocessing splits conditionals in premise and goal",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         ([cond_premise], public_x_le_y) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([num_less public_x public_y], cond_goal))

val public_min = numSyntax.mk_min (public_x, public_y)
val public_max = numSyntax.mk_max (public_x, public_y)
val min_le_left = num_leq public_min public_x
val left_le_max = num_leq public_x public_max

val _ =
  check
    ("LINARITH_TAC keeps the ordinary MIN and MAX split path",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC []) ([], min_le_left) andalso
       valid_closes (linarithLib.LINARITH_TAC []) ([], left_le_max))

val _ =
  check
    ("budgeted LINARITH_PROVE follows the MIN split path",
     fn () =>
       let
         val funded = searchBudget.unbounded ()
         val proved =
           linarithLib.LINARITH_PROVE_BUDGETED_IN (Context.snapshot ())
             funded min_le_left
         val used = searchBudget.usage funded
         val limited =
           searchBudget.create
             {candidates = NONE, applications = SOME 1,
              normalization = NONE}
         val cutoff =
           linarithLib.LINARITH_PROVE_BUDGETED_IN (Context.snapshot ())
             limited min_le_left
       in
         (case proved of
              linarithLib.LinarithProved theorem =>
                null (Thm.hyp theorem) andalso
                Term.aconv (Thm.concl theorem) min_le_left
            | _ => false) andalso
         #applications used > 1 andalso
         (case cutoff of
              linarithLib.LinarithLimitReached
                {kind = searchBudget.Application, usage} =>
                  #applications usage = 1
            | _ => false)
       end)

val _ =
  check
    ("full preprocessing is strictly stronger than SIMPLE on MIN",
     fn () =>
       let
         val simple_fails =
           ((ignore
               (Tactical.VALID
                 (linarithLib.SIMPLE_LINARITH_TAC [])
                 ([], min_le_left) (Context.snapshot()));
             false)
            handle Feedback.HOL_ERR _ => true)
       in
         simple_fails andalso
         valid_closes (linarithLib.LINARITH_TAC []) ([], min_le_left)
       end)

val subtraction_zero =
  num_eq (numSyntax.mk_minus (public_x, public_y)) num_zero

val _ =
  check
    ("LINARITH_TAC splits natural subtraction",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         ([num_less public_x public_y], subtraction_zero))

val public_div_three = numSyntax.mk_div (public_x, num_three)
val public_mod_three = numSyntax.mk_mod (public_x, num_three)
val div_equation =
  Thm.concl
    (hd (#atom_facts num_instance public_div_three))
val mod_bound = num_less public_mod_three num_three

val _ =
  check
    ("LINARITH_TAC augments literal DIV/MOD atoms with DIVISION facts",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         ([num_less num_zero public_x], mod_bound) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], div_equation))

(* A conditional of the carrier is an atom: the decomposition cannot
   see into either branch until the condition is decided, so a bound
   that holds of both is out of reach and only a case split reaches it.
   Where the branches are literals the atom lies between them whatever
   the condition is, which is a linear fact and costs no split.  The
   three-bit goal below needs that of each of its three conditionals at
   once, and the seven it falls one short of is the same goal with the
   bound the atoms do not support. *)
fun cond_bit name high low =
  boolSyntax.mk_cond (Term.mk_var (name, Type.bool), high, low)

val cond_horner =
  numSyntax.mk_plus
    (cond_bit "linarith_cond_first" num_one num_zero,
     numSyntax.mk_mult
       (num_two,
        numSyntax.mk_plus
          (cond_bit "linarith_cond_second" num_one num_zero,
           numSyntax.mk_mult
             (num_two, cond_bit "linarith_cond_third" num_one num_zero))))

val cond_horner_bound =
  num_less cond_horner (numSyntax.mk_numeral (Arbnum.fromInt 8))
val cond_horner_short =
  num_less cond_horner (numSyntax.mk_numeral (Arbnum.fromInt 7))

(* The branches the other way round: which of the two is the bound
   below and which above is read off their values and not their
   position. *)
val cond_descending = cond_bit "linarith_cond_fourth" num_zero num_one

val _ =
  check
    ("LINARITH_TAC bounds a conditional by its literal branches",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC []) ([], cond_horner_bound)
         andalso
       tactic_fails (linarithLib.LINARITH_TAC []) ([], cond_horner_short)
         andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], num_leq cond_descending num_one)
         andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], num_leq num_zero cond_descending))

(* Neither branch bounds a conditional on its own, and the bound is
   read off the branches' values: between variables there are no values
   to read, and the goal below is false. *)
val cond_variables =
  cond_bit "linarith_cond_fifth" public_x public_y

val _ =
  check
    ("neither branch of a conditional is taken for its bound",
     fn () =>
       tactic_fails (linarithLib.LINARITH_TAC [])
         ([], num_leq cond_variables public_x))

val one_pipeline_round : linarithLib.linarith_config =
  {neq_limit = 9, split_limit = 1}
val zero_pipeline_rounds : linarithLib.linarith_config =
  {neq_limit = 9, split_limit = 0}
val nine_pipeline_rounds : linarithLib.linarith_config =
  {neq_limit = 9, split_limit = 9}

val _ =
  check
    ("default_config freezes both public limits at nine",
     fn () =>
       let
         val {neq_limit, split_limit} = linarithLib.default_config
       in
         neq_limit = 9 andalso split_limit = 9
       end)

val _ =
  check
    ("div/mod augmentation is bounded by split_limit",
     fn () =>
       tactic_fails
         (linarithLib.CFG_LINARITH_TAC zero_pipeline_rounds [])
         ([], mod_bound) andalso
       valid_closes
         (linarithLib.CFG_LINARITH_TAC one_pipeline_round [])
         ([], mod_bound))

val nested_div =
  numSyntax.mk_div
    (numSyntax.mk_div (public_x, num_three), num_two)
val nested_div_trigger = num_leq nested_div nested_div

(* The inner quotient is not an atom of either side, so closing this
   needs the facts the outer atom's own facts introduce: augmentation
   has to reach a fixpoint rather than stop after the atoms it was
   handed. *)
val nested_div_goal =
  ([num_less num_zero nested_div],
   num_less num_zero (numSyntax.mk_div (public_x, num_three)))

val _ =
  check
    ("nested div/mod augmentation reaches a bounded fixpoint",
     fn () =>
       tactic_fails
         (linarithLib.CFG_LINARITH_TAC zero_pipeline_rounds [])
         nested_div_goal andalso
       valid_closes
         (linarithLib.CFG_LINARITH_TAC one_pipeline_round [])
         nested_div_goal)

(* The certificate for this one scales a row twice, so replay builds
   q * 2 * 3 while the other side carries q * 6.  Cancellation matches
   summands syntactically, so until scaling renormalized its result and
   num canonicalized products, the solver reported a refutation that
   replay then could not derive falsity from. *)
val _ =
  check
    ("a doubly scaled row replays to falsity",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], boolSyntax.mk_imp
                (num_less num_zero nested_div,
                 num_leq (numSyntax.mk_numeral (Arbnum.fromInt 6))
                   public_x)))

(* Splitting on demand means the rounds are spent only when the
   arithmetic cannot close the goal without them: a goal refutable as it
   stands is closed even where no round is allowed at all, however much
   nested div/mod its assumptions carry. *)
val _ =
  check
    ("no augmentation round is spent on an already refutable goal",
     fn () =>
       valid_closes
         (linarithLib.CFG_LINARITH_TAC zero_pipeline_rounds [])
         ([nested_div_trigger, num_leq num_one num_zero],
          num_leq public_x public_x))

val nested_min =
  numSyntax.mk_min (numSyntax.mk_min (public_x, public_y), public_z)
val nested_min_goal = num_leq nested_min public_x

val _ =
  check
    ("operator splitting is bounded and accepts a CFG limit override",
     fn () =>
       tactic_fails
         (linarithLib.CFG_LINARITH_TAC one_pipeline_round [])
         ([], nested_min_goal) andalso
       valid_closes
         (linarithLib.CFG_LINARITH_TAC nine_pipeline_rounds [])
         ([], nested_min_goal))

val public_condition =
  Term.mk_var ("linarith_public_condition", Type.bool)
val public_conditional =
  boolSyntax.mk_cond (public_condition, public_x, public_y)
val public_conditional_bound = num_leq public_conditional public_z
val public_bool_split = TypeBase.case_pred_disj_of ``:bool``

val _ =
  check
    ("LINARITH_TAC consumes a per-call Split rule absent from its seeds",
     fn () =>
       let
         val goal =
           ([public_x_le_z, public_y_le_z], public_conditional_bound)
       in
         tactic_fails (linarithLib.LINARITH_TAC []) goal andalso
         valid_closes
           (linarithLib.LINARITH_TAC
             [markerLib.Split public_bool_split]) goal
       end)

fun full_marker_error marker =
  ((ignore (linarithLib.LINARITH_TAC [marker]); false)
   handle Feedback.HOL_ERR error =>
     String.isSubstring "LINARITH_TAC" (Feedback.message_of error) orelse
     String.isSubstring "CFG_LINARITH_TAC" (Feedback.message_of error))

val _ =
  check
    ("LINARITH_TAC rejects foreign argument markers",
     fn () =>
       List.all full_marker_error
         [clasetLib.Intro boolTheory.TRUTH,
          clasetLib.Simp boolTheory.TRUTH,
          clasetLib.Norm boolTheory.TRUTH])

val _ =
  check
    ("Split validation precedes rejection and preserves first-error order",
     fn () =>
       let
         val malformed = markerLib.Split boolTheory.TRUTH
         val valid = markerLib.Split public_bool_split
         val foreign = markerLib.ExclX "rule:linarith-selftest"
         fun error tactic arguments =
           ((ignore (tactic arguments); NONE)
            handle Feedback.HOL_ERR error =>
              SOME (Feedback.top_structure_of error,
                    Feedback.top_function_of error,
                    Feedback.message_of error))
         fun expected function message =
           SOME ("linarithLib", function, message)
         val bad = "Malformed Split theorem (expected P-form)"
       in
         error linarithLib.SIMPLE_LINARITH_TAC [malformed] =
           SOME ("linarithData", "SIMPLE_LINARITH_TAC", bad) andalso
         error linarithLib.SIMPLE_LINARITH_TAC [valid] =
           expected "SIMPLE_LINARITH_TAC"
             "Split marker is not accepted by SIMPLE_LINARITH_TAC" andalso
         error linarithLib.LINARITH_TAC [malformed, foreign] =
           SOME ("linarithData", "CFG_LINARITH_TAC", bad) andalso
         error linarithLib.LINARITH_TAC [foreign, malformed] =
           expected "CFG_LINARITH_TAC"
             "simplifier-control marker is not accepted by CFG_LINARITH_TAC"
       end)

val full_neq_one : linarithLib.linarith_config =
  {neq_limit = 1, split_limit = 9}
val full_neq_zero : linarithLib.linarith_config =
  {neq_limit = 0, split_limit = 9}
val neq_goal = num_less public_x num_one
val neq_assumptions = [public_x_neq_one, num_leq public_x num_one]

val _ =
  check
    ("CFG_LINARITH_TAC splits neq at the limit and ignores it above",
     fn () =>
       valid_closes
         (linarithLib.CFG_LINARITH_TAC full_neq_one [])
         (neq_assumptions, neq_goal) andalso
       tactic_fails
         (linarithLib.CFG_LINARITH_TAC full_neq_zero [])
         (neq_assumptions, neq_goal))

(* One procedure, one strength.  The forward entries are the search
   reached from a simplifier rather than from a goal, so a question the
   tactic decides cannot be declined merely because a simplifier asked
   it: the [-], MIN and MAX splits belong to the procedure, not to the
   tactic that wraps it. *)
val _ =
  check
    ("the forward entries split MIN like the tactic",
     fn () =>
       ((Term.aconv (Thm.concl (linarithLib.LINARITH_PROVE min_le_left))
           min_le_left)
        handle Feedback.HOL_ERR _ => false) andalso
       valid_closes (linarithLib.LINARITH_TAC []) ([], min_le_left))

val nonlinear_goal =
  num_leq (numSyntax.mk_mult (public_x, public_x)) public_x

val _ =
  check
    ("nonlinear goals fail cleanly without leaking global state",
     fn () =>
       let
         val facts_before = List.length (linarithData.arith_facts ())
         val splits_before =
           List.length (linarithData.arith_split_thms ())
         val injections_before =
           List.length (linarithData.injections ())
         val failed =
           ((ignore
               (linarithLib.SIMPLE_LINARITH_TAC [] ([], nonlinear_goal)
                  (Context.snapshot()));
             false)
            handle Feedback.HOL_ERR _ => true)
       in
         failed andalso
         facts_before = List.length (linarithData.arith_facts ()) andalso
         splits_before =
           List.length (linarithData.arith_split_thms ()) andalso
         injections_before = List.length (linarithData.injections ()) andalso
         Option.isSome (linarithData.instance_for numSyntax.num)
       end)

(* The carrier read off a conclusion is a guess about where to look for
   arithmetic, not a precondition on the goal: a contradictory context
   refutes a conclusion of any type. *)
val list_ty = listSyntax.mk_list_type Type.alpha
val list_l1 = Term.mk_var ("linarith_l1", list_ty)
val list_l2 = Term.mk_var ("linarith_l2", list_ty)

val _ =
  check
    ("a contradictory context closes a goal at an unregistered carrier",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         ([num_less public_x num_zero],
          boolSyntax.mk_eq (list_l1, list_l2)))

val unregistered_ty =
  Type.mk_type ("fun", [numSyntax.num, numSyntax.num])
val unregistered_left =
  Term.mk_var ("linarith_unregistered_left", unregistered_ty)
val unregistered_right =
  Term.mk_var ("linarith_unregistered_right", unregistered_ty)
val unregistered_goal =
  boolSyntax.mk_eq (unregistered_left, unregistered_right)
(* Built from the registry, like the hint itself: a roster spelled out
   here would go stale the moment a carrier is added. *)
val unregistered_message =
  "linear arithmetic found no proof (no linarith instance for " ^
  Parse.type_to_string unregistered_ty ^ "; registered: " ^
  String.concatWith ", "
    (map (Parse.type_to_string o #ty) (linarithData.all_instances ())) ^
  ")"

fun has_unregistered_message operation =
  ((operation (); false)
   handle Feedback.HOL_ERR error =>
     Feedback.message_of error = unregistered_message)

val _ =
  check
    ("all public entries report the same unregistered-carrier failure",
     fn () =>
       List.all has_unregistered_message
         [fn () =>
            ignore
              (linarithLib.LINARITH_TAC [] ([], unregistered_goal)
                (Context.snapshot())),
          fn () =>
            ignore
              (linarithLib.SIMPLE_LINARITH_TAC []
                ([], unregistered_goal) (Context.snapshot())),
          fn () =>
            ignore
              (linarithLib.CFG_LINARITH_TAC
                linarithLib.default_config [] ([], unregistered_goal)
                (Context.snapshot())),
          fn () => ignore (linarithLib.LINARITH_PROVE unregistered_goal),
          fn () => ignore (linarithLib.LINARITH_CONV unregistered_goal)])

(* Reducer, solver, and cache integration. *)

fun reducer_conversion theorems tm =
  let
    val {initial, addcontext, apply, ...} =
      Traverse.dest_reducer linarithLib.LINARITH_REDUCER
    val context = addcontext (initial, theorems)
  in
    apply
      {solver = fn _ => Conv.NO_CONV,
       conv = fn _ => Conv.NO_CONV,
       context = context,
       stack = [],
       relation = (boolSyntax.equality, Thm.REFL)} tm
  end

fun reducer_succeeds theorems tm =
  ((ignore (reducer_conversion theorems tm); true)
   handle Feedback.HOL_ERR _ => false)

val _ =
  check
    ("LINARITH_REDUCER admits local arithmetic context",
     fn () =>
       (linarithLib.clear_linarith_caches ();
        reducer_succeeds [Thm.ASSUME public_x_le_y] public_x_le_y andalso
        reducer_succeeds [Thm.ASSUME public_x_le_y] public_x_le_y))

(* [SUC y] is subtracted and added back, so the goal is decidable only
   once the truncated subtraction is split on its sign.  Stated with a
   context rather than closed, because that is the shape a side
   condition arrives in. *)
val forward_split_context =
  [num_less public_x public_z, num_less public_y public_x]
val forward_split_goal =
  num_less public_x
    (numSyntax.mk_plus
       (numSyntax.mk_suc public_y,
        numSyntax.mk_minus (public_z, numSyntax.mk_suc public_y)))

val _ =
  check
    ("the simplifier-facing entries split subtraction like the tactic",
     fn () =>
       (linarithLib.clear_linarith_caches ();
        valid_closes (linarithLib.LINARITH_TAC [])
          (forward_split_context, forward_split_goal) andalso
        reducer_succeeds (map Thm.ASSUME forward_split_context)
          forward_split_goal andalso
        ((ignore
            (#solve linarithLib.linarith_solver
               {stack = [],
                recurse = Conv.NO_CONV,
                context_thms = map Thm.ASSUME forward_split_context}
               forward_split_goal);
          true)
         handle Feedback.HOL_ERR _ => false)))

val conjunctive_context =
  HolKernel.CONJ
    (Thm.ASSUME public_x_le_y) (Thm.ASSUME public_y_le_z)

val _ =
  check
    ("CACHED_LINARITH tracks atoms in conjunctive context",
     fn () =>
       (linarithLib.clear_linarith_caches ();
        Term.aconv
          (Thm.concl
            (linarithLib.CACHED_LINARITH
              [conjunctive_context] public_x_le_z))
          (boolSyntax.mk_eq (public_x_le_z, boolSyntax.T))))

val nonlinear_closed_fact = arithmeticTheory.X_LE_X_SQUARED
val nonlinear_closed_goal = Thm.concl nonlinear_closed_fact
val quantified_nonlinear_fact =
  Thm.GEN public_x nonlinear_closed_fact

val _ =
  check
    ("LINARITH_REDUCER applies context admission screens",
     fn () =>
       (linarithLib.clear_linarith_caches ();
        not (reducer_succeeds [nonlinear_closed_fact]
               nonlinear_closed_goal) andalso
        (linarithLib.clear_linarith_caches ();
         not (reducer_succeeds [quantified_nonlinear_fact]
                nonlinear_closed_goal)) andalso
        (linarithLib.clear_linarith_caches ();
         not (reducer_succeeds [boolTheory.TRUTH] public_x_le_y))))

val min_le_rule = hd (Drule.CONJUNCTS arithmeticTheory.MIN_EQ_LE)
val linarith_side_ss =
  simpLib.++
    (simpLib.++ (simpLib.empty_ss, simpLib.rewrites [min_le_rule]),
     linarithLib.LINARITH_ss)
val min_side_goal =
  (boolSyntax.mk_eq (numSyntax.mk_min (public_x, public_z), public_x))

val _ =
  check
    ("LINARITH_ss discharges a conditional rewrite side condition",
     fn () =>
       valid_closes
         (simpLib.FULL_SIMP_TAC linarith_side_ss [])
         ([public_x_le_y, public_y_le_z], min_side_goal))

fun private_budget_test body =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = Theory.new_theory "linarithBudgetGateSelftest"
        val name = "budget_gate_atom"
        val _ = Theory.new_constant (name, Type.bool)
        val atom =
          Term.prim_mk_const
            {Thy = Theory.current_theory (), Name = name}
        val assumptions =
          List.tabulate
            (64, fn index =>
              let
                fun variable suffix =
                  Term.mk_var
                    ("budget_gate_" ^ Int.toString index ^ suffix,
                     numSyntax.num)
              in
                Thm.ASSUME
                  (num_leq (variable "_left") (variable "_right"))
              end)
        fun conversion budget tm =
          let
            val {initial, addcontext, apply, ...} =
              Traverse.dest_reducer
                (linarithLib.LINARITH_REDUCER_BUDGETED
                   (Context.snapshot ()) budget)
          in
            apply
              {solver = fn _ => Conv.NO_CONV,
               conv = fn _ => Conv.NO_CONV,
               context = addcontext (initial, assumptions),
               stack = [],
               relation = (boolSyntax.equality, Thm.REFL)} tm
          end
      in
        body (atom, assumptions, conversion)
      end
  in
    Portable.finally (fn () => Context.restore saved) run ()
  end

val _ =
  check
    ("LINARITH gates a non-arithmetic atom before candidate charges",
     fn () =>
       private_budget_test
         (fn (atom, _, conversion) =>
           let
             fun declined budget =
               let
                 val prior_usage = searchBudget.usage budget
                 val refused =
                   ((ignore (conversion budget atom); false)
                    handle Feedback.HOL_ERR _ => true
                         | searchBudget.LimitReached _ => false)
               in
                 refused andalso searchBudget.usage budget = prior_usage
               end
             val zero =
               searchBudget.create
                 {candidates = SOME 0, applications = NONE,
                  normalization = NONE}
           in
             declined (searchBudget.unbounded ()) andalso declined zero
           end))

val _ =
  check
    ("LINARITH still charges and certifies an arithmetic atom",
     fn () =>
       private_budget_test
         (fn (_, assumptions, conversion) =>
           let
             val target = Thm.concl (hd assumptions)
             val context = map Thm.concl assumptions
             val funded = searchBudget.unbounded ()
             val (remaining, validation) =
               Tactical.VALID
                 (Tactic.CONV_TAC (conversion funded))
                 (context, target) (Context.snapshot ())
             val theorem = validation []
             val zero =
               searchBudget.create
                 {candidates = SOME 0, applications = NONE,
                  normalization = NONE}
             val limited =
               ((ignore (conversion zero target); false)
                handle searchBudget.LimitReached
                         (searchBudget.Candidate, used) =>
                         #candidates used = 0
                     | _ => false)
           in
             null remaining andalso Term.aconv (Thm.concl theorem) target
             andalso
             List.all
               (fn premise => List.exists (Term.aconv premise) context)
               (Thm.hyp theorem)
             andalso #candidates (searchBudget.usage funded) > 0
             andalso limited
           end))

val _ =
  check
    ("ORDER gates an unrelated atom before candidate charges",
     fn () =>
       let
         val saved = Context.snapshot ()
         fun run () =
           let
             val _ = Theory.new_theory "orderBudgetGateSelftest"
             val name = "budget_gate_atom"
             val _ = Theory.new_constant (name, Type.bool)
             val atom =
               Term.prim_mk_const
                 {Thy = Theory.current_theory (), Name = name}
             val assumptions =
               List.tabulate
                 (64, fn index =>
                   let
                     fun variable suffix =
                       Term.mk_var
                         ("budget_gate_" ^ Int.toString index ^ suffix,
                          numSyntax.num)
                   in
                     Thm.ASSUME
                       (numSyntax.mk_leq
                          (variable "_left", variable "_right"))
                   end)
             fun declined budget =
               let
                 val ss =
                   simpLib.++
                     (simpLib.empty_ss, orderLib.ORDER_ss_budgeted budget)
                 val {initial, addcontext, apply, ...} =
                   Traverse.dest_reducer
                     (hd (#dprocs (simpLib.traversedata_for_ss ss)))
                 val context = addcontext (initial, assumptions)
                 val prior_usage = searchBudget.usage budget
                 val refused =
                   ((ignore
                       (apply
                          {solver = fn _ => Conv.NO_CONV,
                           conv = fn _ => Conv.NO_CONV,
                           context = context,
                           stack = [],
                           relation = (boolSyntax.equality, Thm.REFL)}
                          atom);
                     false)
                    handle Feedback.HOL_ERR _ => true
                         | searchBudget.LimitReached _ => false)
               in
                 refused andalso searchBudget.usage budget = prior_usage
               end
             val zero =
               searchBudget.create
                 {candidates = SOME 0, applications = NONE,
                  normalization = NONE}
           in
             declined (searchBudget.unbounded ()) andalso declined zero
           end
       in
         Portable.finally (fn () => Context.restore saved) run ()
       end)

val _ =
  check
    ("budgeted LINARITH reducer charges its nested proof",
     fn () =>
       let
         val ctxt = Context.snapshot ()
         val funded = searchBudget.unbounded ()
         val ss =
           simpLib.++
             (simpLib.++
                (simpLib.empty_ss, simpLib.rewrites [min_le_rule]),
              linarithLib.LINARITH_ss_budgeted ctxt funded)
         val closed =
           valid_closes
             (simpLib.FULL_SIMP_TAC ss [])
             ([public_x_le_y, public_y_le_z], min_side_goal)
         val used = searchBudget.usage funded
         val zero =
           searchBudget.create
             {candidates = SOME 0, applications = NONE,
              normalization = NONE}
         val limited_ss =
           simpLib.++
             (simpLib.++
                (simpLib.empty_ss, simpLib.rewrites [min_le_rule]),
              linarithLib.LINARITH_ss_budgeted ctxt zero)
         val cutoff =
           ((ignore
               (Tactical.VALID
                 (simpLib.FULL_SIMP_TAC limited_ss [])
                 ([public_x_le_y, public_y_le_z], min_side_goal)
                 ctxt);
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
    ("LINARITH_ext_ss lifts contexts, nested charges and typed cutoff",
     fn () =>
       let
         val ctxt = Context.snapshot ()
         fun simpset fragment =
           simpLib.++
             (simpLib.++
                (simpLib.empty_ss, simpLib.rewrites [min_le_rule]),
              fragment)
         val goal = ([public_x_le_y, public_y_le_z], min_side_goal)
         fun closes fragment =
           valid_closes
             (simpLib.FULL_SIMP_TAC (simpset fragment) []) goal
         val funded = searchBudget.unbounded ()
         val ordinary_lift = closes linarithLib.LINARITH_ext_ss
         val budgeted_lift =
           closes (linarithLib.LINARITH_ext_ss_budgeted ctxt funded)
         val zero =
           searchBudget.create
             {candidates = SOME 0, applications = NONE,
              normalization = NONE}
         val cutoff =
           ((ignore
               (Tactical.VALID
                 (simpLib.FULL_SIMP_TAC
                   (simpset
                     (linarithLib.LINARITH_ext_ss_budgeted ctxt zero)) [])
                 goal ctxt);
             false)
            handle searchBudget.LimitReached
                     (searchBudget.Candidate, usage) =>
                     #candidates usage = 0
                 | _ => false)
       in
         ordinary_lift andalso budgeted_lift andalso
         #candidates (searchBudget.usage funded) > 0 andalso cutoff
       end)

val _ =
  check
    ("lin_arith solver uses its supplied arithmetic context",
     fn () =>
       let
         val {name, solve} = linarithLib.linarith_solver
         val theorem =
           solve
             {stack = [],
              context_thms =
                [Thm.ASSUME public_x_le_y,
                 Thm.ASSUME public_y_le_z],
              recurse = Conv.NO_CONV} public_x_le_z
       in
         name = "lin_arith" andalso
         Term.aconv (Thm.concl theorem) public_x_le_z
       end)

(* The branch cache_check does not take: a plain boolean atom is neither
   relevant nor F, so the solver keeps the direct forward call and can
   still discharge it from a contradictory arithmetic context. *)
val public_p = Term.mk_var ("linarith_public_p", Type.bool)
val public_successor_bound =
  num_leq (num_plus public_z num_one) public_z

val _ =
  check
    ("lin_arith solver discharges a non-arithmetic side condition",
     fn () =>
       let
         val {solve, ...} = linarithLib.linarith_solver
         val outside_guard =
           not (linarithDecomp.is_relevant public_p) andalso
           not (Term.aconv public_p boolSyntax.F)
         val theorem =
           solve
             {stack = [],
              context_thms = [Thm.ASSUME public_successor_bound],
              recurse = Conv.NO_CONV} public_p
       in
         outside_guard andalso
         Term.aconv (Thm.concl theorem) public_p
       end)

(* The [arith] tests below drive the table through the export the
   attribute itself uses, so what they exercise is the table a user's
   annotation reaches rather than a private hook.  NONE is "this
   session has no such export", which is a failed assertion wherever it
   is asked for. *)
fun with_arith_exports named_thms operation =
  case ThmSetData.data_exportfns {settype = "arith"} of
      NONE => NONE
    | SOME export =>
        let
          fun add named_thm =
            #add export {thy = "arithmetic", named_thm = named_thm}
          fun remove ({Thy, Name}, _) =
            #remove export
              {thy = "arithmetic", remove = Thy ^ "$" ^ Name}
          fun remove_all () = List.app remove named_thms
          val _ = List.app add named_thms
          val result = operation () handle e => (remove_all (); raise e)
          val _ = remove_all ()
        in
          SOME result
        end

fun with_arith_export operation =
  case with_arith_exports
         [({Thy = "arithmetic", Name = "X_LE_X_SQUARED"},
           nonlinear_closed_fact)]
         operation of
      NONE => false
    | SOME result => result

val _ =
  check
    ("cached failure is retried after dynamic [arith] growth",
     fn () =>
       let
         val _ = linarithLib.clear_linarith_caches ()
         val failed_before =
           not (reducer_succeeds [] nonlinear_closed_goal)
       in
         failed_before andalso
         with_arith_export
           (fn () => reducer_succeeds [] nonlinear_closed_goal)
       end)

(* A call the reducer's guard admits carries the whole [arith] table
   into its context, assumed.  Splitting the table into literals and
   assuming them is a pure function of the table and is derived once
   per state of it, so what a repeated call spends on the table is the
   discharge of its result against those literals and nothing else.

   A bound rather than a count: one more [arith] fact costs a repeated
   call at most one PROVE_HYP, and what a PROVE_HYP costs is measured
   here rather than written down.  Inference counting is a global
   kernel flag, off in a fresh session and put back off. *)
fun counted work =
  let
    val meter = Count.mk_meter ()
    val _ = work ()
    val prims = #prims (Count.read meter)
    val _ = Count.counting_thms false
  in
    prims
  end

val discharge_prims =
  let
    val left = Thm.ASSUME public_x_le_y
    val right = Thm.ASSUME public_y_le_z
  in
    counted (fn () => ignore (Drule.PROVE_HYP left right))
  end

val envelope_rounds = 4

(* One warming call, uncounted: what the repeats after it spend is the
   envelope, since the cache answers the goal itself. *)
fun envelope_prims named_thms =
  let
    val {solve, ...} = linarithLib.linarith_solver
    val context = [Thm.ASSUME public_x_le_y, Thm.ASSUME public_y_le_z]
    fun call () =
      ignore
        (solve
          {stack = [],
           context_thms = context, recurse = Conv.NO_CONV}
          public_x_le_z)
    fun repeat 0 = ()
      | repeat rounds = (call (); repeat (rounds - 1))
  in
    with_arith_exports named_thms
      (fn () =>
        (linarithLib.clear_linarith_caches ();
         call ();
         counted (fn () => repeat envelope_rounds)))
  end

(* One literal apiece: a conjunctive fact contributes a discharge per
   conjunct, and the bound is stated per fact. *)
val envelope_facts =
  [({Thy = "arithmetic", Name = "LESS_EQ_REFL"},
    arithmeticTheory.LESS_EQ_REFL),
   ({Thy = "arithmetic", Name = "ZERO_LESS_EQ"},
    arithmeticTheory.ZERO_LESS_EQ),
   ({Thy = "arithmetic", Name = "LESS_EQ_ADD"},
    arithmeticTheory.LESS_EQ_ADD)]

val _ =
  check
    ("a repeated call pays the [arith] table its discharge and no more",
     fn () =>
       case (envelope_prims [], envelope_prims envelope_facts) of
           (SOME bare, SOME loaded) =>
             0 < discharge_prims andalso
             loaded - bare <=
               envelope_rounds * length envelope_facts * discharge_prims
         | _ => false)

(* Data the tactic layer derives from the registry and from the
   [arith_split] table is built once per state of them rather than once
   per call, so the failure to watch for is a stale rule that silently
   does not fire.  The two tests below assert the transitions: each
   state decides the very next tactic call, with no call in between to
   warm anything. *)
fun num_instance_with nnf_rules pre_split =
  {ty = #ty num_instance,
   discrete = #discrete num_instance,
   dest = #dest num_instance,
   kit = #kit num_instance,
   norm_conv = #norm_conv num_instance,
   nnf_rules = nnf_rules,
   pre_split = pre_split,
   atom_facts = #atom_facts num_instance} :
     linarithData.linarith_instance

fun with_num_instances stages =
  let
    fun restore () = linarithData.register_instance num_instance
    fun run [] = true
      | run ((instance, assertion) :: rest) =
          (linarithData.register_instance instance;
           assertion () andalso run rest)
    val result = run stages handle e => (restore (); raise e)
    val _ = restore ()
  in
    result
  end

(* A tactic that raises has not closed the goal, and reporting that as
   a failed assertion rather than an escaping exception keeps a stale
   rule legible as the test that noticed it. *)
fun linarith_closes tm =
  valid_closes (linarithLib.LINARITH_TAC []) ([], tm)
  handle Feedback.HOL_ERR _ => false

fun linarith_fails tm =
  tactic_fails (linarithLib.LINARITH_TAC []) ([], tm)

(* Only nnf_rules closes this one once pre_split is empty: with the
   split seeds gone, x - y is an atom the search knows nothing about. *)
val subtraction_implication =
  boolSyntax.mk_imp (subtraction_zero, public_x_le_y)

val bare_num_instance = num_instance_with [] []

val nnf_only_num_instance =
  num_instance_with (#nnf_rules num_instance) []

val _ =
  check
    ("a fresh registration decides the very next tactic call",
     fn () =>
       with_num_instances
         [(bare_num_instance,
           fn () =>
             linarith_fails subtraction_implication andalso
             linarith_fails min_le_left),
          (nnf_only_num_instance,
           fn () =>
             linarith_closes subtraction_implication andalso
             linarith_fails min_le_left)] andalso
       linarith_closes min_le_left)

fun with_split_export theorem operation =
  case ThmSetData.data_exportfns {settype = "arith_split"} of
      NONE => false
    | SOME export =>
        let
          val name = {Thy = "linarithSeed", Name = "NUM_MIN_SPLIT"}
          fun remove () =
            #remove export
              {thy = "linarithSeed",
               remove = "linarithSeed$NUM_MIN_SPLIT"}
          val _ = #add export
            {thy = "linarithSeed", named_thm = (name, theorem)}
          val result = operation () handle e => (remove (); raise e)
          val _ = remove ()
        in
          result
        end

(* The [arith_split] table is the half no registration counter sees:
   AncestryData installs a whole table on an ancestry change without
   applying a delta, so what the split rules are keyed on is the
   table's own theorems. *)
val _ =
  check
    ("an [arith_split] change decides the very next tactic call",
     fn () =>
       with_num_instances
         [(nnf_only_num_instance,
           fn () =>
             linarith_fails min_le_left andalso
             with_split_export linarithSeedTheory.NUM_MIN_SPLIT
               (fn () => linarith_closes min_le_left) andalso
             linarith_fails min_le_left)] andalso
       null (linarithData.arith_split_thms ()) andalso
       Option.isSome (linarithData.instance_for numSyntax.num))

(* Both tables key an entry on the theory its declaration was made in,
   and a retraction written without one is resolved against the theory
   it is written in.  This binary starts with no theory segment at all,
   so the tests from here on open one -- which is the state anything
   declaring or retracting is called in anyway. *)
val _ = Theory.new_theory "linarithRemovalSelftest"

(* A declaration goes through the attribute's own local function, which
   is the [local] annotation's path and the one that takes the theorem
   it is handed rather than a name to fetch from the database. *)
fun declare_local settype name theorem =
  ThmAttribute.local_attribute
    {name = name, attrname = settype, args = [], thm = theorem}

(* A retraction by key goes through the export the replay of a recorded
   delta goes through, which is what makes it the descendant's view. *)
fun retract_by_key settype key =
  case ThmSetData.data_exportfns {settype = settype} of
      NONE => false
    | SOME export =>
        (#remove export
           {thy = Theory.current_theory (), remove = key};
         true)

(* A declaration under a name the table already holds replaces the
   theorem in place and leaves the key set exactly as it was, which is
   what a user editing a split rule and re-running its declaration
   does.  The split tactic is derived from the table once per state of
   it, so the state it is derived against has to be the table itself. *)
val replaced_split_name = "linarith_replaced_split_selftest"

val replaced_split_key =
  Theory.current_theory () ^ "$" ^ replaced_split_name

fun replaced_split_decides () =
  let
    fun declare theorem =
      declare_local "arith_split" replaced_split_name theorem
    fun retract () = retract_by_key "arith_split" replaced_split_key
    val _ = declare linarithSeedTheory.NUM_MAX_SPLIT
    val before_replacement = linarith_fails min_le_left
    val _ = declare linarithSeedTheory.NUM_MIN_SPLIT
    val after_replacement =
      linarith_closes min_le_left handle e => (retract (); raise e)
  in
    retract () andalso before_replacement andalso after_replacement
  end

val _ =
  check
    ("an [arith_split] rule replaced in place decides the next call",
     fn () =>
       with_num_instances
         [(nnf_only_num_instance, replaced_split_decides)] andalso
       null (linarithData.arith_split_thms ()))

(* A REMOVE delta is replayed by every theory below the one that wrote
   it, so what it names has to designate the same entry there as here.
   The two halves are checked against each other: an unqualified name
   is resolved where the retraction is written, and the applier -- the
   one replay goes through -- deletes with the recorded string as it
   stands. *)
fun recorded_removals settype =
  List.mapPartial
    (fn ThmSetData.REMOVE key => SOME key | _ => NONE)
    (ThmSetData.current_data {settype = settype})

fun retraction_records settype key =
  List.exists (fn recorded => recorded = key) (recorded_removals settype)

val bare_retraction_name = "linarith_bare_retraction_selftest"

val bare_retraction_key =
  Theory.current_theory () ^ "$" ^ bare_retraction_name

val bare_retraction_thm = arithmeticTheory.LESS_EQ_REFL

fun arith_holds theorem =
  List.exists
    (fn candidate => Term.aconv (Thm.concl candidate) (Thm.concl theorem))
    (linarithData.arith_facts ())

val _ =
  check
    ("an unqualified [arith] retraction records the key it denotes",
     fn () =>
       let
         fun declare () =
           declare_local "arith" bare_retraction_name bare_retraction_thm
         val _ = declare ()
         val declared = arith_holds bare_retraction_thm
         val _ = linarithData.remove_arith bare_retraction_name
         val retracted = not (arith_holds bare_retraction_thm)
         (* What a descendant replays is the recorded string, applied as
            it stands. *)
         val _ = declare ()
         val redeclared = arith_holds bare_retraction_thm
         val applied = retract_by_key "arith" bare_retraction_key
       in
         declared andalso retracted andalso redeclared andalso applied
         andalso retraction_records "arith" bare_retraction_key andalso
         not (arith_holds bare_retraction_thm)
       end)

val _ =
  check
    ("an unqualified [arith_split] retraction records a key too",
     fn () =>
       let
         val name = "linarith_bare_split_retraction_selftest"
         val _ = linarithData.remove_arith_split name
       in
         retraction_records "arith_split"
           (Theory.current_theory () ^ "$" ^ name)
       end)

(* A name that spells no key at all denotes nothing anywhere, and a
   retraction that recorded it would be a delta every descendant
   inherits and none can act on.  The one point at which the user is
   there to be told is the call. *)
fun retraction_rejects retract name =
  ((retract name; false)
   handle Feedback.HOL_ERR error =>
     String.isSubstring "Malformed name" (Feedback.message_of error))

val _ =
  check
    ("a retraction spelling no key at all is rejected and records none",
     fn () =>
       let
         val arith_before = List.length (recorded_removals "arith")
         val split_before = List.length (recorded_removals "arith_split")
         val rejected =
           retraction_rejects linarithData.remove_arith
             "linarithThy.linarith_fact.aux" andalso
           retraction_rejects linarithData.remove_arith_split
             "linarithThy.linarith_split.aux"
       in
         rejected andalso
         List.length (recorded_removals "arith") = arith_before andalso
         List.length (recorded_removals "arith_split") = split_before
       end)

val _ =
  check
    ("retracting an absent but well-spelled name is a no-op",
     fn () =>
       ((linarithData.remove_arith "linarith_absent_selftest";
         linarithData.remove_arith_split
           "linarithAbsentThy.linarith_absent_selftest";
         true)
        handle Feedback.HOL_ERR _ => false))

(* An atom fact in equivalence form is the shape that lets fact
   augmentation and disjunction elimination feed each other:
   normalization replaces the equivalence by its disjuncts, the
   elimination consumes those, and the atom is still an atom on the
   branch below, so nothing in the goal records that the fact has
   already been contributed.  A goal the arithmetic cannot refute is
   reported, never searched for ever. *)
fun num_instance_with_atom_facts atom_facts =
  {ty = #ty num_instance,
   discrete = #discrete num_instance,
   dest = #dest num_instance,
   kit = #kit num_instance,
   norm_conv = #norm_conv num_instance,
   nnf_rules = #nnf_rules num_instance,
   pre_split = #pre_split num_instance,
   atom_facts = atom_facts} :
     linarithData.linarith_instance

fun positivity_facts tm =
  if Term.is_var tm andalso
     linarithData.same_type (Term.type_of tm) numSyntax.num
  then [Thm.SPEC tm arithmeticTheory.NOT_ZERO_LT_ZERO]
  else []

val equivalence_fact_instance =
  num_instance_with_atom_facts positivity_facts

(* The message is part of the assertion: a search that only ran out of
   budget reports the limit, and a search that alternated for ever
   reports nothing at all. *)
fun reports_no_proof tm =
  ((ignore
      (linarithLib.LINARITH_TAC [] ([], tm) (Context.snapshot()));
    false)
   handle Feedback.HOL_ERR error =>
     Feedback.message_of error = "linear arithmetic found no proof")

val _ =
  check
    ("an equivalence-shaped atom fact still reports no proof",
     fn () =>
       with_num_instances
         [(equivalence_fact_instance,
           fn () => reports_no_proof (num_less public_x num_three))])

(* A tactic value built before a change and applied after it.  The
   entry points read the registry and the two tables where they are
   applied, so the hoisted value decides the goal the same way the same
   expression written out at the call site would; reading them where
   the value was built answers with the state of an hour ago. *)
val _ =
  check
    ("a hoisted tactic value reads the [arith] table where applied",
     fn () =>
       let
         val hoisted_full = linarithLib.LINARITH_TAC []
         val hoisted_simple = linarithLib.SIMPLE_LINARITH_TAC []
         val hoisted_cfg =
           linarithLib.CFG_LINARITH_TAC linarithLib.default_config []
         fun closes tactic =
           valid_closes tactic ([], nonlinear_closed_goal)
           handle Feedback.HOL_ERR _ => false
       in
         not (closes hoisted_full) andalso
         with_arith_export
           (fn () =>
              closes hoisted_full andalso closes hoisted_simple andalso
              closes hoisted_cfg) andalso
         not (closes hoisted_full)
       end)

val _ =
  check
    ("a hoisted tactic value reads the registry where applied",
     fn () =>
       let
         val hoisted = linarithLib.LINARITH_TAC []
         fun closes tm =
           valid_closes hoisted ([], tm)
           handle Feedback.HOL_ERR _ => false
         fun fails tm = tactic_fails hoisted ([], tm)
       in
         with_num_instances
           [(bare_num_instance,
             fn () =>
               fails subtraction_implication andalso fails min_le_left),
            (nnf_only_num_instance,
             fn () =>
               closes subtraction_implication andalso
               fails min_le_left andalso
               with_split_export linarithSeedTheory.NUM_MIN_SPLIT
                 (fn () => closes min_le_left))] andalso
         closes min_le_left
       end)

(* The result cache records failures, so a registration that turns a
   failure into a proof has to reach it, and the library rather than
   the caller is what has to notice.  Discreteness is the registry-only
   half of the decision: the cached entries run the forward procedure,
   which does no operator splitting and reads no table, so a dense num
   instance decides this goal the other way. *)
val dense_num_instance =
  {ty = #ty num_instance,
   discrete = NONE,
   dest = #dest num_instance,
   kit = #kit num_instance,
   norm_conv = #norm_conv num_instance,
   nnf_rules = #nnf_rules num_instance,
   pre_split = #pre_split num_instance,
   atom_facts = #atom_facts num_instance} :
     linarithData.linarith_instance

val public_x_lt_y = num_less public_x public_y
val public_successor_le_y = num_leq (num_plus public_x num_one) public_y

val _ =
  check
    ("a registry change invalidates a cached failure",
     fn () =>
       let
         val _ = linarithLib.clear_linarith_caches ()
         fun decided () =
           (ignore
              (linarithLib.CACHED_LINARITH [Thm.ASSUME public_x_lt_y]
                 public_successor_le_y);
            true)
           handle Feedback.HOL_ERR _ => false
       in
         with_num_instances
           [(dense_num_instance, fn () => not (decided ())),
            (num_instance, fn () => decided ())]
       end)

(* Traverse offers the solver every side condition of every conditional
   rewrite, and one outside the cache guard is discharged only from a
   contradictory context -- the same question whatever the condition
   was.  So the answer is cached rather than re-derived per condition,
   which an instance counting the atoms the procedure asks it about can
   state without reading the cache. *)
val nonneg_calls = ref 0

val counting_num_instance =
  let
    val kit = #kit num_instance
    fun nonneg tm =
      (nonneg_calls := !nonneg_calls + 1; #nonneg kit tm)
  in
    {ty = #ty num_instance,
     discrete = #discrete num_instance,
     dest = #dest num_instance,
     kit =
       {add_mono = #add_mono kit,
        mult_mono = #mult_mono kit,
        not_less = #not_less kit,
        not_le = #not_le kit,
        neqE = #neqE kit,
        nonneg = nonneg},
     norm_conv = #norm_conv num_instance,
     nnf_rules = #nnf_rules num_instance,
     pre_split = #pre_split num_instance,
     atom_facts = #atom_facts num_instance} :
       linarithData.linarith_instance
  end

fun solver_discharges_public_p () =
  let
    val {solve, ...} = linarithLib.linarith_solver
  in
    Term.aconv
      (Thm.concl
        (solve
          {stack = [],
           context_thms = [Thm.ASSUME public_successor_bound],
           recurse = Conv.NO_CONV} public_p))
      public_p
  end

val _ =
  check
    ("a non-arithmetic side condition is decided once and then cached",
     fn () =>
       with_num_instances
         [(counting_num_instance,
           fn () =>
             let
               val _ = linarithLib.clear_linarith_caches ()
               val _ = nonneg_calls := 0
               val first = solver_discharges_public_p ()
               val after_first = !nonneg_calls
               val repeats =
                 List.all (fn _ => solver_discharges_public_p ())
                   [1, 2, 3]
             in
               first andalso repeats andalso 0 < after_first andalso
               !nonneg_calls = after_first
             end)])

fun solver_declines context tm =
  let
    val {solve, ...} = linarithLib.linarith_solver
  in
    (ignore
       (solve
         {stack = [],
          context_thms = context, recurse = Conv.NO_CONV}
         tm);
     false)
    handle Feedback.HOL_ERR _ => true
  end

(* The condition outside the guard is discharged only by refuting the
   context, and a context with nothing arithmetic in it has no row to
   refute.  So the question is declined where it cannot be answered,
   which costs no inference at all -- not the assumption of the context
   the refutation attempt used to open with. *)
val _ =
  check
    ("an arithmetic-free context costs the solver no inference",
     fn () =>
       let
         val context = [Thm.ASSUME public_p]
         fun decline () =
           (linarithLib.clear_linarith_caches ();
            solver_declines context irrelevant_premise)
         val declined = decline ()
         val prims = counted (fn () => ignore (decline ()))
       in
         null (linarithData.arith_facts ()) andalso declined andalso
         prims = 0
       end)

(* The solver asks the first rung of the ladder only, and the cache
   records what it was asked.  What it records must not stand in for the
   disproof the conversion goes on to look for: the rungs are different
   questions and so different cache keys, and a rung the solver ran and
   lost leaves the other one to be asked. *)
val _ =
  check
    ("a solver failure does not cache away the conversion's disproof",
     fn () =>
       let
         val _ = linarithLib.clear_linarith_caches ()
         val context = [Thm.ASSUME public_x_lt_y]
         val disprovable = num_less public_y public_x
         val declined = solver_declines context disprovable
         val (left, right) =
           boolSyntax.dest_eq
             (Thm.concl (linarithLib.CACHED_LINARITH context disprovable))
       in
         declined andalso Term.aconv left disprovable andalso
         Term.aconv right boolSyntax.F
       end)

(* One decision asks for the same decompositions several times over: the
   result cache screens the goal, reads its atoms and those of every
   context theorem, and the procedure behind it screens the goal again.
   So a term is decomposed once and the answer remembered, which an
   instance counting the additions its destructor is asked to take apart
   states without reading the memo -- reaching the answer decomposes,
   and repeating the decision decomposes nothing further.  The count
   itself is not asserted: what is bounded is the growth, not the
   number of destructor calls one decision happens to make. *)
val plus_dest_calls = ref 0

val counting_dest_num_instance =
  let
    val dest = #dest num_instance
    fun dest_plus tm =
      (plus_dest_calls := !plus_dest_calls + 1; #dest_plus dest tm)
  in
    {ty = #ty num_instance,
     discrete = #discrete num_instance,
     dest =
       {dest_plus = dest_plus,
        dest_minus = #dest_minus dest,
        dest_neg = #dest_neg dest,
        dest_mult = #dest_mult dest,
        dest_div = #dest_div dest,
        dest_suc = #dest_suc dest,
        dest_lit = #dest_lit dest,
        mk_lit = #mk_lit dest,
        dest_less = #dest_less dest,
        dest_leq = #dest_leq dest},
     kit = #kit num_instance,
     norm_conv = #norm_conv num_instance,
     nnf_rules = #nnf_rules num_instance,
     pre_split = #pre_split num_instance,
     atom_facts = #atom_facts num_instance} :
       linarithData.linarith_instance
  end

val _ =
  check
    ("a repeated decision decomposes nothing further",
     fn () =>
       with_num_instances
         [(counting_dest_num_instance,
           fn () =>
             let
               val _ = linarithLib.clear_linarith_caches ()
               fun decided () =
                 (ignore
                    (linarithLib.CACHED_LINARITH
                       [Thm.ASSUME public_x_lt_y] public_successor_le_y);
                  true)
                 handle Feedback.HOL_ERR _ => false
               val _ = plus_dest_calls := 0
               val first = decided ()
               val after_first = !plus_dest_calls
               val repeats = List.all (fn _ => decided ()) [1, 2, 3]
             in
               first andalso repeats andalso 0 < after_first andalso
               !plus_dest_calls = after_first
             end)])

(* That memo is bounded, and bounded by discarding its table rather than
   by evicting from it: what it exists to hold is one decision's working
   set, and a session's worth of boolean subterms is not that.  So a
   decision far enough back is decomposed again rather than answered for,
   and answered the same way when it is.  The count that says so is the
   destructor's, read through the instance, so the bound is stated
   without reading the table it bounds. *)
val memo_overflow = 2500

fun bounded_probe i =
  num_leq
    (num_plus num_x (numSyntax.mk_numeral (Arbnum.fromInt i))) num_y

val _ =
  check
    ("the decomposition memo is bounded by discarding its table",
     fn () =>
       with_num_instances
         [(counting_dest_num_instance,
           fn () =>
             let
               val probe = bounded_probe 0
               val _ = ignore (linarithDecomp.decomp probe)
               val _ = plus_dest_calls := 0
               val remembered =
                 Option.isSome (linarithDecomp.decomp probe) andalso
                 !plus_dest_calls = 0
               fun fill i =
                 ignore (linarithDecomp.decomp (bounded_probe (i + 1)))
               val _ = List.app fill (List.tabulate (memo_overflow, Lib.I))
               val _ = plus_dest_calls := 0
               val again = linarithDecomp.decomp probe
             in
               remembered andalso Option.isSome again andalso
               0 < !plus_dest_calls
             end)])

(* The carrier half of preprocessing normalizes with the rules the
   registry holds and with the propositional set those rules' output
   asks for, and with nothing else.  Reading Rewrite.implicit_rewrites
   would add whatever theories a session had loaded -- and the rule is
   built once per registry state, so which of those states it froze
   would depend on when the first call happened.  The assertion is
   therefore about call order: a goal decided one way before a theory
   touches the implicit set is decided the same way after, whether or
   not a registry change has rebuilt the rule in between. *)
val empty_num_list = listSyntax.mk_list ([], numSyntax.num)

val empty_length_goal =
  num_leq (listSyntax.mk_length empty_num_list) num_zero

fun with_implicit_rewrites theorems operation =
  let
    val saved = Rewrite.implicit_rewrites ()
    fun restore () = Rewrite.set_implicit_rewrites saved
    val _ = Rewrite.add_implicit_rewrites theorems
    val result = operation () handle e => (restore (); raise e)
    val _ = restore ()
  in
    result
  end

val _ =
  check
    ("the carrier normalization reads no implicit rewrite set",
     fn () =>
       let
         (* LENGTH [] is an atom the arithmetic knows nothing about, and
            the rewrite that says it is 0 closes the goal.  This call
            also leaves the carrier rule built. *)
         val refused_before = linarith_fails empty_length_goal
       in
         refused_before andalso
         with_implicit_rewrites [listTheory.LENGTH]
           (fn () =>
              linarith_fails empty_length_goal andalso
              with_num_instances
                [(num_instance,
                  fn () => linarith_fails empty_length_goal)]) andalso
         linarith_fails empty_length_goal
       end)

(* An instance whose norm_conv fails is a malformed instance, and replay
   is where it is discovered: the search runs over rows of rationals and
   finds its certificate, and the failure comes of trying to state that
   certificate as theorems.  What the entry points must not do is report
   that as a refusal -- the goal is provable, the instance is at fault,
   and the message that says so is the only one that locates it. *)
val broken_norm_message = "deliberately broken norm_conv"

val broken_norm_instance =
  {ty = #ty num_instance,
   discrete = #discrete num_instance,
   dest = #dest num_instance,
   kit = #kit num_instance,
   norm_conv =
     fn _ =>
       raise Feedback.mk_HOL_ERR "linarithSelftest" "broken_norm_conv"
         broken_norm_message,
   nnf_rules = #nnf_rules num_instance,
   pre_split = #pre_split num_instance,
   atom_facts = #atom_facts num_instance} :
     linarithData.linarith_instance

fun error_of operation =
  ((operation (); NONE) handle Feedback.HOL_ERR error => SOME error)

val successor_implication =
  boolSyntax.mk_imp (public_x_lt_y, public_successor_le_y)

(* The instance's own message, verbatim: what an entry point may not do
   is replace it with a report that no proof was found. *)
fun reports_the_instance_failure operation =
  case error_of operation of
      NONE => false
    | SOME error => Feedback.message_of error = broken_norm_message

val _ =
  check
    ("a malformed instance surfaces its own failure, not a refusal",
     fn () =>
       with_num_instances
         [(num_instance,
           fn () =>
             valid_closes (linarithLib.LINARITH_TAC [])
               ([], successor_implication)),
          (broken_norm_instance,
           fn () =>
             reports_the_instance_failure
               (fn () =>
                  ignore
                    (linarithLib.LINARITH_PROVE successor_implication))
             andalso
             reports_the_instance_failure
               (fn () =>
                  ignore
                    (linarithLib.LINARITH_CONV successor_implication)))])

val malformed_cached_context = [Thm.ASSUME public_x_lt_y]
val malformed_cached_goal = public_successor_le_y

fun cached_reports_instance_failure () =
  reports_the_instance_failure
    (fn () =>
       ignore
         (linarithLib.CACHED_LINARITH malformed_cached_context
            malformed_cached_goal))

(* LINARITH_ss contains this reducer.  Drive it directly because the
   surrounding simplifier deliberately treats any dproc HOL_ERR as
   "this dproc made no rewrite". *)
fun reducer_reports_instance_failure () =
  reports_the_instance_failure
    (fn () =>
       ignore
         (reducer_conversion malformed_cached_context
            malformed_cached_goal))

fun solver_reports_instance_failure () =
  reports_the_instance_failure
    (fn () =>
       ignore
         (#solve linarithLib.linarith_solver
            {stack = [],
             context_thms = malformed_cached_context,
             recurse = Conv.NO_CONV} malformed_cached_goal))

fun with_broken_cache assertion =
  with_num_instances
    [(broken_norm_instance,
      fn () => (linarithLib.clear_linarith_caches (); assertion ()))]

(* RCACHE turns callback exceptions into negative answers internally.
   The linarith wrapper has to recover the diagnostic at each public
   cached surface and discard the negative entry RCACHE made for it, so
   a repeat must report the same instance failure too. *)
val _ =
  check
    ("CACHED_LINARITH preserves malformed-instance replay failures",
     fn () =>
       with_broken_cache
         (fn () =>
            cached_reports_instance_failure () andalso
            cached_reports_instance_failure ()))

val _ =
  check
    ("LINARITH_ss reducer preserves malformed-instance replay failures",
     fn () =>
       with_broken_cache reducer_reports_instance_failure)

val _ =
  check
    ("lin_arith solver preserves malformed-instance replay failures",
     fn () =>
       with_broken_cache solver_reports_instance_failure)

(* An interrupt is the caller asking the search to stop, not a
   diagnosis of anything, so no part of the cached channel may record
   it, replace it, or answer it with a refusal.  The failure this
   guards against is not hypothetical.  The slot that carries a
   malformed instance's error past RCACHE was consulted for every
   exception, so an interrupt raised anywhere the slot had not been
   filled came back out as [decline ""] -- a refusal.  A simplifier
   reads a refusal as "side condition not provable" and carries on,
   which left a budget unable to stop any search whose side conditions
   reach this solver.

   The instance below interrupts only on atoms mentioning one
   variable, and that variable sits in a context component of its own.
   RCACHE splits the context by connected component and tries them in
   turn, so the goal's component is decided first and declines --
   filling the slot -- and the interrupt then arrives with the slot
   already occupied.  That is the order the failure needs. *)
val interrupting_variable =
  Term.mk_var ("linarith_public_interrupting", numSyntax.num)

fun interrupting_dest () =
  let
    val inner = #dest num_instance
  in
    {dest_plus = #dest_plus inner, dest_minus = #dest_minus inner,
     dest_neg = #dest_neg inner, dest_mult = #dest_mult inner,
     dest_div = #dest_div inner, dest_suc = #dest_suc inner,
     dest_lit = #dest_lit inner, mk_lit = #mk_lit inner,
     dest_leq = #dest_leq inner,
     dest_less =
       fn tm =>
         if Term.free_in interrupting_variable tm then
           raise Portable.Interrupt
         else #dest_less inner tm}
  end

val interrupting_instance =
  {ty = #ty num_instance,
   discrete = #discrete num_instance,
   dest = interrupting_dest (),
   kit = #kit num_instance,
   norm_conv = #norm_conv num_instance,
   nnf_rules = #nnf_rules num_instance,
   pre_split = #pre_split num_instance,
   atom_facts = #atom_facts num_instance} :
     linarithData.linarith_instance

(* [x < y] does not decide [y <= x], so the goal's component declines
   before the interrupting component is reached. *)
val interrupt_context =
  [Thm.ASSUME public_x_lt_y,
   Thm.ASSUME (num_less interrupting_variable public_z)]

val interrupt_goal = num_leq public_y public_x

fun stops_on_interrupt call () =
  ((linarithLib.clear_linarith_caches ();
    call ();
    false)
   handle Portable.Interrupt => true
        | Feedback.HOL_ERR _ => false)

val _ =
  check
    ("the cached channel does not answer an interrupt with a refusal",
     fn () =>
       with_num_instances
         [(interrupting_instance,
           stops_on_interrupt
             (fn () =>
                ignore
                  (linarithLib.CACHED_LINARITH interrupt_context
                     interrupt_goal)))])

val _ =
  check
    ("the lin_arith solver does not answer an interrupt with a refusal",
     fn () =>
       with_num_instances
         [(interrupting_instance,
           stops_on_interrupt
             (fn () =>
                ignore
                  (#solve linarithLib.linarith_solver
                     {stack = [],
                      context_thms = interrupt_context,
                      recurse = Conv.NO_CONV}
                     interrupt_goal)))])

(* The [arith] table refutes nothing on its own, so a context with no
   arithmetic in it cannot be refuted with the table's help either, and
   the guard has to say so however many [arith] facts a session has
   declared.  Otherwise one declaration anywhere in the ancestry sends
   every non-arithmetic side condition of every conditional rewrite
   through a contradiction search that cannot succeed. *)
val _ =
  check
    ("declared [arith] facts do not open a bare context to the solver",
     fn () =>
       let
         val context = [Thm.ASSUME public_p]
         fun decline () =
           (linarithLib.clear_linarith_caches ();
            solver_declines context irrelevant_premise)
       in
         case with_arith_exports envelope_facts
                (fn () =>
                   let
                     val declared =
                       not (null (linarithData.arith_facts ()))
                     val declined = decline ()
                     val prims = counted (fn () => ignore (decline ()))
                   in
                     declared andalso declined andalso prims = 0
                   end) of
             NONE => false
           | SOME result => result
       end)

(* A failure names an entry point the caller who reads it can look up.
   The cached procedure behind this one is private, and named nowhere a
   caller could find it. *)
val _ =
  check
    ("CACHED_LINARITH reports its failure under its own name",
     fn () =>
       (linarithLib.clear_linarith_caches ();
        case error_of
               (fn () =>
                  ignore (linarithLib.CACHED_LINARITH [] public_x_le_y)) of
            NONE => false
          | SOME error =>
              Feedback.top_structure_of error = "linarithLib" andalso
              Feedback.top_function_of error = "CACHED_LINARITH" andalso
              String.isPrefix "linear arithmetic found no proof"
                (Feedback.message_of error)))

(* A tactic carrying Split arguments derives its rule set outside the
   shared memo, and the derivation still has to happen where the tactic
   is applied rather than where it is built: what the tactic value
   caches is one rule set per state of the registry and the
   [arith_split] table, not one for good. *)
val _ =
  check
    ("a hoisted Split tactic tracks the [arith_split] table",
     fn () =>
       let
         val hoisted =
           linarithLib.LINARITH_TAC [markerLib.Split public_bool_split]
         fun closes tm =
           valid_closes hoisted ([], tm)
           handle Feedback.HOL_ERR _ => false
         fun fails tm = tactic_fails hoisted ([], tm)
       in
         with_num_instances
           [(nnf_only_num_instance,
             fn () =>
               fails min_le_left andalso
               with_split_export linarithSeedTheory.NUM_MIN_SPLIT
                 (fn () => closes min_le_left) andalso
               fails min_le_left)]
       end)

(* The 34 num/bool goals among the 54 lemma goals in Isabelle's
   Arith_Examples.thy at f7e02b7e1f31, which linarithCorpus states along
   with the driver, the budgets and the canonical numbering.  The
   instances suite runs all 54 and checks that vendored total; running
   the core partition here is what puts the strength corpus where the
   num instance is built, and the numbering check below pins the list to
   the core subset of the numbering.

   On 2026-08-02 the full core selftest took 13.2s at level 2 versus
   12.2s at level 1 on an AMD Ryzen 9 9950X.  The 90s suite budget,
   30s goal budget, and 5s boundary budget leave ample headroom. *)

val _ =
  check_numbering
    {suite = "Arith_Examples core", numbering = core_numbering}
    core_arith_examples

val _ =
  if selftest_level () >= 2 then
    run_suite
      {suite = "Arith_Examples core",
       tactic = fn () => linarithLib.LINARITH_TAC [],
       suite_budget = Time.fromSeconds 90,
       expected_successes = 33,
       expected_boundaries = 1}
      core_arith_examples
  else ()

(* The guard the solver asks before spending a refutation search on a
   side condition it cannot decide directly answers out of a memo, so
   what has to hold is that the memo is keyed on everything the verdict
   reads: the context, which arrives with the call, and the registry
   generation, which the relevance test reads for itself.  The two
   tests below move one of those and hold the other, so a key missing
   either half serves the previous call's verdict here.

   The verdict is read off which of the three things the solver can do
   it did: prove the condition from a contradictory context, decline it
   for want of arithmetic, or attempt the refutation and fail.  The last
   two both raise, and the guard is the difference between them. *)
fun solver_verdict context tm =
  case error_of
         (fn () =>
            ignore
              (#solve linarithLib.linarith_solver
                 {stack = [],
                  context_thms = context,
                  recurse = Conv.NO_CONV} tm)) of
      NONE => "proved"
    | SOME error =>
        if Feedback.message_of error = "no arithmetic in the context"
        then "declined"
        else "searched"

val _ =
  check
    ("the refutable-context guard tracks the context, registry fixed",
     fn () =>
       let
         val contradictory = [Thm.ASSUME public_successor_bound]
         val bare = [Thm.ASSUME irrelevant_premise]
         fun verdict context = solver_verdict context public_p
       in
         [verdict contradictory, verdict bare,
          verdict contradictory, verdict bare] =
         ["proved", "declined", "proved", "declined"]
       end)

(* A carrier of its own, registered nowhere else, so that the context
   term below is arithmetic-free until the registration and carries a
   subterm at a registered type after it -- with the context list, and
   the theorem in it, the same objects across both calls. *)
val guard_ty = Type.mk_type ("fun", [Type.bool, registry_ty])

val guard_atom = Term.mk_var ("linarith_guard_atom", guard_ty)
val guard_predicate =
  Term.mk_var ("linarith_guard_predicate", function_ty guard_ty Type.bool)
val guard_premise = Term.mk_comb (guard_predicate, guard_atom)

val guard_instance : linarithData.linarith_instance =
  {ty = guard_ty,
   discrete = NONE,
   dest =
     {dest_plus = decline,
      dest_minus = NONE,
      dest_neg = NONE,
      dest_mult = decline,
      dest_div = NONE,
      dest_suc = NONE,
      dest_lit = decline,
      mk_lit = decline,
      dest_less = decline,
      dest_leq = decline},
   kit =
     {add_mono = [],
      mult_mono = [],
      not_less = boolTheory.TRUTH,
      not_le = boolTheory.TRUTH,
      neqE = boolTheory.TRUTH,
      nonneg = (fn _ => NONE)},
   norm_conv = Conv.ALL_CONV,
   nnf_rules = [],
   pre_split = [],
   atom_facts = (fn _ => [])}

val _ =
  check
    ("the refutable-context guard tracks the registry, context fixed",
     fn () =>
       let
         val context = [Thm.ASSUME guard_premise]
         val unregistered = solver_verdict context public_p
         val _ = linarithData.register_instance guard_instance
         val registered = solver_verdict context public_p
       in
         unregistered = "declined" andalso registered = "searched"
       end)

(* A conversion closure may revisit a carrier through a different
   injection, but doing so only nests the conversions around the same
   arithmetic and admits an infinite num -> synth -> num path.  This
   sits last because the two test-only registrations are session state;
   replay proves that both directions are usable. *)
val cycle_num_to_synth =
  Term.mk_var
    ("linarith_cycle_num_to_synth",
     function_ty numSyntax.num registry_ty)
val cycle_synth_to_num =
  Term.mk_var
    ("linarith_cycle_synth_to_num",
     function_ty registry_ty numSyntax.num)

fun assumed_lift variables premise conclusion =
  Thm.ASSUME
    (boolSyntax.list_mk_forall
       (variables, boolSyntax.mk_imp (premise, conclusion)))

val cycle_num_synth_rule =
  assumed_lift
    [public_x, public_y] public_x_le_y
    (mk_binary synth_leq
       (Term.mk_comb (cycle_num_to_synth, public_x))
       (Term.mk_comb (cycle_num_to_synth, public_y)))
val cycle_synth_num_rule =
  assumed_lift
    [synth_x, synth_y] (mk_binary synth_leq synth_x synth_y)
    (num_leq
       (Term.mk_comb (cycle_synth_to_num, synth_x))
       (Term.mk_comb (cycle_synth_to_num, synth_y)))

val _ =
  check
    ("conversion closure terminates across cyclic injections",
     fn () =>
       let
         fun register from_ty to_ty inj rule =
           linarithData.register_injection
             {from_ty = from_ty, to_ty = to_ty, inj = inj,
              hom =
                 {le = rule, lt = rule, eq = rule,
                  add = boolTheory.TRUTH, mul = boolTheory.TRUTH}}
         val _ =
           register numSyntax.num registry_ty cycle_num_to_synth
             cycle_num_synth_rule
         val _ =
           register registry_ty numSyntax.num cycle_synth_to_num
             cycle_synth_num_rule
         val left = mk_binary synth_leq synth_x synth_y
       in
         (ignore
            (linarithReplay.mkthm traceUtil.silent
               [Thm.ASSUME left, Thm.ASSUME public_x_le_y]
               (Added (Asm 0, Asm 1)));
          false)
         handle Feedback.HOL_ERR error =>
           Feedback.message_of error =
             "Linear arithmetic should have refuted the assumptions " ^
             "but failed to."
       end)

(* The tactic reads linarith.trace from the context it is applied in.
   The elimination asks for the level at every pivot, so an ambient read
   would show in the census of a proof the search closes. *)
val _ =
  check
    ("SIMPLE_LINARITH_TAC reads its traces from its context",
     fn () =>
       let
         val warnings = ref ([] : string list)
         val goal =
           ([num_less public_x public_y],
            num_leq (num_plus public_x num_one) public_y)
         val ctxt = Context.snapshot ()
         fun run () =
           (Context.set_ambient_report_level 2;
            Lib.with_flag
              (Feedback.WARNING_outstream,
               fn s => warnings := s :: !warnings)
              (Context.in_proof
                 (fn () => linarithLib.SIMPLE_LINARITH_TAC [] goal ctxt))
              ())
         val (residues, _) =
           Portable.finally (fn () => Context.set_ambient_report_level 1)
                            run ()
       in
         null residues andalso
         not (List.exists
                (fn w => String.isSubstring "(linarith.trace)" w orelse
                         String.isSubstring "(Rewrite.monitoring)" w)
                (!warnings))
       end)

(* The fact-taking constructors use exactly the facts given, while the
   context-free ones read the global table each time they run.  The goal
   needs the nonlinear fact, so it separates the two. *)
fun ext_closes fragment goal =
  (linarithLib.clear_linarith_caches ();
   valid_closes
     (simpLib.FULL_SIMP_TAC
        (simpLib.++ (simpLib.empty_ss, fragment)) [])
     goal)
  handle Feedback.HOL_ERR _ => false

fun solver_proves (solver : Traverse.ssolver) context_thms tm =
  (ignore
     (#solve solver
        {stack = [],
         context_thms = context_thms, recurse = Conv.NO_CONV} tm);
   true)
  handle Feedback.HOL_ERR _ => false

val _ =
  check
    ("LINARITH_ext_ss_with uses the given facts, not the global table",
     fn () =>
       let
         val goal = ([], nonlinear_closed_goal)
         val without_fact =
           ext_closes (linarithLib.LINARITH_ext_ss_with []) goal
       in
         not without_fact andalso
         with_arith_export
           (fn () =>
              not (ext_closes (linarithLib.LINARITH_ext_ss_with []) goal)
              andalso
              ext_closes
                (linarithLib.LINARITH_ext_ss_with [nonlinear_closed_fact])
                goal)
         andalso
         ext_closes
           (linarithLib.LINARITH_ext_ss_with [nonlinear_closed_fact])
           goal
       end)

val _ =
  check
    ("linarith_solver_with_facts uses the given facts, not the global table",
     fn () =>
       let
         val tm = nonlinear_closed_goal
         val none = linarithLib.linarith_solver_with_facts []
         val given =
           linarithLib.linarith_solver_with_facts [nonlinear_closed_fact]
         val _ = linarithLib.clear_linarith_caches ()
       in
         not (solver_proves none [] tm) andalso
         with_arith_export
           (fn () =>
              (linarithLib.clear_linarith_caches ();
               not (solver_proves none [] tm)) andalso
              solver_proves given [] tm) andalso
         solver_proves given [] tm
       end)

val _ =
  check
    ("a fixed-fact solver follows changes to its caller's context",
     fn () =>
       let
         val solver = linarithLib.linarith_solver_with_facts [boolTheory.TRUTH]
         val target = ``(fixed_context_x:num) <= fixed_context_y``
         val context = [Thm.ASSUME target]
         val other = [Thm.ASSUME ``(fixed_context_x:num) <= fixed_context_z``]
         fun supported () =
           let
             val theorem = #solve solver
               {stack = [], context_thms = context, recurse = Conv.NO_CONV}
               target
           in
             Term.aconv (Thm.concl theorem) target andalso
             Lib.list_eq Term.aconv (Thm.hyp theorem) [target]
           end
       in
         supported () andalso not (solver_proves solver other target)
         andalso supported ()
       end)

val _ =
  check
    ("the context-free LINARITH_ext_ss and solver read the table per run",
     fn () =>
       let
         val goal = ([], nonlinear_closed_goal)
         val fragment = linarithLib.LINARITH_ext_ss
         val solver = linarithLib.linarith_solver
         val without_fact =
           ext_closes fragment goal orelse solver_proves solver [] (#2 goal)
       in
         not without_fact andalso
         with_arith_export
           (fn () =>
              ext_closes fragment goal andalso
              (linarithLib.clear_linarith_caches ();
               solver_proves solver [] (#2 goal))) andalso
         not (ext_closes fragment goal)
       end)

val _ =
  check
    ("the fact constructors name their fragment and solver as exported",
     fn () =>
       linarithLib.linarith_fragment_name = "LINARITH" andalso
       linarithLib.linarith_solver_name = "lin_arith" andalso
       simpLib.frag_name (linarithLib.LINARITH_ext_ss_with []) =
         SOME linarithLib.linarith_fragment_name andalso
       simpLib.frag_name linarithLib.LINARITH_ext_ss =
         SOME linarithLib.linarith_fragment_name andalso
       #name linarithLib.linarith_solver =
         linarithLib.linarith_solver_name andalso
       #name (linarithLib.linarith_solver_with_facts []) =
         linarithLib.linarith_solver_name)
