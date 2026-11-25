structure linarithSolve :> linarithSolve =
struct

val ERR = Feedback.mk_HOL_ERR "linarithSolve"

(* Nonneg generalizes upstream Nat (fast_lin_arith.ML:191-202). *)
datatype lineq_type = Eq | Le | Lt

datatype injust =
    Asm of int
  | Nonneg of Term.term
  | LessD of injust
  | NotLessD of injust
  | NotLeD of injust
  | NotLeDD of injust
  | Multiplied of Arbint.int * injust
  | Added of injust * injust

datatype lineq =
  Lineq of Arbint.int * lineq_type * Arbint.int list * injust

type linarith_config = linarithData.linarith_config

(* The meter the search charges, and the linarith.trace level it
   reports at. *)
type work =
  {meter : searchBudget.charger, metered : bool, level : traceUtil.level}

fun free_work level : work =
  {meter = searchBudget.free_charger, metered = false, level = level}

fun budget_work budget level : work =
  {meter = searchBudget.charger budget, metered = true, level = level}

fun candidate (work : work) = #candidate (#meter work) ()
fun application (work : work) = #application (#meter work) ()
fun normalization (work : work) = #normalization (#meter work) ()

(* Relations and negation are structured rather than upstream strings
   (fast_lin_arith.ML:510-541). *)
datatype relation = REL_LE | REL_LT | REL_EQ | REL_NEQ

datatype decomp = Decomp of {
  lhs : (Term.term * Arbrat.rat) list,
  lhs_const : Arbrat.rat,
  rel : relation,
  rhs : (Term.term * Arbrat.rat) list,
  rhs_const : Arbrat.rat,
  discrete : bool,
  negated : bool
}

type int_decomp = {
  lhs : (Term.term * Arbint.int) list,
  lhs_const : Arbint.int,
  rel : relation,
  rhs : (Term.term * Arbint.int) list,
  rhs_const : Arbint.int,
  discrete : bool,
  negated : bool
}

val zero = Arbint.zero
val one = Arbint.one
val negone = Arbint.~ one

fun ai_eq x y = x = y
fun ai_zero x = ai_eq x zero
fun ai_one x = ai_eq x one
fun ai_neg x = Arbint.< (x, zero)
fun ai_pos x = Arbint.> (x, zero)

fun find_add_type (Eq, ty) = ty
  | find_add_type (ty, Eq) = ty
  | find_add_type (_, Lt) = Lt
  | find_add_type (Lt, _) = Lt
  | find_add_type (Le, Le) = Le

(* Scaling a row that is already scaled composes the two literals rather
   than nesting the justifications.  mklineq scales by a denominator LCM
   and elimination then scales that row again, so the nested form would
   reach replay as t * 2 * 3 and leave every instance's norm_conv obliged
   to recognize it as the t * 6 on the other side. *)
fun mk_multiplied n just =
  if ai_one n then just
  else
    case just of
        Multiplied (m, inner) => mk_multiplied (Arbint.* (n, m)) inner
      | _ => Multiplied (n, just)

fun scale_row n ty =
  if ai_one n then Lib.I
  else if ai_zero n andalso ty = Lt then
    raise ERR "multiply_ineq" "zero multiplier on a strict inequality"
  else if ai_neg n andalso (ty = Le orelse ty = Lt) then
    raise ERR "multiply_ineq" "negative multiplier on an inequality"
  else fn c => Arbint.* (n, c)

fun elim_var_with (work : work) drop_column
      (Lineq (k1, ty1, coeffs1, just1), c1)
      (Lineq (k2, ty2, coeffs2, just2), c2) =
  let
    val a1 = Arbint.abs c1
    val a2 = Arbint.abs c2
    (* Both pivot coefficients are nonzero. LCM(a1,a2)/a1 = a2/GCD(a1,a2). *)
    val (m1, m2) =
      if ai_eq a1 a2 then (one, one)
      else if ai_one a1 then (a2, one)
      else if ai_one a2 then (one, a1)
      else
        let val gcd = Arbint.gcd (a1, a2)
        in (Arbint.div (a2, gcd), Arbint.div (a1, gcd)) end
    val (n1, n2) =
      if ai_neg c1 = ai_neg c2 then
        if ty1 = Eq then (Arbint.~ m1, m2)
        else if ty2 = Eq then (m1, Arbint.~ m2)
        else raise ERR "elim_var" "no eliminable coefficient pair"
      else (m1, m2)
    val (p1, p2) =
      if ty1 = Eq andalso ty2 = Eq andalso
         (ai_eq n1 negone orelse ai_eq n2 negone)
      then (Arbint.~ n1, Arbint.~ n2)
      else (n1, n2)
    val scale1 = scale_row p1 ty1
    val scale2 = scale_row p2 ty2
    val coeffs =
      if #metered work then
        (* Charge the two scaling passes before charging the addition. *)
        let
          fun scale factor times cs =
            if ai_one factor then cs
            else List.map (fn c => (candidate work; times c)) cs
        in
          ListPair.mapEq (fn pair => (candidate work; Arbint.+ pair))
            (scale p1 scale1 coeffs1, scale p2 scale2 coeffs2)
        end
      else
        let
          (* Sparse rows still occupy every column in the coefficient list. *)
          fun add (a, b) =
            if ai_zero a then
              if ai_zero b then zero else scale2 b
            else if ai_zero b then scale1 a
            else Arbint.+ (scale1 a, scale2 b)
        in
          ListPair.mapEq add
            (if drop_column then (List.tl coeffs1, List.tl coeffs2)
             else (coeffs1, coeffs2))
        end
  in
    Lineq (Arbint.+ (scale1 k1, scale2 k2), find_add_type (ty1, ty2),
           coeffs, Added (mk_multiplied p1 just1, mk_multiplied p2 just2))
  end

fun is_trivial_with work (Lineq (_, _, coeffs, _)) =
  List.all (fn c => (candidate work; ai_zero c)) coeffs

fun is_contradictory (Lineq (k, ty, _, _)) =
  case ty of
      Eq => not (ai_zero k)
    | Le => ai_pos k
    | Lt => Arbint.>= (k, zero)

(* The equation pivot is a coefficient of least magnitude among the
   nonzero entries of the equations; ties go to the one met first in
   row-then-column order.  A unit coefficient
   wins immediately in the unmetered scan.

   NONE means no equation has a nonzero coefficient.  elim reaches
   this only with nontrivial rows, so that is exactly "no equations",
   and the caller's inequality branch is what NONE asks for. *)
fun pivot_equation_with (work : work) rows =
  let
    exception UnitPivot of int * int * Arbint.int
    fun in_row _ _ [] best = best
      | in_row i j (c :: cs) best =
          let
            val _ = candidate work
            val magnitude = Arbint.abs c
            val _ =
              if not (#metered work) andalso ai_one magnitude then
                raise UnitPivot (i, j, c)
              else ()
            val best' =
              if ai_zero c then best
              else
                case best of
                    NONE => SOME (i, j, c, magnitude)
                  | SOME (_, _, _, m) =>
                      if Arbint.< (magnitude, m) then
                        SOME (i, j, c, magnitude)
                      else best
          in
            in_row i (j + 1) cs best'
          end
    fun over_rows _ [] best = best
      | over_rows i (Lineq (_, _, coeffs, _) :: rest) best =
          (candidate work;
           over_rows (i + 1) rest (in_row i 0 coeffs best))
    (* Splitting the pivot row out by index leaves the other equations
       in their original order, as Lib.pluck did. *)
    fun split _ [] _ = NONE
      | split 0 (row :: rest) prefix =
          SOME (row, List.revAppend (prefix, rest))
      | split i (row :: rest) prefix =
          (candidate work; split (i - 1) rest (row :: prefix))
    fun located (i, j, c, _) =
      Option.map (fn (row, others) => (j, (row, c), others))
        (split i rows [])
  in
    Option.mapPartial located
      (over_rows 0 rows NONE
       handle UnitPivot (i, j, c) => SOME (i, j, c, one))
  end

(* Keep each dependent row's coefficient for the sign partition and
   for every elimination pair that uses that row. *)
fun partition_pivot_with work v drop_column rows =
  let
    fun split (row as Lineq (k, ty, cs, just), (independent, dependent)) =
      let
        val _ = candidate work
        val c = List.nth (cs, v)
      in
        if ai_zero c then
          let
            val remaining =
              if drop_column then Lineq (k, ty, List.tl cs, just)
              else row
          in
            (remaining :: independent, dependent)
          end
        else (independent, (row, c) :: dependent)
      end
    val (independent, dependent) = List.foldl split ([], []) rows
  in
    (List.rev independent, List.rev dependent)
  end

(* Count positive and negative entries in row-then-column order.
   Packed counters avoid allocating a reference pair per column and
   walking a second list during each row scan. *)
fun choose_blowup_with work [] = NONE
  | choose_blowup_with work (rows as Lineq (_, _, first, _) :: _) =
      let
        (* Preserve the metered row visits before scanning coefficients. *)
        val _ =
          if #metered work then List.app (fn _ => candidate work) rows
          else ()
        val width = List.length first
        val positives = Array.array (width, 0)
        val negatives = Array.array (width, 0)
        fun tally i [] =
              if i = width then () else raise ListPair.UnequalLengths
          | tally i (c :: cs) =
              if i = width then raise ListPair.UnequalLengths
              else
                (candidate work;
                 if ai_pos c then
                   Array.update (positives, i, Array.sub (positives, i) + 1)
                 else if ai_neg c then
                   Array.update (negatives, i, Array.sub (negatives, i) + 1)
                 else ();
                 tally (i + 1) cs)
        (* Choose the smallest nonzero product, favouring earlier columns. *)
        fun pick i best =
          if i = width then best
          else
            let
              val _ = candidate work
              val blow = Array.sub (positives, i) * Array.sub (negatives, i)
              val next =
                if blow = 0 then best
                else
                  case best of
                      NONE => SOME (blow, i)
                    | SOME (old, _) =>
                        if blow < old then SOME (blow, i) else best
            in
              pick (i + 1) next
            end
      in
        List.app (fn Lineq (_, _, cs, _) => tally 0 cs) rows;
        pick 0 NONE
      end

(* Eliminating a variable emits |pos| x |neg| rows per round, and the same
   row is reachable along many paths; without this the set grows
   geometrically while the distinct rows stay few. *)
fun row_key (Lineq (k, ty, coeffs, _)) =
  (case ty of Eq => 0 | Le => 1 | Lt => 2, k, coeffs)

fun compare_key ((ty1, k1, cs1), (ty2, k2, cs2)) =
  case Int.compare (ty1, ty2) of
      EQUAL =>
        (case Arbint.compare (k1, k2) of
             EQUAL => Lib.list_compare Arbint.compare (cs1, cs2)
           | order => order)
    | order => order

datatype elimination_result = Rows of lineq list | Contradiction of injust

(* Independent rows are already nontrivial. Derived rows are examined in
   their original order, so a constant contradiction can stop the scan. *)
fun eliminate_equation work drop_column pivot independent dependent =
  let
    fun derive row =
      (application work; elim_var_with work drop_column pivot row)
    fun collect kept [] = Rows (List.revAppend (kept, independent))
      | collect kept (row :: rest) =
          let val derived as Lineq (_, _, _, just) = derive row
          in
            if is_trivial_with work derived then
              if is_contradictory derived then Contradiction just
              else collect kept rest
            else collect (derived :: kept) rest
          end
  in
    if #metered work then Rows (List.map derive dependent @ independent)
    else collect [] dependent
  end

fun eliminate_pairs (work : work) drop_column independent pos neg =
  let
    fun derive p n =
      (application work; elim_var_with work drop_column p n)

    (* Abort a duplicate insertion before rebuilding the tree path.
       Keep the row and justification first encountered. *)
    exception DuplicateRow
    fun duplicate _ = raise DuplicateRow
    fun keep (row, acc as (seen, rev_rows)) =
      (Redblackmap.insertWith duplicate (seen, row_key row, ()),
       row :: rev_rows)
      handle DuplicateRow => acc
    fun finish (_, rev_rows) = Rows (List.rev rev_rows)
    fun positives [] kept = finish kept
      | positives (p :: ps) kept = negatives p ps neg kept
    and negatives p ps [] kept = positives ps kept
      | negatives p ps (n :: ns) kept =
          let val row as Lineq (_, _, _, just) = derive p n
          in
            (* Independent rows are already nontrivial. Classify each
               new row before indexing it, so constant rows need neither
               a key nor another pass at the start of the next round. *)
            if is_trivial_with work row then
              if is_contradictory row then Contradiction just
              else negatives p ps ns kept
            else negatives p ps ns (keep (row, kept))
          end
  in
    if #metered work then
      (* Charge all row applications before any key comparisons, as
         callers with limited budgets can observe the cutoff order. *)
      let
        val derived = List.map (fn p => List.map (derive p) neg) pos
        fun keep (row, acc as (seen, rev_rows)) =
          let val key = row_key row
          in
            if HOLset.member (seen, key) then acc
            else (HOLset.add (seen, key), row :: rev_rows)
          end
        val empty =
          (HOLset.empty (fn pair => (candidate work; compare_key pair)), [])
      in
        finish (List.foldl (fn (rows, kept) => List.foldl keep kept rows)
          (List.foldl keep empty independent) derived)
      end
    else
      positives pos (List.foldl keep (Redblackmap.mkDict compare_key, [])
        independent)
  end

(* Elimination traces one line per pivot, so the message is built only
   once the level has asked for it. *)
fun trace (work : work) message = traceUtil.trace (#level work) 2 message

(* SOME just is a refutation of the rows; NONE is elimination run to a
   system with no eliminable column left, which is the rows failing to
   refute rather than the search giving up early. *)
fun elim_rows_with (work : work) offset nontrivial ineqs =
  let
    val (triv, nontriv) =
      if nontrivial then ([], ineqs)
      else
        List.partition
          (fn row => (candidate work; is_trivial_with work row)) ineqs
    fun report_pivot kind v =
      trace work (fn () => kind ^ " pivot " ^ Int.toString (offset + v))
    (* A leading pivot becomes zero in every remaining row and can be
       dropped without copying any independent coefficient list. Keep
       interior columns and the original metered scans. *)
    fun drop_leading v = v = 0 andalso not (#metered work)
    fun next drop_column =
      elim_rows_with work (if drop_column then offset + 1 else offset)
    fun pivot () =
      let
        val (eqs, noneqs) =
          List.partition
            (fn Lineq (_, ty, _, _) =>
              (candidate work; ty = Eq)) nontriv
      in
        case pivot_equation_with work eqs of
            SOME (v, eq, other_eqs) =>
              let
                val drop_column = drop_leading v
                val (independent, dependent) =
                  partition_pivot_with work v drop_column (other_eqs @ noneqs)
                val result =
                  eliminate_equation work drop_column eq independent dependent
              in
                report_pivot "equation" v;
                case result of
                    Rows rows => next drop_column (not (#metered work)) rows
                  | Contradiction just => SOME just
              end
          | NONE =>
              (case choose_blowup_with work noneqs of
                 NONE => NONE
               | SOME (_, v) =>
                   let
                     val drop_column = drop_leading v
                     val (independent, dependent) =
                       partition_pivot_with work v drop_column nontriv
                     val (pos, neg) =
                       List.partition
                         (fn (_, c) => (candidate work; ai_pos c))
                         dependent
                   in
                     report_pivot "inequality" v;
                     case eliminate_pairs work drop_column
                            independent pos neg of
                         Rows rows =>
                           next drop_column (not (#metered work)) rows
                       | Contradiction just => SOME just
                   end)
      end
  in
    case List.find (fn row => (candidate work; is_contradictory row)) triv of
        SOME (Lineq (_, _, _, just)) => SOME just
      | NONE =>
        (* The metered path retains the original classification charges. *)
        if #metered work andalso not (List.null triv) then
          elim_rows_with work offset false nontriv
        else if List.null nontriv then NONE
        else pivot ()
  end

fun elim_with work rows = elim_rows_with work 0 false rows

fun scale m rat =
  let
    val n = Arbrat.numerator rat
  in
    (* When the common denominator is one, all coefficients are integral. *)
    if ai_one m then n
    else
      let
        val d = Arbrat.denominator rat
      in
        if d = Arbnum.one then Arbint.* (n, m)
        else Arbint.* (n, Arbint.div (m, Arbint.fromNat d))
      end
  end

fun common_denominator lhs lhs_const rhs rhs_const =
  let
    fun include_denominator (rat, acc) =
      let val denominator = Arbrat.denominator rat
      in
        if denominator = Arbnum.one then acc
        else
          let val d = Arbint.fromNat denominator
          in
            if ai_one acc orelse ai_eq acc d then d
            else Arbint.lcm (acc, d)
          end
      end
    fun include_coefficient ((_, c), acc) = include_denominator (c, acc)
    val constants = include_denominator (rhs_const,
                      include_denominator (lhs_const, one))
  in
    List.foldl include_coefficient
      (List.foldl include_coefficient constants lhs) rhs
  end

(* Termtab is keyed on Term.compare, whose EQUAL is exactly Term.aconv
   (both ignore a bound variable's name and compare its type), so the
   index classifies atoms the same way the linear search it replaces
   did. *)
type atom_index = {width : int, column : int Termtab.table}

fun atom_index_with work atoms =
  let
    fun add (atom, (i, columns)) =
      (candidate work; (i + 1, Termtab.update (atom, i) columns))
    val (width, columns) =
      List.foldl add (0, Termtab.empty) atoms
  in
    {width = width, column = columns}
  end

(* Scattering the polynomial into its columns costs
   O(A + |poly| * log A), against the O(A * |poly|) of one linear
   search of the polynomial per column.  Atoms outside the index have
   no column and are dropped, as they were by mapping over the atom
   list.  The entries are placed back to front so that the first
   occurrence of a repeated atom wins, as List.find did. *)
fun scatter_with work ({width, column} : atom_index) m poly =
  let
    val row = Array.array (width, zero)
    fun place (tm, c) =
      (candidate work;
       case Termtab.lookup column tm of
          NONE => ()
        | SOME i => Array.update (row, i, scale m c))
  in
    List.app place (List.rev poly); row
  end

datatype coefficient =
    Absent
  | LeftCoefficient of Arbint.int
  | Difference of Arbint.int

fun differences ({width, column} : atom_index) m lhs rhs =
  let
    val coefficients = Array.array (width, Absent)
    fun place insert (tm, c) =
      case Termtab.lookup column tm of
          NONE => ()
        | SOME i => insert i c (Array.sub (coefficients, i))
    fun left i c Absent =
          Array.update (coefficients, i, LeftCoefficient (scale m c))
      | left _ _ _ = ()
    fun right _ _ (Difference _) = ()
      | right i c (LeftCoefficient l) =
          Array.update
            (coefficients, i, Difference (Arbint.- (scale m c, l)))
      | right i c Absent =
          Array.update (coefficients, i, Difference (scale m c))
    fun coefficient i =
      case Array.sub (coefficients, i) of
          Absent => zero
        | LeftCoefficient c => Arbint.~ c
        | Difference c => c
  in
    (* Read each side in occurrence order. Its first entry for a column
       wins, and only columns on both sides need a subtraction. *)
    List.app (place left) lhs;
    List.app (place right) rhs;
    List.tabulate (width, coefficient)
  end

fun differences_with (work : work) index m reverse lhs rhs =
  if #metered work then
    let
      val lhs_coeffs = scatter_with work index m lhs
      val rhs_coeffs = scatter_with work index m rhs
      val (left, right) =
        if reverse then (rhs_coeffs, lhs_coeffs)
        else (lhs_coeffs, rhs_coeffs)
    in
      List.tabulate
        (#width index,
         fn i =>
            (candidate work; Arbint.- (Array.sub (right, i),
                                       Array.sub (left, i))))
    end
  else if reverse then differences index m rhs lhs
  else differences index m lhs rhs

fun mklineq_with work index
      (Decomp {lhs, lhs_const, rel, rhs, rhs_const, discrete, negated},
       asm_index) =
  let
    val _ = normalization work
    val m = common_denominator lhs lhs_const rhs rhs_const
    val reverse = negated andalso (rel = REL_LE orelse rel = REL_LT)
    val diff = differences_with work index m reverse lhs rhs
    val c = Arbint.- (scale m lhs_const, scale m rhs_const)
    val just = Asm asm_index
    fun lineq (constant, ty, cs, why) =
      Lineq (constant, ty, cs, mk_multiplied m why)
  in
    case (rel, negated) of
        (REL_LE, false) => lineq (c, Le, diff, just)
      (* The strengthening steps below add one to the *unscaled*
         assumption -- lineq attaches the scaling by m outside them, and
         replay executes them in that order -- so the constant they
         contribute to a row whose other constants have already been
         multiplied by m is m, not 1.  Using 1 built a row weaker than
         its own justification by m - 1, which costs no soundness but
         loses refutations of discrete systems the certificate would
         have justified. *)
      | (REL_LE, true) =>
          if discrete then
            lineq (Arbint.- (m, c), Le, diff,
                   NotLeDD just)
          else
            lineq (Arbint.~ c, Lt, diff, NotLeD just)
      | (REL_LT, false) =>
          if discrete then
            lineq (Arbint.+ (c, m), Le, diff, LessD just)
          else lineq (c, Lt, diff, just)
      | (REL_LT, true) =>
          lineq (Arbint.~ c, Le, diff, NotLessD just)
      (* The two equational relations arrive unnegated -- see the
         invariant on decomp in linarithSolve.sig -- so each is one
         arm, not two. *)
      | (REL_EQ, _) => lineq (c, Eq, diff, just)
      | (REL_NEQ, _) => raise ERR "mklineq" "unsplit disequality"
  end

(* Nonneg is the registry-extensible replacement for upstream mknat
   (fast_lin_arith.ML:549-553). *)
fun mknonneg width (index, atom) =
  Lineq (zero, Le,
         List.tabulate (width, fn i => if i = index then one else zero),
         Nonneg atom)

fun is_neq (Decomp {rel, ...}) = rel = REL_NEQ

fun is_discrete (Decomp {discrete, ...}) = discrete

fun less_decomp (Decomp {lhs, lhs_const, rhs, rhs_const,
                          discrete, ...}) =
  Decomp {lhs = lhs, lhs_const = lhs_const, rel = REL_LT,
          rhs = rhs, rhs_const = rhs_const, discrete = discrete,
          negated = false}

fun swap_less (Decomp {lhs, lhs_const, rhs, rhs_const,
                        discrete, ...}) =
  Decomp {lhs = rhs, lhs_const = rhs_const, rel = REL_LT,
          rhs = lhs, rhs_const = lhs_const, discrete = discrete,
          negated = false}

(* Unlike upstream's neqE-list ordering, each premise is discriminated by
   the discreteness its own decomposition carries
   (fast_lin_arith.ML:574-629). *)
fun fold_neq_pass_with work discrete_only visit state items =
  let
    (* Chosen branches are appended after the unprocessed premises. *)
    fun pass reversed state [] [] = visit (List.rev reversed) state
      | pass reversed state [] queued =
          pass reversed state (List.rev queued) []
      | pass reversed state ((item as (tm, decoded)) :: rest) queued =
          (candidate work;
           case decoded of
               SOME decomp =>
                 if is_neq decomp andalso
                    (not discrete_only orelse is_discrete decomp)
                 then
                   (application work;
                    case pass reversed state rest
                           ((tm, SOME (less_decomp decomp)) :: queued) of
                        NONE => NONE
                      | SOME next =>
                          (application work;
                           pass reversed next rest
                             ((tm, SOME (swap_less decomp)) :: queued)))
                 else pass (item :: reversed) state rest queued
             | NONE => pass (item :: reversed) state rest queued)
  in
    pass [] state items []
  end

fun elim_neq_with work items =
  let
    fun cases discrete_only items =
      List.rev (valOf (fold_neq_pass_with work discrete_only
        (fn one => fn reversed => SOME (one :: reversed)) [] items))
  in
    List.concat (List.map (cases false) (cases true items))
  end

fun ignore_neq_with work (tm, NONE) =
      (candidate work; (tm, NONE))
  | ignore_neq_with work (tm, SOME decomp) =
      (candidate work;
       if is_neq decomp then (tm, NONE) else (tm, SOME decomp))

fun number_hyps_with work items =
  let
    fun number _ [] = []
      | number n ((_, NONE) :: rest) =
          (candidate work; number (n + 1) rest)
      | number n ((_, SOME decomp) :: rest) =
          (candidate work;
           (decomp, n) :: number (n + 1) rest)
  in
    number 0 items
  end

fun split_items_with work split_neq items =
  let
    val cases =
      if split_neq then elim_neq_with work items
      else [List.map (ignore_neq_with work) items]
  in
    List.map (fn one => (candidate work; number_hyps_with work one)) cases
  end

(* Coefficient rows follow this order, so every row built for one
   split system must come from this one function. *)
fun atoms_of_decomps_with work decomps =
  let
    fun sides (Decomp {lhs, rhs, ...}) =
      List.map (fn (tm, _) => (candidate work; tm)) (lhs @ rhs)
  in
    listUtil.distinct_by
      (fn pair => (candidate work; Term.compare pair)) Lib.I
      (List.concat (List.map sides decomps))
  end

(* Collecting atoms reports nothing, so no level is asked for. *)
fun atoms_of_decomps decomps =
  atoms_of_decomps_with (free_work traceUtil.silent) decomps

(* The column table can also detect repeated atoms. Assign columns
   as they first appear, with the same left-before-right order used
   by atoms_of_decomps. *)
fun indexed_atoms items =
  let
    fun add ((atom, _), state as (i, columns, atoms)) =
      if Termtab.defined columns atom then state
      else (i + 1, Termtab.update (atom, i) columns, atom :: atoms)
    fun collect ((Decomp {lhs, rhs, ...}, _), state) =
      List.foldl add (List.foldl add state lhs) rhs
    val (width, columns, atoms) =
      List.foldl collect (0, Termtab.empty, []) items
  in
    (List.rev atoms, {width = width, column = columns})
  end

fun refute_system_with (work : work) is_nonnegative items justs =
  let
    val (atoms, index) =
      if #metered work then
        let
          val atoms = atoms_of_decomps_with work
            (List.map (fn (item, _) => (candidate work; item)) items)
        in
          (atoms, atom_index_with work atoms)
        end
      else indexed_atoms items
    val numbered_atoms = Lib.enumerate 0 atoms
    val nonneg_row = mknonneg (#width index)
    fun eligible (_, atom) = (candidate work; is_nonnegative atom)
    val contradiction =
      if #metered work then
        let
          val nonnegative =
            List.mapPartial
              (fn atom => if eligible atom then SOME (nonneg_row atom)
                          else NONE)
              numbered_atoms
        in
          elim_with work
            (List.map (mklineq_with work index) items @ nonnegative)
        end
      else
        let
          (* Check eligibility in atom order even if an assumption
             refutes the system before any unit row is needed. *)
          val eligible_atoms = List.filter eligible numbered_atoms
          (* Keep the assumption order and stop at the first
             contradiction. Unit rows are already nontrivial. *)
          fun collect kept [] =
                elim_rows_with work 0 true
                  (List.revAppend (kept, List.map nonneg_row eligible_atoms))
            | collect kept (item :: rest) =
                let
                  val row as Lineq (_, _, _, just) =
                    mklineq_with work index item
                in
                  if is_trivial_with work row then
                    if is_contradictory row then SOME just
                    else collect kept rest
                  else collect (row :: kept) rest
                end
        in
          collect [] items
        end
  in
    Option.map (fn just => just :: justs) contradiction
  end

fun refutes_with (work : work) is_nonnegative
      {split_neq, neq_count, neq_limit} items =
  let
    fun refute [] justs = SOME (List.rev justs)
      | refute (system :: rest) justs =
          case refute_system_with work is_nonnegative system justs of
              SOME next => refute rest next
            | NONE => NONE
    fun visit one =
      refute_system_with work is_nonnegative (number_hyps_with work one)
  in
    if split_neq andalso not (#metered work) andalso neq_count = 0 then
      Option.map List.rev (visit items [])
    else if split_neq andalso not (#metered work) then
      (* Replay expects all dense branches of each discrete branch in
         order. Stop generating systems as soon as one fails to refute. *)
      Option.map List.rev
        (fold_neq_pass_with work true
          (fn one => fn justs =>
            fold_neq_pass_with work false visit justs one) [] items)
    else
      let
        val systems = split_items_with work split_neq items
        val _ =
          if split_neq then ()
          else trace work
                 (fn () =>
                    "neq_limit exceeded (current value is " ^
                    Int.toString neq_limit ^
                    "); ignoring disequalities")
      in
        refute systems []
      end
  end

fun negate tm =
  if boolSyntax.is_neg tm then boolSyntax.dest_neg tm
  else boolSyntax.mk_neg tm

fun prove_decomposed_with work
      ({neq_limit, split_limit = _} : linarith_config)
                     decompose is_nonnegative hypotheses conclusion =
  case (SOME (negate conclusion)
        handle Feedback.HOL_ERR _ => NONE) of
      NONE => (false, NONE)
    | SOME negated_conclusion =>
        let
          val _ = normalization work
          val items =
            hypotheses @
            [(negated_conclusion, decompose negated_conclusion)]
          fun neq (_, SOME decomp) =
                (candidate work; is_neq decomp)
            | neq (_, NONE) = (candidate work; false)
          val neq_count =
            List.foldl (fn (item, count) =>
              if neq item then count + 1 else count) 0 items
          val split_neq = neq_count <= neq_limit
        in
          (split_neq,
           refutes_with work is_nonnegative {split_neq, neq_count, neq_limit}
             items)
        end

fun prove_decomposed level config decompose is_nonnegative hypotheses
      conclusion =
  prove_decomposed_with (free_work level)
    config decompose is_nonnegative hypotheses conclusion

fun prove_with work config decompose is_nonnegative hypotheses conclusion =
  prove_decomposed_with work config decompose is_nonnegative
    (List.map
      (fn tm => (normalization work; (tm, decompose tm)))
      hypotheses) conclusion

fun prove level config decompose is_nonnegative hypotheses conclusion =
  prove_with (free_work level)
    config decompose is_nonnegative hypotheses conclusion

datatype budget_outcome =
    CertificateFound of {split_neq : bool, justifications : injust list}
  | CertificateExhausted
  | CertificateLimitReached of
      {kind : searchBudget.kind, usage : searchBudget.usage}

fun prove_budgeted level budget config decompose is_nonnegative
      hypotheses conclusion =
  let
    val (split_neq, result) =
      prove_with (budget_work budget level) config decompose
        is_nonnegative hypotheses conclusion
  in
    case result of
        SOME justifications =>
          CertificateFound
            {split_neq = split_neq, justifications = justifications}
      | NONE => CertificateExhausted
  end
  handle searchBudget.LimitReached (kind, usage) =>
    CertificateLimitReached {kind = kind, usage = usage}

fun prove_decomposed_budgeted level budget config decompose
      is_nonnegative hypotheses conclusion =
  let
    val (split_neq, result) =
      prove_decomposed_with (budget_work budget level) config decompose
        is_nonnegative hypotheses conclusion
  in
    case result of
        SOME justifications =>
          CertificateFound
            {split_neq = split_neq, justifications = justifications}
      | NONE => CertificateExhausted
  end
  handle searchBudget.LimitReached (kind, usage) =>
    CertificateLimitReached {kind = kind, usage = usage}

end
