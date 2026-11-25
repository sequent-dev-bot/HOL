structure linarithDecomp :> linarithDecomp =
struct

open HolKernel

type polynomial = (term * Arbrat.rat) list * Arbrat.rat

type atoms =
  {coefficients : Arbrat.rat ref Termtab.table,
   newest : (term * Arbrat.rat ref) list}

val rat_zero = Arbrat.zero
val rat_one = Arbrat.one

val same_type = linarithData.same_type

fun binary_parts tm =
  let
    val (rator, right) = Term.dest_comb tm
    val (operator, left) = Term.dest_comb rator
  in
    (operator, left, right)
  end

fun unary_parts tm = Term.dest_comb tm

fun mk_binary operator left right =
  Term.list_mk_comb (operator, [left, right])

fun instance_of tm = linarithData.instance_for (Term.type_of tm)

(* An injection may be stripped only from an argument built out of the
   operators it distributes over -- sums, products, successors and
   literals.  A successor qualifies because it is the sum SUC k = k + 1,
   which is also how poly_other reads it, so an injection with an add
   homomorphism carries it too.  Every other operator of the source
   carrier keeps the injection, and the injected term stays an atom: num
   subtraction is the standard reason, since &(m - n) is not &m - &n. *)
fun supported source tm =
  let
    val dest = #dest source
    (* Read off the carrier's registration, and read off once for the
       whole traversal rather than per subterm. *)
    val compound = linarithData.compound_ops source
    fun keeps_injection tm =
      List.exists (fn recognises => recognises tm) compound
    fun ok tm =
      case Lib.total (#dest_plus dest) tm of
          SOME (left, right) => ok left andalso ok right
        | NONE =>
      case Lib.total (#dest_mult dest) tm of
          SOME (left, right) => ok left andalso ok right
        | NONE =>
      case Option.mapPartial (fn dest_suc => Lib.total dest_suc tm)
             (#dest_suc dest) of
          SOME argument => ok argument
        | NONE =>
          Option.isSome (Lib.total (#dest_lit dest) tm) orelse
          not (keeps_injection tm)
  in
    ok tm
  end

fun injection_arg tm =
  case Lib.total unary_parts tm of
      NONE => NONE
    | SOME (operator, arg) =>
        (case linarithData.injection_by_const operator of
             NONE => NONE
           | SOME injection =>
               if same_type (Term.type_of arg) (#from_ty injection) andalso
                  same_type (Term.type_of tm) (#to_ty injection)
               then
                 case linarithData.instance_for (#from_ty injection) of
                     SOME source =>
                       if supported source arg then SOME arg else NONE
                   | NONE => SOME arg
               else NONE)

fun dest_optional dest tm =
  Option.mapPartial (fn destroy => Lib.total destroy tm) dest

fun try_product operator left right =
  Lib.total (fn () => mk_binary operator left right) ()

fun restore_factor_type original atom =
  let
    val original_ty = Term.type_of original
    val atom_ty = Term.type_of atom
  in
    if same_type original_ty atom_ty then SOME atom
    else
      case linarithData.injection_for atom_ty original_ty of
          NONE => NONE
        | SOME injection =>
            Lib.total (fn () => Term.mk_comb (#inj injection, atom)) ()
  end

(* Products are normalized to right-associated form while their literal
   factors are accumulated in the Arbrat multiplier. *)
fun demult (tm, multiplier) =
  case instance_of tm of
      NONE => demult_atom (tm, multiplier)
    | SOME instance => demult_with (#dest instance) (tm, multiplier)
and demult_atom (tm, multiplier) =
  case injection_arg tm of
      SOME arg => demult (arg, multiplier)
    | NONE => (SOME tm, multiplier)
and demult_with dest (tm, multiplier) =
  let
    fun give_up () = (SOME tm,multiplier)
    fun rotate operator left1 left2 right =
      Option.mapPartial (try_product operator left1)
        (try_product operator left2 right)
    fun rebuild operator left right left' right' =
      case
        (restore_factor_type left left',restore_factor_type right right')
      of
          (SOME restored_left,SOME restored_right) =>
            try_product operator restored_left restored_right
        | _ => NONE
  in
    case Lib.total (#dest_mult dest) tm of
        SOME (left,right) =>
          let val (operator,_,_) = binary_parts tm
          in
            case Option.mapPartial
                   (fn instance => Lib.total (#dest_mult (#dest instance)) left)
                   (instance_of left) of
                SOME (left1,left2) =>
                  (case rotate operator left1 left2 right of
                       SOME rotated => demult (rotated,multiplier)
                     | NONE => give_up ())
              | NONE =>
                  let val (left_atom,multiplier') = demult (left,multiplier)
                  in
                    case left_atom of
                        NONE => demult (right,multiplier')
                      | SOME left' =>
                          let
                            val (right_atom,multiplier'') =
                              demult (right,multiplier')
                          in
                            case right_atom of
                                NONE => (SOME left',multiplier'')
                              | SOME right' =>
                                  (case rebuild operator left right
                                          left' right' of
                                       SOME product =>
                                         (SOME product,multiplier'')
                                     | NONE => give_up ())
                          end
                  end
          end
      | NONE =>
          case dest_optional (#dest_div dest) tm of
              SOME (numerator,denominator) =>
                (case demult (denominator,rat_one) of
                     (NONE,divisor) =>
                       if divisor = rat_zero then give_up ()
                       else
                         let
                           val (atom,numerator_multiplier) =
                             demult (numerator,multiplier)
                         in
                           (atom,
                            Arbrat.*
                              (numerator_multiplier,Arbrat.inv divisor))
                         end
                   | (SOME _,_) => give_up ())
            | NONE =>
                case dest_optional (#dest_neg dest) tm of
                    SOME arg => demult (arg,Arbrat.negate multiplier)
                  | NONE =>
                      case Lib.total (#dest_lit dest) tm of
                          SOME literal =>
                            (NONE,Arbrat.* (multiplier,literal))
                        | NONE => demult_atom (tm, multiplier)
  end

fun add_atom atom coefficient
      (atoms as {coefficients, newest} : atoms, constant) =
  if coefficient = rat_zero then (atoms, constant)
  else
    case Termtab.lookup coefficients atom of
        NONE =>
          let
            val cell = ref coefficient
          in
            ({coefficients = Termtab.update (atom, cell) coefficients,
              newest = (atom, cell) :: newest}, constant)
          end
      | SOME cell =>
          let
            val sum = Arbrat.+ (!cell, coefficient)
            val _ = cell := sum
          in
            if sum = rat_zero then
              ({coefficients = Termtab.delete atom coefficients,
                newest = newest}, constant)
            else (atoms, constant)
          end

fun add_constant multiplier literal (atoms, constant) =
  (atoms, Arbrat.+ (constant, Arbrat.* (multiplier, literal)))

fun poly_acc (tm, multiplier, polynomial) =
  case instance_of tm of
      NONE =>
        (case injection_arg tm of
             SOME arg => poly_acc (arg, multiplier, polynomial)
           | NONE => add_atom tm multiplier polynomial)
    | SOME instance =>
        let
          val dest = #dest instance
        in
          case Lib.total (#dest_plus dest) tm of
              SOME (left, right) =>
                poly_acc
                  (left, multiplier,
                   poly_acc (right, multiplier, polynomial))
            | NONE =>
                (case dest_optional (#dest_minus dest) tm of
                     SOME (left, right) =>
                       poly_acc
                         (left, multiplier,
                          poly_acc
                            (right, Arbrat.negate multiplier, polynomial))
                   | NONE => poly_other dest (tm, multiplier, polynomial))
        end
and poly_other dest (tm, multiplier, polynomial) =
  case dest_optional (#dest_suc dest) tm of
      SOME arg =>
        poly_acc
          (arg, multiplier,
           add_constant multiplier rat_one polynomial)
    | NONE => poly_non_suc dest (tm, multiplier, polynomial)
and poly_non_suc dest (tm, multiplier, polynomial) =
  case dest_optional (#dest_neg dest) tm of
      SOME arg => poly_acc (arg, Arbrat.negate multiplier, polynomial)
    | NONE =>
        (case Lib.total (#dest_lit dest) tm of
             SOME literal => add_constant multiplier literal polynomial
           | NONE =>
               (* One arm for both, because demult_with re-dispatches on the
                  term itself: what is asked here is only whether it has
                  a product or a quotient to take apart, and the answer
                  decides nothing beyond that.  The aconv self-check is
                  what stops the mutual recursion with demult when demult
                  hands the term back unchanged -- a division by a
                  non-literal, say -- and it is a rule about the
                  recursion rather than about the operator, so it is
                  written once.  The order is unchanged: orelse asks
                  about division only for a term that is no product. *)
               if Option.isSome (Lib.total (#dest_mult dest) tm) orelse
                  Option.isSome (dest_optional (#dest_div dest) tm)
               then
                 let
                   val (atom, coefficient) =
                     demult_with dest (tm, multiplier)
                 in
                   case atom of
                       SOME atom' =>
                         if Term.aconv atom' tm then
                           add_atom atom' coefficient polynomial
                         else
                           poly_acc (atom', coefficient, polynomial)
                     | NONE =>
                         add_constant rat_one coefficient polynomial
                 end
               else
                 (case injection_arg tm of
                      SOME arg => poly_acc (arg, multiplier, polynomial)
                    | NONE => add_atom tm multiplier polynomial))

fun poly tm : polynomial =
  let
    val empty = {coefficients = Termtab.empty, newest = []}
    val ({newest, ...}, constant) =
      poly_acc (tm, rat_one, (empty, rat_zero))
    (* Each insertion keeps its original term and its own coefficient
       cell. Canceled cells stay zero even if the atom is reinserted. *)
    fun collect ((atom, cell), result) =
      let
        val coefficient = !cell
      in
        if coefficient = rat_zero then result
        else (atom, coefficient) :: result
      end
  in
    (List.foldl collect [] newest, constant)
  end

fun relation tm =
  case Lib.total boolSyntax.dest_eq tm of
      SOME (left, right) => SOME (linarithSolve.REL_EQ, left, right)
    | NONE =>
        (case Lib.total binary_parts tm of
             NONE => NONE
           | SOME (_, left, _) =>
               (case linarithData.instance_for (Term.type_of left) of
                    NONE => NONE
                  | SOME instance =>
                      let
                        val dest = #dest instance
                      in
                        case Lib.total (#dest_less dest) tm of
                            SOME (lhs, rhs) =>
                              SOME (linarithSolve.REL_LT, lhs, rhs)
                          | NONE =>
                              (case Lib.total (#dest_leq dest) tm of
                                   SOME (lhs, rhs) =>
                                     SOME
                                       (linarithSolve.REL_LE, lhs, rhs)
                                 | NONE => NONE)
                      end))

fun decompose tm =
  let
    val (negated, body) =
      case Lib.total boolSyntax.dest_neg tm of
          SOME inner => (true, inner)
        | NONE => (false, tm)
  in
    case relation body of
        NONE => NONE
      | SOME (rel, lhs, rhs) =>
          (case linarithData.instance_for (Term.type_of lhs) of
               NONE => NONE
             | SOME instance =>
                 let
                   val (lhs_atoms, lhs_const) = poly lhs
                   val (rhs_atoms, rhs_const) = poly rhs
                   val (rel', negated') =
                     if rel = linarithSolve.REL_EQ andalso negated then
                       (linarithSolve.REL_NEQ, false)
                     else (rel, negated)
                 in
                   SOME
                     (linarithSolve.Decomp
                        {lhs = lhs_atoms, lhs_const = lhs_const,
                         rel = rel', rhs = rhs_atoms,
                         rhs_const = rhs_const,
                         discrete = Option.isSome (#discrete instance),
                         negated = negated'})
                 end)
  end

(* Decomposing a term is a pure function of it and of the instance and
   injection registries, and one decision asks for the same terms
   several times over.  The result cache in linarithLib alone asks
   is_relevant of the goal, then the atoms of the goal and of every
   context theorem's conclusion -- twice, once to split the context into
   connected components and once to attach each theorem to its own --
   and the procedure behind it asks is_relevant once more.  So the
   answers are remembered, keyed on the registry generation the lookups
   inside them read, exactly as the registry's own derivations are.

   The table is bounded, because this sits under the simplifier and is
   offered every boolean subterm of every simplification: an unbounded
   one would grow with the length of the session rather than with the
   work in hand.  What it exists to hold is one decision's working set
   -- a goal, its context theorems, and the subterms of both -- and
   enough neighbouring decisions that a simplifier pass over a goal
   finds its own earlier answers, which a capacity in the thousands is
   generously above either way.  Overflow discards the table rather than
   evicting an entry: it is the same recovery as a registry change, it
   costs no per-entry bookkeeping on the path that matters, and a
   working set this far below the capacity reaches it rarely enough that
   which entry is dropped cannot be worth deciding. *)
val memo_capacity = 2000

(* The generation rule itself is linarithData's, taken from there rather
   than restated: what the helper holds per generation is the table's
   cell, so a change to when a derivation goes stale reaches this table
   along with the registry's own.  The capacity is not the helper's
   business -- everything else it serves is one value per generation, and
   a bound belongs to the table that can grow -- so it stays here, at the
   one insertion that can reach it. *)
val decomp_table =
  linarithData.memo
    (fn () =>
      ref (Termtab.empty : linarithSolve.decomp option Termtab.table))

fun decomp tm =
  let
    val table = decomp_table ()
  in
    case Termtab.lookup (!table) tm of
        SOME answer => answer
      | NONE =>
          let
            val answer = decompose tm
            val kept =
              if Termtab.size (!table) < memo_capacity then !table
              else Termtab.empty
          in
            table := Termtab.update (tm, answer) kept;
            answer
          end
  end

fun is_nonnegative tm =
  case linarithData.instance_for (Term.type_of tm) of
      NONE => false
    | SOME instance =>
        Option.isSome (#nonneg (#kit instance) tm)

fun is_relevant tm = Option.isSome (decomp tm)

end
