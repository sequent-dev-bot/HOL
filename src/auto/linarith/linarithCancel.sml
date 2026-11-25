structure linarithCancel :> linarithCancel =
struct

open Abbrev HolKernel Conv Drule

val ERR = mk_HOL_ERR "linarithCancel"

val same_type = linarithData.same_type

type ac_ops = {
  dest_less : term -> term * term,
  dest_leq : term -> term * term,
  strip_plus : term -> term list,
  mk_plus : term * term -> term,
  assoc : thm,
  comm : thm,
  rid : thm,
  ac_fallback : conv option
}

type norm_spec = {
  ac : ac_ops,
  ty : hol_type,
  leq_cancel : thm,
  less_cancel : thm,
  eq_cancel : thm,
  expression_conv : conv,
  reduce_conv : conv,
  refl_thms : thm list
}

(* Each left occurrence consumes one right occurrence. Walk the original
   right list to remove its first consumed occurrences, so each remainder
   keeps its original terms in order. *)
fun common_summands [item] right =
      Option.map (fn (_, rest) => ([item], [], rest))
        (Lib.total (Lib.pluck (Term.aconv item)) right)
  | common_summands left [item] =
      Option.map (fn (matched, rest) => ([matched], rest, []))
        (Lib.total (Lib.pluck (Term.aconv item)) left)
  | common_summands left right =
      let
        fun count (item, counts) =
          let
            val available = Option.getOpt (Termtab.lookup counts item, 0)
          in
            Termtab.update (item, available + 1) counts
          end
        fun consume (item, (counts, common, rest)) =
          let
            val available = Option.getOpt (Termtab.lookup counts item, 0)
          in
            if available > 0 then
              (Termtab.update (item, available - 1) counts,
               item :: common, rest)
            else (counts, common, item :: rest)
          end
        val right_counts = List.foldl count Termtab.empty right
        val (counts, common, rest_left) =
          List.foldl consume (right_counts, [], []) left
        fun keep_unused (item, (counts, rest)) =
          let
            val available = Option.getOpt (Termtab.lookup counts item, 0)
          in
            if available > 0 then
              (Termtab.update (item, available - 1) counts, item :: rest)
            else (counts, rest)
          end
      in
        case common of
            [] => NONE
          | _ =>
              let
                val (_, rest_right) =
                  List.foldr keep_unused (counts, []) right
              in
                SOME (List.rev common, List.rev rest_left, rest_right)
              end
      end

(* Only ever asked for a non-empty list of summands; an emptied side is
   handled by the identity theorem instead. *)
fun mk_sum (ops : ac_ops) terms =
  list_mk_lbinop (curry (#mk_plus ops)) terms

fun relation_sides (ops : ac_ops) tm =
  case Lib.total (#dest_leq ops) tm of
      SOME sides => sides
    | NONE =>
        (case Lib.total (#dest_less ops) tm of
             SOME sides => sides
           | NONE => boolSyntax.dest_eq tm)

fun ac_equality (ops : ac_ops) rearrange left right =
  if Term.aconv left right then Thm.REFL left
  else
    let
      val equality = boolSyntax.mk_eq (left, right)
      (* A rewrite by EQ_REFL merely matches the reflexive equality;
         certify that it is true before EQT_ELIM consumes the result. *)
      fun refl_conv tm =
        let
          val (lhs, rhs) = boolSyntax.dest_eq tm
        in
          if Term.aconv lhs rhs then EQT_INTRO (REFL lhs)
          else raise ERR "ac_equality" "canonical forms differ"
        end
      fun fallback () =
        case #ac_fallback ops of
            NONE => raise ERR "ac_equality" "AC rearrangement failed"
          | SOME canon =>
              EQT_ELIM
                ((BINOP_CONV canon THENC
                  refl_conv) equality)
    in
      EQT_ELIM (rearrange equality)
      handle HOL_ERR _ => fallback ()
    end

(* cancel_common ops cancel: given the carrier's left-cancellation
   theorem, remove every summand common to both sides of a relation at
   once, matching summands up to aconv and one occurrence at a time.
   Raises UNCHANGED when there is nothing to cancel. *)
fun cancel_common (ops : ac_ops) rearrange cancel tm =
  let
    val operator = Term.rator (Term.rator tm)
    val (left, right) = relation_sides ops tm
    fun summands expression =
      case #strip_plus ops expression of
          [] => [expression]
        | terms => terms
    (* Sides that are equal as multisets would cancel away entirely,
       leaving the cancellation theorem nothing to relate; hold their last
       summand back instead, so the result is the reflexive relation the
       one-at-a-time version stopped at and finish decides.  A lone common
       summand is that relation already, hence UNCHANGED. *)
    fun hold_back_last common =
      case List.rev common of
          last :: (front as _ :: _) =>
            SOME (List.rev front, [last], [last])
        | _ => NONE
    val split =
      case common_summands (summands left) (summands right) of
          NONE => NONE
        | SOME (common, [], []) => hold_back_last common
        | SOME parts => SOME parts
  in
    case split of
        NONE => raise UNCHANGED
      | SOME (common, left', right') =>
          let
            val common_sum = mk_sum ops common
            (* An emptied side becomes common + 0 so that both sides share
               the cancellation theorem's shape. *)
            fun cancellation_side original [] =
                  Thm.TRANS (ac_equality ops rearrange original common_sum)
                    (Thm.SYM (Thm.SPEC common_sum (#rid ops)))
              | cancellation_side original rest =
                  ac_equality ops rearrange original
                    (#mk_plus ops (common_sum, mk_sum ops rest))
            val relation_thm =
              Thm.MK_COMB
                (Thm.AP_TERM operator (cancellation_side left left'),
                 cancellation_side right right')
            val cancel_thm =
              cancel (#2 (boolSyntax.dest_eq (Thm.concl relation_thm)))
          in
            Thm.TRANS relation_thm cancel_thm
          end
  end

val safe_conv = QCONV o TRY_CONV

(* Composed by hand rather than with EVERY_CONV, whose trailing ALL_CONV
   would turn a chain that leaves the term alone into REFL and so lose
   the UNCHANGED an expression_conv is read for. *)
fun chain_convs [] = ALL_CONV
  | chain_convs convs = Lib.end_itlist (curry op THENC) convs

fun mk_expression_conv ty convs =
  let
    val body = chain_convs convs
  in
    fn tm =>
      if same_type (Term.type_of tm) ty then body tm
      else raise UNCHANGED
  end

fun mk_norm_conv (spec : norm_spec) =
  let
    val ops = #ac spec
    val expression_conv = #expression_conv spec
    (* Share theorem matching setup while keeping failures at first use. *)
    fun delayed_conv build =
      let val pending = Portable.HOLSusp.delay build
      in fn tm => Portable.HOLSusp.force pending tm end
    val rearrange =
      delayed_conv (fn () => AC_CONV (#assoc ops, #comm ops))
    fun canceller theorem =
      cancel_common ops rearrange (delayed_conv (fn () => REWR_CONV theorem))
    val leq_cancel = canceller (#leq_cancel spec)
    val less_cancel = canceller (#less_cancel spec)
    val eq_cancel = canceller (#eq_cancel spec)
    fun cancel_rule tm =
      if Lib.can (#dest_leq ops) tm then SOME leq_cancel
      else if Lib.can (#dest_less ops) tm then SOME less_cancel
      else if boolSyntax.is_eq tm andalso
              same_type (Term.type_of (#1 (boolSyntax.dest_eq tm)))
                (#ty spec)
      then SOME eq_cancel
      else NONE
    val finish =
      TRY_CONV (#reduce_conv spec) THENC
      TRY_CONV (simpLib.SIMP_CONV boolSimps.bool_ss (#refl_thms spec))
  in
    fn tm =>
      case cancel_rule tm of
          NONE => expression_conv tm
        | SOME cancel =>
            (BINOP_CONV expression_conv THENC cancel THENC finish) tm
  end

end
