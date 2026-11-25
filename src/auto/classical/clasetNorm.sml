structure clasetNorm :> clasetNorm =
struct

open Abbrev HolKernel boolSyntax

type origin = string * string

fun error (origin_structure, origin_function) message =
  raise mk_HOL_ERR origin_structure origin_function message

(* [IN] is a boolTheory constant, [IN = \x f. f x], so [x IN P] and [P x]
   are one proposition written two ways, and a search that reads them as
   two atoms cannot get from one to the other.  Membership is the normal
   form because it is the one a search can hold on to: a set inside
   [x IN A] stays inside it however [A] is instantiated, whereas [A x]
   with [A] instantiated to a set former is an atom no rule about that
   former can match.

   The crossing is made at formula positions only.  Term positions keep
   beta-eta, so [\x. f x] still contracts to [f]; and a body wrapped as
   [x IN P] is no longer an eta redex, which is what stops [!x. P x] from
   collapsing to [$! P] and coming back applied when a search instantiates
   it.  A formula position is one the engines themselves decompose; an
   atom is compared whole, so a formula buried in a term position needs no
   crossing. *)

(* |- !item set. item IN set = set item *)
val membership_thm =
  let
    val item = mk_var ("item", Type.alpha)
    val set = mk_var ("set", Type.alpha --> Type.bool)
    val definition =
      Thm.AP_THM (Thm.AP_THM boolTheory.IN_DEF item) set
  in
    GENL [item, set]
      (Conv.CONV_RULE
        (Conv.RAND_CONV (Conv.REDEPTH_CONV BETA_CONV))
        definition)
  end

(* |- !item set. set item = item IN set *)
val applied_thm = Conv.GSYM membership_thm

fun head_beta_conv tm =
  if is_abs (rator tm) then BETA_CONV tm
  else Conv.RATOR_CONV head_beta_conv tm

fun expand_conv tm =
  let
    val (domain, _) = Type.dom_rng (type_of tm)
    val variable = variant (free_vars tm) (mk_var ("x", domain))
  in
    Thm.SYM (Drule.ETA_CONV (mk_abs (variable, mk_comb (tm, variable))))
  end

fun connective tm =
  let
    val (head, arguments) = strip_comb tm
  in
    case total dest_thy_const head of
        NONE => NONE
      | SOME {Thy, Name, ...} => SOME (Thy, Name, arguments)
  end

(* [is_hole] tells the crossing which variables stand for an unknown rather
   than for a set.  [?P x] is how a search asks pattern unification to build
   a predicate, and writing it as a membership would leave a first-order
   problem that only another membership can solve.  Each engine names its own
   holes: the classical engine's metavariables, blast's rule variables.

   [total] decides how much of an application counts as a set.  The crossing
   proper answers only where the spelling is forced -- an application of a
   variable -- and leaves a compound head alone, because a rule may be
   stated either way over one and canonicalising would lose the other.  A
   total crossing answers everywhere, and is a spelling rather than a normal
   form for exactly that reason: it exists so a lookup can ask for the
   membership form of a goal the way [applied_conv] asks for the applied
   one. *)
fun formula total is_hole tm =
  Conv.ORELSEC
    (Conv.THENC (head_beta_conv, formula total is_hole), shape total is_hole)
    tm

and shape total is_hole tm =
    let
      val descend = formula total is_hole
    in
      case connective tm of
          SOME ("bool", "!", [_]) => binder total is_hole tm
        | SOME ("bool", "?", [_]) => binder total is_hole tm
        | SOME ("bool", "?!", [_]) => binder total is_hole tm
        | SOME ("bool", "~", [_]) => Conv.RAND_CONV descend tm
        | SOME ("bool", "/\\", [_, _]) => Conv.BINOP_CONV descend tm
        | SOME ("bool", "\\/", [_, _]) => Conv.BINOP_CONV descend tm
        | SOME ("min", "==>", [_, _]) => Conv.BINOP_CONV descend tm
        | SOME ("min", "=", [left, _]) =>
            if type_of left = Type.bool then Conv.BINOP_CONV descend tm
            else atom total is_hole tm
        | SOME ("bool", "IN", [_, set]) =>
            if is_abs set then
              Conv.THENC
                (Conv.REWR_CONV membership_thm,
                 Conv.THENC (BETA_CONV, descend)) tm
            else Conv.ALL_CONV tm
        | _ => atom total is_hole tm
    end

and binder total is_hole tm =
    let
      val predicate = rand tm
    in
      if is_abs predicate then
        Conv.RAND_CONV (Conv.ABS_CONV (formula total is_hole)) tm
      else if is_hole predicate then Conv.ALL_CONV tm
      else
        (* [!x. P x] contracted to [$! P] would come back applied when a
           search instantiates it, so it is expanded and its body crossed. *)
        Conv.THENC (Conv.RAND_CONV expand_conv, formula total is_hole) tm
    end

and atom total is_hole tm =
    (* The type test keeps the conversion total: a caller may hand it a term
       position, where an application over a variable is not an atom at all.
       [head_beta_conv] has already fired, so the head is a variable or a
       constant and never an abstraction. *)
    if is_comb tm andalso type_of tm = Type.bool andalso
       (if total then not (is_hole (fst (strip_comb tm)))
        else is_var (rator tm) andalso not (is_hole (rator tm)))
    then Conv.REWR_CONV applied_thm tm
    else Conv.ALL_CONV tm

fun membership_conv_with is_hole = Conv.QCONV (formula false is_hole)

val membership_conv = membership_conv_with clasetMeta.is_meta

(* Membership at every position, the mirror of [applied_conv]: where the two
   spellings of an application are both normal forms, these two decide which
   is which, and neither is where a term settles. *)
val crossed_conv = Conv.QCONV (formula true clasetMeta.is_meta)

(* The other direction: [IN] unfolded, which is its definition.  Unfolding is
   sound at every position, so this needs no notion of a formula position.
   It exists for looking a goal up in an index keyed on the rules as stated;
   nothing normalises to it. *)
fun membership_operator operator =
  is_comb operator andalso same_const (rator operator) IN_tm

val unfold_membership = Conv.REWR_CONV membership_thm

fun applied_step tm =
  if is_comb tm then
    let val operator = rator tm
    in
      if membership_operator operator then unfold_membership tm
      else if is_abs operator then BETA_CONV tm
      else Conv.NO_CONV tm
    end
  else Conv.NO_CONV tm

val applied_conv = Conv.QCONV (Conv.REDEPTH_CONV applied_step)

(* [x IN (\y. b)] is a beta redex written through the definition of [IN],
   so reducing it is reduction and not the crossing: it makes a strictly
   simpler term, and a membership in anything else is left alone.  Leaving
   it unreduced would keep the engine's state opaque -- every step would
   have to re-cross an atom whose body the rules are stated about. *)
val member_beta_conv = Conv.THENC (unfold_membership, BETA_CONV)

(* [reduce_conv] is what shapes the engine's terms: an instantiated rule is
   reduced, and its premises become goals the caller reads.  The crossing
   deliberately stays out of it, so a residual goal comes back written the
   way it was posed.  [normalize_conv] adds the crossing and is for
   comparing: the matcher and [align_conclusion] use it, and nothing that
   builds a goal does. *)
(* [FST (a, b)] is a redex of the same kind, and the engines meet it
   because a translated [Sigma] is a set former over FST and SND, so a
   membership crossed against a pair leaves one behind.  The simpset
   reduces it and the classical layer did not, which is why AUTO_TAC
   closed such a goal and FAST_TAC and BLAST_TAC did not. *)
val fst_conv = Conv.REWR_CONV pairTheory.FST
val snd_conv = Conv.REWR_CONV pairTheory.SND

(* A bottom-up traversal visits every subterm. Test the redex shape before
   attempting a kernel conversion, especially on the usual unchanged path. *)
fun reduction_step eta tm =
  if is_comb tm then
    let val (operator, operand) = dest_comb tm
    in
      if is_abs operator then BETA_CONV tm
      else if is_abs operand andalso membership_operator operator then
        member_beta_conv tm
      else if same_const operator pairSyntax.fst_tm then fst_conv tm
      else if same_const operator pairSyntax.snd_tm then snd_conv tm
      else Conv.NO_CONV tm
    end
  else if eta andalso is_abs tm then Drule.ETA_CONV tm
  else Conv.NO_CONV tm

(* [dest_forall] fails on [$! P], so a quantifier that reaches a caller's
   goal contracted is one no step can take apart.  The crossing spells such
   a predicate out for the engine's own terms; a goal is not crossed, so it
   is spelled out here instead.  A hole predicate stays contracted: [$! ?P]
   is the first-order pattern a search instantiates, and [!x. ?P x] is
   not. *)
fun expand_binders is_hole tm =
  let
    fun here tm =
      case connective tm of
          SOME ("bool", name, [predicate]) =>
            if (name = "!" orelse name = "?" orelse name = "?!") andalso
               not (is_abs predicate) andalso not (is_hole predicate)
            then Conv.RAND_CONV expand_conv tm
            else Conv.ALL_CONV tm
        | _ => Conv.ALL_CONV tm
  in
    Conv.THENC (here, Conv.SUB_CONV (expand_binders is_hole)) tm
  end

val reduction = Conv.REDEPTH_CONV (reduction_step true)

val reduce_conv = Conv.QCONV reduction

(* The same reduction for a goal arriving from the caller, without eta:
   the caller's terms are its own and contracting one would re-spell a
   quantifier the caller wrote out.  A quantifier that arrives contracted
   is expanded, so a goal posed as [$! P] is as strippable as one posed as
   [!x. P x]. *)
val goal_reduce_conv =
  Conv.QCONV
    (Conv.THENC
      (Conv.REDEPTH_CONV (reduction_step false),
       expand_binders clasetMeta.is_meta))

val normalize_conv =
  Conv.QCONV (Conv.THENC (formula false clasetMeta.is_meta, reduction))

(* A rule application proves a goal in the normal form; the goal is the
   user's, as written.  This carries the proof back to the statement the
   caller has to produce. *)
fun align_conclusion target theorem =
  let
    val conclusion = concl theorem

    fun carry conversion =
      let
        val target_equality = conversion target
        val target' = rhs (concl target_equality)
        val conclusion_equality = conversion conclusion
        val conclusion' = rhs (concl conclusion_equality)
      in
        if aconv conclusion' target' then
          SOME
            (EQ_MP (Thm.SYM target_equality)
              (EQ_MP (ALPHA conclusion' target')
                (EQ_MP conclusion_equality theorem)))
        else NONE
      end
  in
    if aconv conclusion target then
      EQ_MP (ALPHA conclusion target) theorem
    else
      case carry normalize_conv of
          SOME result => result
        | NONE =>
            (* The crossing turns an application into a membership on a
               variable function, so where the set is a compound -- the
               [UNCURRY P] a set comprehension over a pair translates to --
               it crosses neither way and both spellings are normal forms.
               [applied_conv] unfolds [IN] at every position, so it decides
               that case; it is a spelling and not a normal form, which is
               why it settles a comparison the normal form leaves open
               rather than replacing it. *)
            (case carry applied_conv of
                 SOME result => result
               | NONE =>
                   error ("clasetNorm", "align_conclusion")
                     "the theorem does not prove the target in normal form")
  end

(* The engine renders a goal reduced, so a step's child is proved in the
   reduced spelling while the step's own validation was built on the
   spelling the step returned.  This restates such a proof: the conclusion
   through [align_conclusion], and each hypothesis the proof states in a
   spelling of its own through the assumption the goal poses it in.
   Both spellings are the same formula, so the bridge is
   [align_conclusion] again, applied to the assumption: which spellings
   can differ is the entry's business -- one entry eta-contracts, another
   spells a contracted binder out -- and comparing in the normal form
   settles them all, where naming one entry's conversion here would leave
   the others' assumptions undischarged. *)
fun align_goal (asl, w) theorem =
  let
    val aligned = align_conclusion w theorem
    fun posed hypothesis = tmem hypothesis asl
    fun restore (hypothesis, th) =
      let
        fun bridge [] = th
          | bridge (assumption :: rest) =
              case total (align_conclusion hypothesis) (ASSUME assumption) of
                  SOME proof => Drule.PROVE_HYP proof th
                | NONE => bridge rest
      in
        bridge asl
      end
  in
    List.foldl restore aligned (List.filter (not o posed) (hyp aligned))
  end

fun normalize_thm theorem =
  Conv.CONV_RULE reduce_conv theorem

fun normalize_rule_thm theorem =
  let
    fun normalize_hypothesis (hypothesis, current) =
      let
        val equality = reduce_conv hypothesis
        val normalized = rhs (concl equality)
        val original = EQ_MP (SYM equality) (ASSUME normalized)
      in
        Drule.PROVE_HYP original current
      end
  in
    normalize_thm
      (List.foldl normalize_hypothesis theorem (hyp theorem))
  end

fun normalize_assumption_thm theorem =
  let
    val equality = reduce_conv (concl theorem)
  in
    (rhs (concl equality), EQ_MP equality theorem)
  end

fun normalize_assumption assumption =
  normalize_assumption_thm (ASSUME assumption)

fun split_imp_prefix origin arity tm =
  let
    fun split 0 premises conclusion =
          (List.rev premises, conclusion)
      | split remaining premises current =
          (case total dest_imp_only current of
               SOME (premise, rest) =>
                 split (remaining - 1) (premise :: premises) rest
             | NONE =>
                 error origin
                   "the instantiated rule has fewer premises than recorded")
  in
    if arity < 0 then
      error origin "negative implication-prefix arity"
    else
      split arity [] tm
  end

fun nth1 origin values pos =
  if pos < 1 then error origin "positions are one-based"
  else
    List.nth (values, pos - 1)
    handle Subscript => error origin "position out of range"

fun splice_nth origin values pos replacements =
  if pos < 1 then error origin "positions are one-based"
  else
    let
      fun splice _ [] _ = error origin "position out of range"
        | splice 1 (_ :: tail) prefix =
            List.revAppend (prefix, replacements @ tail)
        | splice n (value :: tail) prefix =
            splice (n - 1) tail (value :: prefix)
    in
      splice pos values []
    end

fun delete_nth origin values pos = splice_nth origin values pos []

end
