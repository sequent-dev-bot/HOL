(* =====================================================================
 * Term-indexing net for the claset.
 *
 * The [match] direction (stored pattern variables act as wildcards, the
 * query is rigid) is exactly what src/1/Ho_Net provides.  This net is a
 * separate implementation because it must ALSO support [unify], where the
 * query's own variables act as wildcards and so may match any stored
 * subterm.  That reverse direction needs [skip_one_m] to step over a whole
 * stored subterm, which relies on the uniform one-node-per-application
 * labelling below (Cmb/Lam/Cnst/Fvar/V).  Ho_Net folds the argument count
 * into
 * its labels (Cnet of ... * int), so it cannot skip a subterm without
 * knowing that arity, and extending it lives on a path shared with every
 * simpset.  Keep [match] here consistent with Ho_Net's semantics.
 *
 * Both sides are labelled eta-contracted.  Isabelle's [Pure/net.ML] states
 * the same requirement -- its operands must be beta-eta-normal -- and here
 * it is forced by the engines themselves: [blastTerm.wkNorm] contracts
 * under a binder, so an assumption [!xs. C a xs] reaches the search as
 * [$! (C a)], while the elimination that takes a universal apart is stored
 * under [!y. P y].  Labelling the stored abstraction structurally hid that
 * rule from the one formula it exists to decompose, and the unifier that
 * follows contracts both sides and would have succeeded.  Contracting at
 * each labelled node is what keeps the index's notion of a term the same
 * as theirs; Isabelle goes further and keys every abstraction as a
 * wildcard, which also covers near-eta redexes such as [%x. ?P (?f x)],
 * but resolution there is higher-order where the matcher and the unifier
 * here are first-order, so nothing but eta can bridge the two spellings.
 * ===================================================================== *)

structure clasetNet :> clasetNet =
struct

open HolKernel KernelTypes listUtil

type term = Term.term

datatype label =
    V
  | Cmb
  | Lam
  | Cnst of KernelSig.kernelname
  | Fvar of string

datatype 'a net = NODE of 'a list * (label * 'a net) list

val empty = NODE ([], [])

fun const_label tm =
  let val {Name, Thy, ...} = dest_thy_const tm
  in Cnst {Name = Name, Thy = Thy}
  end

fun fvar_label tm =
  let val (Name, _) = dest_var tm
  in Fvar Name
  end

fun is_bound checkpoint bvars tm =
  (checkpoint (); op_mem aconv tm bvars)

(* [\y. f y] and [f] are the same function and the engines' terms are
   carried in whichever spelling reduction left, so the index answers for
   both: a labelled node is contracted first, and the walk contracts each
   child as it reaches it. *)
fun eta_contract tm =
  if not (is_abs tm) then tm
  else
    let
      val (bvar, body) = dest_abs tm
      val body' = eta_contract body
      fun rebuild () = if aconv body' body then tm else mk_abs (bvar, body')
    in
      if is_comb body' then
        let val (rator, rand) = dest_comb body'
        in
          if aconv rand bvar andalso not (free_in bvar rator)
          then eta_contract rator
          else rebuild ()
        end
      else rebuild ()
    end

fun stored_label patvars bvars tm =
  if is_var tm andalso
     (HOLset.member (patvars, tm) orelse
      is_bound no_checkpoint bvars tm) then V
  else if is_var tm then fvar_label tm
  else if is_abs tm then Lam
  else if is_comb tm then Cmb
  else const_label tm

fun query_label checkpoint bvars tm =
  if is_var tm andalso is_bound checkpoint bvars tm then NONE
  else if is_var tm then SOME (fvar_label tm)
  else if is_abs tm then SOME Lam
  else if is_comb tm then SOME Cmb
  else SOME (const_label tm)

fun edge checkpoint label edges =
  Option.map #2 (findMeasured checkpoint (fn (l, _) => l = label) edges)

fun update_edge label update [] = [(label, update empty)]
  | update_edge label update ((entry as (label', child)) :: rest) =
      if label = label' then (label, update child) :: rest
      else entry :: update_edge label update rest

fun stored_labels patvars pat =
  let
    fun labels bvars tm0 rest =
      let
        val tm = eta_contract tm0
        val label = stored_label patvars bvars tm
      in
        case label of
            Lam =>
              let val (bvar, body) = dest_abs tm
              in label :: labels (bvar :: bvars) body rest
              end
          | Cmb =>
              let val (rator, rand) = dest_comb tm
              in label :: labels bvars rator (labels bvars rand rest)
              end
          | _ => label :: rest
      end
  in
    labels [] pat []
  end

fun insert ({pat, patvars}, value) net =
  let
    fun enter [] (NODE (tips, edges)) = NODE (value :: tips, edges)
      | enter (label :: labels) (NODE (tips, edges)) =
          NODE (tips, update_edge label (enter labels) edges)
  in
    enter (stored_labels patvars pat) net
  end

fun is_empty (NODE (tips, edges)) = null tips andalso null edges

fun filter_at {pat, patvars} keep net =
  let
    fun filter [] (NODE (tips, edges)) =
          NODE (List.filter keep tips, edges)
      | filter (label :: labels) (NODE (tips, edges)) =
          let
            fun descend [] = []
              | descend ((entry as (key, child)) :: rest) =
                  if key = label then
                    let val child' = filter labels child
                    in
                      if is_empty child' then rest else (key, child') :: rest
                    end
                  else entry :: descend rest
          in
            NODE (tips, descend edges)
          end
  in
    filter (stored_labels patvars pat) net
  end

(* A query with only one successful tip list can return it directly. *)
fun join left [] = left
  | join left right = left @ right

fun follow checkpoint measured walk (tm, bvars) rest
      (NODE (_, edges)) suffix =
  let
    val vbranch =
      case edge checkpoint V edges of
          NONE => suffix
        | SOME node => walk rest node suffix
    fun exact label more =
      case edge checkpoint label edges of
          NONE => vbranch
        | SOME node =>
            (* Pass wildcard matches down as the suffix for exact matches.
               Measured walks still charge for the historical joins. *)
            if measured then
              appendMeasured checkpoint (walk more node []) vbranch
            else walk more node vbranch
  in
    case query_label checkpoint bvars tm of
        NONE => vbranch
      | SOME Lam =>
          let val (bvar, body) = dest_abs tm
          in exact Lam ((body, bvar :: bvars) :: rest)
          end
      | SOME Cmb =>
          let val (rator, rand) = dest_comb tm
          in exact Cmb ((rator, bvars) :: (rand, bvars) :: rest)
          end
      | SOME label => exact label rest
  end

fun match tm net =
  let
    fun walk [] (NODE (tips, _)) suffix = join tips suffix
      | walk (_ :: _) (NODE (_, [])) suffix = suffix
      (* The sole wildcard consumes the entire pending subterm. *)
      | walk (_ :: rest) (NODE (_, [(V, child)])) suffix =
          walk rest child suffix
      | walk ((task, bvars) :: rest) node suffix =
          follow no_checkpoint false walk
            (eta_contract task, bvars) rest node suffix
  in
    walk [(tm, [])] net []
  end

fun unify_with checkpoint measured schematic q net =
  let
    fun concat_map f items = concatMapMeasured checkpoint f items
    fun bound tm bvars = existsMeasured checkpoint (aconv tm) bvars

    fun skip_one_m (NODE (_, edges)) =
      let
        val _ = checkpoint ()
        fun skip_edge (V, child) = [child]
          | skip_edge (Cnst _, child) = [child]
          | skip_edge (Fvar _, child) = [child]
          | skip_edge (Lam, child) = skip_one_m child
          | skip_edge (Cmb, child) =
              concat_map skip_one_m (skip_one_m child)
      in
        concat_map skip_edge edges
      end

    (* Skipping an application adds one pending operand after consuming
       the application itself; an abstraction leaves its body pending.
       Prepend matches from completed subterms in edge order. *)
    fun skip_unmeasured visit pending (node as NODE (_, edges)) suffix =
      if pending = 0 then visit node suffix
      else
        List.foldr
          (fn ((label, child), sofar) =>
            skip_unmeasured visit
              (case label of Cmb => pending + 1
                           | Lam => pending
                           | _ => pending - 1)
              child sofar)
          suffix edges

    fun walk [] (NODE (tips, _)) suffix = (checkpoint (); join tips suffix)
      | walk (task :: rest) (node as NODE (_, edges)) suffix =
          if measured then walk_term task rest node suffix
          else
            case edges of
                [] => suffix
              | [(V, child)] => walk rest child suffix
              | _ => walk_term task rest node suffix
    and walk_term (tm0, bvars) rest node suffix =
      let
        val _ = checkpoint ()
        val tm = eta_contract tm0
      in
        if is_var tm andalso not (bound tm bvars) andalso schematic tm then
          if measured then
            concat_map (fn child => walk rest child []) (skip_one_m node)
          else skip_unmeasured (walk rest) 1 node suffix
        else
          follow checkpoint measured walk (tm, bvars) rest node suffix
      end
  in
    walk [(q, [])] net []
  end

fun unify {q, qvars} net =
  unify_with no_checkpoint false (fn v => HOLset.member (qvars, v)) q net

fun unifyMeasured checkpoint (query as {q, qvars}) net =
  if Portable.pointer_eq (checkpoint, no_checkpoint) then unify query net
  else unify_with checkpoint true (fn v => HOLset.member (qvars, v)) q net

(* Eta contraction adds no free variables and the walk already excludes
   opened binders before testing whether a variable is schematic. *)
fun unifyFreesMeasured checkpoint q net =
  unify_with checkpoint
    (not (Portable.pointer_eq (checkpoint, no_checkpoint))) (K true) q net

fun vfilter pred net =
  let
    fun filt (NODE (tips, edges)) =
      let
        fun filt_edges [] = []
          | filt_edges ((label, node) :: rest) =
              let val node' = filt node
              in
                if is_empty node' then filt_edges rest
                else (label, node') :: filt_edges rest
              end
      in
        NODE (List.filter pred tips, filt_edges edges)
      end
  in
    filt net
  end

fun listItems (NODE (tips, edges)) =
  tips @ List.concat (map (listItems o #2) edges)

end
