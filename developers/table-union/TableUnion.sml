(* Prototype: the values of three ancestry tables (TypeBase, the grammars,
   the srw simpset) built as structural unions of their parents' values,
   instead of by replaying deltas.

   Every entry carries an origin stamp (height, theory, seq): height is the
   theory's longest parent path from "min", seq the delta's index in its
   theory.  Ordered lexicographically, stamps respect ancestry and do not
   depend on load order, so they define a canonical order.  A table's
   value is its finished structure plus a map from entry key to the stamp
   of the delta that last set the entry, with a tag saying whether that
   delta added it (front or back) or removed it.  Union keeps the later
   stamp per key and moves the entries whose stamp the second operand wins
   from its finished structure into the first one's.  Shared ancestors give
   equal stamps, so they move nothing, and union (A, A) = A.

   Used by bench.sml; nothing here is part of HOL's load path. *)

structure TableUnion =
struct

open HolKernel boolLib

(* ----------------------------------------------------------------------
    Stamps
   ---------------------------------------------------------------------- *)

type estamp = int * string * int
fun ecmp ((h1, t1, s1) : estamp, (h2, t2, s2) : estamp) =
    case Int.compare (h1, h2) of
        EQUAL => (case String.compare (t1, t2) of
                      EQUAL => Int.compare (s1, s2)
                    | r => r)
      | r => r

(* tag: 0 = removed, 1 = added (front), 2 = added (back) *)
type stamps = (estamp * int) Symtab.table

(* Join two stamp tables keeping the later stamp per key.  Also returns
   the keys on which the operands disagree in a way the finished
   structures must reflect: those b wins (fromB = true), and those a wins
   where a's entry is removed and b's is live (fromB = false). *)
fun join (a : stamps, b : stamps) =
    if Portable.pointer_eq (a, b) then (a, [])
    else
      Symtab.fold
        (fn (k, vb) => fn (acc, d) =>
            case Symtab.lookup acc k of
                NONE => (Symtab.update (k, vb) acc, (k, vb, true) :: d)
              | SOME va =>
                case ecmp (#1 vb, #1 va) of
                    GREATER => (Symtab.update (k, vb) acc, (k, vb, true) :: d)
                  | EQUAL => (acc, d)
                  | LESS => if #2 va = 0 andalso #2 vb <> 0
                            then (acc, (k, va, false) :: d)
                            else (acc, d))
        b (a, [])

(* ----------------------------------------------------------------------
    The theory graph: heights and the canonical rank of a theory
   ---------------------------------------------------------------------- *)

fun thy_parents t = List.filter (fn p => p <> t) (Theory.parents t)
val heights = ref (Symtab.empty : int Symtab.table)
fun height t =
    case Symtab.lookup (!heights) t of
        SOME h => h
      | NONE =>
        let val h = if t = "min" then 0
                    else 1 + List.foldl Int.max 0 (map height (thy_parents t))
        in heights := Symtab.update (t, h) (!heights); h end
fun stamp t i : estamp = (height t, t, i)
fun canon_cmp (a, b) = ecmp (stamp a 0, stamp b 0)
fun canon_sort l = Listsort.sort canon_cmp l

(* the ancestor-closed cone of t under a parents function, canonical order *)
fun cone parents t =
    let
      fun visit (x, seen) =
          if HOLset.member (seen, x) then seen
          else List.foldl visit (HOLset.add (seen, x)) (parents x)
    in
      canon_sort (HOLset.listItems (visit (t, HOLset.empty String.compare)))
    end

(* An int that orders like the stamp, for the pretty-printer's overload
   timestamps; valid within one process (the rank of a theory depends on
   the set of theories loaded). *)
val rank_tab = ref (Symtab.empty : int Symtab.table)
fun set_ranks thys =
    rank_tab := #2 (List.foldl (fn (t, (i, m)) => (i + 1, Symtab.update (t, i) m))
                               (1, Symtab.empty) (canon_sort thys))
fun int_stamp ((_, t, i) : estamp) =
    valOf (Symtab.lookup (!rank_tab) t) * 1048576 + i + 1

(* ----------------------------------------------------------------------
    TypeBase
   ---------------------------------------------------------------------- *)

type tbv = {tb : TypeBasePure.typeBase, st : stamps}

(* entries are keyed by type pattern: pred_set and bag both describe
   instances of min$fun *)
fun tystr ty =
    if is_vartype ty then dest_vartype ty
    else
      let val {Thy, Tyop, Args} = dest_thy_type ty
      in Thy ^ "$" ^ Tyop ^ "(" ^ String.concatWith "," (map tystr Args) ^ ")"
      end
fun normty ty =
    let
      val tvs = type_vars ty
      val new = List.tabulate (length tvs,
                               fn i => mk_vartype ("'z" ^ Int.toString i))
    in
      type_subst (ListPair.map (fn (a, b) => {redex = a, residue = b})
                               (tvs, new)) ty
    end
fun tbkey tyi = tystr (normty (TypeBasePure.ty_of tyi))

(* field-wise: Poly/ML may copy a record, so its own address means little *)
fun tb_same (A : tbv, B : tbv) =
    Portable.pointer_eq (#tb A, #tb B) andalso Portable.pointer_eq (#st A, #st B)
fun tb_union (A : tbv, B : tbv) : tbv =
    if tb_same (A, B) then A
    else
      let
        val (st, diffs) = join (#st A, #st B)
        fun fetch k =
            valOf (List.find (fn tyi => tbkey tyi = k)
                             (TypeBasePure.listItems (#tb B)))
        fun move ((k, _, true), tb) = TypeBasePure.insert tb (fetch k)
          | move (_, tb) = tb
      in
        {tb = List.foldl move (#tb A) diffs, st = st}
      end

fun tb_own t ({tb, st} : tbv) : tbv =
    let
      val ds = TypeBase.thy_updates {thyname = t}
      fun add (tyi, (i, tb, st)) =
          (i + 1, TypeBasePure.insert tb tyi,
           Symtab.update (tbkey tyi, (stamp t i, 1)) st)
      val (_, tb, st) = List.foldl add (0, tb, st) ds
    in
      {tb = tb, st = st}
    end

fun tb_replay thys tb0 =
    List.foldl (fn (t, tb) => List.foldl (fn (tyi, tb) => TypeBasePure.insert tb tyi)
                                         tb (TypeBase.thy_updates {thyname = t}))
               tb0 thys

(* ----------------------------------------------------------------------
    srw simpset
   ---------------------------------------------------------------------- *)

type ssv = {ss : simpLib.simpset, st : stamps}

fun ss_deltas t = ThmSetData.theory_data {settype = "simp", thy = t}

(* the frag and removals a theory's [simp] deltas make, as
   BasicProvers's finaliser does *)
fun ss_frag t =
    let
      val ds = ss_deltas t
      val adds = List.mapPartial (fn ThmSetData.ADD p => SOME p | _ => NONE) ds
      val rms = List.mapPartial (fn ThmSetData.REMOVE s => SOME s | _ => NONE) ds
    in
      (simpLib.named_rewrites_with_names t (List.rev adds), rms)
    end
fun ss_apply (frag, rms) ss =
    let val ss = simpLib.++ (ss, frag)
    in if null rms then ss
       else simpLib.-* (ss, rms) handle Conv.UNCHANGED => ss
    end

(* key of a net entry: "Thy.Name" of the rewrite it came from *)
fun tip_key (SOME thy, name) =
    let
      val b = if String.isPrefix "rewrite:" name
              then String.extract (name, 8, NONE) else name
      val b = case String.fields (fn c => c = #".") b of
                  [x] => x
                | xs => String.concatWith "." (List.take (xs, length xs - 1))
    in
      SOME (thy ^ "." ^ b)
    end
  | tip_key (NONE, _) = NONE

(* entries compare by the theory of their stamp only, so that one
   theory's entries at a net node form a run *)
fun tip_cmp st (a, b) =
    let
      fun origin x =
          case Option.mapPartial (fn k => Symtab.lookup st k) (tip_key x) of
              SOME ((h, t, _), _) => (h, t)
            | NONE => (~1, "")
    in
      pair_compare (Int.compare, String.compare) (origin a, origin b)
    end

fun ss_same (A : ssv, B : ssv) =
    Portable.pointer_eq (#ss A, #ss B) andalso Portable.pointer_eq (#st A, #st B)
fun ss_union (A : ssv, B : ssv) : ssv =
    if ss_same (A, B) then A
    else
      let
        val (st, diffs) = join (#st A, #st B)
        val ss = simpLib.union_ss (tip_cmp st) (#ss A, #ss B)
        val removed = List.mapPartial (fn (k, (_, 0), _) => SOME k | _ => NONE)
                                      diffs
        val ss = if null removed then ss
                 else simpLib.-* (ss, removed) handle Conv.UNCHANGED => ss
      in
        {ss = ss, st = st}
      end

fun ss_own t ({ss, st} : ssv) : ssv =
    let
      val ds = ss_deltas t
      val fr = ss_frag t
      fun key (ThmSetData.ADD ({Thy, Name}, _)) = (Thy ^ "." ^ Name, 1)
        | key (ThmSetData.REMOVE s) = (s, 0)
      val (_, st) =
          List.foldl (fn (d, (i, st)) =>
                         let val (k, tag) = key d
                         in (i + 1, Symtab.update (k, (stamp t i, tag)) st) end)
                     (0, st) ds
    in
      {ss = ss_apply fr ss, st = st}
    end

val initial_simpset =
    simpLib.++ (simpLib.++ (simpLib.++ (simpLib.++ (simpLib.++ (
      boolSimps.bool_ss, combinSimps.COMBIN_ss), boolSimps.NORMEQ_ss),
      boolSimps.ABBREV_ss), boolSimps.LABEL_CONG_ss), boolSimps.HIDE_ss)

fun ss_replay thys ss0 =
    List.foldl (fn (t, ss) => ss_apply (ss_frag t) ss) ss0 thys

(* ----------------------------------------------------------------------
    Grammars

    Overloads (nearly all grammar deltas) are unioned per entry: key
    "name|constant", its stamp tagged front or back.  The other deltas
    (rules, tokens, the type grammar, numerals, user printers, ...) are a
    few hundred; the value keeps them as a stamped list, and when union
    brings in ones the first operand lacks, those parts of the grammar are
    rebuilt by applying the merged list in stamp order to the "min"
    grammar.
   ---------------------------------------------------------------------- *)

open GrammarDeltas term_grammar_dtype

type gv = {tyg : type_grammar.grammar, tmg : term_grammar.grammar,
           st : stamps, small : (estamp * gdelta) list (* latest first *)}

fun tmstr tm =
    case dest_term tm of
        VAR (s, ty) => "V" ^ s ^ ":" ^ tystr ty
      | CONST {Name, Thy, Ty} => "C" ^ Thy ^ "$" ^ Name ^ ":" ^ tystr Ty
      | COMB (f, x) => "(" ^ tmstr f ^ " " ^ tmstr x ^ ")"
      | LAMB (v, b) => "\\" ^ tmstr v ^ "." ^ tmstr b
(* overloads and their removals match terms up to alpha (aconv); a
   constant may be overloaded at several of its type instances *)
fun tmkey tm = tmstr tm
fun constkey {Thy, Name} =
    tmstr (prim_mk_const {Thy = Thy, Name = Name})
    handle HOL_ERR _ => "C" ^ Thy ^ "$" ^ Name
(* Keys: "name|const" for the parse map, "P|name|const" for the print
   map (MOVE_OVLPOSN changes only the first), "name|*" for CLR_OVL. *)
fun okey (s, k) = s ^ "\001" ^ k
fun pkey k = "P\001" ^ k
fun clrkey s = okey (s, "*")
fun fields k = String.fields (fn c => c = #"\001") k

(* overload deltas: SOME (keys set, with their tags; the entry printed) *)
fun ovl_delta d =
    let fun both k tag = [(k, tag), (pkey k, tag)]
    in
      case d of
          TMD (OVERLOAD_ON (s, tm)) => SOME (both (okey (s, tmkey tm)) 1, SOME (s, tm))
        | TMD (IOVERLOAD_ON (s, tm)) => SOME (both (okey (s, tmkey tm)) 2, SOME (s, tm))
        | TMD (RMOVMAP (s, kid)) => SOME (both (okey (s, constkey kid)) 0, NONE)
        | TMD (GRMOVMAP (s, tm)) => SOME (both (okey (s, tmkey tm)) 0, NONE)
        | TMD (MOVE_OVLPOSN {frontp, skid = (s, kid)}) =>
            SOME ([(okey (s, constkey kid), if frontp then 1 else 2)], NONE)
        | TMD (CLR_OVL s) => SOME ([(clrkey s, 0)], NONE)
        | _ => NONE
    end

fun gapply (TYD d) (tyg, tmg) = (type_grammar.apply_delta d tyg, tmg)
  | gapply (TMD d) (tyg, tmg) = (tyg, term_grammar.add_delta d tmg)

structure PM = Overload.PrintMap
fun pm_key c = (free_vars c, #2 (strip_abs c))
fun pm_set (pm, s, c, ts) = PM.insert (pm, pm_key c, (c, s, ts))
fun pm_remove (pm, s, c) =
    let
      val k = pm_key c
      val (pm', old) = PM.delete (pm, k)
      val keep = List.filter (fn (t, s', _) => not (s' = s andalso aconv t c))
                             (PM.Set.listItems old)
    in
      List.foldl (fn (v, pm) => PM.insert (pm, k, v)) pm' keep
    end handle PM.NotFound => pm
fun pm_ts (stp, tag) = if tag = 2 then ~ (int_stamp stp) else int_stamp stp

fun live st n stp =
    case Symtab.lookup st (clrkey n) of
        SOME (cs, _) => ecmp (stp, cs) = GREATER
      | NONE => true

(* rebuild the overload entry for each name some diff touches *)
fun ovl_union (oA, oB, st, diffs) =
    let
      val (pA, pmA) = Overload.dest_oinfo oA
      val (pB, _) = Overload.dest_oinfo oB
      val names = List.foldl (fn ((k, _, _), s) =>
                                 case fields k of
                                     [n, _] => HOLset.add (s, n)
                                   | _ => s)
                             (HOLset.empty String.compare) diffs
      fun ops p n = case Symtab.lookup p n of
                        SOME {actual_ops, ...} => actual_ops
                      | NONE => []
      fun rebuild (n, p) =
          let
            val opsA = ops pA n
            val cands =
                List.foldl (fn (c, acc) =>
                               if List.exists (fn (k, _) => k = tmkey c) acc
                               then acc else acc @ [(tmkey c, c)])
                           [] (opsA @ ops pB n)
            fun entry (k, c) =
                case Symtab.lookup st (okey (n, k)) of
                    SOME (stp, tag) =>
                      if tag <> 0 andalso live st n stp
                      then SOME (SOME (stp, tag), c) else NONE
                  | NONE => if isSome (Symtab.lookup st (clrkey n)) then NONE
                            else SOME (NONE, c)
            val es = List.mapPartial entry cands
            fun stamped tag = List.mapPartial
                                (fn (SOME (stp, t), c) => if t = tag then SOME (stp, c)
                                                          else NONE
                                  | _ => NONE) es
            val fronts = Listsort.sort (fn ((a, _), (b, _)) => ecmp (b, a))
                                       (stamped 1)
            val backs = Listsort.sort (fn ((a, _), (b, _)) => ecmp (a, b))
                                      (stamped 2)
            val base = List.mapPartial (fn (NONE, c) => SOME c | _ => NONE) es
            val ops' = map #2 fronts @ base @ map #2 backs
          in
            if null ops' then Symtab.delete_safe n p
            else Symtab.update (n, Overload.mk_op_info ops') p
          end
      val p = HOLset.foldl rebuild pA names
      (* print map: entries b wins are set or removed in a's *)
      fun term_of (n, ck) =
          List.find (fn c => tmkey c = ck) (ops pB n @ ops pA n)
      fun pmove ((k, (stp, tag), true), pm) =
          (case fields k of
               ["P", n, ck] =>
               (case term_of (n, ck) of
                    NONE => pm
                  | SOME c => if tag = 0 then pm_remove (pm, n, c)
                              else pm_set (pm, n, c, pm_ts (stp, tag)))
             | _ => pm)
        | pmove (_, pm) = pm
      val pm = List.foldl pmove pmA diffs
      (* a CLR_OVL b wins removes every older print entry of its name *)
      val clrs = List.mapPartial
                   (fn (k, (cs, _), true) =>
                       (case fields k of [n, "*"] => SOME (n, cs) | _ => NONE)
                     | _ => NONE) diffs
      fun cleared (c, n) =
          case List.find (fn (n', _) => n' = n) clrs of
              NONE => false
            | SOME (_, cs) =>
              case Symtab.lookup st (pkey (okey (n, tmkey c))) of
                  SOME (stp, _) => ecmp (stp, cs) = LESS
                | NONE => true
      val pm = if null clrs then pm
               else PM.fold (fn (k, v as (c, n, _), acc) =>
                                if cleared (c, n) then acc else PM.insert (acc, k, v))
                            PM.empty pm
    in
      Overload.mk_oinfo (p, pm)
    end

(* merge two latest-first stamped lists; changed = b had entries a lacks *)
fun small_merge (xs, ys) =
    let
      fun go (acc, ch, [], []) = (List.rev acc, ch)
        | go (acc, ch, x :: xs, []) = go (x :: acc, ch, xs, [])
        | go (acc, ch, [], y :: ys) = go (y :: acc, true, [], ys)
        | go (acc, ch, xl as (x :: xs), yl as (y :: ys)) =
          case ecmp (#1 x, #1 y) of
              GREATER => go (x :: acc, ch, xs, yl)
            | LESS => go (y :: acc, true, xl, ys)
            | EQUAL => go (x :: acc, ch, xs, ys)
    in
      if Portable.pointer_eq (xs, ys) then (xs, false) else go ([], false, xs, ys)
    end

fun g_same (A : gv, B : gv) =
    Portable.pointer_eq (#tyg A, #tyg B) andalso
    Portable.pointer_eq (#tmg A, #tmg B) andalso
    Portable.pointer_eq (#st A, #st B) andalso
    Portable.pointer_eq (#small A, #small B)
fun g_union (A : gv, B : gv) : gv =
    if g_same (A, B) then A
    else
      let
        val (st, diffs) = join (#st A, #st B)
        val oi = if null diffs then term_grammar.overload_info (#tmg A)
                 else ovl_union (term_grammar.overload_info (#tmg A),
                                 term_grammar.overload_info (#tmg B), st, diffs)
        val (small, changed) = small_merge (#small A, #small B)
        val (tyg, tmg) =
            if changed then
              List.foldr (fn ((_, d), g) => gapply d g) Parse.min_grammars small
            else (#tyg A, #tmg A)
        val tmg = term_grammar.fupdate_overload_info (K oi) tmg
      in
        {tyg = tyg, tmg = tmg, st = st, small = small}
      end

fun g_deltas t = GrammarDeltas.thy_deltas {thyname = t}

fun g_own t ({tyg, tmg, st, small} : gv) : gv =
    let
      val ds = g_deltas t
      fun step (d, (i, g, st, small, prints)) =
          let
            val g = gapply d g
            (* MOVE_OVLPOSN moves only a live entry *)
            fun settag (k, tag) =
                if tag = 0 orelse not (null (tl (fields k)) andalso false) then tag
                else tag
          in
            case ovl_delta d of
                SOME (keys, pr) =>
                let
                  fun upd ((k, tag), st) =
                      let
                        val tag =
                            if isSome pr orelse tag = 0 then tag
                            else case Symtab.lookup st k of
                                     SOME (_, t') => if t' = 0 then 0 else tag
                                   | NONE => 0
                      in
                        Symtab.update (k, (stamp t i, tag)) st
                      end
                in
                  (i + 1, g, List.foldl upd st keys, small,
                   case (pr, keys) of
                       (SOME (s, c), (_, tag) :: _) => (stamp t i, tag, s, c) :: prints
                     | _ => prints)
                end
              | NONE => (i + 1, g, st, (stamp t i, d) :: small, prints)
          end
      val (_, (tyg, tmg), st, small, prints) =
          List.foldl step (0, (tyg, tmg), st, small, []) ds
      (* give this theory's print-map entries their canonical timestamps;
         an entry later removed in the same theory stays removed *)
      fun fix ((stp, tag, s, c), oi) =
          case Symtab.lookup st (pkey (okey (s, tmkey c))) of
              SOME (stp', tag') =>
                if ecmp (stp, stp') = EQUAL andalso tag' <> 0 then
                  let val (p, pm) = Overload.dest_oinfo oi
                  in Overload.mk_oinfo (p, pm_set (pm, s, c, pm_ts (stp, tag)))
                  end
                else oi
            | NONE => oi
      val tmg =
          if null prints then tmg
          else term_grammar.fupdate_overload_info
                 (fn oi => List.foldl fix oi prints) tmg
    in
      {tyg = tyg, tmg = tmg, st = st, small = small}
    end

(* canonical replay, with the same timestamp fix-up as g_own *)
fun g_replay thys g0 =
    List.foldl (fn (t, g) =>
                   let val {tyg, tmg, ...} =
                           g_own t {tyg = #1 g, tmg = #2 g, st = Symtab.empty,
                                    small = []}
                   in (tyg, tmg) end)
               g0 thys

(* ----------------------------------------------------------------------
    Building every value of a cone bottom-up
   ---------------------------------------------------------------------- *)

(* values : string -> 'v option; returns the table of values and the time
   each theory's union + own deltas took *)
fun build {parents, base : 'v, union : 'v * 'v -> 'v, own : string -> 'v -> 'v}
          thys =
    let
      fun value tab t = valOf (Symtab.lookup tab t)
      fun step (t, (tab, times)) =
          if t = "min" then (Symtab.update (t, base) tab, times)
          else
            let
              val ps = Listsort.sort (fn (a, b) => canon_cmp (b, a)) (parents t)
              val timer = Timer.startRealTimer ()
              val v = case ps of
                          [] => base
                        | p :: rest => List.foldl (fn (q, v) => union (v, value tab q))
                                                  (value tab p) rest
              val v = own t v
              val dt = Timer.checkRealTimer timer
            in
              (Symtab.update (t, v) tab, (t, dt) :: times)
            end
    in
      List.foldl step (Symtab.empty, []) thys
    end

end (* struct *)
