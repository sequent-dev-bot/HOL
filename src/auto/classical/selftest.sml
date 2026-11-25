open HolKernel testutils searchHeap

(* Keep this large, historically written test file readable while the tactic
   API carries an explicit context.  The production tests below intentionally
   exercise the old two-argument VALID convenience shape. *)
structure SelfTestTactical = Tactical
structure Tactical =
struct
  open SelfTestTactical
  fun VALID tactic goal =
    SelfTestTactical.VALID tactic goal (Context.snapshot())
end

fun test (name, check) =
  (tprint name;
   if check () then OK () else die "failed")

fun the_store (SOME store) = store
  | the_store NONE = raise Fail "unexpected metavariable binding failure"

fun the_singleton [value] = value
  | the_singleton _ = raise Fail "expected one value"

fun int_compare (x : int, y : int) =
  if x < y then LESS else if x > y then GREATER else EQUAL

fun from_list compare values =
  List.foldl (fn (x, heap) => add x heap) (empty compare) values

fun key_compare ((key1, _) : int * string, (key2, _)) =
  int_compare (key1, key2)

val duplicate_heap =
  from_list key_compare [(2, "c"), (1, "a"), (3, "d"), (1, "b")]

val _ =
  test
    ("delete_all_min pops every entry with the minimal key",
     fn () =>
       let
         val (entries, rest) = delete_all_min duplicate_heap
         val payloads = map #2 entries
         val (second, final) = delete_all_min rest
      in
         length entries = 2 andalso
         List.all (fn (key, _) => key = 1) entries andalso
         List.exists (fn value => value = "a") payloads andalso
         List.exists (fn value => value = "b") payloads andalso
         map #1 second = [2] andalso
         not (is_empty final)
       end)

fun raises_empty f =
  (f (); false) handle Empty => true | _ => false

val _ =
  test
    ("delete_all_min fails on an empty heap",
     fn () =>
       let
         val heap : int heap = empty int_compare
       in
         raises_empty (fn () => ignore (delete_all_min heap))
       end)

val bool_ty = Type.bool
val fixed = Term.mk_var ("fixed", bool_ty)

val _ =
  test
    ("classical conversions reduce mixed redexes beside a rigid projection",
     fn () =>
       let
         val input =
           ``(((\x:'a. x) (FST (a:'a,b:'b))) IN
              (\y. R y (SND (a,b)))) /\ FST (p:bool # 'b)``
         val reduced = ``R (a:'a) (b:'b) /\ FST (p:bool # 'b)``
         val applied =
           ``R (FST (a:'a,b:'b)) (SND (a,b)) /\ FST (p:bool # 'b)``
         val eta = ``\x:'a. P x : bool``
         fun converts conv tm target =
           let
             val result = conv tm
             val (left, right) = boolSyntax.dest_eq (concl result)
           in
             null (hyp result) andalso aconv left tm andalso aconv right target
           end
       in
         converts clasetNorm.reduce_conv input reduced andalso
         converts clasetNorm.goal_reduce_conv input reduced andalso
         converts clasetNorm.applied_conv input applied andalso
         converts clasetNorm.reduce_conv eta ``P:'a -> bool`` andalso
         converts clasetNorm.goal_reduce_conv eta eta
       end)

fun beta_eta_term tm =
  #2
    (boolSyntax.dest_eq
      (concl
        (Conv.QCONV
          (Conv.REDEPTH_CONV
            (Conv.ORELSEC (BETA_CONV, Drule.ETA_CONV))) tm)))

val _ =
  test
    ("metavariable create bind and walk round-trip",
     fn () =>
       let
         val (m, store0) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
       in
         clasetMeta.is_meta m andalso
         length (clasetMeta.metas_of store0 (boolSyntax.mk_eq (m, m))) = 1
         andalso
         case clasetMeta.bind (m, fixed) store0 of
           NONE => false
         | SOME store1 =>
             Term.aconv (clasetMeta.walk store1 m) fixed andalso
             Term.aconv (clasetMeta.norm store1 m) fixed
       end)

(* A metavariable created at a type that is still a type metavariable has
   two spellings once that type metavariable is bound: the one it was
   created with, which [bindings] keeps reporting, and the refined one a
   normalized term carries.  Whoever keys a set or a lookup on metavariable
   identity must see those as one metavariable. *)
val _ =
  test
    ("metavariable identity ignores a type binding respelling",
     fn () =>
       let
         val (tymeta, store0) = clasetMeta.new_tymeta clasetMeta.empty
         val (m, store1) =
           clasetMeta.new_meta {allow = [], ty = tymeta} store0
         val (other, store2) =
           clasetMeta.new_meta {allow = [], ty = tymeta} store1
         val store3 =
           the_store (clasetMeta.bind_ty (tymeta, bool_ty) store2)
         val predicate =
           Term.mk_var ("respelling_predicate", tymeta --> bool_ty)
         val respelt =
           case
             clasetMeta.metas_of store3 (Term.mk_comb (predicate, m))
           of
               [only] => only
             | _ => fixed
       in
         Term.compare (m, respelt) <> EQUAL andalso
         clasetMeta.meta_compare (m, respelt) = EQUAL andalso
         clasetMeta.meta_compare (m, other) <> EQUAL andalso
         clasetMeta.meta_compare (fixed, fixed) = EQUAL andalso
         clasetMeta.meta_compare (m, fixed) = LESS andalso
         clasetMeta.meta_compare (fixed, m) = GREATER
       end)

val _ =
  test
    ("normalization follows bindings and contracts beta and eta",
     fn () =>
       let
         val fun_ty = bool_ty --> bool_ty
         val x = Term.mk_var ("x", bool_ty)
         val f = Term.mk_var ("f", fun_ty)
         val identity = Term.mk_abs (x, x)
         val (m, store0) =
           clasetMeta.new_meta {allow = [], ty = fun_ty}
             clasetMeta.empty
         val store1 = the_store (clasetMeta.bind (m, identity) store0)
         val beta_term = Term.mk_comb (m, boolSyntax.T)
         val eta_term = Term.mk_abs (x, Term.mk_comb (f, x))
       in
         Term.aconv (clasetMeta.norm store1 beta_term) boolSyntax.T
         andalso Term.aconv (clasetMeta.norm store1 eta_term) f
       end)

val _ =
  test
    ("term walks ignore unrelated historical type bindings",
     fn () =>
       let
         fun add_types 0 store = store
           | add_types remaining store =
               let
                 val (tymeta, store1) = clasetMeta.new_tymeta store
                 val store2 =
                   the_store (clasetMeta.bind_ty (tymeta, bool_ty) store1)
               in
                 add_types (remaining - 1) store2
               end
         val store = add_types 5000 clasetMeta.empty
         fun walk 0 = true
           | walk remaining =
               Term.aconv
                 (clasetMeta.walk store boolSyntax.T) boolSyntax.T andalso
               walk (remaining - 1)
       in
         Timeout.apply (Time.fromSeconds 3) walk 20000
         handle Timeout.TIMEOUT _ => false
       end)

val _ =
  test
    ("bind rejects occurs-check and allow-set violations",
     fn () =>
       let
         val eigen = Term.mk_var ("eigen", bool_ty)
         val generated_eigen = Term.genvar bool_ty
         val (blocked, store0) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val (permitted, store1) =
           clasetMeta.new_meta {allow = [eigen], ty = bool_ty} store0
         val (indirect, store2) =
           clasetMeta.new_meta {allow = [], ty = bool_ty} store1
         val store3 =
           the_store (clasetMeta.bind (indirect, permitted) store2)
         val cyclic =
           the_store (clasetMeta.bind (indirect, blocked) store2)
         val eigen_alias =
           the_store (clasetMeta.bind (permitted, eigen) store2)
         val registered =
           the_store
             (clasetMeta.register_eigen generated_eigen store0)
       in
         not (Option.isSome (clasetMeta.bind (blocked, blocked) store0))
         andalso
         Option.isSome
           (clasetMeta.bind (blocked, generated_eigen) store0)
         andalso
         not (Option.isSome
           (clasetMeta.bind (blocked, generated_eigen) registered))
         andalso
         not (Option.isSome (clasetMeta.bind (blocked, eigen) store1))
         andalso
         not (Option.isSome (clasetMeta.bind (blocked, indirect) cyclic))
         andalso
         not (Option.isSome (clasetMeta.bind (blocked, permitted) eigen_alias))
         andalso
         Option.isSome (clasetMeta.bind (blocked, fixed) store0)
         andalso
         Option.isSome (clasetMeta.bind (permitted, eigen) store1)
         andalso
         not (Option.isSome (clasetMeta.bind (permitted, eigen) store3))
       end)

val _ =
  test
    ("eigen lookup follows type bindings within a matching name",
     fn () =>
       let
         val (ty, store) = clasetMeta.new_tymeta clasetMeta.empty
         val name = "eigen_type_binding"
         val eigen = Term.mk_var (name, ty)
         val concrete = Term.mk_var (name, bool_ty)
         val registered = the_store (clasetMeta.register_eigen eigen store)
         val bound = the_store (clasetMeta.bind_ty (ty, bool_ty) registered)
       in
         not (clasetMeta.is_eigen registered concrete) andalso
         clasetMeta.is_eigen bound concrete andalso
         not (clasetMeta.is_eigen bound boolSyntax.T)
       end)

val _ =
  test
    ("stores are persistent",
     fn () =>
       let
         val (m, store0) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val store1 = the_store (clasetMeta.bind (m, fixed) store0)
       in
         Term.aconv (clasetMeta.walk store0 m) m andalso
         Term.aconv (clasetMeta.walk store1 m) fixed
       end)

val _ =
  test
    ("absorb merges all store tables and preserves eigen allow-sets",
     fn () =>
       let
         val left_eigen =
           Term.mk_var ("absorb_left_eigen", bool_ty)
         val right_eigen =
           Term.mk_var ("absorb_right_eigen", bool_ty)
         val (base_meta, base0) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val (base_tymeta, base) = clasetMeta.new_tymeta base0

         val (left_probe, left0) =
           clasetMeta.new_meta {allow = [left_eigen], ty = bool_ty}
             base
         val (left_bound, left1) =
           clasetMeta.new_meta {allow = [], ty = bool_ty} left0
         val left2 =
           the_store (clasetMeta.bind (left_bound, boolSyntax.T) left1)
         val (left_tymeta, left3) = clasetMeta.new_tymeta left2
         val left =
           the_store (clasetMeta.bind_ty (left_tymeta, bool_ty) left3)

         val (right_probe, right0) =
           clasetMeta.new_meta {allow = [right_eigen], ty = bool_ty}
             base
         val (right_bound, right1) =
           clasetMeta.new_meta {allow = [], ty = bool_ty} right0
         val right2 =
           the_store
             (clasetMeta.bind (right_bound, boolSyntax.F) right1)
         val (right_tymeta, right3) = clasetMeta.new_tymeta right2
         val right =
           the_store
             (clasetMeta.bind_ty (right_tymeta, Type.ind) right3)

         val merged =
           clasetMeta.absorb {base = base, extensions = [left, right]}
       in
         length (clasetMeta.metas_of merged base_meta) = 1 andalso
         Option.isSome
           (clasetMeta.bind_ty (base_tymeta, bool_ty) merged) andalso
         clasetMeta.is_eigen merged left_eigen andalso
         clasetMeta.is_eigen merged right_eigen andalso
         Option.isSome (clasetMeta.bind (left_probe, left_eigen) merged)
         andalso
         not (Option.isSome
           (clasetMeta.bind (left_probe, right_eigen) merged)) andalso
         Option.isSome
           (clasetMeta.bind (right_probe, right_eigen) merged) andalso
         not (Option.isSome
           (clasetMeta.bind (right_probe, left_eigen) merged)) andalso
         Term.aconv (clasetMeta.walk merged left_bound) boolSyntax.T
         andalso
         Term.aconv (clasetMeta.walk merged right_bound) boolSyntax.F
         andalso clasetMeta.norm_type merged left_tymeta = bool_ty
         andalso clasetMeta.norm_type merged right_tymeta = Type.ind
       end)

val _ =
  test
    ("absorb reports conflicting store entries",
     fn () =>
       let
         val (m, base) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val left = the_store (clasetMeta.bind (m, boolSyntax.T) base)
         val right = the_store (clasetMeta.bind (m, boolSyntax.F) base)
       in
         (ignore
            (clasetMeta.absorb
              {base = base, extensions = [left, right]});
          false)
         handle HOL_ERR error =>
           String.isSubstring "conflicting term binding entry"
             (Feedback.message_of error)
       end)

val _ =
  test
    ("stores reject forged and foreign metavariables",
     fn () =>
       let
         val (m, store0) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val (foreign, _) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val (name, _) = Term.dest_var m
         val forged = Term.mk_var (name, Type.ind)
         val (tymeta, store1) = clasetMeta.new_tymeta store0
         val (foreign_ty, _) = clasetMeta.new_tymeta clasetMeta.empty
       in
         not (Option.isSome
           (clasetMeta.bind (forged, Term.genvar Type.ind) store0))
         andalso
         not (Option.isSome (clasetMeta.bind (m, foreign) store0))
         andalso
         not (Option.isSome
           (clasetMeta.bind_ty (tymeta, tymeta) store1))
         andalso
         not (Option.isSome
           (clasetMeta.bind_ty (tymeta, foreign_ty) store1))
       end)

fun type_subst_eq [] [] = true
  | type_subst_eq
      ({redex = left_r, residue = left_s} :: left)
      ({redex = right_r, residue = right_s} :: right) =
      left_r = right_r andalso left_s = right_s andalso
      type_subst_eq left right
  | type_subst_eq _ _ = false

fun term_subst_eq [] [] = true
  | term_subst_eq
      ({redex = left_r, residue = left_s} :: left)
      ({redex = right_r, residue = right_s} :: right) =
      Term.aconv left_r right_r andalso Term.aconv left_s right_s andalso
      term_subst_eq left right
  | term_subst_eq _ _ = false

val _ =
  test
    ("ground is deterministic and grounds types before terms",
     fn () =>
       let
         val (tymeta, store0) = clasetMeta.new_tymeta clasetMeta.empty
         val (m, store1) =
           clasetMeta.new_meta {allow = [], ty = tymeta} store0
         val grounded1 = clasetMeta.ground store1
         val grounded2 = clasetMeta.ground store1
         val (tys1, tms1) = clasetMeta.collapse grounded1
         val (tys2, tms2) = clasetMeta.collapse grounded2
       in
         type_subst_eq tys1 tys2 andalso term_subst_eq tms1 tms2
         andalso length tys1 = 1 andalso length tms1 = 1
         andalso #residue (hd tys1) = bool_ty
         andalso Term.aconv (#redex (hd tms1))
           (Term.inst tys1 m)
         andalso Term.aconv (#residue (hd tms1))
           (boolSyntax.mk_arb bool_ty)
       end)

val _ =
  test
    ("collapse substitutions instantiate kernel theorems",
     fn () =>
       let
         val (tymeta1, store0) = clasetMeta.new_tymeta clasetMeta.empty
         val (tymeta2, store1) = clasetMeta.new_tymeta store0
         val (m1, store2) =
           clasetMeta.new_meta {allow = [], ty = tymeta1} store1
         val (m2, store3) =
           clasetMeta.new_meta {allow = [], ty = tymeta1} store2
         val theorem = ASSUME (boolSyntax.mk_eq (m1, m2))
         val store4 =
           the_store (clasetMeta.bind_ty (tymeta1, tymeta2) store3)
         val store5 =
           the_store (clasetMeta.bind_ty (tymeta2, bool_ty) store4)
         val store6 = the_store (clasetMeta.bind (m1, m2) store5)
         val store7 =
           the_store (clasetMeta.bind (m2, boolSyntax.T) store6)
         val (type_subst, term_subst) = clasetMeta.collapse store7
         val instantiated =
           Drule.INST_TY_TERM (term_subst, type_subst) theorem
       in
         length type_subst = 2 andalso length term_subst = 2
         andalso
         Term.aconv (concl instantiated)
           (boolSyntax.mk_eq (boolSyntax.T, boolSyntax.T))
       end)

val _ =
  test
    ("collapse normalizes a redex exposed by a late lambda binding",
     fn () =>
       let
         val x = Term.mk_var ("late_lambda_x", bool_ty)
         val identity = Term.mk_abs (x, x)
         val function_ty = bool_ty --> bool_ty
         val (dependency, store0) =
           clasetMeta.new_meta {allow = [], ty = function_ty}
             clasetMeta.empty
         val (outer, store1) =
           clasetMeta.new_meta {allow = [], ty = bool_ty} store0
         val raw_outer = Term.mk_comb (dependency, boolSyntax.T)
         val store2 =
           the_store (clasetMeta.bind (outer, raw_outer) store1)
         val store3 =
           the_store (clasetMeta.bind (dependency, identity) store2)
         val (type_substitution, term_substitution) =
           clasetMeta.collapse store3
         val kernel_result =
           Drule.INST_TY_TERM
             (term_substitution, type_substitution) (ASSUME outer)
         fun residue redex =
           Option.map #residue
             (List.find
               (fn substitution =>
                 Term.aconv (#redex substitution) redex)
               term_substitution)
       in
         null type_substitution andalso
         length term_substitution = 2 andalso
         Option.map (fn tm => Term.aconv tm identity)
           (residue dependency) = SOME true andalso
         Option.map (fn tm => Term.aconv tm boolSyntax.T)
           (residue outer) = SOME true andalso
         Term.aconv (concl kernel_result) boolSyntax.T andalso
         Term.aconv (clasetMeta.norm store3 outer) boolSyntax.T andalso
         Term.aconv
           (clasetMeta.instantiate store3 outer)
           (Term.mk_comb (identity, boolSyntax.T))
       end)

val _ =
  test
    ("bindings persist semantically normalized beta-dead residues",
     fn () =>
       let
         fun dead argument =
           let
             val ignored =
               Term.mk_var ("beta_dead_ignored", type_of argument)
           in
             Term.mk_comb
               (Term.mk_abs (ignored, boolSyntax.T), argument)
           end
         fun collapsed store target =
           let
             val (type_substitution, term_substitution) =
               clasetMeta.collapse store
           in
             concl
               (Drule.INST_TY_TERM
                 (term_substitution, type_substitution) (ASSUME target))
           end
         fun persistent_residue store target =
           case #terms (clasetMeta.bindings store) of
               [(redex, residue)] =>
                 Term.aconv redex target andalso
                 Term.aconv residue boolSyntax.T
             | _ => false
         fun accepts base target raw =
           case clasetMeta.bind (target, raw) base of
               SOME ordinary =>
                 persistent_residue ordinary target andalso
                 Term.aconv
                   (clasetMeta.norm ordinary target) boolSyntax.T andalso
                 Term.aconv (collapsed ordinary target) boolSyntax.T
             | _ => false

         val (self, self_store) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val (foreign_target, foreign_store) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val (foreign, _) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val eigen = Term.mk_var ("beta_dead_eigen", bool_ty)
         val (eigen_target, eigen_store0) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val eigen_store =
           the_store (clasetMeta.register_eigen eigen eigen_store0)
         val (type_target, type_store) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val (foreign_tymeta, _) =
           clasetMeta.new_tymeta clasetMeta.empty
         val typed_argument =
           Term.mk_var ("beta_dead_typed", foreign_tymeta)
         val cases =
           [(self_store, self, dead self),
            (foreign_store, foreign_target, dead foreign),
            (eigen_store, eigen_target, dead eigen),
            (type_store, type_target, dead typed_argument)]
       in
         List.all
           (fn (store, target, raw) =>
             not (Term.aconv raw boolSyntax.T) andalso
             accepts store target raw)
           cases
       end)

val _ =
  test
    ("three-meta term bindings expand in both orders without capture",
     fn () =>
       let
         val parameter = Term.mk_var ("capture_x", Type.ind)
         val bound = Term.mk_var ("capture_x", Type.ind)
         val relation =
           Term.mk_var
             ("capture_R", Type.ind --> Type.ind --> bool_ty)
         fun schema dependency =
           boolSyntax.mk_forall
             (bound,
              Term.list_mk_comb (relation, [dependency, bound]))
         val (leaf, store0) =
           clasetMeta.new_meta
             {allow = [parameter], ty = Type.ind}
             clasetMeta.empty
         val (middle, store1) =
           clasetMeta.new_meta
             {allow = [parameter], ty = Type.ind} store0
         val (outer, store2) =
           clasetMeta.new_meta
             {allow = [parameter], ty = bool_ty} store1
         val unresolved = schema middle
         val expected =
           Term.subst
             [{redex = middle, residue = parameter}] unresolved
         val normalized_expected = beta_eta_term expected
         val dependency_first =
           the_store (clasetMeta.bind (leaf, parameter) store2)
         val dependency_first =
           the_store
             (clasetMeta.bind (middle, leaf) dependency_first)
         val dependency_first =
           the_store
             (clasetMeta.bind (outer, unresolved) dependency_first)
         val outer_first =
           the_store (clasetMeta.bind (outer, unresolved) store2)
         val outer_first =
           the_store
             (clasetMeta.bind (middle, leaf) outer_first)
         val outer_first =
           the_store (clasetMeta.bind (leaf, parameter) outer_first)
         val (_, dependency_first_subst) =
           clasetMeta.collapse dependency_first
         val (_, outer_first_subst) = clasetMeta.collapse outer_first
         val dependency_first_theorem =
           Drule.INST_TY_TERM
             (dependency_first_subst, []) (ASSUME outer)
         val outer_first_theorem =
           Drule.INST_TY_TERM
             (outer_first_subst, []) (ASSUME outer)
         val direct =
           clasetMeta.norm outer_first unresolved
         val captured =
           boolSyntax.mk_forall
              (bound,
               Term.list_mk_comb (relation, [bound, bound]))
         fun exact_substitution substitution =
           let
             fun residue redex =
               Option.map #residue
                 (List.find
                   (fn entry => Term.aconv (#redex entry) redex)
                   substitution)
           in
             length substitution = 3 andalso
             Option.map (fn tm => Term.aconv tm parameter)
               (residue leaf) = SOME true andalso
             Option.map (fn tm => Term.aconv tm parameter)
               (residue middle) = SOME true andalso
             Option.map (fn tm => Term.aconv tm normalized_expected)
               (residue outer) = SOME true
           end
       in
         Term.aconv (clasetMeta.norm store2 outer) outer andalso
         Term.aconv
           (clasetMeta.norm dependency_first outer)
           normalized_expected andalso
         Term.aconv
           (clasetMeta.norm outer_first outer) normalized_expected andalso
         exact_substitution dependency_first_subst andalso
         exact_substitution outer_first_subst andalso
         Term.aconv
           (concl dependency_first_theorem) normalized_expected andalso
         Term.aconv
           (concl outer_first_theorem) normalized_expected andalso
         Term.aconv direct normalized_expected andalso
         not (Term.aconv captured expected)
       end)

val _ =
  test
    ("term expansion preserves unrelated and unbound dependencies",
     fn () =>
       let
         val parameter = Term.mk_var ("preserve_x", Type.ind)
         val bound = Term.mk_var ("preserve_x", Type.ind)
         val relation =
           Term.mk_var
             ("preserve_R", Type.ind --> Type.ind --> bool_ty)
         val (dependency, store0) =
           clasetMeta.new_meta
             {allow = [parameter], ty = Type.ind}
             clasetMeta.empty
         val (outer, store1) =
           clasetMeta.new_meta
             {allow = [parameter], ty = bool_ty} store0
         val (unrelated, store2) =
           clasetMeta.new_meta {allow = [], ty = bool_ty} store1
         val unresolved =
           boolSyntax.mk_forall
             (bound,
              Term.list_mk_comb (relation, [dependency, bound]))
         val store3 =
           the_store (clasetMeta.bind (outer, unresolved) store2)
         val store4 =
           the_store
             (clasetMeta.bind (unrelated, boolSyntax.T) store3)
         val (_, substitution) = clasetMeta.collapse store4
         val instantiated =
           Drule.INST_TY_TERM (substitution, []) (ASSUME outer)
       in
         Term.aconv
           (clasetMeta.norm store4 outer) (beta_eta_term unresolved)
         andalso
         Term.aconv (concl instantiated) (beta_eta_term unresolved)
         andalso
         Term.aconv
           (clasetMeta.norm store4 boolSyntax.F) boolSyntax.F
       end)

val _ =
  test
    ("shared and duplicated dependencies expand to exact substitutions",
     fn () =>
       let
         val (leaf, store0) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val (left, store1) =
           clasetMeta.new_meta {allow = [], ty = bool_ty} store0
         val (right, store2) =
           clasetMeta.new_meta {allow = [], ty = bool_ty} store1
         val (outer, store3) =
           clasetMeta.new_meta {allow = [], ty = bool_ty} store2
         val raw =
           boolSyntax.mk_conj
             (left, boolSyntax.mk_conj (left, right))
         val expected =
           boolSyntax.mk_conj
             (boolSyntax.T,
              boolSyntax.mk_conj (boolSyntax.T, boolSyntax.T))
         val store4 = the_store (clasetMeta.bind (outer, raw) store3)
         val store5 = the_store (clasetMeta.bind (left, leaf) store4)
         val store6 = the_store (clasetMeta.bind (right, leaf) store5)
         val store7 =
           the_store (clasetMeta.bind (leaf, boolSyntax.T) store6)
         val (type_substitution, term_substitution) =
           clasetMeta.collapse store7
         val theorem =
           Drule.INST_TY_TERM
             (term_substitution, type_substitution) (ASSUME outer)
         fun residue redex =
           Option.map #residue
             (List.find
               (fn entry => Term.aconv (#redex entry) redex)
               term_substitution)
         fun is_truth redex =
           Option.map (fn tm => Term.aconv tm boolSyntax.T)
             (residue redex) = SOME true
       in
         null type_substitution andalso
         length term_substitution = 4 andalso
         is_truth leaf andalso is_truth left andalso is_truth right andalso
         Option.map (fn tm => Term.aconv tm expected)
           (residue outer) = SOME true andalso
         Term.aconv (clasetMeta.norm store7 outer) expected andalso
         Term.aconv (concl theorem) expected
       end)

val _ =
  test
    ("indirect store cycles are rejected persistently by both bind paths",
     fn () =>
       let
         fun invariant store first second =
           let
             val bindings = clasetMeta.bindings store
             val (_, substitution) = clasetMeta.collapse store
           in
             null (#types bindings) andalso
             (case #terms bindings of
                  [(redex, residue)] =>
                    Term.aconv redex first andalso
                    Term.aconv residue second
                | _ => false) andalso
             (case substitution of
                  [{redex, residue}] =>
                    Term.aconv redex first andalso
                    Term.aconv residue second
                | _ => false) andalso
             Term.aconv (clasetMeta.norm store first) second andalso
             Term.aconv (clasetMeta.norm store second) second
           end
         val (ordinary_a, ordinary0) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val (ordinary_b, ordinary1) =
           clasetMeta.new_meta {allow = [], ty = bool_ty} ordinary0
         val ordinary2 =
           the_store
             (clasetMeta.bind (ordinary_a, ordinary_b) ordinary1)
         val ordinary_rejected =
           clasetMeta.bind (ordinary_b, ordinary_a) ordinary2
       in
         not (Option.isSome ordinary_rejected) andalso
         invariant ordinary2 ordinary_a ordinary_b
       end)

val _ =
  test
    ("normalization still reduces and instantiates without term bindings",
     fn () =>
       let
         val (tymeta, store) = clasetMeta.new_tymeta clasetMeta.empty
         val typed = Term.mk_var ("unbound_term", tymeta)
         val store' = the_store (clasetMeta.bind_ty (tymeta, bool_ty) store)
         val x = Term.mk_var ("unbound_term", bool_ty)
         val f = Term.mk_var ("eta_f", bool_ty --> bool_ty)
         val eta = Term.mk_abs (x, Term.mk_comb (f, x))
       in
         Term.aconv (clasetMeta.instantiate store' typed) x andalso
         Term.aconv (clasetMeta.norm store' typed) x andalso
         Term.aconv (clasetMeta.norm clasetMeta.empty eta) f
       end)

val _ =
  test
    ("term expansion instantiates dependency types capture-safely",
     fn () =>
       let
         val (tymeta, store0) =
           clasetMeta.new_tymeta clasetMeta.empty
         val parameter = Term.mk_var ("typed_capture_x", Type.ind)
         val bound = Term.mk_var ("typed_capture_x", tymeta)
         val relation =
           Term.mk_var
             ("typed_capture_R", tymeta --> tymeta --> bool_ty)
         val (dependency, store1) =
           clasetMeta.new_meta
             {allow = [parameter], ty = tymeta} store0
         val (outer, store2) =
           clasetMeta.new_meta
             {allow = [parameter], ty = bool_ty} store1
         val unresolved =
           boolSyntax.mk_forall
             (bound,
              Term.list_mk_comb (relation, [dependency, bound]))
         val store3 =
           the_store (clasetMeta.bind (outer, unresolved) store2)
         val store4 =
           the_store
             (clasetMeta.bind_ty (tymeta, Type.ind) store3)
         val store5 =
           the_store
             (clasetMeta.bind (dependency, parameter) store4)
         val typed_unresolved =
           Term.inst [{redex = tymeta, residue = Type.ind}] unresolved
         val typed_dependency =
           Term.inst [{redex = tymeta, residue = Type.ind}] dependency
         val expected =
           Term.subst
             [{redex = typed_dependency, residue = parameter}]
             typed_unresolved
       in
         Term.aconv
           (clasetMeta.norm store5 outer) (beta_eta_term expected)
       end)

fun unify_with store mode rule_metas pair =
  clasetUnify.unify store {mode = mode, rule_metas = rule_metas} pair

val no_rule_metas = {terms = [], types = []}

fun bool_meta allow store =
  clasetMeta.new_meta {allow = allow, ty = bool_ty} store

fun bool_fun_meta allow store =
  clasetMeta.new_meta {allow = allow, ty = bool_ty --> bool_ty} store

val _ =
  test
    ("unifier handles typed first-order cases and occurs checks",
     fn () =>
       let
         val (m, store0) = bool_meta [] clasetMeta.empty
         val nested_left = boolSyntax.mk_conj (m, boolSyntax.T)
         val nested_right = boolSyntax.mk_conj (boolSyntax.F, boolSyntax.T)
         val bound = Term.mk_var ("bound", bool_ty)
         val lambda_left = Term.mk_abs (bound, m)
         val lambda_right = Term.mk_abs (bound, bound)
       in
         case unify_with store0 clasetUnify.Unify no_rule_metas
           (nested_left, nested_right)
         of
           NONE => false
         | SOME store1 =>
             Term.aconv (clasetMeta.norm store1 m) boolSyntax.F
             andalso
             not (Option.isSome
               (unify_with store0 clasetUnify.Unify no_rule_metas
                 (m, boolSyntax.mk_neg m)))
             andalso
             not (Option.isSome
               (unify_with store0 clasetUnify.Unify no_rule_metas
                 (fixed, boolSyntax.T)))
             andalso
             not (Option.isSome
               (unify_with store0 clasetUnify.Unify no_rule_metas
                 (lambda_left, lambda_right)))
       end)

val _ =
  test
    ("types-only unification is integrated and checks occurs",
     fn () =>
       let
         val (a, store0) = clasetMeta.new_tymeta clasetMeta.empty
         val (m, store1) =
           clasetMeta.new_meta {allow = [], ty = a} store0
       in
         case unify_with store1 clasetUnify.Unify no_rule_metas
           (m, boolSyntax.T)
         of
           NONE => false
         | SOME store2 =>
             Term.aconv (clasetMeta.norm store2 m) boolSyntax.T
             andalso
             Option.isSome
               (clasetUnify.unify_types store0
                 {mode = clasetUnify.Unify,
                  rule_metas = no_rule_metas}
                 (a, bool_ty))
             andalso
             not (Option.isSome
               (clasetUnify.unify_types store0
                 {mode = clasetUnify.Unify,
                  rule_metas = no_rule_metas}
                 (a, a --> bool_ty)))
       end)

val _ =
  test
    ("pattern unification abstracts distinct eigenvariables",
     fn () =>
       let
         val x = Term.genvar bool_ty
         val y = Term.genvar bool_ty
         val (m, store0) = bool_fun_meta [x, y] clasetMeta.empty
         val lhs = Term.mk_comb (m, x)
         val rhs = boolSyntax.mk_conj (x, y)
         val (n, store1) = bool_fun_meta [x] store0
         val symmetric = Term.mk_comb (n, x)
       in
         case unify_with store1 clasetUnify.Unify no_rule_metas
           (lhs, rhs)
         of
           NONE => false
         | SOME store2 =>
             Term.aconv (clasetMeta.norm store2 lhs) rhs
             andalso
             case unify_with store1 clasetUnify.Unify no_rule_metas
               (boolSyntax.mk_neg x, symmetric)
             of
               NONE => false
             | SOME store3 =>
                 Term.aconv
                   (clasetMeta.norm store3 symmetric)
                   (boolSyntax.mk_neg x)
       end)

val _ =
  test
    ("pattern bindings enforce allow sets and distinct spines",
     fn () =>
       let
         val x = Term.genvar bool_ty
         val y = Term.genvar bool_ty
         val (_, store0) = bool_meta [y] clasetMeta.empty
         val (blocked, store1) = bool_fun_meta [x] store0
         val repeated_ty = bool_ty --> bool_ty --> bool_ty
         val (repeated, store2) =
           clasetMeta.new_meta {allow = [x], ty = repeated_ty} store1
         val repeated_app =
           Term.list_mk_comb (repeated, [x, x])
       in
         not (Option.isSome
           (unify_with store1 clasetUnify.Unify no_rule_metas
             (Term.mk_comb (blocked, x), y)))
         andalso
         not (Option.isSome
           (unify_with store2 clasetUnify.Unify no_rule_metas
             (repeated_app, x)))
       end)

val _ =
  test
    ("patterns handle explicit scope, multiple arguments and fallback",
     fn () =>
       let
         val x = Term.mk_var ("scope_x", bool_ty)
         val y = Term.mk_var ("scope_y", bool_ty)
         val (constant, store0) = bool_fun_meta [] clasetMeta.empty
         val store1 =
           the_store (clasetMeta.register_eigen x store0)
         val constant_app = Term.mk_comb (constant, x)
         val binary_ty = bool_ty --> bool_ty --> bool_ty
         val (binary, store2) =
           clasetMeta.new_meta
             {allow = [x, y], ty = binary_ty} store1
         val binary_app = Term.list_mk_comb (binary, [x, y])
         val binary_rhs = boolSyntax.mk_conj (y, x)
         val (argument, store3) = bool_meta [x] store2
         val fallback_rhs = Term.mk_comb (constant, argument)
       in
         case unify_with store3 clasetUnify.Unify no_rule_metas
           (constant_app, boolSyntax.mk_neg x)
         of
           NONE => false
         | SOME constant_store =>
             Term.aconv
               (clasetMeta.norm constant_store constant_app)
               (boolSyntax.mk_neg x)
             andalso
             case unify_with store3 clasetUnify.Unify no_rule_metas
               (binary_app, binary_rhs)
             of
               NONE => false
             | SOME binary_store =>
                 Term.aconv
                   (clasetMeta.norm binary_store binary_app)
                   binary_rhs
                 andalso
                 case unify_with store3 clasetUnify.Unify no_rule_metas
                   (constant_app, fallback_rhs)
                 of
                   NONE => false
                 | SOME fallback_store =>
                     Term.aconv
                       (clasetMeta.norm fallback_store argument) x
       end)

val _ =
  test
    ("first-order approximation decomposes only equal arities",
     fn () =>
       let
         val x = Term.mk_var ("approx_x", bool_ty)
         val y = Term.mk_var ("approx_y", bool_ty)
         val not_head = #1 (strip_comb (boolSyntax.mk_neg x))
         val and_head =
           #1 (strip_comb (boolSyntax.mk_conj (x, y)))
         val (m, store0) = bool_fun_meta [] clasetMeta.empty
         val equal_left = Term.mk_comb (m, x)
         val equal_right = Term.mk_comb (not_head, x)
         val unequal_right =
           Term.list_mk_comb (and_head, [x, y])
       in
         case unify_with store0 clasetUnify.Unify no_rule_metas
           (equal_left, equal_right)
         of
           NONE => false
         | SOME store1 =>
             Term.aconv (clasetMeta.norm store1 m) not_head
             andalso
             not (Option.isSome
               (unify_with store0 clasetUnify.Unify no_rule_metas
                 (equal_left, unequal_right)))
             andalso
             not (Option.isSome
               (unify_with store0 clasetUnify.Unify no_rule_metas
                 (equal_left, Term.mk_comb (not_head, y))))
       end)

val _ =
  test
    ("unification compares modulo beta eta normalization",
     fn () =>
       let
         val x = Term.mk_var ("eta_x", bool_ty)
         val f = Term.mk_var ("eta_f", bool_ty --> bool_ty)
         val eta = Term.mk_abs (x, Term.mk_comb (f, x))
         val identity = Term.mk_abs (x, x)
         val beta = Term.mk_comb (identity, boolSyntax.T)
         val (m, store0) = bool_fun_meta [] clasetMeta.empty
         val non_eta = Term.mk_abs (x, Term.mk_comb (f, boolSyntax.T))
       in
         Option.isSome
           (unify_with clasetMeta.empty clasetUnify.Unify
             no_rule_metas (eta, f))
         andalso
         Option.isSome
           (unify_with clasetMeta.empty clasetUnify.Unify
             no_rule_metas (beta, boolSyntax.T))
         andalso
         not (Option.isSome
           (unify_with clasetMeta.empty clasetUnify.Unify
             no_rule_metas (non_eta, f)))
         andalso
         case unify_with store0 clasetUnify.Unify no_rule_metas
           (m, eta)
         of
           NONE => false
         | SOME store1 => Term.aconv (clasetMeta.norm store1 m) f
       end)

val _ =
  test
    ("unification renormalizes a sibling after a function binding",
     fn () =>
       let
         val (m, store) = bool_fun_meta [] clasetMeta.empty
         val x = Term.mk_var ("sibling_x", bool_ty)
         val identity = Term.mk_abs (x, x)
         val left =
           boolSyntax.mk_conj
             (boolSyntax.mk_eq (m, m), Term.mk_comb (m, boolSyntax.T))
         val right =
           boolSyntax.mk_conj
             (boolSyntax.mk_eq (identity, identity), boolSyntax.T)
       in
         case unify_with store clasetUnify.Unify no_rule_metas (left, right) of
             SOME final => Term.aconv (clasetMeta.norm final m) identity
           | NONE => false
       end)

val _ =
  test
    ("match mode protects old term and type metavariables",
     fn () =>
       let
         val (old, store0) = bool_meta [] clasetMeta.empty
         val (rule, store1) = bool_meta [] store0
         val (old_head, store2) = bool_fun_meta [] store1
         val (rule_arg, store3) = bool_meta [] store2
         val (old_ty, store4) = clasetMeta.new_tymeta store3
         val (rule_ty, store5) = clasetMeta.new_tymeta store4
         val match_metas =
           {terms = [rule, rule_arg], types = [rule_ty]}
       in
         not (Option.isSome
           (unify_with store5 clasetUnify.Match match_metas
             (old, boolSyntax.T)))
         andalso
         Option.isSome
           (unify_with store5 clasetUnify.Match match_metas
             (rule, old))
         andalso
         Option.isSome
           (unify_with store5 clasetUnify.Match match_metas
             (Term.mk_comb (old_head, rule_arg),
              Term.mk_comb (old_head, boolSyntax.T)))
         andalso
         not (Option.isSome
           (unify_with store5 clasetUnify.Match match_metas
             (Term.mk_comb (old_head, boolSyntax.T),
              boolSyntax.mk_neg boolSyntax.T)))
         andalso
         not (Option.isSome
           (clasetUnify.unify_types store5
             {mode = clasetUnify.Match, rule_metas = match_metas}
             (old_ty, bool_ty)))
         andalso
         Option.isSome
           (clasetUnify.unify_types store5
             {mode = clasetUnify.Match, rule_metas = match_metas}
             (rule_ty, bool_ty))
       end)

(* Keep every production branch represented by a table-driven fixture. *)
val _ =
  test
    ("ordinary and timed unifiers have table-driven branch parity",
     fn () =>
       let
         val unify_config =
           {mode = clasetUnify.Unify, rule_metas = no_rule_metas}

         fun type_meta_terms () =
           let
             val (a, store0) = clasetMeta.new_tymeta clasetMeta.empty
             val (m, store1) =
               clasetMeta.new_meta {allow = [], ty = a --> bool_ty}
                 store0
             val (n, store2) =
               clasetMeta.new_meta
                 {allow = [], ty = Type.ind --> bool_ty} store1
           in
             (store2, unify_config, (m, n))
           end

         fun type_meta_right () =
           let
             val (a, store0) = clasetMeta.new_tymeta clasetMeta.empty
             val (m, store1) =
               clasetMeta.new_meta {allow = [], ty = a} store0
             val rigid = Term.mk_var ("parity_type_right", bool_ty)
           in
             (store1, unify_config, (rigid, m))
           end

         fun type_occurs () =
           let
             val (a, store0) = clasetMeta.new_tymeta clasetMeta.empty
             val left = Term.mk_var ("parity_type_occurs_left", a)
             val right =
               Term.mk_var ("parity_type_occurs_right", a --> bool_ty)
           in
             (store0, unify_config, (left, right))
           end

         fun rigid_type_constructor_mismatch () =
           (clasetMeta.empty, unify_config,
            (boolSyntax.T,
             Term.mk_var ("parity_rigid_type_ind", Type.ind)))

         fun match_term rule_on_left () =
           let
             val (old, store0) = bool_meta [] clasetMeta.empty
             val (rule, store1) = bool_meta [] store0
             val metas = {terms = [rule], types = []}
             val pair =
               if rule_on_left then (rule, old) else (old, boolSyntax.T)
           in
             (store1,
              {mode = clasetUnify.Match, rule_metas = metas}, pair)
           end

         fun match_type include_type () =
           let
             val (a, store0) = clasetMeta.new_tymeta clasetMeta.empty
             val (m, store1) =
               clasetMeta.new_meta {allow = [], ty = a} store0
             val metas =
               {terms = [m], types = if include_type then [a] else []}
           in
             (store1, {mode = clasetUnify.Match, rule_metas = metas},
              (m, boolSyntax.T))
           end

         fun pattern reverse () =
           let
             val x = Term.genvar bool_ty
             val (m, store0) = bool_fun_meta [x] clasetMeta.empty
             val application = Term.mk_comb (m, x)
             val target = boolSyntax.mk_neg x
           in
             (store0, unify_config,
              if reverse then (target, application)
              else (application, target))
           end

         fun pattern_fallback reverse () =
           let
             val x = Term.mk_var ("parity_fallback_x", bool_ty)
             val (head, store0) = bool_fun_meta [] clasetMeta.empty
             val store1 = the_store (clasetMeta.register_eigen x store0)
             val (argument, store2) = bool_meta [x] store1
             val pattern = Term.mk_comb (head, x)
             val blocked = Term.mk_comb (head, argument)
           in
             (store2, unify_config,
              if reverse then (blocked, pattern) else (pattern, blocked))
           end

         fun lambda equal () =
           let
             val x = Term.mk_var ("parity_lambda_x", bool_ty)
             val y = Term.mk_var ("parity_lambda_y", bool_ty)
             val (m, store) = bool_meta [] clasetMeta.empty
             val left = Term.mk_abs (x, if equal then m else boolSyntax.T)
             val right = Term.mk_abs (y, if equal then boolSyntax.T
                                                   else boolSyntax.F)
           in
             (store, unify_config, (left, right))
           end

         fun approximation same_arity () =
           let
             val x = Term.mk_var ("parity_approx_x", bool_ty)
             val y = Term.mk_var ("parity_approx_y", bool_ty)
             val (m, store0) = bool_fun_meta [] clasetMeta.empty
             val left = Term.mk_comb (m, x)
             val right =
               if same_arity then boolSyntax.mk_neg x
               else boolSyntax.mk_conj (x, y)
           in
             (store0, unify_config, (left, right))
           end

         fun match_approximation () =
           let
             val x = Term.mk_var ("parity_match_approx_x", bool_ty)
             val (head, store0) = bool_fun_meta [] clasetMeta.empty
             val (argument, store1) = bool_meta [] store0
             val metas = {terms = [argument], types = []}
           in
             (store1,
              {mode = clasetUnify.Match, rule_metas = metas},
              (Term.mk_comb (head, argument),
               Term.mk_comb (head, boolSyntax.T)))
           end

         fun match_unequal_head_approximation () =
           let
             val x = Term.mk_var ("parity_match_unequal_x", bool_ty)
             val (head, store0) = bool_fun_meta [] clasetMeta.empty
             val (argument, store1) = bool_meta [] store0
             val metas = {terms = [argument], types = []}
           in
             (store1,
              {mode = clasetUnify.Match, rule_metas = metas},
              (Term.mk_comb (head, argument), boolSyntax.mk_neg x))
           end

         fun occurs () =
           let
             val (m, store0) = bool_meta [] clasetMeta.empty
           in
             (store0, unify_config, (m, boolSyntax.mk_neg m))
           end

         fun allow_failure () =
           let
             val x = Term.mk_var ("parity_allow_x", bool_ty)
             val (m, store0) = bool_meta [] clasetMeta.empty
             val store1 = the_store (clasetMeta.register_eigen x store0)
           in
             (store1, unify_config, (m, x))
           end

         fun normalized_store () =
           let
             val x = Term.mk_var ("parity_normalized_x", bool_ty)
             val identity = Term.mk_abs (x, x)
             val (m, store0) = bool_fun_meta [] clasetMeta.empty
             val store1 = the_store (clasetMeta.bind (m, identity) store0)
           in
             (store1, unify_config,
              (Term.mk_comb (m, boolSyntax.T), boolSyntax.T))
           end

         fun beta_eta () =
           let
             val x = Term.mk_var ("parity_eta_x", bool_ty)
             val f = Term.mk_var ("parity_eta_f", bool_ty --> bool_ty)
           in
             (clasetMeta.empty, unify_config,
              (Term.mk_abs (x, Term.mk_comb (f, x)), f))
           end

         fun rigid_constants () =
           (clasetMeta.empty, unify_config,
            (boolSyntax.T, boolSyntax.F))

         fun rigid_variables () =
           (clasetMeta.empty, unify_config,
            (Term.mk_var ("parity_rigid_left", bool_ty),
             Term.mk_var ("parity_rigid_right", bool_ty)))

         fun rigid_right_variable () =
           (clasetMeta.empty, unify_config,
            (boolSyntax.T,
             Term.mk_var ("parity_structural_right", bool_ty)))

         fun structural_wildcard_mismatch () =
           let
             val x = Term.mk_var ("parity_wildcard_x", bool_ty)
             val not_head = #1 (strip_comb (boolSyntax.mk_neg x))
           in
             (clasetMeta.empty, unify_config,
              (Term.mk_abs (x, boolSyntax.T), not_head))
           end

         fun combination_decomposition () =
           let
             val (m, store0) = bool_meta [] clasetMeta.empty
           in
             (store0, unify_config,
              (boolSyntax.mk_conj (m, boolSyntax.T),
               boolSyntax.mk_conj (boolSyntax.F, boolSyntax.T)))
           end

         fun succeeds (_, _, (left, right), SOME result) =
               Term.aconv (clasetMeta.norm result left)
                 (clasetMeta.norm result right)
           | succeeds _ = false

         fun fails (_, _, _, NONE) = true
           | fails _ = false

         (* A failed pattern binding falls through to equal-head
            approximation.  Its distinguishing store leaves [head]
            unbound and binds [argument] to the eigenvariable [x]. *)
         fun fallback_succeeds reverse
               (_, _, (left, right), SOME result) =
               let
                 val (head, left_args) = strip_comb left
                 val (_, right_args) = strip_comb right
                 val x = hd (if reverse then right_args else left_args)
                 val argument =
                   hd (if reverse then left_args else right_args)
               in
                 Term.aconv (clasetMeta.norm result head) head andalso
                 Term.aconv (clasetMeta.norm result argument) x andalso
                 Term.aconv (clasetMeta.norm result left)
                   (clasetMeta.norm result right)
               end
           | fallback_succeeds _ _ = false

         datatype parity_branch =
             NoNamedBranch
           | RigidTypeMismatch
           | ProtectedUnequalHead
           | RightPatternFallback
           | LambdaDescent
           | StructuralWildcard

         (* The explicit term shapes in the failure rows select the named
            branch before returning NONE; successful rows additionally pin
            the complete unifying substitution through [succeeds]. *)
         val fixtures =
           [("type-constructor recursion and left type binding",
             type_meta_terms, succeeds, [84, 24, 5, 109, 2, 35],
             NoNamedBranch),
            ("right type-meta binding", type_meta_right, succeeds,
             [29, 13, 2, 39, 2, 34], NoNamedBranch),
            ("type occurs-check failure", type_occurs, fails,
             [4, 6, 1, 13, 0, 2], NoNamedBranch),
            ("rigid type-constructor mismatch",
             rigid_type_constructor_mismatch, fails, [2, 0, 2, 3, 0, 0],
             RigidTypeMismatch),
            ("Match rule-term binding", match_term true, succeeds,
             [40, 17, 2, 55, 1, 33], NoNamedBranch),
            ("Match protected left variable", match_term false, fails,
             [12, 2, 2, 14, 0, 10], NoNamedBranch),
            ("Match rule-type and term binding", match_type true, succeeds,
             [29, 12, 2, 33, 2, 34], NoNamedBranch),
            ("Match protected type-variable failure",
             match_type false, fails, [1, 1, 1, 3, 0, 0], NoNamedBranch),
            ("left-pattern binding", pattern false, succeeds,
             [48, 7, 1, 38, 1, 46], NoNamedBranch),
            ("right-pattern binding", pattern true, succeeds,
             [48, 7, 1, 39, 1, 46], NoNamedBranch),
            ("left-pattern binding-failure fallback",
             pattern_fallback false, fallback_succeeds false,
             [139, 31, 6, 156, 1, 98], NoNamedBranch),
            ("right-pattern binding-failure fallback",
             pattern_fallback true, fallback_succeeds true,
             [139, 31, 6, 156, 1, 98], RightPatternFallback),
            ("structural lambda descent and binding", lambda true, succeeds,
             [48, 10, 4, 44, 2, 44], LambdaDescent),
            ("structural lambda descent failure", lambda false, fails,
             [28, 2, 4, 22, 1, 22], LambdaDescent),
            ("flexible-head approximation", approximation true, succeeds,
             [72, 9, 6, 69, 1, 58], NoNamedBranch),
            ("approximation arity mismatch", approximation false, fails,
             [19, 3, 2, 21, 0, 19], NoNamedBranch),
            ("protected applied-meta equal-head fallback",
             match_approximation, succeeds, [54, 12, 5, 57, 1, 48],
             NoNamedBranch),
            ("protected applied-meta unequal-head fallback",
             match_unequal_head_approximation, fails,
             [20, 4, 2, 24, 0, 16], ProtectedUnequalHead),
            ("term occurs-check failure", occurs, fails,
             [35, 11, 2, 43, 0, 34], NoNamedBranch),
            ("term allow-set failure", allow_failure, fails,
             [31, 7, 2, 32, 1, 38], NoNamedBranch),
            ("stored normalization and beta equality",
             normalized_store, succeeds, [25, 4, 1, 15, 0, 21],
             NoNamedBranch),
            ("eta-normalized equality", beta_eta, succeeds,
             [17, 0, 1, 11, 0, 14], NoNamedBranch),
            ("structural rigid-constant mismatch", rigid_constants, fails,
             [10, 0, 2, 8, 0, 10], NoNamedBranch),
            ("structural left rigid-variable failure",
             rigid_variables, fails, [10, 0, 2, 11, 0, 10],
             NoNamedBranch),
            ("structural right rigid-variable failure",
             rigid_right_variable, fails, [10, 0, 2, 10, 0, 10],
             NoNamedBranch),
            ("structural combination decomposition",
             combination_decomposition, succeeds, [90, 10, 8, 73, 1, 90],
             NoNamedBranch),
            ("structural wildcard mismatch",
             structural_wildcard_mismatch, fails, [16, 0, 2, 12, 0, 11],
             StructuralWildcard)]

         fun agrees (_, make, expected, _, _) =
           let
             val (store, config, pair) = make ()
             val result = clasetUnify.unify store config pair
           in
             expected (store, config, pair, result)
           end
       in
         List.foldl
           (fn (fixture, all) => agrees fixture andalso all) true fixtures
       end)

fun apply_substitution (tys, tms) tm =
  Term.subst tms (Term.inst tys tm)

fun oracle_agrees store rigid_types rigid_terms pair =
  let
    open optmonad
    infix >>
    val ours =
      unify_with store clasetUnify.Unify no_rule_metas pair
    val oracle =
      FullUnify.Env.fromEmpty
        (FullUnify.unify rigid_types rigid_terms pair >>
         FullUnify.collapse)
  in
    case (ours, oracle) of
      (NONE, NONE) => true
    | (SOME ours_store, SOME full_subst) =>
        Term.aconv
          (clasetMeta.norm ours_store (#1 pair))
          (apply_substitution full_subst (#1 pair))
        andalso
        Term.aconv
          (clasetMeta.norm ours_store (#2 pair))
          (apply_substitution full_subst (#2 pair))
    | _ => false
  end

val _ =
  test
    ("first-order results agree with FullUnify oracle",
     fn () =>
       let
         val x = Term.mk_var ("oracle_x", bool_ty)
         val y = Term.mk_var ("oracle_y", bool_ty)
         val (m, store0) = bool_meta [] clasetMeta.empty
         val (f, store1) = bool_fun_meta [] store0
         val (a, store2) = clasetMeta.new_tymeta store1
         val (typed, store3) =
           clasetMeta.new_meta {allow = [], ty = a} store2
         val (typed_fun, store4) =
           clasetMeta.new_meta {allow = [], ty = a --> a} store3
         val (n, store5) = bool_meta [] store4
         val bound = Term.mk_var ("oracle_bound", bool_ty)
         val identity = Term.mk_abs (bound, bound)
         val rigid_ty = Type.mk_vartype "'oracle_rigid"
         val rigid_typed = Term.mk_var ("rigid_typed", rigid_ty)
         val ind_typed = Term.mk_var ("ind_typed", Type.ind)
         val cases =
           [(store5, [], [], (m, boolSyntax.T)),
            (store5, [], [x], (m, x)),
            (store5, [], [x],
             (Term.mk_comb (f, x), boolSyntax.mk_neg x)),
            (store5, [], [], (m, boolSyntax.mk_neg m)),
            (store5, [], [x, y], (x, y)),
            (store5, [], [], (typed, boolSyntax.T)),
            (store5, [], [], (typed_fun, identity)),
            (store5, [], [], (m, n)),
            (store5, [rigid_ty], [rigid_typed],
             (rigid_typed, boolSyntax.T)),
            (store5, [], [ind_typed, fixed], (ind_typed, fixed)),
            (store5, [], [], (identity, identity))]
       in
         List.all
           (fn (store, rigid_types, rigid_terms, pair) =>
             oracle_agrees store rigid_types rigid_terms pair)
           cases
       end)

val _ =
  test
    ("unifier returns one reproducible deterministic solution",
     fn () =>
       let
         val x = Term.mk_var ("det_x", bool_ty)
         val (m, store0) = bool_fun_meta [] clasetMeta.empty
         val pair = (Term.mk_comb (m, x), boolSyntax.mk_neg x)
       in
         case
           (unify_with store0 clasetUnify.Unify no_rule_metas pair,
            unify_with store0 clasetUnify.Unify no_rule_metas pair)
         of
           (SOME left, SOME right) =>
             let
               val (left_tys, left_tms) = clasetMeta.collapse left
               val (right_tys, right_tms) = clasetMeta.collapse right
             in
               type_subst_eq left_tys right_tys andalso
               term_subst_eq left_tms right_tms
             end
         | _ => false
       end)

val goal_p = Term.mk_var ("goal_p", bool_ty)
val goal_q = Term.mk_var ("goal_q", bool_ty)
val goal_r = Term.mk_var ("goal_r", bool_ty)

fun aconv_list left right =
  ListPair.allEq (fn (tm1, tm2) => Term.aconv tm1 tm2) (left, right)

val _ =
  test
    ("engine intake preserves ordered assumptions",
     fn () =>
       let
         val node = clasetGoal.from_goal ([goal_p, goal_q], goal_r)
         val {params, asl, w} =
           the_singleton (clasetGoal.goals node)
       in
         List.null params andalso aconv_list asl [goal_p, goal_q]
         andalso Term.aconv w goal_r
         andalso clasetGoal.replay_length node = 0
         andalso clasetGoal.level node = 0
       end)

val _ =
  test
    ("new assumptions are consed at the front",
     fn () =>
       let
         val parent = {params = [], asl = [goal_r], w = goal_r}
         val {asl, ...} =
           clasetGoal.cons_assumptions [goal_p, goal_q] parent
       in
         aconv_list asl [goal_q, goal_p, goal_r]
       end)

val _ =
  test
    ("premise children strip only the outer prefix",
     fn () =>
       let
         val x = Term.mk_var ("x", bool_ty)
         val pred_p = Term.mk_var ("pred_p", bool_ty --> bool_ty)
         val pred_q = Term.mk_var ("pred_q", bool_ty --> bool_ty)
         val pred_r = Term.mk_var ("pred_r", bool_ty --> bool_ty)
         fun app f arg = Term.mk_comb (f, arg)
         val quantified =
           boolSyntax.mk_forall
             (x, boolSyntax.mk_imp
               (app pred_p x,
                boolSyntax.mk_imp (app pred_q x, app pred_r x)))
         val nested =
           boolSyntax.mk_imp
             (goal_p,
              boolSyntax.mk_forall
                (x, boolSyntax.mk_imp (goal_q, goal_r)))
         val parent = {params = [x], asl = [goal_r], w = goal_r}
         val sibling_fixed = Term.variant [x] x
         val sibling =
           {params = [], asl = [], w = sibling_fixed}
         val store0 = the_store
           (clasetMeta.register_eigen x clasetMeta.empty)
         val node0 = clasetGoal.create
           {goals = [parent, sibling], store = store0, level = 0}
         val (children, store1) =
           clasetGoal.children node0
             {pos = 1, premises = [quantified, nested],
              consumed = NONE}
         val first = List.nth (children, 0)
         val second = List.nth (children, 1)
         val fresh = List.nth (#params first, 1)
         val (fresh_name, _) = Term.dest_var fresh
         val node1 = clasetGoal.set_store store1 node0
         val (again_children, store2) =
           clasetGoal.children node1
             {pos = 1, premises = [quantified], consumed = NONE}
         val again = the_singleton again_children
         val fresh_again = List.nth (#params again, 1)
         val (m, store3) =
           clasetMeta.new_meta {allow = #params first, ty = bool_ty} store2
       in
         length (#params first) = 2
         andalso String.isPrefix "x" fresh_name
         andalso not (Term.aconv fresh x)
         andalso not (Term.aconv fresh sibling_fixed)
         andalso not (clasetMeta.is_eigen store1 sibling_fixed)
         andalso
         aconv_list (#asl first)
           [app pred_q fresh, app pred_p fresh, goal_r]
         andalso Term.aconv (#w first) (app pred_r fresh)
         andalso aconv_list (#params second) [x]
         andalso aconv_list (#asl second) [goal_p, goal_r]
         andalso boolSyntax.is_forall (#w second)
         andalso not (Term.aconv fresh fresh_again)
         andalso
         Option.isSome (clasetMeta.bind (m, fresh) store3)
       end)

val _ =
  test
    ("eigenvariable names avoid removed goals even at a different type",
     fn () =>
       let
         val historical = Term.mk_var ("old_goal_variable", bool_ty)
         val candidate =
           Term.mk_var ("old_goal_variable", bool_ty --> bool_ty)
         val node0 = clasetGoal.from_goal ([], goal_p)
         val store = clasetGoal.store node0
         val node1 = clasetGoal.replace_goal node0
           {pos = 1, children = [{params = [], asl = [], w = historical}],
            store = store}
         val node2 = clasetGoal.replace_goal node1
           {pos = 1, children = [{params = [], asl = [], w = goal_p}],
            store = store}
         val node3 = clasetGoal.set_store store node2
         val (fresh, _) = clasetGoal.fresh_eigen node3 candidate
       in
         Term.aconv fresh (Term.variant [historical] candidate)
         andalso not (Term.aconv fresh candidate)
       end)

val _ =
  test
    ("elim alternatives delete one positional assumption from every child",
     fn () =>
       let
         val parent =
           {params = [], asl = [goal_p, goal_q, goal_p], w = goal_r}
         val node = clasetGoal.create
           {goals = [parent], store = clasetMeta.empty, level = 0}
         val alternatives =
           clasetGoal.elim_children node
             {pos = 1, premises = [goal_q, goal_r]}
         fun child_asls alternative = map #asl (#children alternative)
       in
         map #assumption alternatives = [1, 2, 3]
         andalso aconv_list (map #major alternatives)
           [goal_p, goal_q, goal_p]
         andalso
         List.all
           (fn asl => aconv_list asl [goal_q, goal_p])
           (child_asls (List.nth (alternatives, 0)))
         andalso
         List.all
           (fn asl => aconv_list asl [goal_p, goal_p])
           (child_asls (List.nth (alternatives, 1)))
         andalso
         List.all
           (fn asl => aconv_list asl [goal_p, goal_q])
           (child_asls (List.nth (alternatives, 2)))
       end)

val _ =
  test
    ("exact prefixes stay static while ordinary children stay eager",
     fn () =>
       let
         val x = Term.mk_var ("static_prefix_x", Type.ind)
         val c =
           Term.mk_var
             ("static_prefix_C", Type.ind --> bool_ty)
         val g =
           Term.mk_var
             ("static_prefix_G", Type.ind --> bool_ty)
         val exposed =
           boolSyntax.mk_forall
             (x,
              boolSyntax.mk_imp
                (Term.mk_comb (c, x), Term.mk_comb (g, x)))
         val (meta, store0) =
           clasetMeta.new_meta
             {allow = [], ty = bool_ty} clasetMeta.empty
         val store1 = the_store (clasetMeta.bind (meta, exposed) store0)
         val node =
           clasetGoal.create
             {goals = [{params = [], asl = [], w = goal_p}],
              store = store1, level = 0}
         val descriptor = clasetReplay.exact_prefix_descriptor meta
         val (exact, _, rebuilds) =
           clasetGoal.exact_blast_children node
             {pos = 1, premises = [meta], prefixes = [descriptor],
              consumed = NONE}
         val (ordinary, _) =
           clasetGoal.children node
             {pos = 1, premises = [meta], consumed = NONE}
         val exact_child = the_singleton exact
         val ordinary_child = the_singleton ordinary
         val nested = boolSyntax.mk_imp (goal_q, exposed)
         val nested_descriptor : clasetReplay.exact_prefix_descriptor =
           clasetReplay.exact_prefix_descriptor nested
         val nested_split =
           clasetReplay.split_exact_prefix
             {descriptor = nested_descriptor, premise = nested,
              fresh = []}
         val malformed =
           total
             (fn () =>
               clasetReplay.split_exact_prefix
                 {descriptor = {foralls = 1, implications = 0},
                  premise = goal_p,
                  fresh = [Term.mk_var ("bad_prefix", bool_ty)]}) ()
       in
         length rebuilds = 1 andalso
         List.null (#params exact_child) andalso
         List.null (#asl exact_child) andalso
         Term.aconv (#w exact_child) exposed andalso
         length (#params ordinary_child) = 1 andalso
         length (#asl ordinary_child) = 1 andalso
         #foralls nested_descriptor = 0 andalso
         #implications nested_descriptor = 1 andalso
         aconv_list (#assumptions nested_split) [goal_q] andalso
         Term.aconv (#residual nested_split) exposed andalso
         not (Option.isSome malformed) andalso
         let
           val fresh = the_singleton (#params ordinary_child)
         in
           Term.aconv (#w ordinary_child) (Term.mk_comb (g, fresh))
         end
       end)

val _ =
  test
    ("node constructors register every declared parameter",
     fn () =>
       let
         val eigen = Term.mk_var ("declared_param", bool_ty)
         val node = clasetGoal.create
           {goals =
              [{params = [eigen], asl = [], w = boolSyntax.T}],
            store = clasetMeta.empty, level = 0}
         val (m, store) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             (clasetGoal.store node)
       in
         clasetMeta.is_eigen store eigen
         andalso not (Option.isSome (clasetMeta.bind (m, eigen) store))
       end)

val _ =
  test
    ("engine size counts atoms and abstractions after substitution",
     fn () =>
       let
         val x = Term.mk_var ("size_x", bool_ty)
         val f = Term.mk_var ("size_f", bool_ty --> bool_ty)
         val lambda = Term.mk_abs (x, Term.mk_comb (f, x))
         val (m, store0) =
           clasetMeta.new_meta
             {allow = [], ty = bool_ty --> bool_ty} clasetMeta.empty
         val identity = Term.mk_abs (x, x)
         val store1 = the_store (clasetMeta.bind (m, identity) store0)
         val applied = Term.mk_comb (m, boolSyntax.T)
         val node = clasetGoal.create
           {goals = [{params = [], asl = [], w = applied}],
            store = store1, level = 0}
         val expected = clasetGoal.from_goal ([], boolSyntax.T)
       in
         clasetGoal.term_size goal_p = 1
         andalso clasetGoal.term_size (Term.mk_comb (f, x)) = 2
         andalso clasetGoal.term_size lambda = 3
         andalso clasetGoal.size node = 1
         andalso
           Term.aconv (snd (clasetGoal.render node 1)) boolSyntax.T
         andalso clasetGoal.equal (node, expected)
       end)

val _ =
  test
    ("sized renderings preserve goal and assumption positions",
     fn () =>
       let
         val (m, store) =
           clasetMeta.new_meta {allow = [], ty = bool_ty} clasetMeta.empty
         val bound = the_store (clasetMeta.bind (m, boolSyntax.T) store)
         val node = clasetGoal.create
           {goals =
              [{params = [], asl = [goal_q], w = goal_p},
               {params = [], asl = [goal_p, m, goal_q], w = m}],
            store = bound, level = 0}
         val expected = clasetGoal.create
           {goals =
              [{params = [], asl = [goal_q], w = goal_p},
               {params = [], asl = [goal_p, boolSyntax.T, goal_q],
                w = boolSyntax.T}],
            store = clasetMeta.empty, level = 0}
         fun same_goal ((asl, w), (asl', w')) =
           Lib.list_eq Term.aconv asl asl' andalso Term.aconv w w'
       in
         clasetGoal.size node = 6 andalso
         Term.aconv (clasetGoal.canonical_rendering node)
           (clasetGoal.canonical_rendering expected) andalso
         same_goal (clasetGoal.render node 1, clasetGoal.render expected 1)
         andalso
         same_goal (clasetGoal.render node 2, clasetGoal.render expected 2)
       end)

val _ =
  test
    ("node equality and ordering use canonical alpha rendering",
     fn () =>
       let
         val x = Term.mk_var ("alpha_x", bool_ty)
         val y = Term.mk_var ("alpha_y", bool_ty)
         val pfun = Term.mk_var ("alpha_p", bool_ty --> bool_ty)
         val qfun = Term.mk_var ("alpha_q", bool_ty --> bool_ty)
         fun singleton param body =
           clasetGoal.create
             {goals =
                [{params = [param], asl = [],
                  w = Term.mk_comb (body, param)}],
              store = clasetMeta.empty, level = 0}
         val left = singleton x pfun
         val alpha = singleton y pfun
         val other = singleton x qfun
         val assumed = clasetGoal.from_goal ([goal_p], goal_q)
         val implication = clasetGoal.from_goal
           ([], boolSyntax.mk_imp (goal_p, goal_q))
         val small = clasetGoal.from_goal ([], boolSyntax.T)
         val large = clasetGoal.from_goal
           ([], boolSyntax.mk_conj (boolSyntax.T, boolSyntax.T))
         val forward = clasetGoal.compare (left, other)
         val backward = clasetGoal.compare (other, left)
       in
         clasetGoal.equal (left, alpha)
         andalso clasetGoal.compare (left, alpha) = EQUAL
         andalso not (clasetGoal.equal (left, other))
         andalso forward <> EQUAL andalso backward <> EQUAL
         andalso forward <> backward
         andalso not (clasetGoal.equal (assumed, implication))
         andalso not (clasetGoal.equal (small, large))
         andalso clasetGoal.compare (small, large) = LESS
       end)

val _ =
  test
    ("unrender records eigenvariables introduced by a tactic",
     fn () =>
       let
         val x = Term.mk_var ("render_x", bool_ty)
         val predicate =
           Term.mk_var ("render_predicate", bool_ty --> bool_ty)
         val quantified = boolSyntax.mk_forall
           (x, Term.mk_comb (predicate, x))
         val node = clasetGoal.from_goal ([], quantified)
         val result = Tactic.GEN_TAC (clasetGoal.render node 1)
           (Context.snapshot())
       in
         case clasetGoal.unrender node 1 result of
           NONE => false
         | SOME node' =>
             let
               val child = the_singleton (clasetGoal.goals node')
               val param = the_singleton (#params child)
             in
               clasetMeta.is_eigen (clasetGoal.store node') param
               andalso Term.aconv (#w child)
                 (Term.mk_comb (predicate, param))
             end
       end)

fun first_step step cs goal =
  case seq.cases (step cs (clasetGoal.from_goal goal, 1)) of
      NONE => NONE
    | SOME (result, _) => SOME result

fun safe_step cs = clasetStep.safe_step_in (Context.snapshot ()) cs

fun rendered_goals node =
  let
    fun recurse pos [] = []
      | recurse pos (_ :: rest) =
          clasetGoal.render node pos :: recurse (pos + 1) rest
  in
    recurse 1 (clasetGoal.goals node)
  end

fun valid_step goal (record, node) =
  let
    val materialized =
      clasetGoal.render (clasetGoal.from_goal goal) 1
    val tactic =
      fn _ => fn _ =>
        (rendered_goals node, clasetStep.validation_of record)
    val _ = Tactical.VALID tactic materialized
  in
    true
  end
  handle HOL_ERR _ => false

val _ =
  test
    ("metavariable-free nodes render and lift tactic children",
     fn () =>
       let
         val node = clasetGoal.from_goal
           ([], boolSyntax.mk_imp (goal_p, goal_q))
         val rendered = clasetGoal.render node 1
         val result = Tactic.DISCH_TAC rendered (Context.snapshot())
       in
         List.null (#1 rendered)
         andalso Term.aconv (#2 rendered)
           (boolSyntax.mk_imp (goal_p, goal_q))
         andalso
         case clasetGoal.unrender node 1 result of
           NONE => false
         | SOME node' =>
             let
               val {params, asl, w} =
                 the_singleton (clasetGoal.goals node')
             in
               List.null params andalso aconv_list asl [goal_p]
               andalso Term.aconv w goal_q
               andalso clasetGoal.replay_length node' = 0
             end
       end)

val _ =
  test
    ("unrender checks markings for the current goal position and store",
     fn () =>
       let
         val (meta, store) =
           clasetMeta.new_meta {allow = [], ty = bool_ty} clasetMeta.empty
         fun premise w = {params = [], asl = [], w = boolSyntax.mk_imp (w, w)}
         val node =
           clasetGoal.create
             {goals = [premise meta, premise fixed], store = store, level = 0}
         fun check node pos expected replay_length =
           let
             val result =
               Tactical.VALID Tactic.DISCH_TAC (clasetGoal.render node pos)
           in
             case clasetGoal.unrender node pos result of
                 NONE => false
               | SOME next =>
                   let val {asl, w, ...} = clasetGoal.goal_at next pos
                   in
                     aconv_list asl [expected] andalso aconv w expected
                     andalso clasetGoal.replay_length next = replay_length
                   end
           end
       in
         check node 1 meta 1 andalso check node 2 fixed 0 andalso
         check (clasetGoal.set_store (the_store (clasetMeta.bind
           (meta, fixed) store)) node) 1 fixed 0
       end)

val _ =
  test
    ("safe-step cascade reaches each ordered slot with valid evidence",
     fn () =>
       let
         open clasetStep
         val implication = boolSyntax.mk_imp (goal_p, goal_q)
         val mp_goal = ([goal_p, implication], goal_r)
         val safe0_cs =
           clasetLib.add_sintros [("truth", boolTheory.TRUTH)]
             clasetLib.empty_cs
         val safep_cs =
           clasetLib.add_sintros
             [("and", boolTheory.AND_INTRO_THM)] clasetLib.empty_cs
         val subst_x = Term.mk_var ("subst_x", bool_ty)
         val subst_goal =
           ([boolSyntax.mk_eq (subst_x, goal_p)], subst_x)
         val cases =
           [(first_step safe_step clasetLib.empty_cs
               ([goal_p], goal_p),
             fn Assumption _ => true | _ => false),
            (first_step safe_step clasetLib.empty_cs mp_goal,
             fn ModusPonens _ => true | _ => false),
            (first_step safe_step safe0_cs ([], boolSyntax.T),
             fn RuleApplication _ => true | _ => false),
            (first_step safe_step clasetLib.empty_cs ([], implication),
             fn Disch => true | _ => false),
            (first_step safe_step clasetLib.empty_cs subst_goal,
             fn HypSubst => true | _ => false),
            (first_step safe_step safep_cs
               ([], boolSyntax.mk_conj (goal_p, goal_q)),
             fn RuleApplication _ => true | _ => false)]
         fun good (NONE, _) = false
           | good (SOME (record, node), expected) =
               expected (kind_of record) andalso
               valid_step
                 (case kind_of record of
                      Assumption _ => ([goal_p], goal_p)
                    | ModusPonens _ => mp_goal
                    | Disch => ([], implication)
                    | HypSubst => subst_goal
                    | RuleApplication _ =>
                        if List.null (clasetGoal.goals node) then
                          ([], boolSyntax.T)
                        else
                          ([], boolSyntax.mk_conj (goal_p, goal_q))
                    | _ => ([], goal_r))
                 (record, node)
       in
         List.all good cases
       end)

(* [rule_origin] recovers the declaration an applied theorem came from by
   comparing the theorem against the canonicalisation the claset stored for
   that declaration.  Probing with forms rebuilt by clasetRules.ext_info
   pins both halves at once: the stored forms have to be exactly what
   ext_info derives, or no probe would match and every case would take the
   fallback; and the reported variant has to follow the scan's priority --
   plain and swapped only for a non-duplicating application, then the two
   duplicated forms whatever the application was, then plain regardless --
   with an undeclared theorem its own origin. *)
val _ =
  test
    ("rule_origin classifies every stored rule form and falls back",
     fn () =>
       let
         open clasetStep
         val origin_p = Term.mk_var ("origin_p", bool_ty)
         val origin_q = Term.mk_var ("origin_q", bool_ty)
         val conjunction = boolSyntax.mk_conj (origin_p, origin_q)
         val intro_thm =
           DISCH origin_p (DISJ1 (ASSUME origin_p) origin_q)
         val dest_thm =
           DISCH conjunction (CONJUNCT1 (ASSUME conjunction))
         val unsafe_intro =
           {kind = clasetRules.Intro, safe = false, prio = NONE}
         val safe_intro =
           {kind = clasetRules.Intro, safe = true, prio = NONE}
         val safe_dest =
           {kind = clasetRules.Dest, safe = true, prio = NONE}
         fun declared spec named_th =
           let
             val cs = clasetLib.add_rule spec named_th clasetLib.empty_cs
             val (_, (_, original)) = the_singleton (clasetLib.rules_of cs)
           in
             (cs, original, clasetRules.ext_info spec original)
           end
         fun reports cs duplicated theorem (origin, expected) =
           let
             val (reported, variant) = rule_origin cs duplicated theorem
           in
             Term.aconv (concl reported) (concl origin) andalso
             variant = expected
           end
         val (unsafe_cs, unsafe_orig,
              {rl = (plain, swapped), dup_rl = (dup, dup_swapped)}) =
           declared unsafe_intro ("origin_unsafe", intro_thm)
         val (safe_cs, safe_orig, {rl = (safe_plain, _), dup_rl = _}) =
           declared safe_intro ("origin_safe", intro_thm)
         val (dest_cs, dest_orig, {rl = (dest_plain, _), dup_rl = _}) =
           declared safe_dest ("origin_dest", dest_thm)
         (* A claset the scan has to look past its first declaration in. *)
         val both_cs =
           clasetLib.add_rule safe_dest ("origin_dest", dest_thm)
             (clasetLib.add_rule unsafe_intro
                ("origin_unsafe", intro_thm) clasetLib.empty_cs)
       in
         reports unsafe_cs false plain (unsafe_orig, Plain) andalso
         reports unsafe_cs false (valOf swapped)
           (unsafe_orig, Swapped) andalso
         reports unsafe_cs false dup (unsafe_orig, Duplicate) andalso
         reports unsafe_cs true dup (unsafe_orig, Duplicate) andalso
         reports unsafe_cs true (valOf dup_swapped)
           (unsafe_orig, Duplicate) andalso
         (* The last resort: a duplicating application of the plain form of
            a rule whose duplicated form differs from it. *)
         reports unsafe_cs true plain (unsafe_orig, Plain) andalso
         (* A safe rule duplicates to itself, so a duplicating application
            of it reaches the duplicate test rather than the plain one. *)
         reports safe_cs false safe_plain (safe_orig, Plain) andalso
         reports safe_cs true safe_plain (safe_orig, Duplicate) andalso
         (* A destruction rule is applied in its made-elimination form,
            which is not the declared theorem. *)
         reports dest_cs false dest_plain (dest_orig, MakeElim) andalso
         reports both_cs false plain (unsafe_orig, Plain) andalso
         reports both_cs false dest_plain (dest_orig, MakeElim) andalso
         (* No declaration derived this theorem, so it is its own origin. *)
         reports unsafe_cs false boolTheory.TRUTH
           (boolTheory.TRUTH, Plain) andalso
         reports unsafe_cs true boolTheory.TRUTH
           (boolTheory.TRUTH, Duplicate)
       end)

val _ =
  test
    ("assumption closing uses shared beta-eta equality",
     fn () =>
       let
         val x = Term.mk_var ("close_x", bool_ty)
         val f = Term.mk_var ("close_f", bool_ty --> bool_ty)
         val h = Term.mk_var ("close_h", bool_ty --> bool_ty)
         val eta = Term.mk_abs (x, Term.mk_comb (f, x))
         val abstraction =
           Term.mk_abs (h, boolSyntax.mk_eq (h, f))
         val assumption = Term.mk_comb (abstraction, eta)
         val input = ([assumption], boolSyntax.mk_eq (f, f))
       in
         case first_step safe_step clasetLib.empty_cs input of
             NONE => false
           | SOME (record, node) =>
               (case clasetStep.kind_of record of
                    clasetStep.Assumption 1 =>
                      valid_step input (record, node)
                  | _ => false)
       end)

val _ =
  test
    ("clarify bimatch2 accepts one closing child and rejects branching",
     fn () =>
       let
         val cs =
           clasetLib.add_sintros
             [("and", boolTheory.AND_INTRO_THM)] clasetLib.empty_cs
         val closing_child = boolSyntax.mk_conj (goal_p, goal_q)
         val target = boolSyntax.mk_conj (closing_child, goal_r)
         val accepted = ([closing_child], target)
         val rejected = ([], target)
       in
         case first_step (clasetStep.clarify_step_in (Context.snapshot ()))
                cs accepted of
             NONE => false
           | SOME (record, node) =>
               (case clasetStep.kind_of record of
                    clasetStep.RuleApplication _ =>
                      length (clasetGoal.goals node) = 1 andalso
                      valid_step accepted (record, node) andalso
                      not (Option.isSome
                        (first_step
                          (clasetStep.clarify_step_in (Context.snapshot ()))
                          cs rejected))
                  | _ => false)
       end)

val _ =
  test
    ("match mode skips unfixed safe-rule premise variables",
     fn () =>
       let
         val x = Term.mk_var ("unfixed_x", bool_ty)
         val predicate =
           Term.mk_var ("unfixed_predicate", bool_ty --> bool_ty)
         val premise = Term.mk_comb (predicate, x)
         val rule = GEN x (DISCH premise boolTheory.TRUTH)
         val cs =
           clasetLib.add_sintros [("unfixed", rule)] clasetLib.empty_cs
         val old_trace = HOLFlags.current_trace "classical.trace"
         val notices = ref ([] : string list)
         fun record_notice message =
           notices := message :: !notices
         val _ = HOLFlags.set_trace "classical.trace" 1
         val result =
           Lib.with_flag
             (Feedback.MESG_outstream, record_notice)
             (fn () =>
               first_step safe_step cs ([], boolSyntax.T)) ()
         val _ = HOLFlags.set_trace "classical.trace" old_trace
       in
         not (Option.isSome result) andalso
         List.exists
           (String.isSubstring "unfixed premise variables") (!notices)
       end)

val _ =
  test
    ("safe wrappers surround the complete cascade",
     fn () =>
       let
         fun truth_before tac =
           NTactical.NORELSE
             (NTactical.LIFT (Tactic.ACCEPT_TAC boolTheory.TRUTH), tac)
         val cs =
           clasetLib.add_safe_wrapper ("truth", truth_before)
             clasetLib.empty_cs
         val goal = ([], boolSyntax.T)
       in
         case first_step safe_step cs goal of
             NONE => false
           | SOME (record, node) =>
               (case clasetStep.kind_of record of
                    clasetStep.Wrapper => valid_step goal (record, node)
                  | _ => false)
       end)

val _ =
  test
    ("safe eq-mp slot closes a matching contradiction",
     fn () =>
       let
         val proposition = boolSyntax.mk_conj (goal_p, goal_q)
         val goal =
           ([boolSyntax.mk_neg proposition, proposition], goal_r)
       in
         case first_step safe_step clasetLib.empty_cs goal of
             NONE => false
           | SOME (record, node) =>
               (case clasetStep.kind_of record of
                    clasetStep.Contradiction (1, 2) =>
                      clasetStep.consumed_of record = SOME 1 andalso
                      valid_step goal (record, node)
                  | _ => false)
       end)

val _ =
  test
    ("rule premise stripping keeps explicit negation opaque",
     fn () =>
       let
         val negative = boolSyntax.mk_neg goal_p
         val rule = DISCH negative (ASSUME negative)
         val cs =
           clasetLib.add_sintros [("negative", rule)]
             clasetLib.empty_cs
         val goal = ([], negative)
       in
         case first_step safe_step cs goal of
             NONE => false
           | SOME (record, node) =>
               let
                 val child = the_singleton (clasetGoal.goals node)
               in
                 List.null (#asl child) andalso
                 Term.aconv (#w child) negative andalso
                 valid_step goal (record, node)
               end
       end)

val _ =
  test
    ("elim lookup dedups tags but keeps positional alternatives",
     fn () =>
       let
         val disjunction = boolSyntax.mk_disj (goal_p, goal_q)
         val goal = ([disjunction, disjunction], goal_r)
         val cs =
           clasetLib.add_selims [("or", boolTheory.OR_ELIM_THM)]
             clasetLib.empty_cs
         val sequence =
           safe_step cs (clasetGoal.from_goal goal, 1)
         fun drain results remaining =
           case seq.cases remaining of
               NONE => List.rev results
             | SOME (result, rest) => drain (result :: results) rest
         val results = drain [] sequence
         val consumed = map (clasetStep.consumed_of o #1) results
       in
         consumed = [SOME 1, SOME 2] andalso
         List.all (valid_step goal) results
       end)

val _ =
  test
    ("rule validations normalize local theorem hypotheses",
     fn () =>
       let
         val x = Term.mk_var ("hyp_close_x", bool_ty)
         val f = Term.mk_var ("hyp_close_f", bool_ty --> bool_ty)
         val h = Term.mk_var ("hyp_close_h", bool_ty --> bool_ty)
         val eta = Term.mk_abs (x, Term.mk_comb (f, x))
         val abstraction =
           Term.mk_abs (h, boolSyntax.mk_eq (h, f))
         val assumption = Term.mk_comb (abstraction, eta)
         val rule = Drule.ADD_ASSUM assumption boolTheory.TRUTH
         val cs =
           clasetLib.add_sintros [("local", rule)] clasetLib.empty_cs
         val goal = ([assumption], boolSyntax.T)
       in
         case first_step safe_step cs goal of
             NONE => false
           | SOME result => valid_step goal result
       end)

val _ =
  test
    ("GEN step records its eigenvariable and valid evidence",
     fn () =>
       let
         val x = Term.mk_var ("step_gen_x", bool_ty)
         val predicate =
           Term.mk_var ("step_gen_predicate", bool_ty --> bool_ty)
         val goal =
           ([], boolSyntax.mk_forall
             (x, Term.mk_comb (predicate, x)))
       in
         case first_step safe_step clasetLib.empty_cs goal of
             NONE => false
           | SOME (record, node) =>
               (case clasetStep.kind_of record of
                    clasetStep.Gen =>
                      length (clasetStep.eigenvariables_of record) = 1
                      andalso valid_step goal (record, node)
                  | _ => false)
       end)

fun same_goal ((asl1, w1), (asl2, w2)) =
  boolSyntax.goal_eq (asl1, w1) (asl2, w2)

fun same_goals left right = ListPair.allEq same_goal (left, right)

fun tactic_fails tactic goal =
  (ignore (tactic goal (Context.snapshot())); false)
  handle HOL_ERR _ => true

fun tactic_error_message tactic goal =
  (ignore (tactic goal (Context.snapshot())); NONE)
  handle HOL_ERR error => SOME (Feedback.message_of error)

val classical_marker_entry_points =
  [classicalLib.SAFE_TAC, classicalLib.CLARIFY_TAC,
   classicalLib.SAFE_STEP_TAC, classicalLib.CLARIFY_STEP_TAC,
   classicalLib.STEP_TAC, classicalLib.SLOW_STEP_TAC,
   classicalLib.INST_STEP_TAC, classicalLib.FAST_TAC,
   classicalLib.SLOW_TAC, classicalLib.BEST_TAC,
   classicalLib.SLOW_BEST_TAC, classicalLib.FIRST_BEST_TAC,
   classicalLib.ASTAR_TAC, classicalLib.SLOW_ASTAR_TAC,
   classicalLib.DEEPEN_TAC]

val _ =
  test
    ("classical tactics clearly reject Simp and Iff markers",
     fn () =>
       let
         val goal = ([], boolSyntax.T)
         fun rejected (marker, expected) =
           List.all
             (fn entry_point =>
                tactic_error_message (entry_point [marker]) goal =
                  SOME expected)
             classical_marker_entry_points
       in
         rejected
           (clasetLib.Simp boolTheory.TRUTH,
            "Simp marker requires a tactic with a simpset") andalso
         rejected
           (clasetLib.Iff boolTheory.TRUTH,
            "Iff marker requires a tactic with a simpset")
       end)

val _ =
  test
    ("SAFE_TAC saturates implication and conjunction in premise order",
     fn () =>
       let
         val goal =
           ([], boolSyntax.mk_imp
             (goal_p, boolSyntax.mk_conj (goal_q, goal_r)))
         val (residues, _) =
           Tactical.VALID
             (classicalLib.SAFE_TAC
               [clasetLib.SIntro boolTheory.AND_INTRO_THM]) goal
         val expected = [([], goal_q), ([], goal_r)]
       in
         same_goals residues expected
       end)

val _ =
  test
    ("SAFE_TAC validates an eta-reduced EXISTS major in match mode",
     fn () =>
       let
         val bound = Term.mk_var ("safe_eta_bound", Type.ind)
         val predicate =
           Term.mk_var ("safe_eta_predicate", Type.ind --> bool_ty)
         val target = Term.mk_var ("safe_eta_target", bool_ty)
         val major =
           boolSyntax.mk_exists
             (bound, Term.mk_comb (predicate, bound))
         val (residues, _) =
           Tactical.VALID (classicalLib.SAFE_TAC []) ([major], target)
       in
         case residues of
             [([assumption], conclusion)] =>
               let val (head, arguments) = strip_comb assumption
               in
                 Term.aconv head predicate andalso
                 length arguments = 1 andalso
                 (* The existential elimination's minor premise already
                    concludes the rule's conclusion, so the classical form
                    adds no negated goal and the target survives the step. *)
                 Term.aconv conclusion target
               end
           | _ => false
       end)

val _ =
  test
    ("SAFE_TAC discharges an assumption the caller posed contracted",
     fn () =>
       let
         val predicate =
           Term.mk_var ("safe_contracted_predicate", Type.ind --> bool_ty)
         val target =
           Term.mk_var ("safe_contracted_target", Type.ind --> bool_ty)
         fun contract predicate =
           Term.mk_comb
             (Term.inst [Type.alpha |-> Type.ind] boolSyntax.universal,
              predicate)
         val assumption = contract predicate
         val conclusion = contract target
         (* The entry spells a contracted binder out, so the proof states
            the assumption spelled out while the caller's goal assumes it
            contracted; a validation that discharges only the spelling it
            entered with leaves the other one a hypothesis. *)
         val (residues, _) =
           Tactical.VALID (classicalLib.SAFE_TAC []) ([assumption], conclusion)
       in
         length residues = 1
       end)

val _ =
  test
    ("CLARIFY_TAC leaves a genuinely branching conjunction intact",
     fn () =>
       let
         val conjunction = boolSyntax.mk_conj (goal_q, goal_r)
         val goal = ([], boolSyntax.mk_imp (goal_p, conjunction))
         val (residues, _) =
           Tactical.VALID
             (classicalLib.CLARIFY_TAC
               [clasetLib.SIntro boolTheory.AND_INTRO_THM]) goal
       in
         same_goals residues [([], conjunction)]
       end)

val _ =
  test
    ("public step tactics perform one valid step",
     fn () =>
       let
         val implication = boolSyntax.mk_imp (goal_p, goal_q)
         val goal = ([], implication)
         val expected = [([goal_p], goal_q)]
         val (safe_goals, _) =
           Tactical.VALID (classicalLib.SAFE_STEP_TAC []) goal
         val (clarify_goals, _) =
           Tactical.VALID (classicalLib.CLARIFY_STEP_TAC []) goal
       in
         same_goals safe_goals expected andalso
         same_goals clarify_goals expected
       end)

val _ =
  test
    ("safe and clarify tactics fail exactly when nothing changes",
     fn () =>
       let val goal = ([], goal_p)
       in
         tactic_fails (classicalLib.SAFE_TAC []) goal andalso
         tactic_fails (classicalLib.CLARIFY_TAC []) goal andalso
         tactic_fails (classicalLib.SAFE_STEP_TAC []) goal andalso
         tactic_fails (classicalLib.CLARIFY_STEP_TAC []) goal
       end)

(* Inserting a fact changes the goal, so the invocation has made progress
   even when the engine then finds no step; discarding the fact would fail
   an invocation that did change something. *)
val _ =
  test
    ("safe and clarify tactics keep an inserted fact when nothing steps",
     fn () =>
       let
         val theorem = boolTheory.TRUTH
         val goal = ([], goal_p)
         val expected = [([concl theorem], goal_p)]
         fun residues tactic =
           #1 (Tactical.VALID (tactic [theorem]) goal)
       in
         same_goals (residues classicalLib.SAFE_TAC) expected andalso
         same_goals (residues classicalLib.CLARIFY_TAC) expected
       end)

val _ =
  test
    ("an unmarked theorem is visible in non-closing tactic residues",
     fn () =>
       let
         val residue_fact = concl boolTheory.TRUTH
         val theorem = boolTheory.TRUTH
         val goal = ([], boolSyntax.mk_conj (goal_p, goal_q))
         val (residues, _) =
           Tactical.VALID (classicalLib.SAFE_TAC [theorem]) goal
       in
         same_goals residues
           [([residue_fact], goal_p), ([residue_fact], goal_q)]
       end)

val _ =
  test
    ("per-invocation claset changes never leak",
     fn () =>
       let
         fun global_rule_names () =
           map (fn (_, (name, _)) => name)
             (clasetLib.rules_of (clasetLib.the_claset ()))
         val initial_names = global_rule_names ()
         val a = Term.mk_var ("leak_a", Type.ind)
         val p = Term.mk_var ("leak_p", Type.ind --> Type.bool)
         val q = Term.mk_var ("leak_q", Type.ind --> Type.bool)
         val pa = mk_comb (p, a)
         val qa = mk_comb (q, a)
         val disjunction = boolSyntax.mk_disj (pa, qa)
         val local_rule = DISCH pa (DISJ1 (ASSUME pa) qa)
         val marker = clasetLib.SIntro local_rule
         val success_goal = ([pa], disjunction)
         val _ =
           Tactical.VALID (classicalLib.SAFE_TAC [marker]) success_goal
         val _ =
           tactic_fails (classicalLib.SAFE_TAC [marker]) ([], goal_p)
       in
         initial_names = global_rule_names ()
       end)

(* TASK_07 group 1: golden safe-cascade ordering. *)

fun step_gives cs goal expected_kind expected_goals =
  case first_step safe_step cs goal of
      NONE => false
    | SOME (record, node) =>
        expected_kind (clasetStep.kind_of record) andalso
        same_goals (rendered_goals node) expected_goals andalso
        valid_step goal (record, node)

val phase1_a = Term.mk_var ("phase1_a", Type.ind)
val phase1_p = Term.mk_var ("phase1_p", Type.ind --> Type.bool)
val phase1_q = Term.mk_var ("phase1_q", Type.ind --> Type.bool)
val phase1_r = Term.mk_var ("phase1_r", Type.ind --> Type.bool)
val phase1_pa = mk_comb (phase1_p, phase1_a)
val phase1_qa = mk_comb (phase1_q, phase1_a)
val phase1_ra = mk_comb (phase1_r, phase1_a)
val phase1_x = Term.mk_var ("phase1_x", Type.ind)
val phase1_c = boolSyntax.mk_arb Type.ind
val phase1_eq = boolSyntax.mk_eq (phase1_x, phase1_c)

val cascade_cs =
  clasetLib.add_sintros
    [("cascade-truth", boolTheory.TRUTH),
     ("cascade-and", boolTheory.AND_INTRO_THM)]
    clasetLib.empty_cs

val _ =
  test
    ("safe cascade slot 1 closes by assumption with exact residue",
     fn () =>
       step_gives cascade_cs ([phase1_pa], phase1_pa)
         (fn clasetStep.Assumption 1 => true | _ => false) [])

val _ =
  test
    ("safe cascade slot 2 performs modus ponens before later slots",
     fn () =>
       let
         val implication = boolSyntax.mk_imp (phase1_pa, phase1_qa)
         val goal = ([phase1_pa, implication], phase1_ra)
         val expected = [([phase1_qa, phase1_pa], phase1_ra)]
       in
         step_gives cascade_cs goal
           (fn clasetStep.ModusPonens
                 {implication = 2, antecedent = 1} => true
             | _ => false)
           expected
       end)

val _ =
  test
    ("indexed safe closure preserves alpha-equivalent assumption order",
     fn () =>
       let
         val x = mk_var ("closure_x", Type.ind)
         val y = mk_var ("closure_y", Type.ind)
         fun all v =
           boolSyntax.mk_forall
             (v, boolSyntax.mk_conj (mk_comb (phase1_p, v), phase1_pa))
         val ax = all x
         val ay = all y
         val negatives =
           [ax, boolSyntax.mk_neg ay, ay, boolSyntax.mk_neg ax]
         val implications =
           [ax, boolSyntax.mk_imp (ay, phase1_qa), ay,
            boolSyntax.mk_imp (ax, phase1_qa)]
         fun positions select assumptions =
           let
             val goal = (assumptions, phase1_ra)
             val steps = seq.take 5 (safe_step cascade_cs
               (clasetGoal.from_goal goal, 1))
           in
             if length steps = 4 andalso List.all (valid_step goal) steps then
               List.mapPartial (select o clasetStep.kind_of o #1) steps
             else []
           end
         fun contradiction (clasetStep.Contradiction positions) =
               SOME positions
           | contradiction _ = NONE
         fun mp (clasetStep.ModusPonens {implication, antecedent}) =
               SOME (implication, antecedent)
           | mp _ = NONE
         val expected = [(2, 1), (2, 3), (4, 1), (4, 3)]
       in
         positions contradiction negatives = expected andalso
         positions mp implications = expected
       end)

val _ =
  test
    ("safe assumption alternatives keep their order and precedence",
     fn () =>
       let
         val x = mk_var ("safe_closure_x", bool_ty)
         val f = mk_var ("safe_closure_f", bool_ty --> bool_ty)
         val g = mk_var ("safe_closure_g", bool_ty --> bool_ty)
         val target = boolSyntax.mk_eq (f, g)
         val eta = boolSyntax.mk_eq (mk_abs (x, mk_comb (f, x)), g)
         val goal = ([phase1_pa, eta, boolSyntax.mk_neg phase1_pa, target],
                     target)
         val steps = seq.take 3
           (safe_step cascade_cs (clasetGoal.from_goal goal, 1))
       in
         (case map (clasetStep.kind_of o #1) steps of
              [clasetStep.Assumption 2, clasetStep.Assumption 4] => true
            | _ => false) andalso
         List.all (valid_step goal) steps
       end)

val _ =
  test
    ("lookup spellings follow beta reductions after instantiation",
     fn () =>
       let
         val residue = ``\x:ind. x IN (lookup_f x : ind -> bool)``
         val (meta, pending) =
           clasetMeta.new_meta {allow = [], ty = type_of residue}
             clasetMeta.empty
         val store = the_store (clasetMeta.bind (meta, residue) pending)
         val exposed = mk_comb (meta, phase1_a)
         val unused = mk_var ("unused", Type.bool)
         val erased = mk_comb (mk_abs (unused, phase1_pa), exposed)
         val goal = {params = [], asl = [erased, exposed], w = exposed}
         fun expected tm =
           let fun spell conv = boolSyntax.rhs (concl (conv tm))
           in
             Lib.op_mk_set aconv
               [tm, spell clasetNorm.membership_conv,
                spell clasetNorm.crossed_conv, spell clasetNorm.applied_conv]
           end
         fun check use_size =
           let
             val node = clasetGoal.create
               {goals = [goal], store = store, level = 0}
             val _ = if use_size then ignore (clasetGoal.size node) else ()
             val {conclusion, assumptions} = clasetGoal.lookup_spellings node 1
             val (asl, w) = clasetGoal.render node 1
             val (head, _) = strip_comb w
             fun same left right =
               ListPair.allEq (uncurry aconv) (left, right)
           in
             same_const head boolSyntax.IN_tm andalso
             aconv (hd asl) phase1_pa andalso
             same conclusion (expected w) andalso
             ListPair.allEq (uncurry same) (assumptions, map expected asl)
           end
       in
         check false andalso check true
       end)

val _ =
  test
    ("safe cascade slot 3 applies a safe zero-premise rule",
     fn () =>
       step_gives cascade_cs ([], boolSyntax.T)
         (fn clasetStep.RuleApplication {elim = false, ...} => true
           | _ => false)
         [])

val _ =
  test
    ("DISCH occupies the built-in position before hyp substitution",
     fn () =>
       let
         val goal =
           ([phase1_eq], boolSyntax.mk_imp (phase1_pa, phase1_qa))
         val expected = [([phase1_pa, phase1_eq], phase1_qa)]
       in
         step_gives cascade_cs goal
           (fn clasetStep.Disch => true | _ => false) expected
       end)

val _ =
  test
    ("GEN occupies the built-in position before hyp substitution",
     fn () =>
       let
         val quantified =
           boolSyntax.mk_forall
             (phase1_x, Term.mk_comb (phase1_p, phase1_x))
         val goal = ([phase1_eq], quantified)
       in
         case first_step safe_step cascade_cs goal of
             NONE => false
           | SOME (record, node) =>
               (case (clasetStep.kind_of record, rendered_goals node) of
                    (clasetStep.Gen, [(asms, body)]) =>
                      let val fresh = rand body
                      in
                        same_goals [(asms, body)]
                          [([phase1_eq], mk_comb (phase1_p, fresh))]
                        andalso
                        not (Term.aconv fresh phase1_x)
                        andalso valid_step goal (record, node)
                      end
                  | _ => false)
       end)

(* src/HOL/Product_Type.thy:518 @ Isabelle2025-2 installs [split_all_tac]
   as a safe claset wrapper, so a product parameter is replaced by one
   parameter per component before any safe rule is tried.  The universal
   here is the parameter, and its own introduction must not get there
   first. *)
val _ =
  test
    ("a paired universal splits before the built-in introduction",
     fn () =>
       let
         val paired =
           Term.mk_var ("phase1_pair",
             pairSyntax.mk_prod (Type.ind, Type.ind) --> Type.bool)
         val bound =
           Term.mk_var ("phase1_v",
             pairSyntax.mk_prod (Type.ind, Type.ind))
         val goal =
           ([], boolSyntax.mk_forall (bound, mk_comb (paired, bound)))
       in
         case first_step safe_step cascade_cs goal of
             NONE => false
           | SOME (record, node) =>
               (case (clasetStep.kind_of record, rendered_goals node) of
                    (clasetStep.SplitPaired, [(_, split)]) =>
                      let
                        val (left, body) = boolSyntax.dest_forall split
                        val (right, _) = boolSyntax.dest_forall body
                      in
                        Type.compare (type_of left, Type.ind) = EQUAL
                        andalso
                        Type.compare (type_of right, Type.ind) = EQUAL
                        andalso valid_step goal (record, node)
                      end
                  | _ => false)
       end)

(* Isabelle's split_all_tac (src/HOL/Product_Type.thy:493 @ Isabelle2025-2)
   splits the subgoal's parameters, and a HOL4 subgoal states its
   conclusion for every free variable it carries, so a product-typed free
   variable is one too even where no universal is left to strip. *)
val _ =
  test
    ("a product free variable splits like a parameter",
     fn () =>
       let
         val pair_type = pairSyntax.mk_prod (Type.ind, Type.ind)
         val paired =
           Term.mk_var ("phase1_free_pair", pair_type --> Type.bool)
         val free = Term.mk_var ("phase1_free_v", pair_type)
         val goal = ([], mk_comb (paired, free))
       in
         case first_step safe_step cascade_cs goal of
             NONE => false
           | SOME (record, node) =>
               (case (clasetStep.kind_of record, rendered_goals node) of
                    (clasetStep.SplitPaired, [(_, split)]) =>
                      not (List.exists (aconv free) (free_vars split))
                      andalso valid_step goal (record, node)
                  | _ => false)
       end)

(* A metavariable is not a parameter: it stands for the schematic variable
   Isabelle's split never reaches, and taking it apart would commit the
   search to a pair before it has chosen the witness. *)
val _ =
  test
    ("a product metavariable is not split",
     fn () =>
       let
         val pair_type = pairSyntax.mk_prod (Type.ind, Type.ind)
         val paired =
           Term.mk_var ("phase1_meta_pair", pair_type --> Type.bool)
         val (meta, store) =
           clasetMeta.new_meta {allow = [], ty = pair_type} clasetMeta.empty
         val node =
           clasetGoal.create
             {goals = [{params = [], asl = [], w = mk_comb (paired, meta)}],
              store = store, level = 0}
       in
         not (Option.isSome
           (seq.cases (safe_step cascade_cs (node, 1))))
       end)

val _ =
  test
    ("safe cascade slot 4 saturates hypothesis substitution",
     fn () =>
       let val goal = ([phase1_eq], mk_comb (phase1_p, phase1_x))
       in
         step_gives cascade_cs goal
           (fn clasetStep.HypSubst => true | _ => false)
           [([], mk_comb (phase1_p, phase1_c))]
       end)

val _ =
  test
    ("safe cascade slot 5 applies a positive-premise safe rule",
     fn () =>
       let
         val goal = ([], boolSyntax.mk_conj (phase1_pa, phase1_qa))
         val expected = [([], phase1_pa), ([], phase1_qa)]
       in
         step_gives cascade_cs goal
           (fn clasetStep.RuleApplication {elim = false, ...} => true
             | _ => false)
           expected
       end)

(* TASK_07 group 2: CLARIFY_TAC restrictions and bimatch2. *)

fun three_premise_intro () =
  let
    val p = Term.mk_var ("three_p", Type.bool)
    val q = Term.mk_var ("three_q", Type.bool)
    val r = Term.mk_var ("three_r", Type.bool)
    val body = CONJ (ASSUME p) (CONJ (ASSUME q) (ASSUME r))
  in
    GENL [p, q, r] (DISCH p (DISCH q (DISCH r body)))
  end

val _ =
  test
    ("CLARIFY accepts weight 1 and asserts its exact residue",
     fn () =>
       let
         val implication = boolSyntax.mk_imp (phase1_qa, phase1_pa)
         val cs =
           clasetLib.add_sintros [("clarify-one", ASSUME implication)]
             clasetLib.empty_cs
         val goal = ([implication], phase1_pa)
       in
         case first_step (clasetStep.clarify_step_in (Context.snapshot ()))
                cs goal of
             NONE => false
           | SOME (record, node) =>
               same_goals (rendered_goals node)
                 [([implication], phase1_qa)] andalso
               valid_step goal (record, node)
       end)

val _ =
  test
    ("CLARIFY rejects rules of weight 3",
     fn () =>
       let
         val cs =
           clasetLib.add_sintros
             [("clarify-three", three_premise_intro ())]
             clasetLib.empty_cs
         val target =
           boolSyntax.mk_conj
             (phase1_pa, boolSyntax.mk_conj (phase1_qa, phase1_ra))
       in
         not (Option.isSome
           (first_step (clasetStep.clarify_step_in (Context.snapshot ()))
              cs ([], target)))
       end)

val _ =
  test
    ("CLARIFY bimatch2 closes the left branch exactly",
     fn () =>
       let
         val cs =
           clasetLib.add_sintros
             [("clarify-and", boolTheory.AND_INTRO_THM)]
             clasetLib.empty_cs
         val goal =
           ([phase1_pa], boolSyntax.mk_conj (phase1_pa, phase1_qa))
       in
         case first_step (clasetStep.clarify_step_in (Context.snapshot ()))
                cs goal of
             NONE => false
           | SOME (record, node) =>
               same_goals (rendered_goals node)
                 [([phase1_pa], phase1_qa)] andalso
               valid_step goal (record, node)
       end)

val _ =
  test
    ("CLARIFY bimatch2 closes the right branch exactly",
     fn () =>
       let
         val cs =
           clasetLib.add_sintros
             [("clarify-and", boolTheory.AND_INTRO_THM)]
             clasetLib.empty_cs
         val goal =
           ([phase1_qa], boolSyntax.mk_conj (phase1_pa, phase1_qa))
       in
         case first_step (clasetStep.clarify_step_in (Context.snapshot ()))
                cs goal of
             NONE => false
           | SOME (record, node) =>
               same_goals (rendered_goals node)
                 [([phase1_qa], phase1_pa)] andalso
               valid_step goal (record, node)
       end)

val _ =
  test
    ("CLARIFY bimatch2 accepts a matching-contradiction branch",
     fn () =>
       let
         val negated = boolSyntax.mk_neg phase1_pa
         val disjunction = boolSyntax.mk_disj (phase1_pa, phase1_qa)
         val cs =
           clasetLib.add_selims
             [("clarify-or", boolTheory.OR_ELIM_THM)]
             clasetLib.empty_cs
         val goal = ([negated, disjunction], phase1_ra)
         val expected = [([phase1_qa, negated], phase1_ra)]
       in
         case first_step (clasetStep.clarify_step_in (Context.snapshot ()))
                cs goal of
             NONE => false
           | SOME (record, node) =>
               same_goals (rendered_goals node) expected andalso
               valid_step goal (record, node)
       end)

val _ =
  test
    ("CLARIFY leaves an unclosable conjunction conclusion untouched",
     fn () =>
       let
         val target = boolSyntax.mk_conj (phase1_pa, phase1_qa)
         val goal = ([], target)
         val (residues, _) =
           Tactical.VALID
             (Tactical.TRY
               (classicalLib.CLARIFY_TAC
                 [clasetLib.SIntro boolTheory.AND_INTRO_THM]))
             goal
       in
         same_goals residues [goal]
       end)

(* TASK_07 group 3: SAFE_TAC against the seed claset. *)

val _ =
  test
    ("seed SAFE_TAC splits conjunctions with exact residues",
     fn () =>
       let
         val goal = ([], boolSyntax.mk_conj (phase1_pa, phase1_qa))
         val (residues, _) =
           Tactical.VALID (classicalLib.SAFE_TAC []) goal
       in
         same_goals residues [([], phase1_pa), ([], phase1_qa)]
       end)

val _ =
  test
    ("seed SAFE_TAC eliminates a conjunctive assumption exactly",
     fn () =>
       let
         val conjunction = boolSyntax.mk_conj (phase1_pa, phase1_qa)
         val goal = ([], boolSyntax.mk_imp (conjunction, phase1_ra))
         val (residues, _) =
           Tactical.VALID (classicalLib.SAFE_TAC []) goal
       in
         same_goals residues [([phase1_qa, phase1_pa], phase1_ra)]
       end)

val _ =
  test
    ("seed SAFE_TAC handles universal introduction and implication",
     fn () =>
       let
         val body =
           boolSyntax.mk_imp
             (mk_comb (phase1_p, phase1_x),
              mk_comb (phase1_p, phase1_x))
         val goal = ([], boolSyntax.mk_forall (phase1_x, body))
         val (residues, _) =
           Tactical.VALID (classicalLib.SAFE_TAC []) goal
       in
         List.null residues
       end)

val _ =
  test
    ("seed SAFE_TAC applies safe disjunction introduction exactly",
     fn () =>
       let
         val target = boolSyntax.mk_disj (phase1_pa, phase1_qa)
         val goal = ([], target)
         val (residues, _) =
           Tactical.VALID (classicalLib.SAFE_TAC []) goal
       in
         same_goals residues
           [([boolSyntax.mk_neg phase1_qa], phase1_pa)]
       end)

val _ =
  test
    ("seed SAFE_TAC never applies unsafe universal elimination",
     fn () =>
       let
         val universal =
           boolSyntax.mk_forall
             (phase1_x, mk_comb (phase1_p, phase1_x))
         val goal = ([universal], phase1_pa)
         val (residues, _) =
           Tactical.VALID
             (Tactical.TRY (classicalLib.SAFE_TAC [])) goal
       in
         same_goals residues [goal]
       end)

val _ =
  test
    ("seed SAFE_TAC never instantiates EXISTS_INTRO_THM",
     fn () =>
       let
         val existential =
           boolSyntax.mk_exists
             (phase1_x, mk_comb (phase1_p, phase1_x))
         val goal = ([phase1_pa], existential)
         val (residues, _) =
           Tactical.VALID
             (Tactical.TRY (classicalLib.SAFE_TAC [])) goal
       in
         same_goals residues [goal]
       end)

(* TASK_07 group 4: failure, markers, wrappers, and state isolation. *)

val _ =
  test
    ("D27 exposes raw no-change behavior through TRY",
     fn () =>
       let
         val goal = ([], phase1_pa)
         val (safe_goals, _) =
           Tactical.VALID
             (Tactical.TRY (classicalLib.SAFE_TAC [])) goal
         val (clarify_goals, _) =
           Tactical.VALID
             (Tactical.TRY (classicalLib.CLARIFY_TAC [])) goal
       in
         tactic_fails (classicalLib.SAFE_TAC []) goal andalso
         tactic_fails (classicalLib.CLARIFY_TAC []) goal andalso
         same_goals safe_goals [goal] andalso
         same_goals clarify_goals [goal]
       end)

fun marker_consumed marker =
  let val (_, leftovers) =
    clasetLib.process_claset_tags [marker] clasetLib.empty_cs
  in List.null leftovers end

val _ =
  test
    ("classical marker vocabulary is consumed and generic tags pass",
     fn () =>
       let
         val consumed =
           [clasetLib.SIntro boolTheory.AND_INTRO_THM,
            clasetLib.Intro boolTheory.EQ_EXT,
            clasetLib.SElim boolTheory.OR_ELIM_THM,
            clasetLib.Elim clasetSeedTheory.FORALL_ELIM_THM,
            clasetLib.SDest boolTheory.OR_ELIM_THM,
            clasetLib.Dest clasetSeedTheory.FORALL_ELIM_THM,
            clasetLib.Del "not-present"]
         val passthrough =
           [markerLib.Cong boolTheory.TRUTH,
            markerLib.Split boolTheory.OR_CLAUSES,
            markerLib.Excl "simp-rule",
            markerLib.ExclX "rule:simp-rule"]
         val (_, leftovers) =
           clasetLib.process_claset_tags passthrough clasetLib.empty_cs
       in
         List.all marker_consumed consumed andalso
         ListPair.allEq
           (fn (left, right) => Term.aconv (concl left) (concl right))
           (leftovers, passthrough)
       end)

val _ =
  test
    ("generic Excl passes through without deleting a seed rule",
     fn () =>
       let
         val goal = ([], boolSyntax.mk_conj (phase1_pa, phase1_qa))
         val (residues, _) =
           Tactical.VALID
             (classicalLib.SAFE_TAC
               [markerLib.Excl "bool$AND_INTRO_THM"])
             goal
       in
         same_goals residues [([], phase1_pa), ([], phase1_qa)]
       end)

val _ =
  test
    ("classical tactics discard Split and ExclX without a simpset",
     fn () =>
       let
         val goal = ([], boolSyntax.mk_conj (phase1_pa, phase1_qa))
         val controls =
           [markerLib.Split boolTheory.OR_CLAUSES,
            markerLib.ExclX "rule:bool.AND_INTRO_THM"]
         val (residues, _) =
           Tactical.VALID (classicalLib.SAFE_TAC controls) goal
       in
         same_goals residues [([], phase1_pa), ([], phase1_qa)]
       end)

val _ =
  test
    ("FAST_TAC unwraps and inserts a Once-wrapped theorem",
     fn () =>
       let
         val theorem = combinTheory.I_THM
         val goal = ([], concl theorem)
       in
         tactic_fails (classicalLib.FAST_TAC []) goal andalso
         not
           (tactic_fails
             (classicalLib.FAST_TAC [BoundedRewrites.Once theorem])
             goal)
       end)

val _ =
  test
    ("FAST_TAC honors Abbr controls before classical search",
     fn () =>
       let
         val abbreviation = "classical_abbreviated_p"
         val abbreviated =
           Term.mk_var (abbreviation, Type.bool)
         val goal =
           ([markerSyntax.mk_abbrev (abbreviation, phase1_pa), phase1_pa],
            abbreviated)
       in
         tactic_fails (classicalLib.FAST_TAC []) goal andalso
         not
           (tactic_fails
             (classicalLib.FAST_TAC
               [markerLib.Abbr [QUOTE abbreviation]]) goal)
       end)

val _ =
  test
    ("Del is consumed and removes a seed rule for one invocation",
     fn () =>
       let
         val goal = ([], boolSyntax.mk_conj (phase1_pa, phase1_qa))
         val (residues, _) =
           Tactical.VALID
             (Tactical.TRY
               (classicalLib.SAFE_TAC
                 [clasetLib.Del "bool$AND_INTRO_THM"]))
             goal
         val (after, _) =
           Tactical.VALID (classicalLib.SAFE_TAC []) goal
       in
         same_goals residues [goal] andalso
         same_goals after [([], phase1_pa), ([], phase1_qa)]
       end)

fun safe_before tactic base =
  NTactical.NORELSE (NTactical.LIFT tactic, base)

val _ =
  test
    ("safe wrappers compose newest innermost with ORELSE commitment",
     fn () =>
       let
         val left = boolSyntax.mk_imp (phase1_pa, phase1_pa)
         val right = boolSyntax.mk_imp (phase1_qa, phase1_qa)
         val target = boolSyntax.mk_conj (left, right)
         val left_thm = DISCH phase1_pa (ASSUME phase1_pa)
         val right_thm = DISCH phase1_qa (ASSUME phase1_qa)
         val target_thm = CONJ left_thm right_thm
         val cs =
           clasetLib.add_safe_wrapper
             ("new", safe_before (Tactic.ACCEPT_TAC target_thm))
             (clasetLib.add_safe_wrapper
               ("old", safe_before Tactic.CONJ_TAC)
               clasetLib.empty_cs)
         val goal = ([], target)
       in
         case first_step safe_step cs goal of
             NONE => false
           | SOME (record, node) =>
               (case clasetStep.kind_of record of
                    clasetStep.Wrapper =>
                      same_goals (rendered_goals node)
                        [([], left), ([], right)] andalso
                      valid_step goal (record, node)
                  | _ => false)
       end)

(* TASK_07 group 5: the materialized hypothesis-substitution slot. *)

val phase1_y = Term.mk_var ("phase1_y", Type.ind)
val phase1_f = Term.mk_var ("phase1_f", Type.ind --> Type.ind)

val _ =
  test
    ("hyp-subst saturates a chain in one safe step",
     fn () =>
       let
         val first = boolSyntax.mk_eq (phase1_x, phase1_c)
         val second = boolSyntax.mk_eq (phase1_y, phase1_x)
         val goal =
           ([first, second], mk_comb (phase1_p, phase1_y))
       in
         step_gives clasetLib.empty_cs goal
           (fn clasetStep.HypSubst => true | _ => false)
           [([], mk_comb (phase1_p, phase1_c))]
       end)

val _ =
  test
    ("hyp-subst refuses both orientations of an occurs-check cycle",
     fn () =>
       let
         val fx = mk_comb (phase1_f, phase1_x)
         val left = boolSyntax.mk_eq (phase1_x, fx)
         val right = boolSyntax.mk_eq (fx, phase1_x)
         fun refuses equality =
           not (Option.isSome
             (first_step safe_step clasetLib.empty_cs
               ([equality], phase1_pa)))
       in
         refuses left andalso refuses right
       end)

val _ =
  test
    ("hyp-subst deletes reflexive equalities",
     fn () =>
       let
         val reflexive = boolSyntax.mk_eq (phase1_x, phase1_x)
         val goal = ([reflexive], mk_comb (phase1_p, phase1_x))
       in
         step_gives clasetLib.empty_cs goal
           (fn clasetStep.HypSubst => true | _ => false)
           [([], mk_comb (phase1_p, phase1_x))]
       end)

val _ =
  test
    ("hyp-subst keeps HOL4 positive and negative bool-atom extras",
     fn () =>
       let
         val atom_p = Term.mk_var ("hyp_atom_p", Type.bool)
         val atom_q = Term.mk_var ("hyp_atom_q", Type.bool)
         val goal =
           ([atom_p, boolSyntax.mk_neg atom_q], phase1_ra)
       in
         step_gives clasetLib.empty_cs goal
           (fn clasetStep.HypSubst => true | _ => false)
           [([], phase1_ra)]
       end)

(* TASK_10: unify-mode cascades and bounded depth selection. *)

fun drain_steps sequence =
  case seq.cases sequence of
      NONE => []
    | SOME (result, rest) => result :: drain_steps rest

val _ =
  test
    ("unify rule application leaves and records a witness metavariable",
     fn () =>
       let
         val witness = Term.mk_var ("unify_witness", Type.ind)
         val predicate =
           Term.mk_var ("unify_predicate", Type.ind --> Type.bool)
         val target =
           boolSyntax.mk_exists (witness, mk_comb (predicate, witness))
         val cs =
           clasetLib.add_intros
             [("unify-exists", clasetSeedTheory.EXISTS_INTRO_THM)]
             clasetLib.empty_cs
         val input = ([], target)
       in
         case first_step clasetStep.unsafe_step cs input of
             NONE => false
           | SOME (record, node) =>
               let
                 val {terms, types} = clasetStep.created_of record
                 val (_, child_w) = the_singleton (rendered_goals node)
                 val unresolved =
                   clasetMeta.metas_of (clasetGoal.store node) child_w
               in
                 (case clasetStep.kind_of record of
                      clasetStep.RuleApplication {elim = false, ...} => true
                    | _ => false) andalso
                 not (List.null terms) andalso
                 not (List.null types) andalso
                 not (List.null unresolved)
               end
       end)

val _ =
  test
    ("inst0 assumption unifies the goal with an assumption",
     fn () =>
       let
         val proposition = Term.mk_var ("unify_assumption", Type.bool)
         val (meta, store) =
           clasetMeta.new_meta {allow = [], ty = Type.bool}
             clasetMeta.empty
         val node =
           clasetGoal.create
             {goals = [{params = [], asl = [proposition], w = meta}],
              store = store, level = 0}
       in
         case seq.cases
           (clasetStep.inst0_step clasetLib.empty_cs (node, 1))
         of
             NONE => false
           | SOME ((record, next), _) =>
               (case clasetStep.kind_of record of
                    clasetStep.Assumption 1 => true
                  | _ => false) andalso
               List.null (clasetGoal.goals next) andalso
               Term.aconv
                 (clasetMeta.norm (clasetGoal.store next) meta)
                 proposition
       end)

val _ =
  test
    ("inst0 APPEND keeps assumption then contradiction alternatives",
     fn () =>
       let
         val proposition = Term.mk_var ("append_proposition", Type.bool)
         val negative = boolSyntax.mk_neg proposition
         val (meta, store) =
           clasetMeta.new_meta {allow = [], ty = Type.bool}
             clasetMeta.empty
         val node =
           clasetGoal.create
             {goals =
                [{params = [], asl = [proposition, negative], w = meta}],
              store = store, level = 0}
         val results =
           drain_steps
             (clasetStep.inst0_step clasetLib.empty_cs (node, 1))
         val kinds = map (clasetStep.kind_of o #1) results
       in
         case kinds of
             [clasetStep.Assumption 1,
              clasetStep.Assumption 2,
              clasetStep.Contradiction (2, 1)] => true
           | _ => false
       end)

val _ =
  test
    ("slow_step_in APPEND keeps unsafe alternatives after inst_step",
     fn () =>
       let
         val witness = Term.mk_var ("slow_append_x", Type.ind)
         val predicate =
           Term.mk_var ("slow_append_p", Type.ind --> Type.bool)
         val proposition = Term.mk_var ("slow_append_q", Type.bool)
         val premise = mk_comb (predicate, witness)
         val safe_rule =
           GENL [predicate, witness]
             (DISCH premise boolTheory.TRUTH)
         val unsafe_rule =
           GEN proposition (DISCH proposition boolTheory.TRUTH)
         val cs =
           clasetLib.add_intros [("slow-unsafe", unsafe_rule)]
             (clasetLib.add_sintros [("slow-inst", safe_rule)]
               clasetLib.empty_cs)
         val node = clasetGoal.from_goal ([], boolSyntax.T)
         val fast =
           drain_steps
             (clasetStep.step_in (Context.snapshot ()) cs (node, 1))
         val slow =
           drain_steps
             (clasetStep.slow_step_in (Context.snapshot ()) cs (node, 1))
         fun child_target (_, result_node) =
           #2 (the_singleton (rendered_goals result_node))
       in
         length fast = 1 andalso length slow = 2 andalso
         is_comb (child_target (hd fast)) andalso
         is_comb (child_target (hd slow)) andalso
         clasetMeta.is_meta (child_target (List.nth (slow, 1)))
       end)

(* The rung reads its alternatives guess-free first.  Read with
   unification, [¬¬t ⇒ t] takes the assumption metavariable for the
   negation its premise wants and leaves it standing for the negation of a
   new metavariable -- a guess the next expansion can guess again.
   [OR_INTRO_THM1] determines nothing the goal has not already fixed, and
   goes first, although a unifying step normally cuts the unsafe ones out
   altogether.  Its swapped form, which reads the same assumption
   metavariable as a disjunction, is a guess and waits with the other one:
   the order changes, the alternatives do not. *)
val guess_order_p = Term.mk_var ("guess_order_p", Type.bool)

val guess_order_dest =
  Drule.GEN_ALL
    (fst (Thm.EQ_IMP_RULE
      (Drule.SPEC_ALL (Thm.CONJUNCT1 boolTheory.NOT_CLAUSES))))

val guess_order_cs =
  clasetLib.add_intros [("guess-order-free", boolTheory.OR_INTRO_THM1)]
    (clasetLib.add_sdests [("guess-order-guess", guess_order_dest)]
      clasetLib.empty_cs)

fun guess_order_node assumption store =
  clasetGoal.create
    {goals =
       [{params = [], asl = [assumption],
         w = boolSyntax.mk_disj (guess_order_p, guess_order_p)}],
     store = store, level = 0}

fun guess_order_rules results =
  List.mapPartial
    (fn (record, _) =>
      case clasetStep.kind_of record of
          clasetStep.RuleApplication {original, ...} => SOME (concl original)
        | _ => NONE)
    results

fun guess_order_offered rung =
  let
    val (meta, store) =
      clasetMeta.new_meta {allow = [], ty = Type.bool} clasetMeta.empty
  in
    guess_order_rules
      (drain_steps
        (rung guess_order_cs
          (guess_order_node (boolSyntax.mk_neg meta) store, 1)))
  end

fun guess_order_expected rules =
  case rules of
      [free, guess, swapped] =>
        aconv free (concl boolTheory.OR_INTRO_THM1) andalso
        aconv guess (concl guess_order_dest) andalso
        aconv swapped (concl boolTheory.OR_INTRO_THM1)
    | _ => false

val _ =
  test
    ("an unsafe step that guesses nothing precedes a unifying guess",
     fn () =>
       guess_order_expected
         (guess_order_offered (clasetStep.step_in (Context.snapshot ()))))

val _ =
  test
    ("the slow rung keeps every alternative and defers the guesses",
     fn () =>
       guess_order_expected
         (guess_order_offered
           (clasetStep.slow_step_in (Context.snapshot ()))))

(* The other way a step leaves an unknown undetermined: [FORALL_ELIM_THM]
   settles the assumption it reads and the goal it leaves, but the instance
   it picks is a metavariable of its own that the goal says nothing about,
   and the next expansion can pick again inside it.  It is declared after
   the introduction rule, so recency offers it first; the guess-free order
   puts it back behind.  The spare unknown in the assumptions is what puts
   the node in the regime where the rung reads both classes. *)
val guess_created_g =
  Term.mk_var ("guess_created_g", Type.ind --> Type.bool)

val guess_created_cs =
  clasetLib.add_elims
    [("guess-created-forall", clasetSeedTheory.FORALL_ELIM_THM)]
    (clasetLib.add_intros
      [("guess-created-free", boolTheory.OR_INTRO_THM1)]
      clasetLib.empty_cs)

val _ =
  test
    ("an instance the goal does not fix is a guess and waits",
     fn () =>
       let
         val y = Term.mk_var ("guess_created_y", Type.ind)
         val universal =
           boolSyntax.mk_forall (y, Term.mk_comb (guess_created_g, y))
         val (meta, store) =
           clasetMeta.new_meta {allow = [], ty = Type.ind} clasetMeta.empty
         val node =
           clasetGoal.create
             {goals =
                [{params = [],
                  asl = [universal, Term.mk_comb (guess_created_g, meta)],
                  w = boolSyntax.mk_disj (guess_order_p, guess_order_p)}],
              store = store, level = 0}
         val rules =
           guess_order_rules
             (drain_steps
               (clasetStep.step_in (Context.snapshot ()) guess_created_cs
                 (node, 1)))
         fun stated theorem = List.exists (aconv (concl theorem))
       in
         case rules of
             first :: rest =>
               aconv first (concl boolTheory.OR_INTRO_THM1) andalso
               stated clasetSeedTheory.FORALL_ELIM_THM rest
           | [] => false
       end)

local
  val subst_variable = Term.mk_var ("internal_subst_x", Type.ind)
  val subst_constant = Term.mk_var ("internal_subst_c", Type.ind)
  val subst_predicate =
    Term.mk_var ("internal_subst_p", Type.ind --> Type.bool)

  fun subst_node assumptions store =
    clasetGoal.create
      {goals =
         [{params = [], asl = assumptions,
           w = mk_comb (subst_predicate, subst_variable)}],
       store = store, level = 0}
in

(* An equality carrying a metavariable is no substitution the search may
   make: eliminating the rigid side restates this branch over an unknown
   the search has not chosen, and the sibling branches keep the variable.
   src/Provers/hypsubst.ML:83 @ Isabelle2025-2 refuses it for the same
   reason. *)
val _ =
  test
    ("metavariable hyp-subst refuses an equality carrying a metavariable",
     fn () =>
       let
         val (meta, store) =
           clasetMeta.new_meta {allow = [], ty = Type.ind}
             clasetMeta.empty
         val node =
           subst_node [boolSyntax.mk_eq (subst_variable, meta)] store
       in
         not (Option.isSome
           (seq.cases
             (safe_step clasetLib.empty_cs (node, 1))))
       end)

(* The refusal is the equality's, not the goal's: a rigid equality still
   substitutes where the goal carries metavariables elsewhere. *)
val _ =
  test
    ("metavariable hyp-subst still eliminates a rigid equality",
     fn () =>
       let
         val (meta, store) =
           clasetMeta.new_meta {allow = [], ty = Type.ind}
             clasetMeta.empty
         val node =
           subst_node
             [boolSyntax.mk_eq (subst_variable, subst_constant),
              mk_comb (subst_predicate, meta)] store
       in
         case seq.cases
           (safe_step clasetLib.empty_cs (node, 1))
         of
             NONE => false
           | SOME ((record, next), _) =>
               let
                 val expected =
                   ([mk_comb (subst_predicate, meta)],
                    mk_comb (subst_predicate, subst_constant))
                 val child = the_singleton (rendered_goals next)
                   val tactic =
                   fn _ => fn _ =>
                     ([child], clasetStep.validation_of record)
                 val _ =
                   Tactical.VALID tactic (clasetGoal.render node 1)
               in
                 (case clasetStep.kind_of record of
                      clasetStep.HypSubst => true
                    | _ => false) andalso
                 same_goal (child, expected) andalso
                 Term.aconv
                   (clasetMeta.walk (clasetGoal.store next) meta) meta
               end
       end)

(* The step saturates, and stops where the equality it reached carries a
   metavariable.  Replay runs against a grounded goal, and the binding the
   search chose later can make that equality substitutable after all: a
   replay that saturates afresh then eliminates what the recorded step
   left standing, and the step recorded against it finds nothing to do.
   So the step replays the eliminations it made, not the ones its goal
   now admits. *)
(* A step's recorded result proves its goal in the spelling the engine
   rendered it in, and replay runs that result against the goal the
   caller posed: a caller who writes a quantifier contracted poses
   [$! P] where the engine's entry spells it out.  The replayed proof is
   restated in the caller's spelling, or the step proves the goal from a
   formula the goal does not assume. *)
val _ =
  test
    ("replay restates a recorded step in the caller's spelling",
     fn () =>
       let
         val predicate =
           Term.mk_var ("replay_spelling_predicate", Type.ind --> bool_ty)
         val witness = Term.mk_var ("replay_spelling_witness", Type.ind)
         val bound = Term.mk_var ("replay_spelling_bound", Type.ind)
         val contracted =
           Term.mk_comb
             (Term.inst [Type.alpha |-> Type.ind] boolSyntax.universal,
              predicate)
         val expanded =
           boolSyntax.mk_forall (bound, Term.mk_comb (predicate, bound))
         val target = Term.mk_comb (predicate, witness)
         val proof = Thm.SPEC witness (ASSUME expanded)
         val record =
           clasetReplay.make_record
             {kind = clasetReplay.Wrapper, target = 1, consumed = NONE,
              created = {terms = [], types = []},
              eigenvariables = [], validation = (fn _ => proof),
              action =
                clasetReplay.fixed_action_on ([expanded], target)
                  ([], fn _ => proof),
              children = []}
         val script = clasetReplay.append (clasetReplay.empty 1) record
         val grounded = clasetReplay.ground clasetMeta.empty script
       in
         case clasetReplay.replay_in (Context.snapshot ())
                grounded ([contracted], target) of
             clasetReplay.Replayed ([], validation) =>
               let
                 val theorem = validation []
               in
                 Term.aconv (concl theorem) target andalso
                 List.all (Term.aconv contracted) (hyp theorem)
               end
           | _ => false
       end)

val _ =
  test
    ("hyp-subst replays its own eliminations, not a fresh saturation",
     fn () =>
       let
         val (meta, store) =
           clasetMeta.new_meta {allow = [], ty = Type.ind}
             clasetMeta.empty
         val reflexive = boolSyntax.mk_eq (subst_constant, subst_constant)
         val deferred = boolSyntax.mk_eq (meta, subst_constant)
         val node = subst_node [reflexive, deferred] store
         val instantiated =
           valOf (clasetMeta.bind (meta, subst_variable) store)
         val grounded_equality =
           boolSyntax.mk_eq (subst_variable, subst_constant)
         val original =
           ([reflexive, grounded_equality],
            mk_comb (subst_predicate, subst_variable))
       in
         case seq.cases
           (safe_step clasetLib.empty_cs (node, 1))
         of
             NONE => false
           | SOME ((record, _), _) =>
               let
                 val script =
                   clasetReplay.append (clasetReplay.empty 1) record
                 val grounded = clasetReplay.ground instantiated script
               in
                 case clasetReplay.replay_in (Context.snapshot ())
                        grounded original of
                     clasetReplay.Replayed ([child], _) =>
                       same_goal
                         (child,
                          ([grounded_equality],
                           mk_comb (subst_predicate, subst_variable)))
                   | _ => false
               end
       end)

end

val _ =
  test
    ("step saturates every safe goal before its selected unsafe rung",
     fn () =>
       let
         val implication = boolSyntax.mk_imp (phase1_pa, phase1_pa)
         val node =
           clasetGoal.create
             {goals =
                [{params = [], asl = [], w = implication},
                 {params = [], asl = [phase1_qa], w = phase1_qa}],
              store = clasetMeta.empty, level = 0}
       in
         case seq.cases
                (clasetStep.step_in (Context.snapshot ()) clasetLib.empty_cs
                  (node, 2)) of
             NONE => false
           | SOME ((_, next), _) => List.null (clasetGoal.goals next)
       end)

val _ =
  test
    ("depth_step_in selects duplicate versus consuming unsafe rules",
     fn () =>
       let
         val bound = Term.mk_var ("depth_bound", Type.ind)
         val predicate =
           Term.mk_var ("depth_predicate", Type.ind --> Type.bool)
         val target = Term.mk_var ("depth_target", Type.bool)
         val universal =
           boolSyntax.mk_forall (bound, mk_comb (predicate, bound))
         val observations =
           ref ([] : (term list * term) list list)

         fun observe tactic goal ctxt =
           seq.map
             (fn result as (goals, _) =>
               (observations := goals :: !observations; result))
             (tactic goal ctxt)

         val cs =
           clasetLib.add_unsafe_wrapper ("observe-depth", observe)
             (clasetLib.add_elims
               [("depth-forall", clasetSeedTheory.FORALL_ELIM_THM)]
               clasetLib.empty_cs)
         val node = clasetGoal.from_goal ([universal], target)

         val forall_head = #1 (strip_comb universal)
         fun is_forall_head tm =
           same_const forall_head (#1 (strip_comb tm))
           handle HOL_ERR _ => false
         fun retained runs =
           List.exists
             (List.exists
               (fn (asl, _) => List.exists is_forall_head asl))
             runs

         val _ =
           seq.length
             (clasetStep.depth_step_in (Context.snapshot ()) cs
               (clasetLib.unsafe_part cs) 1 (node, 1))
         val unsafe_runs = !observations
         val _ = observations := []
         val _ =
           seq.length
             (clasetStep.depth_step_in (Context.snapshot ()) cs
               (clasetLib.dup_part cs) 1 (node, 1))
         val dup_runs = !observations
       in
         not (List.null unsafe_runs) andalso
         not (retained unsafe_runs) andalso retained dup_runs
       end)

(* TASK_11: grounded, zero-search replay and shared vocabulary. *)

fun first_node_step step cs node pos =
  case seq.cases (step cs (node, pos)) of
      NONE => raise Fail "expected a classical engine step"
    | SOME ((record, next), _) => (record, next)

fun valid_grounded_replay original final_node =
  let
    val grounded =
      clasetReplay.ground (clasetGoal.store final_node)
        (clasetGoal.replay final_node)
    val (residues, _) =
      Tactical.VALID (clasetReplay.REPLAY_TAC grounded) original
  in
    List.null residues
  end

fun drain_exact sequence =
  case seq.cases sequence of
      NONE => []
    | SOME (value, rest) => value :: drain_exact rest

fun exact_rule_api_variants cs plain selected input =
  [drain_exact
     (clasetStep.blast_rule_step cs plain (input ())),
   drain_exact
     (clasetStep.blast_rule_step_at cs selected (input ()))]


fun exact_source_term store tm =
  let
    val (type_substitution, term_substitution) =
      clasetMeta.collapse store
  in
    concl
      (Drule.INST_TY_TERM
        (term_substitution, type_substitution) (ASSUME tm))
  end

fun normalize_exact_term tm =
  #2
    (boolSyntax.dest_eq
      (concl
        (Conv.QCONV
          (Conv.REDEPTH_CONV
            (Conv.ORELSEC (BETA_CONV, Drule.ETA_CONV))) tm)))

fun exact_transition_variants cs specification goal =
  [drain_exact
     (clasetStep.blast_rule_step cs specification
       (clasetGoal.from_goal goal, 1))]

fun valid_open_replay goal (record, node) =
  let
    val store = clasetGoal.store node
    (* Replay grounds the store, so a rule parameter still unresolved at
       this node reaches the replayed goal grounded.  Compare the
       rendering after the same grounding; where every metavariable is
       already bound this changes nothing. *)
    val grounded_store = clasetMeta.ground store
    fun ground_goal (asl, w) =
      (map (clasetMeta.instantiate grounded_store) asl,
       clasetMeta.instantiate grounded_store w)
    val expected = map ground_goal (rendered_goals node)
    val grounded = clasetReplay.ground store (clasetGoal.replay node)
    val (actual, _) =
      Tactical.VALID (clasetReplay.REPLAY_TAC grounded) goal
  in
    valid_step goal (record, node) andalso
    same_goals actual expected
  end

fun same_rule_alternatives goal left right =
  length left = length right andalso
  ListPair.allEq
    (fn ((left_record, left_node), (right_record, right_node)) =>
      clasetStep.consumed_of left_record =
        clasetStep.consumed_of right_record andalso
      same_goals (rendered_goals left_node) (rendered_goals right_node)
      andalso valid_open_replay goal (left_record, left_node)
      andalso valid_open_replay goal (right_record, right_node))
    (left, right)

val _ =
  test
    ("rigid replay parameters compare both variable name and type",
     fn () =>
       let
         val rule_variable =
           Term.mk_var ("typed_rigid_parameter", bool_ty)
         val unrelated =
           Term.mk_var ("typed_rigid_parameter", Type.ind)
         val target = Term.mk_var ("typed_rigid_target", bool_ty)
         val theorem = SPEC rule_variable boolTheory.FALSITY
         fun apply parameters =
           clasetReplay.RULE_TAC
             {theorem = theorem, elim = false, consumed = NONE,
              parameters = parameters, eigenvariables = [[]]}
             ([], target) (Context.snapshot())
         val accepted =
           case total apply [rule_variable] of
               SOME ([([], child)], _) => Term.aconv child boolSyntax.F
             | _ => false
         val rejected =
           (ignore (apply [unrelated]); false)
           handle HOL_ERR _ => true
                | _ => false
       in
         accepted andalso rejected
       end)

val _ =
  test
    ("rule_step uses standard children while blast keeps prefixes intact",
     fn () =>
       let
         val schema = Term.mk_var ("bounded_intro_schema", bool_ty)
         val atom = Term.mk_var ("bounded_intro_atom", bool_ty)
         val target = boolSyntax.mk_imp (atom, atom)
         val theorem = GEN schema (DISCH schema (ASSUME schema))
         val goal = ([], target)
         val cs = clasetLib.empty_cs
         val specification = {theorem = theorem, elim = false}
         val selected =
           {theorem = theorem, elim = false, major = NONE}
         fun input () = (clasetGoal.from_goal goal, 1)
         val variants =
           exact_rule_api_variants cs specification selected input
         val standard =
           drain_exact
             (clasetStep.rule_step traceUtil.silent
               {theorem = theorem, elim = false,
                mode = clasetUnify.Match} (input ()))
         val (ordinary_children, ordinary_validation) =
           clasetReplay.RULE_TAC
              {theorem = SPEC target theorem, elim = false,
               consumed = NONE, parameters = [],
              eigenvariables = [[]]} goal (Context.snapshot())

         fun exact result =
           case result of
               [(record, node)] =>
                 same_goals (rendered_goals node) [([], target)]
                 andalso clasetGoal.replay_length node = 1
                 andalso valid_open_replay goal (record, node)
             | _ => false
       in
         List.all exact variants andalso
         (case standard of
              [(record, node)] =>
                same_goals (rendered_goals node) [([atom], atom)]
                andalso valid_open_replay goal (record, node)
            | _ => false) andalso
         same_goals ordinary_children [([atom], atom)] andalso
         let val result = ordinary_validation [ASSUME atom]
         in Term.aconv (concl result) target end
       end)

val _ =
  test
    ("rule_step agrees with blast on plain intro and elim rules",
     fn () =>
       let
         val p = Term.mk_var ("rule_step_diff_p", bool_ty)
         val q = Term.mk_var ("rule_step_diff_q", bool_ty)
         val conjunction = boolSyntax.mk_conj (p, q)
         val intro_goal = ([p, q], conjunction)
         val elim_goal = ([p, p], boolSyntax.T)
         val elim_theorem = DISCH p boolTheory.TRUTH

         fun standard theorem elim goal =
           drain_exact
             (clasetStep.rule_step traceUtil.silent
               {theorem = theorem, elim = elim,
                mode = clasetUnify.Unify}
               (clasetGoal.from_goal goal, 1))
         fun blast theorem elim goal =
           drain_exact
             (clasetStep.blast_rule_step clasetLib.empty_cs
               {theorem = theorem, elim = elim}
               (clasetGoal.from_goal goal, 1))

         val standard_intro =
           standard boolTheory.AND_INTRO_THM false intro_goal
         val blast_intro =
           blast boolTheory.AND_INTRO_THM false intro_goal
         val standard_elim = standard elim_theorem true elim_goal
         val blast_elim = blast elim_theorem true elim_goal
       in
         same_rule_alternatives intro_goal standard_intro blast_intro
         andalso
         same_rule_alternatives elim_goal standard_elim blast_elim
         andalso
         map (clasetStep.consumed_of o #1) standard_elim =
           [SOME 1, SOME 2]
       end)

val _ =
  test
    ("exact elim keeps a newly exposed implication intact",
     fn () =>
       let
         val bound = Term.mk_var ("bounded_elim_bound", Type.ind)
         val predicate =
           Term.mk_var
             ("bounded_elim_predicate", Type.ind --> bool_ty)
         val marker =
           Term.mk_var ("bounded_elim_marker", bool_ty)
         val atom = Term.mk_var ("bounded_elim_atom", bool_ty)
         val target = boolSyntax.mk_imp (atom, atom)
         val major =
           boolSyntax.mk_exists
             (bound,
              boolSyntax.mk_conj
                (Term.mk_comb (predicate, bound), marker))
         val goal = ([major], target)
         val variants =
           exact_transition_variants clasetLib.empty_cs
             {theorem = clasetSeedTheory.EXISTS_ELIM_THM,
              elim = true} goal
         val selected =
           drain_exact
             (clasetStep.blast_rule_step_at clasetLib.empty_cs
               {theorem = clasetSeedTheory.EXISTS_ELIM_THM,
                elim = true, major = SOME 1}
               (clasetGoal.from_goal goal, 1))

         fun exact result =
           case result of
               [(record, node)] =>
                 (case rendered_goals node of
                      [(assumptions, conclusion)] =>
                        let
                          fun predicate_assumption assumption =
                            case total boolSyntax.dest_conj assumption of
                                SOME (left, right) =>
                                  let
                                    val (head, arguments) = strip_comb left
                                  in
                                    Term.aconv head predicate andalso
                                    length arguments = 1 andalso
                                    Term.aconv right marker
                                  end
                              | NONE => false
                          val shape =
                            length assumptions = 1 andalso
                            List.exists predicate_assumption assumptions
                            andalso Term.aconv conclusion target
                        in
                          shape andalso
                          clasetStep.consumed_of record = SOME 1 andalso
                          valid_open_replay goal (record, node)
                        end
                    | _ => false)
             | _ => false
       in
         List.all exact (selected :: variants)
       end)

val _ =
  test
    ("exact descriptors follow the canonicalized rule premises",
     fn () =>
       let
         val p = Term.mk_var ("canonical_prefix_p", bool_ty)
         val q = Term.mk_var ("canonical_prefix_q", bool_ty)
         val conjunction = boolSyntax.mk_conj (p, q)
         val raw = DISCH conjunction (ASSUME conjunction)
         val goal = ([p, q], conjunction)
         val variants =
           exact_transition_variants clasetLib.empty_cs
             {theorem = raw, elim = false} goal

         fun exact result =
           case result of
               [(record, node)] =>
                 same_goals (rendered_goals node)
                   [([p, q], p), ([p, q], q)] andalso
                 clasetGoal.replay_length node = 1 andalso
                 valid_open_replay goal (record, node)
             | _ => false
       in
         List.all exact variants
       end)

(* A forward rule discharges every immediate premise from an assumption, so
   with more than one premise the assumptions selected for the earlier
   premises decide the conclusion just as much as the major one does. *)
val forward_object = Type.ind
val forward_a = Term.mk_var ("forward_a", forward_object)
val forward_b = Term.mk_var ("forward_b", forward_object)
val forward_c = Term.mk_var ("forward_c", forward_object)
val forward_d = Term.mk_var ("forward_d", forward_object)
val forward_x = Term.mk_var ("forward_x", forward_object)
val forward_y = Term.mk_var ("forward_y", forward_object)
val forward_z = Term.mk_var ("forward_z", forward_object)
val forward_edge =
  Term.mk_var
    ("forward_edge", forward_object --> forward_object --> bool_ty)
val forward_node =
  Term.mk_var ("forward_node", forward_object --> bool_ty)
val forward_goal_target = Term.mk_var ("forward_goal_target", bool_ty)

fun forward_edge_of source destination =
  Term.list_mk_comb (forward_edge, [source, destination])

fun forward_node_of value = Term.mk_comb (forward_node, value)

fun forward_reach_of value =
  boolSyntax.mk_exists
    (forward_z,
     boolSyntax.mk_conj
       (forward_edge_of value forward_z, forward_node_of forward_z))

(* |- !x y. Edge x y ==> Node y ==> ?z. Edge x z /\ Node z *)
val forward_reach_rule =
  GENL [forward_x, forward_y]
    (DISCH (forward_edge_of forward_x forward_y)
      (DISCH (forward_node_of forward_y)
        (EXISTS (forward_reach_of forward_x, forward_y)
          (CONJ
            (ASSUME (forward_edge_of forward_x forward_y))
            (ASSUME (forward_node_of forward_y))))))

(* The conclusion each alternative adds, once it has been checked to keep
   the assumptions it matched and to replay against the original goal. *)
fun forward_alternatives assumptions =
  let
    val goal = (assumptions, forward_goal_target)
    val results =
      drain_exact
        (clasetStep.forward_rule_step
          {theorem = forward_reach_rule, immediate = NONE,
           mode = clasetUnify.Match}
          (clasetGoal.from_goal goal, 1))
    fun added (record, node) =
      case rendered_goals node of
          [(conclusion :: retained, target)] =>
            if clasetStep.consumed_of record = NONE andalso
               same_goals [(retained, target)] [goal] andalso
               valid_open_replay goal (record, node)
            then SOME conclusion
            else NONE
        | _ => NONE
  in
    map added results
  end

val _ =
  test
    ("forward_rule_step derives every conclusion of a two-premise rule",
     fn () =>
       let
         val alternatives =
           forward_alternatives
             [forward_edge_of forward_a forward_c,
              forward_edge_of forward_b forward_c,
              forward_node_of forward_c]
       in
         length alternatives = 2 andalso
         ListPair.allEq
           (fn (actual, expected) =>
             case actual of
                 SOME conclusion => Term.aconv conclusion expected
               | NONE => false)
           (alternatives,
            [forward_reach_of forward_a, forward_reach_of forward_b])
       end)

val _ =
  test
    ("forward_rule_step drops conclusions the goal already states",
     fn () =>
       let
         val shared =
           forward_alternatives
             [forward_edge_of forward_a forward_c,
              forward_edge_of forward_a forward_d,
              forward_node_of forward_c,
              forward_node_of forward_d]
         val stated =
           forward_alternatives
             [forward_reach_of forward_a,
              forward_edge_of forward_a forward_c,
              forward_node_of forward_c]
       in
         (case shared of
              [SOME conclusion] =>
                Term.aconv conclusion (forward_reach_of forward_a)
            | _ => false) andalso
         List.null stated
       end)

val _ =
  test
    ("budgeted forward scanning reports a candidate cutoff",
     fn () =>
       let
         val assumptions =
           [forward_edge_of forward_a forward_c,
            forward_edge_of forward_b forward_c,
            forward_node_of forward_c]
         val node = clasetGoal.from_goal
           (assumptions, forward_goal_target)
         fun step budget =
           clasetStep.forward_rule_step_budgeted budget
             {theorem = forward_reach_rule, immediate = NONE,
              mode = clasetUnify.Match} (node, 1)
         val limited =
           searchBudget.create
             {candidates = SOME 0, applications = NONE,
              normalization = NONE}
         val cutoff =
           (ignore (seq.cases (step limited)); false)
           handle searchBudget.LimitReached
             (searchBudget.Candidate, used) =>
               #candidates used = 0
         val funded =
           searchBudget.create
             {candidates = SOME 100, applications = NONE,
              normalization = NONE}
         val alternatives = drain_exact (step funded)
       in
         cutoff andalso length alternatives = 2 andalso
         #candidates (searchBudget.usage funded) > 2 andalso
         #applications (searchBudget.usage funded) = 0
       end)

val _ =
  test
    ("a forward scan resumes after small candidate allocations",
     fn () =>
       let
         val assumptions =
           [forward_edge_of forward_a forward_c,
            forward_edge_of forward_b forward_c,
            forward_node_of forward_c]
         val node =
           clasetGoal.from_goal (assumptions, forward_goal_target)
         val budget =
           searchBudget.create
             {candidates = SOME 1, applications = NONE,
              normalization = NONE}
         val cursor =
           clasetStep.forward_rule_step_budgeted budget
             {theorem = forward_reach_rule, immediate = NONE,
              mode = clasetUnify.Match} (node, 1)
         val reference_budget = searchBudget.unbounded ()
         val reference =
           drain_exact
             (clasetStep.forward_rule_step_budgeted reference_budget
               {theorem = forward_reach_rule, immediate = NONE,
                mode = clasetUnify.Match} (node, 1))
         val initial_cutoff =
           case clasetStep.next_forward cursor of
               clasetStep.ForwardScanLimit
                 {kind = searchBudget.Candidate, cursor = _, usage} =>
                   #candidates usage = 1
             | _ => false
         fun resume 0 _ _ = NONE
           | resume turns current reversed =
               (case clasetStep.next_forward current of
                    clasetStep.ForwardYield {result, rest} =>
                      resume turns rest (result :: reversed)
                  | clasetStep.ForwardExhausted =>
                      SOME (List.rev reversed)
                  | clasetStep.ForwardScanLimit {cursor, ...} =>
                      (searchBudget.extend budget
                         searchBudget.Candidate 1;
                       resume (turns - 1) cursor reversed))
         fun added (_, result) =
           case rendered_goals result of
               [(conclusion :: _, _)] => SOME conclusion
             | _ => NONE
       in
         case resume 100 cursor [] of
             SOME results =>
               initial_cutoff andalso ListPair.allEq
                 (fn (left, right) =>
                   case (left, right) of
                       (SOME actual, SOME expected) =>
                         Term.aconv actual expected
                     | _ => false)
                 (map added results, map added reference) andalso
               length results = 2 andalso
               #candidates (searchBudget.usage budget) =
               #candidates (searchBudget.usage reference_budget)
           | NONE => false
       end)

val forward_guard =
  Term.mk_var ("forward_guard", forward_object --> bool_ty)
fun forward_guard_of value = Term.mk_comb (forward_guard, value)
val forward_w = Term.mk_var ("forward_w", forward_object)
fun forward_product_of source guarded =
  boolSyntax.mk_exists
    (forward_w,
     boolSyntax.mk_conj
       (boolSyntax.mk_conj
          (forward_edge_of source forward_w,
           forward_node_of forward_w),
        forward_guard_of guarded))
val forward_product_rule =
  GENL [forward_x, forward_y, forward_z]
    (DISCH (forward_edge_of forward_x forward_y)
      (DISCH (forward_node_of forward_y)
        (DISCH (forward_guard_of forward_z)
          (EXISTS
            (forward_product_of forward_x forward_z, forward_y)
            (CONJ
              (CONJ
                (ASSUME (forward_edge_of forward_x forward_y))
                (ASSUME (forward_node_of forward_y)))
              (ASSUME (forward_guard_of forward_z)))))))

val _ =
  test
    ("a forward cursor resumes a three-premise Cartesian scan",
     fn () =>
       let
         val assumptions =
           [forward_edge_of forward_a forward_c,
            forward_edge_of forward_b forward_c,
            forward_node_of forward_c,
            forward_guard_of forward_c,
            forward_guard_of forward_d]
         val goal = (assumptions, forward_goal_target)
         val node = clasetGoal.from_goal goal
         fun scan budget =
           clasetStep.forward_rule_step_budgeted budget
             {theorem = forward_product_rule, immediate = NONE,
              mode = clasetUnify.Match} (node, 1)
         val small =
           searchBudget.create
             {candidates = SOME 3, applications = NONE,
              normalization = NONE}
         val large = searchBudget.unbounded ()
         val reference = drain_exact (scan large)
         fun resume 0 _ _ = NONE
           | resume turns cursor reversed =
               (case clasetStep.next_forward cursor of
                    clasetStep.ForwardYield {result, rest} =>
                      resume turns rest (result :: reversed)
                  | clasetStep.ForwardExhausted =>
                      SOME (List.rev reversed)
                  | clasetStep.ForwardScanLimit {cursor, ...} =>
                      (searchBudget.extend small
                         searchBudget.Candidate 3;
                       resume (turns - 1) cursor reversed))
         fun consequence (_, result) =
           case rendered_goals result of
               [(added :: retained, target)] =>
                 if same_goals [(retained, target)] [goal] then
                   SOME added
                 else NONE
             | _ => NONE
       in
         case resume 100 (scan small) [] of
             SOME results =>
               length results > 4 andalso
               ListPair.allEq
                 (fn (SOME left, SOME right) => Term.aconv left right
                   | _ => false)
                 (map consequence results, map consequence reference)
               andalso
               List.all (valid_open_replay goal) results andalso
               #candidates (searchBudget.usage small) =
               #candidates (searchBudget.usage large)
           | NONE => false
       end)

val _ =
  test
    ("a new forward cursor sees a newly available premise",
     fn () =>
       let
         val edge = forward_edge_of forward_a forward_c
         val without_premise = forward_alternatives [edge]
         val with_premise =
           forward_alternatives
             [edge, forward_node_of forward_c]
       in
         null without_premise andalso
         (case with_premise of
              [SOME conclusion] =>
                Term.aconv conclusion (forward_reach_of forward_a)
            | _ => false)
       end)

val _ =
  test
    ("forward duplicates use the candidate's arriving substitution",
     fn () =>
       let
         val a = Term.mk_var ("forward_arriving_a", forward_object)
         val b = Term.mk_var ("forward_arriving_b", forward_object)
         val x = Term.mk_var ("forward_arriving_x", forward_object)
         val p = Term.mk_var
           ("forward_arriving_p", forward_object --> bool_ty)
         val r = Term.mk_var
           ("forward_arriving_r", forward_object --> bool_ty)
         fun app head argument = Term.mk_comb (head, argument)
         val px = app p x
         val rx = app r x
         val rule =
           GEN x
             (DISCH px
               (DISCH rx
                 (CONJ (ASSUME px) (ASSUME rx))))
         val constant_rule =
           GEN x (DISCH px (DISCH rx boolTheory.TRUTH))
         val base = the_store
           (clasetMeta.register_eigen b
             (the_store
               (clasetMeta.register_eigen a clasetMeta.empty)))
         val (meta, store) =
           clasetMeta.new_meta
             {allow = [a, b], ty = forward_object} base
         val known =
           boolSyntax.mk_conj (app r meta, app p meta)
         val premise = [app p meta, app r a]
         fun results_for theorem assumptions =
           let
             val node = clasetGoal.create
               {goals =
                  [{params = [a, b], asl = assumptions,
                    w = forward_goal_target}],
                store = store, level = 0}
           in
             drain_exact
               (clasetStep.forward_rule_step
                 {theorem = theorem, immediate = NONE,
                  mode = clasetUnify.Unify} (node, 1))
           end
         fun results assumptions = results_for rule assumptions
         val plain = results premise
         val duplicate = results (premise @ [known])
         val siblings =
           results [app p meta, app r meta, app r a]
         fun is_bound (_, next) =
           Term.aconv
             (clasetMeta.norm (clasetGoal.store next) meta) a
         fun added (_, next) =
           hd (#asl (clasetGoal.goal_at next 1))
         val unbound = List.filter (not o is_bound) siblings
         val bound = List.filter is_bound siblings
         val constant =
           results_for constant_rule
             [app p meta, app r a, app r b]
         fun binds value (_, next) =
           Term.aconv
             (clasetMeta.norm (clasetGoal.store next) meta)
             value
         fun overlaps_unbound (result as (_, next)) =
           let val arriving = clasetGoal.store next
           in
             List.exists
               (fn previous =>
                 Term.aconv
                   (clasetMeta.norm arriving (added previous))
                   (clasetMeta.norm arriving (added result)))
               unbound
           end
         fun duplicate_after_binding (_, next) =
           let
             val next_store = clasetGoal.store next
             val {asl, ...} = clasetGoal.goal_at next 1
           in
             Term.aconv (clasetMeta.norm next_store meta) a andalso
             Term.aconv
               (clasetMeta.norm next_store (hd asl))
               (clasetMeta.norm next_store known)
           end
       in
         List.exists duplicate_after_binding plain andalso
         not (List.exists duplicate_after_binding duplicate) andalso
         List.exists overlaps_unbound bound andalso
         List.exists (binds a) constant andalso
         List.exists (binds b) constant
       end)

val _ =
  test
    ("exact EXISTS elim preserves an eta-reduced major assumption",
     fn () =>
       let
         val bound = Term.mk_var ("eta_major_bound", Type.ind)
         val predicate =
           Term.mk_var
             ("eta_major_predicate", Type.ind --> bool_ty)
         val target = Term.mk_var ("eta_major_target", bool_ty)
         val major =
           boolSyntax.mk_exists
             (bound, Term.mk_comb (predicate, bound))
         val goal = ([major], target)
         val variants =
           exact_transition_variants clasetLib.empty_cs
             {theorem = clasetSeedTheory.EXISTS_ELIM_THM,
              elim = true} goal
         val selected =
           drain_exact
             (clasetStep.blast_rule_step_at clasetLib.empty_cs
               {theorem = clasetSeedTheory.EXISTS_ELIM_THM,
                elim = true, major = SOME 1}
               (clasetGoal.from_goal goal, 1))

         fun exact result =
           case result of
               [(record, node)] =>
                 (case rendered_goals node of
                      [([assumption], conclusion)] =>
                        let
                          val (head, arguments) = strip_comb assumption
                        in
                          Term.aconv head predicate andalso
                          length arguments = 1 andalso
                          Term.aconv conclusion target andalso
                          clasetStep.consumed_of record = SOME 1 andalso
                          valid_open_replay goal (record, node)
                        end
                    | _ => false)
             | _ => false
       in
         List.all exact (selected :: variants)
       end)

val _ =
  test
    ("exact EXISTS elim instantiates an engine-meta major soundly",
     fn () =>
       let
         val target = Term.mk_var ("meta_major_target", bool_ty)
         val (major, store) =
           clasetMeta.new_meta
             {allow = [], ty = bool_ty} clasetMeta.empty
         val node =
           clasetGoal.create
             {goals = [{params = [], asl = [major], w = target}],
              store = store, level = 0}
         val specification =
           {theorem = clasetSeedTheory.EXISTS_ELIM_THM,
            elim = true}
         val ordinary =
           drain_exact
             (clasetStep.blast_rule_step clasetLib.empty_cs
               specification (node, 1))
         val selected =
           drain_exact
             (clasetStep.blast_rule_step_at clasetLib.empty_cs
               {theorem = clasetSeedTheory.EXISTS_ELIM_THM,
                elim = true, major = SOME 1} (node, 1))

         fun exact result =
           case result of
               [(record, next)] =>
                 let
                   val final_store = clasetGoal.store next
                   val materialized_major =
                     clasetMeta.norm final_store major
                   val materialized_goal =
                     ([materialized_major], target)
                   val expected = rendered_goals next
                   val (direct, _) =
                     Tactical.VALID
                       (fn _ => fn _ =>
                         (expected, clasetStep.validation_of record))
                       materialized_goal
                   val ground_store = clasetMeta.ground final_store
                   val grounded_goal =
                     ([clasetMeta.norm ground_store major], target)
                   val grounded_node =
                     clasetGoal.set_store ground_store next
                   val grounded =
                     clasetReplay.ground final_store
                       (clasetGoal.replay next)
                   val (replayed, _) =
                     Tactical.VALID
                       (clasetReplay.REPLAY_TAC grounded) grounded_goal
                 in
                   not (Term.aconv materialized_major major) andalso
                   length expected = 1 andalso
                   same_goals direct expected andalso
                   same_goals replayed (rendered_goals grounded_node)
                 end
             | _ => false
       in
         List.all exact [ordinary, selected]
       end)

val _ =
  test
    ("exact quantified major uses the final engine store before ASSUME",
     fn () =>
       let
         val parameter =
           Term.mk_var ("quantified_major_x", Type.ind)
         val bound =
           Term.mk_var ("quantified_major_x", Type.ind)
         val predicate =
           Term.mk_var
             ("quantified_major_R",
              Type.ind --> Type.ind --> bool_ty)
         val marker =
           Term.mk_var
             ("quantified_major_S", Type.ind --> bool_ty)
         val (meta, store0) =
           clasetMeta.new_meta
             {allow = [parameter], ty = Type.ind}
             clasetMeta.empty
         val store =
           valOf (clasetMeta.bind (meta, parameter) store0)
         val quantified =
           boolSyntax.mk_forall
             (bound,
              Term.list_mk_comb (predicate, [meta, bound]))
         val target = Term.mk_comb (marker, parameter)
         val major = boolSyntax.mk_conj (quantified, target)
         val normalized_major = clasetMeta.norm store major
         val source_major =
           Term.subst [{redex = meta, residue = parameter}] major
         val specification =
           {theorem = clasetSeedTheory.CONJ_ELIM_THM,
            elim = true, major = SOME 2}
         fun input () =
           (clasetGoal.create
              {goals =
                 [{params = [parameter], asl = [major, major],
                   w = target}],
               store = store, level = 0},
            1)
         val plain =
           {theorem = clasetSeedTheory.CONJ_ELIM_THM,
            elim = true}
         val all_variants =
           [drain_exact
              (clasetStep.blast_rule_step clasetLib.empty_cs
                plain (input ()))]
         val selected_variants =
           [drain_exact
              (clasetStep.blast_rule_step_at clasetLib.empty_cs
                specification (input ()))]
         val invalid =
           drain_exact
             (clasetStep.blast_rule_step_at clasetLib.empty_cs
               {theorem = clasetSeedTheory.CONJ_ELIM_THM,
                elim = true, major = SOME 3} (input ()))

         fun exact position result =
           case result of
               [(record, next)] =>
                 let
                   val proof =
                     clasetStep.validation_of record [ASSUME target]
                 in
                   clasetStep.consumed_of record = SOME position andalso
                   Term.aconv (concl proof) target andalso
                   aconv_list (hyp proof) [source_major]
                 end
             | _ => false
         fun all_exact results =
           ListPair.allEq
             (fn (result, position) => exact position [result])
             (results, [1, 2])
       in
         Term.aconv
           (clasetMeta.norm (clasetGoal.store (#1 (input ()))) major)
           normalized_major andalso
         Term.aconv (List.nth ([major, major], 1)) major andalso
         List.all all_exact all_variants andalso
         List.all (exact 2) selected_variants andalso null invalid
       end)

val _ =
  test
    ("exact elim replay avoids capture in its selected major",
     fn () =>
       let
         val parameter =
           Term.mk_var ("replay_collision_x", Type.ind)
         val bound =
           Term.mk_var ("replay_collision_x", Type.ind)
         val predicate =
           Term.mk_var
             ("replay_collision_R",
              Type.ind --> Type.ind --> bool_ty)
         val marker =
           Term.mk_var
             ("replay_collision_S", Type.ind --> bool_ty)
         val (meta, store0) =
           clasetMeta.new_meta
             {allow = [parameter], ty = Type.ind}
             clasetMeta.empty
         val store =
           valOf (clasetMeta.bind (meta, parameter) store0)
         val quantified =
           boolSyntax.mk_forall
             (bound,
              Term.list_mk_comb (predicate, [meta, bound]))
         val target = Term.mk_comb (marker, parameter)
         val engine_major = boolSyntax.mk_conj (quantified, target)
         fun input () =
           clasetGoal.create
             {goals =
                [{params = [parameter], asl = [engine_major],
                  w = target}],
              store = store, level = 0}
         val specification =
           {theorem = clasetSeedTheory.CONJ_ELIM_THM,
            elim = true, major = SOME 1}
         val plain =
           {theorem = clasetSeedTheory.CONJ_ELIM_THM,
            elim = true}
         val variants =
           exact_rule_api_variants clasetLib.empty_cs plain
             specification (fn () => (input (), 1))
         val source_major =
           Term.subst
             [{redex = meta, residue = parameter}] engine_major
         val (source_quantified, source_target) =
           boolSyntax.dest_conj source_major
         val expected_quantified = beta_eta_term source_quantified
         val captured_quantified =
           boolSyntax.mk_forall
             (bound,
              Term.list_mk_comb (predicate, [bound, bound]))
         fun exact result =
           case result of
               [(record, next)] =>
                 let
                   val script =
                     clasetReplay.append (clasetReplay.empty 1) record
                   val grounded =
                     clasetReplay.ground (clasetGoal.store next) script
                 in
                   case clasetReplay.replay_in (Context.snapshot ()) grounded
                          ([source_major], target) of
                       clasetReplay.Replayed
                         (children as
                            [([actual_target, actual_quantified],
                              child_target)],
                          validation) =>
                         let
                           val theorem = validation [ASSUME child_target]
                         in
                           same_goals children
                             [([source_target, expected_quantified],
                               source_target)] andalso
                           Term.aconv actual_target source_target andalso
                           Term.aconv actual_quantified
                             expected_quantified andalso
                           Term.aconv child_target source_target andalso
                           Term.term_eq (concl theorem) source_target andalso
                           HOLset.equal
                             (Thm.hypset theorem,
                              HOLset.fromList Term.compare [source_major])
                         end
                     | _ => false
                 end
             | _ => false
       in
         not (Term.aconv captured_quantified source_quantified) andalso
         List.all exact variants
       end)

val _ =
  test
    ("exact intro replay avoids capture in its conclusion",
     fn () =>
       let
         val parameter =
           Term.mk_var ("intro_collision_x", Type.ind)
         val bound =
           Term.mk_var ("intro_collision_x", Type.ind)
         val relation =
           Term.mk_var
             ("intro_collision_R",
              Type.ind --> Type.ind --> bool_ty)
         val marker =
           Term.mk_var
             ("intro_collision_S", Type.ind --> bool_ty)
         val (meta, store0) =
           clasetMeta.new_meta
             {allow = [parameter], ty = Type.ind}
             clasetMeta.empty
         val store =
           valOf (clasetMeta.bind (meta, parameter) store0)
         val quantified =
           boolSyntax.mk_forall
             (bound,
              Term.list_mk_comb (relation, [meta, bound]))
         val raw_target =
           boolSyntax.mk_conj
             (quantified, Term.mk_comb (marker, parameter))
         val source_target = exact_source_term store raw_target
         val (source_left, source_right) =
           boolSyntax.dest_conj source_target
         val expected_left = normalize_exact_term source_left
         val expected_right = normalize_exact_term source_right
         val plain =
           {theorem = boolTheory.AND_INTRO_THM, elim = false}
         val selected =
           {theorem = boolTheory.AND_INTRO_THM, elim = false,
            major = NONE}
         fun input () =
           (clasetGoal.create
              {goals =
                 [{params = [parameter], asl = [], w = raw_target}],
               store = store, level = 0},
            1)
         val variants =
           exact_rule_api_variants clasetLib.empty_cs plain selected
             input

         fun exact result =
           case result of
               [(record, next)] =>
                 let
                   val script =
                     clasetReplay.append (clasetReplay.empty 1) record
                   val grounded =
                     clasetReplay.ground (clasetGoal.store next) script
                 in
                   case clasetReplay.replay_in (Context.snapshot ()) grounded
                          ([], source_target) of
                       clasetReplay.Replayed
                         (children as
                            [([], actual_left), ([], actual_right)],
                          validation) =>
                         let
                           val theorem =
                             validation
                               [ASSUME actual_left,
                                ASSUME actual_right]
                           val children_ok =
                             same_goals children
                               [([], expected_left), ([], expected_right)]
                           val conclusion_ok =
                             Term.term_eq (concl theorem) source_target
                           val hypotheses_ok =
                             HOLset.equal
                               (Thm.hypset theorem,
                                HOLset.fromList Term.compare
                                  [expected_left, expected_right])
                         in
                           children_ok andalso conclusion_ok andalso
                           hypotheses_ok
                         end
                     | _ => false
                 end
             | _ => false
       in
         not (Term.aconv quantified source_left) andalso
         List.all exact variants
       end)

val _ =
  test
    ("exact elim replay repairs a conclusion with an exact major",
     fn () =>
       let
         val parameter =
           Term.mk_var ("elim_target_collision_x", Type.ind)
         val bound =
           Term.mk_var ("elim_target_collision_x", Type.ind)
         val relation =
           Term.mk_var
             ("elim_target_collision_R",
              Type.ind --> Type.ind --> bool_ty)
         val left =
           Term.mk_var ("elim_target_collision_p", bool_ty)
         val right =
           Term.mk_var ("elim_target_collision_q", bool_ty)
         val major = boolSyntax.mk_conj (left, right)
         val (meta, store0) =
           clasetMeta.new_meta
             {allow = [parameter], ty = Type.ind}
             clasetMeta.empty
         val store =
           valOf (clasetMeta.bind (meta, parameter) store0)
         val raw_target =
           boolSyntax.mk_forall
             (bound,
              Term.list_mk_comb (relation, [meta, bound]))
         val source_target = exact_source_term store raw_target
         val expected_child_target =
           normalize_exact_term source_target
         val plain =
           {theorem = clasetSeedTheory.CONJ_ELIM_THM,
            elim = true}
         val selected =
           {theorem = clasetSeedTheory.CONJ_ELIM_THM,
            elim = true, major = SOME 1}
         fun input () =
           (clasetGoal.create
              {goals =
                 [{params = [parameter], asl = [major],
                   w = raw_target}],
               store = store, level = 0},
            1)
         val variants =
           exact_rule_api_variants clasetLib.empty_cs plain selected
             input

         fun exact result =
           case result of
               [(record, next)] =>
                 let
                   val script =
                     clasetReplay.append (clasetReplay.empty 1) record
                   val grounded =
                     clasetReplay.ground (clasetGoal.store next) script
                 in
                   case clasetReplay.replay_in (Context.snapshot ()) grounded
                          ([major], source_target) of
                       clasetReplay.Replayed
                         (children as
                            [([actual_right, actual_left],
                              actual_target)],
                          validation) =>
                         let
                           val theorem =
                             validation [ASSUME actual_target]
                         in
                           same_goals children
                             [([right, left], expected_child_target)]
                           andalso Term.aconv actual_left left
                           andalso Term.aconv actual_right right
                           andalso
                           Term.term_eq (concl theorem) source_target
                           andalso
                           HOLset.equal
                              (Thm.hypset theorem,
                               HOLset.fromList Term.compare
                                [major, expected_child_target])
                         end
                     | _ => false
                 end
             | _ => false
       in
         not (Term.aconv raw_target source_target) andalso
         List.all exact variants
       end)

val _ =
  test
    ("exact intro replay avoids capture confined to a minor",
     fn () =>
       let
         val parameter =
           Term.mk_var ("minor_collision_x", Type.ind)
         val schema =
           Term.mk_var ("minor_collision_schema", bool_ty)
         val bound =
           Term.mk_var ("minor_collision_x", Type.ind)
         val theorem =
           GEN schema (DISCH schema boolTheory.TRUTH)
         val plain = {theorem = theorem, elim = false}
         val selected =
           {theorem = theorem, elim = false, major = NONE}
         val relation =
           Term.mk_var
             ("minor_collision_R",
              Type.ind --> Type.ind --> bool_ty)
         val (dependency, initial_store) =
           clasetMeta.new_meta
             {allow = [parameter], ty = Type.ind}
             clasetMeta.empty
         val raw_minor =
           boolSyntax.mk_forall
             (bound,
              Term.list_mk_comb (relation, [dependency, bound]))
         val source_minor =
           Term.subst
             [{redex = dependency, residue = parameter}] raw_minor
         val expected_minor = beta_eta_term source_minor
         val captured_minor =
           boolSyntax.mk_forall
             (bound,
              Term.list_mk_comb (relation, [bound, bound]))
         fun input () =
           (clasetGoal.create
              {goals =
                 [{params = [parameter], asl = [], w = boolSyntax.T}],
               store = initial_store, level = 0},
            1)
         val variants =
           exact_rule_api_variants clasetLib.empty_cs plain selected
             input

         fun exact result =
           case result of
               [(record, next)] =>
                 (case #terms (clasetStep.created_of record) of
                      [created] =>
                        let
                          val store_with_minor =
                            the_store
                              (clasetMeta.bind (created, raw_minor)
                                (clasetGoal.store next))
                          val replay_store =
                            the_store
                              (clasetMeta.bind
                                (dependency, parameter) store_with_minor)
                          val created_minor =
                            #w (the_singleton (clasetGoal.goals next))
                          val script =
                            clasetReplay.append
                              (clasetReplay.empty 1) record
                          val grounded =
                            clasetReplay.ground replay_store script
                        in
                          case clasetReplay.replay_in (Context.snapshot ())
                                 grounded
                                 ([], boolSyntax.T) of
                              clasetReplay.Replayed
                                (children as
                                   [([], actual_minor)],
                                 validation) =>
                                let
                                  val result =
                                    validation [ASSUME actual_minor]
                                in
                                  Term.aconv created_minor created andalso
                                  same_goals children
                                    [([], expected_minor)] andalso
                                  Term.aconv actual_minor
                                    expected_minor andalso
                                  Term.term_eq (concl result)
                                    boolSyntax.T andalso
                                  HOLset.equal
                                     (Thm.hypset result,
                                      HOLset.fromList Term.compare
                                       [expected_minor])
                                end
                            | _ => false
                        end
                    | _ => false)
             | _ => false
       in
         not (Term.aconv raw_minor source_minor) andalso
         not (Term.aconv captured_minor source_minor) andalso
         List.all exact variants
       end)

val _ =
  test
    ("dest-generated elim keeps a newly exposed implication intact",
     fn () =>
       let
         val left = Term.mk_var ("bounded_dest_left", bool_ty)
         val right = Term.mk_var ("bounded_dest_right", bool_ty)
         val atom = Term.mk_var ("bounded_dest_atom", bool_ty)
         val target = boolSyntax.mk_imp (atom, atom)
         val conjunction = boolSyntax.mk_conj (left, right)
         val original =
           DISCH conjunction
             (CONJUNCT1 (ASSUME conjunction))
         val specification =
           {kind = clasetRules.Dest, safe = true, prio = NONE}
         val {rl = (generated, _), ...} =
           clasetRules.ext_info specification original
         val cs =
           clasetLib.add_sdests
             [("bounded-dest-generated", original)]
             clasetLib.empty_cs
         val goal = ([conjunction], target)
         val variants =
           exact_transition_variants cs
             {theorem = generated, elim = true} goal

         fun exact result =
           case result of
               [(record, node)] =>
                 same_goals (rendered_goals node)
                   [([left], target)]
                 andalso
                 (case clasetStep.kind_of record of
                      clasetStep.RuleApplication
                        {variant = clasetStep.MakeElim, ...} => true
                    | _ => false)
                 andalso valid_open_replay goal (record, node)
             | _ => false
       in
         List.all exact variants
       end)

val _ =
  test
    ("measured exact rules preserve intro and elim sequence order",
     fn () =>
       let
         val p = Term.mk_var ("measured_exact_p", bool_ty)
         val q = Term.mk_var ("measured_exact_q", bool_ty)
         val r = Term.mk_var ("measured_exact_r", bool_ty)
         val conjunction = boolSyntax.mk_conj (p, q)
         val intro_goal = ([p, q], conjunction)
         val elim_goal = ([r, conjunction, conjunction], p)
         val cs =
           clasetLib.add_selims
             [("measured-exact-and-elim",
               clasetSeedTheory.CONJ_ELIM_THM)]
             clasetLib.empty_cs

         val intro_results =
           drain_exact
             (clasetStep.blast_rule_step cs
               {theorem = boolTheory.AND_INTRO_THM, elim = false}
               (clasetGoal.from_goal intro_goal, 1))
         val elim_specification =
           {theorem = clasetSeedTheory.CONJ_ELIM_THM, elim = true}
         val ordinary_elims =
           drain_exact
             (clasetStep.blast_rule_step cs elim_specification
               (clasetGoal.from_goal elim_goal, 1))
       in
         length intro_results = 1 andalso
         List.all (valid_open_replay intro_goal) intro_results andalso
         length ordinary_elims = 2 andalso
         map (clasetStep.consumed_of o #1) ordinary_elims =
           [SOME 2, SOME 3] andalso
         List.all (valid_open_replay elim_goal) ordinary_elims
       end)

val _ =
  test
    ("exact elimination premises preserve parent eigenparameters",
     fn () =>
       let
         val outer = Term.mk_var ("x", Type.ind)
         val witness = Term.mk_var ("y", Type.ind)
         val label =
           Term.mk_var ("capture_label", Type.ind --> bool_ty)
         val relation =
           Term.mk_var
             ("capture_relation",
              Type.ind --> Type.ind --> bool_ty)
         fun label_app argument = Term.mk_comb (label, argument)
         fun relation_app left right =
           Term.list_mk_comb (relation, [left, right])
         val major =
           boolSyntax.mk_exists
             (witness,
              boolSyntax.mk_conj
                (label_app witness, relation_app outer witness))
         val store =
           valOf (clasetMeta.register_eigen outer clasetMeta.empty)
         val node =
           clasetGoal.create
             {goals =
                [{params = [outer], asl = [major], w = boolSyntax.F}],
              store = store, level = 0}
         val transition =
           seq.cases
             (clasetStep.blast_rule_step clasetLib.empty_cs
               {theorem = clasetSeedTheory.EXISTS_ELIM_THM,
                elim = true} (node, 1))
       in
         case transition of
             NONE => false
           | SOME ((record, next), _) =>
               let
                 val child = the_singleton (clasetGoal.goals next)
                 val fresh = List.nth (#params child, 1)
                 val expected =
                   boolSyntax.mk_conj
                     (label_app fresh, relation_app outer fresh)
               in
                 not (Term.aconv outer fresh) andalso
                 List.exists (fn assumption =>
                   Term.aconv assumption expected) (#asl child) andalso
                 clasetStep.consumed_of record = SOME 1 andalso
                 valid_step ([major], boolSyntax.F) (record, next)
               end
       end)

(* A rule parameter that no hypothesis pins is instantiable wherever it
   occurs; one occurring in a premise alone is left as a metavariable. *)
fun meta_applied_to argument assumption =
  case Lib.total Term.dest_comb assumption of
      SOME (head, arg) =>
        clasetMeta.is_meta head andalso Term.aconv arg argument
    | NONE => false

val _ =
  test
    ("exact two-binder replay preserves fresh order and collisions",
     fn () =>
       let
         val x = Term.mk_var ("static_eigen_x", Type.ind)
         val y = Term.mk_var ("static_eigen_x", bool_ty)
         val sibling_x = Term.variant [x] x
         val p =
           Term.mk_var ("static_eigen_P", Type.ind --> bool_ty)
         val q =
           Term.mk_var ("static_eigen_Q", bool_ty --> bool_ty)
         val premise =
           boolSyntax.list_mk_forall
             ([x, y],
              boolSyntax.mk_imp
                (Term.mk_comb (p, x),
                 boolSyntax.mk_imp (Term.mk_comb (q, y), boolSyntax.T)))
         val theorem = DISCH premise boolTheory.TRUTH
         val node =
           clasetGoal.create
             {goals =
                [{params = [x, sibling_x], asl = [], w = boolSyntax.T}],
              store = clasetMeta.empty, level = 0}
       in
         case seq.cases
           (clasetStep.blast_rule_step_at clasetLib.empty_cs
             {theorem = theorem, elim = false, major = NONE} (node, 1))
         of
             SOME ((record, next), _) =>
               (case clasetGoal.goals next of
                    {params, asl, w} :: _ =>
                      let
                        val fresh_x = List.nth (params, 2)
                        val fresh_y = List.nth (params, 3)
                        val names =
                          [fst (Term.dest_var fresh_x),
                           fst (Term.dest_var fresh_y)]
                      in
                        length params = 4 andalso
                        not (Term.aconv fresh_x x) andalso
                        not (Term.aconv fresh_x sibling_x) andalso
                        type_of fresh_x = Type.ind andalso
                        type_of fresh_y = bool_ty andalso
                        (* [P] and [Q] occur in the rule's premise only,
                           so matching its conclusion leaves them
                           unresolved.  What the rule fixes is the
                           argument each is applied to, and their
                           order. *)
                        (case asl of
                             [first, second] =>
                               meta_applied_to fresh_y first andalso
                               meta_applied_to fresh_x second andalso
                               not (clasetMeta.same_meta
                                      (Term.rator first)
                                      (Term.rator second))
                           | _ => false) andalso
                        Term.aconv w boolSyntax.T andalso
                        clasetStep.eigenvariables_of record = names andalso
                        valid_open_replay ([], boolSyntax.T) (record, next)
                      end
                  | _ => false)
           | NONE => false
       end)

val _ =
  test
    ("measured exact-rule observations and outputs are deterministic",
     fn () =>
       let
         val p = Term.mk_var ("measured_deterministic_p", bool_ty)
         val q = Term.mk_var ("measured_deterministic_q", bool_ty)
         val goal = ([p, q], boolSyntax.mk_conj (p, q))
         fun run () =
           map
             (fn (record, node) =>
               (clasetStep.consumed_of record,
                rendered_goals node,
                clasetReplay.to_string (clasetGoal.replay node)))
             (drain_exact
               (clasetStep.blast_rule_step
                 clasetLib.empty_cs
                 {theorem = boolTheory.AND_INTRO_THM, elim = false}
                 (clasetGoal.from_goal goal, 1)))
         val views1 = run ()
         val views2 = run ()
         fun same_view ((consumed1, goals1, replay1),
                        (consumed2, goals2, replay2)) =
           consumed1 = consumed2 andalso
           same_goals goals1 goals2 andalso replay1 = replay2
       in
         length views1 = length views2 andalso
         ListPair.allEq same_view (views1, views2)
       end)

val _ =
  test
    ("match-mode derivation grounds and replays without search",
     fn () =>
       let
         val conjunction = boolSyntax.mk_conj (phase1_pa, phase1_qa)
         val original = ([phase1_pa, phase1_qa], conjunction)
         val cs =
           clasetLib.add_sintros
             [("replay-and", boolTheory.AND_INTRO_THM)]
             clasetLib.empty_cs
         val (rule_record, after_rule) =
           first_node_step safe_step cs
             (clasetGoal.from_goal original) 1
         val (_, after_left) =
           first_node_step safe_step cs after_rule 1
         val (_, solved) =
           first_node_step safe_step cs after_left 1
       in
         (case clasetStep.kind_of rule_record of
              clasetStep.RuleApplication
                {original = theorem, variant = clasetStep.Plain,
                 elim = false, ...} =>
                Term.aconv (concl theorem)
                  (concl boolTheory.AND_INTRO_THM)
            | _ => false) andalso
         clasetGoal.replay_length solved = 3 andalso
         valid_grounded_replay original solved
       end)

val _ =
  test
    ("unify-mode witness is grounded before zero-search replay",
     fn () =>
       let
         val witness = Term.mk_var ("replay_witness", Type.ind)
         val constant = boolSyntax.mk_arb Type.ind
         val predicate =
           Term.mk_var ("replay_predicate", Type.ind --> Type.bool)
         val fact = mk_comb (predicate, constant)
         val target =
           boolSyntax.mk_exists (witness, mk_comb (predicate, witness))
         val original = ([fact], target)
         val cs =
           clasetLib.add_intros
             [("replay-exists", clasetSeedTheory.EXISTS_INTRO_THM)]
             clasetLib.empty_cs
         val (_, after_rule) =
           first_node_step clasetStep.unsafe_step cs
             (clasetGoal.from_goal original) 1
         val (_, solved) =
           first_node_step clasetStep.inst0_step cs after_rule 1
       in
         clasetGoal.replay_length solved = 2 andalso
         valid_grounded_replay original solved
       end)

val _ =
  test
    ("grounded scripts and substitutions are deterministic",
     fn () =>
       let
         val (tymeta, store0) =
           clasetMeta.new_tymeta clasetMeta.empty
         val (meta, store1) =
           clasetMeta.new_meta {allow = [], ty = tymeta} store0
         val validation = fn [] => boolTheory.TRUTH
           | _ => raise Fail "bad deterministic validation"
         val record =
           clasetReplay.make_record
             {kind = clasetReplay.Assumption 1, target = 1,
              consumed = SOME 1,
              created = {terms = [meta], types = [tymeta]},
              eigenvariables = [], validation = validation,
              action = clasetReplay.assumption_action 1,
              children = []}
         val script =
           clasetReplay.append (clasetReplay.empty 1) record
         val first = clasetReplay.ground store1 script
         val second = clasetReplay.ground store1 script
         val first_subst =
           clasetMeta.collapse (clasetReplay.grounded_store first)
         val second_subst =
           clasetMeta.collapse (clasetReplay.grounded_store second)
       in
         clasetReplay.grounded_to_string first =
           clasetReplay.grounded_to_string second andalso
         type_subst_eq (#1 first_subst) (#1 second_subst) andalso
         term_subst_eq (#2 first_subst) (#2 second_subst)
       end)

val _ =
  test
    ("assumption replay recovers only through its recorded action",
     fn () =>
       let
         val goal = ([phase1_qa, phase1_pa], phase1_pa)
         val strict =
           clasetReplay.ASSUMPTION_TAC clasetMeta.empty 1
         val recovered =
           clasetReplay.assumption_action 1 clasetMeta.empty
         val strict_fails =
           (ignore (Tactical.VALID strict goal); false)
           handle HOL_ERR _ => true
         val (residues, validate_recovered) = Tactical.VALID recovered goal
         val bound = Term.mk_var ("replay_assumption_bound", Type.bool)
         val redex = mk_comb (mk_abs (bound, bound), phase1_pa)
         val preferred_goal = ([phase1_pa, redex], phase1_pa)
         val (preferred_residues, validate_preferred) =
           clasetReplay.assumption_action 2 clasetMeta.empty
             preferred_goal (Context.snapshot ())
         val rejects_children =
           (ignore (validate_preferred [ASSUME phase1_pa]); false)
           handle HOL_ERR _ => true
         fun uses theorem assumption =
           case hyp theorem of [asm] => aconv asm assumption | _ => false
       in
         strict_fails andalso null residues andalso null preferred_residues
         andalso rejects_children
         andalso uses (validate_recovered []) phase1_pa
         andalso uses (validate_preferred []) redex
       end)

val _ =
  test
    ("move-assumption-to-back validates and round-trips",
     fn () =>
       let
         val original = ([phase1_pa, phase1_qa, phase1_ra], goal_r)
         val move = clasetReplay.MOVE_ASSUMPTION_TO_BACK_TAC 1
         val tactic =
           Tactical.THEN (move, Tactical.THEN (move, move))
         val (goals, _) = Tactical.VALID tactic original
       in
         same_goals goals [original]
       end)

val _ =
  test
    ("corrupt replay is a catchable outcome",
     fn () =>
       let
         val validation = fn [] => boolTheory.TRUTH
           | _ => raise Fail "bad corrupt validation"
         val record =
           clasetReplay.make_record
             {kind = clasetReplay.Assumption 99, target = 1,
              consumed = SOME 99, created = {terms = [], types = []},
              eigenvariables = [], validation = validation,
              action = clasetReplay.assumption_action 99,
              children = []}
         val script =
           clasetReplay.append (clasetReplay.empty 1) record
         val grounded =
           clasetReplay.ground clasetMeta.empty script
       in
         case clasetReplay.replay_in (Context.snapshot ())
                grounded ([phase1_pa], phase1_pa) of
             clasetReplay.ReplayFailed _ => true
           | clasetReplay.Replayed _ => false
       end)

(* TASK_12: D24 rigid wrapper materialization and opaque replay. *)

val _ =
  test
    ("metavariable wrapper round-trips and replays its validation",
     fn () =>
       let
         val (meta, store) =
           clasetMeta.new_meta {allow = [], ty = Type.bool}
             clasetMeta.empty
         val target = boolSyntax.mk_conj (meta, meta)
         val node =
           clasetGoal.create
             {goals = [{params = [], asl = [meta], w = target}],
              store = store, level = 0}
         val cs =
           clasetLib.add_safe_wrapper
             ("meta-conjunction", safe_before Tactic.CONJ_TAC)
             clasetLib.empty_cs
       in
         case seq.cases (safe_step cs (node, 1)) of
             NONE => false
           | SOME ((record, lifted), _) =>
               let
                 val children = rendered_goals lifted
                 val grounded =
                   clasetReplay.ground (clasetGoal.store lifted)
                     (clasetGoal.replay lifted)
                 val (replayed, validation) =
                   Tactical.VALID (clasetReplay.REPLAY_TAC grounded)
                     (clasetGoal.render node 1)
                 val theorem = validation [ASSUME meta, ASSUME meta]
               in
                 (case clasetStep.kind_of record of
                      clasetStep.Wrapper => true
                    | _ => false) andalso
                 clasetGoal.replay_length lifted = 1 andalso
                 same_goals children
                   [([meta], meta), ([meta], meta)] andalso
                 same_goals replayed children andalso
                 Term.aconv (concl theorem) target
               end
       end)

val _ =
  test
    ("wrapper-selected direct alternative keeps its store and action",
     fn () =>
       let
         val (meta, store) =
           clasetMeta.new_meta {allow = [], ty = Type.bool}
             clasetMeta.empty
         val node =
           clasetGoal.create
             {goals =
                [{params = [], asl = [boolSyntax.T, boolSyntax.F],
                  w = meta},
                 {params = [], asl = [], w = meta}],
              store = store, level = 0}

         fun second base goal ctxt =
           seq.delay
             (fn () =>
               case seq.cases (base goal ctxt) of
                   NONE => seq.empty
                 | SOME (_, rest) =>
                     case seq.cases rest of
                         NONE => seq.empty
                       | SOME (result, _) => seq.result result)

         val cs =
           clasetLib.add_unsafe_wrapper ("second", second)
             clasetLib.empty_cs
       in
         case seq.cases
                (clasetStep.step_in (Context.snapshot ()) cs (node, 1)) of
             NONE => false
           | SOME ((record, next), _) =>
               (case clasetStep.kind_of record of
                    clasetStep.Assumption 2 => true
                  | _ => false) andalso
               Term.aconv
                 (clasetMeta.norm (clasetGoal.store next) meta)
                 boolSyntax.F andalso
               same_goals (rendered_goals next) [([], boolSyntax.F)]
       end)

val _ =
  test
    ("wrapper cannot introduce a marked free it did not receive",
     fn () =>
       let
         val (received, store) =
           clasetMeta.new_meta {allow = [], ty = Type.bool}
             clasetMeta.empty
         val (foreign, _) =
           clasetMeta.new_meta {allow = [], ty = Type.bool}
             clasetMeta.empty
         val node =
           clasetGoal.create
             {goals = [{params = [], asl = [], w = received}],
              store = store, level = 0}
         fun forged _ _ =
           seq.result
             ([([], foreign)],
              fn _ => raise Fail "a rejected validation was called")
         val cs =
           clasetLib.add_safe_wrapper
             ("foreign-marker", fn _ => forged)
             clasetLib.empty_cs
       in
         case seq.cases (safe_step cs (node, 1)) of
             NONE => true
           | SOME _ => false
       end)

val _ =
  test
    ("unrender rejects an unreceived marked type variable",
     fn () =>
       let
         val (meta, store) =
           clasetMeta.new_meta {allow = [], ty = Type.bool}
             clasetMeta.empty
         val (foreign_type, _) =
           clasetMeta.new_tymeta clasetMeta.empty
         val foreign =
           Term.mk_var ("wrapper_foreign_type", foreign_type)
         val forged = boolSyntax.mk_eq (foreign, foreign)
         val node =
           clasetGoal.create
             {goals = [{params = [], asl = [], w = meta}],
              store = store, level = 0}
         val result =
           ([([], forged)],
            fn _ => raise Fail "a rejected validation was called")
       in
         not (Option.isSome (clasetGoal.unrender node 1 result))
       end)

(* TASK_13: search drivers, dynamic pruning, bounding, and tracing. *)

fun search_node goals store =
  clasetGoal.create {goals = goals, store = store, level = 0}

fun search_singleton tm =
  search_node [{params = [], asl = [], w = tm}] clasetMeta.empty

fun search_solved store = search_node [] store

fun search_results sequence =
  case seq.cases sequence of
      NONE => []
    | SOME (value, rest) => value :: search_results rest

fun search_target node = #w (hd (clasetGoal.goals node))

val _ =
  test
    ("DEPTH_SOLVE cuts ancestor cycles independently in each sibling",
     fn () =>
       let
         val nodes =
           Vector.tabulate
             (13, fn i =>
                search_singleton (Term.mk_var (Int.toString i, bool_ty)))
         val expanded = ref []
         fun expand node =
           let
             val (name, _) = Term.dest_var (search_target node)
             val i = valOf (Int.fromString name)
             val _ = expanded := i :: !expanded
             val children =
               if i < 9 then [i + 1]
               else
                 case i of
                     9 => [10, 11]
                   | 10 => [12]
                   | 11 => [12]
                   | _ => [10]
           in
             seq.fromList (map (fn j => Vector.sub (nodes, j)) children)
           end
         val results =
           search_results
             (clasetSearch.DEPTH_SOLVE traceUtil.silent expand
                (Vector.sub (nodes, 0)))
       in
         null results andalso
         List.rev (!expanded) = List.tabulate (10, I) @ [10, 12, 11, 12, 10]
       end)

val dfs_root_tm = Term.mk_var ("dfs_root", bool_ty)
val dfs_left_tm = Term.mk_var ("dfs_left", bool_ty)
val dfs_right_tm = Term.mk_var ("dfs_right", bool_ty)
val dfs_solution1_tm = Term.mk_var ("dfs_solution1", bool_ty)
val dfs_solution2_tm = Term.mk_var ("dfs_solution2", bool_ty)
val dfs_solution3_tm = Term.mk_var ("dfs_solution3", bool_ty)

val _ =
  test
    ("DEPTH_FIRST is lazy, depth-first, and suppresses duplicate solutions",
     fn () =>
       let
         val forced_right = ref false
         fun satisfied node =
           let val target = search_target node
           in
             Term.aconv target dfs_solution1_tm orelse
             Term.aconv target dfs_solution2_tm orelse
             Term.aconv target dfs_solution3_tm
           end
         fun expand node =
           let val target = search_target node
           in
             if Term.aconv target dfs_root_tm then
               seq.fromList
                 [search_singleton dfs_left_tm,
                  search_singleton dfs_right_tm]
             else if Term.aconv target dfs_left_tm then
               seq.fromList
                 [search_singleton dfs_solution1_tm,
                  search_singleton dfs_solution1_tm]
             else if Term.aconv target dfs_right_tm then
               (forced_right := true;
                seq.result (search_singleton dfs_solution2_tm))
             else if Term.aconv target dfs_solution1_tm then
               seq.result (search_singleton dfs_solution3_tm)
             else seq.empty
           end
         val results =
           clasetSearch.DEPTH_FIRST traceUtil.silent satisfied expand
             (search_singleton dfs_root_tm)
         val first = seq.hd results
       in
         Term.aconv (search_target first) dfs_solution1_tm andalso
         not (!forced_right) andalso
         aconv_list (map search_target (search_results results))
           [dfs_solution1_tm, dfs_solution3_tm, dfs_solution2_tm]
       end)

val _ =
  test
    ("DEPTH_FIRST preserves solution order after indexing duplicates",
     fn () =>
       let
         val root = search_singleton dfs_root_tm
         val targets = List.tabulate (12, fn i =>
           mk_var ("dfs_solution_" ^ Int.toString i, bool_ty))
         val leaves = map search_singleton targets
         fun satisfied node = not (aconv (search_target node) dfs_root_tm)
         fun expand node =
           if satisfied node then seq.empty
           else seq.fromList (leaves @ map search_singleton targets)
         val results =
           search_results
             (clasetSearch.DEPTH_FIRST traceUtil.silent satisfied expand root)
       in
         aconv_list (map search_target results) targets
       end)

fun bool_function_chain 0 tm = tm
  | bool_function_chain count tm =
      let
        val function =
          Term.mk_var
            ("search_pad_" ^ Int.toString count, bool_ty --> bool_ty)
      in
        bool_function_chain (count - 1) (Term.mk_comb (function, tm))
      end

val best_root_tm = Term.mk_var ("best_root", bool_ty)
val best_small_tm = Term.mk_var ("best_small", bool_ty)
val best_large_tm = bool_function_chain 4
  (Term.mk_var ("best_large", bool_ty))
val best_small_solution_tm = Term.mk_var ("best_small_solution", bool_ty)
val best_large_solution_tm = Term.mk_var ("best_large_solution", bool_ty)

val _ =
  test
    ("BEST_FIRST orders by size and eagerly drains child sequences",
     fn () =>
       let
         val generated = ref 0
         fun satisfied node =
           let val target = search_target node
           in
             Term.aconv target best_small_solution_tm orelse
             Term.aconv target best_large_solution_tm
           end
         fun eager_children values =
           case values of
               [] => seq.empty
             | value :: rest =>
                 seq.delay
                   (fn () =>
                     (generated := !generated + 1;
                      seq.cons value (eager_children rest)))
         fun expand node =
           let val target = search_target node
           in
             if Term.aconv target best_root_tm then
               eager_children
                 [search_singleton best_large_tm,
                  search_singleton best_small_tm]
             else if Term.aconv target best_small_tm then
               seq.result (search_singleton best_small_solution_tm)
             else if Term.aconv target best_large_tm then
               seq.result (search_singleton best_large_solution_tm)
             else seq.empty
           end
         val result =
           seq.hd
             (clasetSearch.BEST_FIRST traceUtil.silent satisfied expand
               (search_singleton best_root_tm))
       in
         !generated = 2 andalso
         Term.aconv (search_target result) best_small_solution_tm
       end)

val _ =
  test
    ("BEST_FIRST delete_all_min expands an equal node only once",
     fn () =>
       let
         val small_expansions = ref 0
         fun satisfied node =
           Term.aconv (search_target node) best_small_solution_tm
         fun expand node =
           let val target = search_target node
           in
             if Term.aconv target best_root_tm then
               seq.fromList
                 [search_singleton best_small_tm,
                  search_singleton best_small_tm]
             else if Term.aconv target best_small_tm then
               (small_expansions := !small_expansions + 1;
                seq.result (search_singleton best_small_solution_tm))
             else seq.empty
           end
         val results =
           search_results
             (clasetSearch.BEST_FIRST traceUtil.silent satisfied expand
               (search_singleton best_root_tm))
       in
         length results = 1 andalso !small_expansions = 1
       end)

(* A state that reaches the frontier again is one the driver has already
   taken apart, and its children are already in the heap.  Expanding it
   a second time only re-enumerates them, and where a rule consumes an
   assumption a sibling branch restores, the re-enumeration is a cycle
   that never grows and so never loses its place at the front. *)
val _ =
  test
    ("BEST_FIRST expands a state returning to the frontier only once",
     fn () =>
       let
         val saved_limit = !clasetSearch.node_limit
         fun expand node =
           if Term.aconv (search_target node) best_root_tm then
             seq.result (search_singleton best_small_tm)
           else seq.result (search_singleton best_root_tm)
         val _ = clasetSearch.node_limit := 1000
         val results =
           search_results
             (clasetSearch.BEST_FIRST traceUtil.silent (fn _ => false) expand
               (search_singleton best_root_tm))
         val count = clasetSearch.node_count ()
         val _ = clasetSearch.node_limit := saved_limit
       in
         List.null results andalso count = 2
       end)

val astar_root_tm = Term.mk_var ("astar_root", bool_ty)
val astar_parent_tm = Term.mk_var ("astar_parent", bool_ty)
val astar_new_tm = Term.mk_var ("astar_new", bool_ty)
val astar_old_tm = bool_function_chain 5
  (Term.mk_var ("astar_old", bool_ty))
val astar_new_solution_tm =
  Term.mk_var ("astar_new_solution", bool_ty)
val astar_old_solution_tm =
  Term.mk_var ("astar_old_solution", bool_ty)

val _ =
  test
    ("ASTAR uses size plus five times level and LIFO equal costs",
     fn () =>
       let
         fun satisfied node =
           let val target = search_target node
           in
             Term.aconv target astar_new_solution_tm orelse
             Term.aconv target astar_old_solution_tm
           end
         fun expand node =
           let val target = search_target node
           in
             if Term.aconv target astar_root_tm then
               seq.fromList
                 [search_singleton astar_parent_tm,
                  search_singleton astar_old_tm]
             else if Term.aconv target astar_parent_tm then
               seq.result (search_singleton astar_new_tm)
             else if Term.aconv target astar_new_tm then
               seq.result (search_singleton astar_new_solution_tm)
             else if Term.aconv target astar_old_tm then
               seq.result (search_singleton astar_old_solution_tm)
             else seq.empty
           end
         val result =
           seq.hd
             (clasetSearch.ASTAR traceUtil.silent satisfied expand
               (search_singleton astar_root_tm))
       in
         clasetGoal.term_size astar_old_tm = 6 andalso
         Term.aconv (search_target result) astar_new_solution_tm
       end)

val _ =
  test
    ("ASTAR suppresses the first equal-cost duplicate",
     fn () =>
       let
         val parent_expansions = ref 0
         fun satisfied node =
           Term.aconv (search_target node) astar_new_solution_tm
         fun expand node =
           let val target = search_target node
           in
             if Term.aconv target astar_root_tm then
               seq.fromList
                 [search_singleton astar_parent_tm,
                  search_singleton astar_parent_tm]
             else if Term.aconv target astar_parent_tm then
               (parent_expansions := !parent_expansions + 1;
                seq.result (search_singleton astar_new_solution_tm))
             else seq.empty
           end
         val _ =
           search_results
             (clasetSearch.ASTAR traceUtil.silent satisfied expand
               (search_singleton astar_root_tm))
       in
         !parent_expansions = 1
       end)

val _ =
  test
    ("a budgeted best frontier resumes its partial child scan",
     fn () =>
       let
         val generated = ref 0
         val yields = ref 0
         fun satisfied node =
           Term.aconv (search_target node) best_small_solution_tm orelse
           Term.aconv (search_target node) best_large_solution_tm
         fun children [] = seq.empty
           | children (value :: rest) =
               seq.delay
                 (fn () =>
                   (generated := !generated + 1;
                    seq.cons value (children rest)))
         fun expand node =
           let val target = search_target node
           in
             if Term.aconv target best_root_tm then
               children
                 [search_singleton best_large_tm,
                  search_singleton best_small_tm]
             else if Term.aconv target best_small_tm then
               seq.result (search_singleton best_small_solution_tm)
             else if Term.aconv target best_large_tm then
               seq.result (search_singleton best_large_solution_tm)
             else seq.empty
           end
         val budget =
           searchBudget.create
             {candidates = SOME 1, applications = SOME 0,
              normalization = SOME 0}
         val session =
           clasetSearch.new_best_session traceUtil.silent
             budget satisfied expand
             (search_singleton best_root_tm)
         fun resume 0 = NONE
           | resume turns =
               (case clasetSearch.resume_frontier session of
                    clasetSearch.FrontierYielded {kind, ...} =>
                      (yields := !yields + 1;
                       searchBudget.extend budget kind 1;
                       resume (turns - 1))
                  | clasetSearch.FrontierResult {node, ...} => SOME node
                  | _ => NONE)
         val result =
           Lib.with_flag (clasetSearch.node_limit, 1)
             (fn () => resume 100) ()
         val reference_budget = searchBudget.unbounded ()
         val reference =
           clasetSearch.resume_frontier
             (clasetSearch.new_best_session traceUtil.silent reference_budget
               satisfied expand (search_singleton best_root_tm))
         val same_work =
           #candidates (searchBudget.usage budget) =
             #candidates (searchBudget.usage reference_budget) andalso
           #applications (searchBudget.usage budget) =
             #applications (searchBudget.usage reference_budget)
         fun next_solution 0 = NONE
           | next_solution turns =
               (case clasetSearch.resume_frontier session of
                    clasetSearch.FrontierYielded {kind, ...} =>
                      (searchBudget.extend budget kind 1;
                       next_solution (turns - 1))
                  | clasetSearch.FrontierResult {node, ...} => SOME node
                  | _ => NONE)
         val later = next_solution 100
       in
         (case (result, reference) of
              (SOME actual,
               clasetSearch.FrontierResult {node = expected, ...}) =>
                 Term.aconv (search_target actual)
                   (search_target expected) andalso
                 Term.aconv (search_target actual)
                   best_small_solution_tm
            | _ => false) andalso
         !yields > 2 andalso !generated = 4 andalso same_work andalso
         (case later of
              SOME node =>
                Term.aconv (search_target node)
                  best_large_solution_tm
            | NONE => false) andalso
         (case clasetSearch.resume_frontier session of
              clasetSearch.FrontierExhausted => true
            | _ => false)
       end)

val _ =
  test
    ("a budgeted A* frontier retains ordering after a yield",
     fn () =>
       let
         fun satisfied node =
           Term.aconv (search_target node) astar_new_solution_tm orelse
           Term.aconv (search_target node) astar_old_solution_tm
         fun expand node =
           let val target = search_target node
           in
             if Term.aconv target astar_root_tm then
               seq.fromList
                 [search_singleton astar_parent_tm,
                  search_singleton astar_old_tm]
             else if Term.aconv target astar_parent_tm then
               seq.result (search_singleton astar_new_tm)
             else if Term.aconv target astar_new_tm then
               seq.result (search_singleton astar_new_solution_tm)
             else if Term.aconv target astar_old_tm then
               seq.result (search_singleton astar_old_solution_tm)
             else seq.empty
           end
         val budget =
           searchBudget.create
             {candidates = SOME 0, applications = NONE,
              normalization = NONE}
         val session =
           clasetSearch.new_astar_session traceUtil.silent budget
             satisfied expand
             (search_singleton astar_root_tm)
         val first = clasetSearch.resume_frontier session
         val _ = searchBudget.extend budget searchBudget.Candidate 100
         val second = clasetSearch.resume_frontier session
       in
         (case first of
              clasetSearch.FrontierYielded
                {kind = searchBudget.Candidate, usage, ...} =>
                  #candidates usage = 0
            | _ => false) andalso
         (case second of
              clasetSearch.FrontierResult {node, ...} =>
                Term.aconv (search_target node)
                  astar_new_solution_tm
            | _ => false)
       end)

val _ =
  test
    ("frontier yields keep every solution from one expansion",
     fn () =>
       let
         val budget =
           searchBudget.create
             {candidates = SOME 1, applications = SOME 1,
              normalization = NONE}
         fun expand node =
           if Term.aconv (search_target node) best_root_tm then
             seq.fromList
               [search_singleton best_small_solution_tm,
                search_singleton best_large_solution_tm]
           else seq.empty
         fun satisfied node =
           Term.aconv (search_target node) best_small_solution_tm orelse
           Term.aconv (search_target node) best_large_solution_tm
         val session =
           clasetSearch.new_best_session traceUtil.silent
             budget satisfied expand
             (search_singleton best_root_tm)
         val first = clasetSearch.resume_frontier session
         val _ = searchBudget.extend budget searchBudget.Candidate 3
         val next = clasetSearch.resume_frontier session
         val after = clasetSearch.resume_frontier session
         val end_result = clasetSearch.resume_frontier session
       in
         (case first of
              clasetSearch.FrontierYielded
                {kind = searchBudget.Candidate, ...} => true
            | _ => false) andalso
         (case (next, after) of
              (clasetSearch.FrontierResult {node = left, ...},
               clasetSearch.FrontierResult {node = right, ...}) =>
                 Term.aconv (search_target left)
                   best_small_solution_tm andalso
                 Term.aconv (search_target right)
                   best_large_solution_tm
            | _ => false) andalso
         (case end_result of
              clasetSearch.FrontierExhausted => true
            | _ => false)
       end)

val _ =
  test
    ("duplicate child floods spend candidate work but few expansions",
     fn () =>
       let
         fun expand node =
           if Term.aconv (search_target node) best_root_tm then
             seq.fromList
               (List.tabulate
                 (251, fn _ => search_singleton best_small_tm))
           else seq.empty
         val budget =
           searchBudget.create
             {candidates = SOME 2, applications = SOME 2,
              normalization = NONE}
         val session =
           clasetSearch.new_best_session traceUtil.silent
             budget (fn _ => false) expand
             (search_singleton best_root_tm)
         val yields = ref 0
         fun finish 0 = false
           | finish turns =
               (case clasetSearch.resume_frontier session of
                    clasetSearch.FrontierYielded
                      {kind = searchBudget.Candidate, ...} =>
                        (yields := !yields + 1;
                         searchBudget.extend budget
                           searchBudget.Candidate 7;
                         finish (turns - 1))
                  | clasetSearch.FrontierExhausted => true
                  | _ => false)
         val exhausted = finish 100
         val reference_budget = searchBudget.unbounded ()
         val reference =
           clasetSearch.resume_frontier
             (clasetSearch.new_best_session traceUtil.silent reference_budget
               (fn _ => false) expand
               (search_singleton best_root_tm))
       in
         exhausted andalso !yields > 1 andalso
         (case reference of
              clasetSearch.FrontierExhausted => true
            | _ => false) andalso
         #applications (searchBudget.usage budget) = 2 andalso
         #applications (searchBudget.usage reference_budget) = 2 andalso
         #candidates (searchBudget.usage budget) =
           #candidates (searchBudget.usage reference_budget) andalso
         #candidates (searchBudget.usage budget) > 251
       end)

val _ =
  test
    ("an inner frontier cutoff retains its cursor and interrupts propagate",
     fn () =>
       let
         val inner =
           searchBudget.create
             {candidates = SOME 0, applications = NONE,
              normalization = NONE}
         fun limited _ =
           (searchBudget.charge inner searchBudget.Candidate;
            seq.empty)
         val session =
           clasetSearch.new_best_session traceUtil.silent
             (searchBudget.unbounded ()) (fn _ => false) limited
             (search_singleton best_root_tm)
         val cutoff = clasetSearch.resume_frontier session
         val _ = searchBudget.extend inner searchBudget.Candidate 1
         val resumed = clasetSearch.resume_frontier session
         val interrupted_session =
           clasetSearch.new_best_session traceUtil.silent
             (searchBudget.unbounded ()) (fn _ => false)
             (fn _ => raise Portable.Interrupt)
             (search_singleton best_root_tm)
         val interrupted =
           ((ignore
               (clasetSearch.resume_frontier interrupted_session);
             false)
            handle Portable.Interrupt => true)
       in
         interrupted andalso
         (case clasetSearch.resume_frontier interrupted_session of
              clasetSearch.FrontierExhausted => true
            | _ => false) andalso
         (case cutoff of
              clasetSearch.FrontierYielded
                {kind = searchBudget.Candidate, usage, ...} =>
                  #candidates usage = 0
            | _ => false) andalso
         (case resumed of
              clasetSearch.FrontierExhausted => true
            | _ => false)
       end)

val _ =
  test
    ("DEEPEN restarts and commits to its first successful bound",
     fn () =>
       let
         val attempted = ref ([] : int list)
         val later_forced = ref false
         val solved_invoked = ref false
         fun bounded bound node =
           (attempted := !attempted @ [bound];
            if bound < 3 then seq.empty
            else if bound = 3 then
              seq.fromList [node, search_singleton dfs_solution1_tm]
            else
              (later_forced := true; seq.result node))
         val results =
           search_results
             (clasetSearch.DEEPEN traceUtil.silent (2, 7) bounded 1
               (search_singleton dfs_root_tm))
         val solved_results =
           search_results
             (clasetSearch.DEEPEN traceUtil.silent (2, 7)
               (fn _ => fn node =>
                 (solved_invoked := true; seq.result node))
               1 (search_solved clasetMeta.empty))
       in
         !attempted = [1, 3] andalso length results = 2 andalso
         not (!later_forced) andalso List.null solved_results andalso
         not (!solved_invoked)
       end)

val _ =
  test
    ("BEST_FIRST node counter stops a runaway frontier cleanly",
     fn () =>
       let
         val saved_limit = !clasetSearch.node_limit
         fun expand node =
           let
             val next = clasetGoal.level node + 1
             val target =
               Term.mk_var
                 ("bounded_node_" ^ Int.toString next, bool_ty)
           in
             seq.result (search_singleton target)
           end
         val _ = clasetSearch.node_limit := 2
         val results =
           search_results
             (clasetSearch.BEST_FIRST traceUtil.silent (fn _ => false) expand
               (search_singleton best_root_tm))
         val count = clasetSearch.node_count ()
         val _ = clasetSearch.node_limit := saved_limit
       in
         List.null results andalso count = 2
       end)

val _ =
  test
    ("swapped implication and universal builtins are valid safe steps",
     fn () =>
       let
         val x = Term.mk_var ("swapped_builtin_x", Type.ind)
         val predicate =
           Term.mk_var
             ("swapped_builtin_predicate", Type.ind --> Type.bool)
         val universal =
           boolSyntax.mk_forall (x, Term.mk_comb (predicate, x))
         val inputs =
           [([boolSyntax.mk_neg
                (boolSyntax.mk_imp (goal_p, goal_q))], goal_r),
            ([boolSyntax.mk_neg universal], goal_r)]
         val _ =
           List.app
             (fn input =>
               ignore
                 (Tactical.VALID
                   (classicalLib.SAFE_STEP_TAC []) input))
             inputs
         val beta_p = Term.mk_var ("swapped_beta_p", Type.bool)
         val abstraction =
           Term.mk_abs
             (beta_p, boolSyntax.mk_imp (beta_p, goal_q))
         val beta_implication = Term.mk_comb (abstraction, goal_p)
         val beta_goal =
           ([], boolSyntax.mk_imp
             (boolSyntax.mk_neg beta_implication,
              boolSyntax.mk_imp (goal_q, goal_p)))
         val (residues, _) =
           Tactical.VALID (classicalLib.FAST_TAC []) beta_goal
       in
         List.null residues
       end
       handle error as HOL_ERR _ =>
         (Feedback.HOL_MESG (Feedback.exn_to_string error); false))

(* -------------------------------------------------------------------------
 * TASK_16: Pelletier fast-parity corpus (BEGIN reusable corpus).
 *
 * These are direct HOL4 translations of Pelletier 1--17 and the
 * easy-quantifier problems for which Paulson's blast report Table 1 records
 * successful Isabelle Fast_tac runs: 24, 26, and 28.  Pelletier 18--23, 25,
 * 27, and 29--33 are retained for the complete TASK_23 blast corpus; Table 1
 * does not report Fast_tac results for them.  Problem 34 is explicitly
 * retained there as expected-unsolved by Fast_tac (Table 1 says "failed").
 * ------------------------------------------------------------------------- *)

val pelletier_fast_corpus : (int * term) list =
  [(1, “(P ==> Q) <=> (~Q ==> ~P)”),
   (2, “~~P <=> P”),
   (3, “~(P ==> Q) ==> (Q ==> P)”),
   (4, “(~P ==> Q) <=> (~Q ==> P)”),
   (5, “((P \/ Q) ==> (P \/ R)) ==> (P \/ (Q ==> R))”),
   (6, “P \/ ~P”),
   (7, “P \/ ~~~P”),
   (8, “((P ==> Q) ==> P) ==> P”),
   (9, “((P \/ Q) /\ (~P \/ Q) /\ (P \/ ~Q)) ==>
         ~(~P \/ ~Q)”),
   (10, “(Q ==> R) /\ (R ==> P /\ Q) /\ (P ==> Q \/ R) ==>
          (P <=> Q)”),
   (11, “P <=> P”),
   (12, “((P <=> Q) <=> R) <=> (P <=> (Q <=> R))”),
   (13, “(P \/ (Q /\ R)) <=> ((P \/ Q) /\ (P \/ R))”),
   (14, “(P <=> Q) <=> ((Q \/ ~P) /\ (~Q \/ P))”),
   (15, “(P ==> Q) <=> (~P \/ Q)”),
   (16, “(P ==> Q) \/ (Q ==> P)”),
   (17, “((P /\ (Q ==> R)) ==> ss) <=>
          ((~P \/ Q \/ ss) /\ (~P \/ ~R \/ ss))”),
   (24, “~(?x:'a. ss x /\ Q x) /\
          (!x. P x ==> Q x \/ R x) /\
          (~(?x. P x) ==> ?x. Q x) /\
          (!x. Q x \/ R x ==> ss x) ==>
          ?x. P x /\ R x”),
   (26, “((?x:'a. p x) <=> (?x. q x)) /\
          (!x y. p x /\ q y ==> (r x <=> s y)) ==>
          ((!x. p x ==> r x) <=> (!x. q x ==> s x))”),
   (28, “(!x:'a. P x ==> (!y. Q y)) /\
          ((!x. Q x \/ R x) ==> ?x. Q x /\ ss x) /\
          ((?x. ss x) ==> !x. L x ==> M x) ==>
          (!x. P x /\ L x ==> M x)”)]

(* TASK_16: Pelletier fast-parity corpus (END reusable corpus). *)

val pelletier_fast_budget = Time.fromSeconds 30
val pelletier_fast_solved = ref 0

fun run_pelletier_fast (number, proposition) =
  let
    val name = "FAST_TAC Pelletier " ^ Int.toString number
    val _ = tprint name
    val start = Time.now ()
    val timed_out = ref false
    val result =
      SOME
        (Timeout.apply pelletier_fast_budget
          (fn () =>
            Tactical.VALID
              (classicalLib.FAST_TAC []) ([], proposition)) ())
      handle Timeout.TIMEOUT _ => (timed_out := true; NONE)
           | HOL_ERR _ => NONE
    val elapsed = Time.- (Time.now (), start)
    val solved =
      case result of
          SOME (residues, _) => List.null residues
        | NONE => false
    val within_budget = Time.< (elapsed, pelletier_fast_budget)
  in
    if solved andalso within_budget then
      (pelletier_fast_solved := !pelletier_fast_solved + 1; OK ())
    else if !timed_out orelse not within_budget then
      die (name ^ " exceeded its 30 second budget")
    else
      die (name ^ " did not solve the goal")
  end

val _ = List.app run_pelletier_fast pelletier_fast_corpus

val _ =
  test
    ("FAST_TAC Pelletier solved-goal count",
     fn () =>
       !pelletier_fast_solved = length pelletier_fast_corpus andalso
       !pelletier_fast_solved = 20)

val _ =
  test
    ("D25 prunes alternatives whose bindings cannot reach a sibling",
     fn () =>
       let
         val rigid = Term.mk_var ("prune_rigid", bool_ty)
         val (meta, store0) = bool_meta [] clasetMeta.empty
         val store1 = the_store (clasetMeta.bind (meta, boolSyntax.T) store0)
         val root =
           search_node
             [{params = [], asl = [], w = meta},
              {params = [], asl = [], w = rigid}]
             store0
         fun child () =
           search_node [{params = [], asl = [], w = rigid}] store1
         val expansions = ref 0
         fun expand node =
           (expansions := !expansions + 1;
            case clasetGoal.goals node of
                [_, _] => seq.fromList [child (), child ()]
              | [_] => seq.result (search_solved (clasetGoal.store node))
              | _ => seq.empty)
         val results =
           search_results (clasetSearch.DEPTH_SOLVE traceUtil.silent
             expand root)
       in
         length results = 1 andalso !expansions = 2 andalso
         clasetSearch.pruning_count () > 0
       end)

val _ =
  test
    ("D25 retains alternatives that bind an indirect sibling metavariable",
     fn () =>
       let
         val (tymeta, type_store) =
           clasetMeta.new_tymeta clasetMeta.empty
         val (outer, fresh_store) =
           clasetMeta.new_meta {allow = [], ty = tymeta} type_store
         val (middle, fresh_store) =
           clasetMeta.new_meta {allow = [], ty = tymeta} fresh_store
         val (shared, unbound_store) =
           clasetMeta.new_meta {allow = [], ty = tymeta} fresh_store
         val chained_store =
           the_store (clasetMeta.bind (outer, middle) unbound_store)
         val chained_store =
           the_store (clasetMeta.bind (middle, shared) chained_store)
         val store0 =
           the_store (clasetMeta.bind_ty (tymeta, bool_ty) chained_store)
         val true_store =
           the_store (clasetMeta.bind (shared, boolSyntax.T) store0)
         val false_store =
           the_store (clasetMeta.bind (shared, boolSyntax.F) store0)
         val root =
           search_node
             [{params = [], asl = [], w = shared},
              {params = [], asl = [], w = outer}]
             store0
         fun child store =
           clasetGoal.replace_goal root {pos = 1, children = [], store = store}
         val expansions = ref 0
         fun expand node =
           (expansions := !expansions + 1;
            case clasetGoal.goals node of
                [_, _] =>
                  seq.fromList [child true_store, child false_store]
              | [_] =>
                  if Term.aconv (#2 (clasetGoal.render node 1)) boolSyntax.F
                  then seq.result (search_solved (clasetGoal.store node))
                  else seq.empty
              | _ => seq.empty)
         val results =
           search_results (clasetSearch.DEPTH_SOLVE traceUtil.silent
             expand root)
       in
         length results = 1 andalso !expansions = 3
       end)

val _ =
  test
    ("D25 follows type dependencies inside term binding residues",
     fn () =>
       let
         val (outer_ty, store) = clasetMeta.new_tymeta clasetMeta.empty
         val (middle_ty, store) = clasetMeta.new_tymeta store
         val (inner_ty, store) = clasetMeta.new_tymeta store
         val (sibling, store) = bool_meta [] store
         val arb = boolSyntax.mk_arb outer_ty
         val store = the_store
           (clasetMeta.bind (sibling, boolSyntax.mk_eq (arb, arb)) store)
         val store = the_store
           (clasetMeta.bind_ty (outer_ty, middle_ty) store)
         val store = the_store
           (clasetMeta.bind_ty (middle_ty, inner_ty) store)
         val root = search_node
           [{params = [], asl = [], w = boolSyntax.T},
            {params = [], asl = [], w = sibling}] store
         fun child ty =
           clasetGoal.replace_goal root
             {pos = 1, children = [],
              store = the_store (clasetMeta.bind_ty (inner_ty, ty) store)}
         fun expand node =
           case clasetGoal.goals node of
               [_, _] => seq.fromList [child alpha, child bool_ty]
             | [_] =>
                 if Term.type_of (boolSyntax.lhs
                      (#2 (clasetGoal.render node 1))) = bool_ty
                 then seq.result (search_solved (clasetGoal.store node))
                 else seq.empty
             | _ => seq.empty
       in
         length (search_results (clasetSearch.DEPTH_SOLVE traceUtil.silent
           expand root)) = 1
       end)

val _ =
  test
    ("D25 does not mistake a solved later sibling for the active goal",
     fn () =>
       let
         val active = Term.mk_var ("prune_active", bool_ty)
         val later = Term.mk_var ("prune_later", bool_ty)
         val dead = Term.mk_var ("prune_dead", bool_ty)
         val live = Term.mk_var ("prune_live", bool_ty)
         val root =
           search_node
             [{params = [], asl = [], w = active},
              {params = [], asl = [], w = later}]
             clasetMeta.empty
         fun expand node =
           case clasetGoal.goals node of
               [_, _] =>
                 seq.fromList
                   [search_singleton dead, search_singleton live]
             | [_] =>
                 if Term.aconv (search_target node) live then
                   seq.result (search_solved (clasetGoal.store node))
                 else seq.empty
             | _ => seq.empty
       in
         length
           (search_results (clasetSearch.DEPTH_SOLVE traceUtil.silent
             expand root)) = 1
       end)

val _ =
  test
    ("classical trace levels report summaries and full candidates",
     fn () =>
       let
         val notices = ref ([] : string list)
         fun remember message = notices := message :: !notices
         val _ =
           Lib.with_flag
             (Feedback.MESG_outstream, remember)
             (fn () =>
               ignore
                 (search_results
                   (clasetSearch.BEST_FIRST
                     (traceUtil.level_of clasetReplay.tracer
                       (HOLFlags.set_flagC
                         (traceUtil.flag clasetReplay.tracer, 3)
                         (Context.snapshot ())))
                     (fn _ => false)
                     (fn _ => seq.empty)
                     (search_singleton best_root_tm)))) ()
       in
         List.exists (String.isSubstring "best-first expansion") (!notices)
         andalso
         List.exists (String.isSubstring "candidate:") (!notices)
         andalso
         List.exists (String.isSubstring "search exhausted") (!notices)
       end)

(* A step tactic consults only the context it is applied in.  The
   instantiating step has no wrappers to hand it to, so nothing reads one
   at all. *)
val _ =
  test
    ("CS_INST_STEP_TAC reads no ambient context in a proof",
     fn () =>
       let
         val p = mk_var ("inst_step_p", bool_ty)
         val goal = ([p], p)
         val ctxt = Context.snapshot ()
         val warnings = ref ([] : string list)
         fun run () =
           (Context.set_ambient_report_level 2;
            Lib.with_flag
              (Feedback.WARNING_outstream,
               fn s => warnings := s :: !warnings)
              (Context.in_proof
                 (fn () =>
                    Lib.total
                      (classicalLib.CS_INST_STEP_TAC clasetLib.empty_cs
                         goal) ctxt))
              ())
         val _ =
           Portable.finally (fn () => Context.set_ambient_report_level 1)
             run ()
       in
         null (!warnings)
       end)

(* A search tactic reports at the classical.trace level of the context it
   is run in; the ambient level, which runtac's context starts from and
   trace_tac then overrides, is not consulted. *)
val _ =
  test
    ("classical search tactics trace at their context's level",
     fn () =>
       let
         fun notices_of ambient tactic =
           let
             val notices = ref ([] : string list)
             fun remember message = notices := message :: !notices
             val old_trace = HOLFlags.current_trace "classical.trace"
             fun attempt () =
               (HOLFlags.set_trace "classical.trace" ambient;
                ignore (Lib.total (runtac tactic) ([], boolSyntax.F)))
             val _ =
               Portable.finally
                 (fn () => HOLFlags.set_trace "classical.trace" old_trace)
                 (Lib.with_flag (Feedback.MESG_outstream, remember) attempt)
                 ()
           in
             !notices
           end
         val best = NTactical.DETERM (classicalLib.CS_BEST_TAC
                                        clasetLib.empty_cs)
         val exhausted = List.exists (String.isSubstring "search exhausted")
       in
         exhausted
           (notices_of 0 (Tactical.trace_tac ("classical.trace", 1) best))
         andalso
         null (notices_of 3 (Tactical.trace_tac ("classical.trace", 0) best))
       end)

(* TASK_14: public and claset-explicit driver surfaces. *)

fun tactic_solves tactic goal =
  let val (residues, _) = Tactical.VALID tactic goal
  in List.null residues end

val driver_witness = Term.mk_var ("driver_witness", Type.ind)
val driver_constant = Term.mk_var ("driver_constant", Type.ind)
val driver_exists_goal : Abbrev.goal =
  ([], boolSyntax.mk_exists
    (driver_witness,
     boolSyntax.mk_eq (driver_witness, driver_constant)))

val _ =
  test
    ("FAST_TAC instantiates a witness and replays the solution",
     fn () => tactic_solves (classicalLib.FAST_TAC []) driver_exists_goal)

(* The universal assumption is the rule, and one of its premises is a
   negated equality: the branch that assumes the equality has to keep the
   goal's own variables, or the contradiction that settles the unknown no
   longer finds them. *)
val _ =
  test
    ("FAST_TAC chains through a negated-equality guard",
     fn () =>
       tactic_solves (classicalLib.FAST_TAC [])
         ([], “(!l:'a. l <> a ==> q l) ==> b <> a ==> q b”) andalso
       tactic_solves (classicalLib.FAST_TAC [])
         ([], “(!l r:'a. ss l /\ ss r /\ l <> r ==> p l r) ==>
               (!x y:'a. p x y ==> q x y) ==>
               ss c ==> ss d ==> c <> d ==> q c d”))

(* Eta contracts [!x. P x] to [$! P], and [dest_forall] fails on the
   contracted form: a goal posed that way had no binder any step could
   take apart, so it was inert whatever its assumptions said.  The goal
   normalisation spells such a quantifier back out, which is what makes
   the two spellings one goal. *)
val _ =
  test
    ("an eta-contracted universal goal is still stripped",
     fn () =>
       let
         val expanded =
           “(!x:'a. eta_goal_q x ==> eta_goal_p x) ==>
            (!x:'a. eta_goal_q x) ==> !x:'a. eta_goal_p x”
         val contracted =
           boolSyntax.rhs (concl
             (Conv.RAND_CONV
               (Conv.RAND_CONV (Conv.RAND_CONV Drule.ETA_CONV))
               expanded))
       in
         not (Term.aconv contracted expanded) andalso
         tactic_solves (classicalLib.FAST_TAC []) ([], contracted)
       end)

val _ =
  test
    ("single engine step drivers replay their resulting nodes",
     fn () =>
       let
         val implication = boolSyntax.mk_imp (goal_p, goal_q)
         val goal = ([], implication)
         val expected = [([], goal_q)]
         val (step_goals, _) =
           Tactical.VALID (classicalLib.STEP_TAC []) goal
         val (slow_goals, _) =
           Tactical.VALID (classicalLib.SLOW_STEP_TAC []) goal
         val (inst_goals, _) =
           Tactical.VALID
             (classicalLib.INST_STEP_TAC [])
             ([goal_p], goal_p)
       in
         same_goals step_goals expected andalso
         same_goals slow_goals expected andalso
         List.null inst_goals
       end)

fun nested_exists 0 body = body
  | nested_exists count body =
      let
        val witness =
          Term.mk_var
            ("deep_witness_" ^ Int.toString count, Type.ind)
      in
        boolSyntax.mk_exists
          (witness, nested_exists (count - 1) body)
      end

val _ =
  test
    ("DEEPEN supports a raised programmatic start beyond four",
     fn () =>
       let
         val goal = ([], nested_exists 5 boolSyntax.T)
         val tactic =
           NTactical.DETERM
             (classicalLib.CS_DEEPEN_TAC (clasetLib.the_claset ())
               {start = 6})
       in
         tactic_solves tactic goal andalso
         tactic_solves (classicalLib.DEEPEN_TAC []) goal
       end)

val _ =
  test
    ("DEEPEN saturates safe siblings before bounded search",
     fn () =>
       let
         val x = Term.mk_var ("deepen_safe_x", Type.ind)
         val a = Term.mk_var ("deepen_safe_a", Type.ind)
         val b = Term.mk_var ("deepen_safe_b", Type.ind)
         val left =
           boolSyntax.mk_exists (x, boolSyntax.mk_eq (x, a))
         val right =
           boolSyntax.mk_exists (x, boolSyntax.mk_eq (x, b))
         val goal = ([], boolSyntax.mk_conj (left, right))
         val tactic =
           NTactical.DETERM
             (classicalLib.CS_DEEPEN_TAC (clasetLib.the_claset ())
               {start = 1})
       in
         tactic_solves tactic goal
       end)

fun depth_duplication_fixture () =
  let
    val bound = Term.mk_var ("depth_duplication_bound", Type.ind)
    val left = Term.mk_var ("depth_duplication_left", Type.ind)
    val right = Term.mk_var ("depth_duplication_right", Type.ind)
    val predicate =
      Term.mk_var
        ("depth_duplication_predicate", Type.ind --> Type.bool)
    val pbound = mk_comb (predicate, bound)
    val pleft = mk_comb (predicate, left)
    val pright = mk_comb (predicate, right)
    val target = boolSyntax.mk_eq (pleft, pright)
    val equality =
      TRANS (Drule.EQT_INTRO (ASSUME pleft))
        (SYM (Drule.EQT_INTRO (ASSUME pright)))
    val bridge = DISCH pleft (DISCH pright equality)
    val cs =
      clasetLib.add_elims
        [("depth-duplication-forall",
          clasetSeedTheory.FORALL_ELIM_THM),
         ("depth-duplication-bridge", bridge)]
        clasetLib.empty_cs
  in
    (cs, ([boolSyntax.mk_forall (bound, pbound)], target))
  end

val _ =
  test
    ("CS_DEPTH_SOLVE_TAC distinguishes duplication at one bound",
     fn () =>
       let
         val (cs, goal) = depth_duplication_fixture ()
         fun depth dup =
           NTactical.DETERM
             (classicalLib.CS_DEPTH_SOLVE_TAC {dup = dup} 3 cs)
       in
         tactic_solves (depth true) goal andalso
         tactic_fails (depth false) goal
       end)

val _ =
  test
    ("CS_DEEPEN_TAC retains duplicating bounded-search behavior",
     fn () =>
       let
         val (cs, goal) = depth_duplication_fixture ()
         val tactic =
           NTactical.DETERM
             (classicalLib.CS_DEEPEN_TAC cs {start = 3})
       in
         tactic_solves tactic goal
       end)

(* An unsafe destruction rule whose conclusion carries an unknown that none
   of its own premises fixes.  The rule leaves two goals: the premise
   [~ p v], which stands on the unknown, and the conclusion, which the
   caller's goal settles.  The premise stands on the unknown applied to a
   parameter, which no assumption here matches, so a search that insists on
   it abandons a state it can solve and the rule is unusable however deep
   the search goes.  The claset holds nothing but the rule, so this is the
   only route to the goal. *)
val selection_fixture =
  let
    val predicate_ty = Type.mk_type ("fun", [Type.ind, bool_ty])
    val element = Term.mk_var ("selection_element", Type.ind)
    val predicate = Term.mk_var ("selection_predicate", predicate_ty)
    val bound = Term.mk_var ("selection_bound", Type.ind)
    val major = Term.mk_var ("selection_major", predicate_ty)
    val flaw = Term.mk_var ("selection_flaw", predicate_ty)
    val witness = Term.mk_var ("selection_witness", Type.ind)

    val major_premise = Term.mk_comb (major, element)
    val negated_instance =
      boolSyntax.mk_neg (Term.mk_comb (predicate, element))
    val universal =
      boolSyntax.mk_forall (bound, Term.mk_comb (predicate, bound))
    val instance = SPEC element (ASSUME universal)
    val absurd = MP (NOT_ELIM (ASSUME negated_instance)) instance
    val rule =
      GENL [element, predicate]
        (DISCH major_premise
          (DISCH negated_instance
            (NOT_INTRO (DISCH universal absurd))))

    val other = Term.mk_var ("selection_other", predicate_ty)
    fun body term =
      boolSyntax.mk_conj
        (Term.mk_comb (flaw, term), Term.mk_comb (other, term))
    val goal : Abbrev.goal =
      ([Term.mk_comb (major, witness), boolSyntax.mk_neg (body witness)],
       boolSyntax.mk_neg (boolSyntax.mk_forall (bound, body bound)))
    val cs =
      clasetLib.add_rule
        {kind = clasetRules.Dest, safe = false, prio = NONE}
        ("selection-dest", rule) clasetLib.empty_cs
  in
    (cs, goal)
  end

val _ =
  test
    ("the bounded depth search takes the goal a rule's unknown is settled \
     \in, not the goal that stands on it",
     fn () =>
       let
         val (cs, goal) = selection_fixture
       in
         tactic_solves
           (NTactical.DETERM
             (classicalLib.CS_DEPTH_SOLVE_TAC {dup = true} 4 cs)) goal
       end)

val _ =
  test
    ("CS_DEEPEN_TAC reaches the same rule",
     fn () =>
       let
         val (cs, goal) = selection_fixture
       in
         tactic_solves
           (NTactical.DETERM (classicalLib.CS_DEEPEN_TAC cs {start = 4}))
           goal
       end)

val _ =
  test
    ("CS_FAST_TAC reaches the same rule",
     fn () =>
       let
         val (cs, goal) = selection_fixture
       in
         tactic_solves
           (NTactical.DETERM (classicalLib.CS_FAST_TAC cs)) goal
       end)

val _ =
  test
    ("all solve-completely drivers fail cleanly on a non-theorem",
     fn () =>
       let
         val goal = ([], Term.mk_var ("driver_non_theorem", bool_ty))
         val drivers =
           [classicalLib.FAST_TAC [], classicalLib.SLOW_TAC [],
            classicalLib.BEST_TAC [], classicalLib.SLOW_BEST_TAC [],
            classicalLib.FIRST_BEST_TAC [], classicalLib.ASTAR_TAC [],
            classicalLib.SLOW_ASTAR_TAC [], classicalLib.DEEPEN_TAC []]
       in
         List.all (fn tactic => tactic_fails tactic goal) drivers
       end)

val _ =
  test
    ("frontier drivers replay Tactical.VALID-checked solutions",
     fn () =>
       let
         val drivers =
           [classicalLib.BEST_TAC [],
            classicalLib.SLOW_BEST_TAC [],
            classicalLib.FIRST_BEST_TAC [],
            classicalLib.ASTAR_TAC [],
            classicalLib.SLOW_ASTAR_TAC []]
       in
         List.all
           (fn tactic => tactic_solves tactic driver_exists_goal)
           drivers
       end)

(* TASK_15 group 1: eigenvariable discipline through every driver. *)

val complete_drivers =
  [("FAST_TAC", classicalLib.FAST_TAC []),
   ("SLOW_TAC", classicalLib.SLOW_TAC []),
   ("BEST_TAC", classicalLib.BEST_TAC []),
   ("SLOW_BEST_TAC", classicalLib.SLOW_BEST_TAC []),
   ("FIRST_BEST_TAC", classicalLib.FIRST_BEST_TAC []),
   ("ASTAR_TAC", classicalLib.ASTAR_TAC []),
   ("SLOW_ASTAR_TAC", classicalLib.SLOW_ASTAR_TAC []),
   ("DEEPEN_TAC", classicalLib.DEEPEN_TAC [])]

val eigen_x = Term.mk_var ("eigen_x", Type.ind)
val eigen_y = Term.mk_var ("eigen_y", Type.ind)
val eigen_z = Term.mk_var ("eigen_z", Type.ind)
val eigen_predicate =
  Term.mk_var
    ("eigen_predicate", Type.ind --> Type.ind --> Type.bool)

fun eigen_app left right =
  Term.list_mk_comb (eigen_predicate, [left, right])

val early_meta_non_theorem : Abbrev.goal =
  ([], boolSyntax.mk_exists
    (eigen_x,
     boolSyntax.mk_forall
       (eigen_y, boolSyntax.mk_eq (eigen_x, eigen_y))))

val dual_eigen_non_theorem : Abbrev.goal =
  ([], boolSyntax.mk_imp
    (boolSyntax.mk_forall
      (eigen_x,
       boolSyntax.mk_exists
         (eigen_y, eigen_app eigen_x eigen_y)),
     boolSyntax.mk_exists
       (eigen_y,
        boolSyntax.mk_forall
          (eigen_x, eigen_app eigen_x eigen_y))))

val sibling_eigen_non_theorem : Abbrev.goal =
  ([], boolSyntax.mk_exists
    (eigen_z,
     boolSyntax.mk_conj
       (boolSyntax.mk_forall
         (eigen_x, boolSyntax.mk_eq (eigen_z, eigen_x)),
        boolSyntax.mk_eq (eigen_z, eigen_z))))

fun every_driver_fails goal =
  List.all (fn (_, tactic) => tactic_fails tactic goal) complete_drivers

val _ =
  test
    ("all drivers reject capture by a later eigenvariable",
     fn () => every_driver_fails early_meta_non_theorem)

val _ =
  test
    ("all drivers reject the dual quantifier interchange",
     fn () => every_driver_fails dual_eigen_non_theorem)

val _ =
  test
    ("all drivers reject capture from a sibling-local parameter",
     fn () => every_driver_fails sibling_eigen_non_theorem)

(* TASK_15 group 2: replay and grounding at the driver boundary. *)

fun theorem_equal left right =
  Term.aconv (concl left) (concl right) andalso
  ListPair.allEq
    (fn (left_hyp, right_hyp) => Term.aconv left_hyp right_hyp)
    (hyp left, hyp right)

fun solved_theorem tactic goal =
  let
    val (residues, validation) = Tactical.VALID tactic goal
  in
    if List.null residues then validation []
    else raise Fail "a complete driver left residual goals"
  end

val _ =
  test
    ("every complete driver success passes Tactical.VALID replay",
     fn () =>
       List.all
         (fn (_, tactic) =>
           tactic_solves tactic driver_exists_goal)
         complete_drivers)

val _ =
  test
    ("grounded driver theorems are deterministic across identical runs",
     fn () =>
       List.all
         (fn (_, tactic) =>
           theorem_equal
             (solved_theorem tactic driver_exists_goal)
             (solved_theorem tactic driver_exists_goal))
         complete_drivers)

val _ =
  test
    ("D24 metavariable wrapper round-trips through a complete driver",
     fn () =>
       let
         val witness = Term.mk_var ("wrapper_driver_witness", Type.bool)
         val target =
           boolSyntax.mk_exists
             (witness, boolSyntax.mk_conj (witness, witness))
         val saw_marked_goal = ref false

         fun observed_conjunction (goal as (_, conclusion)) ctxt =
           (if List.exists clasetMeta.is_meta (free_vars conclusion) then
              saw_marked_goal := true
            else ();
            Tactic.CONJ_TAC goal ctxt)

         val cs =
           clasetLib.add_safe_wrapper
             ("driver-meta-conjunction",
              safe_before observed_conjunction)
             (clasetLib.the_claset ())
         val tactic = NTactical.DETERM (classicalLib.CS_FAST_TAC cs)
       in
         tactic_solves tactic ([], target) andalso !saw_marked_goal
       end)

(* TASK_15 group 3: driver selection, bounds, and D25 pruning. *)

val _ =
  test
    ("SLOW backtracks past the instantiation rung that commits FAST",
     fn () =>
       let
         val schematic = Term.mk_var ("driver_slow_m", Type.ind)
         val constant = Term.mk_var ("driver_slow_c", Type.ind)
         val predicate =
           Term.mk_var ("driver_slow_p", Type.ind --> Type.bool)
         val available = mk_comb (predicate, constant)
         val unsafe_p = Term.mk_var ("driver_slow_u", Type.bool)
         val reflexive = boolSyntax.mk_eq (schematic, schematic)
         val blocked = boolSyntax.mk_imp (reflexive, boolSyntax.F)
         val inst_rule =
           GEN schematic (DISCH blocked boolTheory.TRUTH)
         val unsafe_rule =
           GEN unsafe_p (DISCH unsafe_p boolTheory.TRUTH)
         val cs =
           clasetLib.add_intros [("driver-unsafe", unsafe_rule)]
             (clasetLib.add_sintros [("driver-inst", inst_rule)]
               clasetLib.empty_cs)
         val goal = ([available], boolSyntax.T)
         val fast = NTactical.DETERM (classicalLib.CS_FAST_TAC cs)
         val slow = NTactical.DETERM (classicalLib.CS_SLOW_TAC cs)
       in
         tactic_fails fast goal andalso tactic_solves slow goal
       end)

val _ =
  test
    ("BEST driver expands the smaller child before an earlier large one",
     fn () =>
       let
         (* Two fixed propositions of different size, and fixed means
            closed: a free variable in a rule is a parameter the matcher
            may instantiate, never a particular proposition. *)
         val opaque = Term.inst [Type.alpha |-> bool_ty] boolSyntax.arb
         val opaque_pad =
           Term.inst [Type.alpha |-> (bool_ty --> bool_ty)]
             boolSyntax.arb
         fun pad 0 tm = tm
           | pad count tm = pad (count - 1) (mk_comb (opaque_pad, tm))
         val small = opaque
         val large = pad 5 small
         val large_rule = DISCH large boolTheory.TRUTH
         val small_rule = DISCH small boolTheory.TRUTH
         val visited = ref ([] : term list)

         fun observe base (goal as (_, target)) ctxt =
           (visited := target :: !visited; base goal ctxt)

         val plain_cs =
           clasetLib.add_intros
             [("best-driver-small", small_rule),
              ("best-driver-large", large_rule)]
             clasetLib.empty_cs
         val cs =
           clasetLib.add_safe_wrapper ("best-driver-observe", observe)
             plain_cs
         val goal = ([large, small], boolSyntax.T)
         val first_target =
           case first_step clasetStep.unsafe_step plain_cs goal of
               NONE => raise Fail "expected a large first alternative"
             | SOME (_, node) => #2 (the_singleton (rendered_goals node))
         val tactic = NTactical.DETERM (classicalLib.CS_BEST_TAC cs)
         val solved = tactic_solves tactic goal
         val order = List.rev (!visited)
       in
         Term.aconv first_target large andalso solved
         andalso length order >= 2
         andalso Term.aconv (List.nth (order, 1)) small
       end)

(* The turn is a bound on admitted expansions, so the unbounded search
   names the expansion at which a goal closes: a turn that long closes it,
   and a turn one expansion shorter reports no proof.  Reporting no proof
   is failure, which is what lets a caller offer the goal to a different
   engine, and the bound is back to what it was either way.  Five nested
   witnesses give a search deep enough to tell the two turns apart. *)
val _ =
  test
    ("CS_BOUNDED_FIRST_BEST_TAC closes inside its turn, fails one \
     \expansion short, and leaves the bound as it found it",
     fn () =>
       let
         val saved = !clasetSearch.node_limit
         val cs = clasetLib.the_claset ()
         val goal = ([], nested_exists 5 boolSyntax.T)
         val unbounded =
           tactic_solves
             (NTactical.DETERM (classicalLib.CS_FIRST_BEST_TAC cs)) goal
         val needed = clasetSearch.node_count ()
         fun closes turn =
           tactic_solves
             (classicalLib.CS_BOUNDED_FIRST_BEST_TAC cs turn) goal
             handle HOL_ERR _ => false
       in
         unbounded andalso needed >= 2 andalso
         closes needed andalso not (closes (needed - 1)) andalso
         !clasetSearch.node_limit = saved
       end)

val _ =
  test
    ("CS_BOUNDED_FIRST_BEST_TAC refuses a turn of no expansions",
     fn () =>
       let
         val saved = !clasetSearch.node_limit
         val cs = clasetLib.the_claset ()
         val goal = ([], nested_exists 5 boolSyntax.T)
         fun refuses turn =
           (ignore
              (Tactical.VALID
                (classicalLib.CS_BOUNDED_FIRST_BEST_TAC cs turn) goal);
            false)
           handle HOL_ERR _ => true
       in
         refuses 0 andalso refuses ~1 andalso
         !clasetSearch.node_limit = saved
       end)

fun depth_solves cs bound node =
  List.exists
    (List.null o clasetGoal.goals o #2)
    (drain_steps
      (clasetStep.depth_step_in (Context.snapshot ()) cs
        (clasetLib.dup_part cs) bound (node, 1)))

val _ =
  test
    ("DEEPEN accounting leaves safe steps and inst0 free",
     fn () =>
       let
         val implication = boolSyntax.mk_imp (phase1_pa, phase1_pa)
         val safe_node = clasetGoal.from_goal ([], implication)
         val (meta, store) = bool_meta [] clasetMeta.empty
         val inst0_node =
           clasetGoal.create
             {goals = [{params = [], asl = [phase1_pa], w = meta}],
              store = store, level = 0}
         val cs = clasetLib.the_claset ()
       in
         depth_solves cs 0 safe_node andalso
         depth_solves cs 0 inst0_node
       end)

val _ =
  test
    ("DEEPEN charges exactly one for an unsafe witness step",
     fn () =>
       let
         val witness = Term.mk_var ("bound_witness", Type.ind)
         val constant = Term.mk_var ("bound_constant", Type.ind)
         val predicate =
           Term.mk_var ("bound_predicate", Type.ind --> Type.bool)
         val fact = mk_comb (predicate, constant)
         val target =
           boolSyntax.mk_exists
             (witness, mk_comb (predicate, witness))
         val node = clasetGoal.from_goal ([fact], target)
         val cs = clasetLib.the_claset ()
       in
         not (depth_solves cs 0 node) andalso depth_solves cs 1 node
       end)

val _ =
  test
    ("DEEPEN charges exactly one for a duplicating elimination",
     fn () =>
       let
         val bound = Term.mk_var ("dup_bound", Type.ind)
         val constant = Term.mk_var ("dup_constant", Type.ind)
         val predicate =
           Term.mk_var ("dup_predicate", Type.ind --> Type.bool)
         val universal =
           boolSyntax.mk_forall (bound, mk_comb (predicate, bound))
         val target = mk_comb (predicate, constant)
         val node = clasetGoal.from_goal ([universal], target)
         val cs = clasetLib.the_claset ()
       in
         not (depth_solves cs 0 node) andalso depth_solves cs 1 node
       end)

val _ =
  test
    ("D25 negative case retains shared alternatives in the driver",
     fn () =>
       let
         val (shared, store0) = bool_meta [] clasetMeta.empty
         val true_store =
           the_store (clasetMeta.bind (shared, boolSyntax.T) store0)
         val false_store =
           the_store (clasetMeta.bind (shared, boolSyntax.F) store0)
         val root =
           search_node
             [{params = [], asl = [], w = shared},
              {params = [], asl = [], w = shared}]
             store0
         fun child store =
           search_node [{params = [], asl = [], w = shared}] store
         val steps = ref 0
         fun expand node =
           (steps := !steps + 1;
            case clasetGoal.goals node of
                [_, _] =>
                  seq.fromList [child true_store, child false_store]
              | [_] =>
                  if Term.aconv (#2 (clasetGoal.render node 1))
                       boolSyntax.F
                  then seq.result
                    (search_solved (clasetGoal.store node))
                  else seq.empty
              | _ => seq.empty)
         val results =
           search_results (clasetSearch.DEPTH_SOLVE traceUtil.silent
             expand root)
       in
         length results = 1 andalso !steps = 3
       end)

val _ =
  test
    ("blast hyp-subst skips unsuitable equations and stably reorders",
     fn () =>
       let
         val x = Term.mk_var ("x", Type.bool)
         val y = Term.mk_var ("y", Type.bool)
         val a = Term.mk_var ("a", Type.bool)
         val f = Term.mk_var ("f", Type.bool --> Type.bool)
         val p = Term.mk_var ("P", Type.bool --> Type.bool)
         val q = Term.mk_var ("Q", Type.bool --> Type.bool)
         fun app operator operand = Term.mk_comb (operator, operand)
         val unsuitable = boolSyntax.mk_eq (app f x, x)
         val selected = boolSyntax.mk_eq (x, y)
         val unchanged = app p a
         val px = app p x
         val qx = app q x
         val py = app p y
         val qy = app q y
         val original =
           ([unsuitable, selected, unchanged, px, qx], py)
         val node = clasetGoal.from_goal original
         val (_, substituted) =
           case seq.cases
             (clasetStep.blast_hyp_subst_step_in (Context.snapshot ())
               (node, 1)) of
               SOME (result, _) => result
             | NONE => raise Fail "blast hyp-subst did not apply"
         val expected =
           [boolSyntax.mk_eq (app f y, y), py, qy, unchanged]
         val order_ok =
           case clasetGoal.goals substituted of
               [{asl, ...}] =>
                 ListPair.allEq
                   (fn (left, right) => Term.aconv left right)
                   (asl, expected)
             | _ => false
         val (_, closed) =
           case seq.cases
             (clasetStep.blast_assumption_step (substituted, 1)) of
               SOME (result, _) => result
             | NONE => raise Fail "substituted goal did not close"
         val grounded =
           clasetReplay.ground (clasetGoal.store closed)
             (clasetGoal.replay closed)
         val (residuals, validation) =
           Tactical.VALID (clasetReplay.REPLAY_TAC grounded) original
       in
         order_ok andalso null residuals andalso
         (ignore (validation []); true)
       end)

val _ =
  test
    ("recorded hyp-subst mask survives a late metavariable binding",
     fn () =>
       let
         val x = Term.mk_var ("late_subst_x", Type.bool)
         val y = Term.mk_var ("late_subst_y", Type.bool)
         val p =
           Term.mk_var ("late_subst_P", Type.bool --> Type.bool)
         val q =
           Term.mk_var ("late_subst_Q", Type.bool --> Type.bool)
         fun app operator operand = Term.mk_comb (operator, operand)
         val (meta, store0) =
           clasetMeta.new_meta {allow = [], ty = Type.bool}
             clasetMeta.empty
         val raw_goal =
           ([boolSyntax.mk_eq (x, y), app p meta, app q x, app p y],
            app q y)
         val root =
           clasetGoal.create
             {goals =
                [{params = [], asl = #1 raw_goal, w = #2 raw_goal}],
              store = store0, level = 0}
         val (_, substituted) =
           case seq.cases
             (clasetStep.blast_hyp_subst_step_at_in (Context.snapshot ())
               {equality = 1, changed = [false, true, false],
                side = clasetStep.EliminateLeft}
               (root, 1)) of
               SOME (result, _) => result
             | NONE => raise Fail "recorded late-binding substitution"
         val store1 =
           the_store
             (clasetMeta.bind (meta, x) (clasetGoal.store substituted))
         val rebound = clasetGoal.set_store store1 substituted
         val (_, closed) =
           case seq.cases
             (clasetStep.blast_assumption_step_at 1 (rebound, 1)) of
               SOME (result, _) => result
             | NONE => raise Fail "late-binding exact close"
         val grounded =
           clasetReplay.ground (clasetGoal.store closed)
             (clasetGoal.replay closed)
         val original =
           (map (clasetMeta.norm store1) (#1 raw_goal),
            clasetMeta.norm store1 (#2 raw_goal))
       in
         case total
           (Tactical.VALID (clasetReplay.REPLAY_TAC grounded)) original of
             SOME ([], validation) =>
               (ignore (validation []); true)
           | _ => false
       end)

val _ =
  let
    val x = Term.mk_var ("recorded_side_x", Type.bool)
    val y = Term.mk_var ("recorded_side_y", Type.bool)
    val p = Term.mk_var ("recorded_side_P", Type.bool --> Type.bool)
    val q = Term.mk_var ("recorded_side_Q", Type.bool --> Type.bool)
    fun app operator operand = Term.mk_comb (operator, operand)
    val goal = ([boolSyntax.mk_eq (x, y), app p x, app q y], app q y)
    val node = clasetGoal.from_goal goal
    fun exact expected results =
      case results of
          [(record, next)] =>
            (case rendered_goals next of
                 [(assumptions, conclusion)] =>
                   ListPair.allEq (fn (l, r) => Term.aconv l r)
                     (assumptions, #1 expected) andalso
                   Term.aconv conclusion (#2 expected) andalso
                   valid_open_replay goal (record, next)
               | _ => false)
        | _ => false
  in
    (* Both sides of this equality are substitutable, which is the state a
       metavariable binding made of the equality the search recorded its
       step against; the recorded side decides, not the left-first
       default. *)
    test
      ("a recorded hyp-subst side outranks the left-first orientation",
       fn () =>
         exact ([app q x, app p x], app q x)
           (drain_exact
             (clasetStep.blast_hyp_subst_step_at_in (Context.snapshot ())
               {equality = 1, changed = [false, true],
                side = clasetStep.EliminateRight}
               (node, 1))));
    test
      ("an unrecorded hyp-subst keeps the left-first orientation",
       fn () =>
         exact ([app p y, app q y], app q y)
           [hd (drain_exact
                 (clasetStep.blast_hyp_subst_step_in (Context.snapshot ())
                   (node, 1)))])
  end

val _ =
  test
    ("an unsubstitutable recorded hyp-subst side falls back to the other",
     fn () =>
       let
         val x = Term.mk_var ("fallback_side_x", Type.bool)
         val y = Term.mk_var ("fallback_side_y", Type.bool)
         val a = Term.mk_var ("fallback_side_a", Type.bool)
         val z = Term.mk_var ("fallback_side_z", Type.bool)
         val p = Term.mk_var ("fallback_side_P", Type.bool --> Type.bool)
         val q = Term.mk_var ("fallback_side_Q", Type.bool --> Type.bool)
         fun app operator operand = Term.mk_comb (operator, operand)
         val redex = app (Term.mk_abs (z, x)) a
         (* The search orients the beta-reduced equality and so records the
            left side; the goal keeps the redex, where only the right side
            is substitutable and the recorded preference cannot be met. *)
         val goal =
           ([boolSyntax.mk_eq (redex, y), app p x, app q y], app q y)
         val (children, validation) =
           clasetReplay.BLAST_HYP_SUBST_TAC_AT
             {position = 1, changed = [false, true],
              side = clasetReplay.EliminateLeft} goal
             (Context.snapshot())
         val expected = ([app q redex, app p x], app q redex)
         val child_ok =
           case children of
               [child] => same_goal (child, expected)
             | _ => false
         val replayed = validation [ASSUME (app q redex)]
       in
         child_ok andalso Term.aconv (concl replayed) (app q y)
       end)

val _ =
  test
    ("blast hyp-subst does not beta-normalize equality orientation",
     fn () =>
       let
         val x = Term.mk_var ("beta_x", Type.bool)
         val y = Term.mk_var ("beta_y", Type.bool)
         val a = Term.mk_var ("beta_a", Type.bool)
         val z = Term.mk_var ("beta_z", Type.bool)
         val p = Term.mk_var ("beta_P", Type.bool --> Type.bool)
         val q = Term.mk_var ("beta_Q", Type.bool --> Type.bool)
         fun app operator operand = Term.mk_comb (operator, operand)
         val redex = app (Term.mk_abs (z, x)) a
         val equality = boolSyntax.mk_eq (redex, y)
         val px = app p x
         val qy = app q y
         val goal = ([equality, px, qy], qy)
         val (children, validation) =
           clasetReplay.BLAST_HYP_SUBST_TAC goal (Context.snapshot())
         val expected = ([app q redex, px], app q redex)
         val child_ok =
           case children of
               [child] => same_goal (child, expected)
             | _ => false
         val theorem = ASSUME (app q redex)
         val replayed = validation [theorem]
       in
         child_ok andalso Term.aconv (concl replayed) qy
       end)

val _ =
  test
    ("recorded beta-redex hyp-subst and close replay exactly",
     fn () =>
       let
         val alpha = Type.mk_vartype "'beta_replay"
         val x = Term.mk_var ("beta_replay_x", alpha)
         val y = Term.mk_var ("beta_replay_y", alpha)
         val a = Term.mk_var ("beta_replay_a", alpha)
         val z = Term.mk_var ("beta_replay_z", alpha)
         val p = Term.mk_var ("beta_replay_P", alpha --> Type.bool)
         val redex = Term.mk_comb (Term.mk_abs (z, x), a)
         val goal =
           ([boolSyntax.mk_eq (redex, y), Term.mk_comb (p, y)],
            Term.mk_comb (p, redex))
         val root = clasetGoal.from_goal goal
         val (_, substituted) =
           case seq.cases
             (clasetStep.blast_hyp_subst_step_in (Context.snapshot ())
               (root, 1)) of
               SOME (result, _) => result
             | NONE => raise Fail "beta replay substitution"
         val (_, closed) =
           case seq.cases
             (clasetStep.blast_assumption_step (substituted, 1)) of
               SOME (result, _) => result
             | NONE => raise Fail "beta replay close"
         val grounded =
           clasetReplay.ground (clasetGoal.store closed)
             (clasetGoal.replay closed)
       in
         case total
           (Tactical.VALID (clasetReplay.REPLAY_TAC grounded)) goal of
             SOME ([], validation) =>
               let
                 val theorem = validation []
               in
                 Term.term_eq (concl theorem) (#2 goal) andalso
                 HOLset.equal
                   (Thm.hypset theorem,
                    HOLset.fromList Term.compare (#1 goal))
               end
           | _ => false
       end)

val _ =
  test
    ("recorded beta/eta target contradiction replay exactly",
     fn () =>
       let
         val alpha = Type.mk_vartype "'contradiction_replay"
         val x = Term.mk_var ("contradiction_replay_x", alpha)
         val a = Term.mk_var ("contradiction_replay_a", alpha)
         val z = Term.mk_var ("contradiction_replay_z", alpha)
         val f =
           Term.mk_var
             ("contradiction_replay_f", alpha --> Type.bool)
         val p = Term.mk_var ("contradiction_replay_p", Type.bool)
         val eta = Term.mk_abs (x, Term.mk_comb (f, x))
         val q = boolSyntax.mk_eq (eta, f)
         val target = Term.mk_comb (Term.mk_abs (z, q), a)
         val goal = ([boolSyntax.mk_neg p, p], target)
         val root = clasetGoal.from_goal goal
         val (_, closed) =
           case seq.cases
             (clasetStep.blast_contradiction_step (root, 1)) of
               SOME (result, _) => result
             | NONE => raise Fail "beta/eta contradiction close"
         val grounded =
           clasetReplay.ground (clasetGoal.store closed)
             (clasetGoal.replay closed)
       in
         case total
           (Tactical.VALID (clasetReplay.REPLAY_TAC grounded)) goal of
             SOME ([], validation) =>
               let
                 val theorem = validation []
               in
                 Term.term_eq (concl theorem) (#2 goal) andalso
                 HOLset.equal
                   (Thm.hypset theorem,
                    HOLset.fromList Term.compare (#1 goal))
               end
           | _ => false
       end)

(* Position-directed replay selectors are intentionally tested at this
   owning layer: duplicate syntax must not erase occurrence identity. *)

val _ =
  test
    ("exact intro sequences defer goal lookup until their first pull",
     fn () =>
       let
         val p = Term.mk_var ("exact_lazy_p", Type.bool)
         val theorem = Thm.ASSUME p
         val input = (clasetGoal.from_goal ([], p), 2)
         val specification = {theorem = theorem, elim = false}
         val ordinary =
           clasetStep.blast_rule_step clasetLib.empty_cs
             specification input
         val selected =
           clasetStep.blast_rule_step_at clasetLib.empty_cs
             {theorem = theorem, elim = false, major = NONE} input
       in
         seq.null ordinary andalso seq.null selected
       end)

val _ =
  test
    ("exact closure selectors preserve duplicate occurrence identity",
     fn () =>
       let
         val p = Term.mk_var ("exact_selector_p", Type.bool)
         val q = Term.mk_var ("exact_selector_q", Type.bool)
         val assumption_goal = ([p, p], p)
         val contradiction_goal =
           ([boolSyntax.mk_neg p, p, p], q)
         val assumption =
           drain_exact
             (clasetStep.blast_assumption_step_at 2
               (clasetGoal.from_goal assumption_goal, 1))
         val contradiction =
           drain_exact
             (clasetStep.blast_contradiction_step_at
               {negative = 1, positive = 3}
               (clasetGoal.from_goal contradiction_goal, 1))
         val wrong_assumption =
           seq.null
             (clasetStep.blast_assumption_step_at 1
               (clasetGoal.from_goal ([q, p], p), 1))
         val wrong_polarity =
           seq.null
             (clasetStep.blast_contradiction_step_at
               {negative = 2, positive = 1}
               (clasetGoal.from_goal contradiction_goal, 1))
       in
         case (assumption, contradiction) of
             ([(assumption_record, assumption_node)],
              [(contradiction_record, contradiction_node)]) =>
               clasetStep.consumed_of assumption_record = SOME 2 andalso
               (case clasetStep.kind_of assumption_record of
                    clasetStep.Assumption 2 => true
                  | _ => false) andalso
               (case clasetStep.kind_of contradiction_record of
                    clasetStep.Contradiction (1, 3) => true
                  | _ => false) andalso
               valid_grounded_replay assumption_goal assumption_node andalso
               valid_grounded_replay contradiction_goal
                 contradiction_node andalso
               wrong_assumption andalso wrong_polarity
           | _ => false
       end)

val _ =
  test
    ("strict assumption replay rejects selector drift while legacy recovers",
     fn () =>
       let
         val p = Term.mk_var ("strict_replay_p", Type.bool)
         val q = Term.mk_var ("strict_replay_q", Type.bool)
         val recorded_goal = ([q, p], p)
         val drifted_goal = ([p, q], p)
         val root = clasetGoal.from_goal recorded_goal
         val legacy =
           drain_exact (clasetStep.blast_assumption_step (root, 1))
         val strict =
           drain_exact
             (clasetStep.blast_assumption_step_at 2 (root, 1))
         fun grounded node =
           clasetReplay.ground (clasetGoal.store node)
             (clasetGoal.replay node)
         val legacy_result =
           case legacy of
               [(_, node)] =>
                 total
                   (Tactical.VALID
                     (clasetReplay.REPLAY_TAC (grounded node)))
                   drifted_goal
             | _ => NONE
         val strict_result =
           case strict of
               [(_, node)] => clasetReplay.replay_in (Context.snapshot ())
                                (grounded node) drifted_goal
             | _ => raise Fail "missing strict assumption transition"
       in
         (case legacy_result of
              SOME ([], validation) =>
                (ignore (validation []); true)
            | _ => false) andalso
         (case strict_result of
              clasetReplay.ReplayFailed _ => true
            | _ => false)
       end)

val _ =
  test
    ("exact rule selector validates shape range and nonmatching major",
     fn () =>
       let
         val p = Term.mk_var ("exact_shape_p", Type.bool)
         val q = Term.mk_var ("exact_shape_q", Type.bool)
         val bound = Term.mk_var ("exact_shape_x", Type.ind)
         val predicate =
           Term.mk_var ("exact_shape_P", Type.ind --> Type.bool)
         val major =
           boolSyntax.mk_exists
             (bound, Term.mk_comb (predicate, bound))
         val theorem = clasetSeedTheory.EXISTS_ELIM_THM
         val node = clasetGoal.from_goal ([q, major], p)
         fun empty specification =
           seq.null
             (clasetStep.blast_rule_step_at clasetLib.empty_cs
               specification (node, 1))
       in
         empty {theorem = theorem, elim = false, major = SOME 1}
         andalso empty {theorem = theorem, elim = true, major = NONE}
         andalso
         empty {theorem = theorem, elim = true, major = SOME 0}
         andalso
         empty {theorem = theorem, elim = true, major = SOME 3}
         andalso
         empty {theorem = theorem, elim = true, major = SOME 1}
       end)

val _ =
  test
    ("selected exact rule has ordinary and timed-family parity",
     fn () =>
       let
         val p = Term.mk_var ("exact_parity_p", Type.bool)
         val bound = Term.mk_var ("exact_parity_x", Type.ind)
         val predicate =
           Term.mk_var ("exact_parity_P", Type.ind --> Type.bool)
         val major =
           boolSyntax.mk_exists
             (bound, Term.mk_comb (predicate, bound))
         val goal = ([major, major], p)
         val result =
           drain_exact
             (clasetStep.blast_rule_step_at clasetLib.empty_cs
               {theorem = clasetSeedTheory.EXISTS_ELIM_THM,
                elim = true, major = SOME 2}
               (clasetGoal.from_goal goal, 1))
       in
         case result of
             [(record, node)] =>
               clasetStep.consumed_of record = SOME 2 andalso
               valid_open_replay goal (record, node)
           | _ => false
       end)


val _ =
  test
    ("selected blast hyp-subst uses only the recorded equality",
     fn () =>
       let
         val x = Term.mk_var ("exact_subst_x", Type.bool)
         val y = Term.mk_var ("exact_subst_y", Type.bool)
         val z = Term.mk_var ("exact_subst_z", Type.bool)
         val p = Term.mk_var ("exact_subst_P", Type.bool --> Type.bool)
         fun app argument = Term.mk_comb (p, argument)
         val first = boolSyntax.mk_eq (x, y)
         val selected = boolSyntax.mk_eq (y, z)
         val transformed_first = boolSyntax.mk_eq (x, z)
         val unchanged = app z
         val goal = ([first, selected, unchanged, app y], app y)
         val node = clasetGoal.from_goal goal
         val results =
           drain_exact
             (clasetStep.blast_hyp_subst_step_at_in (Context.snapshot ())
               {equality = 2, changed = [true, false, true],
                side = clasetStep.EliminateLeft}
               (node, 1))
         val wrong =
           seq.null
             (clasetStep.blast_hyp_subst_step_at_in (Context.snapshot ())
               {equality = 5, changed = [],
                side = clasetStep.EliminateLeft} (node, 1))
       in
         case results of
             [(record, next)] =>
               (case rendered_goals next of
                    [(assumptions, conclusion)] =>
                      List.exists (Term.aconv transformed_first)
                        assumptions andalso
                      List.exists (Term.aconv unchanged) assumptions andalso
                      not (List.exists (Term.aconv selected) assumptions)
                      andalso Term.aconv conclusion (app z) andalso
                      valid_open_replay goal (record, next) andalso wrong
                  | _ => false)
           | _ => false
       end)

val _ =
  test
    ("legacy closure and substitution enumeration keeps occurrence order",
     fn () =>
       let
         val p = Term.mk_var ("prepared_legacy_p", Type.bool)
         val q = Term.mk_var ("prepared_legacy_q", Type.bool)
         val assumption_goal = ([p, q, p], p)
         val assumption_node = clasetGoal.from_goal assumption_goal
         val assumptions =
           drain_exact
             (clasetStep.blast_assumption_step (assumption_node, 1))
         val selected_assumptions =
           List.concat
             (map
               (fn position =>
                 drain_exact
                   (clasetStep.blast_assumption_step_at position
                     (assumption_node, 1)))
               [1, 2, 3])
         val contradiction_goal = ([boolSyntax.mk_neg p, p, p], q)
         val contradictions =
           drain_exact
             (clasetStep.blast_contradiction_step
               (clasetGoal.from_goal contradiction_goal, 1))
         val x = Term.mk_var ("prepared_legacy_x", Type.bool)
         val y = Term.mk_var ("prepared_legacy_y", Type.bool)
         val z = Term.mk_var ("prepared_legacy_z", Type.bool)
         val predicate =
           Term.mk_var
             ("prepared_legacy_P", Type.bool --> Type.bool)
         val substitution_goal =
           ([boolSyntax.mk_eq (x, y), boolSyntax.mk_eq (y, z),
             Term.mk_comb (predicate, x)],
            Term.mk_comb (predicate, y))
         val substitution_node = clasetGoal.from_goal substitution_goal
         val substitutions =
           drain_exact
             (clasetStep.blast_hyp_subst_step_in (Context.snapshot ())
               (substitution_node, 1))
         val selected_substitutions =
           List.concat
             (map
               (fn (equality, changed) =>
                 drain_exact
                   (clasetStep.blast_hyp_subst_step_at_in
                     (Context.snapshot ())
                     {equality = equality, changed = changed,
                      side = clasetStep.EliminateLeft}
                     (substitution_node, 1)))
               [(1, [false, true]), (2, [true, false]), (3, [])])
         fun same_nodes ([], []) = true
           | same_nodes ((_, left) :: lefts, (_, right) :: rights) =
               clasetGoal.equal (left, right) andalso
               same_nodes (lefts, rights)
           | same_nodes _ = false
       in
         map (clasetStep.consumed_of o fst) assumptions =
           [SOME 1, SOME 3] andalso
         same_nodes (assumptions, selected_assumptions) andalso
         (case contradictions of
              [(record, _)] =>
                (case clasetStep.kind_of record of
                     clasetStep.Contradiction (1, 2) => true
                   | _ => false)
            | _ => false) andalso
         same_nodes (substitutions, selected_substitutions)
       end)

val _ =
  test
    ("unifying assumption resumes in occurrence order",
     fn () =>
       let
         val p = Term.mk_var ("assumption_order_p", Type.bool)
         val q = Term.mk_var ("assumption_order_q", Type.bool)
         val asl = [p, q, p]
         val (meta, store) =
           clasetMeta.new_meta {allow = [], ty = Type.bool} clasetMeta.empty
         val node = clasetGoal.create
           {goals = [{params = [], asl = asl, w = meta}],
            store = store, level = 0}
         val results = clasetStep.blast_assumption_step (node, 1)
         fun check (position, expected) (result as (record, next)) =
           case clasetStep.kind_of record of
               clasetStep.Assumption selected =>
                 let val instance = clasetMeta.norm (clasetGoal.store next) meta
                 in selected = position andalso Term.aconv instance expected
                    andalso valid_open_replay (asl, instance) result
                 end
             | _ => false
       in
         case seq.cases results of
             SOME (first, rest) =>
               check (1, p) first andalso
               ListPair.allEq (fn (expected, result) => check expected result)
                 ([(2, q), (3, p)], drain_exact rest)
           | NONE => false
       end)

val _ =
  test
    ("unifying contradiction prefers the first exact assumption",
     fn () =>
       let
         val p = Term.mk_var ("contradiction_match_p", Type.bool)
         val q = Term.mk_var ("contradiction_match_q", Type.bool)
         val negative = boolSyntax.mk_neg p
         val (meta, store) =
           clasetMeta.new_meta {allow = [], ty = Type.bool} clasetMeta.empty
         fun positive_positions asl =
           let
             val node = clasetGoal.create
               {goals = [{params = [], asl = asl, w = q}],
                store = store, level = 0}
             val results = drain_exact
               (clasetStep.blast_contradiction_step (node, 1))
           in
             List.mapPartial
               (fn (record, _) =>
                 case clasetStep.kind_of record of
                     clasetStep.Contradiction (2, position) => SOME position
                   | _ => NONE)
               results
           end
       in
         positive_positions [meta, negative, p, p] = [3] andalso
         positive_positions [meta, negative, meta] = [1, 3]
       end)

val _ =
  test
    ("unifying contradiction resumes in negative occurrence order",
     fn () =>
       let
         val p = Term.mk_var ("contradiction_order_p", Type.bool)
         val q = Term.mk_var ("contradiction_order_q", Type.bool)
         val r = Term.mk_var ("contradiction_order_r", Type.bool)
         val goal = ([p, boolSyntax.mk_neg q, q, boolSyntax.mk_neg p, q], r)
         val node = clasetGoal.from_goal goal
         val results = clasetStep.blast_contradiction_step (node, 1)
         fun check (negative, positive) (result as (record, _)) =
           case clasetStep.kind_of record of
               clasetStep.Contradiction (major, minor) =>
                 major = negative andalso minor = positive andalso
                 valid_open_replay goal result
             | _ => false
       in
         case seq.cases results of
             SOME (first, rest) =>
               check (2, 3) first andalso
               (case drain_exact rest of
                    [second] => check (4, 1) second
                  | _ => false)
           | NONE => false
       end)

(* Search work is reported to the shared meter, not just to the per-search
   counter the previous test reads. *)
val _ =
  test
    ("classical search charges the shared work meter",
     fn () =>
       let
         val goal =
           ([] : term list,
            boolSyntax.mk_imp
              (boolSyntax.mk_imp (goal_p, goal_q),
               boolSyntax.mk_imp
                 (boolSyntax.mk_neg goal_q, boolSyntax.mk_neg goal_p)))
         val (solved, work) =
           searchWork.measure
             (fn () =>
               case total (Tactical.VALID (classicalLib.BEST_TAC [])) goal of
                   SOME ([], validation) => (ignore (validation []); true)
                 | _ => false)
       in
         solved andalso #expansions work > 0
       end)

(* [IN] is a boolTheory constant, [IN = \x f. f x], so [x IN P] and [P x] are
   one proposition written two ways.  A rule stated in either spelling has to
   reach a goal stated in the other.  These goals are not benchmark goals. *)

val member_a = Term.mk_var ("member_a", Type.ind)
val member_x = Term.mk_var ("member_x", Type.ind)
val member_p = Term.mk_var ("member_p", Type.ind --> bool_ty)
val member_q = Term.mk_var ("member_q", Type.ind --> bool_ty)

fun member_in item set =
  Term.list_mk_comb
    (Term.inst [Type.alpha |-> Type.ind] boolSyntax.IN_tm, [item, set])

(* A set need not be a variable.  [member_fp] stands for the shape the
   translation writes for a set comprehension over a pair, [UNCURRY P],
   whose head is a constant and whose spelling therefore anchors on
   neither side: it is the position where the two directions of the
   crossing have to agree without a variable to agree on. *)
val member_f =
  Term.mk_var
    ("member_f", (Type.ind --> bool_ty) --> (Type.ind --> bool_ty))
val member_fp = mk_comb (member_f, member_p)

fun member_step implication goal expected =
  let
    val cs =
      clasetLib.add_sintros [("member-crossing", ASSUME implication)]
        clasetLib.empty_cs
  in
    case first_step safe_step cs goal of
        NONE => false
      | SOME (record, node) =>
          same_goals (rendered_goals node) [expected] andalso
          valid_step goal (record, node)
  end

val _ =
  test
    ("a rule stated with IN reaches an applied goal atom",
     fn () =>
       let
         val implication =
           boolSyntax.mk_forall
             (member_x,
              boolSyntax.mk_imp
                (mk_comb (member_q, member_x),
                 member_in member_x member_p))
         val goal = ([implication], mk_comb (member_p, member_a))
       in
         member_step implication goal
           ([implication], mk_comb (member_q, member_a))
       end)

val _ =
  test
    ("an applied rule reaches a goal atom stated with IN",
     fn () =>
       let
         val implication =
           boolSyntax.mk_forall
             (member_x,
              boolSyntax.mk_imp
                (member_in member_x member_q,
                 mk_comb (member_p, member_x)))
         val goal = ([implication], member_in member_a member_p)
       in
         member_step implication goal
           ([implication], member_in member_a member_q)
       end)

val _ =
  test
    ("an applied rule over a compound set reaches a goal atom stated with IN",
     fn () =>
       let
         val implication =
           boolSyntax.mk_forall
             (member_x,
              boolSyntax.mk_imp
                (mk_comb (member_q, member_x),
                 mk_comb (member_fp, member_x)))
         val goal = ([implication], member_in member_a member_fp)
       in
         member_step implication goal
           ([implication], mk_comb (member_q, member_a))
       end)

val _ =
  test
    ("a rule stated with IN over a compound set reaches an applied goal atom",
     fn () =>
       let
         val implication =
           boolSyntax.mk_forall
             (member_x,
              boolSyntax.mk_imp
                (mk_comb (member_q, member_x),
                 member_in member_x member_fp))
         val goal = ([implication], mk_comb (member_fp, member_a))
       in
         member_step implication goal
           ([implication], mk_comb (member_q, member_a))
       end)

(* A step states its children in the spelling the tactic that produced them
   returned, and the engine renders every goal reduced, so substituting an
   abstraction for a function variable leaves a child whose proof comes back
   beta-reduced while the step's own validation was built on the unreduced
   spelling.  The goal is not a corpus entry.

   Only the safe saturation is asserted: a complete search replays its
   record against the caller's own goal, so it reconstructs the unreduced
   spelling for itself and the boundary does not decide it. *)
local
  val redex_g = mk_var ("g", alpha --> bool)
  val redex_b = mk_var ("b", alpha)
  val redex_x = mk_var ("x", alpha)
  val redex_goal =
    ([] : term list,
     boolSyntax.list_mk_forall ([redex_g, redex_b],
       boolSyntax.mk_imp
         (boolSyntax.mk_eq (redex_g, mk_abs (redex_x, boolSyntax.T)),
          mk_comb (redex_g, redex_b))))
  fun closes tactic =
    case SelfTestTactical.VALID tactic redex_goal (Context.snapshot()) of
        ([], validation) => (ignore (validation []); true)
      | _ => false
in
val _ =
  test
    ("a substituted abstraction leaves a safe step its own spelling",
     fn () => closes (classicalLib.SAFE_TAC [boolTheory.TRUTH]))
end

(* The engine reduces the caller's goal on the way in, so a result assembled
   from its own validations proves the reduced goal and not the one the
   caller posed.  Both entry points that hand back engine goals directly are
   asserted; the complete-search drivers replay their record against the
   caller's goal and reconstruct the spelling for themselves.  The goal is
   not a corpus entry. *)
local
  val posed_b = mk_var ("b", alpha)
  val posed_x = mk_var ("x", alpha)
  val posed_goal =
    ([] : term list,
     boolSyntax.mk_forall
       (posed_b, mk_comb (mk_abs (posed_x, boolSyntax.T), posed_b)))
  fun closes tactic =
    case SelfTestTactical.VALID tactic posed_goal (Context.snapshot()) of
        ([], validation) => (ignore (validation []); true)
      | _ => false
in
val _ =
  test
    ("safe saturation proves the goal the caller posed",
     fn () => closes (classicalLib.SAFE_TAC [boolTheory.TRUTH]))

val _ =
  test
    ("a safe step proves the goal the caller posed",
     fn () =>
       closes
         (Tactical.REPEAT (classicalLib.SAFE_STEP_TAC [boolTheory.TRUTH])))
end

(* A plain citation must be available to safe inference even when its
   implication shape also admits an unsafe search-rule reading. *)
val _ = Theory.new_theory "classicalFactSelftest"

val _ = Datatype.Datatype
  `classical_clash_narrow =
   ClassicalClashN0 | ClassicalClashN1 | ClassicalClashN2 |
   ClassicalClashN3 | ClassicalClashN4 | ClassicalClashN5 |
   ClassicalClashN6 | ClassicalClashN7 | ClassicalClashN8 |
   ClassicalClashN9 | ClassicalClashN10 | ClassicalClashN11 |
   ClassicalClashN12 | ClassicalClashN13 | ClassicalClashN14`

val _ = Datatype.Datatype
  `classical_clash_wide =
   ClassicalClashW0 | ClassicalClashW1 | ClassicalClashW2 |
   ClassicalClashW3 | ClassicalClashW4 | ClassicalClashW5 |
   ClassicalClashW6 | ClassicalClashW7 | ClassicalClashW8 |
   ClassicalClashW9 | ClassicalClashW10 | ClassicalClashW11 |
   ClassicalClashW12 | ClassicalClashW13 | ClassicalClashW14 |
   ClassicalClashW15 num`

val _ = Datatype.Datatype
  `classical_clash_enum =
   ClassicalClashE0 | ClassicalClashE1 | ClassicalClashE2 |
   ClassicalClashE3 | ClassicalClashE4 | ClassicalClashE5 |
   ClassicalClashE6 | ClassicalClashE7 | ClassicalClashE8 |
   ClassicalClashE9 | ClassicalClashE10 | ClassicalClashE11 |
   ClassicalClashE12 | ClassicalClashE13 | ClassicalClashE14 |
   ClassicalClashE15`

val _ =
  test
    ("SAFE refutes narrow and wide constructor clashes without hints",
     fn () => List.all (fn equality =>
       let
         val (residues, validation) = Tactical.VALID
           (classicalLib.SAFE_TAC []) ([equality], ``p:bool``)
       in
         null residues andalso Term.aconv (concl (validation [])) ``p:bool``
       end)
       [``ClassicalClashN0 = ClassicalClashN14``,
        ``ClassicalClashW0 = ClassicalClashW15 n``,
        ``ClassicalClashW15 n = ClassicalClashW0``,
        ``ClassicalClashE0 = ClassicalClashE15``])

val _ =
  test
    ("FAST finds constructor witnesses through schematic clashes",
     fn () => List.all (fn target =>
       let
         val (residues, validation) =
           Tactical.VALID (classicalLib.FAST_TAC []) ([], target)
       in
         null residues andalso Term.aconv (concl (validation [])) target
       end)
       [``?x:classical_clash_wide. ClassicalClashW0 = x ==> p``,
        ``?x y:classical_clash_wide. x = y ==> p``])

val _ =
  test
    ("BEST finds constructor witnesses through schematic clashes",
     fn () => List.all (fn target =>
       let
         val (residues, validation) =
           Tactical.VALID (classicalLib.BEST_TAC []) ([], target)
       in
         null residues andalso Term.aconv (concl (validation [])) target
       end)
       [``?x:classical_clash_wide. ClassicalClashW0 = x ==> p``,
        ``?x y:classical_clash_wide. x = y ==> p``])

val _ =
  test
    ("FAST refutes narrow and wide constructor clashes without hints",
     fn () => List.all (fn equality =>
       let
         val (residues, validation) = Tactical.VALID
           (classicalLib.FAST_TAC []) ([equality], ``p:bool``)
       in
         null residues andalso Term.aconv (concl (validation [])) ``p:bool``
       end)
       [``ClassicalClashN0 = ClassicalClashN14``,
        ``ClassicalClashW0 = ClassicalClashW15 n``,
        ``ClassicalClashW15 n = ClassicalClashW0``,
        ``ClassicalClashE0 = ClassicalClashE15``])

val _ =
  test
    ("BEST refutes narrow and wide constructor clashes without hints",
     fn () => List.all (fn equality =>
       let
         val (residues, validation) = Tactical.VALID
           (classicalLib.BEST_TAC []) ([equality], ``p:bool``)
       in
         null residues andalso Term.aconv (concl (validation [])) ``p:bool``
       end)
       [``ClassicalClashN0 = ClassicalClashN14``,
        ``ClassicalClashW0 = ClassicalClashW15 n``,
        ``ClassicalClashW15 n = ClassicalClashW0``,
        ``ClassicalClashE0 = ClassicalClashE15``])

val _ =
  test
    ("SAFE refuses a rigid equality between datatype-valued applications",
     fn () =>
       let
         val equality = ``(f:classical_clash_wide -> classical_clash_wide) x
                           = g y``
         val goal = ([equality], ``p:bool``)
       in
         tactic_error_message (classicalLib.SAFE_TAC []) goal =
           SOME "no change"
       end)

val safe_fact_q_def =
  new_definition
    ("safe_fact_q_def", ``safe_fact_q (x:'a) <=> T``)
val safe_implication_fact =
  Tactical.prove
    (``!x:'a. safe_fact_p x ==> safe_fact_q x``,
     Rewrite.REWRITE_TAC [safe_fact_q_def])
val safe_fact_goal =
  ([``safe_fact_p (a:'a):bool``], ``safe_fact_q (a:'a)``)

fun safe_fact_residual tactic =
  SOME (#1 (Tactical.VALID tactic safe_fact_goal))
    handle HOL_ERR _ => NONE

val _ =
  test
    ("the conditional fact fixture has a visible insertion control",
     fn () =>
       let
         val inserted =
           safe_fact_residual
             (Tactical.THEN
               (Tactic.ASSUME_TAC safe_implication_fact,
                Tactical.TRY (classicalLib.SAFE_TAC [])))
       in
         case inserted of
             SOME [(assumptions, _)] =>
               List.exists
                 (fn assumption =>
                   aconv assumption (concl safe_implication_fact))
                 assumptions
           | _ => false
       end)

val _ =
  test
    ("SAFE_TAC retains a supplied conditional fact",
     fn () =>
       let
         val explicit =
           safe_fact_residual
             (Tactical.THEN
               (Tactic.ASSUME_TAC safe_implication_fact,
                Tactical.TRY (classicalLib.SAFE_TAC [])))
         val supplied =
           safe_fact_residual
             (classicalLib.SAFE_TAC [safe_implication_fact])
       in
         case (explicit, supplied) of
             (SOME left, SOME right) =>
               not (null left) andalso same_goals left right
           | _ => false
       end)

val _ =
  test
    ("CLARIFY_TAC retains a supplied conditional fact",
     fn () =>
       let
         val explicit =
           safe_fact_residual
             (Tactical.THEN
               (Tactic.ASSUME_TAC safe_implication_fact,
                Tactical.TRY (classicalLib.CLARIFY_TAC [])))
         val supplied =
           safe_fact_residual
             (classicalLib.CLARIFY_TAC [safe_implication_fact])
       in
         case (explicit, supplied) of
             (SOME left, SOME right) =>
               not (null left) andalso same_goals left right
           | _ => false
       end)

val _ =
  test
    ("safe methods do not invent a conditional fact's premise",
     fn () =>
       let
         val target = ``safe_fact_q (a:'a)``
         val goal = ([], target)
         fun residual tactic =
           SOME (#1 (Tactical.VALID tactic goal))
             handle HOL_ERR _ => NONE
         fun open_target outcome =
           case outcome of
               SOME [(assumptions, remaining)] =>
                 aconv remaining target andalso
                 List.exists
                   (fn assumption =>
                     aconv assumption (concl safe_implication_fact))
                   assumptions
             | _ => false
       in
         open_target
           (residual
             (classicalLib.SAFE_TAC [safe_implication_fact])) andalso
         open_target
           (residual
             (classicalLib.CLARIFY_TAC [safe_implication_fact]))
       end)

val _ =
  test
    ("search can use a conditional citation beneath an antecedent",
     fn () =>
       let
         val result = ``safe_fact_result:bool``
         val goal =
           ([boolSyntax.mk_imp
               (concl safe_implication_fact, result)],
            result)
         fun closes tactic =
           null (#1 (Tactical.VALID tactic goal))
             handle HOL_ERR _ => false
       in
         not (closes (classicalLib.FAST_TAC [])) andalso
         closes (classicalLib.FAST_TAC [safe_implication_fact])
       end)

val _ =
  test
    ("budgeted first-best preserves a proof pending kernel replay",
     fn () =>
       let
         val p = mk_var ("budgeted_classical_p", bool_ty)
         val target = boolSyntax.mk_imp (p, p)
         val budget =
           searchBudget.create
             {candidates = NONE, applications = NONE,
              normalization = SOME 0}
         val session =
           classicalLib.CS_FIRST_BEST_SESSION budget
             clasetLib.empty_cs ([], target) (Context.snapshot())
         val first = classicalLib.RESUME_FIRST_BEST_SESSION session
         val used_before = searchBudget.usage budget
         val _ = searchBudget.extend budget searchBudget.Normalization 1
         val second = classicalLib.RESUME_FIRST_BEST_SESSION session
         val used_after = searchBudget.usage budget
       in
         (case first of
              classicalLib.BudgetYielded
                {kind = searchBudget.Normalization, usage, ...} =>
                  #normalization usage = 0
            | _ => false) andalso
         (case second of
              classicalLib.BudgetProved
                {result = (remaining, validate), ...} =>
                  null remaining andalso
                  Term.aconv (Thm.concl (validate [])) target
            | _ => false) andalso
         #candidates used_before = #candidates used_after andalso
         #applications used_before = #applications used_after andalso
         #normalization used_after = 1
       end)

val _ =
  test
    ("budgeted first-best separates exhaustion from a work yield",
     fn () =>
       let
         val p = mk_var ("budgeted_classical_open_p", bool_ty)
         val ctxt = Context.snapshot ()
         val empty_budget =
           searchBudget.create
             {candidates = NONE, applications = SOME 0,
              normalization = NONE}
         val yielded =
           classicalLib.RESUME_FIRST_BEST_SESSION
             (classicalLib.CS_FIRST_BEST_SESSION empty_budget
               clasetLib.empty_cs ([], boolSyntax.mk_imp (p, p))
               ctxt)
         val exhausted =
           classicalLib.RESUME_FIRST_BEST_SESSION
             (classicalLib.CS_FIRST_BEST_SESSION
               (searchBudget.unbounded ()) clasetLib.empty_cs
               ([], p) ctxt)
       in
         (case yielded of
              classicalLib.BudgetYielded
                {kind = searchBudget.Application, usage, ...} =>
                  #applications usage = 0
            | _ => false) andalso
         (case exhausted of
              classicalLib.BudgetExhausted => true
            | _ => false)
       end)

val _ =
  test
    ("budgeted depth charges its stage before safe saturation",
     fn () =>
       let
         val p = mk_var ("budgeted_depth_p", bool_ty)
         val goal = ([], boolSyntax.mk_imp (p, p))
         val ctxt = Context.snapshot ()
         val zero =
           searchBudget.create
             {candidates = NONE, applications = SOME 0,
              normalization = NONE}
         val no_candidates =
           searchBudget.create
             {candidates = SOME 0, applications = NONE,
              normalization = NONE}
         val candidate_cutoff =
           (ignore
              (classicalLib.CS_DEPTH_SOLVE_TAC_BUDGETED no_candidates
                 {dup = false} 1 clasetLib.empty_cs goal ctxt);
            false)
           handle searchBudget.LimitReached
                    (searchBudget.Candidate, used) =>
                    #candidates used = 0
                | _ => false
         val cutoff =
           (ignore
              (classicalLib.CS_DEPTH_SOLVE_TAC_BUDGETED zero
                 {dup = false} 1 clasetLib.empty_cs goal ctxt);
            false)
           handle searchBudget.LimitReached
                    (searchBudget.Application, used) =>
                    #applications used = 0
                | _ => false
         val funded = searchBudget.unbounded ()
         val (remaining, _) =
           Tactical.VALID
             (classicalLib.CS_DEPTH_SOLVE_TAC_BUDGETED funded
                {dup = false} 1 clasetLib.empty_cs)
             goal
       in
         cutoff andalso candidate_cutoff andalso null remaining andalso
         #applications (searchBudget.usage funded) > 0
       end)

val _ =
  test
    ("depth session keeps a candidate pending kernel replay",
     fn () =>
       let
         val p = mk_var ("depth_replay_p", bool_ty)
         val goal = ([], boolSyntax.mk_imp (p, p))
         val budget =
           searchBudget.create
             {candidates = NONE, applications = NONE,
              normalization = SOME 0}
         val session =
           classicalLib.CS_DEPTH_SESSION budget
             {dup = false} 1 clasetLib.empty_cs goal
             (Context.snapshot ())
         val first = classicalLib.RESUME_DEPTH_SESSION session
         val _ = searchBudget.extend budget searchBudget.Normalization 1
         val second = classicalLib.RESUME_DEPTH_SESSION session
       in
         (case first of
              classicalLib.DepthYielded
                {kind = searchBudget.Normalization, usage, ...} =>
                  #normalization usage = 0
            | _ => false) andalso
         (case second of
              classicalLib.DepthProved
                {result = (remaining, validate), ...} =>
                  null remaining andalso
                  Term.aconv (Thm.concl (validate [])) (#2 goal)
            | _ => false)
       end)

val _ =
  test
    ("small depth resumes retain a proof under one budget",
     fn () =>
       let
         val (cs, goal) = depth_duplication_fixture ()
         val budget =
           searchBudget.create
             {candidates = SOME 0, applications = SOME 0,
              normalization = SOME 0}
         val session =
           classicalLib.CS_DEPTH_SESSION budget
             {dup = true} 3 cs goal (Context.snapshot ())
         fun finish 0 _ = false
           | finish remaining yields =
               case classicalLib.RESUME_DEPTH_SESSION session of
                   classicalLib.DepthYielded {kind, ...} =>
                     (searchBudget.extend budget kind 1;
                      finish (remaining - 1) (yields + 1))
                 | classicalLib.DepthProved
                     {result = (residual, validate), ...} =>
                     yields > 1 andalso null residual andalso
                     Term.aconv (Thm.concl (validate [])) (#2 goal)
                 | classicalLib.DepthExhausted => false
       in
         finish 2000 0
       end)

(* Lazy constructor pairs under a budget.  Each test has an enumeration
   of its own, so its pairs start underived; [clash_goal] reaches the
   lookup of an assumption ?x = ?y through two universal eliminations. *)
val clash_size = 10
val clash_pairs = clash_size * (clash_size - 1)

fun clash_enum tyop prefix =
  let
    val constructors =
      List.tabulate (clash_size, fn i => prefix ^ Int.toString i)
    val _ = Datatype.Datatype
      [QUOTE (tyop ^ " = " ^ String.concatWith " | " constructors)]
  in
    mk_thy_type {Thy = current_theory (), Tyop = tyop, Args = []}
  end

val pair_first_ty = clash_enum "classical_pair_first" "ClassicalPairFirst"
val pair_depth_ty = clash_enum "classical_pair_depth" "ClassicalPairDepth"
val pair_zero_ty = clash_enum "classical_pair_zero" "ClassicalPairZero"
val pair_resume_ty = clash_enum "classical_pair_resume" "ClassicalPairResume"
val pair_cut_ty = clash_enum "classical_pair_cut" "ClassicalPairCut"
val pair_turns_ty = clash_enum "classical_pair_turns" "ClassicalPairTurns"
val pair_rigid_ty = clash_enum "classical_pair_rigid" "ClassicalPairRigid"
val pair_meta_ty = clash_enum "classical_pair_meta" "ClassicalPairMeta"

fun clash_goal ty =
  let
    val x = mk_var ("x", ty)
    val y = mk_var ("y", ty)
  in
    ([] : term list,
     boolSyntax.mk_imp
       (boolSyntax.list_mk_forall ([x, y], boolSyntax.mk_eq (x, y)),
        mk_var ("clash_p", bool)))
  end

(* A lookup polls once per branch of each pair it derives, beyond the
   polls it makes for every pair.  Counting derives the remaining pairs. *)
fun underived_pairs ty =
  let
    val equality = boolSyntax.mk_eq (mk_var ("x", ty), mk_var ("y", ty))
    fun polls () =
      let
        val count = ref 0
      in
        ignore
          (clasetLib.unify_elim_candidates_measured
             (fn () => count := !count + 1)
             (clasetLib.safe0_part (clasetLib.the_claset ())) equality);
        !count
      end
    val cold = polls ()
  in
    (cold - polls ()) div clash_size
  end

fun candidate_budget limit =
  searchBudget.create
    {candidates = limit, applications = NONE, normalization = NONE}

fun charge_candidate budget () =
  searchBudget.charge budget searchBudget.Candidate

fun first_best_session budget goal =
  classicalLib.CS_FIRST_BEST_SESSION budget (clasetLib.the_claset ())
    goal (Context.snapshot ())

fun proves (goal : term list * term) (remaining, validate) =
  null remaining andalso Term.aconv (Thm.concl (validate [])) (#2 goal)

(* Usage of a proof, or NONE without one. *)
fun first_best_usage goal =
  let
    val budget = candidate_budget NONE
  in
    case classicalLib.RESUME_FIRST_BEST_SESSION
           (first_best_session budget goal) of
        classicalLib.BudgetProved {result, ...} =>
          if proves goal result then SOME (searchBudget.usage budget)
          else NONE
      | _ => NONE
  end

fun depth_usage goal =
  let
    val budget = candidate_budget NONE
    val (remaining, validate) =
      Tactical.VALID
        (classicalLib.CS_DEPTH_SOLVE_TAC_BUDGETED budget {dup = false} 2
           (clasetLib.the_claset ()))
        goal
  in
    if proves goal (remaining, validate) then
      SOME (searchBudget.usage budget)
    else NONE
  end

val first_best_pair_usage =
  let
    val goal = clash_goal pair_first_ty
  in
    (first_best_usage goal, first_best_usage goal)
  end

val depth_pair_usage =
  let
    val goal = clash_goal pair_depth_ty
  in
    (depth_usage goal, depth_usage goal)
  end

val _ =
  test
    ("first-best charges a candidate per constructor pair it derives",
     fn () =>
       case first_best_pair_usage of
           (SOME cold, SOME warm) =>
             #candidates cold - #candidates warm = clash_pairs
         | _ => false)

val _ =
  test
    ("budgeted depth charges a candidate per constructor pair it derives",
     fn () =>
       case depth_pair_usage of
           (SOME cold, SOME warm) =>
             #candidates cold - #candidates warm = clash_pairs
         | _ => false)

val _ =
  test
    ("a pair lookup against no candidates derives no pair",
     fn () =>
       let
         val ty = pair_zero_ty
         val ctxt = Context.snapshot ()
         val cs = clasetLib.the_claset ()
         fun first_child node =
           case seq.cases (clasetStep.step_in ctxt cs (node, 1)) of
               SOME ((_, child), _) => child
             | NONE => raise Fail "expected a classical step"
         val node =
           first_child (first_child (first_child
             (clasetGoal.from_goal (clash_goal ty))))
         val zero = candidate_budget (SOME 0)
         val cut =
           (ignore
              (seq.cases
                 (clasetStep.step_in_with (charge_candidate zero) ctxt cs
                    (node, 1)));
            false)
           handle searchBudget.LimitReached
                    (searchBudget.Candidate, used) =>
                    #candidates used = 0
       in
         List.exists boolSyntax.is_eq (#1 (clasetGoal.render node 1))
         andalso cut andalso underived_pairs ty = clash_pairs
       end)

val _ =
  test
    ("first-best resumes a cut pair lookup one candidate at a time",
     fn () =>
       case first_best_pair_usage of
           (SOME cold, SOME _) =>
             let
               (* Every candidate is a cut, so some land inside the
                  lookup. *)
               val goal = clash_goal pair_resume_ty
               val budget = candidate_budget (SOME 0)
               val session = first_best_session budget goal
               fun finish yields =
                 if yields > #candidates cold then false
                 else
                   case classicalLib.RESUME_FIRST_BEST_SESSION session of
                       classicalLib.BudgetYielded
                         {kind = searchBudget.Candidate, ...} =>
                         (searchBudget.extend budget searchBudget.Candidate 1;
                          finish (yields + 1))
                     | classicalLib.BudgetProved {result, ...} =>
                         yields > 1 andalso proves goal result andalso
                         searchBudget.usage budget = cold
                     | _ => false
             in
               finish 0
             end
         | _ => false)

val _ =
  test
    ("budgeted depth cuts a pair lookup and keeps the pairs it derived",
     fn () =>
       case depth_pair_usage of
           (SOME _, SOME warm) =>
             let
               val ty = pair_cut_ty
               val budget =
                 candidate_budget
                   (SOME (#candidates warm + clash_pairs div 2))
               val cut =
                 (ignore
                    (classicalLib.CS_DEPTH_SOLVE_TAC_BUDGETED budget
                       {dup = false} 2 (clasetLib.the_claset ())
                       (clash_goal ty) (Context.snapshot ()));
                  false)
                 handle searchBudget.LimitReached
                          (searchBudget.Candidate, _) => true
               val underived = underived_pairs ty
             in
               cut andalso 0 < underived andalso underived < clash_pairs
             end
         | _ => false)

val _ =
  test
    ("a depth session resumes a cut pair lookup one candidate at a time",
     fn () =>
       case depth_pair_usage of
           (SOME cold, SOME warm) =>
             let
               (* Every candidate from [warm] on is a cut; the test
                  above shows one inside the lookup. *)
               val goal = clash_goal pair_turns_ty
               val budget = candidate_budget (SOME (#candidates warm))
               val session =
                 classicalLib.CS_DEPTH_SESSION budget {dup = false} 2
                   (clasetLib.the_claset ()) goal (Context.snapshot ())
               fun finish yields =
                 if yields > clash_pairs then false
                 else
                   case classicalLib.RESUME_DEPTH_SESSION session of
                       classicalLib.DepthYielded
                         {kind = searchBudget.Candidate, ...} =>
                         (searchBudget.extend budget searchBudget.Candidate 1;
                          finish (yields + 1))
                     | classicalLib.DepthProved {result, ...} =>
                         let
                           val used = searchBudget.usage budget
                         in
                           (* The session also charges its replay. *)
                           yields > 1 andalso proves goal result andalso
                           #candidates used = #candidates cold andalso
                           #applications used = #applications cold
                         end
                     | _ => false
             in
               finish 0
             end
         | _ => false)

val _ =
  test
    ("a rigid type variable enumerates no constructor pairs",
     fn () =>
       let
         val ty = pair_rigid_ty
         val _ =
           ignore
             (classicalLib.CS_DEPTH_SOLVE_TAC_BUDGETED (candidate_budget NONE)
                {dup = false} 2 (clasetLib.the_claset ())
                (clash_goal (mk_vartype "'a")) (Context.snapshot ()))
           handle HOL_ERR _ => ()
       in
         underived_pairs ty = clash_pairs
       end)

val _ =
  test
    ("a type metavariable still enumerates constructor pairs",
     fn () =>
       let
         val ty = pair_meta_ty
         val {Thy, Tyop, ...} = dest_thy_type ty
         val own = "__claset_tyinfo_" ^ Thy ^ "_" ^ Tyop ^ "_distinct"
         val all = clasetLib.the_claset ()
         val only_own =
           List.foldl
             (fn (name, cs) =>
                if name = own then cs else clasetLib.remove_rule name cs)
             (List.foldl
                (fn ((_, (name, _)), cs) => clasetLib.remove_rule name cs)
                all (clasetLib.rules_of all))
             (clasetLib.distinct_rule_names all)
         val (tymeta, _) = clasetMeta.new_tymeta clasetMeta.empty
         fun lookup alpha =
           let
             val x = mk_var ("x", alpha)
             val y = mk_var ("y", alpha)
             val equality = boolSyntax.mk_eq (x, y)
           in
             length
               (clasetLib.unify_elim_candidates_with
                  {checkpoint = listUtil.no_checkpoint,
                   derive = listUtil.no_checkpoint}
                  (clasetLib.safe0_part only_own) equality
                  {q = equality, qvars = HOLset.fromList Term.compare [x, y],
                   flexible_type = clasetMeta.is_tymeta})
           end
       in
         List.exists (fn name => name = own)
           (clasetLib.distinct_rule_names all) andalso
         lookup tymeta = clash_pairs andalso
         lookup (mk_vartype "'a") = 0
       end)

val safe_context_slot =
  Context.Data.new
    {name = "classical-safe-explicit-context", empty = 0,
     pp = Int.toString}

val _ =
  test
    ("safe wrappers receive the explicit tactic context",
     fn () =>
       let
         val ctxt =
           Context.Data.put safe_context_slot 1 (Context.snapshot ())
         val seen = ref ([] : int list)
         fun observe base goal current =
           (seen := Context.Data.get safe_context_slot current :: !seen;
            base goal current)
         val cs =
           clasetLib.add_safe_wrapper ("observe-context", observe)
             clasetLib.empty_cs
         val p = mk_var ("safe_context_p", bool_ty)
         val goal = ([], boolSyntax.mk_imp (p, p))
       in
         case seq.cases (classicalLib.CS_SAFE_STEP_TAC cs goal ctxt) of
             SOME (_, _) =>
               not (null (!seen)) andalso
               List.all (fn value => value = 1) (!seen)
           | NONE => false
       end)

val _ =
  test
    ("FAST_TAC gives an unsafe wrapper its explicit context",
     fn () =>
       let
         val ctxt =
           Context.Data.put safe_context_slot 2 (Context.snapshot ())
         val seen = ref ([] : int list)
         val p = mk_var ("unsafe_context_p", bool_ty)
         val theorem = DISJ1 boolTheory.TRUTH p
         val goal = ([], Thm.concl theorem)
         fun observe base target current =
           (seen := Context.Data.get safe_context_slot current :: !seen;
            NTactical.NORELSE
              (NTactical.LIFT (Tactic.ACCEPT_TAC theorem), base)
              target current)
         val cs =
           clasetLib.add_unsafe_wrapper ("observe-context", observe)
             clasetLib.empty_cs
         val safe_only =
           null
             (clasetStep.safe_saturation_in (Context.snapshot ())
               clasetLib.empty_cs (clasetGoal.from_goal goal))
       in
         safe_only andalso
         (case seq.cases (classicalLib.CS_FAST_TAC cs goal ctxt) of
              SOME (_, _) =>
                not (null (!seen)) andalso
                List.all (fn value => value = 2) (!seen)
            | NONE => false)
       end)

val _ =
  test
    ("bounded depth search gives wrappers its explicit context",
     fn () =>
       let
         val ctxt =
           Context.Data.put safe_context_slot 3 (Context.snapshot ())
         val seen = ref ([] : int list)
         val p = mk_var ("depth_context_p", bool_ty)
         val theorem = DISJ1 boolTheory.TRUTH p
         val goal = ([], Thm.concl theorem)
         fun observe base target current =
           (seen := Context.Data.get safe_context_slot current :: !seen;
            NTactical.NORELSE
              (NTactical.LIFT (Tactic.ACCEPT_TAC theorem), base)
              target current)
         val cs =
           clasetLib.add_unsafe_wrapper ("observe-depth-context", observe)
             clasetLib.empty_cs
       in
         case seq.cases
                (classicalLib.CS_DEPTH_SOLVE_TAC {dup = false} 2 cs
                   goal ctxt) of
             SOME (_, _) =>
               not (null (!seen)) andalso
               List.all (fn value => value = 3) (!seen)
           | NONE => false
       end)

val _ =
  test
    ("interleaved first-best sessions retain explicit contexts",
     fn () =>
       let
         val ambient = Context.snapshot ()
         val first_ctxt = Context.Data.put safe_context_slot 4 ambient
         val second_ctxt = Context.Data.put safe_context_slot 5 ambient
         val seen = ref ([] : int list)
         val p = mk_var ("session_context_p", bool_ty)
         val theorem = DISJ1 boolTheory.TRUTH p
         val goal = ([], Thm.concl theorem)
         fun observe base target current =
           (seen := Context.Data.get safe_context_slot current :: !seen;
            NTactical.NORELSE
              (NTactical.LIFT (Tactic.ACCEPT_TAC theorem), base)
              target current)
         val cs =
           clasetLib.add_unsafe_wrapper ("session-context", observe)
             clasetLib.empty_cs
         fun meter () =
           searchBudget.create
             {candidates = SOME 0, applications = NONE,
              normalization = NONE}
         val first_budget = meter ()
         val second_budget = meter ()
         val first =
           classicalLib.CS_FIRST_BEST_SESSION first_budget cs goal
             first_ctxt
         val second =
           classicalLib.CS_FIRST_BEST_SESSION second_budget cs goal
             second_ctxt
         fun yielded session =
           case classicalLib.RESUME_FIRST_BEST_SESSION session of
               classicalLib.BudgetYielded
                 {kind = searchBudget.Candidate, ...} => true
             | _ => false
         fun proved session =
           case classicalLib.RESUME_FIRST_BEST_SESSION session of
               classicalLib.BudgetProved
                 {result = ([], validation), ...} =>
                   Term.aconv (Thm.concl (validation [])) (#2 goal)
             | _ => false
       in
         yielded first andalso yielded second andalso
         (searchBudget.extend first_budget searchBudget.Candidate 100;
          searchBudget.extend second_budget searchBudget.Candidate 100;
          proved second andalso
          not (null (!seen)) andalso
          List.all (fn value => value = 5) (!seen) andalso
          proved first andalso
          List.exists (fn value => value = 4) (!seen) andalso
          List.all (fn value => value = 4 orelse value = 5) (!seen))
       end)

val _ =
  test
    ("kernel replay passes its explicit context to recorded actions",
     fn () =>
       let
         val ctxt =
           Context.Data.put safe_context_slot 6 (Context.snapshot ())
         val seen = ref ([] : int list)
         fun action _ goal current =
           (seen := Context.Data.get safe_context_slot current :: !seen;
            Tactic.ACCEPT_TAC boolTheory.TRUTH goal current)
         val record =
           clasetReplay.make_record
             {kind = clasetReplay.Wrapper, target = 1,
              consumed = NONE, created = {terms = [], types = []},
              eigenvariables = [],
              validation = (fn _ => boolTheory.TRUTH),
              action = action, children = []}
         val script =
           clasetReplay.append (clasetReplay.empty 1) record
         val grounded = clasetReplay.ground clasetMeta.empty script
       in
         case SelfTestTactical.VALID
                (clasetReplay.REPLAY_TAC grounded)
                ([], boolSyntax.T) ctxt of
             ([], validation) =>
               Term.aconv (Thm.concl (validation [])) boolSyntax.T
                 andalso !seen = [6]
           | _ => false
       end)

val _ =
  test
    ("recursive replay keeps the same context for child actions",
     fn () =>
       let
         val ctxt =
           Context.Data.put safe_context_slot 7 (Context.snapshot ())
         val seen = ref ([] : int list)
         fun close _ goal current =
           (seen := Context.Data.get safe_context_slot current :: !seen;
            Tactic.ACCEPT_TAC boolTheory.TRUTH goal current)
         val leaf =
           clasetReplay.make_record
             {kind = clasetReplay.Wrapper, target = 1,
              consumed = NONE, created = {terms = [], types = []},
              eigenvariables = [],
              validation = (fn _ => boolTheory.TRUTH),
              action = close, children = []}
         val parent =
           clasetReplay.make_record
             {kind = clasetReplay.Wrapper, target = 1,
              consumed = NONE, created = {terms = [], types = []},
              eigenvariables = [[], []],
              validation = (fn _ => boolTheory.TRUTH),
              action = fn _ => Tactic.CONJ_TAC,
              children = [SOME leaf, SOME leaf]}
         val script =
           clasetReplay.append (clasetReplay.empty 1) parent
         val grounded = clasetReplay.ground clasetMeta.empty script
         val target = boolSyntax.mk_conj (boolSyntax.T, boolSyntax.T)
       in
         case SelfTestTactical.VALID
                (clasetReplay.REPLAY_TAC grounded) ([], target) ctxt of
             ([], validation) =>
               Term.aconv (Thm.concl (validation [])) target andalso
               !seen = [7, 7]
           | _ => false
       end)

val _ =
  test
    ("editing a replay frontier preserves siblings and earlier scripts",
     fn () =>
       let
         open clasetReplay
         val ctxt = Context.snapshot ()
         val p = Term.mk_var ("replay_p", Type.bool)
         val q = Term.mk_var ("replay_q", Type.bool)
         val r = Term.mk_var ("replay_r", Type.bool)
         val target = boolSyntax.mk_conj (p, boolSyntax.mk_conj (q, r))
         val goal = ([p, q, r], target)
         fun record kind target action children =
           make_record
             {kind = kind, target = target, consumed = NONE,
              created = {terms = [], types = []}, eigenvariables = [],
              validation = (fn _ => raise Fail "use the replay action"),
              action = fn _ => action, children = children}
         fun split position children =
           record Wrapper position Tactic.CONJ_TAC children
         fun close position tm =
           record (Assumption position) position
             (Tactic.ACCEPT_TAC (Thm.ASSUME tm)) []
         val first =
           append (empty 1)
             (split 1 [NONE, SOME (split 1 [NONE, NONE])])
         val last = append first (close 3 r)
         val left = append last (close 1 p)
         val middle = append last (close 2 q)
         fun matches script residuals =
           case replay_in ctxt (ground clasetMeta.empty script) goal of
               Replayed (goals, validate) =>
                 ListPair.allEq
                   (fn ((_, tm), expected) => Term.aconv tm expected)
                   (goals, residuals) andalso
                 Term.aconv (Thm.concl (validate (map Thm.ASSUME residuals)))
                   target
             | ReplayFailed _ => false
         fun rejects script position =
           ((ignore (append script (close position p)); false)
            handle Feedback.HOL_ERR _ => true)
         val two_roots = append (empty 2) (close 2 p)
       in
         matches first [p, q, r] andalso matches last [p, q] andalso
         matches left [q] andalso matches middle [p] andalso
         length left = 3 andalso
         to_string two_roots = "open\n2: assumption 2" andalso
         rejects first 0 andalso rejects first 4 andalso
         rejects (append left (close 1 q)) 1
       end)

val _ =
  test
    ("an interrupt in a recorded action escapes replay",
     fn () =>
       let
         val record =
           clasetReplay.make_record
             {kind = clasetReplay.Wrapper, target = 1,
              consumed = NONE, created = {terms = [], types = []},
              eigenvariables = [],
              validation = (fn _ => boolTheory.TRUTH),
              action = fn _ => fn _ => fn _ =>
                raise Portable.Interrupt,
              children = []}
         val script =
           clasetReplay.append (clasetReplay.empty 1) record
         val grounded = clasetReplay.ground clasetMeta.empty script
       in
         ((ignore
             (clasetReplay.REPLAY_TAC grounded
               ([], boolSyntax.T) (Context.snapshot ()));
           false)
          handle Portable.Interrupt => true
               | Feedback.HOL_ERR _ => false)
       end)

val _ =
  test
    ("a shared work cutoff in a recorded action escapes replay",
     fn () =>
       let
         val meter =
           searchBudget.create
             {candidates = SOME 0, applications = NONE,
              normalization = NONE}
         fun action _ goal ctxt =
           (searchBudget.charge meter searchBudget.Candidate;
            Tactic.ACCEPT_TAC boolTheory.TRUTH goal ctxt)
         val record =
           clasetReplay.make_record
             {kind = clasetReplay.Wrapper, target = 1,
              consumed = NONE, created = {terms = [], types = []},
              eigenvariables = [],
              validation = (fn _ => boolTheory.TRUTH),
              action = action, children = []}
         val script =
           clasetReplay.append (clasetReplay.empty 1) record
         val grounded = clasetReplay.ground clasetMeta.empty script
       in
         ((ignore
             (clasetReplay.REPLAY_TAC grounded
               ([], boolSyntax.T) (Context.snapshot ()));
           false)
          handle searchBudget.LimitReached
                   (searchBudget.Candidate, usage) =>
                   #candidates usage = 0
               | Feedback.HOL_ERR _ => false)
       end)

val _ =
  test
    ("lifting empty results still checks the goal position",
     fn () =>
       let val node = clasetGoal.from_goal ([], boolSyntax.T)
       in
         null (clasetGoal.lift_children node 1 []) andalso
         ((ignore (clasetGoal.lift_children node 2 []); false)
          handle Feedback.HOL_ERR _ => true)
       end)

val _ =
  test
    ("rendered variable membership distinguishes types and keeps order",
     fn () =>
       let
         val typed = mk_var ("typed", Type.bool)
         val other_typed = mk_var ("typed", Type.alpha)
         val fresh = mk_var ("fresh", Type.bool)
         val eq = boolSyntax.mk_eq (other_typed, other_typed)
         val parent = ([], typed)
         val child = ([fresh], eq)
         val node = clasetGoal.from_goal parent
         val expected = free_varsl [eq, fresh]
       in
         case clasetGoal.lift_children node 1 [child] of
             [(_, names)] =>
               ListPair.allEq (uncurry Term.aconv) (names, expected) andalso
               clasetReplay.new_free_names parent [child] =
                 [map (fst o dest_var) expected]
           | _ => false
       end)
