signature linarithData =
sig
  include Abbrev

  (* Type equality, spelled once for the whole layer. *)
  val same_type : hol_type -> hol_type -> bool

  val dest_divmod :
    {dest_div : term -> term * term,
     dest_mod : term -> term * term} -> term -> (term * term) option
  val injected_nonneg : (term -> term) -> thm -> term -> thm option

  (* One carrier's implementation of everything the generic engine
     needs, keyed in the registry by its ty.

     "No value" means two different things here.  A NONE in dest is a
     static fact about the carrier -- it has no such operator at all --
     and never a refusal of a particular term.  The destructors that
     are not optional are partial in the usual xxxSyntax way: they
     raise on a term of the wrong shape, and their callers wrap them in
     Lib.total.  The one per-term option is kit's nonneg, which
     declines the atom it is offered.

     dest_plus, dest_leq and dest_mult are also run over the kit
     theorems to read the carrier's operator constants off them, so
     add_mono must mention addition and non-strict order; a mult_mono
     mentioning no multiplication makes replay scale by repeated
     addition instead.  mk_lit is only ever asked for integer
     values. *)
  type linarith_instance = {
    ty : hol_type,
    (* SOME {lessD} exactly for a discrete order, lessD strengthening a
       strict inequality to the non-strict one about the next element
       (num: |- m < n <=> m + 1 <= n).  These are the discreteness
       theorems only -- everything else replay applies is in kit -- and
       a dense carrier gives NONE and never needs them. *)
    discrete : {lessD : thm list} option,
    dest : {
      dest_plus : term -> term * term,
      dest_minus : (term -> term * term) option,
      dest_neg : (term -> term) option,
      dest_mult : term -> term * term,
      dest_div : (term -> term * term) option,
      dest_suc : (term -> term) option,
      dest_lit : term -> Arbrat.rat,
      mk_lit : Arbrat.rat -> term,
      dest_less : term -> term * term,
      dest_leq : term -> term * term
    },
    (* Replay matches these against derived theorems: add_mono adds two
       relations, mult_mono scales one by a positive literal, not_less
       and not_le are the negated-order equivalences (|- ~(x < y) <=>
       y <= x and |- ~(x <= y) <=> y < x), and neqE eliminates a
       disequality, in the shape
       |- x <> y ==> (x < y ==> F) ==> (y < x ==> F) ==> F.
       nonneg atom is SOME (|- 0 <= atom) for an atom of this carrier
       known to be non-negative and NONE to decline it; search adds a
       non-negativity row exactly where it answers SOME, so an answer
       that varies between the two calls makes replay report a declined
       atom. *)
    kit : {
      add_mono : thm list,
      mult_mono : thm list,
      not_less : thm,
      not_le : thm,
      neqE : thm,
      nonneg : term -> thm option
    },
    (* Normalizes a relation or an expression of the carrier, and
       reduces to T the trivially true relations replay builds.  It
       may report "no change" by raising UNCHANGED -- every instance
       built with linarithCancel.mk_norm_conv does so for a term
       outside its carrier -- since replay either absorbs that
       exception or drops it with Lib.total.  The one
       thing it must decide is reflexivity: replay hands left <= left
       straight to EQT_ELIM, so an instance that leaves that term
       alone raises UNCHANGED out of the whole tactic rather than
       failing. *)
    norm_conv : conv,
    (* Carrier rewrites (num: SUB_EQ_0) applied to the assumptions
       after the propositional negation-normal-form pass, not as part
       of it. *)
    nnf_rules : thm list,
    (* P-form operator-splitting rules arriving with the instance:
       session-global, independent of theory ancestry, and not
       removable -- remove_arith_split reaches only the user
       [arith_split] table. *)
    pre_split : thm list,
    (* Extra facts about one atom.  Every registered instance's
       atom_facts is called on every atom, whatever the atom's carrier,
       so it must return [] for the terms it does not recognize; firing
       outside its own carrier is allowed and deliberate (the int
       instance returns INT_OF_NUM facts for Num i : num). *)
    atom_facts : term -> thm list
  }

  (* Every optional operator of the carrier, as recognisers, derived at
     registration like the implications below.  Built beside the record,
     so that adding a destructor to linarith_instance is a compile error
     at one site rather than a silent change of meaning at the places
     that reason about the complement. *)
  val compound_ops : linarith_instance -> (term -> bool) list

  type linarith_injection = {
    from_ty : hol_type,
    to_ty : hol_type,
    inj : term,
    hom : {le : thm, lt : thm, eq : thm, add : thm, mul : thm}
  }

  (* Decomposition asks instance_for for the carrier of every subterm
     it examines, so the lookup goes through a table built once per
     registry generation (see memo) rather than through a scan of the
     registry; all_instances answers out of the same generation's
     derivation rather than rebuilding its list per call. *)
  val register_instance : linarith_instance -> unit
  val instance_for : hol_type -> linarith_instance option
  val all_instances : unit -> linarith_instance list

  (* Every rule the instance supplies, as the implications replay can
     MATCH_MP against: both directions of an equivalence, or the rule
     itself.  Deriving one costs kernel inference, and replay needs
     them at every node of every certificate, so they are derived once,
     at registration.

     Each is a pure function of the entry it is asked about, so there
     is no staleness question and no invalidation rule: an entry that
     is not the registered one has its derivation recomputed on the
     spot rather than being answered for out of someone else's.

     All but mult_mono are flat, because replay tries them in order and
     takes the first that matches.  mult_mono's are grouped by rule,
     because replay makes two passes over one rule's implications
     before it moves to the next rule, so flattening would change which
     rule wins.  lessD is the discreteness field's, and is empty for a
     dense carrier. *)
  type instance_implications = {
    add_mono : thm list,
    mult_mono : thm list list,
    not_less : thm list,
    not_le : thm list,
    neqE : thm list,
    lessD : thm list
  }
  val instance_implications : linarith_instance -> instance_implications

  (* Keyed the same way, and for the same reason: injection_by_const is
     asked about the head of every application decomposition meets, and
     injection_for about every factor whose type it has to restore. *)
  val register_injection : linarith_injection -> unit
  val injections : unit -> linarith_injection list
  val injection_for : hol_type -> hol_type -> linarith_injection option
  val injection_by_const : term -> linarith_injection option

  (* Every registered injection with what replay derives from it, in
     registry order: the implications of its le, lt and eq
     homomorphisms, which is what decides that a relation lifts along
     it; and its add and mul homomorphisms, oriented to push the
     injection inwards, both as rewrites and as the top-depth
     conversion applying them.  rewrite_conv raises UNCHANGED for an
     injection that has no usable homomorphism, as it does for a term
     it does not rewrite.

     Replay walks this list once per theorem of a conversion closure,
     so the list is the registry's own and costs no lookup to obtain.
     all_injection_rewrite_conv is rewrite_conv over every registered
     injection at once, and so is registry-dependent: see memo. *)
  type derived_injection = {
    injection : linarith_injection,
    relation_imps : thm list,
    rewrites : thm list,
    rewrite_conv : conv
  }
  val derived_injections : unit -> derived_injection list
  val all_injection_rewrite_conv : unit -> conv

  (* The [arith] and [arith_split] tables of the context given, and of
     the ambient one. *)
  val arith_facts_of : Context.t -> thm list
  val arith_split_thms_of : Context.t -> thm list
  val arith_facts : unit -> thm list
  val arith_split_thms : unit -> thm list
  (* The name may be a bare theorem name, a "Thy.Name" qualification or
     the stored "Thy$Name" key.  A bare name is resolved against the
     current theory here, where the retraction is written, so that the
     REMOVE delta recorded designates the same entry in every
     descendant theory that replays it.  Removing an absent key is a
     no-op; a string that spells no key at all is an error. *)
  val remove_arith : string -> unit
  val remove_arith_split : string -> unit

  (* The registry generation, bumped by register_instance and
     register_injection.  Those two are the only mutators of the two
     registries, so it is an exact change signal for them -- and for
     nothing else.  In particular it says nothing about the [arith] and
     [arith_split] tables: they are AncestryData values, and
     set_parents replaces the global table wholesale rather than
     through a delta, so no counter maintained at the delta sites could
     see every change to them. *)
  val generation : unit -> int

  (* memo f re-runs f whenever the registry generation has moved since
     the call that produced the cached value, and otherwise returns
     that value; it is for data derived from the instance and injection
     registries alone.

     memo_with_splits is for data that also derives from the
     [arith_split] table of the context it is asked in, which it hands
     compute: its key carries, besides the generation, that table's theorems,
     compared by pointer.  The theorems rather than their names,
     because a re-declaration under a name the table already holds
     replaces the theorem in place and leaves the key set untouched;
     and read from the table rather than counted at the delta sites,
     because a wholesale ancestry replacement applies no delta.
     Neither is offered for the [arith] table: a tactic reads it once
     per call, and the reducer path, which does derive from it, keys on
     the fact list itself rather than on a generation -- it memoizes
     with memoUtil.keyed_memo, the cell memo and memo_with_splits are
     built from. *)
  val memo : (unit -> 'a) -> unit -> 'a
  val memo_with_splits : (thm list -> 'a) -> Context.t -> 'a


  (* check_asm_split function what th: raise ERR function
     ("Malformed " ^ what) unless th is a split rule in P-form. *)
  val check_asm_split : string -> string -> thm -> unit

  type linarith_config = {neq_limit : int, split_limit : int}
  val default_config : linarith_config

  (* The "linarith.trace" trace.  The tactics read its level from their
     context with traceUtil.level_of, and the helpers take that level
     first, then the threshold.  They render nothing unless the level
     asks for it. *)
  val tracer : traceUtil.tracer
  val trace_thm : traceUtil.level -> int -> string -> thm -> unit
  val trace_terms :
    traceUtil.level -> int -> string -> term list -> unit
  val trace_items :
    traceUtil.level -> int -> string -> ('a -> string) -> 'a list -> unit
end
