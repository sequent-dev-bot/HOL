signature clasetMeta =
sig
  type term = Term.term
  type hol_type = Type.hol_type
  type ('a, 'b) subst = ('a, 'b) Lib.subst

  type meta = term
  type tymeta = hol_type
  type store

  val empty : store
  (* Sibling proof-search subtrees extend a common store on disjoint
     domains.  Proof replay uses [absorb] to recover one covering store;
     unequal entries at a shared key report an engine invariant failure. *)
  val absorb : {base : store, extensions : store list} -> store
  val new_meta : {allow : term list, ty : hol_type} -> store ->
                 meta * store
  val new_tymeta : store -> tymeta * store
  val bind : meta * term -> store -> store option
  val bind_ty : tymeta * hol_type -> store -> store option
  val register_eigen : term -> store -> store option
  val walk : store -> term -> term
  (* Capture-safe transitive store substitution, without beta/eta
     normalization. *)
  val instantiate : store -> term -> term
  val norm : store -> term -> term
  val norm_type : store -> hol_type -> hol_type
  val has_term_metas : store -> bool
  val metas_of : store -> term -> meta list
  val metas_of_normalized : store -> term -> meta list
  val is_meta : term -> bool
  (* A metavariable is identified by its name alone.  Its type is refined as
     the type metavariables inside it are bound, so one metavariable has
     several spellings as a term: [bindings] reports the one it was created
     with, while a normalized term carries the refined one.  Comparing whole
     terms therefore reads a single metavariable as two, so any set or
     lookup keyed on metavariable identity must use this order. *)
  val meta_compare : meta * meta -> order
  val same_meta : meta -> meta -> bool
  val is_tymeta : hol_type -> bool
  val same_tymeta : tymeta -> tymeta -> bool
  val is_eigen : store -> term -> bool
  val ground : store -> store

  (* Persistent bindings support search-subtree diffs.  Each residue is
     semantically normalized when accepted; as-yet unbound dependencies
     remain visible to dynamic pruning. *)
  val bindings : store ->
                 {terms : (meta * term) list,
                  types : (tymeta * hol_type) list}
  (* Direct residues retain dependencies on metavariables bound later. *)
  val term_residue : store -> meta -> term option
  val type_residue : store -> tymeta -> hol_type option
  (* [new_bindings old new] returns the metavariables bound in [new]
     whose names had no binding in [old]. *)
  val new_bindings : store -> store -> {terms : meta list, types : tymeta list}
  val collapse : store ->
                 (hol_type, hol_type) subst * (term, term) subst
end
