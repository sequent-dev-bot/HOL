signature clasetUnify =
sig
  type term = Term.term
  type hol_type = Type.hol_type
  type meta = clasetMeta.meta
  type tymeta = clasetMeta.tymeta
  type store = clasetMeta.store

  datatype mode = Match | Unify
  type rule_metas = {terms : meta list, types : tymeta list}
  type config = {mode : mode, rule_metas : rule_metas}

  val unify_types : store -> config -> hol_type * hol_type -> store option
  val unify : store -> config -> term * term -> store option

end
