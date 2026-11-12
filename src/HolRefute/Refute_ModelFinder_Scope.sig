signature Refute_ModelFinder_Scope = sig
  type term = Term.term
  type hol_type = Type.hol_type

  type context = Refute_ModelFinder_HOL.mf_context

  type constr_spec =
    {const : term,
     delta : int,
     epsilon : int,
     exclusive : bool,
     explicit_max : int,
     total : bool}

  type data_type_spec =
    {typ : hol_type,
     card : int,
     co : bool,
     self_rec : bool,
     complete : bool * bool,
     concrete : bool * bool,
     deep : bool,
     constrs : constr_spec list}

  type offset_table = (hol_type, int) Redblackmap.dict * int

  type scope =
    {hol_ctxt : context,
     binarize : bool,
     card_assigns : (hol_type * int) list,
     bits : int,
     bisim_depth : int,
     data_types : data_type_spec list,
     ofs : offset_table}

  val max_scopes : int
  val type_arguments : hol_type -> hol_type list
  val data_type_spec : data_type_spec list -> hol_type -> data_type_spec option
  val constr_spec : data_type_spec list -> term -> constr_spec
  (* these three take the scope: a word type on a value-list carrier
     is incomplete *)
  val is_complete_type : scope -> bool -> hol_type -> bool
  val is_concrete_type : scope -> bool -> hol_type -> bool
  val is_exact_type : scope -> bool -> hol_type -> bool
  val offset_of_type : ('a, 'b) Redblackmap.dict * 'b -> 'a -> 'b
  val spec_of_type : scope -> hol_type -> int * int
  val max_word_width : scope -> int
  (* The values the atoms of a fragment word type stand for, atom [j] being
     the [j]th; NONE for an exact carrier, whose atom [j] is [n2w j]. *)
  val word_values : scope -> hol_type -> IntInf.int list option
  val word_value_index : scope -> hol_type -> IntInf.int -> int option
  val scopes_equivalent : scope * scope -> bool

  val is_self_recursive_constr_type : hol_type -> bool
  val take_at_most : int -> 'a list -> 'a list

  type scope_cursor

  val new_scope_cursor :
    context -> bool -> (hol_type option * int list) list ->
    (term option * int list) list -> (term option * int list) list ->
    int list -> int list -> hol_type list -> hol_type list ->
    hol_type list -> hol_type list -> scope_cursor
  val scope_cursor_batch_with_stop :
    scope_cursor -> int -> (unit -> bool) ->
    {done : bool, scopes : scope list, skipped : int, stopped : bool}
  val all_scopes :
    context -> bool -> (hol_type option * int list) list ->
    (term option * int list) list -> (term option * int list) list ->
    int list -> int list -> hol_type list -> hol_type list ->
    hol_type list -> hol_type list -> int * scope list
  val mono_override : (hol_type option * 'a) list -> hol_type -> 'a option
  val mono_partition_with :
    (hol_type -> bool) -> (hol_type option * bool option) list ->
    hol_type list -> hol_type list * hol_type list
end
