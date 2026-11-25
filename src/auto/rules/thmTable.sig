(* Theorem sets declared through ThmSetData, and the name-keyed table most
   of them keep. *)
signature thmTable =
sig
  type delta = ThmSetData.setdelta
  type table = Thm.thm Symtab.table
  type 'value data = (delta, 'value) AncestryData.fullresult

  (* A set without a finaliser whose every delta stays up to date.  Raises
     if the settype, or an attribute of that name, is already taken. *)
  val register :
    {settype : string, initial_value : 'value,
     apply_delta : delta -> 'value -> 'value,
     apply_to_global : delta -> 'value -> 'value} -> 'value data
  (* As [register], with a finaliser. *)
  val register_finalised :
    {settype : string, initial_value : 'value,
     apply_delta : delta -> 'value -> 'value,
     apply_to_global : delta -> 'value -> 'value,
     thy_finaliser :
       {thyname : string} -> delta list -> 'value -> 'value} ->
    'value data

  (* An addition is keyed by the theorem's kernel name, a removal by the
     key it carries. *)
  val apply_delta : delta -> table -> table
  (* The table of the context given; thms reads the ambient one. *)
  val thms_of : table data -> Context.t -> Thm.thm list
  val thms : table data -> Thm.thm list

  (* Retracts the entry [clasetLib.normalise_rule_name] names, first from
     the global value and then in the theory's record.  A name without a
     theory part is reported through [error]. *)
  val remove :
    {data : table data, apply_to_global : delta -> table -> table,
     error : string -> exn} -> string -> unit
end
