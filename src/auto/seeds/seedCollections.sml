structure seedCollections :> seedCollections =
struct

open Abbrev HolKernel

val ERR = mk_HOL_ERR "seedCollections"

fun register settype =
  thmTable.register
    {settype = settype, initial_value = Symtab.empty,
     apply_delta = thmTable.apply_delta,
     apply_to_global = thmTable.apply_delta}

val algebra_data = register "algebra_simps"
val field_data = register "field_simps"

fun table_entries data = Symtab.dest (#get_global_value data ())
fun persistent_to_name name =
  case String.fields (equal #"$") name of
      [thy, theorem] => {Thy = thy, Name = theorem}
    | _ => raise ERR "persistent_to_name" ("Malformed name: " ^ name)
fun named_entries data =
  map (fn (name, theorem) => (persistent_to_name name, theorem))
    (table_entries data)

fun algebra_rewrites () = thmTable.thms algebra_data
fun field_rewrites () = thmTable.thms field_data

fun algebra_ss () = simpLib.rewrites_with_names (named_entries algebra_data)
fun field_ss () = simpLib.rewrites_with_names (named_entries field_data)

fun remove data function name =
  thmTable.remove
    {data = data, apply_to_global = thmTable.apply_delta,
     error = ERR function} name

fun remove_algebra_simps name =
  remove algebra_data "remove_algebra_simps" name

fun remove_field_simps name =
  remove field_data "remove_field_simps" name

end
