structure thmTable :> thmTable =
struct

open HolKernel

type delta = ThmSetData.setdelta
type table = thm Symtab.table
type 'value data = (delta, 'value) AncestryData.fullresult

val ERR = mk_HOL_ERR "thmTable"

fun check_unregistered settype =
  if List.exists (equal settype) (ThmSetData.all_set_types ()) orelse
     ThmAttribute.is_attribute settype
  then
    raise ERR "registration"
      ("settype or attribute " ^ settype ^ " already exists")
  else ()

fun export settype initial_value apply_delta apply_to_global thy_finaliser =
  (check_unregistered settype;
   ThmSetData.export_with_ancestry
     {settype = settype,
      delta_ops =
        {apply_to_global = apply_to_global,
         thy_finaliser = thy_finaliser,
         uptodate_delta = K true,
         initial_value = initial_value,
         apply_delta = apply_delta}})

fun register {settype, initial_value, apply_delta, apply_to_global} =
  export settype initial_value apply_delta apply_to_global NONE

fun register_finalised
      {settype, initial_value, apply_delta, apply_to_global,
       thy_finaliser} =
  export settype initial_value apply_delta apply_to_global
    (SOME thy_finaliser)

(* A removal's key is resolved where the retraction is written (see
   [removal_key]), not here: every descendant theory replays the delta,
   and resolving a bare name against each would designate a different
   entry in every one. *)
fun apply_delta delta table =
  case delta of
      ThmSetData.ADD (name, theorem) =>
        Symtab.update (KernelSig.name_toString name, theorem) table
    | ThmSetData.REMOVE key => Symtab.delete_safe key table

fun thms_of (data : table data) ctxt =
  map #2 (Symtab.dest (#get_global_value_of data ctxt))

fun thms data = thms_of data (Context.snapshot ())

(* The key is computed where the theory it was written in is current and
   the user can be told it denotes nothing: a name without the kernel
   separator spells no key. *)
fun removal_key error name =
  let
    val key = clasetLib.normalise_rule_name name
  in
    if String.isSubstring "$" key then key
    else raise error ("Malformed name: " ^ name)
  end

fun remove {data : table data, apply_to_global, error} name =
  let
    val delta = ThmSetData.REMOVE (removal_key error name)
    val _ = #update_global_value data (apply_to_global delta)
  in
    #record_delta data delta
  end

end
