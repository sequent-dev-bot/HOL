fun check name ok =
  if ok then print (name ^ ": OK\n")
  else (print (name ^ ": FAILED\n"); OS.Process.exit OS.Process.failure)

val files = ref ([] : string list)
fun temp () =
  let val base = OS.FileSys.tmpName ()
      val file = base ^ ".pft"
      val () = if OS.FileSys.access(base, []) then
                 OS.FileSys.remove base else ()
  in files := file :: !files; file end
fun bytes file =
  let val ins = BinIO.openIn file
  in BinIO.inputAll ins before BinIO.closeIn ins end
fun output ruleset =
  let val file = temp ()
  in (file, PFTWriter.openOut {file=file,version="0.1.0",ruleset=ruleset}) end
fun finish out = PFTWriter.closeOut out
  {n_ty=4,n_tm=4,n_th=32}
fun merged inputs targets =
  let val file = temp ()
  in PFTMerge.merge
       {inputs=inputs,targets=targets,output=file,binary=true}; file end
fun merge_test name f = check name (f ())
val names = ref ([] : string list)
val fh : PFTReader.format_handler =
  {tyvar=fn _ => (),tyop=fn _ => (),var=fn _ => (),const=fn _ => (),
   comb=fn _ => (),abs=fn _ => (),new_type=fn _ => (),
   new_const=fn (name,_) => names := name :: !names,
   axiom=fn _ => (),save=fn (name,_) => names := name :: !names,
   load=fn _ => raise Fail "unresolved LOAD",
   del=fn _ => (),
   del_range=fn _ => ()}
fun read_commands file command =
  let val {ruleset,...} = PFTReader.read_header {file=file,binary=true}
      val descs = PFTOpcodes.descs_for_ruleset ruleset
  in ignore (PFTReader.read {file=file,binary=true,format_handler=fh,
       ruleset_handler=fn opc => fn sr =>
         let val desc = PFTOpcodes.lookup_desc descs opc
             val id = if null (#results desc) then 0 else #readVarint sr ()
         in command (opc,id,PFTReader.read_raw_args desc sr) end})
  end
(* CONJ uses its connective through the kernel cache, not a term ID. *)
val (conj,out) = output "hol4"
val () = PFTWriter.tyop out 0 "min$bool" []
val () = PFTWriter.tyop out 1 "min$fun" [0,0]
val () = PFTWriter.tyop out 2 "min$fun" [0,1]
val () = PFTWriter.new_const out "bool$/\\" 2
val () = PFTWriter.var out 0 "p" 0
val () = PFTWriter.HOL4.assume out 0 0
val () = PFTWriter.HOL4.conj out 1 0 0
val () = PFTWriter.save out "conj$RESULT" 1
val () = finish out
val () = names := []
val () = read_commands (merged [conj] [PFTMerge.ThyAll("conj",false)])
                      (fn _ => ())
val () = check "merge retains the implicit conjunction declaration"
               (List.exists (fn name => name = "bool$/\\") (!names))

(* LOAD keeps the preceding SAVE even when that name is saved again. *)
val (rebind,out) = output "hol4"
val () = PFTWriter.tyop out 0 "min$bool" []
val () = PFTWriter.var out 0 "p" 0
val () = PFTWriter.HOL4.assume out 0 0
val () = PFTWriter.save out "rebind$X" 0
val () = PFTWriter.load out 1 "rebind$X"
val () = PFTWriter.save out "rebind$X" 1
val () = PFTWriter.save out "rebind$RESULT" 1
val () = finish out
val () = names := []
val () = read_commands
  (merged [rebind] [PFTMerge.ThyThm("rebind","RESULT",false)]) (fn _ => ())
val () = check "merge resolves LOAD before SAVE rebinding"
               (!names = ["rebind$RESULT"])

fun preserves_alias options =
  let val alias = temp ()
      val original = bytes conj
      val () = if OS.FileSys.access(alias, []) then
                 OS.FileSys.remove alias else ()
      val () = if OS.Process.isSuccess
        (Systeml.systeml (["ln"] @ options @ [conj,alias])) then ()
        else raise Fail "could not create input alias"
      val rejected =
        ((PFTMerge.merge {inputs=[conj],
            targets=[PFTMerge.ThyAll("conj",false)],output=alias,binary=true};
          false) handle Fail _ => true)
  in rejected andalso bytes conj = original andalso bytes alias = original end
val () = merge_test "merge preserves input aliased by its output"
  (fn () => preserves_alias ["-s"] andalso preserves_alias [])
val () = List.app OS.FileSys.remove (!files)
