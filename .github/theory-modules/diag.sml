(* Prints what Meta.configureTheoryModuleCache looks at. *)
fun fp p = OS.FileSys.fullPath p handle OS.SysErr (m, _) => "SysErr " ^ m;
val base = OS.Path.concat (Systeml.HOLDIR, "bin/hol.state");
val _ = print ("HOLDIR " ^ Systeml.HOLDIR ^ "\ncwd " ^ OS.FileSys.getDir () ^ "\n");
val _ = List.app (fn (_, p) => print ("entry " ^ p ^ " -> " ^ fp p ^ "\n"))
                 (PolyML.SaveState.showHierarchyWithIds ());
val _ = print ("base " ^ base ^ " -> " ^ fp base ^ "\n");
val dir = OS.Path.concat (OS.FileSys.getDir (), "diag-modules");
val ok = Meta.configureTheoryModuleCache {directory = dir, base_state = base}
         handle e => (print ("configure raised " ^ General.exnMessage e ^ "\n"); false);
val _ = print ("configure -> " ^ Bool.toString ok ^ "\n");
