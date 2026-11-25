Theory clasetMarker[bare]
Libs
  HolKernel Parse boolLib

(* Per-invocation claset rule modifiers. *)

val SIntro_def = new_definition("SIntro_def", ``SIntro (x:bool) = x``);
val Intro_def = new_definition("Intro_def", ``Intro (x:bool) = x``);
val SElim_def = new_definition("SElim_def", ``SElim (x:bool) = x``);
val Elim_def = new_definition("Elim_def", ``Elim (x:bool) = x``);
val SDest_def = new_definition("SDest_def", ``SDest (x:bool) = x``);
val Dest_def = new_definition("Dest_def", ``Dest (x:bool) = x``);
val Simp_def = new_definition("Simp_def", ``Simp (x:bool) = x``);
val Iff_def = new_definition("Iff_def", ``Iff (x:bool) = x``);
val Norm_def = new_definition("Norm_def", ``Norm (x:bool) = x``);
val Forward_def = new_definition("Forward_def", ``Forward (x:bool) = x``);
val SForward_def =
  new_definition("SForward_def", ``SForward (x:bool) = x``);
val Del_def = new_definition("Del_def", ``Del (x:'a) = T``);

val _ = OpenTheoryMap.OpenTheory_const_name
  {const = {Thy = "clasetMarker", Name = "SIntro"},
   name = (["Unwanted"], "id")}
val _ = OpenTheoryMap.OpenTheory_const_name
  {const = {Thy = "clasetMarker", Name = "Intro"},
   name = (["Unwanted"], "id")}
val _ = OpenTheoryMap.OpenTheory_const_name
  {const = {Thy = "clasetMarker", Name = "SElim"},
   name = (["Unwanted"], "id")}
val _ = OpenTheoryMap.OpenTheory_const_name
  {const = {Thy = "clasetMarker", Name = "Elim"},
   name = (["Unwanted"], "id")}
val _ = OpenTheoryMap.OpenTheory_const_name
  {const = {Thy = "clasetMarker", Name = "SDest"},
   name = (["Unwanted"], "id")}
val _ = OpenTheoryMap.OpenTheory_const_name
  {const = {Thy = "clasetMarker", Name = "Dest"},
   name = (["Unwanted"], "id")}
val _ = OpenTheoryMap.OpenTheory_const_name
  {const = {Thy = "clasetMarker", Name = "Simp"},
   name = (["Unwanted"], "id")}
val _ = OpenTheoryMap.OpenTheory_const_name
  {const = {Thy = "clasetMarker", Name = "Iff"},
   name = (["Unwanted"], "id")}
val _ = OpenTheoryMap.OpenTheory_const_name
  {const = {Thy = "clasetMarker", Name = "Norm"},
   name = (["Unwanted"], "id")}
val _ = OpenTheoryMap.OpenTheory_const_name
  {const = {Thy = "clasetMarker", Name = "Forward"},
   name = (["Unwanted"], "id")}
val _ = OpenTheoryMap.OpenTheory_const_name
  {const = {Thy = "clasetMarker", Name = "SForward"},
   name = (["Unwanted"], "id")}
