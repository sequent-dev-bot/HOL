Theory tyinfoDelBase
Ancestors
  clasetSeed
Libs
  clasetLib

Datatype:
  tyinfo_del = TyinfoDelA | TyinfoDelB bool
End

(* Both are refused: they warn and record nothing for descendants. *)
val _ = delrule "__claset_tyinfo_tyinfoDelBase_tyinfo_del_inject_0_intro";
val _ = delrule "__claset_tyinfo_tyinfoDelBase_tyinfo_del_distinct";
