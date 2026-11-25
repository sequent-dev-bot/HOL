Theory linarithDiamondRemove
Ancestors
  linarithDiamondRoot

(* Both tables are keyed by the "Thy$Name" form, so a retraction spelled
   with a dot has to be normalized before it can delete anything.  Each
   table is therefore retracted once in each spelling: the inherited
   declaration in one form and the sibling branch's declaration -- which
   is not in this theory's ancestry at all -- in the other. *)

val _ =
  linarithData.remove_arith
    "linarithDiamondRoot.arith_diamond_root_fact"

val _ =
  linarithData.remove_arith
    "linarithDiamondAdd$arith_diamond_contested_fact"

val _ =
  linarithData.remove_arith_split
    "linarithDiamondRoot$arith_split_diamond_root_rule"

val _ =
  linarithData.remove_arith_split
    "linarithDiamondAdd.arith_split_diamond_contested_rule"
