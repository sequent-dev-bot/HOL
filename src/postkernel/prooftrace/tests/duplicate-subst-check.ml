(* Run after replaying duplicate-subst.candle.pft.bin in Candle. *)
let _ =
  let b = mk_type("bool",[]) in
  let x = mk_var("x",b) in
  let z = mk_var("z",b) in
  let result = mk_eq(z,x) in
  let check name hyps tm =
    let th = assoc ("pft_duplicate_subst$" ^ name) (!saved_ths) in
    if hyp th = hyps && aconv (concl th) tm then ()
    else failwith ("duplicate substitution sequent mismatch: " ^ name) in
  check "INST_LAST" [] (mk_eq(result,result));
  check "SUBST_HYPS" [mk_eq(x,z)] (mk_eq(z,z));
  print_endline "DUPLICATE_SUBST_CANDLE_EXACT_PASS";;
