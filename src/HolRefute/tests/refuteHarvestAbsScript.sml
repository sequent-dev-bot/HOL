Theory refuteHarvestAbs
Ancestors
  refuteHarvestType

(* [refute_harvest_deep]'s home theory ([refuteHarvestType]) has neither
   abs/rep constants nor any bijection theorem for it; both are introduced
   here instead, in a theory the type's own home does not own.  This is
   the theorem the lazy harvest scan must reach beyond home to find. *)
val _ = define_new_type_bijections
  {name = "refute_harvest_deep_absrep",
   ABS = "refute_harvest_deep_abs", REP = "refute_harvest_deep_rep",
   tyax = DB.fetch "refuteHarvestType" "refute_harvest_deep_TY_DEF"};

(* A typedef that only a definition mentions: a
   goal over [num] meets the type once the definition is unfolded, so its
   harvest happens after the first preprocessing pass and restarts it. *)
Theorem refute_harvest_hidden_exists[local]:
  ?n : num. (\n. n < 2) n
Proof
  qexists_tac `0` >> simp []
QED

val refute_harvest_hidden_tydef =
  new_type_definition
    ("refute_harvest_hidden", refute_harvest_hidden_exists);

val refute_harvest_hidden_absrep = define_new_type_bijections
  {name = "refute_harvest_hidden_absrep",
   ABS = "refute_harvest_hidden_abs", REP = "refute_harvest_hidden_rep",
   tyax = refute_harvest_hidden_tydef};

Definition refute_harvest_hidden_id_def:
  refute_harvest_hidden_id (n : num) =
    refute_harvest_hidden_rep (refute_harvest_hidden_abs n)
End
