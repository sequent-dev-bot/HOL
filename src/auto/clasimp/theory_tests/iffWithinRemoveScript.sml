Theory iffWithinRemove
Ancestors
  clasetSeed
Libs
  clasimpLib iffTestSupport

Definition iff_within_remove_def:
  iff_within_remove (p : bool) = p
End

Theorem iff_within_remove_rule[iff]:
  !p. iff_within_remove p <=> p
Proof
  simp[iff_within_remove_def]
QED

val removed_name = "iffWithinRemove$iff_within_remove_rule"
val _ = clasimpLib.remove_iff "iff_within_remove_rule"

val _ =
  if has_iff_rewrite removed_name orelse has_any_iff_rules removed_name
  then fail "same-theory remove_iff did not retract both immediate views"
  else ()

(* Two declarations can derive alpha-equivalent rules.  Each owns its own
   copy, so retracting one must leave the other's contribution installed --
   in this session and in every theory that reloads it. *)
Definition iff_shared_shape_def:
  iff_shared_shape (p : bool) = p
End

Theorem iff_shared_shape_first[iff]:
  !p. iff_shared_shape p <=> p
Proof
  simp[iff_shared_shape_def]
QED

Theorem iff_shared_shape_second[iff]:
  !q. iff_shared_shape q <=> q
Proof
  simp[iff_shared_shape_def]
QED

val shared_first_name = "iffWithinRemove$iff_shared_shape_first"
val shared_second_name = "iffWithinRemove$iff_shared_shape_second"
val _ = clasimpLib.remove_iff "iff_shared_shape_first"

val _ =
  if has_any_iff_rules shared_first_name
  then fail "remove_iff left the retracted declaration's rules behind"
  else if not (has_iff_rules shared_second_name)
  then fail "removing one declaration disarmed an alpha-equivalent one"
  else if not (has_iff_rewrite shared_second_name)
  then fail "removing one declaration dropped the other's rewrite"
  else ()

Definition iff_independent_simp_def:
  iff_independent_simp (p : bool) = p
End

Theorem iff_independent_simp_rule[simp,iff]:
  !p. iff_independent_simp p <=> p
Proof
  simp[iff_independent_simp_def]
QED

val independent_name =
  "iffWithinRemove$iff_independent_simp_rule"
val _ = clasimpLib.remove_iff "iff_independent_simp_rule"

val _ =
  if not (rewrite_changes independent_name (BasicProvers.srw_ss ()))
  then fail "remove_iff deleted the independent simp registration"
  else if has_any_iff_rules independent_name
  then fail "remove_iff retained the independent theorem's iff rules"
  else ()

Definition iff_rule_collision_def:
  iff_rule_collision (p : bool) = p
End

Theorem iff_rule_collision_intro[intro]:
  !p. iff_rule_collision p <=> p
Proof
  simp[iff_rule_collision_def]
QED

Theorem iff_rule_collision[iff]:
  !p. iff_rule_collision p <=> p
Proof
  simp[iff_rule_collision_def]
QED

val collision_name = "iffWithinRemove$iff_rule_collision"
val explicit_intro_name =
  "iffWithinRemove$iff_rule_collision_intro"
val _ = clasimpLib.remove_iff "iff_rule_collision"

val _ =
  if not
       (has_named_rule explicit_intro_name iff_rule_collision_intro)
  then fail "remove_iff deleted the colliding explicit intro rule"
  else if has_any_iff_rules collision_name
  then fail "remove_iff retained private rules after a public-name collision"
  else ()

Definition iff_current_name_collision_def:
  iff_current_name_collision (p : bool) = p
End

Theorem NOT_CLAUSES[iff]:
  !p. iff_current_name_collision p <=> p
Proof
  simp[iff_current_name_collision_def]
QED

val _ = clasimpLib.remove_iff "NOT_CLAUSES"

val _ =
  if not (rewrites_to ``~T`` F)
  then fail "current-theory removal deleted bool.NOT_CLAUSES"
  else ()
