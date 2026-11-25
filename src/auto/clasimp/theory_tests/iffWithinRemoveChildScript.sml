Theory iffWithinRemoveChild
Ancestors
  iffWithinRemove
Libs
  iffTestSupport

val removed_name = "iffWithinRemove$iff_within_remove_rule"

val _ =
  if has_iff_rewrite removed_name orelse has_any_iff_rules removed_name
  then fail "same-theory final iff state was not removal in the child"
  else ()

val independent_name =
  "iffWithinRemove$iff_independent_simp_rule"
val collision_name = "iffWithinRemove$iff_rule_collision"
val explicit_intro_name =
  "iffWithinRemove$iff_rule_collision_intro"
val shared_first_name = "iffWithinRemove$iff_shared_shape_first"
val shared_second_name = "iffWithinRemove$iff_shared_shape_second"

val _ =
  if not (rewrite_changes independent_name (BasicProvers.srw_ss ()))
  then fail "replay lost the independent simp registration"
  else if has_any_iff_rules independent_name
  then fail "replay restored removed iff rules"
  else if has_any_iff_rules shared_first_name
  then fail "replay restored the retracted alpha-equivalent declaration"
  else if not (has_iff_rules shared_second_name)
  then fail "replay lost the surviving alpha-equivalent declaration"
  else if not (has_iff_rewrite shared_second_name)
  then fail "replay lost the surviving declaration's rewrite"
  else if not
    (has_named_rule
      explicit_intro_name iffWithinRemoveTheory.iff_rule_collision_intro)
  then fail "replay lost the colliding explicit intro rule"
  else if has_any_iff_rules collision_name
  then fail "replay restored the collision test's removed iff rules"
  else if not (rewrites_to ``~T`` F)
  then fail "replay lost bool.NOT_CLAUSES after basename collision"
  else ()
