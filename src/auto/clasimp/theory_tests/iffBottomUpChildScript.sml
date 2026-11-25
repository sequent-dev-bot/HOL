Theory iffBottomUpChild
Ancestors
  iffBottomUp
Libs
  iffTestSupport

fun fail message = failer "iff bottom-up child test" message

val declared_name = "iffBottomUp$iff_bottom_up_rule"
val spare_name = "iffBottomUp$iff_bottom_up_spare_rule"

(* The reducer is a closure, so a descendant gets it by replaying the
   declarations rather than by reading anything off the parent's simpset. *)
val _ =
  if not (has_iff_rules declared_name)
  then fail "the reloaded child lost the inherited iff rules"
  else if not (rewrites_to ``~iff_bottom_up_wrap p`` ``iff_bottom_up_view p``)
  then fail "the reloaded child lost the inherited rewrite"
  else if
    not (rewrites_to ``~iff_bottom_up_wrap (iff_bottom_up_step p)`` ``T``)
  then fail "the replayed rewrite fired above the subject's own rule"
  else if has_any_iff_rules spare_name
  then fail "replay restored the retracted declaration's claset rules"
  else if rewrites_to ``~iff_bottom_up_spare p`` ``iff_bottom_up_view p``
  then fail "replay restored the retracted declaration's rewrite"
  else ()
