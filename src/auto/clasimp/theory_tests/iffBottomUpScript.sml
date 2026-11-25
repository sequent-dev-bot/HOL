Theory iffBottomUp
Ancestors
  clasetSeed
Libs
  clasimpLib iffTestSupport

fun fail message = failer "iff bottom-up test" message

(* [iff_bottom_up] declares the claset halves of [iff] and installs the
   rewrite as a low-priority reducer, which the traversal reaches only once
   the rewrites and the descent have both left a node alone.  The rule below
   reads its subject through [iff_bottom_up_wrap], so under [iff] it would
   fire above [iff_bottom_up_head] and hide it. *)
Definition iff_bottom_up_wrap_def:
  iff_bottom_up_wrap (p : bool) = ~p
End

Definition iff_bottom_up_view_def:
  iff_bottom_up_view (p : bool) = p
End

Definition iff_bottom_up_step_def:
  iff_bottom_up_step (p : bool) = T
End

Theorem iff_bottom_up_rule[iff_bottom_up]:
  !p. ~iff_bottom_up_wrap p <=> iff_bottom_up_view p
Proof
  simp[iff_bottom_up_wrap_def, iff_bottom_up_view_def]
QED

Theorem iff_bottom_up_head[simp]:
  !p. iff_bottom_up_wrap (iff_bottom_up_step p) <=> F
Proof
  simp[iff_bottom_up_wrap_def, iff_bottom_up_step_def]
QED

val declared_name = "iffBottomUp$iff_bottom_up_rule"

val _ =
  if not (has_iff_rules declared_name)
  then fail "an iff_bottom_up declaration did not derive the iff rules"
  else if not (rewrites_to ``~iff_bottom_up_wrap p`` ``iff_bottom_up_view p``)
  then fail "an iff_bottom_up rewrite did not reduce a subject on its own"
  else if
    not (rewrites_to ``~iff_bottom_up_wrap (iff_bottom_up_step p)`` ``T``)
  then fail "an iff_bottom_up rewrite fired above the subject's own rule"
  else ()

(* One fragment holds every declaration, so a retraction rebuilds it; the
   declarations it does not name have to survive that. *)
Definition iff_bottom_up_spare_def:
  iff_bottom_up_spare (p : bool) = ~p
End

Theorem iff_bottom_up_spare_rule[iff_bottom_up]:
  !p. ~iff_bottom_up_spare p <=> iff_bottom_up_view p
Proof
  simp[iff_bottom_up_spare_def, iff_bottom_up_view_def]
QED

val spare_name = "iffBottomUp$iff_bottom_up_spare_rule"

val _ =
  if not (rewrites_to ``~iff_bottom_up_spare p`` ``iff_bottom_up_view p``)
  then fail "a second iff_bottom_up declaration was not live"
  else ()

val _ = clasimpLib.remove_iff_bottom_up "iff_bottom_up_spare_rule"

val _ =
  if has_any_iff_rules spare_name
  then fail "remove_iff_bottom_up left the retracted claset rules behind"
  else if rewrites_to ``~iff_bottom_up_spare p`` ``iff_bottom_up_view p``
  then fail "remove_iff_bottom_up left the retracted rewrite behind"
  else if not (rewrites_to ``~iff_bottom_up_wrap p`` ``iff_bottom_up_view p``)
  then fail "remove_iff_bottom_up dropped a declaration it does not name"
  else ()
