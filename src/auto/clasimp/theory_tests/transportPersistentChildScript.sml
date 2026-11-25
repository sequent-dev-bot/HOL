Theory transportPersistentChild
Ancestors
  transportPersistentBase
Libs
  clasimpLib

Theorem reloaded_rule_uses_a_certified_view:
  !n. transport_persistent_q n ==> transport_persistent_r n
Proof
  rpt strip_tac >>
  AUTO_TAC
    [clasetLib.Simp
       transportPersistentBaseTheory.transport_persistent_bridge]
QED
