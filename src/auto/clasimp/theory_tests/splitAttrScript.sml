Theory splitAttr[bare]
Libs
  HolKernel Parse boolLib BasicProvers simpLib splitLib
  splitPersistLib

val bool_ss = boolSimps.bool_ss

Definition pick_def:
  pick b (x:'a) y = if b then x else y
End

Theorem attr_pick_split[split]:
  !P. P (pick b (x:'a) y) <=>
      (b ==> P x) /\ (~b ==> P y)
Proof
  Cases_on `b` THEN SIMP_TAC bool_ss [pick_def]
QED

val _ =
  if List.exists
       (fn (name,th) =>
          name = "splitAttr$attr_pick_split" andalso
          aconv (concl th) (concl attr_pick_split))
       (named_split_thms ())
  then ()
  else raise Fail "[split] attribute did not update the split theorem set"

val split_goal =
  ``pick b (x:'a) y = x \/ pick b x y = y``
val excluded_goals =
  #1 (Tactical.VALID
        (SIMP_TAC (bool_ss ++ split_ss)
                  [ExclX "split:splitAttr$attr_pick_split"])
        ([],split_goal) (Context.snapshot()))
val _ =
  case excluded_goals of
      [([],goal)] =>
        if aconv goal split_goal then ()
        else raise Fail "[split] exclusion changed the residual goal"
    | _ => raise Fail "[split] exclusion did not suppress the split"

Theorem attr_pick_split_used:
  pick b (x:'a) y = x \/ pick b x y = y
Proof
  SIMP_TAC (bool_ss ++ split_ss) []
QED
