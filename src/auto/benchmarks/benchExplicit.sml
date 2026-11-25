structure benchExplicit =
struct

open HolKernel

(* Display names that no plain theory$theorem lookup resolves.  The table
   is the single source of truth: benchGuards enumerates it, so a new
   special case cannot escape the alias audit. *)
val special : (string * (unit -> benchLib.named_thm)) list =
  let
    fun derived display theorem : string * (unit -> benchLib.named_thm) =
      (display, fn () => {name = display, theorem = theorem ()})
  in
    [derived "pred_set$MEMBER_NOT_EMPTY_reverse"
       (fn () =>
         Drule.GEN_ALL
           (Thm.SYM (Drule.SPEC_ALL pred_setTheory.MEMBER_NOT_EMPTY))),
     derived "list$SNOC_APPEND[symmetric]"
       (fn () => Conv.GSYM listTheory.SNOC_APPEND),
     derived "list$HD_CONV_EL"
       (fn () =>
         Drule.GEN_ALL
           (Thm.SYM (Drule.SPEC_ALL (CONJUNCT1 listTheory.EL)))),
     derived "list$MAP_REVERSE[symmetric]"
       (fn () =>
         Drule.GEN_ALL (Thm.SYM (Drule.SPEC_ALL listTheory.MAP_REVERSE))),
     derived "list$FILTER_REVERSE[symmetric]"
       (fn () =>
         Drule.GEN_ALL
           (Thm.SYM (Drule.SPEC_ALL listTheory.FILTER_REVERSE))),
     derived "list$nub_set_for_card_set" (fn () => listTheory.nub_set),
     derived "list$ALL_DISTINCT_CARD_LIST_TO_SET_for_nub"
       (fn () => listTheory.ALL_DISTINCT_CARD_LIST_TO_SET),
     derived "list$all_distinct_nub"
       (fn () => listTheory.all_distinct_nub),
     derived "list$LIST_REL_NIL"
       (fn () => CONJUNCT1 listTheory.LIST_REL_NIL),
     derived "option$FORALL_OPTION[of-not-P]"
       (fn () => optionTheory.FORALL_OPTION),
     derived "pair$case_prod_eta"
       (fn () =>
         Drule.GEN_ALL (Thm.SYM (Drule.SPEC_ALL pairTheory.LAMBDA_PROD)))]
  end

end
