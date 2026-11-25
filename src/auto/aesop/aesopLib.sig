signature aesopLib =
sig
  type thm = Thm.thm
  type tactic = Abbrev.tactic
  type hol_type = Type.hol_type

  type aesop_config = aesopSearch.aesop_config
  type rphase = aesopRule.rphase
  type rule = aesopRule.rule

  val default_config : aesop_config

  val AESOP_TAC : thm list -> tactic
  val AESOP_SAFE_TAC : thm list -> tactic

  val CS_AESOP_TAC :
    aesop_config -> clasetLib.claset -> simpLib.simpset -> tactic
  val CS_AESOP_SAFE_TAC :
    aesop_config -> clasetLib.claset -> simpLib.simpset -> tactic

  (* A resumable search under an invocation-owned operational budget.  The
     session runs in the context current when it is created, including
     that context's [split] rules. *)
  val CS_AESOP_SESSION :
    searchBudget.budget -> aesop_config ->
    clasetLib.claset -> simpLib.simpset -> Abbrev.goal ->
    aesopSearch.budget_session

  (* Tactic rules are session-local closures and are never persisted. *)
  val augment_aesop :
    {name : string, phase : rphase,
     tactic : NTactical.ntactic} -> unit

  (* Registers a rule a builder returned, such as [cases_rule_for]'s.  The
     rule keeps its own name, phase and retrieval index.  Rules whose
     action is a theorem-derived engine step are refused. *)
  val augment_aesop_rule : rule -> unit

  val cases_rule_for : hol_type -> rule
end
