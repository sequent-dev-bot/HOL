signature clasetRules =
sig
  type term = Term.term
  type thm = Thm.thm
  type thname = KernelSig.kernelname

  datatype rulekind = Intro | Elim | Dest | Forward | Norm
  (* For unsafe Intro, Elim, Dest, and Forward rules, [prio] is a
     predicted success percentage in the range 1--100.  For Norm rules it
     is an integer penalty (any integer, with the built-in simplifier at
     zero), and NONE denotes the default penalty zero.  Priorities on safe
     rules are reserved and currently ignored. *)
  type rulespec = {kind : rulekind, safe : bool, prio : int option}
  type tag = {weight : int, index : int}
  type brl = bool * thm
  type rl = thm * thm option
  type info = {rl : rl, dup_rl : rl}
  type decl =
    {name : string, spec : rulespec, tag : tag, info : info, orig : thm}

  type canonical =
    {thm : thm, patvars : term HOLset.set, prems : term list, concl : term}

  (* Rename [vars] apart from the free variables of the theorem's
     hypotheses, so that specializing and later generalizing with the
     results cannot make GEN reject a free hypothesis. *)
  val fresh_forall_vars : thm -> term list -> term list

  (* Take the binders of a rule's conclusion as binders of the rule, so
     that its index is an atom.  An Isabelle rule is stored in hhf normal
     form and never quantifies its conclusion's subject; a HOL4 theorem
     standing for one -- a datatype's induction rule, say -- does, and its
     index then meets no atomic goal.  Not a normalisation the claset
     applies on its own: the atomised index of a conclusion that is a bare
     pattern application matches every goal, so an ambient rule must keep
     its binder.  Callers ask for it where they know the source rule's
     shape. *)
  val atomise_conclusion : thm -> thm

  val canonical_rule : thm -> thm
  val canonical_rule_of : rulekind -> thm -> thm
  val canonical_form : thm -> canonical
  val canonical_form_of : rulekind -> thm -> canonical
  val canonical_form_of_measured :
    (unit -> unit) -> rulekind -> thm -> canonical
  val rule_index : rulekind -> thm -> term
  val rule_index_of : rulekind -> canonical -> term
  val rule_premises_of : rulekind -> thm -> term list
  val is_elim : rulekind -> bool

  val MAKE_ELIM_RULE : thm -> thm
  val CLASSICAL_RULE : thm -> thm
  val SWAP_INTRO_RULE : thm -> thm option
  val DUP_INTRO_RULE : thm -> thm
  val DUP_ELIM_RULE : thm -> thm
  val REV_DUP_ELIM_RULE : thm -> thm

  (* A rule's premises are independent antecedents, so any order of them
     states the same rule.  [PERMUTE_PREMISES_RULE kind order th] restates
     [th] with premise [List.nth (order, i)] of its canonical form in
     position [i]; [order] must be a permutation of the premise positions.
     Order is observable to a search that attempts the resulting subgoals
     one after another. *)
  val PERMUTE_PREMISES_RULE : rulekind -> int list -> thm -> thm

  val ext_info : rulespec -> thm -> info

  datatype safe_class = Safe0 | SafeP
  val subgoals_of : brl -> int
  val safe_class_of : rulespec -> info -> safe_class option

  type decls
  val empty_decls : decls
  val make_decl : {name : string, spec : rulespec, weight : int,
                   info : info, orig : thm} -> decl
  val extend_decl : decl -> decls -> decl option * decls
  val extend_derived_decl : decl -> decls -> decl option * decls
  val remove_decl : string -> decls -> decl list * decls
  val find_decl : decls -> string -> decl option
  val decl_name_member : decls -> string -> bool
  val get_decls : decls -> thm -> decl list
  val dest_decls : decls -> decl list
  (* The order [dest_decls] returns: kind-class group, then tag order
     within the group.  Exposed so that a derived list can be maintained
     in [dest_decls] order without re-sorting. *)
  val decl_order : decl * decl -> order
  val merge_decls : decls * decls -> decl list * decls
  (* Fewer subgoals first, then more recent declarations. *)
  val compare_tag : tag * tag -> order
  val candidate_order : (tag * brl) list -> (tag * brl) list
  val candidate_order_measured :
    (unit -> unit) -> (tag * brl) list -> (tag * brl) list

  datatype cdelta = ADD of {name : thname, spec : rulespec} | RM of string
  val encode_delta : cdelta -> ThyDataSexp.t
  val decode_delta : ThyDataSexp.t -> cdelta option
  val load_delta : cdelta -> (thname * rulespec * thm) option
  val uptodate_delta : cdelta -> bool
end
