signature Refute_ModelFinder_Kodkod = sig
  type nut = Refute_ModelFinder_Nut.nut
  type problem_metadata =
    {free_names : nut list,
     sel_names : nut list,
     nonsel_names : nut list,
     rel_table : nut Refute_ModelFinder_Nut.NameTable.table,
     unsound : bool,
     unknown_value : bool,
     scope : Refute_ModelFinder_Scope.scope}
  type rich_problem = Refute_Forl.problem * problem_metadata
  type assembly_params =
    {debug : bool,
     peephole_optim : bool,
     total_consts : bool,
     datatype_sym_break : int,
     kodkod_sym_break : int,
     comment : string,
     solver : string list,
     unsound_delay : int,
     free_names : nut list,
     nonsel_names : nut list,
     nondef_us : nut list,
     def_us : nut list,
     need_us : nut list}
  (* Raises Refute_ModelFinder_Util.TOO_LARGE/TOO_SMALL if assembly still cannot
     fit after the existing offset retry. *)
  val assemble_problem :
    assembly_params -> bool -> Refute_ModelFinder_Scope.scope ->
    rich_problem
  (* [assemble_scope params scope] does the work
     of assembly that the variants of a scope share, once, and raises
     ModelFinder_Util.TOO_LARGE when the relations of a scope cannot fit; it
     returns the function that assembles the problem of a variant, the sound
     one for [false] and the liberal for [true]. *)
  val assemble_scope :
    assembly_params -> Refute_ModelFinder_Scope.scope ->
    bool -> rich_problem
  (* The number of [assemble_problem] calls so far,
     for the selftests. *)
  val assembly_calls : int ref
  val check_sharing : bool ref
  val sharing_checks : int ref
  val sharing_stats :
    {calls : int, hits : int, nodes : int, output_dag : int,
     output_tree : IntInf.int, register_uses : int} ref
  (* [check_expression_arities names universe_card
     formula] raises TOO_LARGE when an expression of [formula] has more
     columns than a universe of [universe_card] atoms allows; [names] say
     which relation each index is. *)
  val check_expression_arities :
    (Refute_Forl.n_ary_index * string) list -> int ->
    Refute_Forl.formula -> unit
end
