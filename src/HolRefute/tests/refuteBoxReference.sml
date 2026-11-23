(* The boxing pass as it was before it worked on shared terms, kept as the
   reference the selftest compares the shared pass with: [reference_box]
   is the pass with its coercions and eta-contraction, each walking a term
   as a tree.  Copied from the model finder's source before the change; do
   not "improve" it. *)
structure refuteBoxReference =
struct
  (* holdep sees a dependency only from an [open] or a qualified name, not
     from the right-hand side of a structure alias. *)
  local open Refute_ModelFinder_Names Refute_ModelFinder_Preproc
            Refute_ModelFinder_Util in end
  open Refute_ModelFinder_HOL
  structure MFH = Refute_ModelFinder_HOL
  structure MFN = Refute_ModelFinder_Names
  structure MFP = Refute_ModelFinder_Preproc
  structure Util = Refute_ModelFinder_Util
  infix |>
  fun err function message =
    Feedback.mk_HOL_ERR "refuteBoxReference" function message
  val is_generated_const = MFP.is_generated_const

  fun reference_eta_contract term =
    if Term.is_abs term then
      let
        val (variable, body) = Term.dest_abs term
        val contracted_body = reference_eta_contract body
      in
        if Term.is_comb contracted_body andalso
           Term.aconv (#2 (Term.dest_comb contracted_body)) variable andalso
           not (Term.free_in variable
             (#1 (Term.dest_comb contracted_body))) then
          reference_eta_contract (#1 (Term.dest_comb contracted_body))
        else
          Term.mk_abs (variable, contracted_body)
      end
    else if Term.is_comb term then
      let val (function, argument) = Term.dest_comb term
      in Term.mk_comb (reference_eta_contract function, reference_eta_contract argument) end
    else
      term

  fun reference_construct_value context constructor raw_arguments =
    let val arguments = map reference_eta_contract raw_arguments
    in
      case arguments of
          [] => constructor
        | first :: _ =>
            (case generated_selector_argument constructor first of
                 SOME value =>
                   if Term.type_of value <>
                      constructor_result_type constructor then
                     Term.list_mk_comb (constructor, arguments)
                   else
                     let
                       val argument_tys = constructor_arg_types constructor
                       val expected = List.tabulate (length argument_tys,
                         fn index => select_nth_constr_arg context constructor
                           value index (List.nth (argument_tys, index)))
                     in
                       if ListPair.allEq (fn (left, right) =>
                            Term.aconv left right) (arguments, expected) then
                         value
                       else
                         Term.list_mk_comb (constructor, arguments)
                     end
               | NONE => Term.list_mk_comb (constructor, arguments))
    end

  fun reference_coerce_term context new_ty old_ty term =
    if new_ty = old_ty then term
    else if is_funbox_type new_ty then
      let
        val arguments = boxed_type_args new_ty
        val domain = List.nth (arguments, 0)
        val range = List.nth (arguments, 1)
        val function_ty = Type.-->(domain, range)
        val function = reference_coerce_term context function_ty old_ty term
      in
        reference_construct_value context (boxed_constructor context new_ty) [function]
      end
    else if is_funbox_type old_ty then
      let
        val arguments = boxed_type_args old_ty
        val domain = List.nth (arguments, 0)
        val range = List.nth (arguments, 1)
        val expanded = constr_expand context old_ty term
        val function = hd (#2 (HolKernel.strip_comb expanded))
      in
        reference_coerce_term context new_ty (Type.-->(domain, range)) function
      end
    else if is_fun_type new_ty andalso is_fun_type old_ty then
      let
        val (new_domain, new_range) = Type.dom_rng new_ty
        val (old_domain, old_range) = Type.dom_rng old_ty
        val variable = Term.variant (Term.all_vars term)
          (Term.mk_var ("x", new_domain))
        val old_argument = reference_coerce_term context old_domain new_domain variable
        val body = Term.mk_comb (term, old_argument)
      in
        Term.mk_abs (variable,
          reference_coerce_term context new_range old_range body)
      end
    else if (is_pair_type new_ty orelse is_pairbox_type new_ty) andalso
            (is_pair_type old_ty orelse is_pairbox_type old_ty) then
      let
        val new_args =
          if is_pair_type new_ty then
            let val (left, right) = pairSyntax.dest_prod new_ty
            in [left, right] end
          else boxed_type_args new_ty
        val old_args =
          if is_pair_type old_ty then
            let val (left, right) = pairSyntax.dest_prod old_ty
            in [left, right] end
          else boxed_type_args old_ty
        val expanded = constr_expand context old_ty term
        val arguments = #2 (HolKernel.strip_comb expanded)
        val coerced = ListPair.mapEq
          (fn ((new_arg, old_arg), argument) =>
            reference_coerce_term context new_arg old_arg argument)
          (ListPair.zip (new_args, old_args), arguments)
      in
        if is_pair_type new_ty then pairSyntax.mk_pair
          (List.nth (coerced, 0), List.nth (coerced, 1))
        else reference_construct_value context (boxed_constructor context new_ty)
          coerced
      end
    else
      raise err "reference_coerce_term"
        ("incompatible types " ^ Parse.type_to_string old_ty ^ " and " ^
         Parse.type_to_string new_ty)

  fun reference_box context def original =
    let
      val original_vars = Term.all_vars original
      fun type_size ty =
        if Type.is_vartype ty then 1
        else 1 + List.foldl (op +) 0
          (map type_size (#Args (Type.dest_thy_type ty)))
      val env_lookup = AList.lookup (Lib.uncurry Term.aconv)
      fun rebind environment variable new_ty body =
        let
          val (name, _) = Term.dest_var variable
          (* A changed binder type may coincide with a free representation
             variable.  Also avoid replacements of outer binders whose
             formerly distinct types collapse under boxing. *)
          val variable' = Term.variant
            (original_vars @ map #2 environment)
            (Term.mk_var (name, new_ty))
        in (variable', body, (variable, variable') :: environment) end
      fun quantifier environment polarity existential candidate =
        let
          val (variable, body) =
            if existential then boolSyntax.dest_exists candidate
            else boolSyntax.dest_forall candidate
          val old_ty = Term.type_of variable
          (* every binder is boxed, as in the
             pass it is compared with *)
          val new_ty = MFH.box_type context MFH.InFunLHS old_ty
          val (variable', body', environment') =
            rebind environment variable new_ty body
          val transformed = recurse environment' polarity body'
        in
          if existential then boolSyntax.mk_exists (variable', transformed)
          else boolSyntax.mk_forall (variable', transformed)
        end
      and equality environment left right =
        let
          val left' = recurse environment Util.Neut left
          val right' = recurse environment Util.Neut right
          val left_ty = Term.type_of left'
          val right_ty = Term.type_of right'
          val common =
            if def orelse type_size left_ty <= type_size right_ty then left_ty
            else right_ty
        in
          boolSyntax.mk_eq
            (reference_coerce_term context common left_ty left',
             reference_coerce_term context common right_ty right')
        end
      and application environment function argument =
        let
          val function' = recurse environment Util.Neut function
          val function_ty = Term.type_of function'
          val (callable, domain_ty) =
            if MFH.is_fun_type function_ty then
              (function', #1 (Type.dom_rng function_ty))
            else if MFH.is_funbox_type function_ty then
              let
                val arguments = MFH.boxed_type_args function_ty
                val domain = List.nth (arguments, 0)
                val range = List.nth (arguments, 1)
                val constructor = hd
                  (MFH.data_type_constrs context function_ty)
                val underlying_ty = Type.-->(domain, range)
              in
                (MFH.select_nth_constr_arg context constructor function' 0
                   underlying_ty, domain)
              end
            else raise err "reference_box"
              "application operator has a nonfunction type"
          val argument' = recurse environment Util.Neut argument
          val old_argument_ty = Term.type_of argument'
        in
          MFH.s_betapply
            (callable, reference_coerce_term context domain_ty old_argument_ty
              argument')
        end
      and constant candidate =
        let
          val ty = Term.type_of candidate
          val new_ty =
            if (case Lib.total Term.dest_var candidate of
                    SOME (name, _) => MFN.is_quot_normal_name name
                  | NONE => false) then
              let
                val (domain, _) = Type.dom_rng ty
                val boxed = MFH.box_type context MFH.InFunLHS domain
              in Type.-->(boxed, boxed) end
            else if MFH.is_descr candidate andalso MFH.is_fun_type ty then
              let
                val result_ty = #2 (Type.dom_rng ty)
                val boxed_result =
                  MFH.box_type context MFH.InFunLHS result_ty
              in
                Type.-->(Type.-->(boxed_result, Type.bool), boxed_result)
              end
            else if MFH.is_built_in_const candidate then ty
            else if MFH.is_nonfree_constr candidate then
              MFH.box_type context MFH.InConstr ty
            else if (case Lib.total Term.dest_var candidate of
                        SOME (name, _) => MFN.is_sel name
                      | NONE => MFH.is_record_get context candidate) then
              MFH.box_type context MFH.InSel ty
            else MFH.box_type context MFH.InExpr ty
        in
          MFH.retype_constant "box" candidate new_ty
        end
      and recurse environment polarity candidate =
        if boolSyntax.is_forall candidate then
          quantifier environment polarity false candidate
        else if boolSyntax.is_exists candidate then
          quantifier environment polarity true candidate
        else if boolSyntax.is_eq candidate then
          let val (left, right) = boolSyntax.dest_eq candidate
          in equality environment left right end
        else if boolSyntax.is_neg candidate then
          boolSyntax.mk_neg (recurse environment
            (Util.flip_polarity polarity) (boolSyntax.dest_neg candidate))
        else if boolSyntax.is_imp_only candidate then
          let val (left, right) = boolSyntax.dest_imp candidate
          in boolSyntax.mk_imp
            (recurse environment (Util.flip_polarity polarity) left,
             recurse environment polarity right)
          end
        else if boolSyntax.is_conj candidate then
          let val (left, right) = boolSyntax.dest_conj candidate
          in boolSyntax.mk_conj
            (recurse environment polarity left,
             recurse environment polarity right)
          end
        else if boolSyntax.is_disj candidate then
          let val (left, right) = boolSyntax.dest_disj candidate
          in boolSyntax.mk_disj
            (recurse environment polarity left,
             recurse environment polarity right)
          end
        else if Term.is_comb candidate then
          let val (function, argument) = Term.dest_comb candidate
          in application environment function argument end
        else if Term.is_abs candidate then
          let
            val (variable, body) = Term.dest_abs candidate
            val (variable', body', environment') =
              rebind environment variable
                (MFH.box_type context MFH.InFunLHS (Term.type_of variable))
                body
          in
            Term.mk_abs (variable', recurse environment' Util.Neut body')
          end
        else if Term.is_var candidate then
          (case env_lookup environment candidate of
               SOME replacement => replacement
             | NONE =>
                 if is_generated_const candidate then
                   constant candidate
                 else
                   (* Upstream boxes a Free unconditionally and consults its
                      definition's left-hand side only for a schematic Var
                      (nitpick_preproc.ML, [do_term]).  HOL4 has no kernel
                      Var: upstream's Frees and its schematic Vars -- the
                      congruence and bound stand-in variables of
                      [is_schematic_var], which reach here inside congruence
                      and specialized axioms -- are both plain variables, so
                      this branch stands in for upstream's Free and Var
                      cases.  Making [def] unbox one silently splits it from
                      its boxed twin in the negated goal, which
                      specialization puts in the same problem, and leaves the
                      definition constraining nothing. *)
                   let val (name, ty) = Term.dest_var candidate
                   in
                     Term.mk_var (name, MFH.box_type context MFH.InExpr ty)
                   end)
        else if Term.is_const candidate then constant candidate
        else candidate
    in
      recurse [] Util.Pos original
    end
end
