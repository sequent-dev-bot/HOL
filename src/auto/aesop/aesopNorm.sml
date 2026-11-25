structure aesopNorm :> aesopNorm =
struct

open Abbrev HolKernel

type tree = aesopTree.tree
type gid = aesopTree.gid
type rule = aesopRule.rule

datatype outcome =
    Complete of {tree : tree, iterations : int}
  | IterationLimit of
      {tree : tree, iterations : int, rule : string}

val ERR = mk_HOL_ERR "aesopNorm"

datatype application =
    Inapplicable
  | Applied of
      {record : clasetReplay.step_record, node : clasetGoal.node}

fun penalty ({phase = aesopRule.RNorm value, ...} : rule) = SOME value
  | penalty _ = NONE

fun ordered_rules rules =
  let
    val positioned =
      List.mapPartial
        (fn (index, rule) =>
          Option.map (fn value => (value, index, rule)) (penalty rule))
        (Lib.enumerate 0 rules)
    fun compare ((left, left_index, _), (right, right_index, _)) =
      case Int.compare (left, right) of
          EQUAL => Int.compare (left_index, right_index)
        | order => order
  in
    map #3 (Listsort.sort compare positioned)
  end

fun new_binding created parent child =
  let
    val {terms, types} = clasetMeta.new_bindings parent child
    fun existing_term meta =
      not (List.exists (clasetMeta.same_meta meta) (#terms created))
    fun existing_type tymeta = not (mem tymeta (#types created))
  in
    List.exists existing_term terms orelse List.exists existing_type types
  end

(* Normalisation rewrites a goal in place, so a norm rule must be
   deterministic and must not split the goal.  A [MultiStep] rule is a
   choice between its steps by construction, so it never normalises. *)
fun raw_application ctxt (rule : rule) node =
  case #apply rule of
      aesopRule.MultiStep _ => Inapplicable
    | _ =>
        (case aesopTree.unique_rule_result_in ctxt rule node of
             SOME ([record], next) =>
               if clasetGoal.goal_count next > 1 then Inapplicable
               else Applied {record = record, node = next}
           | _ => Inapplicable)

fun application ctxt rule node =
  case raw_application ctxt rule node of
      Inapplicable => Inapplicable
    | Applied {record, node = next} =>
        if
          new_binding (clasetReplay.created_of record)
            (clasetGoal.store node) (clasetGoal.store next) orelse
          not (aesopTree.changed node next)
        then Inapplicable
        else Applied {record = record, node = next}
  handle HOL_ERR _ => Inapplicable
       | Match => Inapplicable

fun finish id reversed_records iterations node tree =
  let val records = List.rev reversed_records
  in
  case clasetGoal.goals node of
      [] =>
        Complete
          {tree =
             aesopTree.set_norm_proved id
               {records = records, store = clasetGoal.store node} tree,
           iterations = iterations}
    | [cgoal] =>
        Complete
          {tree =
             aesopTree.set_normalised id
               {records = records, cgoal = cgoal,
                store = clasetGoal.store node} tree,
           iterations = iterations}
    | _ =>
        raise ERR "finish" "a norm chain retained more than one goal"
  end

fun normalise_in ctxt budget {max_depth, rules} id tree =
  if max_depth < 0 then
    raise ERR "normalise" "max_depth must not be negative"
  else
    let val goal = aesopTree.goal tree id
    in
      if aesopTree.is_normalised goal then
        Complete {tree = tree, iterations = 0}
      else
        let
          val ordered = ordered_rules rules

          fun scan reversed_records iterations node [] =
                finish id reversed_records iterations node tree
            | scan reversed_records iterations node (rule :: rest) =
                (Option.app
                   (fn meter =>
                     searchBudget.charge meter searchBudget.Normalization)
                   budget;
                 case application ctxt rule node of
                     Inapplicable =>
                       scan reversed_records iterations node rest
                   | Applied {record, node = next} =>
                       if iterations >= max_depth then
                         IterationLimit
                           {tree = tree, iterations = iterations,
                            rule = #name rule}
                       else
                         let
                           val records' = record :: reversed_records
                           val iterations' = iterations + 1
                         in
                           if null (clasetGoal.goals next) then
                             finish id records' iterations' next tree
                           else
                             scan records' iterations' next ordered
                         end)
        in
          scan [] 0 (aesopTree.goal_node goal) ordered
        end
    end

end
