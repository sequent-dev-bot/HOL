structure searchWork :> searchWork =
struct

type work = {
  expansions : int,
  tableau_depth : int,
  tableau_branches : int,
  inferences : int,
  rule_applications : int
}

val zero : work =
  {expansions = 0, tableau_depth = 0, tableau_branches = 0,
   inferences = 0, rule_applications = 0}

val current = ref zero

fun total ({expansions, tableau_branches, inferences,
            rule_applications, ...} : work) =
  expansions + tableau_branches + inferences + rule_applications

fun render ({expansions, tableau_depth, tableau_branches, inferences,
             rule_applications} : work) =
  "expansions=" ^ Int.toString expansions ^
  ", tableau_depth=" ^ Int.toString tableau_depth ^
  ", tableau_branches=" ^ Int.toString tableau_branches ^
  ", inferences=" ^ Int.toString inferences ^
  ", rule_applications=" ^ Int.toString rule_applications

fun reset () = current := zero

fun read () = !current

fun combine (left : work, right : work) : work =
  {expansions = #expansions left + #expansions right,
   tableau_depth = Int.max (#tableau_depth left, #tableau_depth right),
   tableau_branches = #tableau_branches left + #tableau_branches right,
   inferences = #inferences left + #inferences right,
   rule_applications = #rule_applications left + #rule_applications right}

fun measure body =
  let
    val enclosing = !current
    val _ = current := zero
    fun restore () =
      let val inner = !current
      in current := combine (enclosing, inner); inner
      end
    val result =
      body ()
      handle exn => (ignore (restore ()); raise exn)
  in
    (result, restore ())
  end

fun note_expansion () =
  let val {expansions, tableau_depth, tableau_branches, inferences,
           rule_applications} = !current
  in
    current :=
      {expansions = expansions + 1, tableau_depth = tableau_depth,
       tableau_branches = tableau_branches, inferences = inferences,
       rule_applications = rule_applications}
  end

fun note_tableau {depth, branches, inferences = new_inferences} =
  let val {expansions, tableau_depth, tableau_branches, inferences,
           rule_applications} = !current
  in
    current :=
      {expansions = expansions,
       tableau_depth = Int.max (tableau_depth, depth),
       tableau_branches = tableau_branches + branches,
       inferences = inferences + new_inferences,
       rule_applications = rule_applications}
  end

fun note_rule_applications count =
  let val {expansions, tableau_depth, tableau_branches, inferences,
           rule_applications} = !current
  in
    current :=
      {expansions = expansions, tableau_depth = tableau_depth,
       tableau_branches = tableau_branches, inferences = inferences,
       rule_applications = rule_applications + count}
  end

end
