structure searchBudget :> searchBudget =
struct

open HolKernel

datatype kind = Candidate | Application | Normalization

type limits =
  {candidates : int option,
   applications : int option,
   normalization : int option}

type usage =
  {candidates : int,
   applications : int,
   normalization : int}

datatype budget = Budget of
  {limits : limits ref,
   candidates : int ref,
   applications : int ref,
   normalization : int ref,
   parent : budget option}

exception LimitReached of kind * usage

val ERR = mk_HOL_ERR "searchBudget"

fun valid NONE = true
  | valid (SOME limit) = limit >= 0

fun make parent (limits as {candidates, applications, normalization}) =
  if List.all valid [candidates, applications, normalization] then
    Budget
      {limits = ref limits, candidates = ref 0,
       applications = ref 0, normalization = ref 0,
       parent = parent}
  else
    raise ERR "create" "work limits must not be negative"

fun create limits = make NONE limits

fun child parent limits = make (SOME parent) limits

fun unbounded () =
  create
    {candidates = NONE, applications = NONE,
     normalization = NONE}

fun usage (Budget {candidates, applications, normalization, ...}) =
  {candidates = !candidates,
   applications = !applications,
   normalization = !normalization}

fun counter (Budget {limits, candidates, applications,
                     normalization, ...}) kind =
  let
    val (used, limit) =
      case kind of
          Candidate => (candidates, #candidates (!limits))
        | Application => (applications, #applications (!limits))
        | Normalization => (normalization, #normalization (!limits))
  in
    (used, limit)
  end

fun available budget kind =
  let
    val (used, limit) = counter budget kind
    val Budget {parent, ...} = budget
  in
    case limit of
        SOME maximum =>
          !used < maximum andalso
          (case parent of
               NONE => true
             | SOME ancestor => available ancestor kind)
      | NONE =>
          (case parent of
               NONE => true
             | SOME ancestor => available ancestor kind)
  end

fun charge (budget as Budget {parent, ...}) kind =
  let
    fun check_limit current =
      let val (used, limit) = counter current kind
      in
        (case limit of
             SOME maximum =>
               if !used >= maximum then
                 raise LimitReached (kind, usage current)
               else ()
           | NONE => ());
        used
      end
    fun check (current as Budget {parent, ...}) =
      (ignore (check_limit current);
       case parent of
           NONE => ()
         | SOME ancestor => check ancestor)
    fun increment (Budget {parent, candidates, applications,
                           normalization, ...}) =
      let
        val used =
          case kind of
              Candidate => candidates
            | Application => applications
            | Normalization => normalization
      in
        used := !used + 1;
        case parent of
            NONE => ()
          | SOME ancestor => increment ancestor
      end
  in
    let val used = check_limit budget
    in
      case parent of
          NONE => used := !used + 1
        | SOME ancestor =>
            (* Reject before writing anything, then charge from the
               innermost budget outwards. *)
            (check ancestor;
             used := !used + 1;
             increment ancestor)
    end
  end

fun extend (Budget {limits, ...}) kind extra =
  if extra < 0 then
    raise ERR "extend" "an additional allocation must not be negative"
  else
    let
      val {candidates, applications, normalization} = !limits
      fun grow NONE = NONE
        | grow (SOME maximum) =
            SOME (maximum + extra)
              handle Overflow =>
                raise ERR "extend" "work limit overflow"
    in
      limits :=
        (case kind of
             Candidate =>
               {candidates = grow candidates,
                applications = applications,
                normalization = normalization}
           | Application =>
               {candidates = candidates,
                applications = grow applications,
                normalization = normalization}
           | Normalization =>
               {candidates = candidates,
                applications = applications,
                normalization = grow normalization})
    end

type charger =
  {candidate : unit -> unit,
   application : unit -> unit,
   normalization : unit -> unit}

val free_charger : charger =
  {candidate = fn () => (), application = fn () => (),
   normalization = fn () => ()}

fun charger budget : charger =
  {candidate = fn () => charge budget Candidate,
   application = fn () => charge budget Application,
   normalization = fn () => charge budget Normalization}

end
