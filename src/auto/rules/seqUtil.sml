structure seqUtil :> seqUtil =
struct

fun list_of sequence =
  case seq.cases sequence of
      NONE => []
    | SOME (value, rest) => value :: list_of rest

end
