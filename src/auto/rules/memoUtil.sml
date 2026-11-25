structure memoUtil :> memoUtil =
struct

(* A false key comparison costs a recomputation and nothing else, so the
   cache cell needs no more synchronization than the source it is read
   against. *)
fun keyed_memo same compute =
  let
    val cache = ref NONE
    fun recompute key =
      let
        val value = compute key
      in
        cache := SOME (key, value); value
      end
  in
    fn key =>
      case !cache of
          SOME (recorded, value) =>
            if same recorded key then value else recompute key
        | NONE => recompute key
  end

(* The cache is most-recent-first.  A hit is removed from it and put
   back in front. *)
fun bounded_memo n same compute =
  let
    val cache = ref []
    fun first_n (_, []) = []
      | first_n (k, entry :: rest) =
          if k <= 0 then [] else entry :: first_n (k - 1, rest)
    fun extract _ [] = NONE
      | extract key ((entry as (recorded, _)) :: rest) =
          if same recorded key then SOME (entry, rest)
          else
            Option.map (fn (found, others) => (found, entry :: others))
                       (extract key rest)
  in
    fn key =>
      case extract key (!cache) of
          SOME (entry as (_, value), others) =>
            (cache := entry :: others; value)
        | NONE =>
            let
              val value = compute key
            in
              cache := first_n (n, (key, value) :: !cache); value
            end
  end

end
