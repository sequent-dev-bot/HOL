structure listUtil :> listUtil =
struct

fun no_checkpoint () = ()

fun mapMeasured checkpoint f [] = []
  | mapMeasured checkpoint f (item :: items) =
      (checkpoint (); f item :: mapMeasured checkpoint f items)

fun appMeasured checkpoint f [] = ()
  | appMeasured checkpoint f (item :: items) =
      (checkpoint (); f item; appMeasured checkpoint f items)

fun existsMeasured checkpoint pred [] = false
  | existsMeasured checkpoint pred (item :: items) =
      (checkpoint ();
       pred item orelse existsMeasured checkpoint pred items)

fun findMeasured checkpoint pred [] = NONE
  | findMeasured checkpoint pred (item :: items) =
      (checkpoint ();
       if pred item then SOME item else findMeasured checkpoint pred items)

fun appendMeasured checkpoint [] right = right
  | appendMeasured checkpoint (item :: items) right =
      (checkpoint (); item :: appendMeasured checkpoint items right)

fun partitionMeasured checkpoint pred [] = ([], [])
  | partitionMeasured checkpoint pred (item :: items) =
      let
        val _ = checkpoint ()
        val (yes, no) = partitionMeasured checkpoint pred items
      in
        if pred item then (item :: yes, no) else (yes, item :: no)
      end

fun mapPartialMeasured checkpoint f [] = []
  | mapPartialMeasured checkpoint f (item :: items) =
      let
        val _ = checkpoint ()
        val result = f item
        val rest = mapPartialMeasured checkpoint f items
      in
        case result of NONE => rest | SOME value => value :: rest
      end

fun concatMapMeasured checkpoint f [] = []
  | concatMapMeasured checkpoint f (item :: items) =
      (checkpoint ();
       appendMeasured checkpoint (f item)
         (concatMapMeasured checkpoint f items))

fun distinct_by compare key items =
  let
    fun add (item, entry as (seen, kept)) =
      let
        val item_key = key item
      in
        if HOLset.member (seen, item_key) then entry
        else (HOLset.add (seen, item_key), item :: kept)
      end
    val (_, kept) = List.foldl add (HOLset.empty compare, []) items
  in
    List.rev kept
  end

end
