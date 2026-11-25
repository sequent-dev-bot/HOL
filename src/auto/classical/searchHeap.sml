(* The frontier heap of the BEST_FIRST driver.

   The leftist min-heap itself is mlibHeap.  This structure adds
   operations on equal minima and retains the comparator that mlibHeap
   does not expose. *)
structure searchHeap :> searchHeap =
struct

  datatype 'a heap = Heap of ('a * 'a -> order) * 'a mlibHeap.heap

  fun empty compare = Heap (compare, mlibHeap.empty compare)

  fun add x (Heap (compare, heap)) = Heap (compare, mlibHeap.add x heap)

  fun is_empty (Heap (_, heap)) = mlibHeap.is_empty heap

  (* Raises Empty on an empty heap. *)
  fun delete_min (Heap (compare, heap)) =
    let val (value, remaining) = mlibHeap.remove heap
    in (value, Heap (compare, remaining)) end

  (* Raises Empty on an empty heap. *)
  fun fold_minima collect initial (Heap (compare, heap)) =
    let
      val (first, rest) = mlibHeap.remove heap

      (* Stop at the first different minimum without merging its children. *)
      fun take values heap =
        if mlibHeap.is_empty heap orelse
           compare (mlibHeap.top heap, first) <> EQUAL then
          (values, Heap (compare, heap))
        else
          let
            val (next, remaining) = mlibHeap.remove heap
          in
            take (collect (next, values)) remaining
          end

      val (values, remaining) = take initial rest
    in
      (first, values, remaining)
    end

  fun delete_all_min heap =
    let val (first, reversed, remaining) = fold_minima op:: [] heap
    in (first :: List.rev reversed, remaining) end

  fun delete_min_class heap =
    let val (first, (), remaining) = fold_minima (fn _ => ()) () heap
    in (first, remaining) end

end
