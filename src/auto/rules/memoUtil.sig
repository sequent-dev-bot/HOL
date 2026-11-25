(* Small memos for derivations keyed on immutable values: a single entry,
   or the few most recent. *)
signature memoUtil =
sig
  (* keyed_memo same compute caches the value compute returned for the
     key it last saw, and reuses it for as long as same reports the key
     has not moved.  The equality is the caller's because not every
     source of a key is an equality type -- a derivation keyed on a
     table of theorems compares them by pointer.  A comparison that
     answers "moved" when it has not costs a recomputation and nothing
     else. *)
  val keyed_memo : ('a -> 'a -> bool) -> ('a -> 'b) -> 'a -> 'b

  (* bounded_memo n same compute is keyed_memo's several-entry form: it
     keeps the values compute returned for the n keys it saw most
     recently, and a key that same reports equal to one of them is
     answered by the stored value, without a recomputation.  A hit moves
     its entry to the front, so the entry evicted when an n+1st key
     arrives is the one least recently asked for.  It serves a derivation
     that alternates between a few keys, which a single entry
     recomputes at every change.  The equality is the caller's, as for
     keyed_memo, and a comparison that answers "moved" when it has not
     costs a recomputation and nothing else.  n below 1 keeps no
     entry. *)
  val bounded_memo : int -> ('a -> 'a -> bool) -> ('a -> 'b) -> 'a -> 'b
end
