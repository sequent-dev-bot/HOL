signature Refute_ModelFinder_Words =
sig
  (* The shapes a value-level word operation's arguments and result have:
     a word of the row's width, a natural number, a Boolean. *)
  datatype shape = Word | Num | Bool

  (* One row per constant.  [sem width arguments] is the operation on the
     arguments' values, an unsigned integer below 2^width for a word, a
     natural number for a [Num], 0 or 1 for a Boolean (false, true), in
     the order of [args]; NONE where HOL leaves the value unspecified. *)
  type row =
    {Thy : string, Name : string, args : shape list, res : shape,
     sem : int -> IntInf.int list -> IntInf.int option}

  val rows : row list
  val find_row : {Thy : string, Name : string} -> row option

  (* The values a table is built over, each list without repeats and
     nearest first: the carrier of words of the row's width, and the
     natural numbers.  Booleans are fixed. *)
  type carrier = {word : IntInf.int list, num : IntInf.int list}

  (* An entry gives the positions of the argument values in their lists and
     the position of the result in the list of its shape; NONE when the
     operation is unspecified there or the result is not in the list.  One
     entry per argument tuple, the first argument varying slowest. *)
  type table = (int list * int option) list

  val build_table : row -> int -> carrier -> table

  (* The registry, one line per row. *)
  val listing : unit -> string
end
