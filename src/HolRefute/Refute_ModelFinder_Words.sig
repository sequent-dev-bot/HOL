signature Refute_ModelFinder_Words =
sig
  (* The shapes a value-level word operation's arguments and result have:
     a word of some width, a natural number, a Boolean. *)
  datatype shape = Word | Num | Bool

  (* One row per constant.  [sem widths arguments] is the operation on the
     arguments' values: [widths] holds the width of each word-shaped
     position, the arguments' first and the result's last; a value is an
     unsigned integer below 2^width for a word, a natural number for a
     [Num], 0 or 1 for a Boolean (false, true), in the order of [args].  NONE
     where HOL leaves the value unspecified, and for [word_exp] where the
     exponent is above [exp_bound]. *)
  type row =
    {Thy : string, Name : string, args : shape list, res : shape,
     sem : int list -> IntInf.int list -> IntInf.int option}

  val rows : row list
  val find_row : {Thy : string, Name : string} -> row option

  (* HOL computes a power in full before reducing it, so a replay would not
     terminate on a huge exponent: above this bound [word_exp] is unknown. *)
  val exp_bound : IntInf.int

  (* The values a table is built over for one position, without repeats and
     nearest first: for a word, the values of the carrier of the position's
     [width]; for a natural number or a Boolean, [width] is 0 and the values
     are those the position's atoms stand for. *)
  type column = {width : int, values : IntInf.int list}

  (* An entry gives the positions of the argument values in their columns and
     the position of the result in the result's column; NONE when the
     operation is unspecified there or the result is not in the column.  One
     entry per argument tuple, the first argument varying slowest.  The
     columns are the arguments' then the result's. *)
  type table = (int list * int option) list

  val build_table : row -> column list -> table

  (* The registry, one line per row. *)
  val listing : unit -> string

  (* [neighbourhood width centres count]: the first [count] values of the
     two-sided ring neighbourhood of [centres] in the words of [width] bits,
     nearest first.  At distance d, each centre in turn contributes its
     value plus d and then minus d (modulo 2^width); a value already listed
     is skipped.  Fewer than [count] values come back only when the ring has
     fewer. *)
  val neighbourhood : int -> IntInf.int list -> int -> IntInf.int list
end
