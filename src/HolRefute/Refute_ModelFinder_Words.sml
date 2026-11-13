(*  Title:      HolRefute/Refute_ModelFinder_Words.sml

Registry of the value-level operations of HOL4's wordsTheory, with each
operation's semantics in ML integer arithmetic, and the table builder that
turns a row into a table over a list of concrete values.  Rows say, per
position, whether it is a word, a natural number or a Boolean; a row's
semantics gets the widths of its word positions.
*)

structure Refute_ModelFinder_Words :> Refute_ModelFinder_Words =
struct

datatype shape = Word | Num | Bool

type row =
  {Thy : string, Name : string, args : shape list, res : shape,
   sem : int list -> IntInf.int list -> IntInf.int option}

type column = {width : int, values : IntInf.int list}
type table = (int list * int option) list

fun modulus width = IntInf.pow (2, width)
fun wrap width n = IntInf.mod (n, modulus width)
fun mask n = modulus n - 1
fun two_comp width a = wrap width (modulus width - a)
fun msb width a = a >= IntInf.pow (2, width - 1)
fun signed width a = if msb width a then a - modulus width else a
fun of_bool b = if b then 1 : IntInf.int else 0
fun bit a i = IntInf.andb (IntInf.~>> (a, Word.fromInt i), 1) = 1
fun bits_of width a = List.tabulate (width, fn i => bit a i)
fun from_bits bs =
  #1 (foldl (fn (b, (acc, i)) =>
               (if b then acc + IntInf.pow (2, i) else acc, i + 1))
        (0 : IntInf.int, 0) bs)
fun popcount a = if a = 0 then 0 else IntInf.mod (a, 2) + popcount (IntInf.div (a, 2))

(* The unspecified divisor is 0: HOL's [DIV] and [MOD] leave it open. *)
fun divide a b = if b = 0 then NONE else SOME (IntInf.div (a, b))
fun remainder a b = if b = 0 then NONE else SOME (IntInf.mod (a, b))

(* HOL's [word_quot] and [word_rem]: divide the magnitudes, then negate the
   result when the signs differ (the remainder takes the dividend's sign). *)
fun signed_division unsigned_op negate_when width a b =
  let
    fun magnitude x = if msb width x then two_comp width x else x
    val result = unsigned_op (magnitude a) (magnitude b)
  in
    Option.map (fn r => if negate_when (msb width a) (msb width b)
                        then two_comp width r else r) result
  end

fun count_of_shape Word = 1 | count_of_shape _ = 0

(* [checked args res f]: the widths of the word-shaped positions and the
   argument values arrive as lists of the right length, or the caller's
   table was built wrongly. *)
fun checked args res f =
  let
    val word_count = foldl (fn (s, n) => n + count_of_shape s) 0 (res :: args)
    val arg_count = length args
  in
    fn widths => fn values =>
      if length widths <> word_count then
        raise Refute_ModelFinder_Util.BAD ("Refute_ModelFinder_Words.sem",
          "expected " ^ Int.toString word_count ^ " widths, got " ^
          Int.toString (length widths))
      else if length values <> arg_count then
        raise Refute_ModelFinder_Util.BAD ("Refute_ModelFinder_Words.sem",
          "expected " ^ Int.toString arg_count ^ " arguments, got " ^
          Int.toString (length values))
      else f (widths, values)
  end

fun make name args res f =
  {Thy = "words", Name = name, args = args, res = res,
   sem = checked args res f} : row

(* Rows at one width: every word-shaped position has that width. *)
fun w_w name f = make name [Word] Word
  (fn ([w, _], [a]) => SOME (f w a) | _ => raise Match)
fun ww_w name f = make name [Word, Word] Word
  (fn ([w, _, _], [a, b]) => SOME (f w a b) | _ => raise Match)
fun ww_b name f = make name [Word, Word] Bool
  (fn ([w, _], [a, b]) => SOME (of_bool (f w a b)) | _ => raise Match)
fun ww_wp name f = make name [Word, Word] Word
  (fn ([w, _, _], [a, b]) => f w a b | _ => raise Match)

(* The bits [l] to [min h (w - 1)] of [a], moved down to bit 0. *)
fun field w h l a =
  let val top = IntInf.min (h, IntInf.fromInt (w - 1))
  in
    if l > top then 0
    else IntInf.andb (IntInf.~>> (a, Word.fromInt (IntInf.toInt l)),
                      mask (IntInf.toInt (top - l) + 1))
  end

(* A shift or rotate count is a natural number of any size; counts of the
   width and above are decided before anything is shifted by them. *)
fun shift_left w a n =
  if n >= IntInf.fromInt w then 0
  else wrap w (IntInf.<< (a, Word.fromInt (IntInf.toInt n)))
fun shift_right w a n =
  if n >= IntInf.fromInt w then 0
  else IntInf.~>> (a, Word.fromInt (IntInf.toInt n))
fun arith_shift_right w a n =
  if n >= IntInf.fromInt w then (if msb w a then mask w else 0)
  else wrap w (IntInf.~>> (signed w a, Word.fromInt (IntInf.toInt n)))
fun rotate_right w a n =
  let val k = IntInf.toInt (IntInf.mod (n, IntInf.fromInt w))
  in
    wrap w (IntInf.orb (IntInf.~>> (a, Word.fromInt k),
                        IntInf.<< (a, Word.fromInt (w - k))))
  end
fun rotate_left w a n =
  rotate_right w a (IntInf.fromInt w - IntInf.mod (n, IntInf.fromInt w))

(* HOL computes [a ** b] in full before it reduces it, so an exponent above
   this bound would not terminate in a replay; it is an unknown value here.
   Below it the power is taken by repeated squaring modulo [2^w]. *)
val exp_bound : IntInf.int = 1024
fun power_mod w a n =
  let
    fun go base n acc =
      if n = 0 then acc
      else go (wrap w (base * base)) (IntInf.div (n, 2))
             (if IntInf.mod (n, 2) = 1 then wrap w (acc * base) else acc)
  in go (wrap w a) n (wrap w 1) end

fun saturate w n = if n >= modulus w then mask w else n

(* A reduction folds its function over the bits from the most significant
   down, as [word_reduce] does. *)
fun reduce f w a =
  case rev (bits_of w a) of
      first :: rest => of_bool (foldl (fn (x, acc) => f (acc, x)) first rest)
    | [] => 0

val rows : row list =
  [ww_w "word_add" (fn w => fn a => fn b => wrap w (a + b)),
   ww_w "word_sub" (fn w => fn a => fn b => wrap w (a - b)),
   ww_w "word_mul" (fn w => fn a => fn b => wrap w (a * b)),
   w_w "word_2comp" two_comp,
   w_w "word_1comp" (fn w => fn a => modulus w - 1 - a),
   ww_w "word_and" (fn _ => fn a => fn b => IntInf.andb (a, b)),
   ww_w "word_or" (fn _ => fn a => fn b => IntInf.orb (a, b)),
   ww_w "word_xor" (fn _ => fn a => fn b => IntInf.xorb (a, b)),
   ww_b "word_lo" (fn _ => fn a => fn b => a < b),
   ww_b "word_ls" (fn _ => fn a => fn b => a <= b),
   ww_b "word_hi" (fn _ => fn a => fn b => a > b),
   ww_b "word_hs" (fn _ => fn a => fn b => a >= b),
   ww_b "word_lt" (fn w => fn a => fn b => signed w a < signed w b),
   ww_b "word_le" (fn w => fn a => fn b => signed w a <= signed w b),
   ww_b "word_gt" (fn w => fn a => fn b => signed w a > signed w b),
   ww_b "word_ge" (fn w => fn a => fn b => signed w a >= signed w b),
   ww_wp "word_div" (fn _ => divide),
   ww_wp "word_mod" (fn _ => remainder),
   ww_wp "word_quot"
     (signed_division divide (fn neg_a => fn neg_b => neg_a <> neg_b)),
   ww_wp "word_rem"
     (signed_division remainder (fn neg_a => fn _ => neg_a)),

   (* conversions *)
   make "w2w" [Word] Word
     (fn ([_, wb], [a]) => SOME (wrap wb a) | _ => raise Match),
   make "sw2sw" [Word] Word
     (fn ([wa, wb], [a]) => SOME (wrap wb (signed wa a)) | _ => raise Match),
   make "w2n" [Word] Num (fn (_, [a]) => SOME a | _ => raise Match),
   make "n2w" [Num] Word
     (fn ([w], [n]) => SOME (wrap w n) | _ => raise Match),
   make "saturate_n2w" [Num] Word
     (fn ([w], [n]) => SOME (saturate w n) | _ => raise Match),
   make "saturate_w2w" [Word] Word
     (fn ([_, wb], [a]) => SOME (saturate wb a) | _ => raise Match),

   (* constants and the further orderings and arithmetic *)
   make "word_T" [] Word (fn ([w], []) => SOME (mask w) | _ => raise Match),
   make "word_L" [] Word
     (fn ([w], []) => SOME (IntInf.pow (2, w - 1)) | _ => raise Match),
   make "word_H" [] Word
     (fn ([w], []) => SOME (IntInf.pow (2, w - 1) - 1) | _ => raise Match),
   make "word_L2" [] Word
     (fn ([w], []) =>
        SOME (wrap w (IntInf.pow (2, w - 1) * IntInf.pow (2, w - 1)))
       | _ => raise Match),
   ww_w "word_min" (fn _ => fn a => fn b => if a < b then a else b),
   ww_w "word_max" (fn _ => fn a => fn b => if a < b then b else a),
   ww_w "word_smin"
     (fn w => fn a => fn b => if signed w a < signed w b then a else b),
   ww_w "word_smax"
     (fn w => fn a => fn b => if signed w a < signed w b then b else a),
   w_w "word_abs" (fn w => fn a => if msb w a then two_comp w a else a),
   ww_w "word_nand"
     (fn w => fn a => fn b => mask w - IntInf.andb (a, b)),
   ww_w "word_nor"
     (fn w => fn a => fn b => mask w - IntInf.orb (a, b)),
   ww_w "word_xnor"
     (fn w => fn a => fn b => mask w - IntInf.xorb (a, b)),
   make "word_exp" [Word, Word] Word
     (fn ([w, _, _], [a, b]) =>
        if b > exp_bound then NONE else SOME (power_mod w a b)
       | _ => raise Match),
   make "word_log2" [Word] Word
     (fn ([w, _], [a]) =>
        if a = 0 then NONE else SOME (IntInf.fromInt (IntInf.log2 a))
       | _ => raise Match),
   ww_w "saturate_add" (fn w => fn a => fn b => saturate w (a + b)),
   ww_w "saturate_sub"
     (fn _ => fn a => fn b => if a > b then a - b else 0),
   ww_w "saturate_mul" (fn w => fn a => fn b => saturate w (a * b)),
   make "word_compare" [Word, Word] Word
     (fn ([_, _, _], [a, b]) => SOME (if a = b then 1 else 0)
       | _ => raise Match),

   (* bit selection, fields and reversal *)
   make "word_msb" [Word] Bool
     (fn ([w], [a]) => SOME (of_bool (msb w a)) | _ => raise Match),
   make "word_lsb" [Word] Bool
     (fn (_, [a]) => SOME (of_bool (bit a 0)) | _ => raise Match),
   make "word_bit" [Num, Word] Bool
     (fn ([w], [b, a]) =>
        SOME (of_bool (b < IntInf.fromInt w andalso bit a (IntInf.toInt b)))
       | _ => raise Match),
   make "word_bits" [Num, Num, Word] Word
     (fn ([w, _], [h, l, a]) => SOME (field w h l a) | _ => raise Match),
   make "word_slice" [Num, Num, Word] Word
     (fn ([w, _], [h, l, a]) =>
        let val top = IntInf.min (h, IntInf.fromInt (w - 1))
        in
          SOME (if l > top then 0
                else IntInf.andb (a, mask (IntInf.toInt top + 1) -
                                     mask (IntInf.toInt l)))
        end
       | _ => raise Match),
   make "word_signed_bits" [Num, Num, Word] Word
     (fn ([w, _], [h, l, a]) =>
        let val top = IntInf.min (h, IntInf.fromInt (w - 1))
        in
          SOME (if l > top then 0
                else from_bits (List.tabulate (w, fn i =>
                       bit a (IntInf.toInt (IntInf.min (IntInf.fromInt i + l,
                                                        top))))))
        end
       | _ => raise Match),
   make "word_extract" [Num, Num, Word] Word
     (fn ([wa, wb], [h, l, a]) => SOME (wrap wb (field wa h l a))
       | _ => raise Match),
   make "word_reverse" [Word] Word
     (fn ([w, _], [a]) => SOME (from_bits (rev (bits_of w a)))
       | _ => raise Match),
   make "word_len" [Word] Num
     (fn ([w], _) => SOME (IntInf.fromInt w) | _ => raise Match),
   make "bit_count" [Word] Num
     (fn ([w], [a]) => SOME (popcount a) | _ => raise Match),
   make "bit_count_upto" [Num, Word] Num
     (fn ([w], [n, a]) =>
        if n > IntInf.fromInt w then NONE
        else SOME (popcount (IntInf.andb (a, mask (IntInf.toInt n))))
       | _ => raise Match),
   make "bit_field_insert" [Num, Num, Word, Word] Word
     (fn ([wa, wb, _], [h, l, a, v]) =>
        let
          fun result i =
            if l <= IntInf.fromInt i andalso IntInf.fromInt i <= h then
              let val k = IntInf.fromInt i - l
              in if k >= IntInf.fromInt wa then NONE
                 else SOME (bit a (IntInf.toInt k))
              end
            else SOME (bit v i)
          val outcomes = List.tabulate (wb, result)
        in
          if List.all Option.isSome outcomes
          then SOME (from_bits (map Option.valOf outcomes))
          else NONE
        end
       | _ => raise Match),
   make "reduce_and" [Word] Word
     (fn ([w, _], [a]) => SOME (reduce (fn (x, y) => x andalso y) w a)
       | _ => raise Match),
   make "reduce_or" [Word] Word
     (fn ([w, _], [a]) => SOME (reduce (fn (x, y) => x orelse y) w a)
       | _ => raise Match),
   make "reduce_xor" [Word] Word
     (fn ([w, _], [a]) => SOME (reduce (fn (x, y) => x <> y) w a)
       | _ => raise Match),
   make "reduce_nand" [Word] Word
     (fn ([w, _], [a]) =>
        SOME (reduce (fn (x, y) => not (x andalso y)) w a)
       | _ => raise Match),
   make "reduce_nor" [Word] Word
     (fn ([w, _], [a]) =>
        SOME (reduce (fn (x, y) => not (x orelse y)) w a)
       | _ => raise Match),
   make "reduce_xnor" [Word] Word
     (fn ([w, _], [a]) => SOME (reduce (fn (x, y) => x = y) w a)
       | _ => raise Match),

   (* shifts and rotates, by a natural number and by a word *)
   make "word_lsl" [Word, Num] Word
     (fn ([w, _], [a, n]) => SOME (shift_left w a n) | _ => raise Match),
   make "word_lsr" [Word, Num] Word
     (fn ([w, _], [a, n]) => SOME (shift_right w a n) | _ => raise Match),
   make "word_asr" [Word, Num] Word
     (fn ([w, _], [a, n]) => SOME (arith_shift_right w a n)
       | _ => raise Match),
   make "word_ror" [Word, Num] Word
     (fn ([w, _], [a, n]) => SOME (rotate_right w a n) | _ => raise Match),
   make "word_rol" [Word, Num] Word
     (fn ([w, _], [a, n]) => SOME (rotate_left w a n) | _ => raise Match),
   make "word_lsl_bv" [Word, Word] Word
     (fn ([w, _, _], [a, n]) => SOME (shift_left w a n) | _ => raise Match),
   make "word_lsr_bv" [Word, Word] Word
     (fn ([w, _, _], [a, n]) => SOME (shift_right w a n)
       | _ => raise Match),
   make "word_asr_bv" [Word, Word] Word
     (fn ([w, _, _], [a, n]) => SOME (arith_shift_right w a n)
       | _ => raise Match),
   make "word_ror_bv" [Word, Word] Word
     (fn ([w, _, _], [a, n]) => SOME (rotate_right w a n)
       | _ => raise Match),
   make "word_rol_bv" [Word, Word] Word
     (fn ([w, _, _], [a, n]) => SOME (rotate_left w a n)
       | _ => raise Match),

   (* concatenation *)
   make "word_join" [Word, Word] Word
     (fn ([_, wb, wr], [a, b]) =>
        SOME (wrap wr (IntInf.<< (a, Word.fromInt wb) + b))
       | _ => raise Match),
   make "word_concat" [Word, Word] Word
     (fn ([_, wb, wr], [a, b]) =>
        SOME (wrap wr (IntInf.<< (a, Word.fromInt wb) + b))
       | _ => raise Match),
   make "word_replicate" [Num, Word] Word
     (fn ([wa, wb], [n, a]) =>
        SOME (from_bits (List.tabulate (wb, fn i =>
          IntInf.fromInt i < n * IntInf.fromInt wa andalso
          bit a (i mod wa)))) | _ => raise Match),
   make "word_sign_extend" [Num, Word] Word
     (fn ([wa, _], [n, a]) =>
        (* [n2w (SIGN_EXTEND n (dimindex 'a) (w2n a))]: from the number's
           low n bits (the sign bit tested at n - 1, or at 0 for n = 0) up
           to the width, the subtraction cut off at 0 as in HOL.  A field
           of the width or more leaves the word as it is. *)
        if n >= IntInf.fromInt wa then SOME a
        else
          let
            val k = IntInf.toInt n
            val low = IntInf.mod (a, modulus k)
            val extended = IntInf.max (modulus wa - modulus k, 0) + low
          in
            SOME (wrap wa (if bit a (Int.max (k - 1, 0)) then extended else low))
          end
       | _ => raise Match),
   make "word_exp_tailrec" [Word, Word, Word] Word
     (fn ([w, _, _, _], [b, e, a]) =>
        if e > exp_bound then NONE else SOME (wrap w (a * power_mod w b e))
       | _ => raise Match)]

fun find_row {Thy, Name} =
  List.find (fn (row : row) => #Thy row = Thy andalso #Name row = Name) rows

fun check_values who what ok values =
  case List.find (not o ok) values of
      SOME bad => raise Refute_ModelFinder_Util.BAD (who, what ^ " value " ^
                                  IntInf.toString bad ^ " is out of range")
    | NONE =>
        let
          fun add (value, seen) =
            if Redblackset.member (seen, value) then
              raise Refute_ModelFinder_Util.BAD (who, what ^ " values repeat")
            else Redblackset.add (seen, value)
        in
          ignore (foldl add (Redblackset.empty IntInf.compare) values)
        end

fun build_table (row : row) (columns : column list) =
  let
    val who = "Refute_ModelFinder_Words.build_table"
    val shapes = #args row @ [#res row]
    val () =
      if length columns = length shapes then ()
      else raise Refute_ModelFinder_Util.BAD (who,
             "expected " ^ Int.toString (length shapes) ^ " columns, got " ^
             Int.toString (length columns))
    fun check (Word, {width, values}) =
          check_values who "word" (fn v => 0 <= v andalso v < modulus width)
            values
      | check (Num, {values, ...}) =
          check_values who "num" (fn v => 0 <= v) values
      | check (Bool, {values, ...}) =
          check_values who "Boolean" (fn v => v = 0 orelse v = 1) values
    val () = ListPair.app check (shapes, columns)
    val widths = List.mapPartial (fn (Word, {width, ...} : column) => SOME width
                                   | _ => NONE) (ListPair.zip (shapes, columns))
    val argument_values = map #values (List.take (columns, length (#args row)))
    val result_values = #values (List.last columns)
    (* argument tuples as (positions, values), first argument slowest *)
    fun tuples [] = [([], [])]
      | tuples (vs :: rest) =
          List.concat (Lib.mapi (fn i => fn v =>
            map (fn (is, xs) => (i :: is, v :: xs)) (tuples rest)) vs)
    val positions_of_result =
      foldl (fn ((i, v), found) => Redblackmap.insert (found, v, i))
        (Redblackmap.mkDict IntInf.compare)
        (Lib.mapi (fn i => fn v => (i, v)) result_values)
    fun position result = Redblackmap.peek (positions_of_result, result)
    fun entry (positions, args) =
      (positions, Option.mapPartial position (#sem row widths args))
  in
    map entry (tuples argument_values)
  end

fun neighbourhood width centres count =
  let
    val m = modulus width
    val wanted = IntInf.min (IntInf.fromInt count, m)
    val centres = map (wrap width) centres
    fun add (v, (found, seen, n)) =
      if n >= wanted orelse Redblackset.member (seen, v) then (found, seen, n)
      else (v :: found, Redblackset.add (seen, v), n + 1)
    (* One round lists, centre by centre, the value d above and d below it. *)
    fun round d state =
      let
        val values =
          if d = 0 then centres
          else List.concat (map (fn c => [wrap width (c + d),
                                          wrap width (c - d)]) centres)
        val (found, seen, n) = foldl add state values
      in
        if n >= wanted then rev found else round (d + 1) (found, seen, n)
      end
  in
    if wanted <= 0 orelse null centres then []
    else round 0 ([], Redblackset.empty IntInf.compare, 0 : IntInf.int)
  end

fun shape_name Word = "word"
  | shape_name Num = "num"
  | shape_name Bool = "bool"

fun listing () =
  String.concat (map (fn (row : row) =>
    #Thy row ^ "." ^ #Name row ^ " : " ^
    String.concatWith " -> " (map shape_name (#args row @ [#res row])) ^
    "\n") rows)

end
