(*  Title:      HolRefute/Refute_ModelFinder_Words.sml

Registry of the value-level operations of HOL4's wordsTheory, with each
operation's semantics in ML integer arithmetic, and the table builder that
turns a row into a table over a list of concrete values.  Standalone: the
model finder does not use it yet.
*)

structure Refute_ModelFinder_Words :> Refute_ModelFinder_Words =
struct

datatype shape = Word | Num | Bool

type row =
  {Thy : string, Name : string, args : shape list, res : shape,
   sem : int -> IntInf.int list -> IntInf.int option}

type carrier = {word : IntInf.int list, num : IntInf.int list}
type table = (int list * int option) list

fun modulus width = IntInf.pow (2, width)
fun wrap width n = IntInf.mod (n, modulus width)
fun two_comp width a = wrap width (modulus width - a)
fun msb width a = a >= IntInf.pow (2, width - 1)
fun signed width a = if msb width a then a - modulus width else a
fun of_bool b = if b then 1 : IntInf.int else 0

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

fun unary f width args =
  case args of
      [a] => f width a
    | _ => raise Refute_ModelFinder_Util.BAD ("Refute_ModelFinder_Words.unary",
                           "expected one argument, got " ^
                           Int.toString (length args))

fun binary f width args =
  case args of
      [a, b] => f width a b
    | _ => raise Refute_ModelFinder_Util.BAD ("Refute_ModelFinder_Words.binary",
                           "expected two arguments, got " ^
                           Int.toString (length args))

fun word_row name f =
  {Thy = "words", Name = name, args = [Word, Word], res = Word,
   sem = binary (fn w => fn a => fn b => SOME (f w a b))} : row

fun order_row name f =
  {Thy = "words", Name = name, args = [Word, Word], res = Bool,
   sem = binary (fn w => fn a => fn b => SOME (of_bool (f w a b)))} : row

fun partial_row name f =
  {Thy = "words", Name = name, args = [Word, Word], res = Word,
   sem = binary f} : row

fun unary_row name f =
  {Thy = "words", Name = name, args = [Word], res = Word,
   sem = unary (fn w => fn a => SOME (f w a))} : row

val rows : row list =
  [word_row "word_add" (fn w => fn a => fn b => wrap w (a + b)),
   word_row "word_sub" (fn w => fn a => fn b => wrap w (a - b)),
   word_row "word_mul" (fn w => fn a => fn b => wrap w (a * b)),
   unary_row "word_2comp" two_comp,
   unary_row "word_1comp" (fn w => fn a => modulus w - 1 - a),
   word_row "word_and" (fn _ => fn a => fn b => IntInf.andb (a, b)),
   word_row "word_or" (fn _ => fn a => fn b => IntInf.orb (a, b)),
   word_row "word_xor" (fn _ => fn a => fn b => IntInf.xorb (a, b)),
   order_row "word_lo" (fn _ => fn a => fn b => a < b),
   order_row "word_ls" (fn _ => fn a => fn b => a <= b),
   order_row "word_hi" (fn _ => fn a => fn b => a > b),
   order_row "word_hs" (fn _ => fn a => fn b => a >= b),
   order_row "word_lt" (fn w => fn a => fn b => signed w a < signed w b),
   order_row "word_le" (fn w => fn a => fn b => signed w a <= signed w b),
   order_row "word_gt" (fn w => fn a => fn b => signed w a > signed w b),
   order_row "word_ge" (fn w => fn a => fn b => signed w a >= signed w b),
   partial_row "word_div" (fn _ => divide),
   partial_row "word_mod" (fn _ => remainder),
   partial_row "word_quot"
     (signed_division divide (fn neg_a => fn neg_b => neg_a <> neg_b)),
   partial_row "word_rem"
     (signed_division remainder (fn neg_a => fn _ => neg_a))]

fun find_row {Thy, Name} =
  List.find (fn (row : row) => #Thy row = Thy andalso #Name row = Name) rows

fun check_values who what ok values =
  let
    fun distinct [] = true
      | distinct (x :: rest) = not (List.exists (fn y => y = x) rest) andalso
                               distinct rest
  in
    case List.find (not o ok) values of
        SOME bad => raise Refute_ModelFinder_Util.BAD (who, what ^ " value " ^
                                    IntInf.toString bad ^ " is out of range")
      | NONE =>
          if distinct values then ()
          else raise Refute_ModelFinder_Util.BAD (who, what ^ " values repeat")
  end

fun build_table (row : row) width ({word, num} : carrier) =
  let
    val who = "Refute_ModelFinder_Words.build_table"
    val () = check_values who "word" (fn v => 0 <= v andalso v < modulus width)
               word
    val () = check_values who "num" (fn v => 0 <= v) num
    fun values Word = word
      | values Num = num
      | values Bool = [0, 1]
    (* argument tuples as (positions, values), first argument slowest *)
    fun tuples [] = [([], [])]
      | tuples (shape :: rest) =
          List.concat (Lib.mapi (fn i => fn v =>
            map (fn (is, vs) => (i :: is, v :: vs)) (tuples rest))
            (values shape))
    fun position result =
      Option.map #1 (List.find (fn (_, v) => v = result)
                       (Lib.mapi (fn i => fn v => (i, v)) (values (#res row))))
    fun entry (positions, args) =
      (positions, Option.mapPartial position (#sem row width args))
  in
    map entry (tuples (#args row))
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
