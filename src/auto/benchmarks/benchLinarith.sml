structure benchLinarith =
struct

open HolKernel autoSeedTheory

val commit = "f7e02b7e"

fun lookup number goals =
  case List.find (fn (item, _, _) => item = number) goals of
      SOME (_, _, goal) => goal
    | NONE => raise Fail ("missing Arith_Examples goal " ^
                          Int.toString number)

val carrier_goals =
  [(2, “(i:int) <= int_max i j”),
   (4, “int_min i j <= (i:int)”),
   (6, “int_min (i:int) j <= int_max i j”),
   (8, “int_min (i:int) j + int_max i j = i + j”),
   (10, “(i:int) < j ==> int_min i j < int_max i j”),
   (11, “(0:int) <= ABS i”),
   (12, “(i:int) <= ABS i”),
   (13, “ABS (ABS (i:int)) = ABS i”),
   (19, “(x:int) < y ==> x - y < 0”),
   (20,
    “Num (int_max ((i:int) + j) 0) <=
     Num (int_max i 0) + Num (int_max j 0)”),
   (21, “(i:int) < j ==> Num (int_max (i - j) 0) = 0”),
   (27, “(i:int) % 42 <= 41”),
   (28, “-(i:int) * 1 = 0 ==> i = 0”),
   (29,
    “(0:int) < ABS i /\ ABS i * 1 < ABS i * j ==>
     1 < ABS i * j”),
   (50, “(0:int) < 1”),
   (52, “(47:int) + 11 < 8 * 15”),
   (53,
    “(a:num) <> b /\ (i:int) <> j /\ a < 2 /\ b < 2 ==>
     a + b <= Num (int_max (ABS i) (ABS j))”),
   (54,
    “(i:int) <> j /\ (a:num) <> b /\ a < 2 /\ b < 2 ==>
     a + b <= Num (int_max (ABS i) (ABS j))”)]

fun goal number =
  case List.find (fn (item, _) => item = number) carrier_goals of
      SOME (_, result) => result
    | NONE => lookup number linarithCorpus.core_arith_examples

fun entry number line representative : benchLib.source_goal =
  {id = "linarith_L" ^ Int.toString line, goal = goal number,
   source_method = "by linarith",
   provenance =
     {file = "src/HOL/ex/Arith_Examples.thy", line = line,
      commit = commit},
   representative = representative}

(* Goals 22, 23, 25, and 26 use an additional split fact; goals 47 and
   48 are oops examples.  Goal 32 is aconv-identical to goal 30 after
   translating Isabelle's meta equality, while goal 34 duplicates goal
   33 after translating Isabelle premise brackets to conjunction. *)
val source_index =
  [(1, 35), (2, 38), (3, 41), (4, 44), (5, 47), (6, 50),
   (7, 53), (8, 56), (9, 59), (10, 62), (11, 65), (12, 68),
   (13, 71), (14, 76), (15, 79), (16, 82), (17, 85),
   (18, 88), (19, 91), (20, 94), (21, 97), (24, 111),
   (27, 124), (28, 127), (29, 130), (30, 136), (31, 139),
   (33, 148), (35, 157), (36, 160), (37, 163),
   (38, 166), (39, 169), (40, 172), (41, 175), (42, 178),
   (43, 181), (44, 184), (45, 187), (46, 190), (49, 215),
   (50, 218), (51, 221), (52, 224), (53, 229), (54, 235)]

fun representative number =
  List.exists (equal number) [1, 3, 5, 19]

(* PresburgerEx.thy's one [arith] proof; its [presburger] proofs name
   a procedure the layer does not have and are not in the corpus. *)
val presburger_ex_arith : benchLib.source_goal =
  {id = "presburger_L102",
   goal =
     ``x3 = ABS x2 - x1 ==> x4 = ABS x3 - x2 ==>
       x5 = ABS x4 - x3 ==> x6 = ABS x5 - x4 ==>
       x7 = ABS x6 - x5 ==> x8 = ABS x7 - x6 ==>
       x9 = ABS x8 - x7 ==> x10 = ABS x9 - x8 ==>
       x11 = ABS x10 - x9 ==> x1 = x10 /\ x2 = (x11 : int)``,
   source_method = "by arith",
   provenance =
     {file = "src/HOL/ex/PresburgerEx.thy", line = 102, commit = commit},
   representative = false}

val raw_goals =
  map
    (fn (number, line) => entry number line (representative number))
    source_index @
  [presburger_ex_arith]

val goals = benchDerive.prepare "linarith" raw_goals

val shortfalls : benchLib.shortfall list = []

fun run level =
  benchLib.run_corpus_family
    {family = "linarith", goals = goals, shortfalls = shortfalls,
     budget = benchLib.default_budget,
     battery = [benchLib.Auto, benchLib.Aesop], level = level}

end
