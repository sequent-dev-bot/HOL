structure benchClassical =
struct

open HolKernel autoSeedTheory

val commit = "f7e02b7e"

(* Pelletier goals are owned by its separate corpus.  HOL4 aconv also
   collapses Isabelle lines 506/509/512/515/518/522/525 onto
   111/114/117/120/137/141/144, and line 780 onto line 375. *)

fun entry id line representative method goal : benchLib.source_goal =
  {id = id, goal = goal, source_method = method,
   provenance =
     {file = "src/HOL/ex/Classical.thy", line = line,
      commit = commit},
   representative = representative}

fun blast id line representative goal =
  entry id line representative "by blast" goal

val raw_goals =
  [blast "classical_L17" 17 true
     ``(p ==> q \/ r) ==> (p ==> q) \/ (p ==> r)``,
   blast "classical_L22" 22 true
     ``((p : bool) <=> q) <=> (q <=> p)``,
   blast "classical_L25" 25 true
     ``~((p : bool) <=> ~p)``,
   blast "classical_L111" 111 false
     ``(!x. P x /\ Q x) <=> (!x. P x) /\ (!x. Q x)``,
   blast "classical_L114" 114 false
     ``(?x. P ==> Q x) <=> (P ==> ?x. Q x)``,
   blast "classical_L117" 117 false
     ``(?x. P x ==> Q) <=> ((!x. P x) ==> Q)``,
   blast "classical_L120" 120 false
     ``((!x. P x) \/ Q) <=> (!x. P x \/ Q)``,
   blast "classical_L124" 124 true
     ``((!x. Q x ==> R x) /\ ~R a /\
        (!x. ~R x /\ ~Q x ==> P b \/ Q b)) ==>
       P b \/ R b``,
   blast "classical_L133" 133 false
     ``(?x. !y. P x <=> P y) ==>
       ((?x. P x) <=> (!y. P y))``,
   blast "classical_L137" 137 false
     ``(!x. P x ==> P (f x)) /\ P d ==> P (f (f (f d)))``,
   blast "classical_L141" 141 false
     ``?x. P x ==> P a /\ P b``,
   blast "classical_L144" 144 false
     ``?z. P z ==> (!x. P x)``,
   blast "classical_L147" 147 false
     ``?x. (?y. P y) ==> P x``,
   blast "classical_L322" 322 false
     ``(a = b \/ c = d) /\ (a = c \/ b = d) ==>
       a = d \/ b = c``,
   blast "classical_L333" 333 false
     ``(!x. P a x \/ (!y. P x y)) ==> (?x. !y. P x y)``,
   blast "classical_L337" 337 false
     ``(?z w. !x y. P x y <=> (x = z /\ y = w)) ==>
       (?z. !x. ?w. ((!y. P x y <=> y = w) <=> x = z))``,
   blast "classical_L362" 362 false
     ``(!x. (?y. P y /\ x = f y) ==> P x) <=>
       (!x. P x ==> P (f x))``,
   blast "classical_L366" 366 false
     ``P (f a b) (f b c) /\ P (f b c) (f a c) /\
       (!x y z. P x y /\ P y z ==> P x z) ==>
       P (f a b) (f a c)``,
   blast "classical_L375" 375 false
     ``(!x. P x <=> ~P (f x)) ==>
       (?x. P x /\ ~P (f x))``,
   blast "classical_L379" 379 false
     ``!x. P x (f x) <=>
       ?y. (!z. P z y ==> P z (f x)) /\ P x y``,
   blast "classical_L404" 404 false
     ``(!x. honest x /\ industrious x ==> healthy x) /\
       ~(?x. grocer x /\ healthy x) /\
       (!x. industrious x /\ grocer x ==> honest x) /\
       (!x. cyclist x ==> industrious x) /\
       (!x. ~healthy x /\ cyclist x ==> ~honest x) ==>
       (!x. grocer x ==> ~cyclist x)``,
   blast "classical_L412" 412 false
     ``(!x y. relr x y \/ relr y x) /\
       (!x y. rels x y /\ rels y x ==> x = y) /\
       (!x y. relr x y ==> rels x y) ==>
       (!x y. rels x y ==> relr x y)``,
   blast "classical_L776" 776 false
     ``!P Q R x. ?v w. !y z.
       P x /\ Q y ==> (P v \/ R w) /\ (R z ==> Q v)``,
   entry "classical_L803" 803 false "using a b d by blast"
     ``(!x y. (pred : 'a -> bool) (impf x (impf y x))) ==>
       (!x y z.
          pred
            (impf (impf x (impf y z))
              (impf (impf x y) (impf x z)))) ==>
       (!x y. pred (impf x y) /\ pred x ==> pred y) ==>
       (!x. pred (impf x x))``,
   blast "classical_L818" 818 false
     ``p1 <=> (p2 <=>
       (p3 <=> (p4 <=>
         (p5 <=> (p1 <=>
           (p2 <=> (p3 <=> (p4 <=> p5))))))))``]

val goals = benchDerive.prepare "classical" raw_goals

val shortfalls : benchLib.shortfall list = []

fun run level =
  benchLib.run_corpus_family
    {family = "classical", goals = goals, shortfalls = shortfalls,
     budget = benchLib.default_budget,
     battery = [benchLib.Auto, benchLib.Aesop], level = level}

end
