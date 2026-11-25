structure benchSets =
struct

open HolKernel autoSeedTheory

val commit = "f7e02b7e"

fun example id line method goal : benchLib.source_goal =
  {id = id, goal = goal, source_method = method,
   provenance =
     {file = "src/HOL/ex/Set_Theory.thy", line = line,
      commit = commit},
   representative = false}

val example_goals =
  [example "set_theory_L18" 18 "by blast"
     ``xset = yset UNION zset <=>
       yset SUBSET xset /\ zset SUBSET xset /\
       !vset. yset SUBSET vset /\ zset SUBSET vset ==>
         xset SUBSET vset``,
   example "set_theory_L22" 22 "by blast"
     ``xset = yset INTER zset <=>
       xset SUBSET yset /\ xset SUBSET zset /\
       !vset. vset SUBSET yset /\ vset SUBSET zset ==>
         vset SUBSET xset``,
   example "set_theory_L36" 36 "by blast"
     ``BIGUNION (IMAGE (\x. f x UNION g x) family) =
       BIGUNION (IMAGE f family) UNION
       BIGUNION (IMAGE g family)``,
   example "set_theory_L40" 40 "by blast"
     ``BIGINTER (IMAGE (\x. f x INTER g x) family) =
       BIGINTER (IMAGE f family) INTER
       BIGINTER (IMAGE g family)``,
   example "set_theory_L44" 44 "by blast"
     ``(!x. x IN (sets : 'a set set) ==>
          !y. y IN sets ==> x SUBSET y) ==>
       ?z. sets SUBSET {z}``,
   example "set_theory_L48" 48 "by blast"
     ``(!x. x IN (sets : 'a set set) ==> BIGUNION sets SUBSET x) ==>
       ?z. sets SUBSET {z}``,
   example "set_theory_L79" 79
     "using lfp_unfold [OF monoI, of F] by blast"
     ``?fixed. fixed = COMPL (IMAGE g (COMPL (IMAGE f fixed)))``,
   example "set_theory_L156" 156 "by force"
     ``?aset : int set. !x. x IN aset ==> x <= 0``,
   example "set_theory_L160" 160 "by force"
     ``d IN fam ==> ?groups. !aset. aset IN groups ==>
       ?bset. bset IN fam /\ aset SUBSET bset``,
   example "set_theory_L164" 164 "by force"
     ``P a ==> ?aset. (!x. x IN aset ==> P x) /\ ?y. y IN aset``,
   example "set_theory_L168" 168 "by auto"
     ``a < (b : int) /\ b < c ==>
       ?aset. a NOTIN aset /\ b IN aset /\ c NOTIN aset``,
   example "set_theory_L172" 172 "by force"
     ``P (f b) ==> ?s aset. (!x. x IN aset ==> P x) /\ f s IN aset``,
   example "set_theory_L180" 180 "by force"
     ``?aset. a NOTIN aset``,
   example "set_theory_L184" 184 "by force"
     ``(!u v : int. u < 0 ==> u <> ABS v) ==>
       ?aset : int set. -2 IN aset /\ !y. ABS y NOTIN aset``,
   example "set_theory_L199" 199 "by auto"
     ``((!aset : num set.
          0 IN aset /\ (!x. x IN aset ==> SUC x IN aset) ==>
            n IN aset) /\
        P 0 /\ (!x. P x ==> P (SUC x))) ==> P n``]

val translated_goals : benchLib.source_goal list =
  [{id = "set_L461_ball_cong_simp",
    goal = Thm.concl parityTranslationTheory.source_ball_cong_simp,
    source_method =
      "by (simp add: simp_implies_def Ball_def)",
    provenance =
      {file = "src/HOL/Set.thy", line = 461, commit = commit},
    representative = false},
   {id = "set_L471_bex_cong_simp",
    goal = Thm.concl parityTranslationTheory.source_bex_cong_simp,
    source_method =
      "by (simp add: simp_implies_def Bex_def cong: conj_cong)",
    provenance =
      {file = "src/HOL/Set.thy", line = 471, commit = commit},
    representative = false},
   {id = "set_L972_image_cong_simp",
    goal = Thm.concl parityTranslationTheory.source_image_cong_simp,
    source_method = "using that image_cong [of M N f g] " ^
                    "by (simp add: simp_implies_def)",
    provenance =
      {file = "src/HOL/Set.thy", line = 972, commit = commit},
    representative = false},
   {id = "set_L994_image_add_0",
    goal = Thm.concl parityTranslationTheory.source_image_add_zero,
    source_method = "by auto",
    provenance =
      {file = "src/HOL/Set.thy", line = 994, commit = commit},
    representative = false}]

val raw_goals = example_goals @ translated_goals @ benchSetCorpus.goals
val goals = benchDerive.prepare "sets" raw_goals

val shortfalls : benchLib.shortfall list = benchSetShortfalls.entries

fun run level =
  benchLib.run_corpus_family
    {family = "sets", goals = goals, shortfalls = shortfalls,
     budget = benchLib.default_budget,
     battery = [benchLib.Blast, benchLib.Aesop], level = level}

end
