Theory listAutoSeed
Ancestors
  list
Libs
  clasetLib clasimpLib

(* src/HOL/List.thy:874-993 @ f7e02b7e *)
Theorem LENGTH_EQ_0_AUTO[iff] = listTheory.LENGTH_EQ_0
Theorem LENGTH_NON_NIL_AUTO[iff] = listTheory.LENGTH_NON_NIL
Theorem APPEND_EQ_NIL_LEFT_AUTO[iff] = CONJUNCT1 listTheory.APPEND_eq_NIL
Theorem APPEND_EQ_NIL_RIGHT_AUTO[iff] = CONJUNCT2 listTheory.APPEND_eq_NIL
Theorem APPEND_EQ_SELF_1_AUTO[iff] = CONJUNCT1 listTheory.APPEND_EQ_SELF

Theorem APPEND_EQ_SELF_2_AUTO[iff] =
  CONJUNCT1 (CONJUNCT2 listTheory.APPEND_EQ_SELF)

Theorem APPEND_EQ_SELF_3_AUTO[iff] =
  CONJUNCT1 (CONJUNCT2 (CONJUNCT2 listTheory.APPEND_EQ_SELF))

Theorem APPEND_EQ_SELF_4_AUTO[iff] =
  CONJUNCT2 (CONJUNCT2 (CONJUNCT2 listTheory.APPEND_EQ_SELF))

Theorem APPEND_11_LEFT_AUTO[iff] = CONJUNCT1 listTheory.APPEND_11
Theorem APPEND_11_RIGHT_AUTO[iff] = CONJUNCT2 listTheory.APPEND_11
Theorem SNOC_11_AUTO[iff] = listTheory.SNOC_11

(* src/HOL/List.thy:1106,1115 @ f7e02b7e.  [map_map] and [map_eq_conv]
   are simp there and declared to no simpset here.  Without the first a
   map of a map stays two walks down the list; without the second an
   equality between two maps over one list is left as it stands, and
   the two mapped functions are never brought together -- neither
   simplification nor search has a step that relates them.  Together
   they read such an equality as the pointwise equality of the two
   functions on the list's elements, which the seeded pair quantifier
   takes apart where the elements are pairs. *)
Theorem MAP_MAP_o_AUTO[simp] = listTheory.MAP_MAP_o
Theorem MAP_EQ_f_AUTO[simp] = listTheory.MAP_EQ_f

(* src/HOL/List.thy:1123-1292 @ f7e02b7e *)
Theorem MAP_EQ_NIL_LEFT_AUTO[iff] =
  GEN_ALL (CONJUNCT1 (SPEC_ALL listTheory.MAP_EQ_NIL))

Theorem MAP_EQ_NIL_RIGHT_AUTO[iff] =
  GEN_ALL (CONJUNCT2 (SPEC_ALL listTheory.MAP_EQ_NIL))

Theorem MAP_EQ_CONS_AUTO[iff] = listTheory.MAP_EQ_CONS
Theorem REVERSE_EQ_NIL_AUTO[iff] = listTheory.REVERSE_EQ_NIL
Theorem REVERSE_11_AUTO[iff] = listTheory.REVERSE_11

(* src/HOL/List.thy:1222 @ f7e02b7e.  [rev_append] is simp there and
   declared to no simpset here.  HOL4's ambient REVERSE rules take the
   reversal off a membership, a length or an EVERY; none of them moves
   it past an append, so a law stated on an appended list is out of
   reach behind one -- a fold over an append stays whole where the
   source's simpset has already split it. *)
Theorem REVERSE_APPEND_AUTO[simp] = listTheory.REVERSE_APPEND

(* src/HOL/List.thy:3014-3042,6917-6970 @ f7e02b7e *)
Theorem LIST_REL_NIL_LEFT_AUTO[iff] =
  GEN_ALL (CONJUNCT1 (SPEC_ALL listTheory.LIST_REL_NIL))

Theorem LIST_REL_NIL_RIGHT_AUTO[iff] =
  GEN_ALL (CONJUNCT2 (SPEC_ALL listTheory.LIST_REL_NIL))

Theorem LIST_REL_CONS1_AUTO[iff] = listTheory.LIST_REL_CONS1
Theorem LIST_REL_CONS2_AUTO[iff] = listTheory.LIST_REL_CONS2
Theorem EVERY_APPEND_AUTO[iff] = listTheory.EVERY_APPEND
Theorem EVERY_MEM_AUTO[iff] = listTheory.EVERY_MEM

(* src/HOL/List.thy:1351 @ f7e02b7e.  [set_filter] reads a membership in
   a filtered list as the membership in the list and then the predicate;
   HOL4's MEM_FILTER states the predicate first.  A goal translated from
   the source states its own comprehensions the source's way round, so
   the two readings meet as an iff between the same two conjuncts in
   opposite orders -- which neither system's simplifier closes, both
   declaring associativity of the conjunction and not commutativity.
   The seed states the source's orientation. *)
Theorem MEM_FILTER_AUTO[iff]:
  !P L x. MEM x (FILTER P L) <=> MEM x L /\ P x
Proof
  metis_tac [listTheory.MEM_FILTER]
QED

Theorem LIST_REL_REVERSE_AUTO[iff]:
  !R left right.
    LIST_REL R (REVERSE left) (REVERSE right) <=> LIST_REL R left right
Proof
  metis_tac [LIST_REL_REVERSE, REVERSE_REVERSE]
QED

(* src/HOL/List.thy:1616,1635,1638 @ f7e02b7e.  [filter_append] is simp
   there and declared to no simpset here, and with it the two rules that
   collapse a filter whose predicate the list itself settles,
   [filter_True] and [filter_False].  HOL4 states the collapses as
   equivalences between an equation and an EVERY and declares neither,
   so a goal that filters across an append keeps the append whole, and
   the half whose elements the context already decides stays a filter
   beside the list it would reduce to.  The rest of the family,
   [length_filter_le] and [distinct_filter], is seeded in
   rich_listAutoSeed.  [filter_filter] is simp there as well and is
   left undeclared: a composite filter is settled by the collapses
   below, which read the inner walk's elements through the seeded
   MEM_FILTER_AUTO, so nothing reaches the rule that writes two walks as
   one. *)
Theorem FILTER_APPEND_DISTRIB_AUTO[simp] = listTheory.FILTER_APPEND_DISTRIB

Theorem FILTER_NONE_AUTO[simp]:
  !P l. EVERY (\item. ~P item) l ==> FILTER P l = []
Proof
  simp[listTheory.FILTER_EQ_NIL]
QED

Theorem FILTER_ID_AUTO[simp]:
  !P l. EVERY P l ==> FILTER P l = l
Proof
  simp[listTheory.FILTER_EQ_ID]
QED

(* src/HOL/List.thy:1348,1521 @ f7e02b7e.  [set_map] and [set_concat]
   are simp there, so a membership in a mapped or a flattened list is
   read as one in the image, or the union, the list is built from.  HOL4
   states the composite readings as MEM_MAP and MEM_FLAT and declares
   neither, so a membership in [MAP f xs] or [FLAT xss] is inert and the
   element it would name is never introduced.  The other two of the
   four, [set_append] and [set_filter], need no analogue here:
   MEM_APPEND is ambient, and MEM_FILTER is seeded above.

   Both are declared in the membership reading rather than the source's
   set reading, which is the reading the goals are in: [MEM x l] is
   [x IN set l] itself, so the set form is met as a subterm and leaves
   an image or a union membership where a membership already stood.

   The union is a rewrite and the image is not, which is the split the
   source makes: [UN_iff] of src/HOL/Complete_Lattices.thy:1052 is simp,
   while an image membership is left to [image_eqI] and [imageE] of
   src/HOL/Set.thy:882,893 -- an unsafe introduction and a safe
   elimination -- and [image_iff] beside them is declared to nothing.
   The split earns its keep here: a rewrite of the image reading reaches
   an enclosing membership before the MAP beneath it, and the ambient
   projections of a zip, which are conditional on the two sides having
   equal length, then never see the MAP they reduce.

   The elimination is declared safe, which is the class the source gives
   [imageE].  It stood unsafe here until 2026-09-20, on the reading that
   a safe elimination is tried at every node of the tableau and that its
   entirely schematic major premise would then meet the undetermined
   literals a witness-guessing branch leaves behind.  Measured across the
   six families that reading costs a goal and buys none: the safe class
   loses nothing, and it is what takes
   [list_L7054_set_trans_list_step_subset_trancl] of the list/map corpus
   apart, where a membership in a FLAT over a MAP over a FILTER stands
   past the two stages the assigned method runs the classical leg to --
   Isabelle's own [auto_tac ctxt = mk_auto_tac ctxt 4 2] of
   src/Provers/clasimp.ML.  Declared unsafe each decomposition spends a
   stage and the goal is left with the membership standing; declared
   safe they spend none, and what is then left is the closure those two
   edges have to be built into, which set_relationAutoSeed's rules
   close.  [set_L1610_Pow_Compl] of the sets corpus, the
   witness-guessing goal the unsafe reading was chosen for, runs to its
   budget under both classes and is a shortfall of its own either
   way. *)
Theorem MEM_FLAT_AUTO[simp] = listTheory.MEM_FLAT

(* The set reading of the same source rule, which the membership
   reading does not cover: a flattened list also stands as a set of its
   own, with no membership around it for MEM_FLAT_AUTO to meet.
   [list_L4011_length_remdups_concat] is where that shows -- its simp
   leaves [CARD (set (FLAT xss)) = CARD (BIGUNION (IMAGE set (set
   xss)))], two readings of one set under a CARD.  The rule is stated in
   the source's image form rather than HOL4's LIST_TO_SET_FLAT, whose
   [set (MAP set ls)] right-hand side would need the image reading of a
   mapped list, which this layer declines to declare for the reason
   above.  A membership still meets MEM_FLAT_AUTO first: it stands at
   the head of the term, and HOL4's traversal rewrites there before it
   reaches the set beneath. *)
Theorem LIST_TO_SET_FLAT_AUTO[simp]:
  !ls. set (FLAT ls) = BIGUNION (IMAGE set (set ls))
Proof
  simp[listTheory.LIST_TO_SET_FLAT, listTheory.LIST_TO_SET_MAP]
QED

(* src/HOL/Set.thy:1652,1663 @ f7e02b7e, at the mapped list
   src/HOL/List.thy:1348's [set_map] takes to an image.  The image
   clauses of [ball_simps] and [bex_simps] are simp there; seeded on
   the image in pred_setAutoSeed, they do not reach a list, whose
   membership HOL4 states as MEM and not as [IN set].  These are that
   reading, and they are not the image rewrite the split above
   declines: a bare [MEM y (MAP f xs)] is left alone, and only the
   membership a quantifier binds is taken -- which is the position
   MEM_FLAT_AUTO's right-hand side puts it in, and the only one where
   applying the function to the name costs nothing, the name being
   quantified in either reading.

   That position is where a flatten over a map stands.  Without these
   the membership stops at [?l. MEM l (MAP f xs) /\ MEM y l], whose l
   is fixed only by an equation under a further existential; with them
   it is [?x. MEM x xs /\ MEM y (f x)], and [f x] applied exposes the
   next layer, so a second flatten beneath the first is reached rather
   than left to a search that has to guess the list it names. *)
Theorem EXISTS_MEM_MAP_AUTO[simp]:
  !f P (xs : 'a list).
    (?y. MEM y (MAP f xs) /\ P y) <=> ?x. MEM x xs /\ P (f x)
Proof
  simp[listTheory.MEM_MAP] >> metis_tac[]
QED

Theorem FORALL_MEM_MAP_AUTO[simp]:
  !f P (xs : 'a list).
    (!y. MEM y (MAP f xs) ==> P y) <=> !x. MEM x xs ==> P (f x)
Proof
  simp[listTheory.MEM_MAP] >> metis_tac[]
QED

(* src/HOL/Set.thy:1650,1660 @ f7e02b7e, at the list src/HOL/List.thy
   states as a cons.  The insert clauses of [ball_simps] and
   [bex_simps] are simp there, and Isabelle's [set (x # xs)] is
   [insert x (set xs)], so a bounded quantifier over a cons meets them
   and splits off the head.  HOL4 states list membership as MEM, whose
   own cons equation is a simp rule too, and outermost-first that
   equation is the one a quantified membership descends into: the bound
   becomes a disjunction and no rule stated on the bounded quantifier
   matches it again.  What is left, [!e. e = x \/ MEM e xs ==> P e]
   against [P x /\ !e. MEM e xs ==> P e], is not closed by the ambient
   simpset -- measured -- and needs a distributive law and a one-point
   elimination that Isabelle never reaches for, because its clause
   fires above the membership and not inside it.  These are that
   clause; stated on the quantifier they are reached first, so the cons
   equation never runs on a bound. *)
Theorem FORALL_MEM_CONS_AUTO[simp]:
  !(x : 'a) xs P.
    (!e. MEM e (x::xs) ==> P e) <=> P x /\ !e. MEM e xs ==> P e
Proof
  metis_tac [listTheory.MEM]
QED

Theorem EXISTS_MEM_CONS_AUTO[simp]:
  !(x : 'a) xs P.
    (?e. MEM e (x::xs) /\ P e) <=> P x \/ ?e. MEM e xs /\ P e
Proof
  metis_tac [listTheory.MEM]
QED

Theorem MEM_MAP_IMAGE_AUTO[intro]:
  !f y x (xs : 'a list). y = f x /\ MEM x xs ==> MEM y (MAP f xs)
Proof
  metis_tac [listTheory.MEM_MAP]
QED

Theorem MEM_MAP_CASES_AUTO[sdest]:
  !f y (xs : 'a list). MEM y (MAP f xs) ==> ?x. y = f x /\ MEM x xs
Proof
  metis_tac [listTheory.MEM_MAP]
QED

(* src/HOL/List.thy:3475-3481 @ f7e02b7e.  The translated half-open
   interval [start..<finish] is GENLIST (\offset. start + offset)
   (finish - start), written here in the eta-contracted spelling the
   src/auto simpsets normalise to. *)
Theorem GENLIST_RANGE_SUC_AUTO[simp]:
  !start finish.
    start <= finish ==>
    GENLIST ($+ start) (SUC finish - start) =
    SNOC finish (GENLIST ($+ start) (finish - start))
Proof
  rpt strip_tac
  >> `SUC finish - start = SUC (finish - start)` by decide_tac
  >> `start + (finish - start) = finish` by decide_tac
  >> simp[listTheory.GENLIST]
QED

(* src/HOL/List.thy:1381 @ f7e02b7e.  [set_upt] rewrites the set of a
   half-open interval to the interval itself, whose membership Isabelle's
   ambient interval rules then decide; the translated interval is
   GENLIST (\offset. start + offset) (finish - start), so here the same
   consequence is one rewrite.

   The zero-start spelling below is a HOL4 normalisation artefact rather
   than a second Isabelle rule: Isabelle writes one term for every start,
   while HOL4's simplifier cancels the [0 +] and leaves an abstraction
   that no eta-instance of [$+ start] matches. *)
Theorem MEM_GENLIST_INTERVAL_AUTO[simp]:
  !start count item.
    MEM item (GENLIST ($+ start) count) <=>
    start <= item /\ item < start + count
Proof
  rpt gen_tac
  >> simp[listTheory.MEM_GENLIST]
  >> eq_tac
  >- (strip_tac >> simp[])
  >> strip_tac >> qexists_tac `item - start` >> simp[]
QED

Theorem MEM_GENLIST_FROM_ZERO_AUTO[simp]:
  !count item. MEM item (GENLIST (\offset. offset) count) <=> item < count
Proof
  rpt gen_tac >> simp[listTheory.MEM_GENLIST]
QED

(* src/HOL/List.thy:174-176,2700-2703 @ f7e02b7e.  zip is primrec on its
   second argument, so [zip xs [] = []] is simp there, [zip_Nil] and
   [zip_Cons_Cons] are declared beside it, and only [zip_Cons], the case
   split, is simp del.  HOL4 exports [ZIP], which is the cons/cons
   equation and the nil/nil instance of the other two, so a zip against a
   list empty on one side only stays whole.  Both general equations are
   conjuncts of ZIP_def. *)
Theorem ZIP_NIL_LEFT_AUTO[simp] = CONJUNCT1 listTheory.ZIP_def
Theorem ZIP_NIL_RIGHT_AUTO[simp] = CONJUNCT1 (CONJUNCT2 listTheory.ZIP_def)

(* src/HOL/List.thy:2749 @ f7e02b7e.  [zip_append] is simp there and
   undeclared here: HOL4 states the same fact as rich_list's ZIP_APPEND,
   which reads the two zips into one rather than the one into two and
   asks both pairs to be of equal length where the source asks it of the
   prefixes alone.  What the source's orientation buys is that a zip of
   two lists built the same way to the left comes apart, and its rules
   then meet the pieces: [list_L8044_listrel1_subset_listrel] is where
   that shows -- the two lists differ at one position, and split at it
   what is left is a diagonal zip on either side. *)
Theorem ZIP_APPEND_AUTO[simp]:
  !prefix left suffix right.
    LENGTH prefix = LENGTH left ==>
    ZIP (prefix ++ suffix, left ++ right) =
    ZIP (prefix, left) ++ ZIP (suffix, right)
Proof
  Induct >> Cases_on `left` >> fs[listTheory.ZIP_def]
QED

(* src/HOL/List.thy:1222-1228,2826-2827 @ f7e02b7e.  [map_fst_zip],
   [map_snd_zip] and [nth_zip] are simp there and undeclared here; HOL4's
   MAP_ZIP carries the two composed forms as well, which Isabelle reaches
   by rewriting under the map. *)
Theorem MAP_ZIP_AUTO[simp] = listTheory.MAP_ZIP
Theorem EL_ZIP_AUTO[simp] = listTheory.EL_ZIP

(* src/HOL/List.thy:1956 @ f7e02b7e.  [nth_mem] is simp there and
   declared to no simpset here, so a goal that indexes a list and then
   asks about membership stops at [MEM (EL index xs) xs] with the index
   bound already in hand. *)
Theorem EL_MEM_AUTO[simp] = listTheory.EL_MEM

(* src/HOL/List.thy:1830,1966-1969,2328,2337 @ f7e02b7e.  The rest of
   the indexing family, which Isabelle declares simp entire so that an
   index reaches through a list however the list was built: nth_map,
   nth_list_update_eq and _neq, nth_take, nth_drop.  HOL4 states each
   and declares none, which leaves a goal that characterises an
   operation by index with nothing to push the index through the
   constructor it was built with.  EL_LUPDATE is the two Isabelle
   update rules in one conditional equation; the zip case is seeded
   above with map_snd_zip. *)
Theorem EL_MAP_AUTO[simp] = listTheory.EL_MAP
Theorem EL_LUPDATE_AUTO[simp] = listTheory.EL_LUPDATE
Theorem EL_TAKE_AUTO[simp] = listTheory.EL_TAKE
Theorem EL_DROP_AUTO[simp] = listTheory.EL_DROP

(* src/HOL/List.thy:2247 @ f7e02b7e.  [take_take] is simp there and
   declared to no simpset here, so a take of a take stays two walks
   down the list and the length that decides it is never formed.  Its
   [drop_drop] counterpart is seeded in rich_listAutoSeed, which
   states it. *)
Theorem TAKE_TAKE_MIN_AUTO[simp] = listTheory.TAKE_TAKE_MIN

(* src/HOL/List.thy:2209 @ f7e02b7e.  [length_take] is simp there and
   is unconditional, the length being the smaller of the two.  HOL4
   declares the conditional reading, which says nothing about a take
   whose length is not already known to be within the list, and states
   the unconditional one as a conditional expression that no rule about
   MIN meets.  A bound on the length of a take is where a rule that
   reaches through the take gets its side condition. *)
Theorem LENGTH_TAKE_MIN_AUTO[simp]:
  !n (l : 'a list). LENGTH (TAKE n l) = MIN (LENGTH l) n
Proof
  rw[listTheory.LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >> fs[]
QED

(* src/HOL/List.thy @ f7e02b7e, [drop_append], [take_all] and
   [drop_all], simp there and declared to no simpset here.  Isabelle
   pushes a drop through an append and then reads off each half by its
   length; HOL4 states the three and carries none, so a rewrite that
   introduces [DROP n (l1 ++ l2)] leaves it and the subtracted length
   standing.  [take_append] is rich_list$TAKE_APPEND and is seeded
   with it. *)
Theorem DROP_APPEND_AUTO[simp] = listTheory.DROP_APPEND
Theorem TAKE_LENGTH_TOO_LONG_AUTO[simp] = listTheory.TAKE_LENGTH_TOO_LONG
Theorem DROP_LENGTH_TOO_LONG_AUTO[simp] = listTheory.DROP_LENGTH_TOO_LONG

(* src/HOL/List.thy @ f7e02b7e, the takeWhile and dropWhile primrecs.
   Both are primrec there, so both recursion equations are simp.  HOL4
   tags dropWhile_def and leaves takeWhile_def untagged -- it is the newer
   constant and its equations were added without changing any
   pre-existing simpset -- so the two halves of one decomposition
   reduce differently: a goal that walks a list drops its dropWhile
   away and keeps the takeWhile whole. *)
Theorem takeWhile_AUTO[simp] = listTheory.takeWhile_def

(* src/HOL/List.thy @ f7e02b7e, the results about those two that
   Isabelle declares simp: takeWhile_dropWhile_id, dropWhile_append1,
   dropWhile_append2, takeWhile_eq_all_conv and dropWhile_eq_Nil_conv.
   HOL4 states all five and declares none, so a goal that pushes a
   dropWhile through an append, or reads a takeWhile or a dropWhile off
   against the list it ran down, keeps both spellings side by side.

   dropWhile_id is simp there and is the implication from a predicate
   no element satisfies; HOL4's theorem of that name is the equivalence
   Isabelle calls dropWhile_eq_self_iff and leaves undeclared, so it is
   not seeded here. *)
Theorem takeWhile_APPEND_dropWhile_AUTO[simp] =
  listTheory.takeWhile_APPEND_dropWhile

Theorem dropWhile_APPEND_EVERY_AUTO[simp] = listTheory.dropWhile_APPEND_EVERY
Theorem dropWhile_APPEND_EXISTS_AUTO[simp] = listTheory.dropWhile_APPEND_EXISTS

Theorem takeWhile_id_AUTO[iff] = listTheory.takeWhile_id
Theorem dropWhile_eq_nil_AUTO[iff] = listTheory.dropWhile_eq_nil

(* src/HOL/List.thy:2559 @ f7e02b7e.  [set_takeWhileD] reads a member of
   a takeWhile as a member of the list that satisfies the predicate, and
   Isabelle declares it to no simpset and no claset.  HOL4 states its
   first half as [MEM_takeWhile_IMP] and carries the second only inside
   [EVERY_takeWhile], where nothing takes it apart: a walk stopped by
   its own predicate leaves an element of the prefix against the
   predicate it was taken by, and neither system's declared rules reach
   it.  Declared here as a dest rule, which is a declaration Isabelle
   does not make: the target is automation at least as strong as
   Isabelle's, and what is declared is a schema about the walk.  Its
   companion needs no declaration -- [MEM_takeWhile_IMP] gives
   membership in the list, which the goals reach by other routes. *)
Theorem MEM_takeWhile_HOLDS_AUTO[dest]:
  !P l x. MEM x (takeWhile P (l : 'a list)) ==> P x
Proof
  metis_tac [listTheory.EVERY_takeWhile, listTheory.EVERY_MEM]
QED

(* src/HOL/List.thy:7279 @ f7e02b7e.  Isabelle gives lexicographic
   transitivity to the classical reasoner as [intro], where HOL4 states it
   but declares it to no claset.  SHORTLEX carries it because HOL4's
   SHORTLEX R and Isabelle's lenlex r are the same order.  The rest of
   the lexicographic block needs nothing: [simp] already covers
   lexord_Nil_left, lexord_Nil_right and lexord_cons_cons through
   LLEX_THM and LLEX_NIL2, and lexord_transI carries no attribute, so
   LLEX_transitive gets none.

   wf_lenlex is [intro!] at 7253 and is not seeded here.  HOL4 carries
   WF_SHORTLEX as a [simp] rule, which already closes WF (SHORTLEX R)
   from WF R, and declaring it a *safe* intro rule instead owes
   seedAudit the invertibility obligation WF (SHORTLEX R) ==> WF R.
   That obligation is true but the audit's fixed prover stack does not
   close it, and an unproven safety claim is not worth the little the
   declaration would add. *)
Theorem SHORTLEX_TRANSITIVE_AUTO[intro] = listTheory.SHORTLEX_transitive

(* src/HOL/List.thy:254-257 @ f7e02b7e.  [successively] is a fun there,
   so its three defining equations are simp by construction, and it is
   the third of them --

     successively P (x # y # xs) = (P x y /\ successively P (y # xs))

   -- that [auto simp: distinct_adj_def] rewrites a successively over a
   cons with.  HOL4 has no such constant, and the translation states
   successively through [adjacent].  Its declared equations
   ([adjacent_thm]) settle the empty list, the singleton, and a pair
   that is the head of the list; a pair anywhere else is [adjacent_iff],
   which HOL4 states and declares to no simpset.  So unfolding a
   successively over a cons left an [adjacent] on that cons with nothing
   to take it apart.  The rule recurses into the tail, so it terminates
   where the list does. *)
Theorem adjacent_iff_AUTO[simp] = listTheory.adjacent_iff

(* src/HOL/List.thy:8499-8500 @ f7e02b7e.  Isabelle's [null] is defined
   by [null_iff], and that equation carries [simp]: a null is a list
   being empty, everywhere, before anything else is tried.  HOL4 states
   the same equation as [NULL_EQ] and declares it to no simpset, so
   NULL and [= []] are two spellings that never meet -- a goal reduced
   to the one is left standing against a rule or a hypothesis wearing
   the other.  HOL4's own NULL rules ([NULL_MAP], [NULL_APPEND],
   [NULL_GENLIST]) push a NULL through a list operation, which is not
   the step that is missing: they leave a NULL. *)
Theorem NULL_EQ_AUTO[simp] = listTheory.NULL_EQ

(* src/HOL/List.thy:70-71,262-264 @ f7e02b7e.  [last] and [remdups] are
   primrec there, so the cons equation of each is simp and reads a walk
   down a list whose tail is a variable: [last (x # xs)] becomes a
   choice on whether that tail is empty, and [remdups (x # xs)] one on
   whether the head recurs.  HOL4 states both equations -- the first as
   [LAST_CONS_cond], the second as the second conjunct of [nub_def] --
   and declares neither.  What it declares of LAST instead
   ([LAST_CONS]) settles a tail spelled [] or spelled as a cons and
   leaves a variable tail alone, and of nub only the empty list. *)
Theorem LAST_CONS_COND_AUTO[simp] = listTheory.LAST_CONS_cond
Theorem NUB_CONS_AUTO[simp] = CONJUNCT2 listTheory.nub_def

(* src/HOL/List.thy:1007 @ f7e02b7e.  [tl_append2] is simp there: a tail
   of an append reads as the tail of the first list wherever that list
   is known to be non-empty.  HOL4 states no equation about TL of an
   append at all, so the walk stops at the append and the non-emptiness
   in hand is never used. *)
Theorem TL_APPEND2_AUTO[simp]:
  !xs ys. xs <> [] ==> TL (xs ++ ys) = TL xs ++ ys
Proof
  Cases >> simp[]
QED

(* src/HOL/List.thy:2045,2085 @ f7e02b7e.  [butlast_snoc] and
   [append_butlast_last_id] are simp there, and both are stated on the
   append with a singleton: a list built by appending one element has
   its front read off, and a non-empty list is put back together from
   its front and its last.  HOL4 states the pair on SNOC ([FRONT_SNOC],
   [LAST_SNOC]) and keeps [SNOC_APPEND] out of the simpset by design,
   so a front of an append never reduces; [APPEND_FRONT_LAST] is
   declared to no simpset at all.  Of the append form only LAST
   reduces, through [LAST_APPEND_CONS], and the two spellings never
   meet. *)
Theorem FRONT_APPEND_SINGLETON_AUTO[simp]:
  !xs x. FRONT (xs ++ [x]) = xs
Proof
  REWRITE_TAC [GSYM listTheory.SNOC_APPEND, listTheory.FRONT_SNOC]
QED

Theorem APPEND_FRONT_LAST_AUTO[simp] = listTheory.APPEND_FRONT_LAST
