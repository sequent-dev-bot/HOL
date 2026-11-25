structure benchListLex =
struct

open HolKernel

fun entry id line method goal : benchLib.source_goal =
  {id = id, goal = goal, source_method = method,
   provenance =
     {file = "src/HOL/List.thy", line = line, commit = "f7e02b7e"},
   representative = false}

val goals =
  [entry "list_L7247_lex_conv" 7247
     "by (force simp add: lex_def lexn_conv)"
     ``!relation xs ys.
         (parityTranslation$source_lex relation xs ys <=>
          LENGTH xs = LENGTH ys /\
          ?prefix left right xs' ys'.
            xs = prefix ++ (left::xs') /\
            ys = prefix ++ (right::ys') /\
            relation left right)``,
   entry "list_L7256_lenlex_conv" 7256
     "by (auto simp add: lenlex_def Id_on_def lex_prod_def inv_image_def)"
     ``!relation xs ys.
         (parityTranslation$source_lenlex relation xs ys <=>
          LENGTH xs < LENGTH ys \/
          (LENGTH xs = LENGTH ys /\
           parityTranslation$source_lex relation xs ys))``,
   entry "list_L7283_Nil_notin_lex" 7283
     "by (simp add: lex_conv)"
     ``!relation ys.
         ~parityTranslation$source_lex relation [] ys``,
   entry "list_L7286_Nil2_notin_lex" 7286
     "by (simp add: lex_conv)"
     ``!relation xs.
         ~parityTranslation$source_lex relation xs []``,
   entry "list_L7300_Nil_lenlex_iff1" 7300
     "by (auto simp: lenlex_def)"
     ``!relation xs.
         (parityTranslation$source_lenlex relation [] xs <=> xs <> [])``,
   entry "list_L7300_Nil_lenlex_iff2" 7300
     "by (auto simp: lenlex_def)"
     ``!relation xs.
         ~parityTranslation$source_lenlex relation xs []``,
   entry "list_L7304_Cons_lenlex_iff" 7304
     "by (auto simp: lenlex_def)"
     ``!relation left xs right ys.
         (parityTranslation$source_lenlex
            relation (left::xs) (right::ys) <=>
          LENGTH xs < LENGTH ys \/
          (LENGTH xs = LENGTH ys /\ relation left right) \/
          (left = right /\
           parityTranslation$source_lenlex relation xs ys))``,
   entry "list_L7318_lenlex_length" 7318
     "by (auto simp: lenlex_def)"
     ``!relation xs ys.
         parityTranslation$source_lenlex relation xs ys ==>
         LENGTH xs <= LENGTH ys``,
   entry "list_L7321_lex_append_rightI" 7321
     "by (fastforce simp: lex_def lexn_conv)"
     ``!relation xs ys us vs.
         parityTranslation$source_lex relation xs ys ==>
         LENGTH vs = LENGTH us ==>
         parityTranslation$source_lex
           relation (xs ++ us) (ys ++ vs)``,
   entry "list_L7387_lexord_same_pref_if_irrefl" 7387
     "by (simp add: irrefl_def lexord_same_pref_iff)"
     ``!relation.
         relation$irreflexive relation ==>
         !prefix xs ys.
           (parityTranslation$source_lexord relation
              (prefix ++ xs) (prefix ++ ys) <=>
            parityTranslation$source_lexord relation xs ys)``,
   entry "list_L7394_lexord_append_left_rightI" 7394
     "by (simp add: lexord_same_pref_iff)"
     ``!relation left right prefix xs ys.
         relation left right ==>
         parityTranslation$source_lexord relation
           (prefix ++ left::xs) (prefix ++ right::ys)``,
   entry "list_L7398_lexord_append_leftI" 7398
     "by (simp add: lexord_same_pref_iff)"
     ``!relation xs ys prefix.
         parityTranslation$source_lexord relation xs ys ==>
         parityTranslation$source_lexord relation
           (prefix ++ xs) (prefix ++ ys)``,
   (* The source premise is [(!a. (a,a) ~: r)], stated unfolded: the
      neighbouring [lexord_same_pref_if_irrefl] is the one stating
      [irrefl r], and that one cites [irrefl_def] to close.  Rendering
      this premise through HOL4's [irreflexive] asks the method to
      unfold a constant it does not name. *)
   entry "list_L7401_lexord_append_leftD" 7401
     "by (simp add: lexord_same_pref_iff)"
     ``!relation prefix xs ys.
         parityTranslation$source_lexord relation
           (prefix ++ xs) (prefix ++ ys) ==>
         (!item. ~relation item item) ==>
         parityTranslation$source_lexord relation xs ys``,
   entry "list_L7508_lexord_trans" 7508
     "by (auto simp: trans_def intro: lexord_partial_trans)"
     ``!relation xs ys zs.
         parityTranslation$source_lexord relation xs ys ==>
         parityTranslation$source_lexord relation ys zs ==>
         relation$transitive relation ==>
         parityTranslation$source_lexord relation xs zs``,
   entry "list_L7537_lexord_irrefl" 7537
     "by (simp add: irrefl_def lexord_irreflexive)"
     ``!relation.
         relation$irreflexive relation ==>
         relation$irreflexive
           (parityTranslation$source_lexord relation)``,
   entry "list_L7570_asym_lenlex" 7570
     "by (simp add: lenlex_def asym_inv_image asym_less_than asym_lex)"
     ``!relation.
         parityTranslation$source_asym relation ==>
         parityTranslation$source_asym
           (parityTranslation$source_lenlex relation)``,
   entry "list_L7716_lexordp_conv_lexord" 7716
     "by (simp add: lexordp_iff lexord_def)"
     ``!relation xs ys.
         relation$StrongLinearOrder relation ==>
         (parityTranslation$source_lexordp relation xs ys <=>
          parityTranslation$source_lexord relation xs ys)``,
   entry "list_L7752_lexordp_eq_conv_lexord" 7752
     "by (auto simp add: lexordp_conv_lexordp_eq lexordp_eq_refl \
      \dest: lexordp_eq_antisym)"
     ``!relation xs ys.
         relation$StrongLinearOrder relation ==>
         (parityTranslation$source_lexordp_eq relation xs ys <=>
          xs = ys \/
          parityTranslation$source_lexordp relation xs ys)``]

val shortfalls : benchLib.shortfall list = []

end
