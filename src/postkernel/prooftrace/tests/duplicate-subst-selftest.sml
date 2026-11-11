open Lib;
val x = Term.mk_var("x",Type.bool);
val y = Term.mk_var("y",Type.bool);
val z = Term.mk_var("z",Type.bool);
val v = Term.mk_var("v",Type.bool);
fun eq a b = let
  val equality = Term.mk_thy_const
    {Thy="min",Name="=",Ty=Type.--> (Type.bool,
                                    Type.--> (Type.bool,Type.bool))}
in Term.mk_comb(Term.mk_comb(equality,a),b) end;

val () = load_pft ["PFTReader","PFTReplay"];
val () = if identity_phase = "produce" then let
    val () = Theory.new_theory "pft_duplicate_subst"
    val source = Thm.REFL (eq x y)
    val expected = Thm.INST [y |-> x,x |-> z] source
    (* Current kernels reject the old proof constructors' duplicate lists.
       Attach them explicitly; replay must check their derived sequents. *)
    val inst = Thm.mk_proof_thm
      (Thm.INST_prf ([x |-> y,y |-> x,x |-> z],source))
      (Thm.hyp expected,Thm.concl expected)
    val () = ignore (Theory.save_thm("INST_LAST",inst))
    val equation = Thm.ASSUME (eq x z)
    val source = Thm.REFL x
    val template = eq v v
    val expected = Thm.SUBST [v |-> equation] template source
    val subst = Thm.mk_proof_thm
      (Thm.SUBST_prf ([v |-> equation,v |-> equation],template,source))
      (Thm.hyp expected,Thm.concl expected)
    val () = ignore (Theory.save_thm("SUBST_HYPS",subst))
    val () = Theory.export_theory ()
    val () = Theory.new_theory "pft_duplicate_subst_reject"
    val first = Thm.ASSUME (eq x y)
    val last = Thm.ASSUME (eq x z)
    val unsafe = Thm.mk_proof_thm
      (Thm.SUBST_prf ([v |-> first,v |-> last],template,Thm.REFL x))
      ([eq x y,eq x z],eq z z)
    val () = ignore (Theory.save_thm("DIFFERENT_EQUATIONS",unsafe))
  in Theory.export_theory () end
  else let
    fun check_pairs file ruleset = let
      fun skip _ = ()
      fun instruction opcode (reader:PFTReader.stream_reader) = let
        val desc = PFTOpcodes.lookup_desc
          (PFTOpcodes.descs_for_ruleset ruleset) opcode
        val () = List.app (fn _ => ignore (#readVarint reader ()))
          (#results desc)
        val args = PFTReader.read_raw_args desc reader
        fun distinct [] = ()
          | distinct ((v,_)::rest) =
              if List.exists (fn (w,_) => v = w) rest then
                raise Fail "duplicate redex remains in converted substitution"
              else distinct rest
        fun check (PFTOpcodes.VIdPairs pairs) = distinct pairs
          | check _ = ()
      in if #tag desc = "INST" orelse #tag desc = "SUBST" then
           List.app check args else () end
      val _ = PFTReader.read {file=file,binary=true,
        format_handler={tyvar=skip,tyop=skip,var=skip,const=skip,
          comb=skip,abs=skip,new_const=skip,new_type=skip,axiom=skip,
          save=skip,load=skip,del=skip,del_range=skip},
        ruleset_handler=instruction}
    in () end
    fun convert (name,ruleset) = let
      val output = "duplicate-subst." ^ name ^ ".pft.bin"
      val () = PFTEmit.emit_theory
        {trace=".hol/objs/pft_duplicate_substTheory.tr.gz",
         output=output,ruleset=ruleset}
      val () = check_pairs output name
      val rejected =
        (PFTEmit.emit_theory
          {trace=".hol/objs/pft_duplicate_subst_rejectTheory.tr.gz",
           output="rejected." ^ name ^ ".pft.bin",ruleset=ruleset}; false)
        handle Fail message =>
          if String.isPrefix "PFTEmit: SUBST repeats redex " message
          then true else raise Fail message
    in if rejected then print ("DUPLICATE_SUBST_CONVERT_PASS " ^ name ^ "\n")
       else raise Fail "differing duplicate SUBST equations were accepted"
    end
    val () = List.app convert
      [("hol4",PFTEmit.HOL4),("candle",PFTEmit.Candle)]
    val db = PFTReplay.replay PFTReplay.empty_trDB
      "duplicate-subst.hol4.pft.bin"
    fun check name expected_hyps expected_concl = let
      val th = valOf (PFTReplay.lookup db ("pft_duplicate_subst$" ^ name))
    in if ListPair.allEq (fn (a,b) => Term.aconv a b)
            (Thm.hyp th,expected_hyps) andalso
          Term.aconv (Thm.concl th) expected_concl then ()
       else raise Fail ("duplicate substitution sequent mismatch: " ^ name)
    end
    val result = eq z x
    val () = check "INST_LAST" [] (eq result result)
    val () = check "SUBST_HYPS" [eq x z] (eq z z)
  in print "DUPLICATE_SUBST_HOL_EXACT_PASS\n" end;
