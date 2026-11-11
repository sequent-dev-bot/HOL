open HolKernel;
val () = Theory.new_theory "oracle_hyps";

val p = Term.mk_var ("p", Type.bool);
val q = Term.mk_var ("q", Type.bool);
val r = Term.mk_var ("r", Type.bool);
fun oracle sequent = Thm.mk_oracle_thm "PFT_ORACLE_REGRESSION" sequent;
fun save name th = ignore (Theory.save_thm (name, th));

val () = save "hyps" (oracle ([q, r], p));
val () = Theory.export_theory ();

val () = print "PFT_ORACLE_FIXTURES_PRODUCED\n";

val () = load_pft ["PFTReader","PFTMerge","PFTReplay"];
val () = use (test_source ^ "oracle-check-results.sml");

val separate = "oracle_hyps.pft.bin";
val () = PFTEmit.emit_theory
  {trace=".hol/objs/oracle_hypsTheory.tr.gz", output=separate,
   ruleset=PFTEmit.HOL4};
val () = check_oracle_results
  (PFTReplay.replay PFTReplay.empty_trDB separate);
val merged = "oracle_merged.pft.bin";
val () = PFTMerge.merge
  {inputs=[separate], targets=[PFTMerge.ThyAll ("oracle_hyps", false)],
   output=merged, binary=true};
val () = check_oracle_results
  (PFTReplay.replay PFTReplay.empty_trDB merged);
val () = List.app OS.FileSys.remove [separate, merged];
val () = print "PFT_ORACLE_SELFTEST_PASSED\n";
