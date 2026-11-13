structure QUse :> QUse =
struct

val {print = emit, hadError} = HOLSourceParser.trackingPrint print
val failOnError = ref false
(* bench-only: split compile vs run CPU (usr+sys incl. GC) when set *)
val split_timing = ref false
val compile_time = ref Time.zeroTime
val run_time = ref Time.zeroTime
fun cpu_of t = let val {usr, sys} = Timer.checkCPUTimer t in Time.+ (usr, sys) end

fun use_reader fname {read = infn, fileline, eof} =
  let
    open PolyML
    fun line () = #line (fileline ()) + 1
  in
    while not (eof()) do (
      if !split_timing then
        let
          val t0 = Timer.startCPUTimer ()
          val code = compiler (infn, [Compiler.CPFileName fname, Compiler.CPLineNo line])
          val _ = compile_time := Time.+ (!compile_time, cpu_of t0)
          val t1 = Timer.startCPUTimer ()
        in
          (code () handle e => (run_time := Time.+ (!run_time, cpu_of t1); raise e));
          run_time := Time.+ (!run_time, cpu_of t1)
        end
      else
      compiler (infn, [Compiler.CPFileName fname, Compiler.CPLineNo line]) ();
      if !failOnError andalso hadError () then
        OS.Process.exit OS.Process.failure
      else ()
    )
  end

fun prim_use {quietOpen} fname =
    use_reader fname (HOLSource.fileToReader {quietOpen = quietOpen, print = emit} fname)

val use = prim_use {quietOpen = false}


fun useScript fname =
    let
      val istream = TextIO.openIn fname
      val reader =
        HOLSource.streamToReader {quietOpen = false, print = emit} fname istream
      val _ = use_reader fname reader
              handle e => (TextIO.closeIn istream; PolyML.Exception.reraise e)
    in
      TextIO.closeIn istream
    end

end
