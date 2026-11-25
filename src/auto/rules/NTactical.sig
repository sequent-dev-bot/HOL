signature NTactical =
sig
  include Abbrev

  type nresult = goal list * validation
  type ntactic = goal -> Context.t -> nresult seq.seq
  type wrapper = ntactic -> ntactic

  val LIFT : tactic -> ntactic
  val DETERM : ntactic -> tactic

  val NNO_TAC : ntactic
  val NALL_TAC : ntactic
  val NTHEN : ntactic * ntactic -> ntactic
  val NORELSE : ntactic * ntactic -> ntactic
  val NAPPEND : ntactic * ntactic -> ntactic
  val NTRY : ntactic -> ntactic
  val NREPEAT : ntactic -> ntactic
  val NCHANGED : ntactic -> ntactic
end
