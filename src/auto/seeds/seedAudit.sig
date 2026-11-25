signature seedAudit =
sig
  include Abbrev

  type waiver = {rule : string, reason : string, date : string}

  datatype obligation_kind =
      SafeZero
    | IntroInversion
    | ElimExhaustiveness
    | ElimPreservation of int
    | KernelPreservation
    | SplitShape

  type obligation = {kind : obligation_kind, term : term}

  datatype result =
      Proved of {rule : string, kind : obligation_kind,
                 prover : string, elapsed : Time.time}
    | Waived of {rule : string, kind : obligation_kind,
                 waiver : waiver, detail : string}
    | Failed of {rule : string, kind : obligation_kind,
                 detail : string}

  type report = {
    checked : int,
    proved : int,
    waivers : waiver list,
    results : result list,
    split_checked : int
  }

  val default_budget : Time.time

  val obligations : clasetLib.aesop_rule -> obligation list

  val inspect : {
    claset : clasetLib.claset,
    budget : Time.time,
    waivers : waiver list
  } -> report

  val audit_with : {
    claset : clasetLib.claset,
    budget : Time.time,
    waivers : waiver list
  } -> report

  val audit : {waivers : waiver list} -> report
end
