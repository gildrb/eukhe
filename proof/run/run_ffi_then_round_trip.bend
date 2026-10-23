# eukhe: the proof of LAW run_ffi_then_round_trip

import Base
import ../../bend/ffi_run.bend as FRn
import ../../bend/run/decision.bend as RnDecision
import ../../bend/wire.bend as Wr
import ../../laws/run.bend as Run

def rk.rt_then(x: RnDecision.Then, +rest: String) -> {FRn.get_then(FRn.put_then(x, rest)) == Wr.Got{x, rest} : Wr.Dec<RnDecision.Then>}:
  match x:
    case RnDecision.DoAnswer{}:
      {==}
    case RnDecision.DoTools{}:
      {==}
    case RnDecision.DoPoll{}:
      {==}
    case RnDecision.DoRetry{}:
      {==}
    case RnDecision.DoNote{}:
      {==}
    case RnDecision.DoCompact{}:
      {==}
    case RnDecision.DoFail{}:
      {==}
    case RnDecision.DoLate{}:
      {==}

def Run.run_ffi_then_round_trip(x, rest):
  rk.rt_then(x, rest)
