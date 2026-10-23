# eukhe: the proof of LAW run_ffi_then_round_trip

import Base
import ../../bend/run.bend as Rn
import ../../bend/wire.bend as Wr
import ../../bend/ffi_run.bend as FRn
import ../../LAWS.bend as Laws

def rk.rt_then(x: Rn.Then, +rest: String) -> {FRn.get_then(FRn.put_then(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.Then>}:
  match x:
    case Rn.DoAnswer{}:
      {==}
    case Rn.DoTools{}:
      {==}
    case Rn.DoPoll{}:
      {==}
    case Rn.DoRetry{}:
      {==}
    case Rn.DoNote{}:
      {==}
    case Rn.DoCompact{}:
      {==}
    case Rn.DoFail{}:
      {==}
    case Rn.DoLate{}:
      {==}

def Laws.run_ffi_then_round_trip(x, rest):
  rk.rt_then(x, rest)
