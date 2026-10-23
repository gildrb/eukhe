# eukhe: the proof of LAW run_ffi_end_round_trip

import Base
import ../../bend/ffi_run.bend as FRn
import ../../bend/run/decision.bend as RnDecision
import ../../bend/wire.bend as Wr
import ../../laws/run.bend as Run
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire

def rk.rt_end(x: RnDecision.End, +rest: String, +h: {Run.run.end_fits(x) == True{} : Bool}) -> {FRn.get_end(FRn.put_end(x, rest)) == Wr.Got{x, rest} : Wr.Dec<RnDecision.End>}:
  match x:
    case RnDecision.EndStop{}:
      {==}
    case RnDecision.EndReset{}:
      {==}
    case RnDecision.EndCapped{}:
      {==}
    case RnDecision.EndNext{+count}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(count, rest)), Wr.Got{count, rest}, Wire.wire_nat_round_trip(count, rest, h)) : {FRn.get_end.c3.f0(_) == Wr.Got{RnDecision.EndNext{count}, rest} : Wr.Dec<RnDecision.End>}
      {==}

def Run.run_ffi_end_round_trip(x, rest, h):
  rk.rt_end(x, rest, h)
