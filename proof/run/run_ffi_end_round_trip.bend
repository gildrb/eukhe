# eukhe: the proof of LAW run_ffi_end_round_trip

import Base
import ../../bend/ffi_run.bend as FRn
import ../../bend/run.bend as Rn
import ../../bend/wire.bend as Wr
import ../../laws/run.bend as Run
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire

def rk.rt_end(x: Rn.End, +rest: String, +h: {Run.run.end_fits(x) == True{} : Bool}) -> {FRn.get_end(FRn.put_end(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.End>}:
  match x:
    case Rn.EndStop{}:
      {==}
    case Rn.EndReset{}:
      {==}
    case Rn.EndCapped{}:
      {==}
    case Rn.EndNext{+count}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(count, rest)), Wr.Got{count, rest}, Wire.wire_nat_round_trip(count, rest, h)) : {FRn.get_end.c3.f0(_) == Wr.Got{Rn.EndNext{count}, rest} : Wr.Dec<Rn.End>}
      {==}

def Run.run_ffi_end_round_trip(x, rest, h):
  rk.rt_end(x, rest, h)
