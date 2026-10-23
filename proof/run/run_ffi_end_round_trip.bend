# eukhe: the proof of LAW run_ffi_end_round_trip

import Base
import ../../bend/run.bend as Rn
import ../../bend/wire.bend as Wr
import ../../bend/ffi_run.bend as FRn
import ../../LAWS.bend as Laws
import ../base.bend as L

def rk.rt_end(x: Rn.End, +rest: String, +h: {Laws.run.end_fits(x) == True{} : Bool}) -> {FRn.get_end(FRn.put_end(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.End>}:
  match x:
    case Rn.EndStop{}:
      {==}
    case Rn.EndReset{}:
      {==}
    case Rn.EndCapped{}:
      {==}
    case Rn.EndNext{+count}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(count, rest)), Wr.Got{count, rest}, Laws.wire_nat_round_trip(count, rest, h)) : {FRn.get_end.c3.f0(_) == Wr.Got{Rn.EndNext{count}, rest} : Wr.Dec<Rn.End>}
      {==}

def Laws.run_ffi_end_round_trip(x, rest, h):
  rk.rt_end(x, rest, h)
