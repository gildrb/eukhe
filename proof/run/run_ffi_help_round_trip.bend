# eukhe: the proof of LAW run_ffi_help_round_trip

import Base
import ../../bend/ffi_run.bend as FRn
import ../../bend/run.bend as Rn
import ../../bend/wire.bend as Wr
import ../../laws/run.bend as Run
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire

def rk.rt_help(x: Rn.Help, +rest: String, +h: {Run.run.help_fits(x) == True{} : Bool}) -> {FRn.get_help(FRn.put_help(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.Help>}:
  match x:
    case Rn.Runs{}:
      {==}
    case Rn.Redoes{+row}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(row, rest)), Wr.Got{row, rest}, Wire.wire_nat_round_trip(row, rest, h)) : {FRn.get_help.c1.f0(_) == Wr.Got{Rn.Redoes{row}, rest} : Wr.Dec<Rn.Help>}
      {==}
    case Rn.Stands{}:
      {==}
    case Rn.Quits{}:
      {==}

def Run.run_ffi_help_round_trip(x, rest, h):
  rk.rt_help(x, rest, h)
