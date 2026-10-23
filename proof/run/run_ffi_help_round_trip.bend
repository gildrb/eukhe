# eukhe: the proof of LAW run_ffi_help_round_trip

import Base
import ../../bend/run.bend as Rn
import ../../bend/wire.bend as Wr
import ../../bend/ffi_run.bend as FRn
import ../../LAWS.bend as Laws
import ../base.bend as L

def rk.rt_help(x: Rn.Help, +rest: String, +h: {Laws.run.help_fits(x) == True{} : Bool}) -> {FRn.get_help(FRn.put_help(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.Help>}:
  match x:
    case Rn.Runs{}:
      {==}
    case Rn.Redoes{+row}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(row, rest)), Wr.Got{row, rest}, Laws.wire_nat_round_trip(row, rest, h)) : {FRn.get_help.c1.f0(_) == Wr.Got{Rn.Redoes{row}, rest} : Wr.Dec<Rn.Help>}
      {==}
    case Rn.Stands{}:
      {==}
    case Rn.Quits{}:
      {==}

def Laws.run_ffi_help_round_trip(x, rest, h):
  rk.rt_help(x, rest, h)
