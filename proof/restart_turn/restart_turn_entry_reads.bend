# eukhe: the proof of LAW restart_turn_entry_reads
#
# PROOF: the tag computes; the count made reads back by
# wire_nat_round_trip (it fits by the premise).

import Base
import ../../bend/restart_turn.bend as Rt
import ../../bend/ffi_restart_turn.bend as FRt
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/restart_turn.bend as RestartTurn
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire

def RestartTurn.restart_turn_entry_reads(f, rest, h):
  match f:
    case Rt.Reopened{+n}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h)) : {FRt.get_req.reopened(_) == Wr.Got{Rt.Reopened{n}, rest} : Wr.Dec<Rt.Fact>}
      {==}
    case Rt.GaveUp{p}:
      match p:
        case Rt.Clear{}:
          {==}
        case Rt.Unsettled{}:
          {==}
        case Rt.Ended{}:
          {==}
