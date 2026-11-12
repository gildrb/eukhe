# eukhe: the proof of LAW dash_policy_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left (the
# decoder is the wire's string decoder: wire_str_round_trip), so the entry
# answers the model's verdict with its tag, which is Rust's (dpa.tag: case
# by case).

import Base
import ../../bend/dash_policy.bend as Dp
import ../../bend/ffi_dash_policy.bend as FDp
import ../../bend/wire.bend as Wr
import ../../laws/dash_policy.bend as DashPolicy
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire

def dpa.tag(v: Dp.Verdict) -> {FDp.tag(v) == DashPolicy.dp_tag(v) : Nat}:
  match v:
    case Dp.ForSession{}:
      {==}
    case Dp.ForCatalog{}:
      {==}
    case Dp.NotRun{}:
      {==}

def DashPolicy.dash_policy_entry_answers(n, h):
  %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(n, "")), Wr.Got{n, ""}, Wire.wire_str_round_trip(n, "", h)) : {FDp.ffi.got(_) == Wr.put_nat(DashPolicy.dp_tag(Dp.verdict(n)), "") : String}
  %dpa.tag(Dp.verdict(n)) : {Wr.put_nat(FDp.tag(Dp.verdict(n)), "") == Wr.put_nat(_, "") : String}
  {==}
