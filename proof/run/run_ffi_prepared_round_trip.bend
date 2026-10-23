# eukhe: the proof of LAW run_ffi_prepared_round_trip

import Base
import ../../bend/ffi_run.bend as FRn
import ../../bend/run/decision.bend as RnDecision
import ../../bend/wire.bend as Wr
import ../../laws/run.bend as Run
import ../../laws/wire.bend as Wire
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip

def rk.rt_prepared(x: RnDecision.Prepared, +rest: String) -> {FRn.get_prepared(FRn.put_prepared(x, rest)) == Wr.Got{x, rest} : Wr.Dec<RnDecision.Prepared>}:
  match x:
    case RnDecision.Waits{}:
      {==}
    case RnDecision.Sends{+background}:
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(background, rest)), Wr.Got{background, rest}, Wire.wire_bool_round_trip(background, rest)) : {FRn.get_prepared.c1.f0(_) == Wr.Got{RnDecision.Sends{background}, rest} : Wr.Dec<RnDecision.Prepared>}
      {==}

def Run.run_ffi_prepared_round_trip(x, rest):
  rk.rt_prepared(x, rest)
