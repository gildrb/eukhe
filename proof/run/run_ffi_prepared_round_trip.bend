# eukhe: the proof of LAW run_ffi_prepared_round_trip

import Base
import ../../bend/run.bend as Rn
import ../../bend/wire.bend as Wr
import ../../bend/ffi_run.bend as FRn
import ../../LAWS.bend as Laws
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip

def rk.rt_prepared(x: Rn.Prepared, +rest: String) -> {FRn.get_prepared(FRn.put_prepared(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.Prepared>}:
  match x:
    case Rn.Waits{}:
      {==}
    case Rn.Sends{+background}:
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(background, rest)), Wr.Got{background, rest}, Laws.wire_bool_round_trip(background, rest)) : {FRn.get_prepared.c1.f0(_) == Wr.Got{Rn.Sends{background}, rest} : Wr.Dec<Rn.Prepared>}
      {==}

def Laws.run_ffi_prepared_round_trip(x, rest):
  rk.rt_prepared(x, rest)
