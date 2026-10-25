# eukhe: the proof of LAW throttle_ffi_step

import Base
import ../../bend/throttle.bend as Th
import ../../bend/ffi_throttle.bend as FTh
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip
import ../base/wire.bend as LWire
import ../../laws/throttle.bend as Throttle
import ./base.bend as LAThrottle

# PROOF of LAW throttle_ffi_step: the event reads back with nothing left (th.ev_rt) and the stepper's reply writer is the spec's speller (th.of).

def Throttle.throttle_ffi_step(g, e):
  %LAThrottle.th.ev_rt(e, "") : {FTh.step.ev(g, _) == Throttle.spell_moved(Th.step(g, e)) : FTh.St & String}
  LAThrottle.th.of(Th.step(g, e))
