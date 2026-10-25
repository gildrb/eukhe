# eukhe: the proof of LAW throttle_ffi_step_errors

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

# PROOF of LAW throttle_ffi_step_errors: an event the decoder reads whole answers the model's actions, never the error form (th.of_not_err); every other step keeps the throttle and answers the malformed error form.

def tsr.end(r: String, +g: Th.Gate, +e: Th.Ev, er: {LawsBase.wire_opens_err(Throttle.reply(FTh.step.end(Wr.end(r), g, e))) == True{} : Bool}) -> {FTh.step.end(Wr.end(r), g, e) == (FTh.Live{g}, Wr.err("throttle: malformed event")) : FTh.St & String}:
  match r:
    case SNil{}:
      LAThrottle.th.absurd({FTh.step.of(Th.step(g, e)) == (FTh.Live{g}, Wr.err("throttle: malformed event")) : FTh.St & String}, Equal.trans(Bool, False{}, LawsBase.wire_opens_err(Throttle.reply(FTh.step.of(Th.step(g, e)))), True{}, Equal.sym(Bool, LawsBase.wire_opens_err(Throttle.reply(FTh.step.of(Th.step(g, e)))), False{}, LAThrottle.th.of_not_err(Th.step(g, e))), er))
    case SCon{h, t}:
      {==}

def tsr.ev(+g: Th.Gate, d: Wr.Dec<Th.Ev>, er: {LawsBase.wire_opens_err(Throttle.reply(FTh.step.ev(g, d))) == True{} : Bool}) -> {FTh.step.ev(g, d) == (FTh.Live{g}, Wr.err("throttle: malformed event")) : FTh.St & String}:
  match d:
    case Wr.Got{+e, +r}:
      tsr.end(r, g, e, er)
    case Wr.Bad{}:
      {==}

def Throttle.throttle_ffi_step_errors(g, s, e):
  tsr.ev(g, FTh.get_ev(Wr.get_nat(s)), e)
