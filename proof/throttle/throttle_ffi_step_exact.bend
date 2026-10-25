# eukhe: the proof of LAW throttle_ffi_step_exact

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

# PROOF of LAW throttle_ffi_step_exact: what the decoder reads is spelled (th.pe); an event with input left over or a malformed one answers the error form.

def tsx.end(-s: String, r: String, +g: Th.Gate, +e: Th.Ev, p: {s == Throttle.spell_ev(e, r) : String}, ok: {LawsBase.wire_opens_err(Throttle.reply(FTh.step.end(Wr.end(r), g, e))) == False{} : Bool}) -> Sigma<&1, &1, Th.Ev, x => {s == Throttle.spell_ev(x, "") : String}>:
  match r:
    case SNil{}:
      (e, p)
    case SCon{h, t}:
      LAThrottle.th.absurd_t(Sigma<&1, &1, Th.Ev, x => {s == Throttle.spell_ev(x, "") : String}>, ok)

def tsx.ev(-s: String, +g: Th.Gate, d: Wr.Dec<Th.Ev>, p: LAThrottle.th.PE(s, d), ok: {LawsBase.wire_opens_err(Throttle.reply(FTh.step.ev(g, d))) == False{} : Bool}) -> Sigma<&1, &1, Th.Ev, x => {s == Throttle.spell_ev(x, "") : String}>:
  match d:
    case Wr.Got{+e, +r}:
      tsx.end(s, r, g, e, p, ok)
    case Wr.Bad{}:
      LAThrottle.th.absurd_t(Sigma<&1, &1, Th.Ev, x => {s == Throttle.spell_ev(x, "") : String}>, ok)

def Throttle.throttle_ffi_step_exact(g, s, ok):
  tsx.ev(s, g, FTh.get_ev(Wr.get_nat(s)), LAThrottle.th.pe(s), ok)
