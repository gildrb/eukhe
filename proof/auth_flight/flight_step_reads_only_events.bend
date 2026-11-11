# eukhe: the proof of LAW flight_step_reads_only_events
# Whatever the entry's decoder reads from the input is an event spelled as
# the laws spell it, then the rest, and the event fits (LAE.ae.spelled).
# A failed read, or a rest that is not empty, answers the malformed-event
# error form, which the premise excludes; so the rest is empty, the input
# is the spelled event, and the entry steps F.desk.step on it (LAE.ae.put).

import Base
import ../../bend/auth_flight.bend as F
import ../../bend/ffi_auth_flight.bend as FA
import ../../bend/wire.bend as Wr
import ../../laws/auth_flight/entry.bend as AuthFlightEntry
import ./base/entry.bend as LAE

def aro.G(+d: F.Desk, s: String, a: FA.St & String) -> Type:
  &e: F.DEv -> {(s, (AuthFlightEntry.af_ev_fits(e), a)) == (AuthFlightEntry.af_spell_ev(e, ""), (True{}, AuthFlightEntry.af_step_of(F.desk.step(d, e)))) : String & (Bool & (FA.St & String))}

def aro.top(+d: F.Desk, +s: String, +e: F.DEv, -a: FA.St & String, h: {s == AuthFlightEntry.af_spell_ev(e, "") : String}, f: {AuthFlightEntry.af_ev_fits(e) == True{} : Bool}, ea: {a == AuthFlightEntry.af_step_of(F.desk.step(d, e)) : FA.St & String}) -> {(s, (AuthFlightEntry.af_ev_fits(e), a)) == (AuthFlightEntry.af_spell_ev(e, ""), (True{}, AuthFlightEntry.af_step_of(F.desk.step(d, e)))) : String & (Bool & (FA.St & String))}:
  %Equal.sym(String, s, AuthFlightEntry.af_spell_ev(e, ""), h) : {(_, (AuthFlightEntry.af_ev_fits(e), a)) == (AuthFlightEntry.af_spell_ev(e, ""), (True{}, AuthFlightEntry.af_step_of(F.desk.step(d, e)))) : String & (Bool & (FA.St & String))}
  %Equal.sym(Bool, AuthFlightEntry.af_ev_fits(e), True{}, f) : {(AuthFlightEntry.af_spell_ev(e, ""), (_, a)) == (AuthFlightEntry.af_spell_ev(e, ""), (True{}, AuthFlightEntry.af_step_of(F.desk.step(d, e)))) : String & (Bool & (FA.St & String))}
  %Equal.sym(FA.St & String, a, AuthFlightEntry.af_step_of(F.desk.step(d, e)), ea) : {(AuthFlightEntry.af_spell_ev(e, ""), (True{}, _)) == (AuthFlightEntry.af_spell_ev(e, ""), (True{}, AuthFlightEntry.af_step_of(F.desk.step(d, e)))) : String & (Bool & (FA.St & String))}
  {==}

def aro.fin(+d: F.Desk, +s: String, +e: F.DEv, r: String, h: {s == AuthFlightEntry.af_spell_ev(e, r) : String}, f: {AuthFlightEntry.af_ev_fits(e) == True{} : Bool}, other: {String.eq(AuthFlightEntry.af_reply(FA.step.fin(Wr.end(r), d, e)), Wr.err("auth_flight: malformed event")) == False{} : Bool}) -> aro.G(d, s, FA.step.fin(Wr.end(r), d, e)):
  match r:
    case SNil{}:
      (e, aro.top(d, s, e, FA.step.fin(True{}, d, e), h, f, LAE.ae.put(F.desk.step(d, e))))
    case SCon{c, t}:
      LAE.ae.tf(aro.G(d, s, FA.step.fin(False{}, d, e)), other)

def aro.main(+d: F.Desk, +s: String, r: Wr.Dec<F.DEv>, sp: LAE.ae.Spelled(s, r), other: {String.eq(AuthFlightEntry.af_reply(FA.step.go(d, r)), Wr.err("auth_flight: malformed event")) == False{} : Bool}) -> aro.G(d, s, FA.step.go(d, r)):
  match r:
    case Wr.Got{+e, +t}:
      (h, f) = sp
      aro.fin(d, s, e, t, h, f, other)
    case Wr.Bad{}:
      LAE.ae.tf(aro.G(d, s, FA.step.go(d, Wr.Bad{})), other)

def AuthFlightEntry.flight_step_reads_only_events(d, s, other):
  aro.main(d, s, FA.get_ev(Wr.get_nat(s)), LAE.ae.spelled(s), other)
