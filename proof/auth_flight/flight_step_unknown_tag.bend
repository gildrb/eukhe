# eukhe: the proof of LAW flight_step_unknown_tag
# An encoded tag past 3 (or a found past 7, after a caller that reads
# back) reads back as itself, or Bad when too long
# (LAWireSpell.ws_nat_read); either way the entry answers its error form
# and keeps the desk.

import Base
import ../../bend/auth_flight.bend as F
import ../../bend/ffi_auth_flight.bend as FA
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/auth_flight/entry.bend as AuthFlightEntry
import ../wire/base/spell.bend as LAWireSpell
import ../base/wire.bend as LWire

def afu.tag(b: Bool, +d: F.Desk, +n: Nat, +rest: String) -> {FA.step.go(d, FA.get_ev(LAWireSpell.ws_nat_answer(b, 4n+n, rest))) == (FA.Open{d}, SCon{'E', SCon{' ', "auth_flight: malformed event"}}) : FA.St & String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def afu.what(b: Bool, +d: F.Desk, +k: Nat, +n: Nat, +rest: String) -> {FA.step.go(d, FA.get_ev.found(k, LAWireSpell.ws_nat_answer(b, 8n+n, rest))) == (FA.Open{d}, SCon{'E', SCon{' ', "auth_flight: malformed event"}}) : FA.St & String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def afu.first(+d: F.Desk, +n: Nat, +r: String) -> {FA.step(FA.Open{d}, Wr.put_nat(4n+n, r)) == (FA.Open{d}, SCon{'E', SCon{' ', "auth_flight: malformed event"}}) : FA.St & String}:
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(4n+n, r)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(4n+n), 4n+n, r), LAWireSpell.ws_nat_read(4n+n, r)) : {FA.step.go(d, FA.get_ev(_)) == (FA.Open{d}, SCon{'E', SCon{' ', "auth_flight: malformed event"}}) : FA.St & String}
  afu.tag(LawsBase.wire_fits(4n+n), d, n, r)

def afu.second(+d: F.Desk, +n: Nat, +r: String, +k: Nat, fits: {LawsBase.wire_fits(k) == True{} : Bool}) -> {FA.step(FA.Open{d}, Wr.put_nat(1n, Wr.put_nat(k, Wr.put_nat(8n+n, r)))) == (FA.Open{d}, SCon{'E', SCon{' ', "auth_flight: malformed event"}}) : FA.St & String}:
  %LWire.pw6.nat(1n, Wr.put_nat(k, Wr.put_nat(8n+n, r)), {==}) : {FA.step.go(d, FA.get_ev(_)) == (FA.Open{d}, SCon{'E', SCon{' ', "auth_flight: malformed event"}}) : FA.St & String}
  %LWire.pw6.nat(k, Wr.put_nat(8n+n, r), fits) : {FA.step.go(d, FA.get_ev.caller(_)) == (FA.Open{d}, SCon{'E', SCon{' ', "auth_flight: malformed event"}}) : FA.St & String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(8n+n, r)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(8n+n), 8n+n, r), LAWireSpell.ws_nat_read(8n+n, r)) : {FA.step.go(d, FA.get_ev.found(k, _)) == (FA.Open{d}, SCon{'E', SCon{' ', "auth_flight: malformed event"}}) : FA.St & String}
  afu.what(LawsBase.wire_fits(8n+n), d, k, n, r)

def AuthFlightEntry.flight_step_unknown_tag(d, n, rest, k, fits):
  (afu.first(d, n, rest), afu.second(d, n, rest, k, fits))
