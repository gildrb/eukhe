# eukhe: the proof of LAW flight_after_end_stored

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight.bend as AuthFlight
import ./base.bend as LA

def pf.flight_after_end_stored(+evs: List<&2, F.Ev>, +k: Nat, +f: Nat, +c: Nat, lands: {List.get(&2, F.Leg, F.St.cs(F.run(evs)), k) == Some{F.Land{f, F.Ok{c}}} : Maybe<&2, F.Leg>}, +ok: Bool) -> {F.le(c, F.Sto.c(F.W.sto(F.St.w(F.step(F.run(evs), F.Step{k, ok}))))) == True{} : Bool}:
  LA.pf.stored(F.run(evs), LA.pf.inv_run(evs), k, f, c, lands, ok)

def AuthFlight.flight_after_end_stored(evs, k, f, c, lands, ok):
  pf.flight_after_end_stored(evs, k, f, c, lands, ok)
