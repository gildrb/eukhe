# eukhe: the proof of LAW flight_callers_get_its_outcome

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight/model.bend as AuthFlight
import ./base.bend as LA

def pf.got(s: F.St, inv: LA.auth_flight.pf.Inv(s), +k: Nat, +f: Nat, +o: F.Out, served: {List.get(&2, F.Leg, F.St.cs(s), k) == Some{F.Served{Some{f}, o}} : Maybe<&2, F.Leg>}) -> {List.get(&2, F.Out, F.W.landed(F.St.w(s)), f) == Some{o} : Maybe<&2, F.Out>}:
  match s:
    case F.St{w, +cs}:
      match w:
        case F.W{+sto, +fl, +ld, +n}:
          (cnt, all) = inv
          LA.pf.all_get(F.W{sto, fl, ld, n}, cs, k, F.Served{Some{f}, o}, served, all)

def pf.flight_callers_get_its_outcome(+evs: List<&2, F.Ev>, +k: Nat, +f: Nat, +o: F.Out, served: {List.get(&2, F.Leg, F.St.cs(F.run(evs)), k) == Some{F.Served{Some{f}, o}} : Maybe<&2, F.Leg>}) -> {List.get(&2, F.Out, F.W.landed(F.St.w(F.run(evs))), f) == Some{o} : Maybe<&2, F.Out>}:
  pf.got(F.run(evs), LA.pf.inv_run(evs), k, f, o, served)

def AuthFlight.flight_callers_get_its_outcome(evs, k, f, o, served):
  pf.flight_callers_get_its_outcome(evs, k, f, o, served)
