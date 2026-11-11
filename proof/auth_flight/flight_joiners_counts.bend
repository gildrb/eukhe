# eukhe: the proof of LAW flight_joiners_counts
# The desk's in-flight test is the laws' (LAE.ae.inflight); with a flight
# in flight its count is how many wait on it (FR.fr.joined).

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight/desk.bend as AuthFlightDesk
import ./base/entry.bend as LAE
import ./base/frame.bend as FR

def pjc.at(fl: Bool, +p: String, +cs: List<&2, F.Cl>, +n: Nat) -> {F.DRes{F.Desk{cs, n}, F.Joined{F.joiners(fl, p, cs)}} == F.DRes{F.Desk{cs, n}, F.Joined{AuthFlightDesk.af_count(fl, p, cs)}} : F.DRes}:
  match fl:
    case True{}:
      %Equal.sym(Nat, F.joined(p, cs), List.length(&2, F.Cl, AuthFlightDesk.af_waiters(p, cs)), FR.fr.joined(p, cs)) : {F.DRes{F.Desk{cs, n}, F.Joined{Some{_}}} == F.DRes{F.Desk{cs, n}, F.Joined{Some{List.length(&2, F.Cl, AuthFlightDesk.af_waiters(p, cs))}}} : F.DRes}
      {==}
    case False{}:
      {==}

def AuthFlightDesk.flight_joiners_counts(cs, n, p):
  %LAE.ae.inflight(p, cs) : {F.DRes{F.Desk{cs, n}, F.Joined{F.joiners(F.inflight(p, cs), p, cs)}} == F.DRes{F.Desk{cs, n}, F.Joined{AuthFlightDesk.af_count(_, p, cs)}} : F.DRes}
  pjc.at(F.inflight(p, cs), p, cs, n)
