# eukhe: the proof of LAW flight_land_serves_joiners
# The desk finds caller k after pre (FR.fr.find); split on its place and
# the found: where the found lands the flight, the desk lands it (F.land):
# caller k leaves (FR.fr.cut), the callers waiting on p's flight leave
# (FR.fr.unwait) and are told done in order (FR.fr.wake). Every other
# pair contradicts the premise.

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight/entry.bend as S
import ../../laws/auth_flight/safety.bend as SS
import ../../laws/auth_flight/desk.bend as AuthFlightDesk
import ./base/entry.bend as LAE
import ./base/frame.bend as FR

# the desk and the reply the law states
def pls.R(+k: Nat, +p: String, +pre: List<&2, F.Cl>, +post: List<&2, F.Cl>, +n: Nat) -> F.DRes:
  F.DRes{F.Desk{AuthFlightDesk.af_others(p, List.append(&2, F.Cl, pre, post)), n}, F.Acts{F.To{k, F.DoDone{}} <> AuthFlightDesk.af_tell(F.DoDone{}, AuthFlightDesk.af_waiters(p, List.append(&2, F.Cl, pre, post)))}}

# a land of p's flight on the callers r: its joiners leave and are done
def pls.of(+k: Nat, +p: String, +r: List<&2, F.Cl>, +n: Nat) -> {F.DRes{F.Desk{F.unwait(p, r), n}, F.Acts{F.To{k, F.DoDone{}} <> F.wake(p, F.DoDone{}, r)}} == F.DRes{F.Desk{AuthFlightDesk.af_others(p, r), n}, F.Acts{F.To{k, F.DoDone{}} <> AuthFlightDesk.af_tell(F.DoDone{}, AuthFlightDesk.af_waiters(p, r))}} : F.DRes}:
  %Equal.sym(List<&2, F.Cl>, F.unwait(p, r), AuthFlightDesk.af_others(p, r), FR.fr.unwait(p, r)) : {F.DRes{F.Desk{_, n}, F.Acts{F.To{k, F.DoDone{}} <> F.wake(p, F.DoDone{}, r)}} == F.DRes{F.Desk{AuthFlightDesk.af_others(p, r), n}, F.Acts{F.To{k, F.DoDone{}} <> AuthFlightDesk.af_tell(F.DoDone{}, AuthFlightDesk.af_waiters(p, r))}} : F.DRes}
  %Equal.sym(List<&2, F.To>, F.wake(p, F.DoDone{}, r), AuthFlightDesk.af_tell(F.DoDone{}, AuthFlightDesk.af_waiters(p, r)), FR.fr.wake(p, F.DoDone{}, r)) : {F.DRes{F.Desk{AuthFlightDesk.af_others(p, r), n}, F.Acts{F.To{k, F.DoDone{}} <> _}} == F.DRes{F.Desk{AuthFlightDesk.af_others(p, r), n}, F.Acts{F.To{k, F.DoDone{}} <> AuthFlightDesk.af_tell(F.DoDone{}, AuthFlightDesk.af_waiters(p, r))}} : F.DRes}
  {==}

# the leader k lands its flight, between pre and post
def pls.land(+k: Nat, +p: String, +a: F.At, +pre: List<&2, F.Cl>, +post: List<&2, F.Cl>, +n: Nat, nl: {SS.af_live(k, pre) == False{} : Bool}) -> {F.land(k, p, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post), n) == pls.R(k, p, pre, post, n) : F.DRes}:
  Equal.trans(F.DRes, F.land(k, p, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post), n), F.DRes{F.Desk{F.unwait(p, List.append(&2, F.Cl, pre, post)), n}, F.Acts{F.To{k, F.DoDone{}} <> F.wake(p, F.DoDone{}, List.append(&2, F.Cl, pre, post))}}, pls.R(k, p, pre, post, n), Equal.cong(List<&2, F.Cl>, F.DRes, r => F.DRes{F.Desk{F.unwait(p, r), n}, F.Acts{F.To{k, F.DoDone{}} <> F.wake(p, F.DoDone{}, r)}}, F.cut(k, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post)), List.append(&2, F.Cl, pre, post), FR.fr.cut(k, pre, p, a, post, nl)), pls.of(k, p, List.append(&2, F.Cl, pre, post), n))

# the claim, after the found's caller is found
def pls.G(+a: F.At, +fd: F.Fd, +k: Nat, +p: String, +pre: List<&2, F.Cl>, +post: List<&2, F.Cl>, +n: Nat) -> Type:
  {F.found.fit(Nat.is_eq(F.At.tag(a), F.Fd.tag(fd)), fd, k, p, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post), n) == pls.R(k, p, pre, post, n) : F.DRes}

def pls.fit(a: F.At, fd: F.Fd, +k: Nat, +p: String, +pre: List<&2, F.Cl>, +post: List<&2, F.Cl>, +n: Nat, nl: {SS.af_live(k, pre) == False{} : Bool}, lands: {S.af_lands(a, fd) == True{} : Bool}) -> pls.G(a, fd, k, p, pre, post, n):
  match a:
    case F.Loads{}:
      LAE.ae.ft(pls.G(F.Loads{}, fd, k, p, pre, post, n), lands)
    case F.Checks{}:
      match fd:
        case F.LoadFresh{}:
          LAE.ae.ft(pls.G(F.Checks{}, F.LoadFresh{}, k, p, pre, post, n), lands)
        case F.LoadExpired{}:
          LAE.ae.ft(pls.G(F.Checks{}, F.LoadExpired{}, k, p, pre, post, n), lands)
        case F.LoadFailed{}:
          LAE.ae.ft(pls.G(F.Checks{}, F.LoadFailed{}, k, p, pre, post, n), lands)
        case F.CheckFresh{}:
          pls.land(k, p, F.Checks{}, pre, post, n, nl)
        case F.CheckExpired{}:
          LAE.ae.ft(pls.G(F.Checks{}, F.CheckExpired{}, k, p, pre, post, n), lands)
        case F.FetchOk{}:
          LAE.ae.ft(pls.G(F.Checks{}, F.FetchOk{}, k, p, pre, post, n), lands)
        case F.FetchFailed{}:
          LAE.ae.ft(pls.G(F.Checks{}, F.FetchFailed{}, k, p, pre, post, n), lands)
        case F.Stored{}:
          LAE.ae.ft(pls.G(F.Checks{}, F.Stored{}, k, p, pre, post, n), lands)
    case F.Fetches{}:
      match fd:
        case F.LoadFresh{}:
          LAE.ae.ft(pls.G(F.Fetches{}, F.LoadFresh{}, k, p, pre, post, n), lands)
        case F.LoadExpired{}:
          LAE.ae.ft(pls.G(F.Fetches{}, F.LoadExpired{}, k, p, pre, post, n), lands)
        case F.LoadFailed{}:
          LAE.ae.ft(pls.G(F.Fetches{}, F.LoadFailed{}, k, p, pre, post, n), lands)
        case F.CheckFresh{}:
          LAE.ae.ft(pls.G(F.Fetches{}, F.CheckFresh{}, k, p, pre, post, n), lands)
        case F.CheckExpired{}:
          LAE.ae.ft(pls.G(F.Fetches{}, F.CheckExpired{}, k, p, pre, post, n), lands)
        case F.FetchOk{}:
          LAE.ae.ft(pls.G(F.Fetches{}, F.FetchOk{}, k, p, pre, post, n), lands)
        case F.FetchFailed{}:
          pls.land(k, p, F.Fetches{}, pre, post, n, nl)
        case F.Stored{}:
          LAE.ae.ft(pls.G(F.Fetches{}, F.Stored{}, k, p, pre, post, n), lands)
    case F.Stores{}:
      match fd:
        case F.LoadFresh{}:
          LAE.ae.ft(pls.G(F.Stores{}, F.LoadFresh{}, k, p, pre, post, n), lands)
        case F.LoadExpired{}:
          LAE.ae.ft(pls.G(F.Stores{}, F.LoadExpired{}, k, p, pre, post, n), lands)
        case F.LoadFailed{}:
          LAE.ae.ft(pls.G(F.Stores{}, F.LoadFailed{}, k, p, pre, post, n), lands)
        case F.CheckFresh{}:
          LAE.ae.ft(pls.G(F.Stores{}, F.CheckFresh{}, k, p, pre, post, n), lands)
        case F.CheckExpired{}:
          LAE.ae.ft(pls.G(F.Stores{}, F.CheckExpired{}, k, p, pre, post, n), lands)
        case F.FetchOk{}:
          LAE.ae.ft(pls.G(F.Stores{}, F.FetchOk{}, k, p, pre, post, n), lands)
        case F.FetchFailed{}:
          LAE.ae.ft(pls.G(F.Stores{}, F.FetchFailed{}, k, p, pre, post, n), lands)
        case F.Stored{}:
          pls.land(k, p, F.Stores{}, pre, post, n, nl)
    case F.Waits{}:
      LAE.ae.ft(pls.G(F.Waits{}, fd, k, p, pre, post, n), lands)

def AuthFlightDesk.flight_land_serves_joiners(pre, post, n, k, p, a, first, fd, lands):
  +nl = first
  %Equal.sym(Maybe<&2, F.Cl>, F.find(k, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post)), Some{F.Cl{k, p, a}}, FR.fr.find(k, pre, p, a, post, nl)) : {F.found(_, fd, k, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post), n) == pls.R(k, p, pre, post, n) : F.DRes}
  pls.fit(a, fd, k, p, pre, post, n, nl, lands)
