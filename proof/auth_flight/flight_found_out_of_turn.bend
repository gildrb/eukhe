# eukhe: the proof of LAW flight_found_out_of_turn
# The desk finds caller k after pre (FR.fr.find); split on its place and
# the found: where the found does not answer the place's act, the place's
# step and the found's differ (F.At.tag, F.Fd.tag) and the desk answers
# out of turn with the desk kept; every other pair contradicts the
# premise.

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight/desk.bend as AuthFlightDesk
import ../../laws/auth_flight/safety.bend as SS
import ./base/entry.bend as LAE
import ./base/frame.bend as FR

# the claim, after the found's caller is found
def pfo.G(+a: F.At, +fd: F.Fd, +k: Nat, +p: String, +pre: List<&2, F.Cl>, +post: List<&2, F.Cl>, +n: Nat) -> Type:
  {F.found.fit(Nat.is_eq(F.At.tag(a), F.Fd.tag(fd)), fd, k, p, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post), n) == F.DRes{F.Desk{List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post), n}, F.Off{}} : F.DRes}

def pfo.fit(a: F.At, fd: F.Fd, +k: Nat, +p: String, +pre: List<&2, F.Cl>, +post: List<&2, F.Cl>, +n: Nat, off: {AuthFlightDesk.af_answers(AuthFlightDesk.af_place_act(a), fd) == False{} : Bool}) -> pfo.G(a, fd, k, p, pre, post, n):
  match a:
    case F.Loads{}:
      match fd:
        case F.LoadFresh{}:
          LAE.ae.tf(pfo.G(F.Loads{}, F.LoadFresh{}, k, p, pre, post, n), off)
        case F.LoadExpired{}:
          LAE.ae.tf(pfo.G(F.Loads{}, F.LoadExpired{}, k, p, pre, post, n), off)
        case F.LoadFailed{}:
          LAE.ae.tf(pfo.G(F.Loads{}, F.LoadFailed{}, k, p, pre, post, n), off)
        case F.CheckFresh{}:
          {==}
        case F.CheckExpired{}:
          {==}
        case F.FetchOk{}:
          {==}
        case F.FetchFailed{}:
          {==}
        case F.Stored{}:
          {==}
    case F.Checks{}:
      match fd:
        case F.LoadFresh{}:
          {==}
        case F.LoadExpired{}:
          {==}
        case F.LoadFailed{}:
          {==}
        case F.CheckFresh{}:
          LAE.ae.tf(pfo.G(F.Checks{}, F.CheckFresh{}, k, p, pre, post, n), off)
        case F.CheckExpired{}:
          LAE.ae.tf(pfo.G(F.Checks{}, F.CheckExpired{}, k, p, pre, post, n), off)
        case F.FetchOk{}:
          {==}
        case F.FetchFailed{}:
          {==}
        case F.Stored{}:
          {==}
    case F.Fetches{}:
      match fd:
        case F.LoadFresh{}:
          {==}
        case F.LoadExpired{}:
          {==}
        case F.LoadFailed{}:
          {==}
        case F.CheckFresh{}:
          {==}
        case F.CheckExpired{}:
          {==}
        case F.FetchOk{}:
          LAE.ae.tf(pfo.G(F.Fetches{}, F.FetchOk{}, k, p, pre, post, n), off)
        case F.FetchFailed{}:
          LAE.ae.tf(pfo.G(F.Fetches{}, F.FetchFailed{}, k, p, pre, post, n), off)
        case F.Stored{}:
          {==}
    case F.Stores{}:
      match fd:
        case F.LoadFresh{}:
          {==}
        case F.LoadExpired{}:
          {==}
        case F.LoadFailed{}:
          {==}
        case F.CheckFresh{}:
          {==}
        case F.CheckExpired{}:
          {==}
        case F.FetchOk{}:
          {==}
        case F.FetchFailed{}:
          {==}
        case F.Stored{}:
          LAE.ae.tf(pfo.G(F.Stores{}, F.Stored{}, k, p, pre, post, n), off)
    case F.Waits{}:
      match fd:
        case F.LoadFresh{}:
          {==}
        case F.LoadExpired{}:
          {==}
        case F.LoadFailed{}:
          {==}
        case F.CheckFresh{}:
          {==}
        case F.CheckExpired{}:
          {==}
        case F.FetchOk{}:
          {==}
        case F.FetchFailed{}:
          {==}
        case F.Stored{}:
          {==}

def AuthFlightDesk.flight_found_out_of_turn(pre, post, n, k, p, a, first, fd, off):
  %Equal.sym(Maybe<&2, F.Cl>, F.find(k, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post)), Some{F.Cl{k, p, a}}, FR.fr.find(k, pre, p, a, post, first)) : {F.found(_, fd, k, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post), n) == F.DRes{F.Desk{List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post), n}, F.Off{}} : F.DRes}
  pfo.fit(a, fd, k, p, pre, post, n, off)
