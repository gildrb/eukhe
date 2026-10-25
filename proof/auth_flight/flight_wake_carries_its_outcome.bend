# eukhe: the proof of LAW flight_wake_carries_its_outcome
# The entry steps the desk as the laws' desk (LAE.ae.answers); the
# caller is the one found; then split on its place and the found: where
# the found lands the flight both sides compute; every other pair
# contradicts the premise.

import Base
import ../../bend/auth_flight.bend as F
import ../../bend/ffi_auth_flight.bend as FA
import ../../laws/auth_flight/entry.bend as AuthFlightEntry
import ./base/entry.bend as LAE

# the landed flight's step and reply
def afw.R(+k: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat) -> FA.St & String:
  (FA.Open{F.Desk{AuthFlightEntry.af_unwait(p, AuthFlightEntry.af_cut(k, cs)), n}}, AuthFlightEntry.af_spell_out(F.Acts{F.To{k, F.DoDone{}} <> AuthFlightEntry.af_wake(p, F.DoDone{}, AuthFlightEntry.af_cut(k, cs))}))

# the claim, after the found's caller is found
def afw.G(fit: Bool, +fd: F.Fd, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat) -> Type:
  {AuthFlightEntry.af_step_of(AuthFlightEntry.af_found_fit(fit, fd, k, p, cs, n)) == afw.R(k, p, cs, n) : FA.St & String}

def afw.fit(a: F.At, fd: F.Fd, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat, lands: {AuthFlightEntry.af_lands(a, fd) == True{} : Bool}) -> afw.G(AuthFlightEntry.af_takes(a, fd), fd, k, p, cs, n):
  match a:
    case F.Loads{}:
      match fd:
        case F.LoadFresh{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Loads{}, F.LoadFresh{}), F.LoadFresh{}, k, p, cs, n), lands)
        case F.LoadExpired{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Loads{}, F.LoadExpired{}), F.LoadExpired{}, k, p, cs, n), lands)
        case F.LoadFailed{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Loads{}, F.LoadFailed{}), F.LoadFailed{}, k, p, cs, n), lands)
        case F.CheckFresh{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Loads{}, F.CheckFresh{}), F.CheckFresh{}, k, p, cs, n), lands)
        case F.CheckExpired{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Loads{}, F.CheckExpired{}), F.CheckExpired{}, k, p, cs, n), lands)
        case F.FetchOk{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Loads{}, F.FetchOk{}), F.FetchOk{}, k, p, cs, n), lands)
        case F.FetchFailed{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Loads{}, F.FetchFailed{}), F.FetchFailed{}, k, p, cs, n), lands)
        case F.Stored{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Loads{}, F.Stored{}), F.Stored{}, k, p, cs, n), lands)
    case F.Checks{}:
      match fd:
        case F.LoadFresh{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Checks{}, F.LoadFresh{}), F.LoadFresh{}, k, p, cs, n), lands)
        case F.LoadExpired{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Checks{}, F.LoadExpired{}), F.LoadExpired{}, k, p, cs, n), lands)
        case F.LoadFailed{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Checks{}, F.LoadFailed{}), F.LoadFailed{}, k, p, cs, n), lands)
        case F.CheckFresh{}:
          {==}
        case F.CheckExpired{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Checks{}, F.CheckExpired{}), F.CheckExpired{}, k, p, cs, n), lands)
        case F.FetchOk{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Checks{}, F.FetchOk{}), F.FetchOk{}, k, p, cs, n), lands)
        case F.FetchFailed{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Checks{}, F.FetchFailed{}), F.FetchFailed{}, k, p, cs, n), lands)
        case F.Stored{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Checks{}, F.Stored{}), F.Stored{}, k, p, cs, n), lands)
    case F.Fetches{}:
      match fd:
        case F.LoadFresh{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Fetches{}, F.LoadFresh{}), F.LoadFresh{}, k, p, cs, n), lands)
        case F.LoadExpired{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Fetches{}, F.LoadExpired{}), F.LoadExpired{}, k, p, cs, n), lands)
        case F.LoadFailed{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Fetches{}, F.LoadFailed{}), F.LoadFailed{}, k, p, cs, n), lands)
        case F.CheckFresh{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Fetches{}, F.CheckFresh{}), F.CheckFresh{}, k, p, cs, n), lands)
        case F.CheckExpired{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Fetches{}, F.CheckExpired{}), F.CheckExpired{}, k, p, cs, n), lands)
        case F.FetchOk{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Fetches{}, F.FetchOk{}), F.FetchOk{}, k, p, cs, n), lands)
        case F.FetchFailed{}:
          {==}
        case F.Stored{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Fetches{}, F.Stored{}), F.Stored{}, k, p, cs, n), lands)
    case F.Stores{}:
      match fd:
        case F.LoadFresh{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Stores{}, F.LoadFresh{}), F.LoadFresh{}, k, p, cs, n), lands)
        case F.LoadExpired{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Stores{}, F.LoadExpired{}), F.LoadExpired{}, k, p, cs, n), lands)
        case F.LoadFailed{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Stores{}, F.LoadFailed{}), F.LoadFailed{}, k, p, cs, n), lands)
        case F.CheckFresh{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Stores{}, F.CheckFresh{}), F.CheckFresh{}, k, p, cs, n), lands)
        case F.CheckExpired{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Stores{}, F.CheckExpired{}), F.CheckExpired{}, k, p, cs, n), lands)
        case F.FetchOk{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Stores{}, F.FetchOk{}), F.FetchOk{}, k, p, cs, n), lands)
        case F.FetchFailed{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Stores{}, F.FetchFailed{}), F.FetchFailed{}, k, p, cs, n), lands)
        case F.Stored{}:
          {==}
    case F.Waits{}:
      match fd:
        case F.LoadFresh{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Waits{}, F.LoadFresh{}), F.LoadFresh{}, k, p, cs, n), lands)
        case F.LoadExpired{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Waits{}, F.LoadExpired{}), F.LoadExpired{}, k, p, cs, n), lands)
        case F.LoadFailed{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Waits{}, F.LoadFailed{}), F.LoadFailed{}, k, p, cs, n), lands)
        case F.CheckFresh{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Waits{}, F.CheckFresh{}), F.CheckFresh{}, k, p, cs, n), lands)
        case F.CheckExpired{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Waits{}, F.CheckExpired{}), F.CheckExpired{}, k, p, cs, n), lands)
        case F.FetchOk{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Waits{}, F.FetchOk{}), F.FetchOk{}, k, p, cs, n), lands)
        case F.FetchFailed{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Waits{}, F.FetchFailed{}), F.FetchFailed{}, k, p, cs, n), lands)
        case F.Stored{}:
          LAE.ae.ft(afw.G(AuthFlightEntry.af_takes(F.Waits{}, F.Stored{}), F.Stored{}, k, p, cs, n), lands)

def AuthFlightEntry.flight_wake_carries_its_outcome(cs, n, k, fits, j, p, a, at, fd, lands):
  %LAE.ae.answers_r(F.Desk{cs, n}, F.Found{k, fd}, fits) : {_ == afw.R(k, p, cs, n) : FA.St & String}
  %LAE.ae.at_r(k, cs, F.Cl{j, p, a}, at) : {AuthFlightEntry.af_step_of(AuthFlightEntry.af_found_at(_, fd, k, cs, n)) == afw.R(k, p, cs, n) : FA.St & String}
  afw.fit(a, fd, k, p, cs, n, lands)
