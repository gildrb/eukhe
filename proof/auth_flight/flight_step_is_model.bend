# eukhe: the proof of LAW flight_step_is_model
# The entry steps the desk as the laws' desk (LAE.ae.answers); the
# caller is the one found; then split on its place and the found: where
# its step gives the found, both the desk's act for it and the model's
# next leg compute (the model world split where its step reads it, the
# provider's flight in flight or not where the load boards), and the rest
# of the reply is the flight's joiners when it lands, else nothing; every
# other pair contradicts the premise.

import Base
import ../../bend/auth_flight.bend as F
import ../../bend/ffi_auth_flight.bend as FA
import ../../laws/auth_flight/entry.bend as AuthFlightEntry
import ./base/entry.bend as LAE

# the claim, after the found's caller is found
def afm.G(fit: Bool, +fd: F.Fd, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat, +c: Nat, +f: Nat, +w: F.W) -> Type:
  &rest: List<&2, F.To> -> {AuthFlightEntry.af_reply(AuthFlightEntry.af_step_of(AuthFlightEntry.af_found_fit(fit, fd, k, p, cs, n))) == AuthFlightEntry.af_spell_out(F.Acts{F.To{k, AuthFlightEntry.af_model_fd(fd, AuthFlightEntry.af_inflight(p, cs), c, f, w)} <> rest}) : String}

def afm.board(fl: Bool, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat, +c: Nat, +w: F.W) -> &rest: List<&2, F.To> -> {AuthFlightEntry.af_reply(AuthFlightEntry.af_step_of(AuthFlightEntry.af_board(fl, k, cs, n))) == AuthFlightEntry.af_spell_out(F.Acts{F.To{k, AuthFlightEntry.af_model_fd(F.LoadExpired{}, fl, c, 0n, w)} <> rest}) : String}:
  match fl:
    case True{}:
      (Nil{}, {==})
    case False{}:
      (Nil{}, {==})

def afm.fit(a: F.At, fd: F.Fd, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat, +c: Nat, +f: Nat, +w: F.W, takes: {AuthFlightEntry.af_takes(a, fd) == True{} : Bool}) -> afm.G(AuthFlightEntry.af_takes(a, fd), fd, k, p, cs, n, c, f, w):
  match a:
    case F.Loads{}:
      match fd:
        case F.LoadFresh{}:
          (Nil{}, {==})
        case F.LoadExpired{}:
          afm.board(AuthFlightEntry.af_inflight(p, cs), k, p, cs, n, c, w)
        case F.LoadFailed{}:
          (Nil{}, {==})
        case F.CheckFresh{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Loads{}, F.CheckFresh{}), F.CheckFresh{}, k, p, cs, n, c, f, w), takes)
        case F.CheckExpired{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Loads{}, F.CheckExpired{}), F.CheckExpired{}, k, p, cs, n, c, f, w), takes)
        case F.FetchOk{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Loads{}, F.FetchOk{}), F.FetchOk{}, k, p, cs, n, c, f, w), takes)
        case F.FetchFailed{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Loads{}, F.FetchFailed{}), F.FetchFailed{}, k, p, cs, n, c, f, w), takes)
        case F.Stored{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Loads{}, F.Stored{}), F.Stored{}, k, p, cs, n, c, f, w), takes)
    case F.Checks{}:
      match fd:
        case F.LoadFresh{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Checks{}, F.LoadFresh{}), F.LoadFresh{}, k, p, cs, n, c, f, w), takes)
        case F.LoadExpired{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Checks{}, F.LoadExpired{}), F.LoadExpired{}, k, p, cs, n, c, f, w), takes)
        case F.LoadFailed{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Checks{}, F.LoadFailed{}), F.LoadFailed{}, k, p, cs, n, c, f, w), takes)
        case F.CheckFresh{}:
          (AuthFlightEntry.af_wake(p, F.DoDone{}, AuthFlightEntry.af_cut(k, cs)), {==})
        case F.CheckExpired{}:
          (Nil{}, {==})
        case F.FetchOk{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Checks{}, F.FetchOk{}), F.FetchOk{}, k, p, cs, n, c, f, w), takes)
        case F.FetchFailed{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Checks{}, F.FetchFailed{}), F.FetchFailed{}, k, p, cs, n, c, f, w), takes)
        case F.Stored{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Checks{}, F.Stored{}), F.Stored{}, k, p, cs, n, c, f, w), takes)
    case F.Fetches{}:
      match fd:
        case F.LoadFresh{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Fetches{}, F.LoadFresh{}), F.LoadFresh{}, k, p, cs, n, c, f, w), takes)
        case F.LoadExpired{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Fetches{}, F.LoadExpired{}), F.LoadExpired{}, k, p, cs, n, c, f, w), takes)
        case F.LoadFailed{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Fetches{}, F.LoadFailed{}), F.LoadFailed{}, k, p, cs, n, c, f, w), takes)
        case F.CheckFresh{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Fetches{}, F.CheckFresh{}), F.CheckFresh{}, k, p, cs, n, c, f, w), takes)
        case F.CheckExpired{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Fetches{}, F.CheckExpired{}), F.CheckExpired{}, k, p, cs, n, c, f, w), takes)
        case F.FetchOk{}:
          match w:
            case F.W{s, fl, ld, m}:
              (Nil{}, {==})
        case F.FetchFailed{}:
          match w:
            case F.W{s, fl, ld, m}:
              (AuthFlightEntry.af_wake(p, F.DoDone{}, AuthFlightEntry.af_cut(k, cs)), {==})
        case F.Stored{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Fetches{}, F.Stored{}), F.Stored{}, k, p, cs, n, c, f, w), takes)
    case F.Stores{}:
      match fd:
        case F.LoadFresh{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Stores{}, F.LoadFresh{}), F.LoadFresh{}, k, p, cs, n, c, f, w), takes)
        case F.LoadExpired{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Stores{}, F.LoadExpired{}), F.LoadExpired{}, k, p, cs, n, c, f, w), takes)
        case F.LoadFailed{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Stores{}, F.LoadFailed{}), F.LoadFailed{}, k, p, cs, n, c, f, w), takes)
        case F.CheckFresh{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Stores{}, F.CheckFresh{}), F.CheckFresh{}, k, p, cs, n, c, f, w), takes)
        case F.CheckExpired{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Stores{}, F.CheckExpired{}), F.CheckExpired{}, k, p, cs, n, c, f, w), takes)
        case F.FetchOk{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Stores{}, F.FetchOk{}), F.FetchOk{}, k, p, cs, n, c, f, w), takes)
        case F.FetchFailed{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Stores{}, F.FetchFailed{}), F.FetchFailed{}, k, p, cs, n, c, f, w), takes)
        case F.Stored{}:
          match w:
            case F.W{s, fl, ld, m}:
              match s:
                case F.Sto{q, fresh}:
                  match fresh:
                    case True{}:
                      (AuthFlightEntry.af_wake(p, F.DoDone{}, AuthFlightEntry.af_cut(k, cs)), {==})
                    case False{}:
                      (AuthFlightEntry.af_wake(p, F.DoDone{}, AuthFlightEntry.af_cut(k, cs)), {==})
    case F.Waits{}:
      match fd:
        case F.LoadFresh{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Waits{}, F.LoadFresh{}), F.LoadFresh{}, k, p, cs, n, c, f, w), takes)
        case F.LoadExpired{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Waits{}, F.LoadExpired{}), F.LoadExpired{}, k, p, cs, n, c, f, w), takes)
        case F.LoadFailed{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Waits{}, F.LoadFailed{}), F.LoadFailed{}, k, p, cs, n, c, f, w), takes)
        case F.CheckFresh{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Waits{}, F.CheckFresh{}), F.CheckFresh{}, k, p, cs, n, c, f, w), takes)
        case F.CheckExpired{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Waits{}, F.CheckExpired{}), F.CheckExpired{}, k, p, cs, n, c, f, w), takes)
        case F.FetchOk{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Waits{}, F.FetchOk{}), F.FetchOk{}, k, p, cs, n, c, f, w), takes)
        case F.FetchFailed{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Waits{}, F.FetchFailed{}), F.FetchFailed{}, k, p, cs, n, c, f, w), takes)
        case F.Stored{}:
          LAE.ae.ft(afm.G(AuthFlightEntry.af_takes(F.Waits{}, F.Stored{}), F.Stored{}, k, p, cs, n, c, f, w), takes)

def AuthFlightEntry.flight_step_is_model(cs, n, k, fits, j, p, a, at, fd, c, f, w, takes):
  %LAE.ae.answers_r(F.Desk{cs, n}, F.Found{k, fd}, fits) : &rest: List<&2, F.To> -> {AuthFlightEntry.af_reply(_) == AuthFlightEntry.af_spell_out(F.Acts{F.To{k, AuthFlightEntry.af_model_fd(fd, AuthFlightEntry.af_inflight(p, cs), c, f, w)} <> rest}) : String}
  %LAE.ae.at_r(k, cs, F.Cl{j, p, a}, at) : &rest: List<&2, F.To> -> {AuthFlightEntry.af_reply(AuthFlightEntry.af_step_of(AuthFlightEntry.af_found_at(_, fd, k, cs, n))) == AuthFlightEntry.af_spell_out(F.Acts{F.To{k, AuthFlightEntry.af_model_fd(fd, AuthFlightEntry.af_inflight(p, cs), c, f, w)} <> rest}) : String}
  afm.fit(a, fd, k, p, cs, n, c, f, w, takes)
