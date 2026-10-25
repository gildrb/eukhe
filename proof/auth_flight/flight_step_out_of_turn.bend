# eukhe: the proof of LAW flight_step_out_of_turn
# The entry steps the desk as the laws' desk (LAE.ae.answers); split on
# the event and on the caller the desk finds: an unknown caller, or a
# found the caller's step does not give, is out of turn; every other
# case contradicts the premise.

import Base
import ../../bend/auth_flight.bend as F
import ../../bend/ffi_auth_flight.bend as FA
import ../../laws/auth_flight/entry.bend as AuthFlightEntry
import ./base/entry.bend as LAE

def afo.fit(t: Bool, fd: F.Fd, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat, off: {Bool.not(t) == True{} : Bool}) -> {AuthFlightEntry.af_step_of(AuthFlightEntry.af_found_fit(t, fd, k, p, cs, n)) == (FA.Open{F.Desk{cs, n}}, SCon{'E', SCon{' ', "auth_flight: out of turn"}}) : FA.St & String}:
  match t:
    case True{}:
      LAE.ae.ft({AuthFlightEntry.af_step_of(AuthFlightEntry.af_found_fit(True{}, fd, k, p, cs, n)) == (FA.Open{F.Desk{cs, n}}, SCon{'E', SCon{' ', "auth_flight: out of turn"}}) : FA.St & String}, off)
    case False{}:
      {==}

def afo.found(m: Maybe<&2, F.Cl>, +fd: F.Fd, +k: Nat, +cs: List<&2, F.Cl>, +n: Nat, off: {AuthFlightEntry.af_off.at(m, fd) == True{} : Bool}) -> {AuthFlightEntry.af_step_of(AuthFlightEntry.af_found_at(m, fd, k, cs, n)) == (FA.Open{F.Desk{cs, n}}, SCon{'E', SCon{' ', "auth_flight: out of turn"}}) : FA.St & String}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case F.Cl{j, p, +a}:
          afo.fit(AuthFlightEntry.af_takes(a, fd), fd, k, p, cs, n, off)

def afo.unwind(m: Maybe<&2, F.Cl>, +k: Nat, +cs: List<&2, F.Cl>, +n: Nat, off: {Maybe.is_none(&2, F.Cl, m) == True{} : Bool}) -> {AuthFlightEntry.af_step_of(AuthFlightEntry.af_unwind_at(m, k, cs, n)) == (FA.Open{F.Desk{cs, n}}, SCon{'E', SCon{' ', "auth_flight: out of turn"}}) : FA.St & String}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      LAE.ae.ft({AuthFlightEntry.af_step_of(AuthFlightEntry.af_unwind_at(Some{x}, k, cs, n)) == (FA.Open{F.Desk{cs, n}}, SCon{'E', SCon{' ', "auth_flight: out of turn"}}) : FA.St & String}, off)

def afo.desk(d: F.Desk, e: F.DEv, off: {AuthFlightEntry.af_off(e, AuthFlightEntry.af_cs(d)) == True{} : Bool}) -> {AuthFlightEntry.af_step_of(AuthFlightEntry.af_desk(d, e)) == (FA.Open{d}, SCon{'E', SCon{' ', "auth_flight: out of turn"}}) : FA.St & String}:
  match d:
    case F.Desk{+cs, +n}:
      match e:
        case F.Comes{p}:
          LAE.ae.ft({AuthFlightEntry.af_step_of(AuthFlightEntry.af_desk(F.Desk{cs, n}, F.Comes{p})) == (FA.Open{F.Desk{cs, n}}, SCon{'E', SCon{' ', "auth_flight: out of turn"}}) : FA.St & String}, off)
        case F.Found{+k, +fd}:
          afo.found(AuthFlightEntry.af_find(k, cs), fd, k, cs, n, off)
        case F.Unwinds{+k}:
          afo.unwind(AuthFlightEntry.af_find(k, cs), k, cs, n, off)
        case F.Joiners{p}:
          LAE.ae.ft({AuthFlightEntry.af_step_of(AuthFlightEntry.af_desk(F.Desk{cs, n}, F.Joiners{p})) == (FA.Open{F.Desk{cs, n}}, SCon{'E', SCon{' ', "auth_flight: out of turn"}}) : FA.St & String}, off)

def AuthFlightEntry.flight_step_out_of_turn(d, e, fits, off):
  %LAE.ae.answers_r(d, e, fits) : {_ == (FA.Open{d}, SCon{'E', SCon{' ', "auth_flight: out of turn"}}) : FA.St & String}
  afo.desk(d, e, off)
