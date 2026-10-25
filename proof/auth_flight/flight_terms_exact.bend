# eukhe: the proof of LAW flight_terms_exact
# fetching: induction on the callers, a case per leg; led: a case per leg.

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight/model.bend as AuthFlight

def pft.fetching(cs: List<&2, F.Leg>) -> {F.fetching(cs) == AuthFlight.af_fetching(cs) : Nat}:
  match cs:
    case Nil{}:
      {==}
    case l <> t:
      match l:
        case F.Load{}:
          pft.fetching(t)
        case F.Board{}:
          pft.fetching(t)
        case F.Check{f}:
          pft.fetching(t)
        case F.Fetch{f}:
          %pft.fetching(t) : {Nat.add(1n, F.fetching(t)) == Nat.add(1n, _) : Nat}
          {==}
        case F.Store{f, c}:
          pft.fetching(t)
        case F.Land{f, o}:
          pft.fetching(t)
        case F.Waiting{f}:
          pft.fetching(t)
        case F.Served{v, o}:
          pft.fetching(t)

def pft.led(l: F.Leg) -> {F.led(l) == AuthFlight.af_led(l) : Maybe<&2, Nat>}:
  match l:
    case F.Load{}:
      {==}
    case F.Board{}:
      {==}
    case F.Check{f}:
      {==}
    case F.Fetch{f}:
      {==}
    case F.Store{f, c}:
      {==}
    case F.Land{f, o}:
      {==}
    case F.Waiting{f}:
      {==}
    case F.Served{v, o}:
      {==}

def AuthFlight.flight_terms_exact(cs, l):
  (pft.fetching(cs), pft.led(l))
