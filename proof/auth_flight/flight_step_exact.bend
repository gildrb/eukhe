# eukhe: the proof of LAW flight_step_exact
# Split on the event, then on the caller's leg and on what the step reads
# (the store's freshness, the flight in flight, the fetch, the landed
# outcome): both sides compute to the same state.

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight/model.bend as AuthFlight

def pfs.wait(m: Maybe<&2, F.Out>, +k: Nat, +f: Nat, +c: Nat, +fresh: Bool, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, +cs: List<&2, F.Leg>) -> {F.put(k, F.adv.wait.got(f, m, F.W{F.Sto{c, fresh}, fl, ld, n}), cs) == AuthFlight.am_put(k, AuthFlight.am_wait(m, f, F.W{F.Sto{c, fresh}, fl, ld, n}), cs) : F.St}:
  match m:
    case None{}:
      {==}
    case Some{o}:
      {==}

def pfs.leg(l: F.Leg, +k: Nat, ok: Bool, +c: Nat, +fresh: Bool, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, +cs: List<&2, F.Leg>) -> {F.put(k, F.adv(l, ok, F.W{F.Sto{c, fresh}, fl, ld, n}), cs) == AuthFlight.am_put(k, AuthFlight.am_adv(l, ok, c, fresh, fl, ld, n), cs) : F.St}:
  match l:
    case F.Load{}:
      match fresh:
        case True{}:
          {==}
        case False{}:
          {==}
    case F.Board{}:
      match fl:
        case True{}:
          {==}
        case False{}:
          {==}
    case F.Check{f}:
      match fresh:
        case True{}:
          {==}
        case False{}:
          {==}
    case F.Fetch{f}:
      match ok:
        case True{}:
          {==}
        case False{}:
          {==}
    case F.Store{f, p}:
      match fresh:
        case True{}:
          {==}
        case False{}:
          {==}
    case F.Land{f, o}:
      {==}
    case F.Waiting{+f}:
      pfs.wait(List.get(&2, F.Out, ld, f), k, f, c, fresh, fl, ld, n, cs)
    case F.Served{v, o}:
      {==}

def pfs.at(m: Maybe<&2, F.Leg>, +k: Nat, ok: Bool, +c: Nat, +fresh: Bool, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, +cs: List<&2, F.Leg>) -> {F.step.at(m, k, ok, F.W{F.Sto{c, fresh}, fl, ld, n}, cs) == AuthFlight.am_at(m, k, ok, c, fresh, fl, ld, n, cs) : F.St}:
  match m:
    case None{}:
      {==}
    case Some{l}:
      pfs.leg(l, k, ok, c, fresh, fl, ld, n, cs)

def AuthFlight.flight_step_exact(s, e):
  match s:
    case F.St{w, +cs}:
      match w:
        case F.W{sto, +fl, +ld, +n}:
          match sto:
            case F.Sto{+c, +fresh}:
              match e:
                case F.Arrive{}:
                  {==}
                case F.Step{+k, ok}:
                  pfs.at(List.get(&2, F.Leg, cs, k), k, ok, c, fresh, fl, ld, n, cs)
                case F.Peer{}:
                  {==}
                case F.Expire{}:
                  {==}
