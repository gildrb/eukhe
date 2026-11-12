# eukhe: the proof of LAW flight_after_end_served
# The land stores c or a newer credential (LA.pf.stored, from the run's
# invariant); with the store fresh, an arriving caller's load serves the
# stored credential (pf.after_of.load), and the store holds c2.

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight/model.bend as AuthFlight
import ./base.bend as LA

def pf.after_of.load(+c2: Nat, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, +cs: List<&2, F.Leg>, +ok: Bool) -> {List.get(&2, F.Leg, F.St.cs(F.step.at(List.get(&2, F.Leg, List.append(&2, F.Leg, cs, [F.Load{}]), List.length(&2, F.Leg, cs)), List.length(&2, F.Leg, cs), ok, F.W{F.Sto{c2, True{}}, fl, ld, n}, List.append(&2, F.Leg, cs, [F.Load{}]))), List.length(&2, F.Leg, cs)) == Some{F.Served{None{}, F.Ok{c2}}} : Maybe<&2, F.Leg>}:
  %Equal.sym(Maybe<&2, F.Leg>, List.get(&2, F.Leg, List.append(&2, F.Leg, cs, [F.Load{}]), List.length(&2, F.Leg, cs)), Some{F.Load{}}, LA.pf.get_snoc(F.Leg, cs, F.Load{})) : {List.get(&2, F.Leg, F.St.cs(F.step.at(_, List.length(&2, F.Leg, cs), ok, F.W{F.Sto{c2, True{}}, fl, ld, n}, List.append(&2, F.Leg, cs, [F.Load{}]))), List.length(&2, F.Leg, cs)) == Some{F.Served{None{}, F.Ok{c2}}} : Maybe<&2, F.Leg>}
  LA.pf.get_put(F.Leg, List.append(&2, F.Leg, cs, [F.Load{}]), List.length(&2, F.Leg, cs), F.Load{}, F.Served{None{}, F.Ok{c2}}, LA.pf.get_snoc(F.Leg, cs, F.Load{}))

# a caller that arrives while the store holds a fresh c2 is served c2
def pf.late(s: F.St, +ok: Bool, +c2: Nat, fresh: {F.W.sto(F.St.w(s)) == F.Sto{c2, True{}} : F.Sto}) -> {AuthFlight.af_late(s, ok) == Some{F.Served{None{}, F.Ok{c2}}} : Maybe<&2, F.Leg>}:
  match s:
    case F.St{w, +cs}:
      match w:
        case F.W{sto, +fl, +ld, +n}:
          match sto:
            case F.Sto{+c3, fr}:
              match fr:
                case True{}:
                  %Equal.cong(F.Sto, Nat, x => F.Sto.c(x), F.Sto{c3, True{}}, F.Sto{c2, True{}}, fresh) : {AuthFlight.af_late(F.St{F.W{F.Sto{c3, True{}}, fl, ld, n}, cs}, ok) == Some{F.Served{None{}, F.Ok{_}}} : Maybe<&2, F.Leg>}
                  pf.after_of.load(c3, fl, ld, n, cs, ok)
                case False{}:
                  LA.auth_flight.pf.absurdF({AuthFlight.af_late(F.St{F.W{F.Sto{c3, False{}}, fl, ld, n}, cs}, ok) == Some{F.Served{None{}, F.Ok{c2}}} : Maybe<&2, F.Leg>}, Equal.cong(F.Sto, Bool, x => F.Sto.fresh(x), F.Sto{c3, False{}}, F.Sto{c2, True{}}, fresh))

def pf.kept.le(+c: Nat, s: F.St, +c2: Nat, fresh: {F.W.sto(F.St.w(s)) == F.Sto{c2, True{}} : F.Sto}, stored: {LA.pf.le(c, F.Sto.c(F.W.sto(F.St.w(s)))) == True{} : Bool}) -> {LA.pf.le(c, c2) == True{} : Bool}:
  %fresh : {LA.pf.le(c, F.Sto.c(_)) == True{} : Bool}
  stored

# the stored credential, c or newer, is c2
def pf.kept(+c: Nat, s: F.St, +c2: Nat, fresh: {F.W.sto(F.St.w(s)) == F.Sto{c2, True{}} : F.Sto}, stored: {LA.pf.le(c, F.Sto.c(F.W.sto(F.St.w(s)))) == True{} : Bool}) -> {Nat.is_le(c, c2) == True{} : Bool}:
  LA.pf.is_le(c, c2, pf.kept.le(c, s, c2, fresh, stored))

def AuthFlight.flight_after_end_served(evs, k, f, c, lands, ok, ok2, c2, fresh):
  +fr = fresh
  (pf.late(F.step(AuthFlight.am_run(evs), F.Step{k, ok}), ok2, c2, fr), pf.kept(c, F.step(AuthFlight.am_run(evs), F.Step{k, ok}), c2, fr, LA.pf.stored(AuthFlight.am_run(evs), LA.pf.inv_run(evs), k, f, c, lands, ok)))
