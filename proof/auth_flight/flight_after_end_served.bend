# eukhe: the proof of LAW flight_after_end_served

import Base
import ../../bend/auth_flight.bend as F
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pf.after_of.load(+c2: Nat, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, +cs: List<&2, F.Leg>, +ok: Bool) -> {List.get(&2, F.Leg, F.St.cs(F.step.at(List.get(&2, F.Leg, List.append(&2, F.Leg, cs, [F.Load{}]), List.length(&2, F.Leg, cs)), List.length(&2, F.Leg, cs), ok, F.W{F.Sto{c2, True{}}, fl, ld, n}, List.append(&2, F.Leg, cs, [F.Load{}]))), List.length(&2, F.Leg, cs)) == Some{F.Served{None{}, F.Ok{c2}}} : Maybe<&2, F.Leg>}:
  %Equal.sym(Maybe<&2, F.Leg>, List.get(&2, F.Leg, List.append(&2, F.Leg, cs, [F.Load{}]), List.length(&2, F.Leg, cs)), Some{F.Load{}}, LA.pf.get_snoc(F.Leg, cs, F.Load{})) : {List.get(&2, F.Leg, F.St.cs(F.step.at(_, List.length(&2, F.Leg, cs), ok, F.W{F.Sto{c2, True{}}, fl, ld, n}, List.append(&2, F.Leg, cs, [F.Load{}]))), List.length(&2, F.Leg, cs)) == Some{F.Served{None{}, F.Ok{c2}}} : Maybe<&2, F.Leg>}
  LA.pf.get_put(F.Leg, List.append(&2, F.Leg, cs, [F.Load{}]), List.length(&2, F.Leg, cs), F.Load{}, F.Served{None{}, F.Ok{c2}}, LA.pf.get_snoc(F.Leg, cs, F.Load{}))

# a caller that arrives while the store is fresh is served it
def pf.after_of(+c: Nat, s: F.St, +ok: Bool, fresh: {F.Sto.fresh(F.W.sto(F.St.w(s))) == True{} : Bool}, kept: {F.le(c, F.Sto.c(F.W.sto(F.St.w(s)))) == True{} : Bool}) -> F.After(c, s, ok):
  match s:
    case F.St{w, +cs}:
      match w:
        case F.W{sto, +fl, +ld, +n}:
          match sto:
            case F.Sto{+c2, fr}:
              match fr:
                case True{}:
                  (pf.after_of.load(c2, fl, ld, n, cs, ok), kept)
                case False{}:
                  LA.auth_flight.pf.absurdF(F.After(c, F.St{F.W{F.Sto{c2, False{}}, fl, ld, n}, cs}, ok), fresh)

def pf.flight_after_end_served(+evs: List<&2, F.Ev>, +k: Nat, +f: Nat, +c: Nat, lands: {List.get(&2, F.Leg, F.St.cs(F.run(evs)), k) == Some{F.Land{f, F.Ok{c}}} : Maybe<&2, F.Leg>}, +ok: Bool, +ok2: Bool, fresh: {F.Sto.fresh(F.W.sto(F.St.w(F.step(F.run(evs), F.Step{k, ok})))) == True{} : Bool}) -> F.After(c, F.step(F.run(evs), F.Step{k, ok}), ok2):
  pf.after_of(c, F.step(F.run(evs), F.Step{k, ok}), ok2, fresh, LA.pf.stored(F.run(evs), LA.pf.inv_run(evs), k, f, c, lands, ok))

def Laws.flight_after_end_served(evs, k, f, c, lands, ok, ok2, fresh):
  pf.flight_after_end_served(evs, k, f, c, lands, ok, ok2, fresh)
