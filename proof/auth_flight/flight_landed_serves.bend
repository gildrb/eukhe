# eukhe: the proof of LAW flight_landed_serves

import Base
import ../../bend/auth_flight.bend as F
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pf.landed_serves(s: F.St, +k: Nat, +f: Nat, +o: F.Out, +ok: Bool, +waits: {List.get(&2, F.Leg, F.St.cs(s), k) == Some{F.Waiting{f}} : Maybe<&2, F.Leg>}, landed: {List.get(&2, F.Out, F.W.landed(F.St.w(s)), f) == Some{o} : Maybe<&2, F.Out>}) -> {List.get(&2, F.Leg, F.St.cs(F.step(s, F.Step{k, ok})), k) == Some{F.Served{Some{f}, o}} : Maybe<&2, F.Leg>}:
  match s:
    case F.St{w, +cs}:
      match w:
        case F.W{sto, +fl, +ld, +n}:
          match sto:
            case F.Sto{+c, +fr}:
              %Equal.sym(Maybe<&2, F.Leg>, List.get(&2, F.Leg, cs, k), Some{F.Waiting{f}}, waits) : {List.get(&2, F.Leg, F.St.cs(F.step.at(_, k, ok, F.W{F.Sto{c, fr}, fl, ld, n}, cs)), k) == Some{F.Served{Some{f}, o}} : Maybe<&2, F.Leg>}
              %Equal.sym(Maybe<&2, F.Out>, List.get(&2, F.Out, ld, f), Some{o}, landed) : {List.get(&2, F.Leg, F.St.cs(F.put(k, F.adv.wait.got(f, _, F.W{F.Sto{c, fr}, fl, ld, n}), cs)), k) == Some{F.Served{Some{f}, o}} : Maybe<&2, F.Leg>}
              LA.pf.get_put(F.Leg, cs, k, F.Waiting{f}, F.Served{Some{f}, o}, waits)

def pf.flight_landed_serves(+s: F.St, +k: Nat, +f: Nat, +o: F.Out, +ok: Bool, waits: {List.get(&2, F.Leg, F.St.cs(s), k) == Some{F.Waiting{f}} : Maybe<&2, F.Leg>}, landed: {List.get(&2, F.Out, F.W.landed(F.St.w(s)), f) == Some{o} : Maybe<&2, F.Out>}) -> {List.get(&2, F.Leg, F.St.cs(F.step(s, F.Step{k, ok})), k) == Some{F.Served{Some{f}, o}} : Maybe<&2, F.Leg>}:
  pf.landed_serves(s, k, f, o, ok, waits, landed)

def Laws.flight_landed_serves(s, k, f, o, ok, waits, landed):
  pf.flight_landed_serves(s, k, f, o, ok, waits, landed)
