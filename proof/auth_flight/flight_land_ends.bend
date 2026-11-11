# eukhe: the proof of LAW flight_land_ends
# Caller k's leg is Land{f, o} (the premise, rewritten into the step), so
# adv.land serves o, clears the flight and appends o to the landed
# outcomes; LA.pf.get_put reads caller k's new leg back.

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight/model.bend as AuthFlight
import ./base.bend as LA

def pfl.leg(s: F.St, +k: Nat, +f: Nat, +o: F.Out, +ok: Bool, +lands: {List.get(&2, F.Leg, F.St.cs(s), k) == Some{F.Land{f, o}} : Maybe<&2, F.Leg>}) -> {List.get(&2, F.Leg, F.St.cs(F.step(s, F.Step{k, ok})), k) == Some{F.Served{Some{f}, o}} : Maybe<&2, F.Leg>}:
  match s:
    case F.St{w, +cs}:
      match w:
        case F.W{sto, +fl, +ld, +n}:
          match sto:
            case F.Sto{+c, +fr}:
              %Equal.sym(Maybe<&2, F.Leg>, List.get(&2, F.Leg, cs, k), Some{F.Land{f, o}}, lands) : {List.get(&2, F.Leg, F.St.cs(F.step.at(_, k, ok, F.W{F.Sto{c, fr}, fl, ld, n}, cs)), k) == Some{F.Served{Some{f}, o}} : Maybe<&2, F.Leg>}
              LA.pf.get_put(F.Leg, cs, k, F.Land{f, o}, F.Served{Some{f}, o}, lands)

def pfl.fl(s: F.St, +k: Nat, +f: Nat, +o: F.Out, +ok: Bool, lands: {List.get(&2, F.Leg, F.St.cs(s), k) == Some{F.Land{f, o}} : Maybe<&2, F.Leg>}) -> {F.W.fl(F.St.w(F.step(s, F.Step{k, ok}))) == False{} : Bool}:
  match s:
    case F.St{w, +cs}:
      match w:
        case F.W{sto, +fl, +ld, +n}:
          match sto:
            case F.Sto{+c, +fr}:
              %Equal.sym(Maybe<&2, F.Leg>, List.get(&2, F.Leg, cs, k), Some{F.Land{f, o}}, lands) : {F.W.fl(F.St.w(F.step.at(_, k, ok, F.W{F.Sto{c, fr}, fl, ld, n}, cs))) == False{} : Bool}
              {==}

def pfl.ld(s: F.St, +k: Nat, +f: Nat, +o: F.Out, +ok: Bool, lands: {List.get(&2, F.Leg, F.St.cs(s), k) == Some{F.Land{f, o}} : Maybe<&2, F.Leg>}) -> {F.W.landed(F.St.w(F.step(s, F.Step{k, ok}))) == List.append(&2, F.Out, F.W.landed(F.St.w(s)), [o]) : List<&2, F.Out>}:
  match s:
    case F.St{w, +cs}:
      match w:
        case F.W{sto, +fl, +ld, +n}:
          match sto:
            case F.Sto{+c, +fr}:
              %Equal.sym(Maybe<&2, F.Leg>, List.get(&2, F.Leg, cs, k), Some{F.Land{f, o}}, lands) : {F.W.landed(F.St.w(F.step.at(_, k, ok, F.W{F.Sto{c, fr}, fl, ld, n}, cs))) == List.append(&2, F.Out, ld, [o]) : List<&2, F.Out>}
              {==}

def AuthFlight.flight_land_ends(s, k, f, o, ok, lands):
  +ls = lands
  (pfl.leg(s, k, f, o, ok, ls), pfl.fl(s, k, f, o, ok, ls), pfl.ld(s, k, f, o, ok, ls))
