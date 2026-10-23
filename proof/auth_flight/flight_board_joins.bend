# eukhe: the proof of LAW flight_board_joins

import Base
import ../../bend/auth_flight.bend as F
import ../../LAWS.bend as Laws
import ./base.bend as LA

# the flight a caller leads is the flight in flight
def pf.led_lead(+s: F.Sto, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, l: F.Leg, +f: Nat, e: {F.led(l) == Some{f} : Maybe<&2, Nat>}, g: LA.pf.Good(F.W{s, fl, ld, n}, l)) -> LA.pf.Lead(fl, ld, f):
  match l:
    case F.Load{}:
      LA.pf.none_some(Nat, LA.pf.Lead(fl, ld, f), f, e)
    case F.Board{}:
      LA.pf.none_some(Nat, LA.pf.Lead(fl, ld, f), f, e)
    case F.Check{+f2}:
      %LA.pf.some_inj(Nat, 0n, f2, f, e) : LA.pf.Lead(fl, ld, _)
      g
    case F.Fetch{+f2}:
      %LA.pf.some_inj(Nat, 0n, f2, f, e) : LA.pf.Lead(fl, ld, _)
      g
    case F.Store{+f2, c}:
      %LA.pf.some_inj(Nat, 0n, f2, f, e) : LA.pf.Lead(fl, ld, _)
      g
    case F.Land{+f2, o}:
      (lead, kept) = g
      %LA.pf.some_inj(Nat, 0n, f2, f, e) : LA.pf.Lead(fl, ld, _)
      lead
    case F.Waiting{f2}:
      LA.pf.none_some(Nat, LA.pf.Lead(fl, ld, f), f, e)
    case F.Served{v, o}:
      LA.pf.none_some(Nat, LA.pf.Lead(fl, ld, f), f, e)

def pf.joins.go(+c: Nat, +fr: Bool, fl: Bool, +ld: List<&2, F.Out>, +n: Nat, +cs: List<&2, F.Leg>, +f: Nat, +k: Nat, +ok: Bool, lead: LA.pf.Lead(fl, ld, f), +boards: {List.get(&2, F.Leg, cs, k) == Some{F.Board{}} : Maybe<&2, F.Leg>}) -> {List.get(&2, F.Leg, F.St.cs(F.step(F.St{F.W{F.Sto{c, fr}, fl, ld, n}, cs}, F.Step{k, ok})), k) == Some{F.Waiting{f}} : Maybe<&2, F.Leg>}:
  match fl:
    case True{}:
      (efl, ef) = lead
      %Equal.sym(Maybe<&2, F.Leg>, List.get(&2, F.Leg, cs, k), Some{F.Board{}}, boards) : {List.get(&2, F.Leg, F.St.cs(F.step.at(_, k, ok, F.W{F.Sto{c, fr}, True{}, ld, n}, cs)), k) == Some{F.Waiting{f}} : Maybe<&2, F.Leg>}
      %Equal.sym(Nat, f, List.length(&2, F.Out, ld), ef) : {List.get(&2, F.Leg, List.append(&2, F.Leg, List.take(&2, F.Leg, cs, k), F.Waiting{List.length(&2, F.Out, ld)} <> List.drop(&2, F.Leg, cs, 1n+k)), k) == Some{F.Waiting{_}} : Maybe<&2, F.Leg>}
      LA.pf.get_put(F.Leg, cs, k, F.Board{}, F.Waiting{List.length(&2, F.Out, ld)}, boards)
    case False{}:
      (efl, ef) = lead
      LA.auth_flight.pf.absurdF({List.get(&2, F.Leg, F.St.cs(F.step(F.St{F.W{F.Sto{c, fr}, False{}, ld, n}, cs}, F.Step{k, ok})), k) == Some{F.Waiting{f}} : Maybe<&2, F.Leg>}, efl)

def pf.joins(s: F.St, inv: LA.auth_flight.pf.Inv(s), +j: Nat, +lj: F.Leg, +f: Nat, leads: {List.get(&2, F.Leg, F.St.cs(s), j) == Some{lj} : Maybe<&2, F.Leg>}, flight: {F.led(lj) == Some{f} : Maybe<&2, Nat>}, +k: Nat, +ok: Bool, boards: {List.get(&2, F.Leg, F.St.cs(s), k) == Some{F.Board{}} : Maybe<&2, F.Leg>}) -> {List.get(&2, F.Leg, F.St.cs(F.step(s, F.Step{k, ok})), k) == Some{F.Waiting{f}} : Maybe<&2, F.Leg>}:
  match s:
    case F.St{w, +cs}:
      match w:
        case F.W{sto, +fl, +ld, +n}:
          match sto:
            case F.Sto{+c, +fr}:
              (cnt, all) = inv
              pf.joins.go(c, fr, fl, ld, n, cs, f, k, ok, pf.led_lead(F.Sto{c, fr}, fl, ld, n, lj, f, flight, LA.pf.all_get(F.W{F.Sto{c, fr}, fl, ld, n}, cs, j, lj, leads, all)), boards)

def pf.flight_board_joins(+evs: List<&2, F.Ev>, +j: Nat, +lj: F.Leg, +f: Nat, leads: {List.get(&2, F.Leg, F.St.cs(F.run(evs)), j) == Some{lj} : Maybe<&2, F.Leg>}, flight: {F.led(lj) == Some{f} : Maybe<&2, Nat>}, +k: Nat, +ok: Bool, boards: {List.get(&2, F.Leg, F.St.cs(F.run(evs)), k) == Some{F.Board{}} : Maybe<&2, F.Leg>}) -> {List.get(&2, F.Leg, F.St.cs(F.step(F.run(evs), F.Step{k, ok})), k) == Some{F.Waiting{f}} : Maybe<&2, F.Leg>}:
  pf.joins(F.run(evs), LA.pf.inv_run(evs), j, lj, f, leads, flight, k, ok, boards)

def Laws.flight_board_joins(evs, j, lj, f, leads, flight, k, ok, boards):
  pf.flight_board_joins(evs, j, lj, f, leads, flight, k, ok, boards)
