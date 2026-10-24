# eukhe: the proof of LAW flight_board_leads
# Caller k's leg is Board{} and no flight is in flight (the premises,
# rewritten into the step), so adv.board starts flight |landed| and the
# world is in flight; LA.pf.get_put reads caller k's new leg back.

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight.bend as AuthFlight
import ./base.bend as LA

def pfb.leg(s: F.St, +k: Nat, +ok: Bool, +boards: {List.get(&2, F.Leg, F.St.cs(s), k) == Some{F.Board{}} : Maybe<&2, F.Leg>}, free: {F.W.fl(F.St.w(s)) == False{} : Bool}) -> {List.get(&2, F.Leg, F.St.cs(F.step(s, F.Step{k, ok})), k) == Some{F.Check{List.length(&2, F.Out, F.W.landed(F.St.w(s)))}} : Maybe<&2, F.Leg>}:
  match s:
    case F.St{w, +cs}:
      match w:
        case F.W{sto, +fl, +ld, +n}:
          match sto:
            case F.Sto{+c, +fr}:
              %Equal.sym(Maybe<&2, F.Leg>, List.get(&2, F.Leg, cs, k), Some{F.Board{}}, boards) : {List.get(&2, F.Leg, F.St.cs(F.step.at(_, k, ok, F.W{F.Sto{c, fr}, fl, ld, n}, cs)), k) == Some{F.Check{List.length(&2, F.Out, ld)}} : Maybe<&2, F.Leg>}
              %Equal.sym(Bool, fl, False{}, free) : {List.get(&2, F.Leg, F.St.cs(F.put(k, F.adv.board(F.W{F.Sto{c, fr}, _, ld, n}), cs)), k) == Some{F.Check{List.length(&2, F.Out, ld)}} : Maybe<&2, F.Leg>}
              LA.pf.get_put(F.Leg, cs, k, F.Board{}, F.Check{List.length(&2, F.Out, ld)}, boards)

def pfb.fl(s: F.St, +k: Nat, +ok: Bool, +boards: {List.get(&2, F.Leg, F.St.cs(s), k) == Some{F.Board{}} : Maybe<&2, F.Leg>}, free: {F.W.fl(F.St.w(s)) == False{} : Bool}) -> {F.W.fl(F.St.w(F.step(s, F.Step{k, ok}))) == True{} : Bool}:
  match s:
    case F.St{w, +cs}:
      match w:
        case F.W{sto, +fl, +ld, +n}:
          match sto:
            case F.Sto{+c, +fr}:
              %Equal.sym(Maybe<&2, F.Leg>, List.get(&2, F.Leg, cs, k), Some{F.Board{}}, boards) : {F.W.fl(F.St.w(F.step.at(_, k, ok, F.W{F.Sto{c, fr}, fl, ld, n}, cs))) == True{} : Bool}
              %Equal.sym(Bool, fl, False{}, free) : {F.W.fl(F.St.w(F.put(k, F.adv.board(F.W{F.Sto{c, fr}, _, ld, n}), cs))) == True{} : Bool}
              {==}

def AuthFlight.flight_board_leads(s, k, ok, boards, free):
  +bd = boards
  +fe = free
  (pfb.leg(s, k, ok, bd, fe), pfb.fl(s, k, ok, bd, fe))
