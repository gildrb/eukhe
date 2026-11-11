# eukhe: the proof of LAW flight_step_progresses
# Caller k's step puts the leg its adv gives at its index (LA.pf.put_eta,
# LA.pf.get_put); split on the leg and on what adv reads (the store's
# freshness, the flight in flight, the fetch's result, the landed
# outcome): every leg it gives ranks below the one it moved. A served leg
# and a wait whose flight has not landed contradict the premise.

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight/model.bend as AuthFlight
import ./base.bend as LA

# a landed wait is served
def pg.got(m: Maybe<&2, F.Out>, +f: Nat, +w: F.W, mv: {Maybe.is_some(&2, F.Out, m) == True{} : Bool}) -> {Nat.is_lt(AuthFlight.af_rank(F.Adv.l(F.adv.wait.got(f, m, w))), 1n) == True{} : Bool}:
  match m:
    case None{}:
      LA.auth_flight.pf.absurdF({Nat.is_lt(AuthFlight.af_rank(F.Adv.l(F.adv.wait.got(f, None{}, w))), 1n) == True{} : Bool}, mv)
    case Some{o}:
      {==}

def pg.adv(l: F.Leg, ok: Bool, +c: Nat, fr: Bool, fl: Bool, +ld: List<&2, F.Out>, +n: Nat, mv: {AuthFlight.af_moves(l, ld) == True{} : Bool}) -> {Nat.is_lt(AuthFlight.af_rank(F.Adv.l(F.adv(l, ok, F.W{F.Sto{c, fr}, fl, ld, n}))), AuthFlight.af_rank(l)) == True{} : Bool}:
  match l:
    case F.Load{}:
      match fr:
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
      match fr:
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
      match fr:
        case True{}:
          {==}
        case False{}:
          {==}
    case F.Land{f, o}:
      {==}
    case F.Waiting{+f}:
      pg.got(List.get(&2, F.Out, ld, f), f, F.W{F.Sto{c, fr}, fl, ld, n}, mv)
    case F.Served{v, o}:
      LA.auth_flight.pf.absurdF({Nat.is_lt(AuthFlight.af_rank(F.Adv.l(F.adv(F.Served{v, o}, ok, F.W{F.Sto{c, fr}, fl, ld, n}))), AuthFlight.af_rank(F.Served{v, o})) == True{} : Bool}, mv)

# the leg at index k after its step is the leg adv gives
def pg.at(+l: F.Leg, +k: Nat, +ok: Bool, +w: F.W, +cs: List<&2, F.Leg>, at: {List.get(&2, F.Leg, cs, k) == Some{l} : Maybe<&2, F.Leg>}) -> {List.get(&2, F.Leg, F.St.cs(F.step.at(List.get(&2, F.Leg, cs, k), k, ok, w, cs)), k) == Some{F.Adv.l(F.adv(l, ok, w))} : Maybe<&2, F.Leg>}:
  +g = at
  %Equal.sym(Maybe<&2, F.Leg>, List.get(&2, F.Leg, cs, k), Some{l}, g) : {List.get(&2, F.Leg, F.St.cs(F.step.at(_, k, ok, w, cs)), k) == Some{F.Adv.l(F.adv(l, ok, w))} : Maybe<&2, F.Leg>}
  %LA.pf.put_eta(k, F.adv(l, ok, w), cs) : {List.get(&2, F.Leg, F.St.cs(_), k) == Some{F.Adv.l(F.adv(l, ok, w))} : Maybe<&2, F.Leg>}
  LA.pf.get_put(F.Leg, cs, k, l, F.Adv.l(F.adv(l, ok, w)), g)

def pg.main(s: F.St, +k: Nat, +ok: Bool, +l: F.Leg, at: {List.get(&2, F.Leg, F.St.cs(s), k) == Some{l} : Maybe<&2, F.Leg>}, mv: {AuthFlight.af_moves(l, F.W.landed(F.St.w(s))) == True{} : Bool}) -> {Nat.is_lt(AuthFlight.af_mrank(List.get(&2, F.Leg, F.St.cs(F.step(s, F.Step{k, ok})), k)), AuthFlight.af_rank(l)) == True{} : Bool}:
  match s:
    case F.St{w, +cs}:
      match w:
        case F.W{sto, +fl, +ld, +n}:
          match sto:
            case F.Sto{+c, +fr}:
              %Equal.sym(Maybe<&2, F.Leg>, List.get(&2, F.Leg, F.St.cs(F.step.at(List.get(&2, F.Leg, cs, k), k, ok, F.W{F.Sto{c, fr}, fl, ld, n}, cs)), k), Some{F.Adv.l(F.adv(l, ok, F.W{F.Sto{c, fr}, fl, ld, n}))}, pg.at(l, k, ok, F.W{F.Sto{c, fr}, fl, ld, n}, cs, at)) : {Nat.is_lt(AuthFlight.af_mrank(_), AuthFlight.af_rank(l)) == True{} : Bool}
              pg.adv(l, ok, c, fr, fl, ld, n, mv)

def AuthFlight.flight_step_progresses(s, k, ok, l, at, moves):
  pg.main(s, k, ok, l, at, moves)
