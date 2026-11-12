# eukhe: the proof of LAW flight_one_flight
# Every run keeps the model's invariant (LA.pf.inv_run): the callers that
# lead number 1 when a flight is in flight, else 0 (pf.leads == pf.holds),
# and every leader's flight is |landed| (pf.Good's pf.Lead). The laws'
# counts are those counts (po.leaders, po.bit), leg by leg.

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight/model.bend as AuthFlight
import ./base.bend as LA

def po.cons1(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  Equal.cong(Nat, Nat, x => 1n+x, a, b, e)

# the laws' leader count is the proofs' count
def po.leaders(cs: List<&2, F.Leg>) -> {AuthFlight.af_leaders(cs) == LA.pf.leads(cs) : Nat}:
  match cs:
    case Nil{}:
      {==}
    case l <> t:
      match l:
        case F.Load{}:
          po.leaders(t)
        case F.Board{}:
          po.leaders(t)
        case F.Check{f}:
          po.cons1(AuthFlight.af_leaders(t), LA.pf.leads(t), po.leaders(t))
        case F.Fetch{f}:
          po.cons1(AuthFlight.af_leaders(t), LA.pf.leads(t), po.leaders(t))
        case F.Store{f, c}:
          po.cons1(AuthFlight.af_leaders(t), LA.pf.leads(t), po.leaders(t))
        case F.Land{f, o}:
          po.cons1(AuthFlight.af_leaders(t), LA.pf.leads(t), po.leaders(t))
        case F.Waiting{f}:
          po.leaders(t)
        case F.Served{v, o}:
          po.leaders(t)

def po.bit(b: Bool) -> {LA.pf.holds(b) == AuthFlight.am_bit(b) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def po.eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      po.eq_refl(p)

# a leader of flight f, f being |ld|, is on flight |ld|
def po.on(+ld: List<&2, F.Out>, +f: Nat, ef: {f == List.length(&2, F.Out, ld) : Nat}) -> {Nat.is_eq(f, List.length(&2, F.Out, ld)) == True{} : Bool}:
  %Equal.sym(Nat, f, List.length(&2, F.Out, ld), ef) : {Nat.is_eq(_, List.length(&2, F.Out, ld)) == True{} : Bool}
  po.eq_refl(List.length(&2, F.Out, ld))

# every leader leads flight |ld|
def po.all_on(+s: F.Sto, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, cs: List<&2, F.Leg>, all: LA.pf.All(F.W{s, fl, ld, n}, cs)) -> {AuthFlight.af_all_on(List.length(&2, F.Out, ld), cs) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case l <> t:
      match l:
        case F.Load{}:
          (g, rest) = all
          po.all_on(s, fl, ld, n, t, rest)
        case F.Board{}:
          (g, rest) = all
          po.all_on(s, fl, ld, n, t, rest)
        case F.Check{+f}:
          (g, rest) = all
          (efl, ef) = g
          %Equal.sym(Bool, Nat.is_eq(f, List.length(&2, F.Out, ld)), True{}, po.on(ld, f, ef)) : {Bool.and(_, AuthFlight.af_all_on(List.length(&2, F.Out, ld), t)) == True{} : Bool}
          po.all_on(s, fl, ld, n, t, rest)
        case F.Fetch{+f}:
          (g, rest) = all
          (efl, ef) = g
          %Equal.sym(Bool, Nat.is_eq(f, List.length(&2, F.Out, ld)), True{}, po.on(ld, f, ef)) : {Bool.and(_, AuthFlight.af_all_on(List.length(&2, F.Out, ld), t)) == True{} : Bool}
          po.all_on(s, fl, ld, n, t, rest)
        case F.Store{+f, c}:
          (g, rest) = all
          (efl, ef) = g
          %Equal.sym(Bool, Nat.is_eq(f, List.length(&2, F.Out, ld)), True{}, po.on(ld, f, ef)) : {Bool.and(_, AuthFlight.af_all_on(List.length(&2, F.Out, ld), t)) == True{} : Bool}
          po.all_on(s, fl, ld, n, t, rest)
        case F.Land{+f, o}:
          (g, rest) = all
          (lead, kept) = g
          (efl, ef) = lead
          %Equal.sym(Bool, Nat.is_eq(f, List.length(&2, F.Out, ld)), True{}, po.on(ld, f, ef)) : {Bool.and(_, AuthFlight.af_all_on(List.length(&2, F.Out, ld), t)) == True{} : Bool}
          po.all_on(s, fl, ld, n, t, rest)
        case F.Waiting{f}:
          (g, rest) = all
          po.all_on(s, fl, ld, n, t, rest)
        case F.Served{v, o}:
          (g, rest) = all
          po.all_on(s, fl, ld, n, t, rest)

def po.main(s: F.St, inv: LA.auth_flight.pf.Inv(s)) -> ({AuthFlight.af_leaders(F.St.cs(s)) == AuthFlight.am_bit(F.W.fl(F.St.w(s))) : Nat} & {AuthFlight.af_all_on(List.length(&2, F.Out, F.W.landed(F.St.w(s))), F.St.cs(s)) == True{} : Bool}):
  match s:
    case F.St{w, +cs}:
      match w:
        case F.W{+sto, +fl, +ld, +n}:
          (cnt, all) = inv
          (Equal.trans(Nat, AuthFlight.af_leaders(cs), LA.pf.holds(fl), AuthFlight.am_bit(fl), Equal.trans(Nat, AuthFlight.af_leaders(cs), LA.pf.leads(cs), LA.pf.holds(fl), po.leaders(cs), cnt), po.bit(fl)), po.all_on(sto, fl, ld, n, cs, all))

def AuthFlight.flight_one_flight(evs):
  po.main(AuthFlight.am_run(evs), LA.pf.inv_run(evs))
