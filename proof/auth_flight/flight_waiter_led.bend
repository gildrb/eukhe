# eukhe: the proof of LAW flight_waiter_led
# Every run keeps the model's invariant (LA.pf.inv_run), whose clause for a
# waiting caller (LA.pf.Wt) is that its flight landed or is the flight in
# flight, numbered |landed|; read it as the law's Bool (pw.of).

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight/model.bend as AuthFlight
import ./base.bend as LA

def pw.eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pw.eq_refl(p)

def pw.of(m: Maybe<&2, F.Out>, +fl: Bool, +ld: List<&2, F.Out>, +f: Nat, g: LA.pf.WtM(m, fl, ld, f)) -> {Bool.or(Maybe.is_some(&2, F.Out, m), Bool.and(fl, Nat.is_eq(f, List.length(&2, F.Out, ld)))) == True{} : Bool}:
  match m:
    case None{}:
      (efl, ef) = g
      %Equal.sym(Bool, fl, True{}, efl) : {Bool.or(False{}, Bool.and(_, Nat.is_eq(f, List.length(&2, F.Out, ld)))) == True{} : Bool}
      %Equal.sym(Nat, f, List.length(&2, F.Out, ld), ef) : {Bool.or(False{}, Bool.and(True{}, Nat.is_eq(_, List.length(&2, F.Out, ld)))) == True{} : Bool}
      pw.eq_refl(List.length(&2, F.Out, ld))
    case Some{o}:
      {==}

def pw.main(s: F.St, inv: LA.auth_flight.pf.Inv(s), +k: Nat, +f: Nat, waits: {List.get(&2, F.Leg, F.St.cs(s), k) == Some{F.Waiting{f}} : Maybe<&2, F.Leg>}) -> {Bool.or(Maybe.is_some(&2, F.Out, List.get(&2, F.Out, F.W.landed(F.St.w(s)), f)), Bool.and(F.W.fl(F.St.w(s)), Nat.is_eq(f, List.length(&2, F.Out, F.W.landed(F.St.w(s)))))) == True{} : Bool}:
  match s:
    case F.St{w, +cs}:
      match w:
        case F.W{+sto, +fl, +ld, +n}:
          (cnt, all) = inv
          pw.of(List.get(&2, F.Out, ld, f), fl, ld, f, LA.pf.all_get(F.W{sto, fl, ld, n}, cs, k, F.Waiting{f}, waits, all))

def AuthFlight.flight_waiter_led(evs, k, f, waits):
  pw.main(AuthFlight.am_run(evs), LA.pf.inv_run(evs), k, f, waits)
