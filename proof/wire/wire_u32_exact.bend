# eukhe: the proof of LAW wire_u32_exact

import Base
import ../../bend/wire.bend as Wr
import ../../LAWS.bend as Laws
import ./base.bend as LA
import ./wire_nat_exact.bend as PWireNatExact

def wu_nat_eq_sound(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LA.wu_absurd({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      LA.wu_absurd({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, wu_nat_eq_sound(p, q, e))

# get_u32 accepts only what get_nat read and from_nat keeps

# a motive: at Got{y, r}, a is the Nat answer of y and r; trivial at Bad
def wu_M(a: Wr.Dec<Nat>, d: Wr.Dec<U32>) -> Type:
  match d:
    case Wr.Got{y, r}:
      {a == Wr.Got{U32.to_nat(y), r} : Wr.Dec<Nat>}
    case Wr.Bad{}:
      Unit

def wu_in_inv(ok: Bool, +n: Nat, +s: String, -x: U32, -rest: String, eok: {Nat.is_eq(U32.to_nat(U32.from_nat(n)), n) == ok : Bool}, h: {Wr.get_u32.in(ok, U32.from_nat(n), s) == Wr.Got{x, rest} : Wr.Dec<U32>}) -> {Wr.Got{n, s} == Wr.Got{U32.to_nat(x), rest} : Wr.Dec<Nat>}:
  match ok:
    case False{}:
      %h : wu_M(Wr.Got{n, s}, _)
      Unit{}
    case True{}:
      %h : wu_M(Wr.Got{n, s}, _)
      %Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, wu_nat_eq_sound(U32.to_nat(U32.from_nat(n)), n, eok)) : {Wr.Got{n, s} == Wr.Got{_, s} : Wr.Dec<Nat>}
      {==}

def wu_fit_inv(+r: Wr.Dec<Nat>, -x: U32, -rest: String, h: {Wr.get_u32.fit(r) == Wr.Got{x, rest} : Wr.Dec<U32>}) -> {r == Wr.Got{U32.to_nat(x), rest} : Wr.Dec<Nat>}:
  match r:
    case Wr.Got{n, s}:
      wu_in_inv(Nat.is_eq(U32.to_nat(U32.from_nat(n)), n), n, s, x, rest, {==}, h)
    case Wr.Bad{}:
      %h : wu_M(Wr.Bad{}, _)
      Unit{}

# LAW wire_u32_exact
def Laws.wire_u32_exact(s, x, rest, h):
  Laws.wire_nat_exact(s, U32.to_nat(x), rest, wu_fit_inv(Wr.get_nat(s), x, rest, h))
