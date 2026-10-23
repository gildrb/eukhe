# eukhe: the proof of LAW settle_reached

import Base
import ../../bend/compactor.bend as C
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

def pc.NZ(n: Nat, A: Type) -> Type:
  match n:
    case 0n:
      A
    case 1n+p:
      Unit

# 1+n is not 0
def pc.succ_zero(-A: Type, -n: Nat, e: {1n+n == 0n : Nat}) -> A:
  %e : pc.NZ(_, A)
  Unit{}

def pc.le_zero_eq(x: Nat, e: {Nat.is_le(x, 0n) == True{} : Bool}) -> {x == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      L.pc.absurd_ft({1n+p == 0n : Nat}, e)

# h + x <= m <= h leaves x = 0
def pc.rest_zero(h: Nat, x: Nat, m: Nat, e1: {Nat.is_le(Nat.add(h, x), m) == True{} : Bool}, e2: {Nat.is_le(m, h) == True{} : Bool}) -> {x == 0n : Nat}:
  match h m:
    case 0n 0n:
      pc.le_zero_eq(x, e1)
    case 0n 1n+q:
      L.pc.absurd_ft({x == 0n : Nat}, e2)
    case 1n+p 0n:
      L.pc.absurd_ft({x == 0n : Nat}, e1)
    case 1n+p 1n+q:
      pc.rest_zero(p, x, q, e1, e2)

def pc.zero_settled(ps: List<&2, C.Pend>, e: {C.measure(ps) == 0n : Nat}) -> {C.settled(ps) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case p <> rest:
      match p:
        case C.Made{}:
          pc.zero_settled(rest, e)
        case C.Owed{n}:
          pc.succ_zero({Bool.and(False{}, C.settled(rest)) == True{} : Bool}, Nat.add(n, C.measure(rest)), e)

def pc.settle_reached(+es: List<&2, C.End>, +ps: List<&2, C.Pend>, enough: {Nat.is_le(C.measure(ps), C.hits(es, ps)) == True{} : Bool}) -> {C.settled(C.run(es, ps)) == True{} : Bool}:
  pc.zero_settled(C.run(es, ps), pc.rest_zero(C.hits(es, ps), C.measure(C.run(es, ps)), C.measure(ps), LA.pc.settle_bounded(es, ps), enough))

def Laws.settle_reached(es, ps, enough):
  pc.settle_reached(es, ps, enough)
