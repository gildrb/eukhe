# eukhe: the proof of LAW semver_le_total

import Base
import ../../bend/semver.bend as Sv
import ../../laws/semver.bend as Semver

def ps.num_total(a: Nat, b: Nat) -> {Bool.or(Sv.Num.le(a, b), Sv.Num.le(b, a)) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ps.num_total(p, q)

def ps.le2_total(b1: Nat, b2: Nat, +c1: Nat, +c2: Nat) -> {Bool.or(Sv.Ver.le2(b1, b2, c1, c2), Sv.Ver.le2(b2, b1, c2, c1)) == True{} : Bool}:
  match b1 b2:
    case 0n 0n:
      ps.num_total(c1, c2)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ps.le2_total(p, q, c1, c2)

def ps.le3_total(a1: Nat, a2: Nat, +b1: Nat, +b2: Nat, +c1: Nat, +c2: Nat) -> {Bool.or(Sv.Ver.le3(a1, a2, b1, b2, c1, c2), Sv.Ver.le3(a2, a1, b2, b1, c2, c1)) == True{} : Bool}:
  match a1 a2:
    case 0n 0n:
      ps.le2_total(b1, b2, c1, c2)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ps.le3_total(p, q, b1, b2, c1, c2)

def ps.le_total(u: Sv.Ver, v: Sv.Ver) -> {Bool.or(Sv.Ver.le(u, v), Sv.Ver.le(v, u)) == True{} : Bool}:
  match u v:
    case Sv.Ver{a1, b1, c1} Sv.Ver{a2, b2, c2}:
      ps.le3_total(a1, a2, b1, b2, c1, c2)

def Semver.semver_le_total(u, v):
  ps.le_total(u, v)
