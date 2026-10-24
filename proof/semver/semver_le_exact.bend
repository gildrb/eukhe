# eukhe: the proof of LAW semver_le_exact
#
# PROOF of LAW semver_le_exact: Ver.le3 walks both majors down together:
# a lower major answers True, a higher one False, equal ones hand over to
# Ver.le2 on the minors, which hands over to Num.le on the patches; each
# walk is the native compare of the spec (induction on the pair).

import Base
import ../../bend/semver.bend as Sv
import ../../laws/semver.bend as Semver

def pl.num(a: Nat, b: Nat) -> {Sv.Num.le(a, b) == Nat.is_le(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pl.num(p, q)

def pl.le2(b1: Nat, b2: Nat, +c1: Nat, +c2: Nat) -> {Sv.Ver.le2(b1, b2, c1, c2) == Bool.or(Nat.is_lt(b1, b2), Bool.and(Nat.is_eq(b1, b2), Nat.is_le(c1, c2))) : Bool}:
  match b1 b2:
    case 0n 0n:
      pl.num(c1, c2)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pl.le2(p, q, c1, c2)

def pl.le3(a1: Nat, a2: Nat, +b1: Nat, +b2: Nat, +c1: Nat, +c2: Nat) -> {Sv.Ver.le3(a1, a2, b1, b2, c1, c2) == Bool.or(Nat.is_lt(a1, a2), Bool.and(Nat.is_eq(a1, a2), Bool.or(Nat.is_lt(b1, b2), Bool.and(Nat.is_eq(b1, b2), Nat.is_le(c1, c2))))) : Bool}:
  match a1 a2:
    case 0n 0n:
      pl.le2(b1, b2, c1, c2)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pl.le3(p, q, b1, b2, c1, c2)

def Semver.semver_le_exact(a1, b1, c1, a2, b2, c2):
  pl.le3(a1, a2, b1, b2, c1, c2)
