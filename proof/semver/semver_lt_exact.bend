# eukhe: the proof of LAW semver_lt_exact
#
# PROOF of LAW semver_lt_exact: Ver.lt(u, v) is not Ver.le(v, u); the walk
# of Ver.le3 over the swapped majors (then Ver.le2 over the minors, Num.le
# over the patches) answers the negation of the strict native compare
# (induction on each pair).

import Base
import ../../bend/semver.bend as Sv
import ../../laws/semver.bend as Semver

def plt.num(a: Nat, b: Nat) -> {Bool.not(Sv.Num.le(b, a)) == Nat.is_lt(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      plt.num(p, q)

def plt.le2(b1: Nat, b2: Nat, +c1: Nat, +c2: Nat) -> {Bool.not(Sv.Ver.le2(b2, b1, c2, c1)) == Bool.or(Nat.is_lt(b1, b2), Bool.and(Nat.is_eq(b1, b2), Nat.is_lt(c1, c2))) : Bool}:
  match b1 b2:
    case 0n 0n:
      plt.num(c1, c2)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      plt.le2(p, q, c1, c2)

def plt.le3(a1: Nat, a2: Nat, +b1: Nat, +b2: Nat, +c1: Nat, +c2: Nat) -> {Bool.not(Sv.Ver.le3(a2, a1, b2, b1, c2, c1)) == Bool.or(Nat.is_lt(a1, a2), Bool.and(Nat.is_eq(a1, a2), Bool.or(Nat.is_lt(b1, b2), Bool.and(Nat.is_eq(b1, b2), Nat.is_lt(c1, c2))))) : Bool}:
  match a1 a2:
    case 0n 0n:
      plt.le2(b1, b2, c1, c2)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      plt.le3(p, q, b1, b2, c1, c2)

def Semver.semver_lt_exact(a1, b1, c1, a2, b2, c2):
  plt.le3(a1, a2, b1, b2, c1, c2)
