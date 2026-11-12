# eukhe: the proof of LAW semver_in_series_order

import Base
import ../../bend/semver.bend as Sv
import ../../laws/semver.bend as Semver

# PROOF of LAW semver_in_series_order: by induction on the majors (pso.l3)
# then the minors (pso.l2), as Ver.le3 and Ver.le2 descend: a major or a
# minor below the series' puts v below X.Y.0, one above puts it at or past
# X.(Y+1).0 (for the minor: the case Y+1 at v's minor is X.(Y+1).0 or
# newer whatever v's patch), equal ones put v in the interval.

def pso.l2(b: Nat, vb: Nat, +vc: Nat) -> {Nat.is_eq(b, vb) == Bool.and(Sv.Ver.le2(b, vb, 0n, vc), Bool.not(Sv.Ver.le2(1n+b, vb, 0n, vc))) : Bool}:
  match b vb:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      match q:
        case 0n:
          {==}
        case 1n+r:
          {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pso.l2(p, q, vc)

def pso.l3(a: Nat, va: Nat, +b: Nat, +vb: Nat, +vc: Nat) -> {Bool.and(Nat.is_eq(a, va), Nat.is_eq(b, vb)) == Bool.and(Sv.Ver.le3(a, va, b, vb, 0n, vc), Bool.not(Sv.Ver.le3(a, va, 1n+b, vb, 0n, vc))) : Bool}:
  match a va:
    case 0n 0n:
      pso.l2(b, vb, vc)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pso.l3(p, q, b, vb, vc)

def Semver.semver_in_series_order(a, b, c, v):
  match v:
    case Sv.Ver{+va, +vb, +vc}:
      pso.l3(a, va, b, vb, vc)
