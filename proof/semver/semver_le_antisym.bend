# eukhe: the proof of LAW semver_le_antisym

import Base
import ../../bend/semver.bend as Sv
import ../../LAWS.bend as Laws
import ../base.bend as L

def ps.num_anti(a: Nat, b: Nat, h1: {Sv.Num.le(a, b) == True{} : Bool}, h2: {Sv.Num.le(b, a) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      L.semver.ps.absurdF({0n == 1n+q : Nat}, h2)
    case 1n+p 0n:
      L.semver.ps.absurdF({1n+p == 0n : Nat}, h1)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, ps.num_anti(p, q, h1, h2))

def ps.bminor(v: Sv.Ver) -> Sv.Ver:
  match v:
    case Sv.Ver{a, b, c}:
      Sv.Ver{a, 1n+b, c}

def ps.bmajor(v: Sv.Ver) -> Sv.Ver:
  match v:
    case Sv.Ver{a, b, c}:
      Sv.Ver{1n+a, b, c}

def ps.le2_anti(-a: Nat, b1: Nat, b2: Nat, +c1: Nat, +c2: Nat, h1: {Sv.Ver.le2(b1, b2, c1, c2) == True{} : Bool}, h2: {Sv.Ver.le2(b2, b1, c2, c1) == True{} : Bool}) -> {Sv.Ver{a, b1, c1} == Sv.Ver{a, b2, c2} : Sv.Ver}:
  match b1 b2:
    case 0n 0n:
      Equal.cong(Nat, Sv.Ver, x => Sv.Ver{a, 0n, x}, c1, c2, ps.num_anti(c1, c2, h1, h2))
    case 0n 1n+q:
      L.semver.ps.absurdF({Sv.Ver{a, 0n, c1} == Sv.Ver{a, 1n+q, c2} : Sv.Ver}, h2)
    case 1n+p 0n:
      L.semver.ps.absurdF({Sv.Ver{a, 1n+p, c1} == Sv.Ver{a, 0n, c2} : Sv.Ver}, h1)
    case 1n+p 1n+q:
      Equal.cong(Sv.Ver, Sv.Ver, ps.bminor, Sv.Ver{a, p, c1}, Sv.Ver{a, q, c2}, ps.le2_anti(a, p, q, c1, c2, h1, h2))

def ps.le3_anti(a1: Nat, a2: Nat, +b1: Nat, +b2: Nat, +c1: Nat, +c2: Nat, h1: {Sv.Ver.le3(a1, a2, b1, b2, c1, c2) == True{} : Bool}, h2: {Sv.Ver.le3(a2, a1, b2, b1, c2, c1) == True{} : Bool}) -> {Sv.Ver{a1, b1, c1} == Sv.Ver{a2, b2, c2} : Sv.Ver}:
  match a1 a2:
    case 0n 0n:
      ps.le2_anti(0n, b1, b2, c1, c2, h1, h2)
    case 0n 1n+q:
      L.semver.ps.absurdF({Sv.Ver{0n, b1, c1} == Sv.Ver{1n+q, b2, c2} : Sv.Ver}, h2)
    case 1n+p 0n:
      L.semver.ps.absurdF({Sv.Ver{1n+p, b1, c1} == Sv.Ver{0n, b2, c2} : Sv.Ver}, h1)
    case 1n+p 1n+q:
      Equal.cong(Sv.Ver, Sv.Ver, ps.bmajor, Sv.Ver{p, b1, c1}, Sv.Ver{q, b2, c2}, ps.le3_anti(p, q, b1, b2, c1, c2, h1, h2))

def ps.le_anti(u: Sv.Ver, v: Sv.Ver, h1: {Sv.Ver.le(u, v) == True{} : Bool}, h2: {Sv.Ver.le(v, u) == True{} : Bool}) -> {u == v : Sv.Ver}:
  match u v:
    case Sv.Ver{a1, b1, c1} Sv.Ver{a2, b2, c2}:
      ps.le3_anti(a1, a2, b1, b2, c1, c2, h1, h2)

def Laws.semver_le_antisym(u, v, uv, vu):
  ps.le_anti(u, v, uv, vu)
