# eukhe: the proof of LAW semver_le_trans

import Base
import ../../bend/semver.bend as Sv
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

def ps.le2_trans(b1: Nat, b2: Nat, b3: Nat, +c1: Nat, +c2: Nat, +c3: Nat, h1: {Sv.Ver.le2(b1, b2, c1, c2) == True{} : Bool}, h2: {Sv.Ver.le2(b2, b3, c2, c3) == True{} : Bool}) -> {Sv.Ver.le2(b1, b3, c1, c3) == True{} : Bool}:
  match b1 b2 b3:
    case 0n 0n 0n:
      LA.ps.num_trans(c1, c2, c3, h1, h2)
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      L.semver.ps.absurdF({Sv.Num.le(c1, c3) == True{} : Bool}, h2)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      L.semver.ps.absurdF({Sv.Ver.le2(1n+p, b3, c1, c3) == True{} : Bool}, h1)
    case 1n+p 1n+q 0n:
      L.semver.ps.absurdF({False{} == True{} : Bool}, h2)
    case 1n+p 1n+q 1n+r:
      ps.le2_trans(p, q, r, c1, c2, c3, h1, h2)

def ps.le3_trans(a1: Nat, a2: Nat, a3: Nat, +b1: Nat, +b2: Nat, +b3: Nat, +c1: Nat, +c2: Nat, +c3: Nat, h1: {Sv.Ver.le3(a1, a2, b1, b2, c1, c2) == True{} : Bool}, h2: {Sv.Ver.le3(a2, a3, b2, b3, c2, c3) == True{} : Bool}) -> {Sv.Ver.le3(a1, a3, b1, b3, c1, c3) == True{} : Bool}:
  match a1 a2 a3:
    case 0n 0n 0n:
      ps.le2_trans(b1, b2, b3, c1, c2, c3, h1, h2)
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      L.semver.ps.absurdF({Sv.Ver.le2(b1, b3, c1, c3) == True{} : Bool}, h2)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      L.semver.ps.absurdF({Sv.Ver.le3(1n+p, a3, b1, b3, c1, c3) == True{} : Bool}, h1)
    case 1n+p 1n+q 0n:
      L.semver.ps.absurdF({False{} == True{} : Bool}, h2)
    case 1n+p 1n+q 1n+r:
      ps.le3_trans(p, q, r, b1, b2, b3, c1, c2, c3, h1, h2)

def semver.ps.le_trans(u: Sv.Ver, v: Sv.Ver, w: Sv.Ver, h1: {Sv.Ver.le(u, v) == True{} : Bool}, h2: {Sv.Ver.le(v, w) == True{} : Bool}) -> {Sv.Ver.le(u, w) == True{} : Bool}:
  match u v w:
    case Sv.Ver{a1, b1, c1} Sv.Ver{a2, b2, c2} Sv.Ver{a3, b3, c3}:
      ps.le3_trans(a1, a2, a3, b1, b2, b3, c1, c2, c3, h1, h2)

def Laws.semver_le_trans(u, v, w, uv, vw):
  semver.ps.le_trans(u, v, w, uv, vw)
