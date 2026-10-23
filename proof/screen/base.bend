# eukhe: lemmas the proofs of area screen share

import Base
import ../base.bend as L

def screen.ps.and_t(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def ps.min_le_l(n: Nat, m: Nat) -> {Nat.is_le(Nat.min(n, m), n) == True{} : Bool}:
  match n m:
    case 0n _:
      {==}
    case 1n+np 0n:
      {==}
    case 1n+np 1n+mp:
      ps.min_le_l(np, mp)

# 2. Pacing
# ---------

# a frame shows no more than the backlog
def ps.bound(s: Nat, r: Nat, +x: Nat, h: {Nat.is_le(s, r) == True{} : Bool}) -> {Nat.is_le(Nat.add(s, Nat.min(Nat.sub(r, s), x)), r) == True{} : Bool}:
  match s r:
    case 0n 0n:
      {==}
    case 0n 1n+rp:
      ps.min_le_l(1n+rp, x)
    case 1n+sp 0n:
      L.screen.ps.absurdF({Nat.is_le(Nat.add(1n+sp, Nat.min(Nat.sub(0n, 1n+sp), x)), 0n) == True{} : Bool}, h)
    case 1n+sp 1n+rp:
      ps.bound(sp, rp, x, h)
