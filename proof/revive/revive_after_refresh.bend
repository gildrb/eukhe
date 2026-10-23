# eukhe: the proof of LAW revive_after_refresh

import Base
import ../../bend/revive.bend as Rv
import ../../laws/revive.bend as Revive
import ../base.bend as L

# adding b on the right keeps the order
def ps.le_mono_r(a: Nat, h: Nat, +b: Nat, ah: {Nat.is_le(a, h) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, b), Nat.add(h, b)) == True{} : Bool}:
  match a h:
    case 0n _:
      L.supervisor.ps.le_add_l(h, b)
    case 1n+p 0n:
      L.supervisor.ps.absurdF({Nat.is_le(Nat.add(1n+p, b), Nat.add(0n, b)) == True{} : Bool}, ah)
    case 1n+p 1n+q:
      ps.le_mono_r(p, q, b, ah)

def ps.lt_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n _:
      L.ps.le_zero(b)
    case 1n+p 0n:
      L.supervisor.ps.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      ps.lt_le(p, q, h)

# r below h and r + 1 not h make r + 1 below h
def ps.lt_succ_ne(r: Nat, h: Nat, lt: {Nat.is_lt(r, h) == True{} : Bool}, ne: {Nat.is_eq(1n+r, h) == False{} : Bool}) -> {Nat.is_lt(1n+r, h) == True{} : Bool}:
  match r h:
    case 0n 0n:
      L.supervisor.ps.absurdF({Nat.is_lt(1n, 0n) == True{} : Bool}, lt)
    case 0n 1n+q:
      match q:
        case 0n:
          L.supervisor.ps.absurd({Nat.is_lt(1n, 1n) == True{} : Bool}, ne)
        case 1n+s:
          {==}
    case 1n+p 0n:
      L.supervisor.ps.absurdF({Nat.is_lt(2n+p, 0n) == True{} : Bool}, lt)
    case 1n+p 1n+q:
      ps.lt_succ_ne(p, q, lt, ne)

# (D1) revive_after_refresh
# -------------------------

def ps.tick_at(b: Bool, +h: Nat, +r: Nat, e: {Nat.is_eq(1n+r, h) == b : Bool}, pos: {Nat.is_lt(0n, h) == True{} : Bool}, lt: {Nat.is_lt(r, h) == True{} : Bool}) -> {Nat.is_lt(Rv.tick.put(b, r), h) == True{} : Bool}:
  match b:
    case True{}:
      pos
    case False{}:
      ps.lt_succ_ne(r, h, lt, e)

# a tick keeps the time since the last record below h
def ps.tick_lt(+h: Nat, +r: Nat, pos: {Nat.is_lt(0n, h) == True{} : Bool}, lt: {Nat.is_lt(r, h) == True{} : Bool}) -> {Nat.is_lt(Rv.tick(h, r), h) == True{} : Bool}:
  ps.tick_at(Nat.is_eq(1n+r, h), h, r, {==}, pos, lt)

# so does a run of any length
def ps.since_lt(c: Nat, +h: Nat, +r: Nat, +pos: {Nat.is_lt(0n, h) == True{} : Bool}, lt: {Nat.is_lt(r, h) == True{} : Bool}) -> {Nat.is_lt(Rv.since(c, h, r), h) == True{} : Bool}:
  match c:
    case 0n:
      lt
    case 1n+p:
      ps.since_lt(p, h, Rv.tick(h, r), pos, ps.tick_lt(h, r, pos, lt))

def ps.revive_after_refresh(+h: Nat, +pos: {Nat.is_lt(0n, h) == True{} : Bool}, +b: Nat, +c: Nat, +d: Nat, soon: {Nat.is_le(d, b) == True{} : Bool}) -> {Rv.fresh(Nat.add(h, b), Rv.age(h, c, d)) == True{} : Bool}:
  +a = Rv.since(c, h, 0n)
  +al = ps.lt_le(a, h, ps.since_lt(c, h, 0n, pos, pos))
  L.supervisor.ps.le_trans(Nat.add(a, d), Nat.add(a, b), Nat.add(h, b), L.ps.le_mono(a, d, b, soon), ps.le_mono_r(a, h, b, al))

def Revive.revive_after_refresh(h, L.pos, b, c, d, soon):
  ps.revive_after_refresh(h, L.pos, b, c, d, soon)
