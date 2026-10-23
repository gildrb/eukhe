# eukhe: the proof of LAW facts_room_leaves_the_answer

import Base
import ../../bend/facts.bend as Fx
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

def facts.pf.add_zero(+n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %facts.pf.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def pf.add_succ(+x: Nat, +q: Nat) -> {Nat.add(x, 1n+q) == 1n+Nat.add(x, q) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %pf.add_succ(p, q) : {1n+Nat.add(p, 1n+q) == 1n+_ : Nat}
      {==}

# (m - a) + a is m when a is at most m
def pf.sub_add(+m: Nat, +a: Nat, h: {Nat.is_le(a, m) == True{} : Bool}) -> {Nat.add(Nat.sub(m, a), a) == m : Nat}:
  match m a:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      L.pq.absurdF({Nat.add(Nat.sub(0n, 1n+q), 1n+q) == 0n : Nat}, h)
    case 1n+p 0n:
      facts.pf.add_zero(1n+p)
    case 1n+p 1n+q:
      %Equal.sym(Nat, Nat.add(Nat.sub(p, q), 1n+q), 1n+Nat.add(Nat.sub(p, q), q), pf.add_succ(Nat.sub(p, q), q)) : {_ == 1n+p : Nat}
      %pf.sub_add(p, q, h) : {1n+Nat.add(Nat.sub(p, q), q) == 1n+_ : Nat}
      {==}

def pf.le_add(+y: Nat, +a: Nat) -> {Nat.is_le(a, Nat.add(y, a)) == True{} : Bool}:
  match y:
    case 0n:
      LA.facts.pf.le_refl(a)
    case 1n+q:
      LA.pf.le_trans(a, Nat.add(q, a), 1n+Nat.add(q, a), pf.le_add(q, a), LA.facts.pf.le_succ(Nat.add(q, a)))

def pf.le_add_mono(+x: Nat, +y: Nat, +a: Nat, h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(Nat.add(x, a), Nat.add(y, a)) == True{} : Bool}:
  match x y:
    case 0n y:
      pf.le_add(y, a)
    case 1n+p 0n:
      L.pq.absurdF({Nat.is_le(Nat.add(1n+p, a), Nat.add(0n, a)) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pf.le_add_mono(p, q, a, h)

def pf.facts_room_leaves_the_answer(+b: Nat, +m: Nat, +a: Nat, fits: {Nat.is_le(a, m) == True{} : Bool}) -> {Nat.is_le(Nat.add(Fx.room(b, m, a), a), m) == True{} : Bool}:
  +R = Nat.min(b, Nat.sub(m, a))
  %pf.sub_add(m, a, fits) : {Nat.is_le(Nat.add(R, a), _) == True{} : Bool}
  pf.le_add_mono(R, Nat.sub(m, a), a, LA.pf.min_le_r(b, Nat.sub(m, a)))

def Laws.facts_room_leaves_the_answer(b, m, a, fits):
  pf.facts_room_leaves_the_answer(b, m, a, fits)
