# eukhe: the proof of LAW facts_aux_cap_within

import Base
import ../../bend/facts.bend as Fx
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

def w2.aux_cap(c: Bool, +b: Nat, +a: Nat, +top: Nat) -> {Fx.aux_cap.add(c, b, a, top) == Fx.fit.cap.add(c, a, top, b) : Nat}:
  match c:
    case True{}:
      L.pa.add_comm(b, a)
    case False{}:
      {==}

def w2.aux_sum(+b: Nat, +a: Nat, +top: Nat) -> {Fx.fit.cap.add(Nat.is_lt(b, Nat.sub(top, a)), a, top, b) == Nat.min(Nat.add(b, a), top) : Nat}:
  %L.pa.add_comm(a, b) : {Fx.fit.cap.add(Nat.is_lt(b, Nat.sub(top, a)), a, top, b) == Nat.min(_, top) : Nat}
  LA.w2.cap_sum(a, top, b)

def Laws.facts_aux_cap_within(b, a, top):
  +C = Nat.is_lt(b, Nat.sub(top, a))
  Equal.trans(Nat, Fx.aux_cap.add(C, b, a, top), Fx.fit.cap.add(C, a, top, b), Nat.min(Nat.add(b, a), top), w2.aux_cap(C, b, a, top), w2.aux_sum(b, a, top))
