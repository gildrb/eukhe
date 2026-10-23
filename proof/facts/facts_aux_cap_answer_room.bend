# eukhe: the proof of LAW facts_aux_cap_answer_room

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts.bend as Facts

def pf.sub_zero(+a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pf.add_sub(+b: Nat, +a: Nat) -> {Nat.sub(Nat.add(b, a), b) == a : Nat}:
  match b:
    case 0n:
      pf.sub_zero(a)
    case 1n+p:
      pf.add_sub(p, a)

def pf.facts_aux_cap_answer_room(+b: Nat, +a: Nat) -> {Nat.sub(Fx.aux_cap(b, a), b) == a : Nat}:
  pf.add_sub(b, a)

def Facts.facts_aux_cap_answer_room(b, a):
  pf.facts_aux_cap_answer_room(b, a)
