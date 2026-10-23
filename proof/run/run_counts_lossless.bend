# eukhe: the proof of LAW run_counts_lossless

import Base
import ../../bend/run.bend as Rn
import ../../LAWS.bend as Laws
import ./base.bend as LA

def rk.att(+attempt: Nat, +notes: Nat, +e: {Nat.is_le(1n+notes, attempt) == True{} : Bool}) -> {attempt == 1n+Nat.add(Nat.sub(Nat.sub(attempt, 1n), notes), notes) : Nat}:
  match attempt:
    case 0n:
      LA.rk.absurd({0n == 1n+Nat.add(Nat.sub(Nat.sub(0n, 1n), notes), notes) : Nat}, e)
    case 1n++b:
      %LA.rk.sub0(b) : {1n+b == 1n+Nat.add(Nat.sub(_, notes), notes) : Nat}
      %LA.rk.subadd(b, notes, e) : {1n+_ == 1n+Nat.add(Nat.sub(b, notes), notes) : Nat}
      {==}

def rk.c(+compacted: Bool) -> {compacted == Nat.is_eq(Rn.c.of(compacted), 0n) : Bool}:
  match compacted:
    case True{}:
      {==}
    case False{}:
      {==}

def rk.run_counts_lossless(+l: Rn.Lim, +t: Rn.At, +w: {Laws.rust.within(l, t) == True{} : Bool}) -> {Laws.rust.back(l, Rn.At.a(l, t), Rn.At.n(l, t), Rn.At.p(l, t), Rn.At.c(t)) == t : Rn.At}:
  match l:
    case Rn.Lim{+rounds, +wait, +retries, +most}:
      match t:
        case Rn.At{+attempt, +notes, +waited, +compacted}:
          +spent = Nat.sub(Nat.sub(attempt, 1n), notes)
          +b1 = Nat.is_le(notes, most)
          +b2 = Nat.is_le(1n+notes, attempt)
          +b3 = Nat.is_le(spent, retries)
          +b4 = Nat.is_le(waited, wait)
          +w1 = LA.rk.and_l(b1, Bool.and(b2, Bool.and(b3, b4)), w)
          +r1 = LA.rk.and_r(b1, Bool.and(b2, Bool.and(b3, b4)), w)
          +w2 = LA.rk.and_l(b2, Bool.and(b3, b4), r1)
          +r2 = LA.rk.and_r(b2, Bool.and(b3, b4), r1)
          +w3 = LA.rk.and_l(b3, b4, r2)
          +w4 = LA.rk.and_r(b3, b4, r2)
          %LA.rk.subsub(retries, spent, w3) : {Rn.At{1n+Nat.add(_, Nat.sub(most, Nat.sub(most, notes))), Nat.sub(most, Nat.sub(most, notes)), Nat.sub(wait, Nat.sub(wait, waited)), Nat.is_eq(Rn.c.of(compacted), 0n)} == Rn.At{attempt, notes, waited, compacted} : Rn.At}
          %LA.rk.subsub(most, notes, w1) : {Rn.At{1n+Nat.add(spent, _), _, Nat.sub(wait, Nat.sub(wait, waited)), Nat.is_eq(Rn.c.of(compacted), 0n)} == Rn.At{attempt, notes, waited, compacted} : Rn.At}
          %LA.rk.subsub(wait, waited, w4) : {Rn.At{1n+Nat.add(spent, notes), notes, _, Nat.is_eq(Rn.c.of(compacted), 0n)} == Rn.At{attempt, notes, waited, compacted} : Rn.At}
          %rk.c(compacted) : {Rn.At{1n+Nat.add(spent, notes), notes, waited, _} == Rn.At{attempt, notes, waited, compacted} : Rn.At}
          %rk.att(attempt, notes, w2) : {Rn.At{_, notes, waited, compacted} == Rn.At{attempt, notes, waited, compacted} : Rn.At}
          {==}

def Laws.run_counts_lossless(l, t, w):
  rk.run_counts_lossless(l, t, w)
