# eukhe: the proof of LAW run_counts_lossless

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../laws/run/model.bend as Run
import ./base.bend as LA

def rk.att(+attempt: Nat, +notes: Nat, +e: {Nat.is_le(1n+notes, attempt) == True{} : Bool}) -> {attempt == 1n+Nat.add(Nat.sub(Nat.sub(attempt, 1n), notes), notes) : Nat}:
  match attempt:
    case 0n:
      LA.rk.absurd({0n == 1n+Nat.add(Nat.sub(Nat.sub(0n, 1n), notes), notes) : Nat}, e)
    case 1n++b:
      %LA.rk.sub0(b) : {1n+b == 1n+Nat.add(Nat.sub(_, notes), notes) : Nat}
      %LA.rk.subadd(b, notes, e) : {1n+_ == 1n+Nat.add(Nat.sub(b, notes), notes) : Nat}
      {==}

def rk.c(+compacted: Bool) -> {compacted == Nat.is_eq(RnDecision.c.of(compacted), 0n) : Bool}:
  match compacted:
    case True{}:
      {==}
    case False{}:
      {==}

def rk.run_counts_lossless(+l: RnDecision.Lim, +t: RnDecision.At, +w: {Run.rust.within(l, t) == True{} : Bool}) -> {Run.rust.back(l, RnDecision.At.a(l, t), RnDecision.At.n(l, t), RnDecision.At.p(l, t), RnDecision.At.c(t), RnDecision.At.streams(t)) == t : RnDecision.At}:
  match l:
    case RnDecision.Lim{+rounds, +wait, +retries, +most, +streams}:
      match t:
        case RnDecision.At{+attempt, +notes, +spent, +waited, +compacted}:
          +old = Nat.sub(Nat.sub(attempt, 1n), notes)
          +b1 = Nat.is_le(notes, most)
          +b2 = Nat.is_le(1n+notes, attempt)
          +b3 = Nat.is_le(old, retries)
          +b4 = Nat.is_le(waited, wait)
          +b5 = Nat.is_le(spent, streams)
          +w1 = LA.rk.and_l(b1, Bool.and(b2, Bool.and(b3, Bool.and(b4, b5))), w)
          +r1 = LA.rk.and_r(b1, Bool.and(b2, Bool.and(b3, Bool.and(b4, b5))), w)
          +w2 = LA.rk.and_l(b2, Bool.and(b3, Bool.and(b4, b5)), r1)
          +r2 = LA.rk.and_r(b2, Bool.and(b3, Bool.and(b4, b5)), r1)
          +w3 = LA.rk.and_l(b3, Bool.and(b4, b5), r2)
          +r3 = LA.rk.and_r(b3, Bool.and(b4, b5), r2)
          +w4 = LA.rk.and_l(b4, b5, r3)
          %LA.rk.subsub(retries, old, w3) : {RnDecision.At{1n+Nat.add(_, Nat.sub(most, Nat.sub(most, notes))), Nat.sub(most, Nat.sub(most, notes)), spent, Nat.sub(wait, Nat.sub(wait, waited)), Nat.is_eq(RnDecision.c.of(compacted), 0n)} == RnDecision.At{attempt, notes, spent, waited, compacted} : RnDecision.At}
          %LA.rk.subsub(most, notes, w1) : {RnDecision.At{1n+Nat.add(old, _), _, spent, Nat.sub(wait, Nat.sub(wait, waited)), Nat.is_eq(RnDecision.c.of(compacted), 0n)} == RnDecision.At{attempt, notes, spent, waited, compacted} : RnDecision.At}
          %LA.rk.subsub(wait, waited, w4) : {RnDecision.At{1n+Nat.add(old, notes), notes, spent, _, Nat.is_eq(RnDecision.c.of(compacted), 0n)} == RnDecision.At{attempt, notes, spent, waited, compacted} : RnDecision.At}
          %rk.c(compacted) : {RnDecision.At{1n+Nat.add(old, notes), notes, spent, waited, _} == RnDecision.At{attempt, notes, spent, waited, compacted} : RnDecision.At}
          %rk.att(attempt, notes, w2) : {RnDecision.At{_, notes, spent, waited, compacted} == RnDecision.At{attempt, notes, spent, waited, compacted} : RnDecision.At}
          {==}

def Run.run_counts_lossless(l, t, w):
  rk.run_counts_lossless(l, t, w)
