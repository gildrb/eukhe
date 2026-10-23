# eukhe: the proof of LAW compact_starts_early

import Base
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer
import ../base.bend as L
import ./base.bend as LA

def pi.lt_le(a: Nat, b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      L.pi.absurdF({True{} == True{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      L.pi.absurdF({False{} == True{} : Bool}, h)
    case 1n+p 1n+q:
      pi.lt_le(p, q, h)

def pi.nle_lt(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      LA.pi.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      LA.pi.absurd({Nat.is_lt(1n+q, 0n) == True{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pi.nle_lt(p, q, h)

def pi.lt_zero(+a: Nat, +h: {Nat.is_lt(a, 0n) == True{} : Bool}) -> Empty:
  match a:
    case 0n:
      L.pi.absurdF(Empty, h)
    case 1n+p:
      L.pi.absurdF(Empty, h)

def pi.lt_succ(+a: Nat) -> {Nat.is_lt(a, 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      pi.lt_succ(p)

def pi.lt_succ_r(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      L.pi.absurdF({Nat.is_lt(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pi.lt_succ_r(p, q, h)

# Early compaction
# ----------------

def pi.le_succ_false(+x: Nat, +lim: Nat, +h: {Nat.is_le(x, lim) == True{} : Bool}) -> {Nat.is_le(1n+lim, x) == False{} : Bool}:
  match x lim:
    case 0n _:
      {==}
    case 1n+p 0n:
      L.pi.absurdF({Nat.is_le(1n, 1n+p) == False{} : Bool}, h)
    case 1n+p 1n+q:
      pi.le_succ_false(p, q, h)

def pi.lt_sub(+x: Nat, +lim: Nat, +m: Nat, +h: {Nat.is_lt(x, Nat.sub(lim, m)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(x, m), lim) == True{} : Bool}:
  match lim m:
    case 0n _:
      LA.pi.void({Nat.is_lt(Nat.add(x, m), 0n) == True{} : Bool}, pi.lt_zero(x, h))
    case 1n+a 0n:
      %LA.pi.add_zero(x) : {Nat.is_lt(_, 1n+a) == True{} : Bool}
      h
    case 1n+a 1n+b:
      %Equal.sym(Nat, Nat.add(x, 1n+b), 1n+Nat.add(x, b), LA.pi.add_succ(x, b)) : {Nat.is_lt(_, 1n+a) == True{} : Bool}
      pi.lt_sub(x, a, b, h)

# an index past i: the first reach from j > i
def pi.later(+xs: List<&2, Nat>, +t: Nat, +j: Nat, hit: Bool, +i: Nat, +lt: {Nat.is_lt(i, j) == True{} : Bool}) -> {If.m.lt(Some{i}, If.first_at.go(xs, t, j, hit)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      match hit:
        case True{}:
          lt
        case False{}:
          pi.later(rest, t, 1n+j, If.reach.at(rest, t), i, pi.lt_succ_r(i, j, lt))

# below the threshold, the next size stays within the limit
def pi.compact_go(+xs: List<&2, Nat>, +m: Nat, +lim: Nat, +prev: Nat, +i: Nat, hit: Bool, +eh: {If.reach.at(xs, Nat.sub(lim, m)) == hit : Bool}, +inv: {Nat.is_le(Nat.add(prev, m), lim) == True{} : Bool}, +st: {If.steps_le(xs, m, prev) == True{} : Bool}) -> {If.m.lt(If.first_at.go(xs, Nat.sub(lim, m), i, hit), If.first_at.go(xs, 1n+lim, i, If.reach.at(xs, 1n+lim))) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      match hit:
        case True{}:
          +xle = LA.pi.le_trans(x, Nat.add(prev, m), lim, LA.pi.and_l(Nat.is_le(x, Nat.add(prev, m)), If.steps_le(rest, m, x), st), inv)
          %Equal.sym(Bool, Nat.is_le(1n+lim, x), False{}, pi.le_succ_false(x, lim, xle)) : {If.m.lt(Some{i}, If.first_at.go(x <> rest, 1n+lim, i, _)) == True{} : Bool}
          pi.later(rest, 1n+lim, 1n+i, If.reach.at(rest, 1n+lim), i, pi.lt_succ(i))
        case False{}:
          +T = Nat.sub(lim, m)
          +xle = LA.pi.le_trans(x, Nat.add(prev, m), lim, LA.pi.and_l(Nat.is_le(x, Nat.add(prev, m)), If.steps_le(rest, m, x), st), inv)
          %Equal.sym(Bool, Nat.is_le(1n+lim, x), False{}, pi.le_succ_false(x, lim, xle)) : {If.m.lt(If.first_at.go(rest, T, 1n+i, If.reach.at(rest, T)), If.first_at.go(x <> rest, 1n+lim, i, _)) == True{} : Bool}
          +inv2 = pi.lt_le(Nat.add(x, m), lim, pi.lt_sub(x, lim, m, pi.nle_lt(T, x, eh)))
          pi.compact_go(rest, m, lim, x, 1n+i, If.reach.at(rest, T), {==}, inv2, LA.pi.and_r(Nat.is_le(x, Nat.add(prev, m)), If.steps_le(rest, m, x), st))

def pi.compact_starts_early(+xs: List<&2, Nat>, +m: Nat, +lim: Nat, small: {Nat.is_le(m, lim) == True{} : Bool}, steps: {If.steps_le(xs, m, 0n) == True{} : Bool}) -> {If.m.lt(If.first_at(xs, Nat.sub(lim, m), 0n), If.first_at(xs, 1n+lim, 0n)) == True{} : Bool}:
  pi.compact_go(xs, m, lim, 0n, 0n, If.reach.at(xs, Nat.sub(lim, m)), {==}, small, steps)

def Infer.compact_starts_early(xs, m, lim, small, steps):
  pi.compact_starts_early(xs, m, lim, small, steps)
