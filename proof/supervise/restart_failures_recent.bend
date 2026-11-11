# eukhe: the proof of LAW restart_failures_recent
#
# PROOF: srf.cnt(w, d, A) counts the ages a of A with d + a < w. A step
# with gap x keeps the ages of A with x + a < w, each x ms older, so its
# count is srf.cnt(w, x, A) (srf.c1); counting the kept ages again d ms
# later counts the ages of A with (x + d) + a < w, since an age that left
# the window never comes back (srf.c2, srf.lt_false). By induction over the
# gaps after a failure (srf.run): the last failure, plus each earlier one
# whose distance to it is under the window, plus the ages of the start
# still inside it; from no failure the start has no age but the first.

import Base
import ../../bend/supervise.bend as Su
import ../../laws/supervise.bend as Supervise
import ../base/nat.bend as LNat

# the ages a of A with d + a < w
def srf.cnt(+w: Nat, +d: Nat, A: List<&2, Nat>) -> Nat:
  match A:
    case Nil{}:
      0n
    case +a <> t:
      Supervise.restart_inside.put(Nat.is_lt(Nat.add(d, a), w), srf.cnt(w, d, t))

def srf.len_put(b: Bool, +x: Nat, +r: List<&2, Nat>) -> {List.length(&2, Nat, Su.keep.put(b, x, r)) == Supervise.restart_inside.put(b, List.length(&2, Nat, r)) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a step with gap d keeps srf.cnt(w, d, A) ages
def srf.c1(+w: Nat, +d: Nat, A: List<&2, Nat>) -> {List.length(&2, Nat, Su.keep(w, Su.older(d, A))) == srf.cnt(w, d, A) : Nat}:
  match A:
    case Nil{}:
      {==}
    case +a <> +t:
      +b = Nat.is_lt(Nat.add(d, a), w)
      %srf.c1(w, d, t) : {List.length(&2, Nat, Su.keep.put(b, Nat.add(d, a), Su.keep(w, Su.older(d, t)))) == Supervise.restart_inside.put(b, _) : Nat}
      srf.len_put(b, Nat.add(d, a), Su.keep(w, Su.older(d, t)))

# d + (x + a) = (x + d) + a
def srf.e(+x: Nat, +d: Nat, +a: Nat) -> {Nat.add(d, Nat.add(x, a)) == Nat.add(Nat.add(x, d), a) : Nat}:
  Equal.trans(Nat, Nat.add(d, Nat.add(x, a)), Nat.add(x, Nat.add(d, a)), Nat.add(Nat.add(x, d), a), LNat.add_lcomm(d, x, a), LNat.add_assoc_r(x, d, a))

# x + a <= (x + d) + a
def srf.le_shift(+x: Nat, +d: Nat, +a: Nat) -> {Nat.is_le(Nat.add(x, a), Nat.add(Nat.add(x, d), a)) == True{} : Bool}:
  %srf.e(x, d, a) : {Nat.is_le(Nat.add(x, a), _) == True{} : Bool}
  LNat.supervisor.ps.le_add_l(d, Nat.add(x, a))

def srf.lt_false.at(b: Bool, +y: Nat, +z: Nat, +w: Nat, e: {Nat.is_lt(z, w) == b : Bool}, le: {Nat.is_le(y, z) == True{} : Bool}, f: {Nat.is_lt(y, w) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      +t = LNat.pc.le_lt_trans(y, z, w, le, e)
      Equal.trans(Bool, True{}, Nat.is_lt(y, w), False{}, Equal.sym(Bool, Nat.is_lt(y, w), True{}, t), f)
    case False{}:
      {==}

# an age y that reached the window: every z >= y has reached it too
def srf.lt_false(+y: Nat, +z: Nat, +w: Nat, le: {Nat.is_le(y, z) == True{} : Bool}, f: {Nat.is_lt(y, w) == False{} : Bool}) -> {Nat.is_lt(z, w) == False{} : Bool}:
  srf.lt_false.at(Nat.is_lt(z, w), y, z, w, {==}, le, f)

def srf.c2.at(b1: Bool, +w: Nat, +d: Nat, +x: Nat, +a: Nat, +t: List<&2, Nat>, e1: {Nat.is_lt(Nat.add(x, a), w) == b1 : Bool}, ih: {srf.cnt(w, d, Su.keep(w, Su.older(x, t))) == srf.cnt(w, Nat.add(x, d), t) : Nat})
  -> {srf.cnt(w, d, Su.keep.put(b1, Nat.add(x, a), Su.keep(w, Su.older(x, t)))) == Supervise.restart_inside.put(Nat.is_lt(Nat.add(Nat.add(x, d), a), w), srf.cnt(w, Nat.add(x, d), t)) : Nat}:
  match b1:
    case True{}:
      +kt = Su.keep(w, Su.older(x, t))
      +r = srf.cnt(w, Nat.add(x, d), t)
      %Equal.sym(Nat, srf.cnt(w, d, kt), r, ih) : {Supervise.restart_inside.put(Nat.is_lt(Nat.add(d, Nat.add(x, a)), w), _) == Supervise.restart_inside.put(Nat.is_lt(Nat.add(Nat.add(x, d), a), w), r) : Nat}
      %Equal.sym(Nat, Nat.add(d, Nat.add(x, a)), Nat.add(Nat.add(x, d), a), srf.e(x, d, a)) : {Supervise.restart_inside.put(Nat.is_lt(_, w), r) == Supervise.restart_inside.put(Nat.is_lt(Nat.add(Nat.add(x, d), a), w), r) : Nat}
      {==}
    case False{}:
      +kt = Su.keep(w, Su.older(x, t))
      +r = srf.cnt(w, Nat.add(x, d), t)
      %Equal.sym(Nat, srf.cnt(w, d, kt), r, ih) : {_ == Supervise.restart_inside.put(Nat.is_lt(Nat.add(Nat.add(x, d), a), w), r) : Nat}
      %Equal.sym(Bool, Nat.is_lt(Nat.add(Nat.add(x, d), a), w), False{}, srf.lt_false(Nat.add(x, a), Nat.add(Nat.add(x, d), a), w, srf.le_shift(x, d, a), e1)) : {r == Supervise.restart_inside.put(_, r) : Nat}
      {==}

# counting the ages kept by a step with gap x again d ms later counts the
# ages of A with (x + d) + a < w
def srf.c2(+w: Nat, +d: Nat, +x: Nat, A: List<&2, Nat>) -> {srf.cnt(w, d, Su.keep(w, Su.older(x, A))) == srf.cnt(w, Nat.add(x, d), A) : Nat}:
  match A:
    case Nil{}:
      {==}
    case +a <> +t:
      srf.c2.at(Nat.is_lt(Nat.add(x, a), w), w, d, x, a, t, {==}, srf.c2(w, d, x, t))

# r + put(b, c) = put(b, r) + c
def srf.swap(b: Bool, +r: Nat, +c: Nat) -> {Nat.add(r, Supervise.restart_inside.put(b, c)) == Nat.add(Supervise.restart_inside.put(b, r), c) : Nat}:
  match b:
    case True{}:
      LNat.add_succ(r, c)
    case False{}:
      {==}

def srf.succ(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  Equal.cong(Nat, Nat, z => 1n+z, a, b, e)

# after a failure x ms after the state with ages A, then the gaps t: the
# last failure, the earlier ones of t inside the window, and the ages of A
# still inside it
def srf.run(t: List<&2, Nat>, +c: Su.Cfg, +x: Nat, +A: List<&2, Nat>, +n: Nat) -> {Su.St.n(Su.go(c, x <> t, Su.St{A, n})) == 1n+Nat.add(Supervise.restart_inside(Su.Cfg.w(c), t), srf.cnt(Su.Cfg.w(c), Supervise.restart_sum(x <> t), A)) : Nat}:
  match t:
    case Nil{}:
      +w = Su.Cfg.w(c)
      +k = Su.keep(w, Su.older(x, A))
      %Equal.sym(Nat, Nat.add(x, 0n), x, LNat.add_zero(x)) : {1n+List.length(&2, Nat, k) == 1n+srf.cnt(w, _, A) : Nat}
      %srf.c1(w, x, A) : {1n+List.length(&2, Nat, k) == 1n+_ : Nat}
      {==}
    case +y <> +t2:
      +w = Su.Cfg.w(c)
      +k = Su.keep(w, Su.older(x, A))
      +d = Supervise.restart_sum(y <> t2)
      +i = Supervise.restart_inside(w, t2)
      +ih = srf.run(t2, c, y, 0n <> k, 1n+List.length(&2, Nat, k))
      %Equal.sym(Nat, Su.St.n(Su.go(c, y <> t2, Su.St{0n <> k, 1n+List.length(&2, Nat, k)})), 1n+Nat.add(i, srf.cnt(w, d, 0n <> k)), ih) : {_ == 1n+Nat.add(Supervise.restart_inside(w, y <> t2), srf.cnt(w, Nat.add(x, d), A)) : Nat}
      %Equal.sym(Nat, Nat.add(d, 0n), d, LNat.add_zero(d)) : {1n+Nat.add(i, Supervise.restart_inside.put(Nat.is_lt(_, w), srf.cnt(w, d, k))) == 1n+Nat.add(Supervise.restart_inside.put(Nat.is_lt(d, w), i), srf.cnt(w, Nat.add(x, d), A)) : Nat}
      %Equal.sym(Nat, srf.cnt(w, d, k), srf.cnt(w, Nat.add(x, d), A), srf.c2(w, d, x, A)) : {1n+Nat.add(i, Supervise.restart_inside.put(Nat.is_lt(d, w), _)) == 1n+Nat.add(Supervise.restart_inside.put(Nat.is_lt(d, w), i), srf.cnt(w, Nat.add(x, d), A)) : Nat}
      srf.succ(Nat.add(i, Supervise.restart_inside.put(Nat.is_lt(d, w), srf.cnt(w, Nat.add(x, d), A))), Nat.add(Supervise.restart_inside.put(Nat.is_lt(d, w), i), srf.cnt(w, Nat.add(x, d), A)), srf.swap(Nat.is_lt(d, w), i, srf.cnt(w, Nat.add(x, d), A)))

def Supervise.restart_failures_recent(c, gs):
  match gs:
    case Nil{}:
      {==}
    case +g0 <> rest:
      match rest:
        case Nil{}:
          {==}
        case +x <> +t:
          +w = Su.Cfg.w(c)
          +d = Supervise.restart_sum(x <> t)
          +i = Supervise.restart_inside(w, t)
          +b = Nat.is_lt(d, w)
          %Equal.sym(Nat, Su.St.n(Su.go(c, x <> t, Su.St{[0n], 1n})), 1n+Nat.add(i, srf.cnt(w, d, [0n])), srf.run(t, c, x, [0n], 1n)) : {_ == 1n+Supervise.restart_inside.put(b, i) : Nat}
          %Equal.sym(Nat, Nat.add(d, 0n), d, LNat.add_zero(d)) : {1n+Nat.add(i, Supervise.restart_inside.put(Nat.is_lt(_, w), 0n)) == 1n+Supervise.restart_inside.put(b, i) : Nat}
          srf.succ(Nat.add(i, Supervise.restart_inside.put(b, 0n)), Supervise.restart_inside.put(b, i), Equal.trans(Nat, Nat.add(i, Supervise.restart_inside.put(b, 0n)), Nat.add(Supervise.restart_inside.put(b, i), 0n), Supervise.restart_inside.put(b, i), srf.swap(b, i, 0n), LNat.add_zero(Supervise.restart_inside.put(b, i))))
