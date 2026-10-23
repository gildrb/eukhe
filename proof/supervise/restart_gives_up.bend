# eukhe: the proof of LAW restart_gives_up

import Base
import ../../bend/supervise.bend as Su
import ../../laws/supervise.bend as Supervise
import ../base.bend as L

def ps.le_lt(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n 0n:
      L.supervisor.ps.absurdF({Nat.is_lt(0n, 0n) == True{} : Bool}, bc)
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      L.supervisor.ps.absurdF({Nat.is_lt(0n, 0n) == True{} : Bool}, bc)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      L.supervisor.ps.absurdF({Nat.is_lt(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      L.supervisor.ps.absurdF({Nat.is_lt(1n+p, 0n) == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      ps.le_lt(p, q, r, ab, bc)

# k + 1 at most n makes k below n
def ps.lt_of_le_succ(k: Nat, n: Nat, h: {Nat.is_le(1n+k, n) == True{} : Bool}) -> {Nat.is_lt(k, n) == True{} : Bool}:
  match k n:
    case 0n 0n:
      L.supervisor.ps.absurdF({Nat.is_lt(0n, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      L.supervisor.ps.absurdF({Nat.is_lt(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      ps.lt_of_le_succ(p, q, h)

def ps.add_succ_r(a: Nat, +m: Nat) -> {Nat.add(a, 1n+m) == 1n+Nat.add(a, m) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %ps.add_succ_r(p, m) : {1n+Nat.add(p, 1n+m) == 1n+_ : Nat}
      {==}

def ps.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %ps.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

# (D1) restart_gives_up
# ---------------------

# the ages of A at most x
def ps.young.put(b: Bool, r: Nat) -> Nat:
  match b:
    case True{}:
      1n+r
    case False{}:
      r

def ps.young(+x: Nat, A: List<&2, Nat>) -> Nat:
  match A:
    case Nil{}:
      0n
    case +a <> t:
      ps.young.put(Nat.is_le(a, x), ps.young(x, t))

def ps.put_ge(b: Bool, +r: Nat) -> {Nat.is_le(r, ps.young.put(b, r)) == True{} : Bool}:
  match b:
    case True{}:
      L.supervisor.ps.le_succ(r)
    case False{}:
      L.supervisor.ps.le_refl(r)

def ps.young_len.put(b: Bool, +r: Nat, +l: Nat, h: {Nat.is_le(r, l) == True{} : Bool}) -> {Nat.is_le(ps.young.put(b, r), 1n+l) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      L.supervisor.ps.le_trans(r, l, 1n+l, h, L.supervisor.ps.le_succ(l))

def ps.young_len(+x: Nat, A: List<&2, Nat>) -> {Nat.is_le(ps.young(x, A), List.length(&2, Nat, A)) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case +a <> +t:
      ps.young_len.put(Nat.is_le(a, x), ps.young(x, t), List.length(&2, Nat, t), ps.young_len(x, t))

# the window keeps every young age g ms later: one age
def ps.keep.at(b1: Bool, +a: Nat, +x: Nat, +g: Nat, +w: Nat, e1: {Nat.is_le(a, x) == b1 : Bool}, b2: Bool, e2: {Nat.is_lt(Nat.add(g, a), w) == b2 : Bool}, lt: {Nat.is_lt(Nat.add(g, x), w) == True{} : Bool}, +y: Nat, +k: List<&2, Nat>, ih: {Nat.is_le(y, ps.young(Nat.add(g, x), k)) == True{} : Bool})
  -> {Nat.is_le(ps.young.put(b1, y), ps.young(Nat.add(g, x), Su.keep.put(b2, Nat.add(g, a), k))) == True{} : Bool}:
  match b1 b2:
    case True{} True{}:
      %Equal.sym(Bool, Nat.is_le(Nat.add(g, a), Nat.add(g, x)), True{}, L.ps.le_mono(g, a, x, e1)) : {Nat.is_le(1n+y, ps.young.put(_, ps.young(Nat.add(g, x), k))) == True{} : Bool}
      ih
    case True{} False{}:
      L.supervisor.ps.absurd({Nat.is_le(1n+y, ps.young(Nat.add(g, x), k)) == True{} : Bool}, Equal.trans(Bool, True{}, Nat.is_lt(Nat.add(g, a), w), False{}, Equal.sym(Bool, Nat.is_lt(Nat.add(g, a), w), True{}, ps.le_lt(Nat.add(g, a), Nat.add(g, x), w, L.ps.le_mono(g, a, x, e1), lt)), e2))
    case False{} True{}:
      L.supervisor.ps.le_trans(y, ps.young(Nat.add(g, x), k), ps.young.put(Nat.is_le(Nat.add(g, a), Nat.add(g, x)), ps.young(Nat.add(g, x), k)), ih, ps.put_ge(Nat.is_le(Nat.add(g, a), Nat.add(g, x)), ps.young(Nat.add(g, x), k)))
    case False{} False{}:
      ih

# the window keeps every young age g ms later
def ps.keep(+w: Nat, +g: Nat, +x: Nat, A: List<&2, Nat>, +lt: {Nat.is_lt(Nat.add(g, x), w) == True{} : Bool})
  -> {Nat.is_le(ps.young(x, A), ps.young(Nat.add(g, x), Su.keep(w, Su.older(g, A)))) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case +a <> +t:
      ps.keep.at(Nat.is_le(a, x), a, x, g, w, {==}, Nat.is_lt(Nat.add(g, a), w), {==}, lt, ps.young(x, t), Su.keep(w, Su.older(g, t)), ps.keep(w, g, x, t, lt))

# the span from c is at least c
def ps.span_ge(gs: List<&2, Nat>, +c: Nat) -> {Nat.is_le(c, Su.span.go(gs, c)) == True{} : Bool}:
  match gs:
    case Nil{}:
      L.supervisor.ps.le_refl(c)
    case +g <> +rest:
      L.supervisor.ps.le_trans(c, Nat.add(g, c), Su.span.go(rest, Nat.add(g, c)), L.supervisor.ps.le_add_l(g, c), ps.span_ge(rest, Nat.add(g, c)))

# a new failure is young
def ps.young_new(+z: Nat, +k: List<&2, Nat>) -> {ps.young(z, 0n <> k) == 1n+ps.young(z, k) : Nat}:
  %Equal.sym(Bool, Nat.is_le(0n, z), True{}, L.ps.le_zero(z)) : {ps.young.put(_, ps.young(z, k)) == 1n+ps.young(z, k) : Nat}
  {==}

def ps.block.yo(+z: Nat, +k: List<&2, Nat>, +m: Nat, kept: {Nat.is_le(m, ps.young(z, k)) == True{} : Bool}) -> {Nat.is_le(1n+m, ps.young(z, 0n <> k)) == True{} : Bool}:
  %Equal.sym(Nat, ps.young(z, 0n <> k), 1n+ps.young(z, k), ps.young_new(z, k)) : {Nat.is_le(1n+m, _) == True{} : Bool}
  kept

# from a state with m failures at most x ms old (and n at least m), the
# failures gs inside the window leave at least m + |gs| in the window
def ps.block(+c: Su.Cfg, gs: List<&2, Nat>, s: Su.St, +x: Nat, +m: Nat,
  yo: {Nat.is_le(m, ps.young(x, Su.St.ages(s))) == True{} : Bool},
  nm: {Nat.is_le(m, Su.St.n(s)) == True{} : Bool},
  +sp: {Nat.is_lt(Su.span.go(gs, x), Su.Cfg.w(c)) == True{} : Bool})
  -> {Nat.is_le(Nat.add(List.length(&2, Nat, gs), m), Su.St.n(Su.go(c, gs, s))) == True{} : Bool}:
  match gs:
    case Nil{}:
      nm
    case +g <> +rest:
      match s:
        case Su.St{+a, n}:
          +w = Su.Cfg.w(c)
          +z = Nat.add(g, x)
          +k = Su.kept(c, g, a)
          +lt = ps.le_lt(z, Su.span.go(rest, z), w, ps.span_ge(rest, z), sp)
          +kept = L.supervisor.ps.le_trans(m, ps.young(x, a), ps.young(z, k), yo, ps.keep(w, g, x, a, lt))
          +yo2 = ps.block.yo(z, k, m, kept)
          +nm2 = L.supervisor.ps.le_trans(m, ps.young(z, k), List.length(&2, Nat, k), kept, ps.young_len(z, k))
          %ps.add_succ_r(List.length(&2, Nat, rest), m) : {Nat.is_le(_, Su.St.n(Su.go(c, rest, Su.St{0n <> k, 1n+List.length(&2, Nat, k)}))) == True{} : Bool}
          ps.block(c, rest, Su.St{0n <> k, 1n+List.length(&2, Nat, k)}, z, 1n+m, yo2, nm2, sp)

# the first failure of the loop is young
def ps.first_young(+c: Su.Cfg, s: Su.St, +g: Nat) -> {Nat.is_le(1n, ps.young(0n, Su.St.ages(Su.step(c, s, g)))) == True{} : Bool}:
  match s:
    case Su.St{a, n}:
      L.ps.le_zero(ps.young(0n, Su.kept(c, g, a)))

# and counted
def ps.first_n(+c: Su.Cfg, s: Su.St, +g: Nat) -> {Nat.is_le(1n, Su.St.n(Su.step(c, s, g))) == True{} : Bool}:
  match s:
    case Su.St{a, n}:
      L.ps.le_zero(List.length(&2, Nat, Su.kept(c, g, a)))

def ps.go_append(+c: Su.Cfg, xs: List<&2, Nat>, +ys: List<&2, Nat>, s: Su.St) -> {Su.go(c, List.append(&2, Nat, xs, ys), s) == Su.go(c, ys, Su.go(c, xs, s)) : Su.St}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      ps.go_append(c, rest, ys, Su.step(c, s, x))

def ps.gives_up_of(+c: Su.Cfg, +n: Nat, lt: {Nat.is_lt(Su.Cfg.k(c), n) == True{} : Bool}) -> {Su.gives_up(Su.verdict(c, n)) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_lt(Su.Cfg.k(c), n), True{}, lt) : {Su.gives_up(Su.verdict.put(_, c, n)) == True{} : Bool}
  {==}

def ps.le_k(+l: Nat, +k: Nat, +n: Nat, many: {l == k : Nat}, blk: {Nat.is_le(Nat.add(l, 1n), n) == True{} : Bool}) -> {Nat.is_le(1n+k, n) == True{} : Bool}:
  %many : {Nat.is_le(1n+_, n) == True{} : Bool}
  %ps.add_zero(l) : {Nat.is_le(1n+_, n) == True{} : Bool}
  %ps.add_succ_r(l, 0n) : {Nat.is_le(_, n) == True{} : Bool}
  blk

def ps.restart_gives_up(+c: Su.Cfg, +pre: List<&2, Nat>, +g: Nat, +gs: List<&2, Nat>, many: {List.length(&2, Nat, gs) == Su.Cfg.k(c) : Nat}, fast: {Nat.is_lt(Su.span(gs), Su.Cfg.w(c)) == True{} : Bool})
  -> {Su.gives_up(Su.verdict(c, Su.failures(c, List.append(&2, Nat, pre, g <> gs)))) == True{} : Bool}:
  +s0 = Su.go(c, pre, Su.St.empty())
  +s1 = Su.step(c, s0, g)
  +blk = ps.block(c, gs, s1, 0n, 1n, ps.first_young(c, s0, g), ps.first_n(c, s0, g), fast)
  +n = Su.St.n(Su.go(c, gs, s1))
  +lt = ps.lt_of_le_succ(Su.Cfg.k(c), n, ps.le_k(List.length(&2, Nat, gs), Su.Cfg.k(c), n, many, blk))
  %Equal.sym(Su.St, Su.go(c, List.append(&2, Nat, pre, g <> gs), Su.St.empty()), Su.go(c, g <> gs, s0), ps.go_append(c, pre, g <> gs, Su.St.empty())) : {Su.gives_up(Su.verdict(c, Su.St.n(_))) == True{} : Bool}
  ps.gives_up_of(c, n, lt)

# (D1) Supervisor

def Supervise.restart_gives_up(c, pre, g, gs, many, fast):
  ps.restart_gives_up(c, pre, g, gs, many, fast)
