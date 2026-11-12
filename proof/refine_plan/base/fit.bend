# eukhe: lemmas of the refine_plan fit proofs: Nat facts, the code's
# budget test is R8's (rpf.fits), its middle is R8's (rpf.mid), its max
# tokens are R8's (rpf.room, rpf.no_room)

import Base
import ../../../bend/refine_plan.bend as Rp
import ../../../laws/refine_plan/walk.bend as RefinePlanWalk
import ./chars.bend as LCh

# Nat
# ---

def rpf.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 0n), p, rpf.add_zero(p))

def rpf.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 1n+b), 1n+Nat.add(p, b), rpf.add_succ(p, b))

def rpf.add_one(+n: Nat) -> {Nat.add(n, 1n) == 1n+n : Nat}:
  %rpf.add_zero(n) : {Nat.add(n, 1n) == 1n+_ : Nat}
  rpf.add_succ(n, 0n)

def rpf.eq(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n++q:
      LCh.absurdF({0n == 1n+q : Nat}, e)
    case 1n++p 0n:
      LCh.absurdF({1n+p == 0n : Nat}, e)
    case 1n++p 1n++q:
      Equal.cong(Nat, Nat, z => 1n+z, p, q, rpf.eq(p, q, e))

def rpf.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      rpf.le_refl(p)

def rpf.le_succ(n: Nat) -> {Nat.is_le(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      rpf.le_succ(p)

def rpf.le_trans(a: Nat, b: Nat, c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n b c:
      match c:
        case 0n:
          {==}
        case 1n++r:
          {==}
    case 1n++p 0n c:
      LCh.absurdF({Nat.is_le(1n+p, c) == True{} : Bool}, h1)
    case 1n++p 1n++q 0n:
      LCh.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, h2)
    case 1n++p 1n++q 1n++r:
      rpf.le_trans(p, q, r, h1, h2)

def rpf.min_le_r(a: Nat, b: Nat) -> {Nat.is_le(Nat.min(a, b), b) == True{} : Bool}:
  match a b:
    case 0n b:
      match b:
        case 0n:
          {==}
        case 1n++q:
          {==}
    case 1n++p 0n:
      {==}
    case 1n++p 1n++q:
      rpf.min_le_r(p, q)

def rpf.min_l(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.min(a, b) == a : Nat}:
  match a b:
    case 0n b:
      {==}
    case 1n++p 0n:
      LCh.absurdF({Nat.min(1n+p, 0n) == 1n+p : Nat}, h)
    case 1n++p 1n++q:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.min(p, q), p, rpf.min_l(p, q, h))

def rpf.min_r(a: Nat, b: Nat, h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.min(a, b) == b : Nat}:
  match a b:
    case 0n b:
      match b:
        case 0n:
          {==}
        case 1n++q:
          LCh.absurdF({Nat.min(0n, 1n+q) == 1n+q : Nat}, h)
    case 1n++p 0n:
      {==}
    case 1n++p 1n++q:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.min(p, q), q, rpf.min_r(p, q, h))

def rpf.min_zero(a: Nat) -> {Nat.min(a, 0n) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      {==}

# x + b within c: x within c
def rpf.mono(x: Nat, -b: Nat, c: Nat, h: {Nat.is_le(Nat.add(x, b), c) == True{} : Bool}) -> {Nat.is_le(x, c) == True{} : Bool}:
  match x c:
    case 0n c:
      match c:
        case 0n:
          {==}
        case 1n++r:
          {==}
    case 1n++p 0n:
      LCh.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, h)
    case 1n++p 1n++r:
      rpf.mono(p, b, r, h)

# x + m within c: m within c less x
def rpf.sub_le(x: Nat, c: Nat, +m: Nat, h: {Nat.is_le(Nat.add(x, m), c) == True{} : Bool}) -> {Nat.is_le(m, Nat.sub(c, x)) == True{} : Bool}:
  match x c:
    case 0n c:
      match c:
        case 0n:
          h
        case 1n++r:
          h
    case 1n++p 0n:
      LCh.absurdF({Nat.is_le(m, 0n) == True{} : Bool}, h)
    case 1n++p 1n++r:
      rpf.sub_le(p, r, m, h)

def rpf.sub_add(x: Nat, +m: Nat) -> {Nat.sub(Nat.add(x, m), x) == m : Nat}:
  match x:
    case 0n:
      match m:
        case 0n:
          {==}
        case 1n++q:
          {==}
    case 1n++p:
      rpf.sub_add(p, m)

# a within b: a less b is 0
def rpf.sub_zero(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.sub(a, b) == 0n : Nat}:
  match a b:
    case 0n b:
      {==}
    case 1n++p 0n:
      LCh.absurdF({Nat.sub(1n+p, 0n) == 0n : Nat}, h)
    case 1n++p 1n++q:
      rpf.sub_zero(p, q, h)

def rpf.or_assoc(p: Bool, -q: Bool, -r: Bool) -> {Bool.or(Bool.or(p, q), r) == Bool.or(p, Bool.or(q, r)) : Bool}:
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

def rpf.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def rpf.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      LCh.absurdF({b == True{} : Bool}, e)

# x within c less L (L within c): x + L within c
def rpf.le_sub(L: Nat, c: Nat, +x: Nat, h: {Nat.is_le(L, c) == True{} : Bool}) -> {Nat.is_le(x, Nat.sub(c, L)) == Nat.is_le(Nat.add(x, L), c) : Bool}:
  match L c:
    case 0n c:
      match c:
        case 0n:
          %Equal.sym(Nat, Nat.add(x, 0n), x, rpf.add_zero(x)) : {Nat.is_le(x, 0n) == Nat.is_le(_, 0n) : Bool}
          {==}
        case 1n++r:
          %Equal.sym(Nat, Nat.add(x, 0n), x, rpf.add_zero(x)) : {Nat.is_le(x, 1n+r) == Nat.is_le(_, 1n+r) : Bool}
          {==}
    case 1n++l 0n:
      LCh.absurdF({Nat.is_le(x, Nat.sub(0n, 1n+l)) == Nat.is_le(Nat.add(x, 1n+l), 0n) : Bool}, h)
    case 1n++l 1n++d:
      %Equal.sym(Nat, Nat.add(x, 1n+l), 1n+Nat.add(x, l), rpf.add_succ(x, l)) : {Nat.is_le(x, Nat.sub(d, l)) == Nat.is_le(_, 1n+d) : Bool}
      rpf.le_sub(l, d, x, h)

def rpf.or_zero_l.f(w: Bool, +x: Nat, +b: Nat, +c: Nat, ev: {Nat.is_le(x, c) == False{} : Bool}, ew: {Nat.is_le(Nat.add(x, b), c) == w : Bool}) -> {False{} == w : Bool}:
  match w:
    case False{}:
      {==}
    case True{}:
      LCh.absurd({False{} == True{} : Bool}, Equal.trans(Bool, True{}, Nat.is_le(x, c), False{}, Equal.sym(Bool, Nat.is_le(x, c), True{}, rpf.mono(x, b, c, ew)), ev))

# x + 0 within c, or x + b within c: x + 0 within c
def rpf.or_zero_l(v: Bool, +x: Nat, +b: Nat, +c: Nat, ev: {Nat.is_le(x, c) == v : Bool}) -> {v == Bool.or(v, Nat.is_le(Nat.add(x, b), c)) : Bool}:
  match v:
    case True{}:
      {==}
    case False{}:
      rpf.or_zero_l.f(Nat.is_le(Nat.add(x, b), c), x, b, c, ev, {==})


def rpf.or_zero_r.t(w: Bool) -> {True{} == Bool.or(w, True{}) : Bool}:
  match w:
    case True{}:
      {==}
    case False{}:
      {==}

# x + b within c, or x within c: x within c
def rpf.or_zero_r(v: Bool, +x: Nat, +b: Nat, +c: Nat, ev: {Nat.is_le(x, c) == v : Bool}) -> {v == Bool.or(Nat.is_le(Nat.add(x, b), c), v) : Bool}:
  match v:
    case True{}:
      rpf.or_zero_r.t(Nat.is_le(Nat.add(x, b), c))
    case False{}:
      %Equal.sym(Bool, Nat.is_le(Nat.add(x, b), c), False{}, Equal.sym(Bool, False{}, Nat.is_le(Nat.add(x, b), c), rpf.or_zero_l.f(Nat.is_le(Nat.add(x, b), c), x, b, c, ev, {==}))) : {False{} == Bool.or(_, False{}) : Bool}
      {==}

# x plus the least of a and b within c: x + a or x + b within c
def rpf.min_add(a: Nat, b: Nat, +x: Nat, +c: Nat) -> {Nat.is_le(Nat.add(x, Nat.min(a, b)), c) == Bool.or(Nat.is_le(Nat.add(x, a), c), Nat.is_le(Nat.add(x, b), c)) : Bool}:
  match a b:
    case 0n b:
      %Equal.sym(Nat, Nat.add(x, 0n), x, rpf.add_zero(x)) : {Nat.is_le(_, c) == Bool.or(Nat.is_le(_, c), Nat.is_le(Nat.add(x, b), c)) : Bool}
      rpf.or_zero_l(Nat.is_le(x, c), x, b, c, {==})
    case 1n++p 0n:
      %Equal.sym(Nat, Nat.add(x, 0n), x, rpf.add_zero(x)) : {Nat.is_le(_, c) == Bool.or(Nat.is_le(Nat.add(x, 1n+p), c), Nat.is_le(_, c)) : Bool}
      rpf.or_zero_r(Nat.is_le(x, c), x, 1n+p, c, {==})
    case 1n++p 1n++q:
      %Equal.sym(Nat, Nat.add(x, 1n+Nat.min(p, q)), 1n+Nat.add(x, Nat.min(p, q)), rpf.add_succ(x, Nat.min(p, q))) : {Nat.is_le(_, c) == Bool.or(Nat.is_le(Nat.add(x, 1n+p), c), Nat.is_le(Nat.add(x, 1n+q), c)) : Bool}
      %Equal.sym(Nat, Nat.add(x, 1n+p), 1n+Nat.add(x, p), rpf.add_succ(x, p)) : {Nat.is_le(1n+Nat.add(x, Nat.min(p, q)), c) == Bool.or(Nat.is_le(_, c), Nat.is_le(Nat.add(x, 1n+q), c)) : Bool}
      %Equal.sym(Nat, Nat.add(x, 1n+q), 1n+Nat.add(x, q), rpf.add_succ(x, q)) : {Nat.is_le(1n+Nat.add(x, Nat.min(p, q)), c) == Bool.or(Nat.is_le(1n+Nat.add(x, p), c), Nat.is_le(_, c)) : Bool}
      rpf.min_add(p, q, 1n+x, c)

# Halves
# ------

def rpf.dbl(m: Nat) -> Nat:
  match m:
    case 0n:
      0n
    case 1n++p:
      2n+rpf.dbl(p)

def rpf.add_dbl(m: Nat) -> {Nat.add(m, m) == rpf.dbl(m) : Nat}:
  match m:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), rpf.add_succ(p, p)) : {1n+_ == 2n+rpf.dbl(p) : Nat}
      Equal.cong(Nat, Nat, z => 2n+z, Nat.add(p, p), rpf.dbl(p), rpf.add_dbl(p))

def rpf.half_even(m: Nat, +d: Nat) -> {Nat.divmod.go(rpf.dbl(m), 1n, d, 0n) == (Nat.add(m, d), 0n) : Nat & Nat}:
  match m:
    case 0n:
      {==}
    case 1n++p:
      %rpf.add_succ(p, d) : {Nat.divmod.go(rpf.dbl(p), 1n, 1n+d, 0n) == (_, 0n) : Nat & Nat}
      rpf.half_even(p, 1n+d)

def rpf.half_odd(m: Nat, +d: Nat) -> {Nat.divmod.go(1n+rpf.dbl(m), 1n, d, 0n) == (Nat.add(m, d), 1n) : Nat & Nat}:
  match m:
    case 0n:
      {==}
    case 1n++p:
      %rpf.add_succ(p, d) : {Nat.divmod.go(1n+rpf.dbl(p), 1n, 1n+d, 0n) == (_, 1n) : Nat & Nat}
      rpf.half_odd(p, 1n+d)

def rpf.half_go(c: Nat, +d: Nat) -> {Nat.is_le(Pair.fst(Nat, Nat, Nat.divmod.go(c, 1n, d, 0n)), Nat.add(c, d)) == True{} : Bool}:
  match c:
    case 0n:
      rpf.le_refl(d)
    case 1n++p:
      match p:
        case 0n:
          rpf.le_succ(d)
        case 1n++q:
          +F = Pair.fst(Nat, Nat, Nat.divmod.go(q, 1n, 1n+d, 0n))
          +h = Equal.trans(Bool, Nat.is_le(F, 1n+Nat.add(q, d)), Nat.is_le(F, Nat.add(q, 1n+d)), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(F, z), 1n+Nat.add(q, d), Nat.add(q, 1n+d), Equal.sym(Nat, Nat.add(q, 1n+d), 1n+Nat.add(q, d), rpf.add_succ(q, d))), rpf.half_go(q, 1n+d))
          rpf.le_trans(F, 1n+Nat.add(q, d), 2n+Nat.add(q, d), h, rpf.le_succ(1n+Nat.add(q, d)))

# R8
# --

def rpf.half(+c: Nat) -> {Nat.is_le(Nat.div(c, 2n), c) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(Nat.div(c, 2n), c), Nat.is_le(Nat.div(c, 2n), Nat.add(c, 0n)), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(Nat.div(c, 2n), z), c, Nat.add(c, 0n), Equal.sym(Nat, Nat.add(c, 0n), c, rpf.add_zero(c))), rpf.half_go(c, 0n))

# the least of the max tokens, the output reserve and half the window is
# within the window
def rpf.least_le(+cw: Nat, +mx: Nat, +res: Nat) -> {Nat.is_le(Nat.min(Nat.min(mx, res), Nat.div(cw, 2n)), cw) == True{} : Bool}:
  rpf.le_trans(Nat.min(Nat.min(mx, res), Nat.div(cw, 2n)), Nat.div(cw, 2n), cw, rpf.min_le_r(Nat.min(mx, res), Nat.div(cw, 2n)), rpf.half(cw))

# the code's budget test is R8's: within the window with any one of the
# three
def rpf.fits(+cw: Nat, +mx: Nat, +res: Nat, +sys: Nat, +plen: Nat) -> {Nat.is_le(Nat.add(Nat.add(sys, 1024n), plen), Nat.sub(cw, Nat.min(Nat.min(mx, res), Nat.div(cw, 2n)))) == RefinePlanWalk.rs_fits(Rp.Win{cw, mx, res, sys}, plen) : Bool}:
  Equal.trans(Bool, Nat.is_le(Nat.add(Nat.add(sys, 1024n), plen), Nat.sub(cw, Nat.min(Nat.min(mx, res), Nat.div(cw, 2n)))), Nat.is_le(Nat.add(Nat.add(Nat.add(sys, 1024n), plen), Nat.min(Nat.min(mx, res), Nat.div(cw, 2n))), cw), RefinePlanWalk.rs_fits(Rp.Win{cw, mx, res, sys}, plen), rpf.le_sub(Nat.min(Nat.min(mx, res), Nat.div(cw, 2n)), cw, Nat.add(Nat.add(sys, 1024n), plen), rpf.least_le(cw, mx, res)), Equal.trans(Bool, Nat.is_le(Nat.add(Nat.add(Nat.add(sys, 1024n), plen), Nat.min(Nat.min(mx, res), Nat.div(cw, 2n))), cw), Bool.or(Nat.is_le(Nat.add(Nat.add(Nat.add(sys, 1024n), plen), Nat.min(mx, res)), cw), Nat.is_le(Nat.add(Nat.add(Nat.add(sys, 1024n), plen), Nat.div(cw, 2n)), cw)), RefinePlanWalk.rs_fits(Rp.Win{cw, mx, res, sys}, plen), rpf.min_add(Nat.min(mx, res), Nat.div(cw, 2n), Nat.add(Nat.add(sys, 1024n), plen), cw), Equal.trans(Bool, Bool.or(Nat.is_le(Nat.add(Nat.add(Nat.add(sys, 1024n), plen), Nat.min(mx, res)), cw), Nat.is_le(Nat.add(Nat.add(Nat.add(sys, 1024n), plen), Nat.div(cw, 2n)), cw)), Bool.or(Bool.or(Nat.is_le(Nat.add(Nat.add(Nat.add(sys, 1024n), plen), mx), cw), Nat.is_le(Nat.add(Nat.add(Nat.add(sys, 1024n), plen), res), cw)), Nat.is_le(Nat.add(Nat.add(Nat.add(sys, 1024n), plen), Nat.div(cw, 2n)), cw)), RefinePlanWalk.rs_fits(Rp.Win{cw, mx, res, sys}, plen), Equal.cong(Bool, Bool, z => Bool.or(z, Nat.is_le(Nat.add(Nat.add(Nat.add(sys, 1024n), plen), Nat.div(cw, 2n)), cw)), Nat.is_le(Nat.add(Nat.add(Nat.add(sys, 1024n), plen), Nat.min(mx, res)), cw), Bool.or(Nat.is_le(Nat.add(Nat.add(Nat.add(sys, 1024n), plen), mx), cw), Nat.is_le(Nat.add(Nat.add(Nat.add(sys, 1024n), plen), res), cw)), rpf.min_add(mx, res, Nat.add(Nat.add(sys, 1024n), plen), cw)), rpf.or_assoc(Nat.is_le(Nat.add(Nat.add(Nat.add(sys, 1024n), plen), mx), cw), Nat.is_le(Nat.add(Nat.add(Nat.add(sys, 1024n), plen), res), cw), Nat.is_le(Nat.add(Nat.add(Nat.add(sys, 1024n), plen), Nat.div(cw, 2n)), cw)))))

def rpf.mid.t(+lo: Nat, +hi: Nat, +m: Nat, e: {Nat.add(m, m) == Nat.add(lo, hi) : Nat}) -> {Nat.div(Nat.add(Nat.add(lo, hi), 1n), 2n) == m : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(lo, hi), 1n), 1n+Nat.add(lo, hi), rpf.add_one(Nat.add(lo, hi))) : {Nat.div(_, 2n) == m : Nat}
  %e : {Nat.div(1n+_, 2n) == m : Nat}
  %Equal.sym(Nat, Nat.add(m, m), rpf.dbl(m), rpf.add_dbl(m)) : {Nat.div(1n+_, 2n) == m : Nat}
  %Equal.sym(Nat & Nat, Nat.divmod.go(1n+rpf.dbl(m), 1n, 0n, 0n), (Nat.add(m, 0n), 1n), rpf.half_odd(m, 0n)) : {Pair.fst(Nat, Nat, _) == m : Nat}
  rpf.add_zero(m)

def rpf.mid.f(+lo: Nat, +hi: Nat, +m: Nat, e: {Nat.add(m, m) == 1n+Nat.add(lo, hi) : Nat}) -> {Nat.div(Nat.add(Nat.add(lo, hi), 1n), 2n) == m : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(lo, hi), 1n), 1n+Nat.add(lo, hi), rpf.add_one(Nat.add(lo, hi))) : {Nat.div(_, 2n) == m : Nat}
  %e : {Nat.div(_, 2n) == m : Nat}
  %Equal.sym(Nat, Nat.add(m, m), rpf.dbl(m), rpf.add_dbl(m)) : {Nat.div(_, 2n) == m : Nat}
  %Equal.sym(Nat & Nat, Nat.divmod.go(rpf.dbl(m), 1n, 0n, 0n), (Nat.add(m, 0n), 0n), rpf.half_even(m, 0n)) : {Pair.fst(Nat, Nat, _) == m : Nat}
  rpf.add_zero(m)

def rpf.mid.at(a: Bool, +lo: Nat, +hi: Nat, +m: Nat, ea: {Nat.is_eq(Nat.add(m, m), Nat.add(lo, hi)) == a : Bool}, h: {Bool.or(a, Nat.is_eq(Nat.add(m, m), 1n+Nat.add(lo, hi))) == True{} : Bool}) -> {Nat.div(Nat.add(Nat.add(lo, hi), 1n), 2n) == m : Nat}:
  match a:
    case True{}:
      rpf.mid.t(lo, hi, m, rpf.eq(Nat.add(m, m), Nat.add(lo, hi), ea))
    case False{}:
      rpf.mid.f(lo, hi, m, rpf.eq(Nat.add(m, m), 1n+Nat.add(lo, hi), h))

# the code's middle is R8's
def rpf.mid(+lo: Nat, +hi: Nat, +m: Nat, h: {RefinePlanWalk.rs_mid(lo, hi, m) == True{} : Bool}) -> {Nat.div(Nat.add(Nat.add(lo, hi), 1n), 2n) == m : Nat}:
  rpf.mid.at(Nat.is_eq(Nat.add(m, m), Nat.add(lo, hi)), lo, hi, m, {==}, h)

def rpf.room.at(v: Bool, +cw: Nat, +mx: Nat, +x: Nat, +m: Nat, ev: {Nat.is_eq(m, mx) == v : Bool}, le_mx: {Nat.is_le(m, mx) == True{} : Bool}, le_w: {Nat.is_le(Nat.add(x, m), cw) == True{} : Bool}, h: {Bool.or(v, Nat.is_eq(Nat.add(x, m), cw)) == True{} : Bool}) -> {Nat.min(mx, Nat.sub(cw, x)) == m : Nat}:
  match v:
    case True{}:
      %rpf.eq(m, mx, ev) : {Nat.min(_, Nat.sub(cw, x)) == m : Nat}
      rpf.min_l(m, Nat.sub(cw, x), rpf.sub_le(x, cw, m, le_w))
    case False{}:
      %rpf.eq(Nat.add(x, m), cw, h) : {Nat.min(mx, Nat.sub(_, x)) == m : Nat}
      %Equal.sym(Nat, Nat.sub(Nat.add(x, m), x), m, rpf.sub_add(x, m)) : {Nat.min(mx, _) == m : Nat}
      rpf.min_r(mx, m, le_mx)

def rpf.pos(m: Nat, h: {Nat.is_lt(0n, m) == True{} : Bool}) -> {Rp.fit.room(m) == Rp.TOk{m} : Rp.Step}:
  match m:
    case 0n:
      LCh.absurdF({Rp.fit.room(0n) == Rp.TOk{0n} : Rp.Step}, h)
    case 1n+p:
      {==}

# a final prompt with room: the code's max tokens are R8's
def rpf.room(+cw: Nat, +mx: Nat, +res: Nat, +sys: Nat, conv: Nat, +plen: Nat, +m: Nat, +ok: {RefinePlanWalk.rs_room(Rp.Win{cw, mx, res, sys}, plen, m) == True{} : Bool}) -> {Rp.fit(Rp.Win{cw, mx, res, sys}, conv, Rp.SFinal{}, plen) == Rp.TOk{m} : Rp.Step}:
  +x = Nat.add(Nat.add(sys, 1024n), plen)
  +A = Nat.is_lt(0n, m)
  +B = Nat.is_le(m, mx)
  +C = Nat.is_le(Nat.add(x, m), cw)
  +D = Bool.or(Nat.is_eq(m, mx), Nat.is_eq(Nat.add(x, m), cw))
  +r1 = rpf.and_r(A, Bool.and(B, Bool.and(C, D)), ok)
  +r2 = rpf.and_r(B, Bool.and(C, D), r1)
  %Equal.sym(Nat, Nat.min(mx, Nat.sub(cw, x)), m, rpf.room.at(Nat.is_eq(m, mx), cw, mx, x, m, {==}, rpf.and_l(B, Bool.and(C, D), r1), rpf.and_l(C, D, r2), rpf.and_r(C, D, r2))) : {Rp.fit.room(_) == Rp.TOk{m} : Rp.Step}
  rpf.pos(m, rpf.and_l(A, Bool.and(B, Bool.and(C, D)), ok))

def rpf.no_room.at(a: Bool, +cw: Nat, +mx: Nat, +x: Nat, ea: {Nat.is_eq(mx, 0n) == a : Bool}, h: {Bool.or(a, Nat.is_le(cw, x)) == True{} : Bool}) -> {Nat.min(mx, Nat.sub(cw, x)) == 0n : Nat}:
  match a:
    case True{}:
      %Equal.sym(Nat, mx, 0n, rpf.eq(mx, 0n, ea)) : {Nat.min(_, Nat.sub(cw, x)) == 0n : Nat}
      {==}
    case False{}:
      %Equal.sym(Nat, Nat.sub(cw, x), 0n, rpf.sub_zero(cw, x, h)) : {Nat.min(mx, _) == 0n : Nat}
      rpf.min_zero(mx)

# a final prompt without room: the code refuses
def rpf.no_room(+cw: Nat, +mx: Nat, +res: Nat, +sys: Nat, conv: Nat, +plen: Nat, no: {RefinePlanWalk.rs_no_room(Rp.Win{cw, mx, res, sys}, plen) == True{} : Bool}) -> {Rp.fit(Rp.Win{cw, mx, res, sys}, conv, Rp.SFinal{}, plen) == Rp.TNo{"Refinement prompt leaves no room for output in the model's context window; retry with a smaller request."} : Rp.Step}:
  %Equal.sym(Nat, Nat.min(mx, Nat.sub(cw, Nat.add(Nat.add(sys, 1024n), plen))), 0n, rpf.no_room.at(Nat.is_eq(mx, 0n), cw, mx, Nat.add(Nat.add(sys, 1024n), plen), {==}, no)) : {Rp.fit.room(_) == Rp.TNo{"Refinement prompt leaves no room for output in the model's context window; retry with a smaller request."} : Rp.Step}
  {==}

# a conversation that is not empty: its length is above 0
def rpf.some(conv: Nat, h: {Nat.is_eq(conv, 0n) == False{} : Bool}) -> {Nat.is_lt(0n, conv) == True{} : Bool}:
  match conv:
    case 0n:
      LCh.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, h)
    case 1n+p:
      {==}
