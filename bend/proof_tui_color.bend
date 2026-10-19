# proof_tui_color: the T3 laws (docs/interface.md "Terminal colors") of
# the model in bend/tui_color.bend.
#
# The division takes n off x while n fits, so n times the quotient is at
# most x, and every q with n * q at most x is at most the quotient. So
# adding d to x never lowers the quotient, and raises it when d is at
# least n. A rung moves each channel from the last rung by such a step:
# the rising channels count the weight up, the falling ones count it
# down. So every channel moves toward the high end, and the widest
# channel, at least n wide, moves at each rung: a rung differs from all
# the rungs after it. A band is reached when w * num <= t * den; more
# tokens keep it reached, and a factor 1 + k on both t and w cancels.

import Base
import ./tui_color.bend as TC
import ./theme.bend as T
import ./color.bend as Co
import ./effort.bend as Ef
import ./proof_themes.bend as TP

# Logic
# -----

def pu.BD(+b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pu.absurd_ft(-A: Type, +e: {False{} == True{} : Bool}) -> A:
  %e : pu.BD(_, A, Unit)
  Unit{}

def pu.absurd_tf(-A: Type, +e: {True{} == False{} : Bool}) -> A:
  %e : pu.BD(_, Unit, A)
  Unit{}

def pu.and_t(+a: Bool, +b: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def pu.and_l(+a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      pu.absurd_ft({False{} == True{} : Bool}, h)

def pu.and_r(+a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      pu.absurd_ft({b == True{} : Bool}, h)

# Numbers
# -------

def pu.le_zero(+n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pu.le_refl(+n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pu.le_refl(p)

def pu.le_trans(+a: Nat, +b: Nat, +c: Nat, +ab: {Nat.is_le(a, b) == True{} : Bool}, +bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n q r:
      pu.le_zero(r)
    case 1n+p 0n r:
      pu.absurd_ft({Nat.is_le(1n+p, r) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      pu.absurd_ft({False{} == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      pu.le_trans(p, q, r, ab, bc)

def pu.le_succ_r(+a: Nat, +b: Nat, +e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n q:
      {==}
    case 1n+p 0n:
      pu.absurd_ft({Nat.is_le(1n+p, 1n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pu.le_succ_r(p, q, e)

def pu.lt_le(+a: Nat, +b: Nat, +e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n q:
      pu.le_zero(q)
    case 1n+p 0n:
      pu.absurd_ft({Nat.is_le(1n+p, 0n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pu.lt_le(p, q, e)

def pu.lt_of_le_succ(+a: Nat, +b: Nat, +e: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case p 0n:
      pu.absurd_ft({Nat.is_lt(p, 0n) == True{} : Bool}, e)
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      pu.lt_of_le_succ(p, q, e)

def pu.lt_zero_f(+q: Nat) -> {False{} == Nat.is_lt(q, 0n) : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pu.le_lt_trans(+a: Nat, +b: Nat, +c: Nat, +ab: {Nat.is_le(a, b) == True{} : Bool}, +bc: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case p q 0n:
      pu.absurd_ft({Nat.is_lt(p, 0n) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(q, 0n), True{}, pu.lt_zero_f(q), bc))
    case 0n q 1n+r:
      {==}
    case 1n+p 0n 1n+r:
      pu.absurd_ft({Nat.is_lt(1n+p, 1n+r) == True{} : Bool}, ab)
    case 1n+p 1n+q 1n+r:
      pu.le_lt_trans(p, q, r, ab, bc)

def pu.lt_ne(+a: Nat, +b: Nat, +e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      pu.absurd_ft({True{} == False{} : Bool}, e)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pu.lt_ne(p, q, e)

def pu.gt_ne(+a: Nat, +b: Nat, +e: {Nat.is_lt(b, a) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      pu.absurd_ft({True{} == False{} : Bool}, e)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pu.gt_ne(p, q, e)

# m <= n + m
def pu.le_add(+n: Nat, +m: Nat) -> {Nat.is_le(m, Nat.add(n, m)) == True{} : Bool}:
  match n:
    case 0n:
      pu.le_refl(m)
    case 1n+p:
      +q = p
      pu.le_succ_r(m, Nat.add(q, m), pu.le_add(q, m))

# a <= a + c
def pu.le_add_r(+a: Nat, +c: Nat) -> {Nat.is_le(a, Nat.add(a, c)) == True{} : Bool}:
  match a:
    case 0n:
      pu.le_zero(c)
    case 1n+p:
      pu.le_add_r(p, c)

def pu.le_add_l(+c: Nat, -x: Nat, -y: Nat, +e: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(Nat.add(c, x), Nat.add(c, y)) == True{} : Bool}:
  match c:
    case 0n:
      e
    case 1n+p:
      pu.le_add_l(p, x, y, e)

def pu.lt_add_l(+c: Nat, -x: Nat, -y: Nat, +e: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(Nat.add(c, x), Nat.add(c, y)) == True{} : Bool}:
  match c:
    case 0n:
      e
    case 1n+p:
      pu.lt_add_l(p, x, y, e)

def pu.le_add_mono_r(+a: Nat, +b: Nat, +d: Nat, +e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, d), Nat.add(b, d)) == True{} : Bool}:
  match a b:
    case 0n q:
      pu.le_add(q, d)
    case 1n+p 0n:
      pu.absurd_ft({Nat.is_le(Nat.add(1n+p, d), Nat.add(0n, d)) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pu.le_add_mono_r(p, q, d, e)

def pu.le_add_both(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +ab: {Nat.is_le(a, b) == True{} : Bool}, +cd: {Nat.is_le(c, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}:
  pu.le_trans(Nat.add(a, c), Nat.add(a, d), Nat.add(b, d), pu.le_add_l(a, c, d, cd), pu.le_add_mono_r(a, b, d, ab))

# n + (x - n) = x when n <= x
def pu.sub_add(+n: Nat, +x: Nat, +e: {Nat.is_le(n, x) == True{} : Bool}) -> {Nat.add(n, Nat.sub(x, n)) == x : Nat}:
  match n x:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      pu.absurd_ft({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, e)
    case 1n+p 1n+q:
      %pu.sub_add(p, q, e) : {1n+Nat.add(p, Nat.sub(q, p)) == 1n+_ : Nat}
      {==}

# z <= x - n when n + z <= x
def pu.le_sub(+n: Nat, +z: Nat, +x: Nat, +e: {Nat.is_le(Nat.add(n, z), x) == True{} : Bool}) -> {Nat.is_le(z, Nat.sub(x, n)) == True{} : Bool}:
  match n x:
    case 0n 0n:
      e
    case 0n 1n+q:
      e
    case 1n+p 0n:
      pu.absurd_ft({Nat.is_le(z, Nat.sub(0n, 1n+p)) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pu.le_sub(p, z, q, e)

def pu.le_add_left(+n: Nat, +z: Nat, +x: Nat, +e: {Nat.is_le(Nat.add(n, z), x) == True{} : Bool}) -> {Nat.is_le(n, x) == True{} : Bool}:
  pu.le_trans(n, Nat.add(n, z), x, pu.le_add_r(n, z), e)

def pu.sub_le_self(+x: Nat, +n: Nat) -> {Nat.is_le(Nat.sub(x, n), x) == True{} : Bool}:
  match x n:
    case 0n q:
      {==}
    case 1n+p 0n:
      pu.le_refl(1n+p)
    case 1n+p 1n+q:
      pu.le_succ_r(Nat.sub(p, q), p, pu.sub_le_self(p, q))

# x - n <= f when x <= 1 + f and n >= 1
def pu.sub_fuel(+x: Nat, +f: Nat, +n: Nat, +ex: {Nat.is_le(x, 1n+f) == True{} : Bool}, +en: {Nat.is_le(1n, n) == True{} : Bool}) -> {Nat.is_le(Nat.sub(x, n), f) == True{} : Bool}:
  match x n:
    case p 0n:
      pu.absurd_ft({Nat.is_le(Nat.sub(p, 0n), f) == True{} : Bool}, en)
    case 0n 1n+q:
      pu.le_zero(f)
    case 1n+p 1n+q:
      pu.le_trans(Nat.sub(p, q), p, f, pu.sub_le_self(p, q), ex)

# Division
# --------

# n times the quotient is at most x
def pu.dv_low(+fuel: Nat, +ok: Bool, +x: Nat, +n: Nat, +eo: {Nat.is_le(n, x) == ok : Bool}) -> {Nat.is_le(Nat.mul(TC.dv.go(fuel, ok, x, n), n), x) == True{} : Bool}:
  match fuel:
    case 0n:
      pu.le_zero(x)
    case 1n+f:
      match ok:
        case True{}:
          +y = Nat.sub(x, n)
          +q = TC.dv.go(f, Nat.is_le(n, y), y, n)
          +ih = pu.dv_low(f, Nat.is_le(n, y), y, n, {==})
          %pu.sub_add(n, x, eo) : {Nat.is_le(Nat.add(n, Nat.mul(q, n)), _) == True{} : Bool}
          pu.le_add_l(n, Nat.mul(q, n), y, ih)
        case False{}:
          pu.le_zero(x)

# a q with n * q at most x is at most the quotient (n >= 1, x <= fuel)
def pu.dv_max(+fuel: Nat, +ok: Bool, +x: Nat, +n: Nat, +q: Nat, +eo: {Nat.is_le(n, x) == ok : Bool}, +ef: {Nat.is_le(x, fuel) == True{} : Bool}, +en: {Nat.is_le(1n, n) == True{} : Bool}, +eq: {Nat.is_le(Nat.mul(q, n), x) == True{} : Bool}) -> {Nat.is_le(q, TC.dv.go(fuel, ok, x, n)) == True{} : Bool}:
  match fuel:
    case 0n:
      match n:
        case 0n:
          match q:
            case 0n:
              {==}
            case 1n+r:
              pu.absurd_ft({Nat.is_le(1n+r, 0n) == True{} : Bool}, en)
        case 1n+m:
          match q:
            case 0n:
              {==}
            case 1n+r:
              pu.absurd_ft({Nat.is_le(1n+r, 0n) == True{} : Bool}, pu.le_trans(Nat.mul(1n+r, 1n+m), x, 0n, eq, ef))
    case 1n+f:
      match ok:
        case True{}:
          match q:
            case 0n:
              {==}
            case 1n+r:
              +y = Nat.sub(x, n)
              pu.dv_max(f, Nat.is_le(n, y), y, n, r, {==}, pu.sub_fuel(x, f, n, ef, en), en, pu.le_sub(n, Nat.mul(r, n), x, eq))
        case False{}:
          match q:
            case 0n:
              {==}
            case 1n+r:
              +fits = pu.le_add_left(n, Nat.mul(r, n), x, eq)
              pu.absurd_tf({Nat.is_le(1n+r, 0n) == True{} : Bool}, Equal.trans(Bool, True{}, Nat.is_le(n, x), False{}, Equal.sym(Bool, Nat.is_le(n, x), True{}, fits), eo))

# adding d never lowers the quotient
def pu.dv_le_add(+x: Nat, +d: Nat, +n: Nat, +en: {Nat.is_le(1n, n) == True{} : Bool}) -> {Nat.is_le(TC.dv(x, n), TC.dv(Nat.add(d, x), n)) == True{} : Bool}:
  +y = Nat.add(d, x)
  +q = TC.dv(x, n)
  +low = pu.le_trans(Nat.mul(q, n), x, y, pu.dv_low(x, Nat.is_le(n, x), x, n, {==}), pu.le_add(d, x))
  pu.dv_max(y, Nat.is_le(n, y), y, n, q, {==}, pu.le_refl(y), en, low)

# adding d >= n raises the quotient
def pu.dv_lt_add(+x: Nat, +d: Nat, +n: Nat, +en: {Nat.is_le(1n, n) == True{} : Bool}, +ed: {Nat.is_le(n, d) == True{} : Bool}) -> {Nat.is_lt(TC.dv(x, n), TC.dv(Nat.add(d, x), n)) == True{} : Bool}:
  +y = Nat.add(d, x)
  +q = TC.dv(x, n)
  +low = pu.le_add_both(n, d, Nat.mul(q, n), x, ed, pu.dv_low(x, Nat.is_le(n, x), x, n, {==}))
  pu.lt_of_le_succ(q, TC.dv(y, n), pu.dv_max(y, Nat.is_le(n, y), y, n, 1n+q, {==}, pu.le_refl(y), en, low))

# The effort ramp
# ---------------

# a channel never goes back from rung k to rung k + 1
def pu.chan_le(+u: Bool, +a: Nat, +b: Nat, +k: Nat, +l: Nat, +n: Nat, +en: {Nat.is_le(1n, n) == True{} : Bool})
  -> {TC.step.pick(u, TC.chan.pick(u, a, b, k, 1n+l, n), TC.chan.pick(u, a, b, 1n+k, l, n)) == True{} : Bool}:
  match u:
    case True{}:
      +d = Nat.sub(b, a)
      pu.le_add_l(a, TC.dv(Nat.mul(k, d), n), TC.dv(Nat.add(d, Nat.mul(k, d)), n), pu.dv_le_add(Nat.mul(k, d), d, n, en))
    case False{}:
      +d = Nat.sub(a, b)
      pu.le_add_l(b, TC.dv(Nat.mul(l, d), n), TC.dv(Nat.add(d, Nat.mul(l, d)), n), pu.dv_le_add(Nat.mul(l, d), d, n, en))

# x is strictly beyond y toward the high end
def pu.rel(u: Bool, +x: Nat, +y: Nat) -> Bool:
  match u:
    case True{}:
      Nat.is_lt(x, y)
    case False{}:
      Nat.is_lt(y, x)

# a channel at least n wide moves from rung k to rung k + 1
def pu.chan_lt(+u: Bool, +a: Nat, +b: Nat, +k: Nat, +l: Nat, +n: Nat, +en: {Nat.is_le(1n, n) == True{} : Bool}, +ed: {Nat.is_le(n, TC.gap.pick(u, a, b)) == True{} : Bool})
  -> {pu.rel(u, TC.chan.pick(u, a, b, k, 1n+l, n), TC.chan.pick(u, a, b, 1n+k, l, n)) == True{} : Bool}:
  match u:
    case True{}:
      +d = Nat.sub(b, a)
      pu.lt_add_l(a, TC.dv(Nat.mul(k, d), n), TC.dv(Nat.add(d, Nat.mul(k, d)), n), pu.dv_lt_add(Nat.mul(k, d), d, n, en, ed))
    case False{}:
      +d = Nat.sub(a, b)
      pu.lt_add_l(b, TC.dv(Nat.mul(l, d), n), TC.dv(Nat.add(d, Nat.mul(l, d)), n), pu.dv_lt_add(Nat.mul(l, d), d, n, en, ed))

# the rungs after rung done move every channel on from it
def pu.ordered_go(+left: Nat, +done: Nat, +lr: Nat, +lg: Nat, +lb: Nat, +hr: Nat, +hg: Nat, +hb: Nat, +n: Nat, +en: {Nat.is_le(1n, n) == True{} : Bool})
  -> {TC.ordered.from(TC.ramp.go(left, done, TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n), TC.rung(TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, done, left, n), TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}) == True{} : Bool}:
  match left:
    case 0n:
      {==}
    case 1n+l:
      +sr = pu.chan_le(Nat.is_le(lr, hr), lr, hr, done, l, n, en)
      +sg = pu.chan_le(Nat.is_le(lg, hg), lg, hg, done, l, n, en)
      +sb = pu.chan_le(Nat.is_le(lb, hb), lb, hb, done, l, n, en)
      +here = pu.and_t(TC.step(lr, hr, TC.chan(lr, hr, done, 1n+l, n), TC.chan(lr, hr, 1n+done, l, n)), Bool.and(TC.step(lg, hg, TC.chan(lg, hg, done, 1n+l, n), TC.chan(lg, hg, 1n+done, l, n)), TC.step(lb, hb, TC.chan(lb, hb, done, 1n+l, n), TC.chan(lb, hb, 1n+done, l, n))), sr, pu.and_t(TC.step(lg, hg, TC.chan(lg, hg, done, 1n+l, n), TC.chan(lg, hg, 1n+done, l, n)), TC.step(lb, hb, TC.chan(lb, hb, done, 1n+l, n), TC.chan(lb, hb, 1n+done, l, n)), sg, sb))
      +more = pu.ordered_go(l, 1n+done, lr, lg, lb, hr, hg, hb, n, en)
      pu.and_t(TC.moves(TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, TC.rung(TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, done, 1n+l, n), TC.rung(TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, 1n+done, l, n)), TC.ordered.from(TC.ramp.go(l, 1n+done, TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n), TC.rung(TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, 1n+done, l, n), TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}), here, more)

def tui_effort_ramp_ordered(+lo: TC.Px, +hi: TC.Px, +n: Nat) -> {TC.ordered(lo, hi, TC.ramp(lo, hi, n)) == True{} : Bool}:
  match lo hi n:
    case TC.Px{lr, lg, lb} TC.Px{hr, hg, hb} 0n:
      {==}
    case TC.Px{lr, lg, lb} TC.Px{hr, hg, hb} 1n+m:
      pu.ordered_go(m, 1n, lr, lg, lb, hr, hg, hb, 1n+m, pu.le_zero(m))

def pu.length_go(+left: Nat, +done: Nat, +lo: TC.Px, +hi: TC.Px, +n: Nat) -> {List.length(&2, TC.Px, TC.ramp.go(left, done, lo, hi, n)) == left : Nat}:
  match left:
    case 0n:
      {==}
    case 1n+l:
      %pu.length_go(l, 1n+done, lo, hi, n) : {1n+List.length(&2, TC.Px, TC.ramp.go(l, 1n+done, lo, hi, n)) == 1n+_ : Nat}
      {==}

def tui_effort_ramp_length(+lo: TC.Px, +hi: TC.Px, +n: Nat) -> {List.length(&2, TC.Px, TC.ramp(lo, hi, n)) == n : Nat}:
  pu.length_go(n, 0n, lo, hi, n)

type pu.Ch is Data:
  ChR{}
  ChG{}
  ChB{}

def pu.ch(c: pu.Ch, p: TC.Px) -> Nat:
  match c:
    case ChR{}:
      match p:
        case TC.Px{r, g, b}:
          r
    case ChG{}:
      match p:
        case TC.Px{r, g, b}:
          g
    case ChB{}:
      match p:
        case TC.Px{r, g, b}:
          b

# channel c of a rung is the ramp of channel c
def pu.rung_ch(+c: pu.Ch, +lr: Nat, +lg: Nat, +lb: Nat, +hr: Nat, +hg: Nat, +hb: Nat, +wu: Nat, +wd: Nat, +n: Nat)
  -> {TC.chan(pu.ch(c, TC.Px{lr, lg, lb}), pu.ch(c, TC.Px{hr, hg, hb}), wu, wd, n) == pu.ch(c, TC.rung(TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, wu, wd, n)) : Nat}:
  match c:
    case ChR{}:
      {==}
    case ChG{}:
      {==}
    case ChB{}:
      {==}

def pu.not_and_f(+a: Bool) -> {Bool.not(Bool.and(a, False{})) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pu.not_and2_f(+a: Bool, +b: Bool) -> {Bool.not(Bool.and(a, Bool.and(b, False{}))) == True{} : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} y:
      {==}

# two colors that differ in one channel differ
def pu.ne_px(+c: pu.Ch, +x: TC.Px, +y: TC.Px, +h: {Nat.is_eq(pu.ch(c, x), pu.ch(c, y)) == False{} : Bool}) -> {Bool.not(TC.px.eq(x, y)) == True{} : Bool}:
  match c x y:
    case ChR{} TC.Px{xr, xg, xb} TC.Px{yr, yg, yb}:
      %Equal.sym(Bool, Nat.is_eq(xr, yr), False{}, h) : {Bool.not(Bool.and(_, Bool.and(Nat.is_eq(xg, yg), Nat.is_eq(xb, yb)))) == True{} : Bool}
      {==}
    case ChG{} TC.Px{xr, xg, xb} TC.Px{yr, yg, yb}:
      %Equal.sym(Bool, Nat.is_eq(xg, yg), False{}, h) : {Bool.not(Bool.and(Nat.is_eq(xr, yr), Bool.and(_, Nat.is_eq(xb, yb)))) == True{} : Bool}
      pu.not_and_f(Nat.is_eq(xr, yr))
    case ChB{} TC.Px{xr, xg, xb} TC.Px{yr, yg, yb}:
      %Equal.sym(Bool, Nat.is_eq(xb, yb), False{}, h) : {Bool.not(Bool.and(Nat.is_eq(xr, yr), Bool.and(Nat.is_eq(xg, yg), _))) == True{} : Bool}
      pu.not_and2_f(Nat.is_eq(xr, yr), Nat.is_eq(xg, yg))

def pu.le_succ_of_lt(+a: Nat, +b: Nat, +e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a b:
    case p 0n:
      pu.absurd_ft({Nat.is_le(1n+p, 0n) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(p, 0n), True{}, pu.lt_zero_f(p), e))
    case 0n 1n+q:
      pu.le_zero(q)
    case 1n+p 1n+q:
      pu.le_succ_of_lt(p, q, e)

def pu.lt_le_trans(+a: Nat, +b: Nat, +c: Nat, +ab: {Nat.is_lt(a, b) == True{} : Bool}, +bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  pu.lt_of_le_succ(a, c, pu.le_trans(1n+a, b, c, pu.le_succ_of_lt(a, b, ab), bc))

def pu.rel_trans(+u: Bool, +p: Nat, +q: Nat, +r: Nat, +h1: {TC.step.pick(u, p, q) == True{} : Bool}, +h2: {pu.rel(u, q, r) == True{} : Bool}) -> {pu.rel(u, p, r) == True{} : Bool}:
  match u:
    case True{}:
      pu.le_lt_trans(p, q, r, h1, h2)
    case False{}:
      pu.lt_le_trans(r, q, p, h2, h1)

def pu.rel_ne(+u: Bool, +p: Nat, +r: Nat, +h: {pu.rel(u, p, r) == True{} : Bool}) -> {Nat.is_eq(p, r) == False{} : Bool}:
  match u:
    case True{}:
      pu.lt_ne(p, r, h)
    case False{}:
      pu.gt_ne(p, r, h)

def pu.rel_step(+u: Bool, +p: Nat, +r: Nat, +h: {pu.rel(u, p, r) == True{} : Bool}) -> {TC.step.pick(u, p, r) == True{} : Bool}:
  match u:
    case True{}:
      pu.lt_le(p, r, h)
    case False{}:
      pu.lt_le(r, p, h)

def pu.step_refl(+u: Bool, +p: Nat) -> {TC.step.pick(u, p, p) == True{} : Bool}:
  match u:
    case True{}:
      pu.le_refl(p)
    case False{}:
      pu.le_refl(p)

# a color at or behind rung done in a channel at least n wide is none of
# the rungs after it
def pu.notin_go(+c: pu.Ch, +left: Nat, +done: Nat, +lr: Nat, +lg: Nat, +lb: Nat, +hr: Nat, +hg: Nat, +hb: Nat, +n: Nat, +x: TC.Px, +en: {Nat.is_le(1n, n) == True{} : Bool}, +ed: {Nat.is_le(n, TC.gap(pu.ch(c, TC.Px{lr, lg, lb}), pu.ch(c, TC.Px{hr, hg, hb}))) == True{} : Bool}, +h: {TC.step(pu.ch(c, TC.Px{lr, lg, lb}), pu.ch(c, TC.Px{hr, hg, hb}), pu.ch(c, x), TC.chan(pu.ch(c, TC.Px{lr, lg, lb}), pu.ch(c, TC.Px{hr, hg, hb}), done, left, n)) == True{} : Bool})
  -> {TC.notin(x, TC.ramp.go(left, done, TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n)) == True{} : Bool}:
  match left:
    case 0n:
      {==}
    case 1n+l:
      +a = pu.ch(c, TC.Px{lr, lg, lb})
      +b = pu.ch(c, TC.Px{hr, hg, hb})
      +u = Nat.is_le(a, b)
      +y = TC.rung(TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, 1n+done, l, n)
      +next = TC.chan(a, b, 1n+done, l, n)
      +moved = pu.rel_trans(u, pu.ch(c, x), TC.chan(a, b, done, 1n+l, n), next, h, pu.chan_lt(u, a, b, done, l, n, en, ed))
      +ne = pu.rel_ne(u, pu.ch(c, x), next, moved)
      +ney = {%pu.rung_ch(c, lr, lg, lb, hr, hg, hb, 1n+done, l, n) : {Nat.is_eq(pu.ch(c, x), _) == False{} : Bool}; ne : {Nat.is_eq(pu.ch(c, x), pu.ch(c, y)) == False{} : Bool}}
      +more = pu.notin_go(c, l, 1n+done, lr, lg, lb, hr, hg, hb, n, x, en, ed, pu.rel_step(u, pu.ch(c, x), next, moved))
      pu.and_t(Bool.not(TC.px.eq(x, y)), TC.notin(x, TC.ramp.go(l, 1n+done, TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n)), pu.ne_px(c, x, y, ney), more)

# the rungs after rung done are distinct in a channel at least n wide
def pu.distinct_go(+c: pu.Ch, +left: Nat, +done: Nat, +lr: Nat, +lg: Nat, +lb: Nat, +hr: Nat, +hg: Nat, +hb: Nat, +n: Nat, +en: {Nat.is_le(1n, n) == True{} : Bool}, +ed: {Nat.is_le(n, TC.gap(pu.ch(c, TC.Px{lr, lg, lb}), pu.ch(c, TC.Px{hr, hg, hb}))) == True{} : Bool})
  -> {TC.distinct(TC.ramp.go(left, done, TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n)) == True{} : Bool}:
  match left:
    case 0n:
      {==}
    case 1n+l:
      +a = pu.ch(c, TC.Px{lr, lg, lb})
      +b = pu.ch(c, TC.Px{hr, hg, hb})
      +y = TC.rung(TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, 1n+done, l, n)
      +next = TC.chan(a, b, 1n+done, l, n)
      +at = {%pu.rung_ch(c, lr, lg, lb, hr, hg, hb, 1n+done, l, n) : {TC.step(a, b, _, next) == True{} : Bool}; pu.step_refl(Nat.is_le(a, b), next) : {TC.step(a, b, pu.ch(c, y), next) == True{} : Bool}}
      +first = pu.notin_go(c, l, 1n+done, lr, lg, lb, hr, hg, hb, n, y, en, ed, at)
      +more = pu.distinct_go(c, l, 1n+done, lr, lg, lb, hr, hg, hb, n, en, ed)
      pu.and_t(TC.notin(y, TC.ramp.go(l, 1n+done, TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n)), TC.distinct(TC.ramp.go(l, 1n+done, TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n)), first, more)

# n at most the larger of a and b is at most one of them
def pu.max_or(+n: Nat, +a: Nat, +b: Nat, +h: {Nat.is_le(n, Nat.max(a, b)) == True{} : Bool}) -> {Bool.or(Nat.is_le(n, a), Nat.is_le(n, b)) == True{} : Bool}:
  match n a b:
    case 0n p q:
      %Equal.sym(Bool, Nat.is_le(0n, p), True{}, pu.le_zero(p)) : {Bool.or(_, Nat.is_le(0n, q)) == True{} : Bool}
      {==}
    case 1n+m 0n q:
      h
    case 1n+m 1n+p 0n:
      %Equal.sym(Bool, Nat.is_le(1n+m, 1n+p), True{}, h) : {Bool.or(_, Nat.is_le(1n+m, 0n)) == True{} : Bool}
      {==}
    case 1n+m 1n+p 1n+q:
      pu.max_or(m, p, q, h)

def pu.distinct_by(+c: pu.Ch, +m: Nat, +lr: Nat, +lg: Nat, +lb: Nat, +hr: Nat, +hg: Nat, +hb: Nat, +ed: {Nat.is_le(1n+m, TC.gap(pu.ch(c, TC.Px{lr, lg, lb}), pu.ch(c, TC.Px{hr, hg, hb}))) == True{} : Bool})
  -> {TC.distinct(TC.ramp(TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, 1n+m)) == True{} : Bool}:
  pu.distinct_go(c, 1n+m, 0n, lr, lg, lb, hr, hg, hb, 1n+m, pu.le_zero(m), ed)

def pu.distinct_gb(+xg: Bool, +m: Nat, +lr: Nat, +lg: Nat, +lb: Nat, +hr: Nat, +hg: Nat, +hb: Nat, +eg: {Nat.is_le(1n+m, TC.gap(lg, hg)) == xg : Bool}, +h: {Bool.or(xg, Nat.is_le(1n+m, TC.gap(lb, hb))) == True{} : Bool})
  -> {TC.distinct(TC.ramp(TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, 1n+m)) == True{} : Bool}:
  match xg:
    case True{}:
      pu.distinct_by(ChG{}, m, lr, lg, lb, hr, hg, hb, eg)
    case False{}:
      pu.distinct_by(ChB{}, m, lr, lg, lb, hr, hg, hb, h)

def pu.distinct_rgb(+xr: Bool, +m: Nat, +lr: Nat, +lg: Nat, +lb: Nat, +hr: Nat, +hg: Nat, +hb: Nat, +er: {Nat.is_le(1n+m, TC.gap(lr, hr)) == xr : Bool}, +h: {Bool.or(xr, Nat.is_le(1n+m, Nat.max(TC.gap(lg, hg), TC.gap(lb, hb)))) == True{} : Bool})
  -> {TC.distinct(TC.ramp(TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, 1n+m)) == True{} : Bool}:
  match xr:
    case True{}:
      pu.distinct_by(ChR{}, m, lr, lg, lb, hr, hg, hb, er)
    case False{}:
      pu.distinct_gb(Nat.is_le(1n+m, TC.gap(lg, hg)), m, lr, lg, lb, hr, hg, hb, {==}, pu.max_or(1n+m, TC.gap(lg, hg), TC.gap(lb, hb), h))

def tui_effort_ramp_distinct(+lo: TC.Px, +hi: TC.Px, +n: Nat, +fits: {Nat.is_le(n, TC.span(lo, hi)) == True{} : Bool}) -> {TC.distinct(TC.ramp(lo, hi, n)) == True{} : Bool}:
  match lo hi n:
    case TC.Px{lr, lg, lb} TC.Px{hr, hg, hb} 0n:
      {==}
    case TC.Px{lr, lg, lb} TC.Px{hr, hg, hb} 1n+m:
      +wide = pu.max_or(1n+m, TC.gap(lr, hr), Nat.max(TC.gap(lg, hg), TC.gap(lb, hb)), fits)
      pu.distinct_rgb(Nat.is_le(1n+m, TC.gap(lr, hr)), m, lr, lg, lb, hr, hg, hb, {==}, wide)

# every shipped ramp is wider than the longest ladder
def pu.shipped_wide(s: T.Shipped) -> {Nat.is_le(TC.ladder.max(), TC.span(TC.shipped.lo(s), TC.shipped.hi(s))) == True{} : Bool}:
  match s:
    case T.Eukhe{}:
      {==}
    case T.Dark{}:
      {==}
    case T.Light{}:
      {==}

def tui_effort_shipped_distinct(+s: T.Shipped, +n: Nat, +fits: {Nat.is_le(n, TC.ladder.max()) == True{} : Bool}) -> {TC.distinct(TC.ramp(TC.shipped.lo(s), TC.shipped.hi(s), n)) == True{} : Bool}:
  +lo = TC.shipped.lo(s)
  +hi = TC.shipped.hi(s)
  tui_effort_ramp_distinct(lo, hi, n, pu.le_trans(n, TC.ladder.max(), TC.span(lo, hi), fits, pu.shipped_wide(s)))

# The usage bands
# ---------------

def tui_usage_bands_ascend() -> {TC.ascend(TC.bands()) == True{} : Bool}:
  {==}

# t * den <= (t + e) * den
def pu.mul_le_add(+t: Nat, +e: Nat, +den: Nat) -> {Nat.is_le(Nat.mul(t, den), Nat.mul(Nat.add(t, e), den)) == True{} : Bool}:
  match t:
    case 0n:
      pu.le_zero(Nat.mul(e, den))
    case 1n+p:
      pu.le_add_l(den, Nat.mul(p, den), Nat.mul(Nat.add(p, e), den), pu.mul_le_add(p, e, den))

def pu.one_and(+p: Bool, +x: Bool, +y: Bool, hxy: {x == True{} : Bool} -> {y == True{} : Bool}) -> {Nat.is_le(TC.one(Bool.and(p, x)), TC.one(Bool.and(p, y))) == True{} : Bool}:
  match p:
    case False{}:
      {==}
    case True{}:
      match x:
        case True{}:
          %Equal.sym(Bool, y, True{}, hxy({==})) : {Nat.is_le(1n, TC.one(_)) == True{} : Bool}
          {==}
        case False{}:
          pu.le_zero(TC.one(y))

# a band reached by t tokens stays reached by t + e
def pu.reach_mono(+f: TC.Frac, +t: Nat, +e: Nat, +w: Nat) -> {Nat.is_le(TC.one(TC.reached(f, t, w)), TC.one(TC.reached(f, Nat.add(t, e), w))) == True{} : Bool}:
  match f:
    case TC.Frac{num, den}:
      +lhs = Nat.mul(w, num)
      pu.one_and(Nat.is_lt(0n, w), Nat.is_le(lhs, Nat.mul(t, den)), Nat.is_le(lhs, Nat.mul(Nat.add(t, e), den)), ex => pu.le_trans(lhs, Nat.mul(t, den), Nat.mul(Nat.add(t, e), den), ex, pu.mul_le_add(t, e, den)))

def pu.band_mono(+fs: List<&2, TC.Frac>, +t: Nat, +e: Nat, +w: Nat) -> {Nat.is_le(TC.band.go(fs, t, w), TC.band.go(fs, Nat.add(t, e), w)) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Con{+f, rest}:
      pu.le_add_both(TC.one(TC.reached(f, t, w)), TC.one(TC.reached(f, Nat.add(t, e), w)), TC.band.go(rest, t, w), TC.band.go(rest, Nat.add(t, e), w), pu.reach_mono(f, t, e, w), pu.band_mono(rest, t, e, w))

def tui_usage_band_monotone(+t: Nat, +e: Nat, +w: Nat) -> {Nat.is_le(TC.band(t, w), TC.band(Nat.add(t, e), w)) == True{} : Bool}:
  pu.band_mono(TC.bands(), t, e, w)

def pu.add_assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %pu.add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

def pu.mul_add_r(+x: Nat, +y: Nat, +c: Nat) -> {Nat.mul(Nat.add(x, y), c) == Nat.add(Nat.mul(x, c), Nat.mul(y, c)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(Nat.add(p, y), c), Nat.add(Nat.mul(p, c), Nat.mul(y, c)), pu.mul_add_r(p, y, c)) : {Nat.add(c, _) == Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(y, c)) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(y, c)), Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(y, c))), pu.add_assoc(c, Nat.mul(p, c), Nat.mul(y, c)))

def pu.mul_assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(Nat.add(b, Nat.mul(p, b)), c), Nat.add(Nat.mul(b, c), Nat.mul(Nat.mul(p, b), c)), pu.mul_add_r(b, Nat.mul(p, b), c)) : {_ == Nat.add(Nat.mul(b, c), Nat.mul(p, Nat.mul(b, c))) : Nat}
      %pu.mul_assoc(p, b, c) : {Nat.add(Nat.mul(b, c), Nat.mul(Nat.mul(p, b), c)) == Nat.add(Nat.mul(b, c), _) : Nat}
      {==}

def pu.mul_zero_r(+k: Nat) -> {Nat.mul(k, 0n) == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pu.mul_zero_r(p)

def pu.pos(+k: Nat, +w: Nat) -> {Nat.is_lt(0n, Nat.mul(1n+k, w)) == Nat.is_lt(0n, w) : Bool}:
  match w:
    case 0n:
      %Equal.sym(Nat, Nat.mul(k, 0n), 0n, pu.mul_zero_r(k)) : {Nat.is_lt(0n, _) == Nat.is_lt(0n, 0n) : Bool}
      {==}
    case 1n+v:
      {==}

def pu.mul_le_mono_r(+k: Nat, +x: Nat, +y: Nat, +h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(Nat.mul(k, x), Nat.mul(k, y)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pu.le_add_both(x, y, Nat.mul(p, x), Nat.mul(p, y), h, pu.mul_le_mono_r(p, x, y, h))

def pu.lt_add_both(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +ab: {Nat.is_lt(a, b) == True{} : Bool}, +cd: {Nat.is_le(c, d) == True{} : Bool}) -> {Nat.is_lt(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}:
  pu.lt_of_le_succ(Nat.add(a, c), Nat.add(b, d), pu.le_add_both(1n+a, b, c, d, pu.le_succ_of_lt(a, b, ab), cd))

def pu.mul_lt_mono(+k: Nat, +x: Nat, +y: Nat, +h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(1n+k, x), Nat.mul(1n+k, y)) == True{} : Bool}:
  pu.lt_add_both(x, y, Nat.mul(k, x), Nat.mul(k, y), h, pu.mul_le_mono_r(k, x, y, pu.lt_le(x, y, h)))

def pu.not_le_lt(+x: Nat, +y: Nat, +h: {Nat.is_le(x, y) == False{} : Bool}) -> {Nat.is_lt(y, x) == True{} : Bool}:
  match x y:
    case 0n 0n:
      pu.absurd_tf({Nat.is_lt(0n, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      pu.absurd_tf({Nat.is_lt(1n+q, 0n) == True{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pu.not_le_lt(p, q, h)

def pu.lt_not_le(+a: Nat, +b: Nat, +e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      pu.absurd_ft({True{} == False{} : Bool}, e)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      pu.absurd_ft({True{} == False{} : Bool}, e)
    case 1n+p 1n+q:
      pu.lt_not_le(p, q, e)

def pu.cancel.pick(+b: Bool, +k: Nat, +x: Nat, +y: Nat, +eb: {Nat.is_le(x, y) == b : Bool}) -> {Nat.is_le(Nat.mul(1n+k, x), Nat.mul(1n+k, y)) == b : Bool}:
  match b:
    case True{}:
      pu.mul_le_mono_r(1n+k, x, y, eb)
    case False{}:
      pu.lt_not_le(Nat.mul(1n+k, y), Nat.mul(1n+k, x), pu.mul_lt_mono(k, y, x, pu.not_le_lt(x, y, eb)))

# a factor 1 + k on both sides of <= cancels
def pu.cancel(+k: Nat, +x: Nat, +y: Nat) -> {Nat.is_le(Nat.mul(1n+k, x), Nat.mul(1n+k, y)) == Nat.is_le(x, y) : Bool}:
  pu.cancel.pick(Nat.is_le(x, y), k, x, y, {==})

# a band is reached by the same fraction of any window
def pu.reach_scale(+f: TC.Frac, +k: Nat, +t: Nat, +w: Nat) -> {TC.reached(f, Nat.mul(1n+k, t), Nat.mul(1n+k, w)) == TC.reached(f, t, w) : Bool}:
  match f:
    case TC.Frac{num, den}:
      +kk = {1n+k : Nat}
      +rhs = Bool.and(Nat.is_lt(0n, w), Nat.is_le(Nat.mul(w, num), Nat.mul(t, den)))
      %Equal.sym(Bool, Nat.is_lt(0n, Nat.mul(kk, w)), Nat.is_lt(0n, w), pu.pos(k, w)) : {Bool.and(_, Nat.is_le(Nat.mul(Nat.mul(kk, w), num), Nat.mul(Nat.mul(kk, t), den))) == rhs : Bool}
      %Equal.sym(Nat, Nat.mul(Nat.mul(kk, w), num), Nat.mul(kk, Nat.mul(w, num)), pu.mul_assoc(kk, w, num)) : {Bool.and(Nat.is_lt(0n, w), Nat.is_le(_, Nat.mul(Nat.mul(kk, t), den))) == rhs : Bool}
      %Equal.sym(Nat, Nat.mul(Nat.mul(kk, t), den), Nat.mul(kk, Nat.mul(t, den)), pu.mul_assoc(kk, t, den)) : {Bool.and(Nat.is_lt(0n, w), Nat.is_le(Nat.mul(kk, Nat.mul(w, num)), _)) == rhs : Bool}
      %Equal.sym(Bool, Nat.is_le(Nat.mul(kk, Nat.mul(w, num)), Nat.mul(kk, Nat.mul(t, den))), Nat.is_le(Nat.mul(w, num), Nat.mul(t, den)), pu.cancel(k, Nat.mul(w, num), Nat.mul(t, den))) : {Bool.and(Nat.is_lt(0n, w), _) == rhs : Bool}
      {==}

def pu.band_scale(+fs: List<&2, TC.Frac>, +k: Nat, +t: Nat, +w: Nat) -> {TC.band.go(fs, Nat.mul(1n+k, t), Nat.mul(1n+k, w)) == TC.band.go(fs, t, w) : Nat}:
  match fs:
    case Nil{}:
      {==}
    case Con{+f, rest}:
      +kt = Nat.mul(1n+k, t)
      +kw = Nat.mul(1n+k, w)
      %pu.band_scale(rest, k, t, w) : {Nat.add(TC.one(TC.reached(f, kt, kw)), TC.band.go(rest, kt, kw)) == Nat.add(TC.one(TC.reached(f, t, w)), _) : Nat}
      %pu.reach_scale(f, k, t, w) : {Nat.add(TC.one(TC.reached(f, kt, kw)), TC.band.go(rest, kt, kw)) == Nat.add(TC.one(_), TC.band.go(rest, kt, kw)) : Nat}
      {==}

def tui_usage_band_fraction(+k: Nat, +t: Nat, +w: Nat) -> {TC.band(Nat.mul(1n+k, t), Nat.mul(1n+k, w)) == TC.band(t, w) : Nat}:
  pu.band_scale(TC.bands(), k, t, w)

# The roles
# ---------

def pu.fill_len(+cols: List<&2, T.Ent>, +bg: Co.Rgb, +ts: List<&2, U32>) -> {List.length(&2, Maybe<&2, T.Val>, T.fill.map(cols, bg, ts)) == List.length(&2, U32, ts) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case Con{t, rest}:
      %pu.fill_len(cols, bg, rest) : {1n+List.length(&2, Maybe<&2, T.Val>, T.fill.map(cols, bg, rest)) == 1n+_ : Nat}
      {==}

def pu.all_lt(rs: List<&2, Nat>, +n: Nat) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, rest}:
      Bool.and(Nat.is_lt(r, n), pu.all_lt(rest, n))

# a complete palette has a value at every index below its length
def pu.get_found(+p: List<&2, Maybe<&2, T.Val>>, +r: Nat, +hc: {T.complete(p) == True{} : Bool}, +hl: {Nat.is_lt(r, List.length(&2, Maybe<&2, T.Val>, p)) == True{} : Bool})
  -> {TC.found(T.Val, List.get(&2, Maybe<&2, T.Val>, p, r)) == True{} : Bool}:
  match p r:
    case Nil{} q:
      pu.absurd_ft({TC.found(T.Val, List.get(&2, Maybe<&2, T.Val>, Nil{}, q)) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(q, 0n), True{}, pu.lt_zero_f(q), hl))
    case Con{+v, +rest} 0n:
      pu.and_l(Maybe.is_some(&2, T.Val, v), T.complete(rest), hc)
    case Con{+v, +rest} 1n+q:
      pu.get_found(rest, q, pu.and_r(Maybe.is_some(&2, T.Val, v), T.complete(rest), hc), hl)

def pu.resolves_go(+p: List<&2, Maybe<&2, T.Val>>, +rs: List<&2, Nat>, +hc: {T.complete(p) == True{} : Bool}, +hl: {pu.all_lt(rs, List.length(&2, Maybe<&2, T.Val>, p)) == True{} : Bool})
  -> {TC.resolves(p, rs) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      +len = List.length(&2, Maybe<&2, T.Val>, p)
      +here = pu.get_found(p, r, hc, pu.and_l(Nat.is_lt(r, len), pu.all_lt(rest, len), hl))
      +more = pu.resolves_go(p, rest, hc, pu.and_r(Nat.is_lt(r, len), pu.all_lt(rest, len), hl))
      pu.and_t(TC.found(T.Val, List.get(&2, Maybe<&2, T.Val>, p, r)), TC.resolves(p, rest), here, more)

def tui_roles_resolve(+f: T.Th, +v: {T.valid(f) == True{} : Bool}) -> {TC.resolves(T.palette(f), TC.roles()) == True{} : Bool}:
  match f:
    case T.Th{name, cols, page}:
      +bg = T.background(cols, page)
      +p = T.fill.map(cols, bg, T.toks())
      +hc = TP.theme_tokens_complete(T.Th{name, cols, page}, v)
      +hl = {%Equal.sym(Nat, List.length(&2, Maybe<&2, T.Val>, p), List.length(&2, U32, T.toks()), pu.fill_len(cols, bg, T.toks())) : {pu.all_lt(TC.roles(), _) == True{} : Bool}; {==} : {pu.all_lt(TC.roles(), List.length(&2, Maybe<&2, T.Val>, p)) == True{} : Bool}}
      pu.resolves_go(p, TC.roles(), hc, hl)

def tui_roles_shipped(s: T.Shipped) -> {TC.paints(T.table(s), TC.roles()) == True{} : Bool}:
  match s:
    case T.Eukhe{}:
      {==}
    case T.Dark{}:
      {==}
    case T.Light{}:
      {==}
