# eukhe: lemmas the proofs of area tui_color share

import Base
import ../../bend/ffi_tui_color.bend as FTC
import ../../bend/tui_color.bend as TC
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tui_color.bend as TuiColor
import ../base/bool.bend as LBool
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ../base/wire.bend as LWire

def pu.absurd_tf(-A: Type, +e: {True{} == False{} : Bool}) -> A:
  %e : LLogicLogic.pu.BD(_, Unit, A)
  Unit{}

def pu.lt_le(+a: Nat, +b: Nat, +e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n q:
      LNat.pu.le_zero(q)
    case 1n+p 0n:
      LLogicLogic.pu.absurd_ft({Nat.is_le(1n+p, 0n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pu.lt_le(p, q, e)

def pu.lt_of_le_succ(+a: Nat, +b: Nat, +e: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case p 0n:
      LLogicLogic.pu.absurd_ft({Nat.is_lt(p, 0n) == True{} : Bool}, e)
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      pu.lt_of_le_succ(p, q, e)

def pu.le_lt_trans(+a: Nat, +b: Nat, +c: Nat, +ab: {Nat.is_le(a, b) == True{} : Bool}, +bc: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case p q 0n:
      LLogicLogic.pu.absurd_ft({Nat.is_lt(p, 0n) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(q, 0n), True{}, LNat.pu.lt_zero_f(q), bc))
    case 0n q 1n+r:
      {==}
    case 1n+p 0n 1n+r:
      LLogicLogic.pu.absurd_ft({Nat.is_lt(1n+p, 1n+r) == True{} : Bool}, ab)
    case 1n+p 1n+q 1n+r:
      pu.le_lt_trans(p, q, r, ab, bc)

def pu.lt_ne(+a: Nat, +b: Nat, +e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      LLogicLogic.pu.absurd_ft({True{} == False{} : Bool}, e)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pu.lt_ne(p, q, e)

def pu.gt_ne(+a: Nat, +b: Nat, +e: {Nat.is_lt(b, a) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      LLogicLogic.pu.absurd_ft({True{} == False{} : Bool}, e)
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
      LNat.pu.le_refl(m)
    case 1n+p:
      +q = p
      LNat.pu.le_succ_r(m, Nat.add(q, m), pu.le_add(q, m))

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
      LLogicLogic.pu.absurd_ft({Nat.is_le(Nat.add(1n+p, d), Nat.add(0n, d)) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pu.le_add_mono_r(p, q, d, e)

def pu.le_add_both(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +ab: {Nat.is_le(a, b) == True{} : Bool}, +cd: {Nat.is_le(c, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}:
  LNat.pu.le_trans(Nat.add(a, c), Nat.add(a, d), Nat.add(b, d), pu.le_add_l(a, c, d, cd), pu.le_add_mono_r(a, b, d, ab))

def pu.le_succ_of_lt(+a: Nat, +b: Nat, +e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a b:
    case p 0n:
      LLogicLogic.pu.absurd_ft({Nat.is_le(1n+p, 0n) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(p, 0n), True{}, LNat.pu.lt_zero_f(p), e))
    case 0n 1n+q:
      LNat.pu.le_zero(q)
    case 1n+p 1n+q:
      pu.le_succ_of_lt(p, q, e)

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
      LLogicLogic.pu.absurd_ft({True{} == False{} : Bool}, e)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LLogicLogic.pu.absurd_ft({True{} == False{} : Bool}, e)
    case 1n+p 1n+q:
      pu.lt_not_le(p, q, e)

# Division
# --------

# a step of Nat.divmod (n = 1 + bp) adds one to q * n + r, and r stays
# at most bp: so q * n + r is x and r < n
def pu.go_eq(+a: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat, +h: {Nat.add(m, r) == bp : Nat})
  -> {Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(a, m, d, r)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(a, m, d, r))) == Nat.add(a, Nat.add(Nat.mul(d, 1n+bp), r)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+ap:
      match m:
        case 0n:
          +lhs = Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(ap, r, 1n+d, 0n)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(ap, r, 1n+d, 0n)))
          +dm = Nat.mul(d, 1n+bp)
          +h2 = {%Equal.sym(Nat, Nat.add(r, 0n), r, LNat.pa.add_zero(r)) : {_ == bp : Nat}; h : {Nat.add(r, 0n) == bp : Nat}}
          +ih = pu.go_eq(ap, r, 1n+d, 0n, bp, h2)
          +y = Nat.add(bp, dm)
          %Equal.sym(Nat, r, bp, h) : {lhs == 1n+Nat.add(ap, Nat.add(dm, _)) : Nat}
          %LNat.pa.add_comm(bp, dm) : {lhs == 1n+Nat.add(ap, _) : Nat}
          %LNat.pa.add_succ(ap, y) : {lhs == _ : Nat}
          %LNat.pa.add_zero(y) : {lhs == Nat.add(ap, 1n+_) : Nat}
          ih
        case 1n+mp:
          +lhs = Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(ap, mp, d, 1n+r)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(ap, mp, d, 1n+r)))
          +dm = Nat.mul(d, 1n+bp)
          +h3 = Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), bp, LNat.pa.add_succ(mp, r), h)
          +ih = pu.go_eq(ap, mp, d, 1n+r, bp, h3)
          %LNat.pa.add_succ(ap, Nat.add(dm, r)) : {lhs == _ : Nat}
          %LNat.pa.add_succ(dm, r) : {lhs == Nat.add(ap, _) : Nat}
          ih

def pu.go_le(+a: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat, +h: {Nat.add(m, r) == bp : Nat})
  -> {Nat.is_le(Pair.snd(Nat, Nat, Nat.divmod.go(a, m, d, r)), bp) == True{} : Bool}:
  match a:
    case 0n:
      %h : {Nat.is_le(r, _) == True{} : Bool}
      pu.le_add(m, r)
    case 1n+ap:
      match m:
        case 0n:
          pu.go_le(ap, r, 1n+d, 0n, bp, {%Equal.sym(Nat, Nat.add(r, 0n), r, LNat.pa.add_zero(r)) : {_ == bp : Nat}; h : {Nat.add(r, 0n) == bp : Nat}})
        case 1n+mp:
          pu.go_le(ap, mp, d, 1n+r, bp, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), bp, LNat.pa.add_succ(mp, r), h))

# x = (x / n) * n + x mod n, for n = 1 + bp
def pu.div_eq(+x: Nat, +bp: Nat) -> {Nat.add(Nat.mul(Nat.div(x, 1n+bp), 1n+bp), Nat.mod(x, 1n+bp)) == x : Nat}:
  %LNat.pa.add_zero(x) : {Nat.add(Nat.mul(Nat.div(x, 1n+bp), 1n+bp), Nat.mod(x, 1n+bp)) == _ : Nat}
  pu.go_eq(x, bp, 0n, 0n, bp, LNat.pa.add_zero(bp))

# x mod n < n, for n = 1 + bp
def pu.mod_le(+x: Nat, +bp: Nat) -> {Nat.is_le(Nat.mod(x, 1n+bp), bp) == True{} : Bool}:
  pu.go_le(x, bp, 0n, 0n, bp, LNat.pa.add_zero(bp))

def pu.mul_le_mono_l(+x: Nat, +y: Nat, +k: Nat, +h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(Nat.mul(x, k), Nat.mul(y, k)) == True{} : Bool}:
  match x y:
    case 0n q:
      LNat.pu.le_zero(Nat.mul(q, k))
    case 1n+p 0n:
      LLogicLogic.pu.absurd_ft({Nat.is_le(Nat.mul(1n+p, k), Nat.mul(0n, k)) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pu.le_add_l(k, Nat.mul(p, k), Nat.mul(q, k), pu.mul_le_mono_l(p, q, k, h))

def pu.le_add_cancel_l(+c: Nat, -x: Nat, -y: Nat, +h: {Nat.is_le(Nat.add(c, x), Nat.add(c, y)) == True{} : Bool}) -> {Nat.is_le(x, y) == True{} : Bool}:
  match c:
    case 0n:
      h
    case 1n+p:
      pu.le_add_cancel_l(p, x, y, h)

def pu.lt_succ(+b: Nat) -> {Nat.is_lt(b, 1n+b) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+p:
      pu.lt_succ(p)

# n times the quotient is at most x
def pu.div_low(+x: Nat, +n: Nat, +en: {Nat.is_le(1n, n) == True{} : Bool}) -> {Nat.is_le(Nat.mul(Nat.div(x, n), n), x) == True{} : Bool}:
  match n:
    case 0n:
      LLogicLogic.pu.absurd_ft({Nat.is_le(Nat.mul(Nat.div(x, 0n), 0n), x) == True{} : Bool}, en)
    case 1n+bp:
      +qn = Nat.mul(Nat.div(x, 1n+bp), 1n+bp)
      %pu.div_eq(x, bp) : {Nat.is_le(qn, _) == True{} : Bool}
      LNat.pu.le_add_r(qn, Nat.mod(x, 1n+bp))

def pu.div_max.pick(+b: Bool, +x: Nat, +bp: Nat, +q: Nat, +eb: {Nat.is_le(q, Nat.div(x, 1n+bp)) == b : Bool}, +eq: {Nat.is_le(Nat.mul(q, 1n+bp), x) == True{} : Bool})
  -> {Nat.is_le(q, Nat.div(x, 1n+bp)) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      +n = {1n+bp : Nat}
      +dq = Nat.div(x, n)
      +dn = Nat.mul(dq, n)
      +r = Nat.mod(x, n)
      +up = pu.mul_le_mono_l(1n+dq, q, n, pu.le_succ_of_lt(dq, q, pu.not_le_lt(q, dq, eb)))
      +over = LNat.pu.le_trans(Nat.add(n, dn), Nat.mul(q, n), x, up, eq)
      +over2 = {%Equal.sym(Nat, Nat.add(dn, r), x, pu.div_eq(x, bp)) : {Nat.is_le(Nat.add(n, dn), _) == True{} : Bool}; over : {Nat.is_le(Nat.add(n, dn), Nat.add(dn, r)) == True{} : Bool}}
      +over3 = {%LNat.pa.add_comm(n, dn) : {Nat.is_le(_, Nat.add(dn, r)) == True{} : Bool}; over2 : {Nat.is_le(Nat.add(dn, n), Nat.add(dn, r)) == True{} : Bool}}
      +big = LNat.pu.le_trans(n, r, bp, pu.le_add_cancel_l(dn, n, r, over3), pu.mod_le(x, bp))
      pu.absurd_tf({Nat.is_le(q, dq) == True{} : Bool}, Equal.trans(Bool, True{}, Nat.is_le(n, bp), False{}, Equal.sym(Bool, Nat.is_le(n, bp), True{}, big), pu.lt_not_le(bp, n, pu.lt_succ(bp))))

# a q with q * n at most x is at most the quotient (n >= 1)
def pu.div_max(+x: Nat, +n: Nat, +q: Nat, +en: {Nat.is_le(1n, n) == True{} : Bool}, +eq: {Nat.is_le(Nat.mul(q, n), x) == True{} : Bool}) -> {Nat.is_le(q, Nat.div(x, n)) == True{} : Bool}:
  match n:
    case 0n:
      LLogicLogic.pu.absurd_ft({Nat.is_le(q, Nat.div(x, 0n)) == True{} : Bool}, en)
    case 1n+bp:
      pu.div_max.pick(Nat.is_le(q, Nat.div(x, 1n+bp)), x, bp, q, {==}, eq)

# adding d >= n raises the quotient
def pu.dv_lt_add(+x: Nat, +d: Nat, +n: Nat, +en: {Nat.is_le(1n, n) == True{} : Bool}, +ed: {Nat.is_le(n, d) == True{} : Bool}) -> {Nat.is_lt(Nat.div(x, n), Nat.div(Nat.add(d, x), n)) == True{} : Bool}:
  +y = Nat.add(d, x)
  +q = Nat.div(x, n)
  +low = pu.le_add_both(n, d, Nat.mul(q, n), x, ed, pu.div_low(x, n, en))
  pu.lt_of_le_succ(q, Nat.div(y, n), pu.div_max(y, n, 1n+q, en, low))

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
      pu.lt_add_l(a, Nat.div(Nat.mul(k, d), n), Nat.div(Nat.add(d, Nat.mul(k, d)), n), pu.dv_lt_add(Nat.mul(k, d), d, n, en, ed))
    case False{}:
      +d = Nat.sub(a, b)
      pu.lt_add_l(b, Nat.div(Nat.mul(l, d), n), Nat.div(Nat.add(d, Nat.mul(l, d)), n), pu.dv_lt_add(Nat.mul(l, d), d, n, en, ed))

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

def pu.lt_le_trans(+a: Nat, +b: Nat, +c: Nat, +ab: {Nat.is_lt(a, b) == True{} : Bool}, +bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  pu.lt_of_le_succ(a, c, LNat.pu.le_trans(1n+a, b, c, pu.le_succ_of_lt(a, b, ab), bc))

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
      LNat.pu.le_refl(p)
    case False{}:
      LNat.pu.le_refl(p)

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
      LBool.pu.and_t(Bool.not(TC.px.eq(x, y)), TC.notin(x, TC.ramp.go(l, 1n+done, TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n)), pu.ne_px(c, x, y, ney), more)

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
      LBool.pu.and_t(TC.notin(y, TC.ramp.go(l, 1n+done, TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n)), TC.distinct(TC.ramp.go(l, 1n+done, TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n)), first, more)

# n at most the larger of a and b is at most one of them
def pu.max_or(+n: Nat, +a: Nat, +b: Nat, +h: {Nat.is_le(n, Nat.max(a, b)) == True{} : Bool}) -> {Bool.or(Nat.is_le(n, a), Nat.is_le(n, b)) == True{} : Bool}:
  match n a b:
    case 0n p q:
      %Equal.sym(Bool, Nat.is_le(0n, p), True{}, LNat.pu.le_zero(p)) : {Bool.or(_, Nat.is_le(0n, q)) == True{} : Bool}
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
  pu.distinct_go(c, 1n+m, 0n, lr, lg, lb, hr, hg, hb, 1n+m, LNat.pu.le_zero(m), ed)

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

def pu.mul_le_mono_r(+k: Nat, +x: Nat, +y: Nat, +h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(Nat.mul(k, x), Nat.mul(k, y)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pu.le_add_both(x, y, Nat.mul(p, x), Nat.mul(p, y), h, pu.mul_le_mono_r(p, x, y, h))

# Nat arithmetic: associativity, distribution, zero
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

# The entry
# ---------

# a ramp request read back: every number fits, so each reads back and
# the rest follows
def tcf.dec_ramp(+lr: Nat, +lg: Nat, +lb: Nat, +hr: Nat, +hg: Nat, +hb: Nat, +n: Nat, +rest: String,
  +fit: {TuiColor.req_fits(FTC.QRamp{TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n}) == True{} : Bool})
  -> {FTC.get_req(TuiColor.spell_req(FTC.QRamp{TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n}, rest)) == Wr.Got{FTC.QRamp{TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n}, rest} : Wr.Dec<FTC.Req>}:
  +pl = TuiColor.px_fits(TC.Px{lr, lg, lb})
  +ph = TuiColor.px_fits(TC.Px{hr, hg, hb})
  +fl = LLogicBool.wr_and_l(pl, Bool.and(ph, LawsBase.wire_fits(n)), fit)
  +fhn = LLogicBool.wr_and_r(pl, Bool.and(ph, LawsBase.wire_fits(n)), fit)
  +fh = LLogicBool.wr_and_l(ph, LawsBase.wire_fits(n), fhn)
  +fn = LLogicBool.wr_and_r(ph, LawsBase.wire_fits(n), fhn)
  +flgb = LLogicBool.wr_and_r(LawsBase.wire_fits(lr), Bool.and(LawsBase.wire_fits(lg), LawsBase.wire_fits(lb)), fl)
  +fhgb = LLogicBool.wr_and_r(LawsBase.wire_fits(hr), Bool.and(LawsBase.wire_fits(hg), LawsBase.wire_fits(hb)), fh)
  +x6 = Wr.put_nat(n, rest)
  +x5 = Wr.put_nat(hb, x6)
  +x4 = Wr.put_nat(hg, x5)
  +x3 = Wr.put_nat(hr, x4)
  +x2 = Wr.put_nat(lb, x3)
  +x1 = Wr.put_nat(lg, x2)
  +g = {Wr.Got{FTC.QRamp{TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n}, rest} : Wr.Dec<FTC.Req>}
  %LWire.pw6.nat(lr, x1, LLogicBool.wr_and_l(LawsBase.wire_fits(lr), Bool.and(LawsBase.wire_fits(lg), LawsBase.wire_fits(lb)), fl)) : {FTC.get_ramp(FTC.get_px(_)) == g : Wr.Dec<FTC.Req>}
  %LWire.pw6.nat(lg, x2, LLogicBool.wr_and_l(LawsBase.wire_fits(lg), LawsBase.wire_fits(lb), flgb)) : {FTC.get_ramp(FTC.get_px.g(lr, _)) == g : Wr.Dec<FTC.Req>}
  %LWire.pw6.nat(lb, x3, LLogicBool.wr_and_r(LawsBase.wire_fits(lg), LawsBase.wire_fits(lb), flgb)) : {FTC.get_ramp(FTC.get_px.b(lr, lg, _)) == g : Wr.Dec<FTC.Req>}
  %LWire.pw6.nat(hr, x4, LLogicBool.wr_and_l(LawsBase.wire_fits(hr), Bool.and(LawsBase.wire_fits(hg), LawsBase.wire_fits(hb)), fh)) : {FTC.get_ramp.hi(TC.Px{lr, lg, lb}, FTC.get_px(_)) == g : Wr.Dec<FTC.Req>}
  %LWire.pw6.nat(hg, x5, LLogicBool.wr_and_l(LawsBase.wire_fits(hg), LawsBase.wire_fits(hb), fhgb)) : {FTC.get_ramp.hi(TC.Px{lr, lg, lb}, FTC.get_px.g(hr, _)) == g : Wr.Dec<FTC.Req>}
  %LWire.pw6.nat(hb, x6, LLogicBool.wr_and_r(LawsBase.wire_fits(hg), LawsBase.wire_fits(hb), fhgb)) : {FTC.get_ramp.hi(TC.Px{lr, lg, lb}, FTC.get_px.b(hr, hg, _)) == g : Wr.Dec<FTC.Req>}
  %LWire.pw6.nat(n, rest, fn) : {FTC.get_ramp.n(TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, _) == g : Wr.Dec<FTC.Req>}
  {==}

# a request that fits the wire reads back, and the rest follows
def tcf.dec(+q: FTC.Req, +rest: String, +fit: {TuiColor.req_fits(q) == True{} : Bool}) -> {FTC.get_req(TuiColor.spell_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FTC.Req>}:
  match q:
    case FTC.QRamp{lo, hi, n}:
      match lo hi:
        case TC.Px{lr, lg, lb} TC.Px{hr, hg, hb}:
          tcf.dec_ramp(lr, lg, lb, hr, hg, hb, n, rest, fit)
    case FTC.QBand{+t, +w}:
      +g = {Wr.Got{FTC.QBand{t, w}, rest} : Wr.Dec<FTC.Req>}
      %LWire.pw6.nat(t, Wr.put_nat(w, rest), LLogicBool.wr_and_l(LawsBase.wire_fits(t), LawsBase.wire_fits(w), fit)) : {FTC.get_band(_) == g : Wr.Dec<FTC.Req>}
      %LWire.pw6.nat(w, rest, LLogicBool.wr_and_r(LawsBase.wire_fits(t), LawsBase.wire_fits(w), fit)) : {FTC.get_band.w(t, _) == g : Wr.Dec<FTC.Req>}
      {==}
    case FTC.QRoles{}:
      {==}

# The reader, stage by stage: the entry reads every input as the laws'
# reader does

def tcf.px_b(r: Nat, g: Nat, d: Wr.Dec<Nat>) -> {TuiColor.read_px.b(r, g, d) == FTC.get_px.b(r, g, d) : Wr.Dec<TC.Px>}:
  match d:
    case Wr.Got{b, s}:
      {==}
    case Wr.Bad{}:
      {==}

def tcf.px_g(r: Nat, d: Wr.Dec<Nat>) -> {TuiColor.read_px.g(r, d) == FTC.get_px.g(r, d) : Wr.Dec<TC.Px>}:
  match d:
    case Wr.Got{g, s}:
      tcf.px_b(r, g, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def tcf.px(d: Wr.Dec<Nat>) -> {TuiColor.read_px(d) == FTC.get_px(d) : Wr.Dec<TC.Px>}:
  match d:
    case Wr.Got{r, s}:
      tcf.px_g(r, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def tcf.ramp_n(lo: TC.Px, hi: TC.Px, d: Wr.Dec<Nat>) -> {TuiColor.read_ramp.n(lo, hi, d) == FTC.get_ramp.n(lo, hi, d) : Wr.Dec<FTC.Req>}:
  match d:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def tcf.ramp_hi(lo: TC.Px, d: Wr.Dec<TC.Px>) -> {TuiColor.read_ramp.hi(lo, d) == FTC.get_ramp.hi(lo, d) : Wr.Dec<FTC.Req>}:
  match d:
    case Wr.Got{hi, s}:
      tcf.ramp_n(lo, hi, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def tcf.ramp_lo(lo: TC.Px, +s: String) -> {TuiColor.read_ramp.hi(lo, TuiColor.read_px(Wr.get_nat(s))) == FTC.get_ramp.hi(lo, FTC.get_px(Wr.get_nat(s))) : Wr.Dec<FTC.Req>}:
  %tcf.px(Wr.get_nat(s)) : {TuiColor.read_ramp.hi(lo, TuiColor.read_px(Wr.get_nat(s))) == FTC.get_ramp.hi(lo, _) : Wr.Dec<FTC.Req>}
  tcf.ramp_hi(lo, TuiColor.read_px(Wr.get_nat(s)))

def tcf.ramp(d: Wr.Dec<TC.Px>) -> {TuiColor.read_ramp(d) == FTC.get_ramp(d) : Wr.Dec<FTC.Req>}:
  match d:
    case Wr.Got{lo, s}:
      tcf.ramp_lo(lo, s)
    case Wr.Bad{}:
      {==}

def tcf.band_w(t: Nat, d: Wr.Dec<Nat>) -> {TuiColor.read_band.w(t, d) == FTC.get_band.w(t, d) : Wr.Dec<FTC.Req>}:
  match d:
    case Wr.Got{w, s}:
      {==}
    case Wr.Bad{}:
      {==}

def tcf.band(d: Wr.Dec<Nat>) -> {TuiColor.read_band(d) == FTC.get_band(d) : Wr.Dec<FTC.Req>}:
  match d:
    case Wr.Got{t, s}:
      tcf.band_w(t, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def tcf.req_tag(t: Nat, +s: String) -> {TuiColor.read_req.tag(t, s) == FTC.get_req.tag(t, s) : Wr.Dec<FTC.Req>}:
  match t:
    case 0n:
      %tcf.px(Wr.get_nat(s)) : {TuiColor.read_ramp(TuiColor.read_px(Wr.get_nat(s))) == FTC.get_ramp(_) : Wr.Dec<FTC.Req>}
      tcf.ramp(TuiColor.read_px(Wr.get_nat(s)))
    case 1n:
      tcf.band(Wr.get_nat(s))
    case 2n:
      {==}
    case 3n+p:
      {==}

def tcf.req(d: Wr.Dec<Nat>) -> {TuiColor.read_req.go(d) == FTC.get_req.go(d) : Wr.Dec<FTC.Req>}:
  match d:
    case Wr.Got{t, s}:
      tcf.req_tag(t, s)
    case Wr.Bad{}:
      {==}

# The replies
# -----------

# the entry's list of colors is the spec's: its count, then each color
def tcf.rungs_go(xs: List<&2, TC.Px>) -> {Wr.put_list.go(~TC.Px, ~FTC.put_px, xs, "") == (List.length(&2, TC.Px, xs), TuiColor.spell_rungs.items(xs)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      match x:
        case TC.Px{r, g, b}:
          %Equal.sym(Nat & String, Wr.put_list.go(~TC.Px, ~FTC.put_px, t, ""), (List.length(&2, TC.Px, t), TuiColor.spell_rungs.items(t)), tcf.rungs_go(t)) : {Wr.put_list.step(~TC.Px, ~FTC.put_px, TC.Px{r, g, b}, _) == (1n+List.length(&2, TC.Px, t), TuiColor.spell_px(TC.Px{r, g, b}, TuiColor.spell_rungs.items(t))) : Nat & String}
          {==}

def tcf.rungs(+xs: List<&2, TC.Px>) -> {Wr.put_list(~TC.Px, ~FTC.put_px, xs, "") == TuiColor.spell_rungs(xs) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~TC.Px, ~FTC.put_px, xs, ""), (List.length(&2, TC.Px, xs), TuiColor.spell_rungs.items(xs)), tcf.rungs_go(xs)) : {Wr.put_list.fin(_) == TuiColor.spell_rungs(xs) : String}
  {==}

