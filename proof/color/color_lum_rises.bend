# eukhe: the proof of LAW color_lum_rises: every leaf of lin's table (a
# closed check per part, cl.table, so lin(c) for every c, a walk of the
# table) has its three weighted products equal to the products of the
# values and at most 0.2126, 0.7152 and 0.0722; those bounds' sums do not
# carry (two closed
# carries of 32 bits), so neither does the luminance's (lr.cy_monoU) and its
# value is the sum of the three products' values (lrs.sum); each product
# keeps the order of its linear value (lr.term_le), and sums keep order
# (lr.add_le). The U32 arithmetic is ./color_lum_rises/word.bend.

import Base
import ../../bend/color.bend as Co
import ../../laws/color/math.bend as Color
import ./base/lum.bend as LCl
import ./color_lum_rises/word.bend as LLr
import ./color_contrast_exact_wide/bin.bend as LCb
import ../base/logic/bool.bend as LLogicBool

# The leaves
# ----------

def lumr.t0() -> {LCl.cl.all(LCl.ClTerm{}, Co.lin.t0()) == True{} : Bool}:
  {==}

def lumr.t1() -> {LCl.cl.all(LCl.ClTerm{}, Co.lin.t1()) == True{} : Bool}:
  {==}

def lumr.t2() -> {LCl.cl.all(LCl.ClTerm{}, Co.lin.t2()) == True{} : Bool}:
  {==}

def lumr.t3() -> {LCl.cl.all(LCl.ClTerm{}, Co.lin.t3()) == True{} : Bool}:
  {==}

def lumr.t4() -> {LCl.cl.all(LCl.ClTerm{}, Co.lin.t4()) == True{} : Bool}:
  {==}

def lumr.t5() -> {LCl.cl.all(LCl.ClTerm{}, Co.lin.t5()) == True{} : Bool}:
  {==}

def lumr.t6() -> {LCl.cl.all(LCl.ClTerm{}, Co.lin.t6()) == True{} : Bool}:
  {==}

def lumr.t7() -> {LCl.cl.all(LCl.ClTerm{}, Co.lin.t7()) == True{} : Bool}:
  {==}

def lumr.t8() -> {LCl.cl.all(LCl.ClTerm{}, Co.lin.t8()) == True{} : Bool}:
  {==}

def lumr.t9() -> {LCl.cl.all(LCl.ClTerm{}, Co.lin.t9()) == True{} : Bool}:
  {==}

def lumr.t10() -> {LCl.cl.all(LCl.ClTerm{}, Co.lin.t10()) == True{} : Bool}:
  {==}

def lumr.t11() -> {LCl.cl.all(LCl.ClTerm{}, Co.lin.t11()) == True{} : Bool}:
  {==}

def lumr.t12() -> {LCl.cl.all(LCl.ClTerm{}, Co.lin.t12()) == True{} : Bool}:
  {==}

def lumr.t13() -> {LCl.cl.all(LCl.ClTerm{}, Co.lin.t13()) == True{} : Bool}:
  {==}

def lumr.t14() -> {LCl.cl.all(LCl.ClTerm{}, Co.lin.t14()) == True{} : Bool}:
  {==}

def lumr.t15() -> {LCl.cl.all(LCl.ClTerm{}, Co.lin.t15()) == True{} : Bool}:
  {==}

# every leaf of lin's table, part by part
def lrs.term_all() -> {LCl.cl.all(LCl.ClTerm{}, Co.lin.table()) == True{} : Bool}:
  LCl.cl.table(LCl.ClTerm{}, lumr.t0(), lumr.t1(), lumr.t2(), lumr.t3(), lumr.t4(), lumr.t5(), lumr.t6(), lumr.t7(), lumr.t8(), lumr.t9(), lumr.t10(), lumr.t11(), lumr.t12(), lumr.t13(), lumr.t14(), lumr.t15())

# the linear value of every channel has the leaves' product facts
def lrs.term(+c: U32) -> {LCl.cl.ok(LCl.ClTerm{}, Co.lin(c)) == True{} : Bool}:
  LCl.cl.lin(LCl.ClTerm{}, c, {==}, lrs.term_all())

def lrs.m1(+v: U32, h: {LCl.cl.ok(LCl.ClTerm{}, v) == True{} : Bool}) -> {LCl.cl.mterm(2126, 21260000, v) == True{} : Bool}:
  LLogicBool.wr_and_l(LCl.cl.mterm(2126, 21260000, v), Bool.and(LCl.cl.mterm(7152, 71520000, v), LCl.cl.mterm(722, 7220000, v)), h)

def lrs.m23(+v: U32, h: {LCl.cl.ok(LCl.ClTerm{}, v) == True{} : Bool}) -> {Bool.and(LCl.cl.mterm(7152, 71520000, v), LCl.cl.mterm(722, 7220000, v)) == True{} : Bool}:
  LLogicBool.wr_and_r(LCl.cl.mterm(2126, 21260000, v), Bool.and(LCl.cl.mterm(7152, 71520000, v), LCl.cl.mterm(722, 7220000, v)), h)

def lrs.m2(+v: U32, h: {LCl.cl.ok(LCl.ClTerm{}, v) == True{} : Bool}) -> {LCl.cl.mterm(7152, 71520000, v) == True{} : Bool}:
  LLogicBool.wr_and_l(LCl.cl.mterm(7152, 71520000, v), LCl.cl.mterm(722, 7220000, v), lrs.m23(v, h))

def lrs.m3(+v: U32, h: {LCl.cl.ok(LCl.ClTerm{}, v) == True{} : Bool}) -> {LCl.cl.mterm(722, 7220000, v) == True{} : Bool}:
  LLogicBool.wr_and_r(LCl.cl.mterm(7152, 71520000, v), LCl.cl.mterm(722, 7220000, v), lrs.m23(v, h))

# k·v is the product of the values
def lrs.mul(+k: U32, +m: U32, +v: U32, h: {LCl.cl.mterm(k, m, v) == True{} : Bool}) -> {U32.to_nat((k * v : U32)) == Nat.mul(U32.to_nat(k), U32.to_nat(v)) : Nat}:
  LLr.lr.mulv(k, v, LLogicBool.wr_and_l(Cmp.is_eq(LCb.cb.cmp(LCb.cb.u32((k * v : U32)), LCb.cb.mul(LCb.cb.u32(k), LCb.cb.u32(v)))), U32.is_le((k * v : U32), m), h))

# k·v is at most m
def lrs.bnd(+k: U32, +m: U32, +v: U32, h: {LCl.cl.mterm(k, m, v) == True{} : Bool}) -> {Nat.is_le(U32.to_nat((k * v : U32)), U32.to_nat(m)) == True{} : Bool}:
  LLr.lr.leN((k * v : U32), m, LLogicBool.wr_and_r(Cmp.is_eq(LCb.cb.cmp(LCb.cb.u32((k * v : U32)), LCb.cb.mul(LCb.cb.u32(k), LCb.cb.u32(v)))), U32.is_le((k * v : U32), m), h))

# The sum
# -------

# 0.2126 + 0.7152 does not carry, nor does it plus 0.0722
def lrs.nc12() -> {LLr.lr.cyU(21260000, 71520000) == False{} : Bool}:
  {==}

def lrs.nc123() -> {LLr.lr.cyU((21260000 + 71520000 : U32), 7220000) == False{} : Bool}:
  {==}

# the luminance of linear values x, y, z is the sum of its three products'
# values
def lrs.sumv(+x: U32, +y: U32, +z: U32, hx: {LCl.cl.ok(LCl.ClTerm{}, x) == True{} : Bool}, hy: {LCl.cl.ok(LCl.ClTerm{}, y) == True{} : Bool}, hz: {LCl.cl.ok(LCl.ClTerm{}, z) == True{} : Bool}) -> {U32.to_nat((2126 * x + 7152 * y + 722 * z : U32)) == Nat.add(Nat.add(U32.to_nat((2126 * x : U32)), U32.to_nat((7152 * y : U32))), U32.to_nat((722 * z : U32))) : Nat}:
  +le1 = lrs.bnd(2126, 21260000, x, lrs.m1(x, hx))
  +le2 = lrs.bnd(7152, 71520000, y, lrs.m2(y, hy))
  le3 = lrs.bnd(722, 7220000, z, lrs.m3(z, hz))
  +nc1 = LLr.lr.cy_monoU((2126 * x : U32), (7152 * y : U32), 21260000, 71520000, le1, le2, lrs.nc12())
  le12 = LLr.lr.le_sum((2126 * x : U32), (7152 * y : U32), 21260000, 71520000, le1, le2, nc1, lrs.nc12())
  nc2 = LLr.lr.cy_monoU(((2126 * x : U32) + (7152 * y : U32) : U32), (722 * z : U32), (21260000 + 71520000 : U32), 7220000, le12, le3, lrs.nc123())
  Equal.trans(Nat, U32.to_nat((((2126 * x : U32) + (7152 * y : U32) : U32) + (722 * z : U32) : U32)), Nat.add(U32.to_nat(((2126 * x : U32) + (7152 * y : U32) : U32)), U32.to_nat((722 * z : U32))), Nat.add(Nat.add(U32.to_nat((2126 * x : U32)), U32.to_nat((7152 * y : U32))), U32.to_nat((722 * z : U32))),
    LLr.lr.addU(((2126 * x : U32) + (7152 * y : U32) : U32), (722 * z : U32), nc2),
    Equal.cong(Nat, Nat, w => Nat.add(w, U32.to_nat((722 * z : U32))), U32.to_nat(((2126 * x : U32) + (7152 * y : U32) : U32)), Nat.add(U32.to_nat((2126 * x : U32)), U32.to_nat((7152 * y : U32))), LLr.lr.addU((2126 * x : U32), (7152 * y : U32), nc1)))

# the luminance of a color is the sum of its three products' values
def lrs.sum(+r: U32, +g: U32, +b: U32) -> {U32.to_nat(Co.lum(Co.Rgb{r, g, b})) == Nat.add(Nat.add(U32.to_nat((2126 * Co.lin(r) : U32)), U32.to_nat((7152 * Co.lin(g) : U32))), U32.to_nat((722 * Co.lin(b) : U32))) : Nat}:
  lrs.sumv(Co.lin(r), Co.lin(g), Co.lin(b), lrs.term(r), lrs.term(g), lrs.term(b))

# k·lin(c) <= k·lin(c2) when lin(c) <= lin(c2), for the weight k of
# bound m
def lrs.le(+k: U32, +m: U32, +c: U32, +c2: U32, h1: {LCl.cl.mterm(k, m, Co.lin(c)) == True{} : Bool}, h2: {LCl.cl.mterm(k, m, Co.lin(c2)) == True{} : Bool}, h: {U32.is_le(Co.lin(c), Co.lin(c2)) == True{} : Bool}) -> {Nat.is_le(U32.to_nat((k * Co.lin(c) : U32)), U32.to_nat((k * Co.lin(c2) : U32))) == True{} : Bool}:
  LLr.lr.term_le(k, Co.lin(c), Co.lin(c2), lrs.mul(k, m, Co.lin(c), h1), lrs.mul(k, m, Co.lin(c2), h2), h)

def Color.color_lum_rises(r, g, b, r2, g2, b2, hr, hg, hb):
  +t1 = U32.to_nat((2126 * Co.lin(r) : U32))
  +t2 = U32.to_nat((7152 * Co.lin(g) : U32))
  +t3 = U32.to_nat((722 * Co.lin(b) : U32))
  +u1 = U32.to_nat((2126 * Co.lin(r2) : U32))
  +u2 = U32.to_nat((7152 * Co.lin(g2) : U32))
  +u3 = U32.to_nat((722 * Co.lin(b2) : U32))
  d1 = lrs.le(2126, 21260000, r, r2, lrs.m1(Co.lin(r), lrs.term(r)), lrs.m1(Co.lin(r2), lrs.term(r2)), hr)
  d2 = lrs.le(7152, 71520000, g, g2, lrs.m2(Co.lin(g), lrs.term(g)), lrs.m2(Co.lin(g2), lrs.term(g2)), hg)
  d3 = lrs.le(722, 7220000, b, b2, lrs.m3(Co.lin(b), lrs.term(b)), lrs.m3(Co.lin(b2), lrs.term(b2)), hb)
  %Equal.sym(Bool, U32.is_le(Co.lum(Co.Rgb{r, g, b}), Co.lum(Co.Rgb{r2, g2, b2})), Nat.is_le(U32.to_nat(Co.lum(Co.Rgb{r, g, b})), U32.to_nat(Co.lum(Co.Rgb{r2, g2, b2}))), LLr.lr.le(Co.lum(Co.Rgb{r, g, b}), Co.lum(Co.Rgb{r2, g2, b2}))) : {_ == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(Co.lum(Co.Rgb{r, g, b})), Nat.add(Nat.add(t1, t2), t3), lrs.sum(r, g, b)) : {Nat.is_le(_, U32.to_nat(Co.lum(Co.Rgb{r2, g2, b2}))) == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(Co.lum(Co.Rgb{r2, g2, b2})), Nat.add(Nat.add(u1, u2), u3), lrs.sum(r2, g2, b2)) : {Nat.is_le(Nat.add(Nat.add(t1, t2), t3), _) == True{} : Bool}
  LLr.lr.add_le(Nat.add(t1, t2), Nat.add(u1, u2), t3, u3, LLr.lr.add_le(t1, u1, t2, u2, d1, d2), d3)
