# eukhe: lemmas the luminance laws of area color share. lin(c) is the leaf
# of lin's table the low eight bits of c select (or 0 on a path that runs
# out), so a fact every leaf has (a closed check per part of the table,
# cl.table) holds of lin(c) for every U32 c (cl.lin): a tree walk, not an
# enumeration of c.

import Base
import ../../../bend/color.bend as Co
import ../../base/logic/bool.bend as LLogicBool
import ../../wire/wire_bool_exact.bend as PWireBoolExact
import ../color_contrast_exact_wide/bin.bend as LCb

# The facts a leaf is checked for
# -------------------------------

type cl.Q is Data:
  ClGrey{}
  ClOrder{}
  ClTerm{}

# the product k·v on U32 is the product of the values (on bits, cb.mul)
# and stays at most m
def cl.mterm(+k: U32, m: U32, +v: U32) -> Bool:
  Bool.and(Cmp.is_eq(LCb.cb.cmp(LCb.cb.u32((k * v : U32)), LCb.cb.mul(LCb.cb.u32(k), LCb.cb.u32(v)))), U32.is_le((k * v : U32), m))

# the fact q of the linear value v
def cl.ok(q: cl.Q, +v: U32) -> Bool:
  match q:
    case ClGrey{}:
      U32.is_eq((2126 * v + 7152 * v + 722 * v : U32), (10000 * v : U32))
    case ClOrder{}:
      Bool.and(U32.is_le((2126 * Co.lin(0) + 7152 * Co.lin(0) + 722 * v : U32), (2126 * v + 7152 * Co.lin(0) + 722 * Co.lin(0) : U32)), U32.is_le((2126 * v + 7152 * Co.lin(0) + 722 * Co.lin(0) : U32), (2126 * Co.lin(0) + 7152 * v + 722 * Co.lin(0) : U32)))
    case ClTerm{}:
      Bool.and(cl.mterm(2126, 21260000, v), Bool.and(cl.mterm(7152, 71520000, v), cl.mterm(722, 7220000, v)))

# every leaf of t has the fact q
def cl.all(+q: cl.Q, t: Co.LinT) -> Bool:
  match t:
    case Co.Leaf{+v}:
      cl.ok(q, v)
    case Co.Node{lo, hi}:
      Bool.and(cl.all(q, lo), cl.all(q, hi))

# The tree walk
# -------------

# the leaf any path selects has the fact every leaf has (0 on a path that
# runs out has it too)
def cl.at(+q: cl.Q, t: Co.LinT, bs: List<&2, Bool>, z: {cl.ok(q, 0) == True{} : Bool}, h: {cl.all(q, t) == True{} : Bool}) -> {cl.ok(q, Co.lin.go(t, bs)) == True{} : Bool}:
  match t:
    case Co.Leaf{v}:
      h
    case Co.Node{+lo, +hi}:
      match bs:
        case Nil{}:
          z
        case Con{b, rest}:
          match b:
            case True{}:
              cl.at(q, hi, rest, z, LLogicBool.wr_and_r(cl.all(q, lo), cl.all(q, hi), h))
            case False{}:
              cl.at(q, lo, rest, z, LLogicBool.wr_and_l(cl.all(q, lo), cl.all(q, hi), h))

# the linear value of every U32 has the fact q, once every leaf of lin's
# table has it
def cl.lin(+q: cl.Q, +c: U32, z: {cl.ok(q, 0) == True{} : Bool}, h: {cl.all(q, Co.lin.table()) == True{} : Bool}) -> {cl.ok(q, Co.lin(c)) == True{} : Bool}:
  cl.at(q, Co.lin.table(), Co.bits(c), z, h)

# The closed check, by part
# -------------------------
# lin's table is sixteen parts (Co.lin.t0 .. Co.lin.t15): every leaf of
# the table has the fact once every leaf of each part has it, so each
# part is its own closed check (the whole table at once runs the checker
# out of fuel).

def cl.node(+q: cl.Q, +lo: Co.LinT, +hi: Co.LinT, hl: {cl.all(q, lo) == True{} : Bool}, hh: {cl.all(q, hi) == True{} : Bool}) -> {cl.all(q, Co.Node{lo, hi}) == True{} : Bool}:
  %Equal.sym(Bool, cl.all(q, lo), True{}, hl) : {Bool.and(_, cl.all(q, hi)) == True{} : Bool}
  hh

def cl.quad(+q: cl.Q, +a: Co.LinT, +b: Co.LinT, +c: Co.LinT, +d: Co.LinT, ha: {cl.all(q, a) == True{} : Bool}, hb: {cl.all(q, b) == True{} : Bool}, hc: {cl.all(q, c) == True{} : Bool}, hd: {cl.all(q, d) == True{} : Bool}) -> {cl.all(q, Co.Node{Co.Node{a, b}, Co.Node{c, d}}) == True{} : Bool}:
  cl.node(q, Co.Node{a, b}, Co.Node{c, d}, cl.node(q, a, b, ha, hb), cl.node(q, c, d, hc, hd))

def cl.table(+q: cl.Q, h0: {cl.all(q, Co.lin.t0()) == True{} : Bool}, h1: {cl.all(q, Co.lin.t1()) == True{} : Bool}, h2: {cl.all(q, Co.lin.t2()) == True{} : Bool}, h3: {cl.all(q, Co.lin.t3()) == True{} : Bool}, h4: {cl.all(q, Co.lin.t4()) == True{} : Bool}, h5: {cl.all(q, Co.lin.t5()) == True{} : Bool}, h6: {cl.all(q, Co.lin.t6()) == True{} : Bool}, h7: {cl.all(q, Co.lin.t7()) == True{} : Bool}, h8: {cl.all(q, Co.lin.t8()) == True{} : Bool}, h9: {cl.all(q, Co.lin.t9()) == True{} : Bool}, h10: {cl.all(q, Co.lin.t10()) == True{} : Bool}, h11: {cl.all(q, Co.lin.t11()) == True{} : Bool}, h12: {cl.all(q, Co.lin.t12()) == True{} : Bool}, h13: {cl.all(q, Co.lin.t13()) == True{} : Bool}, h14: {cl.all(q, Co.lin.t14()) == True{} : Bool}, h15: {cl.all(q, Co.lin.t15()) == True{} : Bool}) -> {cl.all(q, Co.lin.table()) == True{} : Bool}:
  +a = {Co.Node{Co.Node{Co.lin.t0(), Co.lin.t1()}, Co.Node{Co.lin.t2(), Co.lin.t3()}} : Co.LinT}
  +b = {Co.Node{Co.Node{Co.lin.t4(), Co.lin.t5()}, Co.Node{Co.lin.t6(), Co.lin.t7()}} : Co.LinT}
  +c = {Co.Node{Co.Node{Co.lin.t8(), Co.lin.t9()}, Co.Node{Co.lin.t10(), Co.lin.t11()}} : Co.LinT}
  +d = {Co.Node{Co.Node{Co.lin.t12(), Co.lin.t13()}, Co.Node{Co.lin.t14(), Co.lin.t15()}} : Co.LinT}
  cl.quad(q, a, b, c, d, cl.quad(q, Co.lin.t0(), Co.lin.t1(), Co.lin.t2(), Co.lin.t3(), h0, h1, h2, h3), cl.quad(q, Co.lin.t4(), Co.lin.t5(), Co.lin.t6(), Co.lin.t7(), h4, h5, h6, h7), cl.quad(q, Co.lin.t8(), Co.lin.t9(), Co.lin.t10(), Co.lin.t11(), h8, h9, h10, h11), cl.quad(q, Co.lin.t12(), Co.lin.t13(), Co.lin.t14(), Co.lin.t15(), h12, h13, h14, h15))

# U32.is_eq is equality
def cl.eq(+a: U32, +b: U32, e: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  PWireBoolExact.wr_eq_sound(a, b, e)
