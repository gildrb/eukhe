# eukhe: lemmas the luminance laws of area color share. lin(c) is the leaf
# of lin's table the low eight bits of c select (or 0 on a path that runs
# out), so a fact every leaf has (one closed check, cl.all) holds of lin(c)
# for every U32 c (cl.lin): a tree walk, not an enumeration of c.

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

# U32.is_eq is equality
def cl.eq(+a: U32, +b: U32, e: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  PWireBoolExact.wr_eq_sound(a, b, e)
