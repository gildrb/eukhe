# eukhe: the proof of LAW glob_class_fold_other
#
# PROOF: x is neither A-Z nor a-z, so the code's other case of x is x
# itself, and the folded test is (x in rs) or (x in rs).

import Base
import ../../bend/glob/items.bend as GItems
import ../../bend/glob/match.bend as GMatch
import ../../laws/glob.bend as Glob
import ./base/logic.bend as GL

# the other case of a byte that is no letter is itself
def cfo.swap(+x: U32, up: Bool, eu: {Bool.and(U32.is_le(65, x), U32.is_le(x, 90)) == up : Bool}, lo: Bool, el: {Bool.and(U32.is_le(97, x), U32.is_le(x, 122)) == lo : Bool}, h: {Bool.or(up, lo) == False{} : Bool}) -> {GMatch.swap(x) == x : U32}:
  match up:
    case True{}:
      GL.gl.tf({GMatch.swap(x) == x : U32}, h)
    case False{}:
      match lo:
        case True{}:
          GL.gl.tf({GMatch.swap(x) == x : U32}, h)
        case False{}:
          %Equal.sym(Bool, Bool.and(U32.is_le(65, x), U32.is_le(x, 90)), False{}, eu) : {GMatch.swap.up(x, _) == x : U32}
          %Equal.sym(Bool, Bool.and(U32.is_le(97, x), U32.is_le(x, 122)), False{}, el) : {GMatch.swap.lo(x, _) == x : U32}
          {==}

def cfo.set(+rs: List<&2, GItems.BR>, +x: U32, e: {GMatch.swap(x) == x : U32}) -> {GMatch.in_set(rs, x, True{}) == GMatch.in_set(rs, x, False{}) : Bool}:
  %Equal.sym(U32, GMatch.swap(x), x, e) : {Bool.or(GMatch.in_rs(rs, x), GMatch.in_rs(rs, _)) == GMatch.in_rs(rs, x) : Bool}
  GL.gl.or_idem(GMatch.in_rs(rs, x))

def cfo.go(neg: Bool, +rs: List<&2, GItems.BR>, +x: U32, e: {GMatch.swap(x) == x : U32}) -> {GMatch.bc(GItems.BSet{neg, True{}, rs}, x) == GMatch.bc(GItems.BSet{neg, False{}, rs}, x) : Bool}:
  match neg:
    case True{}:
      Equal.cong(Bool, Bool, b => Bool.not(b), GMatch.in_set(rs, x, True{}), GMatch.in_set(rs, x, False{}), cfo.set(rs, x, e))
    case False{}:
      cfo.set(rs, x, e)

def Glob.glob_class_fold_other(neg, rs, x, h):
  +up = Bool.and(U32.is_le(65, x), U32.is_le(x, 90))
  +lo = Bool.and(U32.is_le(97, x), U32.is_le(x, 122))
  cfo.go(neg, rs, x, cfo.swap(x, up, {==}, lo, {==}, h))
