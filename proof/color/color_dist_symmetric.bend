# eukhe: the proof of LAW color_dist_symmetric: the distance of two channels
# is the same either way round (cds.absd: the order one way is the flip of
# the other, and two channels that compare equal are one value), so each
# of the three terms is

import Base
import ../../bend/color.bend as Co
import ../../laws/color/math.bend as Color
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ./base/word.bend as LCw

def cds.absd.at(p: Cmp, +a: U32, +b: U32, eq: {p == EQ{} : Cmp} -> {a == b : U32}) -> {Co.sel(Cmp.is_ge(p), (a - b : U32), (b - a : U32)) == Co.sel(Cmp.is_ge(LCw.cw.flip(p)), (b - a : U32), (a - b : U32)) : U32}:
  match p:
    case LT{}:
      {==}
    case EQ{}:
      %eq({==}) : {(a - _ : U32) == (_ - a : U32) : U32}
      {==}
    case GT{}:
      {==}

# the distance of two channels, either way round
def cds.absd(+a: U32, +b: U32) -> {Co.absdiff(a, b) == Co.absdiff(b, a) : U32}:
  %Equal.sym(Cmp, U32.cmp(b, a), LCw.cw.flip(U32.cmp(a, b)), LCw.cw.anti(b, a)) : {Co.absdiff(a, b) == Co.sel(Cmp.is_ge(_), (b - a : U32), (a - b : U32)) : U32}
  cds.absd.at(U32.cmp(a, b), a, b, PWireBoolExact.wr_cmp_eq(a, b))

def Color.color_dist_symmetric(a, b):
  match a b:
    case Co.Rgb{+ar, +ag, +ab} Co.Rgb{+br, +bg, +bb}:
      %cds.absd(ar, br) : {Co.dist(Co.Rgb{ar, ag, ab}, Co.Rgb{br, bg, bb}) == (299 * Co.sq(_) + 587 * Co.sq(Co.absdiff(bg, ag)) + 114 * Co.sq(Co.absdiff(bb, ab)) : U32) : U32}
      %cds.absd(ag, bg) : {Co.dist(Co.Rgb{ar, ag, ab}, Co.Rgb{br, bg, bb}) == (299 * Co.sq(Co.absdiff(ar, br)) + 587 * Co.sq(_) + 114 * Co.sq(Co.absdiff(bb, ab)) : U32) : U32}
      %cds.absd(ab, bb) : {Co.dist(Co.Rgb{ar, ag, ab}, Co.Rgb{br, bg, bb}) == (299 * Co.sq(Co.absdiff(ar, br)) + 587 * Co.sq(Co.absdiff(ag, bg)) + 114 * Co.sq(_) : U32) : U32}
      {==}
