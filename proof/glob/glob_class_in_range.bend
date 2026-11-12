# eukhe: the proof of LAW glob_class_in_range
#
# PROOF: by induction on the ranges before lo..hi: the class test is an or
# over the ranges, true at lo..hi.

import Base
import ../../bend/glob/items.bend as GItems
import ../../bend/glob/match.bend as GMatch
import ../../laws/glob.bend as Glob
import ./base/logic.bend as GL

def cir.go(pre: List<&2, GItems.BR>, +lo: U32, +hi: U32, +post: List<&2, GItems.BR>, +x: U32, +h: {Bool.and(U32.is_le(lo, x), U32.is_le(x, hi)) == True{} : Bool}) -> {GMatch.in_rs(List.append(&2, GItems.BR, pre, GItems.BR{lo, hi} <> post), x) == True{} : Bool}:
  match pre:
    case Nil{}:
      GL.gl.or_l(Bool.and(U32.is_le(lo, x), U32.is_le(x, hi)), GMatch.in_rs(post, x), h)
    case r <> t:
      match r:
        case GItems.BR{a, b}:
          GL.gl.or_r(Bool.and(U32.is_le(a, x), U32.is_le(x, b)), GMatch.in_rs(List.append(&2, GItems.BR, t, GItems.BR{lo, hi} <> post), x), cir.go(t, lo, hi, post, x, h))

def Glob.glob_class_in_range(pre, lo, hi, post, x, h):
  cir.go(pre, lo, hi, post, x, h)
