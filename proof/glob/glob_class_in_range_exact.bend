# eukhe: the proof of LAW glob_class_in_range_exact
#
# PROOF: by induction on the ranges: the class test is an or over them; a
# true one is found at the head (pre empty) or in the rest (the head put
# before pre).

import Base
import ../../bend/glob/items.bend as GItems
import ../../bend/glob/match.bend as GMatch
import ../../laws/glob.bend as Glob
import ./base/logic.bend as GL

# x is within a range of rs, where it says
def cie.Ex(rs: List<&2, GItems.BR>, x: U32) -> Type:
  &pre: List<&2, GItems.BR> -> &lo: U32 -> &hi: U32 -> &post: List<&2, GItems.BR> -> ({rs == List.append(&2, GItems.BR, pre, GItems.BR{lo, hi} <> post) : List<&2, GItems.BR>} & {Bool.and(U32.is_le(lo, x), U32.is_le(x, hi)) == True{} : Bool})

def cie.cons(+r: GItems.BR, -t: List<&2, GItems.BR>, -x: U32, e: cie.Ex(t, x)) -> cie.Ex(r <> t, x):
  (pre, e1) = e
  (lo, e2) = e1
  (hi, e3) = e2
  (post, pf) = e3
  (eq, ok) = pf
  (r <> pre, (lo, (hi, (post, (Equal.cong(List<&2, GItems.BR>, List<&2, GItems.BR>, z => r <> z, t, List.append(&2, GItems.BR, pre, GItems.BR{lo, hi} <> post), eq), ok)))))

def cie.step(+a: U32, +b: U32, +t: List<&2, GItems.BR>, +x: U32, q: Bool, eq: {Bool.and(U32.is_le(a, x), U32.is_le(x, b)) == q : Bool}, h: {Bool.or(q, GMatch.in_rs(t, x)) == True{} : Bool}, ih: {GMatch.in_rs(t, x) == True{} : Bool} -> cie.Ex(t, x)) -> cie.Ex(GItems.BR{a, b} <> t, x):
  match q:
    case True{}:
      (Nil{}, (a, (b, (t, ({==}, eq)))))
    case False{}:
      cie.cons(GItems.BR{a, b}, t, x, ih(h))

def cie.go(rs: List<&2, GItems.BR>, +x: U32, h: {GMatch.in_rs(rs, x) == True{} : Bool}) -> cie.Ex(rs, x):
  match rs:
    case Nil{}:
      GL.gl.ft(cie.Ex(Nil{}, x), h)
    case r <> +t:
      match r:
        case GItems.BR{+a, +b}:
          cie.step(a, b, t, x, Bool.and(U32.is_le(a, x), U32.is_le(x, b)), {==}, h, hh => cie.go(t, x, hh))

def Glob.glob_class_in_range_exact(rs, x, h):
  cie.go(rs, x, h)
