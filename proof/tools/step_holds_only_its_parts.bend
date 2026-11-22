# eukhe: the proof of LAW step_holds_only_its_parts
#
# PROOF: by induction on the parts. The join of no parts holds nothing.
# The join of x then the rest is x ++ join(rest): an element of xs ++ ys
# is an element of xs or of ys (sh.elem_app_split, by induction on xs),
# and one of join(rest) is in some list of rest (induction).

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ./base.bend as LA

# or(a, b) holds, and b gives d: or(a, d) holds
def sh.or_mono(a: Bool, +b: Bool, +d: Bool, h: {Bool.or(a, b) == True{} : Bool}, f: {b == True{} : Bool} -> {d == True{} : Bool}) -> {Bool.or(a, d) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      f(h)

# the head test b of an element of xr ++ ys: either b, or the element is
# in xr or in ys
def sh.split_head(b: Bool, +xr: List<&2, Nat>, +ys: List<&2, Nat>, +c: Nat, h: {Bool.or(b, Tl.elem(List.append(&2, Nat, xr, ys), c)) == True{} : Bool}, ih: {Tl.elem(List.append(&2, Nat, xr, ys), c) == True{} : Bool} -> {Bool.or(Tl.elem(xr, c), Tl.elem(ys, c)) == True{} : Bool}) -> {Bool.or(Bool.or(b, Tl.elem(xr, c)), Tl.elem(ys, c)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih(h)

# an element of xs ++ ys is an element of xs or of ys
def sh.elem_app_split(xs: List<&2, Nat>, +ys: List<&2, Nat>, +c: Nat, h: {Tl.elem(List.append(&2, Nat, xs, ys), c) == True{} : Bool}) -> {Bool.or(Tl.elem(xs, c), Tl.elem(ys, c)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +x <> +xr:
      sh.split_head(Nat.is_eq(x, c), xr, ys, c, h, k => sh.elem_app_split(xr, ys, c, k))

def sh.only_its_parts(xs: List<&2, List<&2, Nat>>, +c: Nat, has: {Tl.elem(Tl.join(xs), c) == True{} : Bool}) -> {Tools.tools_some_has(xs, c) == True{} : Bool}:
  match xs:
    case Nil{}:
      LA.shell.ps.absurdF({False{} == True{} : Bool}, has)
    case +x <> +xr:
      sh.or_mono(Tl.elem(x, c), Tl.elem(Tl.join(xr), c), Tools.tools_some_has(xr, c), sh.elem_app_split(x, Tl.join(xr), c, has), k => sh.only_its_parts(xr, c, k))

def Tools.step_holds_only_its_parts(xs, c, has):
  sh.only_its_parts(xs, c, has)
