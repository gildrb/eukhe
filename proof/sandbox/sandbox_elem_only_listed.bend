# eukhe: the proof of LAW sandbox_elem_only_listed
#
# PROOF: by induction on the list, deciding its first value's test
# (peo.at): a first value that is x splits the list there (LA.px.eq_true);
# otherwise the rest holds x (peo.or_r) and its split, with the first value
# put in front.

import Base
import ../../bend/sandbox.bend as Sb
import ../../laws/sandbox.bend as Sandbox
import ./base.bend as LA

def peo.G(xs: List<&2, Nat>, +x: Nat) -> Type:
  &pre: List<&2, Nat> -> &post: List<&2, Nat> -> {xs == List.append(&2, Nat, pre, x <> post) : List<&2, Nat>}

# the test of the first value of xs (False for none)
def peo.at(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Nat.is_eq(y, x)

# an or that holds with a false left side holds by its right side
def peo.or_r(a: Bool, -b: Bool, ea: {a == False{} : Bool}, h: {Bool.or(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      LA.px.absurdF({b == True{} : Bool}, Equal.sym(Bool, True{}, False{}, ea))
    case False{}:
      h

def peo.cons(+y: Nat, +rest: List<&2, Nat>, +x: Nat, r: peo.G(rest, x)) -> peo.G(y <> rest, x):
  (pre, r1) = r
  (post, e) = r1
  (y <> pre, (post, Equal.cong(List<&2, Nat>, List<&2, Nat>, z => y <> z, rest, List.append(&2, Nat, pre, x <> post), e)))

def peo.go(xs: List<&2, Nat>, +x: Nat, t: Bool, et: {peo.at(xs, x) == t : Bool}, h: {Sb.elem(xs, x) == True{} : Bool}) -> peo.G(xs, x):
  match xs:
    case Nil{}:
      LA.px.absurdF(peo.G(Nil{}, x), h)
    case +y <> +rest:
      match t:
        case True{}:
          (Nil{}, (rest, Equal.cong(Nat, List<&2, Nat>, z => z <> rest, y, x, LA.px.eq_true(y, x, et))))
        case False{}:
          peo.cons(y, rest, x, peo.go(rest, x, peo.at(rest, x), {==}, peo.or_r(Nat.is_eq(y, x), Sb.elem(rest, x), et, h)))

def Sandbox.sandbox_elem_only_listed(xs, x, h):
  peo.go(xs, x, peo.at(xs, x), {==}, h)
