# eukhe: the proof of LAW tiny_elem_only_members
#
# PROOF: by induction on the list. An empty list holds nothing (elem is
# False). On a head equal to x (Nat.is_eq is sound: teo.eq) the list is
# no models, x, then the rest; on another head the rest holds x, split
# as pre, x, post, and the list is the head before pre.

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/tiny/pick.bend as Tiny
import ./base.bend as LA

# Nat.is_eq answers True only for equal numbers
def teo.eq(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LA.tiny.pn.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      LA.tiny.pn.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, teo.eq(p, q, h))

def teo.G(xs: List<&2, Nat>, x: Nat) -> Type:
  &pre: List<&2, Nat> -> &post: List<&2, Nat> -> {xs == List.append(&2, Nat, pre, x <> post) : List<&2, Nat>}

# x in the rest, split so: the list is the head, then the same split
def teo.cons(+y: Nat, +rest: List<&2, Nat>, +x: Nat, w: teo.G(rest, x)) -> teo.G(y <> rest, x):
  (+pre, (+post, e)) = w
  (y <> pre, (post, Equal.cong(List<&2, Nat>, List<&2, Nat>, z => y <> z, rest, List.append(&2, Nat, pre, x <> post), e)))

def teo.at(b: Bool, +y: Nat, +rest: List<&2, Nat>, +x: Nat, eb: {Nat.is_eq(y, x) == b : Bool}, h: {Bool.or(b, Tn.elem(rest, x)) == True{} : Bool}, ih: {Tn.elem(rest, x) == True{} : Bool} -> teo.G(rest, x)) -> teo.G(y <> rest, x):
  match b:
    case True{}:
      +ey = teo.eq(y, x, eb)
      (Nil{}, (rest, Equal.cong(Nat, List<&2, Nat>, z => z <> rest, y, x, ey)))
    case False{}:
      teo.cons(y, rest, x, ih(h))

def teo.go(xs: List<&2, Nat>, +x: Nat, hit: {Tn.elem(xs, x) == True{} : Bool}) -> teo.G(xs, x):
  match xs:
    case Nil{}:
      LA.tiny.pn.absurdF(teo.G(Nil{}, x), hit)
    case +y <> +rest:
      teo.at(Nat.is_eq(y, x), y, rest, x, {==}, hit, e => teo.go(rest, x, e))

def Tiny.tiny_elem_only_members(xs, x, hit):
  teo.go(xs, x, hit)
