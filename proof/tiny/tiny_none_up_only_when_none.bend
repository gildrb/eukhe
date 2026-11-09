# eukhe: the proof of LAW tiny_none_up_only_when_none
#
# PROOF: by induction on the list. An empty list's `none_up` is True. On
# an available head the list is no models, the head, then the rest; on
# a head that is not available `none_up` of the list is that of the rest,
# which holds an available model split as pre, x, post, and the list is
# the head before pre.

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/tiny/pick.bend as Tiny
import ./base.bend as LA

def tnw.G(xs: List<&2, Nat>, up: List<&2, Nat>) -> Type:
  &pre: List<&2, Nat> -> &x: Nat -> &post: List<&2, Nat> -> {xs == List.append(&2, Nat, pre, x <> post) : List<&2, Nat>} & {Tn.elem(up, x) == True{} : Bool}

# an available model of the rest, split so: the list is the head, then
# the same split
def tnw.cons(+y: Nat, +rest: List<&2, Nat>, -up: List<&2, Nat>, w: tnw.G(rest, up)) -> tnw.G(y <> rest, up):
  (+pre, (+x, (+post, (e, el)))) = w
  (y <> pre, (x, (post, (Equal.cong(List<&2, Nat>, List<&2, Nat>, z => y <> z, rest, List.append(&2, Nat, pre, x <> post), e), el))))

def tnw.at(b: Bool, +y: Nat, +rest: List<&2, Nat>, +up: List<&2, Nat>, eb: {Tn.elem(up, y) == b : Bool}, h: {Bool.and(Bool.not(b), Tn.none_up(rest, up)) == False{} : Bool}, ih: {Tn.none_up(rest, up) == False{} : Bool} -> tnw.G(rest, up)) -> tnw.G(y <> rest, up):
  match b:
    case True{}:
      (Nil{}, (y, (rest, ({==}, eb))))
    case False{}:
      tnw.cons(y, rest, up, ih(h))

def tnw.go(xs: List<&2, Nat>, +up: List<&2, Nat>, some: {Tn.none_up(xs, up) == False{} : Bool}) -> tnw.G(xs, up):
  match xs:
    case Nil{}:
      LA.te.tf(tnw.G(Nil{}, up), some)
    case +y <> +rest:
      tnw.at(Tn.elem(up, y), y, rest, up, {==}, some, e => tnw.go(rest, up, e))

def Tiny.tiny_none_up_only_when_none(xs, up, some):
  tnw.go(xs, up, some)
