# eukhe: the proof of LAW tiny_elem_finds
#
# PROOF: by induction on the models before x: at x the test of the head
# is Nat.is_eq(x, x), which is True; past another head the rest finds x,
# and an `or` with True is True.

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/tiny/pick.bend as Tiny
import ./base.bend as LA

def tef.or_t(b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def tef.go(pre: List<&2, Nat>, +x: Nat, +post: List<&2, Nat>) -> {Tn.elem(List.append(&2, Nat, pre, x <> post), x) == True{} : Bool}:
  match pre:
    case Nil{}:
      %LA.pn.eq_refl(x) : {Bool.or(_, Tn.elem(post, x)) == True{} : Bool}
      {==}
    case +y <> +rest:
      %Equal.sym(Bool, Tn.elem(List.append(&2, Nat, rest, x <> post), x), True{}, tef.go(rest, x, post)) : {Bool.or(Nat.is_eq(y, x), _) == True{} : Bool}
      tef.or_t(Nat.is_eq(y, x))

def Tiny.tiny_elem_finds(pre, x, post):
  tef.go(pre, x, post)
