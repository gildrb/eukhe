# eukhe: the proof of LAW sandbox_elem_listed
#
# PROOF: by induction on the values before x: at x, Nat.is_eq(x, x) is
# true (LA.px.eq_refl); a value before it leaves an or whose right side,
# the rest's answer, is already true.

import Base
import ../../bend/sandbox.bend as Sb
import ../../laws/sandbox.bend as Sandbox
import ./base.bend as LA

def pel.or_true(b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pel.go(pre: List<&2, Nat>, +x: Nat, +post: List<&2, Nat>) -> {Sb.elem(List.append(&2, Nat, pre, x <> post), x) == True{} : Bool}:
  match pre:
    case Nil{}:
      %LA.px.eq_refl(x) : {Bool.or(_, Sb.elem(post, x)) == True{} : Bool}
      {==}
    case +y <> +rest:
      %Equal.sym(Bool, Sb.elem(List.append(&2, Nat, rest, x <> post), x), True{}, pel.go(rest, x, post)) : {Bool.or(Nat.is_eq(y, x), _) == True{} : Bool}
      pel.or_true(Nat.is_eq(y, x))

def Sandbox.sandbox_elem_listed(pre, x, post):
  pel.go(pre, x, post)
