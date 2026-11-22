# eukhe: the proof of LAW elem_finds_a_member
#
# PROOF: by induction on pre. No entries before c: the first test is
# c == c. One entry before: the test of the rest holds (induction), so the
# or holds.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ./base.bend as LA

def ef.go(pre: List<&2, Nat>, +c: Nat, +post: List<&2, Nat>) -> {Tl.elem(List.append(&2, Nat, pre, c <> post), c) == True{} : Bool}:
  match pre:
    case Nil{}:
      %LA.tools.pl.eq_refl(c) : {Bool.or(_, Tl.elem(post, c)) == True{} : Bool}
      {==}
    case +q <> +pr:
      LA.shell.ps.or_tr(Nat.is_eq(q, c), Tl.elem(List.append(&2, Nat, pr, c <> post), c), ef.go(pr, c, post))

def Tools.elem_finds_a_member(pre, c, post):
  ef.go(pre, c, post)
