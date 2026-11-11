# eukhe: the proof of LAW tool_surface_quit_drops_every_copy
# By induction on the tools before the copy: a copy at the head is
# dropped (Nat.is_eq(t, t)); every other head is dropped or kept alike on
# both sides.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tool_surface.bend as ToolSurface
import ./base.bend as LATs

# a head y with test b: both lists drop it, or both keep it
def tsd.head(b: Bool, +y: Nat, -a: List<&2, Nat>, -c: List<&2, Nat>, +t: Nat, ih: {Tl.drop(a, t) == Tl.drop(c, t) : List<&2, Nat>}) -> {Tl.drop.go(y <> a, t, b) == Tl.drop.go(y <> c, t, b) : List<&2, Nat>}:
  match b:
    case True{}:
      ih
    case False{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => y <> z, Tl.drop(a, t), Tl.drop(c, t), ih)

def tsd.copy(pre: List<&2, Nat>, +post: List<&2, Nat>, +t: Nat) -> {Tl.drop(List.append(&2, Nat, pre, t <> post), t) == Tl.drop(List.append(&2, Nat, pre, post), t) : List<&2, Nat>}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(t, t), True{}, LATs.ts.eq_refl(t)) : {Tl.drop.go(t <> post, t, _) == Tl.drop(post, t) : List<&2, Nat>}
      {==}
    case +y <> pr:
      tsd.head(Nat.is_eq(y, t), y, List.append(&2, Nat, pr, t <> post), List.append(&2, Nat, pr, post), t, tsd.copy(pr, post, t))

def ToolSurface.tool_surface_quit_drops_every_copy(r, pre, post, x, t):
  tsd.copy(pre, post, t)
