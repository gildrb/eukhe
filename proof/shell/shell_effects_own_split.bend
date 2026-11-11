# eukhe: the proof of LAW shell_effects_own_split
# The plain codes of xs then ys are those of xs then those of ys
# (shes.plain); a one-part step's effects are its part's (append nil).

import Base
import ../../bend/tools.bend as Tl
import ../../laws/shell.bend as Shell
import ./base.bend as LASh

def shes.add(b: Bool, c: Nat, xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {Tl.plain.add(b, c, List.append(&2, Nat, xs, ys)) == List.append(&2, Nat, Tl.plain.add(b, c, xs), ys) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def shes.plain(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {Tl.plain(List.append(&2, Nat, xs, ys)) == List.append(&2, Nat, Tl.plain(xs), Tl.plain(ys)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +c <> +t:
      %Equal.sym(List<&2, Nat>, Tl.plain(List.append(&2, Nat, t, ys)), List.append(&2, Nat, Tl.plain(t), Tl.plain(ys)), shes.plain(t, ys)) : {Tl.plain.add(Nat.is_eq(c, 6n), c, _) == List.append(&2, Nat, Tl.plain.add(Nat.is_eq(c, 6n), c, Tl.plain(t)), Tl.plain(ys)) : List<&2, Nat>}
      shes.add(Nat.is_eq(c, 6n), c, Tl.plain(t), Tl.plain(ys))

def Shell.shell_effects_own_split(xs, ys):
  %Equal.sym(List<&2, Nat>, List.append(&2, Nat, Tl.plain(List.append(&2, Nat, xs, ys)), Nil{}), Tl.plain(List.append(&2, Nat, xs, ys)), LASh.sh.app_nil(Nat, Tl.plain(List.append(&2, Nat, xs, ys)))) : {_ == List.append(&2, Nat, List.append(&2, Nat, Tl.plain(xs), Nil{}), List.append(&2, Nat, Tl.plain(ys), Nil{})) : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, List.append(&2, Nat, Tl.plain(xs), Nil{}), Tl.plain(xs), LASh.sh.app_nil(Nat, Tl.plain(xs))) : {Tl.plain(List.append(&2, Nat, xs, ys)) == List.append(&2, Nat, _, List.append(&2, Nat, Tl.plain(ys), Nil{})) : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, List.append(&2, Nat, Tl.plain(ys), Nil{}), Tl.plain(ys), LASh.sh.app_nil(Nat, Tl.plain(ys))) : {Tl.plain(List.append(&2, Nat, xs, ys)) == List.append(&2, Nat, Tl.plain(xs), _) : List<&2, Nat>}
  shes.plain(xs, ys)
