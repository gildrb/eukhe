# eukhe: the proof of LAW shell_flat_concat
# A list spelled before rest then more is that list spelled before rest
# ++ more (shfc.one); then list by list.

import Base
import ../../bend/wire_flat.bend as Fl
import ../../laws/shell.bend as Shell

def shfc.one(xs: List<&2, Nat>, r: List<&2, Nat>, +zs: List<&2, Nat>) -> {List.append(&2, Nat, Fl.one(xs, r), zs) == Fl.one(xs, List.append(&2, Nat, r, zs)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %Equal.sym(List<&2, Nat>, List.append(&2, Nat, Fl.one(t, r), zs), Fl.one(t, List.append(&2, Nat, r, zs)), shfc.one(t, r, zs)) : {{1n+x : Nat} <> _ == {1n+x : Nat} <> Fl.one(t, List.append(&2, Nat, r, zs)) : List<&2, Nat>}
      {==}

def Shell.shell_flat_concat(xss, yss):
  match xss:
    case Nil{}:
      {==}
    case +xs <> +t:
      %Equal.sym(List<&2, Nat>, Fl.flat(List.append(&2, List<&2, Nat>, t, yss)), List.append(&2, Nat, Fl.flat(t), Fl.flat(yss)), Shell.shell_flat_concat(t, yss)) : {Fl.one(xs, _) == List.append(&2, Nat, Fl.one(xs, Fl.flat(t)), Fl.flat(yss)) : List<&2, Nat>}
      Equal.sym(List<&2, Nat>, List.append(&2, Nat, Fl.one(xs, Fl.flat(t)), Fl.flat(yss)), Fl.one(xs, List.append(&2, Nat, Fl.flat(t), Fl.flat(yss))), shfc.one(xs, Fl.flat(t), Fl.flat(yss)))
