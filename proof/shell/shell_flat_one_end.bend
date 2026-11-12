# eukhe: the proof of LAW shell_flat_one_end
# One list spelled before rest is one item per item, then the end mark,
# then rest: its length (shfe.len) and the place after its items
# (shfe.end).

import Base
import ../../bend/wire_flat.bend as Fl
import ../../laws/shell.bend as Shell

def shfe.len(xs: List<&2, Nat>) -> {List.length(&2, Nat, Fl.one(xs, Nil{})) == 1n+List.length(&2, Nat, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, Nat, Fl.one(t, Nil{})), 1n+List.length(&2, Nat, t), shfe.len(t))

def shfe.end(xs: List<&2, Nat>) -> {List.get(&2, Nat, Fl.one(xs, Nil{}), List.length(&2, Nat, xs)) == Some{0n} : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      shfe.end(t)

def Shell.shell_flat_one_end(xs):
  (shfe.len(xs), shfe.end(xs))
