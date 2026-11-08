# eukhe: the proof of LAW shell_flat_spelled
# Fl.one and the spec's sh_flat_one agree item by item; then list by list.

import Base
import ../../bend/wire_flat.bend as Fl
import ../../laws/shell.bend as Shell

def shfs.one(xs: List<&2, Nat>, +rest: List<&2, Nat>) -> {Fl.one(xs, rest) == Shell.sh_flat_one(xs, rest) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %shfs.one(t, rest) : {{1n+x : Nat} <> Fl.one(t, rest) == {1n+x : Nat} <> _ : List<&2, Nat>}
      {==}

def Shell.shell_flat_spelled(xss):
  match xss:
    case Nil{}:
      {==}
    case +xs <> +t:
      %Shell.shell_flat_spelled(t) : {Fl.one(xs, Fl.flat(t)) == Shell.sh_flat_one(xs, _) : List<&2, Nat>}
      shfs.one(xs, Fl.flat(t))
