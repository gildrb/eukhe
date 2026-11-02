# eukhe: the proof of LAW tree_ffi_open_exact
#
# PROOF: the open reads the halves with the wire's list reader, as the
# spec does; each answer of that reader computes to the spec's.

import Base
import ../../bend/ffi_tree.bend as Ft
import ../../bend/tree.bend as Tr
import ../../bend/wire.bend as Wr
import ../../laws/tree.bend as Tree

def tox.go(d: Wr.Dec<List<&2, Nat>>) -> {Ft.open.go(d) == Tree.tt_open.of(d) : Ft.St & String}:
  match d:
    case Wr.Got{hs, r}:
      match r:
        case SNil{}:
          {==}
        case SCon{c, t}:
          {==}
    case Wr.Bad{}:
      {==}

def Tree.tree_ffi_open_exact(input):
  tox.go(Wr.get_list(~Nat, ~Wr.get_nat, input))
