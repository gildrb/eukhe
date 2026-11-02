# eukhe: the proof of LAW tree_ffi_open_spec
#
# PROOF: the open is tt_open.of on the halves read (tree_ffi_open_exact);
# its opened core is the core fed the empty journal.

import Base
import ../../bend/ffi_tree.bend as Ft
import ../../bend/tree.bend as Tr
import ../../bend/wire.bend as Wr
import ../../laws/tree.bend as Tree
import ./tree_ffi_open_exact.bend as PTreeFfiOpenExact

def to.of(d: Wr.Dec<List<&2, Nat>>) -> {Tree.tt_open.of(d) == Tree.ts_open.of(d) : Ft.St & String}:
  match d:
    case Wr.Got{hs, r}:
      match r:
        case SNil{}:
          {==}
        case SCon{c, t}:
          {==}
    case Wr.Bad{}:
      {==}

def Tree.tree_ffi_open_spec(input):
  Equal.trans(Ft.St & String, Ft.open(input), Tree.tt_open.of(Wr.get_list(~Nat, ~Wr.get_nat, input)), Tree.ts_open.of(Wr.get_list(~Nat, ~Wr.get_nat, input)), Tree.tree_ffi_open_exact(input), to.of(Wr.get_list(~Nat, ~Wr.get_nat, input)))
