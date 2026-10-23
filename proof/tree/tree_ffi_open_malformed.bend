# eukhe: the proof of LAW tree_ffi_open_malformed

import Base
import ../../bend/ffi_tree.bend as Ft
import ../../bend/wire.bend as Wr
import ../../laws/tree.bend as Tree

def Tree.tree_ffi_open_malformed(input, h):
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, input), Wr.Bad{}, h) : {Ft.open.go(_) == (Ft.Shut{}, Wr.err("tree: malformed halves")) : Ft.St & String}
  {==}
