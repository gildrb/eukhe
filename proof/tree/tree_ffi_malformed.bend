# eukhe: the proof of LAW tree_ffi_malformed

import Base
import ../../bend/ffi_tree.bend as Ft
import ../../bend/tree.bend as Tr
import ../../bend/wire.bend as Wr
import ../../laws/tree.bend as Tree

def Tree.tree_ffi_malformed(s, input, h):
  %Equal.sym(Wr.Dec<Tr.Ask>, Ft.get_ask(input), Wr.Bad{}, h) : {Ft.step.ask(s, _) == (Ft.Live{s}, Wr.err("tree: malformed ask")) : Ft.St & String}
  {==}
