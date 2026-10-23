# eukhe: the proof of LAW tree_ffi_trailing

import Base
import ../../bend/ffi_tree.bend as Ft
import ../../bend/tree.bend as Tr
import ../../bend/wire.bend as Wr
import ../../laws/tree.bend as Tree

def Tree.tree_ffi_trailing(s, input, q, rest, h, left):
  %Equal.sym(Wr.Dec<Tr.Ask>, Ft.get_ask(input), Wr.Got{q, rest}, h) : {Ft.step.ask(s, _) == (Ft.Live{s}, Wr.err("tree: input left after the ask")) : Ft.St & String}
  %Equal.sym(Bool, Wr.end(rest), False{}, left) : {Ft.step.end(_, s, q) == (Ft.Live{s}, Wr.err("tree: input left after the ask")) : Ft.St & String}
  {==}
