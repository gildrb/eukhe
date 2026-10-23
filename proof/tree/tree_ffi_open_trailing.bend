# eukhe: the proof of LAW tree_ffi_open_trailing

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_tree.bend as Ft
import ../../LAWS.bend as Laws

def Laws.tree_ffi_open_trailing(input, hs, rest, h, left):
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, input), Wr.Got{hs, rest}, h) : {Ft.open.go(_) == (Ft.Shut{}, Wr.err("tree: input left after the halves")) : Ft.St & String}
  %Equal.sym(Bool, Wr.end(rest), False{}, left) : {Ft.open.end(_, hs) == (Ft.Shut{}, Wr.err("tree: input left after the halves")) : Ft.St & String}
  {==}
