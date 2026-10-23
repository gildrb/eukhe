# eukhe: the proof of LAW tree_ffi_open

import Base
import ../../bend/tree.bend as Tr
import ../../bend/wire.bend as Wr
import ../../bend/ffi_tree.bend as Ft
import ../../LAWS.bend as Laws
import ../base.bend as L

def Laws.tree_ffi_open(hs, h):
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, hs, "")), Wr.Got{hs, ""}, Laws.wire_list_round_trip(hs, "", h)) : {Ft.open.go(_) == (Ft.Live{Tr.core.start(hs)}, "") : Ft.St & String}
  {==}
