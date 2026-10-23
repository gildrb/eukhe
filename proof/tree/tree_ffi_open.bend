# eukhe: the proof of LAW tree_ffi_open

import Base
import ../../bend/ffi_tree.bend as Ft
import ../../bend/tree.bend as Tr
import ../../bend/wire.bend as Wr
import ../../laws/tree.bend as Tree
import ../../laws/wire.bend as Wire
import ../base.bend as L

def Tree.tree_ffi_open(hs, h):
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, hs, "")), Wr.Got{hs, ""}, Wire.wire_list_round_trip(hs, "", h)) : {Ft.open.go(_) == (Ft.Live{Tr.core.start(hs)}, "") : Ft.St & String}
  {==}
