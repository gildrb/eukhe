# eukhe: the proof of LAW tree_ffi_open_left_over
#
# PROOF: halves that fit read back with the rest untouched
# (wire_list_round_trip); a rest with a char is not the end, so the open
# is refused with the left-over error.

import Base
import ../../bend/ffi_tree.bend as Ft
import ../../bend/wire.bend as Wr
import ../../laws/tree.bend as Tree
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire

def Tree.tree_ffi_open_left_over(hs, fits, c, t):
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, hs, SCon{c, t})), Wr.Got{hs, SCon{c, t}}, Wire.wire_list_round_trip(hs, SCon{c, t}, fits)) : {Ft.open.go(_) == (Ft.Shut{}, Wr.err("tree: input left after the halves")) : Ft.St & String}
  {==}
