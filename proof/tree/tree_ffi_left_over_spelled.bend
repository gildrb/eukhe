# eukhe: the proof of LAW tree_ffi_left_over_spelled
#
# PROOF: the laws' spelling of an ask is the entry's (ts.ask), which reads
# back with the rest untouched (tf.ask_rt); a rest with a char is not the
# end, so the step keeps the core and answers the left-over error.

import Base
import ../../bend/ffi_tree.bend as Ft
import ../../bend/tree.bend as Tr
import ../../bend/wire.bend as Wr
import ../../laws/tree.bend as Tree
import ./base/spell.bend as LASpell
import ./base/wire.bend as LAWire

def Tree.tree_ffi_left_over_spelled(s, q, fits, c, t):
  %LASpell.ts.ask(q, SCon{c, t}) : {Ft.step(Ft.Live{s}, _) == (Ft.Live{s}, Wr.err("tree: input left after the ask")) : Ft.St & String}
  %Equal.sym(Wr.Dec<Tr.Ask>, Ft.get_ask(Ft.put_ask(q, SCon{c, t})), Wr.Got{q, SCon{c, t}}, LAWire.tf.ask_rt(q, SCon{c, t}, fits)) : {Ft.step.ask(s, _) == (Ft.Live{s}, Wr.err("tree: input left after the ask")) : Ft.St & String}
  {==}
