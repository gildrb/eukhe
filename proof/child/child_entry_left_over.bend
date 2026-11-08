# eukhe: the proof of LAW child_entry_left_over
#
# PROOF: the spelled request reads back stage by stage to its last stage
# (LA.lo.run), whose end check sees the char left and answers the error
# form (LA.lo.left).

import Base
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child/entry.bend as Child
import ./base.bend as LA

def Child.child_entry_left_over(r, fits, c, t):
  Equal.trans(String, FCh.ffi(Child.ch_spell_req(r, SCon{c, t})), LA.lo.fin(r, False{}), Wr.err("child: input left over"), LA.lo.run(r, SCon{c, t}, fits), LA.lo.left(r))
