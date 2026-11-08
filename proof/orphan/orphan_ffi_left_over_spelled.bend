# eukhe: the proof of LAW orphan_ffi_left_over_spelled
#
# PROOF: the spelled request reads back field by field (LA.oe.run), whose
# end check sees the char left and answers the error form.

import Base
import ../../laws/orphan.bend as Orphan
import ./base.bend as LA

def Orphan.orphan_ffi_left_over_spelled(q, fits, c, t):
  LA.oe.run(q, SCon{c, t}, fits)
