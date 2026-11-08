# eukhe: the proof of LAW afw_left_over_spelled
#
# PROOF: the spelled request reads back (LA.pfs.run), and the end check
# sees the char left and answers the error form.

import Base
import ../../laws/aux_fallback/wire.bend as AuxFallbackWire
import ./base.bend as LA

def AuxFallbackWire.afw_left_over_spelled(x, fits, c, t):
  LA.pfs.run(x, SCon{c, t}, fits)
