# eukhe: the proof of LAW stop_long_row_exact
#
# PROOF: the count is the spec's row kind by kind (stb.long_row).

import Base
import ./base.bend as LA
import ../../laws/stop.bend as Stop

def Stop.stop_long_row_exact(k, row):
  LA.stb.long_row(k, row)
