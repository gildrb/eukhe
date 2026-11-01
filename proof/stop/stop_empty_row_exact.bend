# eukhe: the proof of LAW stop_empty_row_exact
#
# PROOF: the count is the spec's row kind by kind (stb.empty_row).

import Base
import ./base.bend as LA
import ../../laws/stop.bend as Stop

def Stop.stop_empty_row_exact(k, row):
  LA.stb.empty_row(k, row)
