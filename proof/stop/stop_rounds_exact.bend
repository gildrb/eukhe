# eukhe: the proof of LAW stop_rounds_exact
#
# PROOF: the code's round note is the spec's once the threshold and the rounds left are split (LA.stb.rounds).

import Base
import ../../bend/stop.bend as S
import ./base.bend as LA
import ../../laws/stop.bend as Stop

def Stop.stop_rounds_exact(m, d):
  LA.stb.rounds(m, d)
