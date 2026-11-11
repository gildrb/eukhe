# eukhe: the proof of LAW stop_verdict_exact
#
# PROOF: per Director, the code's verdict is the spec's (LA.stb.verdict).

import Base
import ../../bend/stop.bend as S
import ./base.bend as LA
import ../../laws/stop.bend as Stop

def Stop.stop_verdict_exact(d, f):
  LA.stb.verdict(d, f)
