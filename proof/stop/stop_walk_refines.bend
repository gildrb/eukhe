# eukhe: the proof of LAW stop_walk_refines
#
# PROOF: case by case, the code's walk is the spec's decision (LA.stb.walk).

import Base
import ../../bend/stop.bend as S
import ./base.bend as LA
import ../../laws/stop.bend as Stop

def Stop.stop_walk_refines(f):
  LA.stb.walk(f)
