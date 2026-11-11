# eukhe: the proof of LAW orphan_starts_live
#
# PROOF: with no event the run is its start state, by evaluation.

import Base
import ../../bend/orphan.bend as Or
import ../../laws/orphan.bend as Orphan

def Orphan.orphan_starts_live(window):
  {==}
