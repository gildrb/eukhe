# eukhe: the proof of LAW stop_cut_spent_never_kept
#
# PROOF: the closed claims compute: at a spent window LengthStop continues when a compaction can run and drops the reply when none can, before any outer Director reads the stop.

import Base
import ../../bend/stop.bend as S
import ../../laws/stop/cut.bend as StopCut

def StopCut.stop_cut_spent_never_kept(b, p):
  ({==}, {==})
