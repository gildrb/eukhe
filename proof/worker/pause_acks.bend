# eukhe: the proof of LAW pause_acks
#
# PROOF of LAW pause_acks: the step computes on any state.

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker

def Worker.pause_acks(m, p, k, n):
  {==}
