# eukhe: the proof of LAW running_passes
#
# PROOF of LAW running_passes: the step computes on a running state.

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker

def Worker.running_passes(p, k, n, id, w):
  {==}
