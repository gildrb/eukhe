# eukhe: the proof of LAW paused_starts_nothing
#
# PROOF of LAW paused_starts_nothing: the step computes on a paused state,
# for any kind.

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker

def Worker.paused_starts_nothing(p, k, n, kind, id):
  {==}
