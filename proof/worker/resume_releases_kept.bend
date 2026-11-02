# eukhe: the proof of LAW resume_releases_kept
#
# PROOF of LAW resume_releases_kept: the step computes on a paused state.

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker

def Worker.resume_releases_kept(p, k, n):
  {==}
