# eukhe: the proof of LAW resume_continues
#
# PROOF of LAW resume_continues: the three steps compute; the count after
# the gate is the spec's by the kind (0, 1, 2 or more).

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker

def Worker.resume_continues(p, k, n, kind, id):
  match kind:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+x:
      {==}
