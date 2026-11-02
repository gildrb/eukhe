# eukhe: the proof of LAW done_settles
#
# PROOF of LAW done_settles: by the count: none stays none, else one less.

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker

def Worker.done_settles(m, p, k, n):
  match n:
    case 0n:
      {==}
    case 1n+q:
      {==}
