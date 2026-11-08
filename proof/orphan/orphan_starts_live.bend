# eukhe: the proof of LAW orphan_starts_live: the empty history runs no
# step, so the worker is the empty live worker, which is the spec state of
# the empty history

import Base
import ../../bend/orphan.bend as Or
import ../../laws/orphan.bend as Orphan

def Orphan.orphan_starts_live(window):
  {==}
