# eukhe: the proof of LAW child_look_exact
# The verdict is K1's, case by case (LAE.cl.look).

import Base
import ../../laws/child/exact.bend as Child
import ./base/entry.bend as LAE

def Child.child_look_exact(cfg, w, e, o):
  LAE.cl.look(cfg, w, e, o)
