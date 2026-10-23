# eukhe: the proof of LAW child_stalls_in_time

import Base
import ../../laws/child.bend as Child
import ../base.bend as L

# (H5) Every subagent reports back exactly once

def Child.child_stalls_in_time(cfg, w, h, hs, long):
  L.pc.stalls_in_time(cfg, w, h, hs, long)
