# eukhe: the proof of LAW child_stalls_in_time

import Base
import ../../laws/child.bend as Child
import ../base/child.bend as LChild

# (H5) Every subagent reports back exactly once

def Child.child_stalls_in_time(cfg, w, h, hs, long):
  LChild.pc.stalls_in_time(cfg, w, h, hs, long)
