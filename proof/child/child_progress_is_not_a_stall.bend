# eukhe: the proof of LAW child_progress_is_not_a_stall

import Base
import ../../LAWS.bend as Laws
import ../base.bend as L

def Laws.child_progress_is_not_a_stall(cfg, w, e, x, news):
  L.pc.progress_is_not_a_stall(cfg, w, e, x, news)
