# eukhe: the proof of LAW run_end_stays

import Base
import ../../LAWS.bend as Laws
import ../base.bend as L

def Laws.run_end_stays(cfg, s, ended, e):
  L.end_stays(cfg, s, e, ended)
