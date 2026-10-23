# eukhe: the proof of LAW run_end_stays

import Base
import ../../laws/run.bend as Run
import ../base.bend as L

def Run.run_end_stays(cfg, s, ended, e):
  L.end_stays(cfg, s, e, ended)
