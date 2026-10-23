# eukhe: the proof of LAW run_end_stays

import Base
import ../../laws/run.bend as Run
import ../base/run.bend as LRun

def Run.run_end_stays(cfg, s, ended, e):
  LRun.end_stays(cfg, s, e, ended)
