# eukhe: the proof of LAW restart_go_exact

import Base
import ../../bend/supervise.bend as Su
import ../../laws/supervise.bend as Supervise
import ./base.bend as LA

def Supervise.restart_go_exact(c, gs, s):
  LA.ps.rs_go(c, gs, s)
