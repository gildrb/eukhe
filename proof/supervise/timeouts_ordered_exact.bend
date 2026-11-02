# eukhe: the proof of LAW timeouts_ordered_exact

import Base
import ../../bend/supervise.bend as Su
import ../../laws/supervise.bend as Supervise

def Supervise.timeouts_ordered_exact(t):
  match t:
    case Su.Tm{snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, bmax, loop, qanswer}:
      {==}
