# eukhe: the proof of LAW timeouts_values_are_model
# On any base values both sides compute to the same sums.

import Base
import ../../bend/supervise.bend as Su
import ../../laws/timeouts.bend as Timeouts

def Timeouts.timeouts_values_are_model(t):
  match t:
    case Su.Tm{snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, bmax, loop, qanswer}:
      {==}
