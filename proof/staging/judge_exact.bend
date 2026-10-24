# eukhe: the proof of LAW judge_exact

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA

def Staging.judge_exact(c, l, now, own, inner):
  %LA.rr.judge_old(c, l, now, own, inner) : {_ == Staging.sp_judge(c, l, now, own, inner) : Sg.Plan}
  LA.rr.judge_go(Staging.sp_all_old(now, own <> inner), c, l)
