# eukhe: the proof of LAW sweep_never_young_real

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA

def Staging.sweep_never_young_real(c, l, now, own, inner, young):
  %LA.rr.judge_old(c, l, now, own, inner) : {_ == Sg.PKeep{} : Sg.Plan}
  %Equal.sym(Bool, Staging.sp_all_old(now, own <> inner), False{}, young) : {Sg.judge.go(_, c, l) == Sg.PKeep{} : Sg.Plan}
  {==}
