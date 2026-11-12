# eukhe: the proof of LAW judge_gone_lock_kept

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA

def jg.go(b: Bool) -> {Sg.judge.go(b, Sg.CLock{}, Sg.LAbsent{}) == Sg.PKeep{} : Sg.Plan}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Staging.judge_gone_lock_kept(now, own, inner):
  jg.go(Sg.stale_all(now, own <> inner))
