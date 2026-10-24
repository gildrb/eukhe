# eukhe: the proof of LAW sweep_never_live_real

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA

def nl.go(b: Bool, c: Sg.Cand) -> {Sg.judge.go(b, c, Sg.LHeld{}) == Sg.PKeep{} : Sg.Plan}:
  match b:
    case True{}:
      match c:
        case Sg.CDir{}:
          {==}
        case Sg.CLock{}:
          {==}
    case False{}:
      {==}

def Staging.sweep_never_live_real(c, now, own, inner):
  nl.go(Sg.stale_all(now, own <> inner), c)
