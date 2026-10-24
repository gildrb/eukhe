# eukhe: the proof of LAW launcher_stop_counts_runs

import Base
import ../../bend/launcher.bend as La
import ../../laws/launcher.bend as Launcher

def lsc.count(ws: List<&2, La.Wk>) -> {La.busy_count(ws) == Launcher.busy_spec(ws) : Nat}:
  match ws:
    case Nil{}:
      {==}
    case La.Wk{b, c} <> t:
      match b:
        case True{}:
          %lsc.count(t) : {1n+La.busy_count(t) == 1n+_ : Nat}
          {==}
        case False{}:
          lsc.count(t)

def Launcher.launcher_stop_counts_runs(ws):
  lsc.count(ws)
