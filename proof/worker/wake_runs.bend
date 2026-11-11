# eukhe: the proof of LAW wake_runs
#
# PROOF of LAW wake_runs: by the state and the event: a resume
# runs the tree in either mode, a message runs a running tree (it passes)
# and a paused one when it wakes; every other event contradicts the
# premise.

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker
import ./base.bend as LAWorker

def wr_goal(s: Wk.St, e: Wk.Ev) -> Type:
  {Worker.wk_paused(Worker.wk_state(Wk.step(s, e))) == False{} : Bool}

def Worker.wake_runs(s, e, wakes):
  match s e:
    case Wk.St{m, p, k, n} Wk.Pause{}:
      LAWorker.wb_absurd_ft(wr_goal(Wk.St{m, p, k, n}, Wk.Pause{}), wakes)
    case Wk.St{Wk.Run{}, p, k, n} Wk.Resume{}:
      {==}
    case Wk.St{Wk.Paused{}, p, k, n} Wk.Resume{}:
      {==}
    case Wk.St{m, p, k, n} Wk.Gate{g, i}:
      LAWorker.wb_absurd_ft(wr_goal(Wk.St{m, p, k, n}, Wk.Gate{g, i}), wakes)
    case Wk.St{m, p, k, n} Wk.ToolDone{}:
      LAWorker.wb_absurd_ft(wr_goal(Wk.St{m, p, k, n}, Wk.ToolDone{}), wakes)
    case Wk.St{Wk.Run{}, p, k, n} Wk.Msg{i, w}:
      {==}
    case Wk.St{Wk.Paused{}, p, k, n} Wk.Msg{i, True{}}:
      {==}
    case Wk.St{Wk.Paused{}, p, k, n} Wk.Msg{i, False{}}:
      LAWorker.wb_absurd_ft(wr_goal(Wk.St{Wk.Paused{}, p, k, n}, Wk.Msg{i, False{}}), wakes)
    case Wk.St{m, p, k, n} Wk.End{}:
      LAWorker.wb_absurd_ft(wr_goal(Wk.St{m, p, k, n}, Wk.End{}), wakes)
