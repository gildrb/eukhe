# eukhe: the proof of LAW pause_never_cancels
#
# PROOF of LAW pause_never_cancels: by the state and the event: a pause, a
# resume and a message (in either mode, waking or not) compute to a state
# with the same count; the other events contradict the premise.

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker
import ./base.bend as LAWorker

def pnc_goal(s: Wk.St, e: Wk.Ev) -> Type:
  {Worker.wk_inflight(Worker.wk_state(Wk.step(s, e))) == Worker.wk_inflight(s) : Nat}

def Worker.pause_never_cancels(s, e, keeps):
  match s e:
    case Wk.St{m, p, k, n} Wk.Pause{}:
      {==}
    case Wk.St{Wk.Run{}, p, k, n} Wk.Resume{}:
      {==}
    case Wk.St{Wk.Paused{}, p, k, n} Wk.Resume{}:
      {==}
    case Wk.St{m, p, k, n} Wk.Gate{g, i}:
      LAWorker.wb_absurd_ft(pnc_goal(Wk.St{m, p, k, n}, Wk.Gate{g, i}), keeps)
    case Wk.St{m, p, k, n} Wk.ToolDone{}:
      LAWorker.wb_absurd_ft(pnc_goal(Wk.St{m, p, k, n}, Wk.ToolDone{}), keeps)
    case Wk.St{Wk.Run{}, p, k, n} Wk.Msg{i, w}:
      {==}
    case Wk.St{Wk.Paused{}, p, k, n} Wk.Msg{i, True{}}:
      {==}
    case Wk.St{Wk.Paused{}, p, k, n} Wk.Msg{i, False{}}:
      {==}
    case Wk.St{m, p, k, n} Wk.End{}:
      LAWorker.wb_absurd_ft(pnc_goal(Wk.St{m, p, k, n}, Wk.End{}), keeps)
