# eukhe: the proof of LAW pause_only_done_lowers
#
# PROOF of LAW pause_only_done_lowers: by the state and the event: a gate
# of a running tree raises the count by one for a tool call (n <= n + 1)
# and keeps it otherwise; every other event but a tool's end and the run's
# end keeps it (n <= n); those two contradict the premise.

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker
import ./base.bend as LAWorker

def pol_goal(s: Wk.St, e: Wk.Ev) -> Type:
  {Nat.is_le(Worker.wk_inflight(s), Worker.wk_inflight(Worker.wk_state(Wk.step(s, e)))) == True{} : Bool}

def pol_gate(g: Nat, +n: Nat) -> {Nat.is_le(n, Wk.started(g, n)) == True{} : Bool}:
  match g:
    case 0n:
      LAWorker.wb_le_refl(n)
    case 1n:
      LAWorker.wb_le_succ(n)
    case 2n+x:
      LAWorker.wb_le_refl(n)

def Worker.pause_only_done_lowers(s, e, other):
  match s e:
    case Wk.St{m, p, k, n} Wk.Pause{}:
      LAWorker.wb_le_refl(n)
    case Wk.St{Wk.Run{}, p, k, n} Wk.Resume{}:
      LAWorker.wb_le_refl(n)
    case Wk.St{Wk.Paused{}, p, k, n} Wk.Resume{}:
      LAWorker.wb_le_refl(n)
    case Wk.St{Wk.Run{}, p, k, n} Wk.Gate{g, i}:
      pol_gate(g, n)
    case Wk.St{Wk.Paused{}, p, k, n} Wk.Gate{g, i}:
      LAWorker.wb_le_refl(n)
    case Wk.St{m, p, k, n} Wk.ToolDone{}:
      LAWorker.wb_absurd_tf(pol_goal(Wk.St{m, p, k, n}, Wk.ToolDone{}), other)
    case Wk.St{Wk.Run{}, p, k, n} Wk.Msg{i, w}:
      LAWorker.wb_le_refl(n)
    case Wk.St{Wk.Paused{}, p, k, n} Wk.Msg{i, True{}}:
      LAWorker.wb_le_refl(n)
    case Wk.St{Wk.Paused{}, p, k, n} Wk.Msg{i, False{}}:
      LAWorker.wb_le_refl(n)
    case Wk.St{m, p, k, n} Wk.End{}:
      LAWorker.wb_absurd_tf(pol_goal(Wk.St{m, p, k, n}, Wk.End{}), other)
