# eukhe: the proof of LAW running_keeps_nothing
#
# PROOF of LAW running_keeps_nothing: by the state and the
# event: a paused tree either stays paused or runs with nothing kept (a
# resume, a waking message); a running tree that keeps nothing keeps
# nothing after any event (no event of a running tree adds a kept id); a
# running tree that keeps an id contradicts the premise.

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker
import ./base.bend as LAWorker

def rkn_goal(s: Wk.St, e: Wk.Ev) -> Type:
  {Worker.wk_clean(Worker.wk_state(Wk.step(s, e))) == True{} : Bool}

def Worker.running_keeps_nothing(s, e, clean):
  match s e:
    case Wk.St{Wk.Paused{}, p, k, n} Wk.Pause{}:
      {==}
    case Wk.St{Wk.Paused{}, p, k, n} Wk.Resume{}:
      {==}
    case Wk.St{Wk.Paused{}, p, k, n} Wk.Gate{g, i}:
      {==}
    case Wk.St{Wk.Paused{}, p, k, n} Wk.ToolDone{}:
      {==}
    case Wk.St{Wk.Paused{}, p, k, n} Wk.Msg{i, True{}}:
      {==}
    case Wk.St{Wk.Paused{}, p, k, n} Wk.Msg{i, False{}}:
      {==}
    case Wk.St{Wk.Paused{}, p, k, n} Wk.End{}:
      {==}
    case Wk.St{Wk.Run{}, p, Nil{}, n} Wk.Pause{}:
      {==}
    case Wk.St{Wk.Run{}, p, Nil{}, n} Wk.Resume{}:
      {==}
    case Wk.St{Wk.Run{}, p, Nil{}, n} Wk.Gate{g, i}:
      {==}
    case Wk.St{Wk.Run{}, p, Nil{}, n} Wk.ToolDone{}:
      {==}
    case Wk.St{Wk.Run{}, p, Nil{}, n} Wk.Msg{i, w}:
      {==}
    case Wk.St{Wk.Run{}, p, Nil{}, n} Wk.End{}:
      {==}
    case Wk.St{Wk.Run{}, p, Con{x, r}, n} e:
      LAWorker.wb_absurd_ft(rkn_goal(Wk.St{Wk.Run{}, p, x <> r, n}, e), clean)
