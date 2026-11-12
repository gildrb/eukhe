# eukhe: the proof of LAW answers_by_event
#
# PROOF of LAW answers_by_event: by the state and the event: each
# computes to the class the table names for the mode before and after.

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker
import ./base.bend as LAWorker

def Worker.answers_by_event(s, e):
  match s e:
    case Wk.St{m, p, k, n} Wk.Pause{}:
      {==}
    case Wk.St{Wk.Run{}, p, k, n} Wk.Resume{}:
      {==}
    case Wk.St{Wk.Paused{}, p, k, n} Wk.Resume{}:
      {==}
    case Wk.St{Wk.Run{}, p, k, n} Wk.Gate{g, i}:
      {==}
    case Wk.St{Wk.Paused{}, p, k, n} Wk.Gate{g, i}:
      {==}
    case Wk.St{m, p, k, n} Wk.ToolDone{}:
      {==}
    case Wk.St{Wk.Run{}, p, k, n} Wk.Msg{i, w}:
      {==}
    case Wk.St{Wk.Paused{}, p, k, n} Wk.Msg{i, True{}}:
      {==}
    case Wk.St{Wk.Paused{}, p, k, n} Wk.Msg{i, False{}}:
      {==}
    case Wk.St{m, p, k, n} Wk.End{}:
      {==}
