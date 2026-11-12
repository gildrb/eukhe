# eukhe: the proof of LAW parked_names_held
#
# PROOF of LAW parked_names_held: by the state and the event: each
# computes to the parked boundary the table names.

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker
import ./base.bend as LAWorker

def Worker.parked_names_held(s, e):
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
