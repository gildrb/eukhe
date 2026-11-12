# eukhe: the proof of LAW wf_ended_ordinal_replays

import Base
import ../../bend/workflow.bend as W
import ../../laws/workflow/model.bend as Workflow
import ./base.bend as LA

def Workflow.wf_ended_ordinal_replays(s, k, rs, p, prem):
  match s:
    case W.Queued{}:
      LA.pw.absurd({W.admit(Some{W.Queued{}}, k, rs, p) == (W.Ended{}, p) : W.Admit & W.Pool}, prem)
    case W.Running{}:
      LA.pw.absurd({W.admit(Some{W.Running{}}, k, rs, p) == (W.Ended{}, p) : W.Admit & W.Pool}, prem)
    case W.Finished{}:
      {==}
    case W.Erred{}:
      {==}
    case W.Cancelled{}:
      {==}
    case W.Cached{}:
      {==}
