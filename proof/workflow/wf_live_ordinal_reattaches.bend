# eukhe: the proof of LAW wf_live_ordinal_reattaches

import Base
import ../../bend/workflow.bend as W
import ../../laws/workflow/model.bend as Workflow
import ./base.bend as LA

def Workflow.wf_live_ordinal_reattaches(s, k, rs, p, prem):
  match s:
    case W.Queued{}:
      {==}
    case W.Running{}:
      {==}
    case W.Finished{}:
      LA.pw.absurd({W.admit(Some{W.Finished{}}, k, rs, p) == (W.Reattach{}, p) : W.Admit & W.Pool}, Equal.sym(Bool, True{}, False{}, prem))
    case W.Erred{}:
      LA.pw.absurd({W.admit(Some{W.Erred{}}, k, rs, p) == (W.Reattach{}, p) : W.Admit & W.Pool}, Equal.sym(Bool, True{}, False{}, prem))
    case W.Cancelled{}:
      LA.pw.absurd({W.admit(Some{W.Cancelled{}}, k, rs, p) == (W.Reattach{}, p) : W.Admit & W.Pool}, Equal.sym(Bool, True{}, False{}, prem))
    case W.Cached{}:
      LA.pw.absurd({W.admit(Some{W.Cached{}}, k, rs, p) == (W.Reattach{}, p) : W.Admit & W.Pool}, Equal.sym(Bool, True{}, False{}, prem))
