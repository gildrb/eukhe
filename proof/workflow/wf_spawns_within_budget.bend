# eukhe: the proof of LAW wf_spawns_within_budget

import Base
import ../../bend/workflow.bend as W
import ../../laws/workflow/model.bend as Workflow
import ./base.bend as LA

def Workflow.wf_spawns_within_budget(k, rs, t, l, miss):
  %Equal.sym(Maybe<&2, Nat>, W.found(rs, k, 0n), None{}, LA.pw.miss(rs, k, 0n, miss)) : {W.admit.fresh(_, W.Pool{t, 1n+l}) == (W.Spawn{}, W.Pool{1n+t, l}) : W.Admit & W.Pool}
  {==}
