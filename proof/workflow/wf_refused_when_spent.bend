# eukhe: the proof of LAW wf_refused_when_spent

import Base
import ../../bend/workflow.bend as W
import ../../laws/workflow/model.bend as Workflow
import ./base.bend as LA

def Workflow.wf_refused_when_spent(k, rs, t, miss):
  %Equal.sym(Maybe<&2, Nat>, W.found(rs, k, 0n), None{}, LA.pw.miss(rs, k, 0n, miss)) : {W.admit.fresh(_, W.Pool{t, 0n}) == (W.Refused{}, W.Pool{t, 0n}) : W.Admit & W.Pool}
  {==}
