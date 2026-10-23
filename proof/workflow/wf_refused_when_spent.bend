# eukhe: the proof of LAW wf_refused_when_spent

import Base
import ../../bend/workflow.bend as W
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pw.refused(+k: Nat, +rs: List<&2, W.Row>, t: Nat, miss: {Laws.wf_first(rs, k) == None{} : Maybe<&2, Nat>}) -> {W.admit(None{}, k, rs, W.Pool{t, 0n}) == (W.Refused{}, W.Pool{t, 0n}) : W.Admit & W.Pool}:
  %Equal.sym(Maybe<&2, Nat>, W.found(rs, k, 0n), LA.pw.off(0n, Laws.wf_first(rs, k)), LA.pw.found(rs, k, 0n)) : {W.admit.fresh(_, W.Pool{t, 0n}) == (W.Refused{}, W.Pool{t, 0n}) : W.Admit & W.Pool}
  %Equal.sym(Maybe<&2, Nat>, Laws.wf_first(rs, k), None{}, miss) : {W.admit.fresh(LA.pw.off(0n, _), W.Pool{t, 0n}) == (W.Refused{}, W.Pool{t, 0n}) : W.Admit & W.Pool}
  {==}

def Laws.wf_refused_when_spent(k, rs, t, miss):
  pw.refused(k, rs, t, miss)
