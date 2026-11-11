# eukhe: the proof of LAW wf_reuses_first_answered

import Base
import ../../bend/workflow.bend as W
import ../../laws/workflow/model.bend as Workflow
import ./base.bend as LA

def Workflow.wf_reuses_first_answered(k, pre, s, post, p, first, answered):
  %Equal.sym(Maybe<&2, Nat>, W.found(List.append(&2, W.Row, pre, W.Row{k, s} <> post), k, 0n), Some{Nat.add(List.length(&2, W.Row, pre), 0n)}, LA.pw.first(pre, k, s, post, 0n, first, answered)) : {W.admit.fresh(_, p) == (W.Reuse{List.length(&2, W.Row, pre)}, p) : W.Admit & W.Pool}
  %Equal.sym(Nat, Nat.add(List.length(&2, W.Row, pre), 0n), List.length(&2, W.Row, pre), LA.pw.add_zero(List.length(&2, W.Row, pre))) : {W.admit.fresh(Some{_}, p) == (W.Reuse{List.length(&2, W.Row, pre)}, p) : W.Admit & W.Pool}
  {==}
