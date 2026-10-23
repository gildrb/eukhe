# eukhe: the proof of LAW wf_reuses_first_answer

import Base
import ../../bend/workflow.bend as W
import ../../laws/workflow.bend as Workflow
import ./base.bend as LA

def pw.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %pw.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def pw.reuses(+k: Nat, +rs: List<&2, W.Row>, p: W.Pool, +i: Nat, hit: {Workflow.wf_first(rs, k) == Some{i} : Maybe<&2, Nat>}) -> {W.admit(None{}, k, rs, p) == (W.Reuse{i}, p) : W.Admit & W.Pool}:
  %Equal.sym(Maybe<&2, Nat>, W.found(rs, k, 0n), LA.pw.off(0n, Workflow.wf_first(rs, k)), LA.pw.found(rs, k, 0n)) : {W.admit.fresh(_, p) == (W.Reuse{i}, p) : W.Admit & W.Pool}
  %Equal.sym(Maybe<&2, Nat>, Workflow.wf_first(rs, k), Some{i}, hit) : {W.admit.fresh(LA.pw.off(0n, _), p) == (W.Reuse{i}, p) : W.Admit & W.Pool}
  %Equal.sym(Nat, Nat.add(i, 0n), i, pw.add_zero(i)) : {W.admit.fresh(Some{_}, p) == (W.Reuse{i}, p) : W.Admit & W.Pool}
  {==}

def Workflow.wf_reuses_first_answer(k, rs, p, i, hit):
  pw.reuses(k, rs, p, i, hit)
