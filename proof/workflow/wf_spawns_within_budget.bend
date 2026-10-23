# eukhe: the proof of LAW wf_spawns_within_budget

import Base
import ../../bend/workflow.bend as W
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pw.spawns(+k: Nat, +rs: List<&2, W.Row>, t: Nat, l: Nat, miss: {Laws.wf_first(rs, k) == None{} : Maybe<&2, Nat>}) -> {W.admit(None{}, k, rs, W.Pool{t, 1n+l}) == (W.Spawn{}, W.Pool{1n+t, l}) : W.Admit & W.Pool}:
  %Equal.sym(Maybe<&2, Nat>, W.found(rs, k, 0n), LA.pw.off(0n, Laws.wf_first(rs, k)), LA.pw.found(rs, k, 0n)) : {W.admit.fresh(_, W.Pool{t, 1n+l}) == (W.Spawn{}, W.Pool{1n+t, l}) : W.Admit & W.Pool}
  %Equal.sym(Maybe<&2, Nat>, Laws.wf_first(rs, k), None{}, miss) : {W.admit.fresh(LA.pw.off(0n, _), W.Pool{t, 1n+l}) == (W.Spawn{}, W.Pool{1n+t, l}) : W.Admit & W.Pool}
  {==}

def Laws.wf_spawns_within_budget(k, rs, t, l, miss):
  pw.spawns(k, rs, t, l, miss)
