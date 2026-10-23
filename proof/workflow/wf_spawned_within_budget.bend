# eukhe: the proof of LAW wf_spawned_within_budget

import Base
import ../../bend/workflow.bend as W
import ../../laws/workflow.bend as Workflow
import ./base.bend as LA

def pw.spawns_size(n: Nat, +p: W.Pool) -> {W.size(W.spawns(n, p)) == W.size(p) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      Equal.trans(Nat, W.size(W.spawns(m, W.take(p))), W.size(W.take(p)), W.size(p), pw.spawns_size(m, W.take(p)), LA.pw.take_size(p))

def Workflow.wf_spawned_within_budget(max, n):
  pw.spawns_size(n, W.pool(max))
