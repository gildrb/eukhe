# eukhe: the proof of LAW wf_cached_key_spawns_nothing

import Base
import ../../bend/workflow.bend as W
import ../../laws/workflow.bend as Workflow

def pw.cached(+k: Nat, cache: List<&2, Nat>, hit: {W.member(k, cache) == True{} : Bool}) -> {W.cost(k, cache) == 0n : Nat}:
  %Equal.sym(Bool, W.member(k, cache), True{}, hit) : {W.cost.go(_) == 0n : Nat}
  {==}

def Workflow.wf_cached_key_spawns_nothing(k, cache, hit):
  pw.cached(k, cache, hit)
