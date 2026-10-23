# eukhe: the proof of LAW wf_empty_cache_spawns_all

import Base
import ../../bend/workflow.bend as W
import ../../laws/workflow.bend as Workflow

def pw.empty(keys: List<&2, Nat>) -> {W.resumed([], keys) == List.length(&2, Nat, keys) : Nat}:
  match keys:
    case Nil{}:
      {==}
    case k <> +rest:
      %pw.empty(rest) : {1n+W.resumed([], rest) == 1n+_ : Nat}
      {==}

def Workflow.wf_empty_cache_spawns_all(keys):
  pw.empty(keys)
