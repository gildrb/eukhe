# eukhe: the proof of LAW gate_yes_runs

import Base
import ../../bend/path_policy.bend as Pp
import ../../laws/path_policy.bend as PathPolicy
import ./base.bend as LA

def pp.gate_yes_runs(c: Pp.Cls, a: Pp.Acc, +auto: List<&2, Nat>) -> {Pp.runs(c, a, auto, Pp.Yes{}) == True{} : Bool}:
  LA.pp.or_tr(Pp.allows(auto, Pp.effs(c, a)), True{}, {==})

def PathPolicy.gate_yes_runs(c, a, auto):
  pp.gate_yes_runs(c, a, auto)
