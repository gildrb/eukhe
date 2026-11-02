# eukhe: the proof of LAW gate_runs_spec
#
# PROOF of LAW gate_runs_spec: the effects are the spec's
# (gate_effs_spec's lemma), the auto test is the spec's code by code (a
# grantable code is one below 7, membership is the spec's, the
# conjunction reordered), and a yes is the spec's
# (proof/path_policy/base/spec.bend).

import Base
import ../../laws/path_policy.bend as PathPolicy
import ./base/spec.bend as LAPathPolicySpec

def PathPolicy.gate_runs_spec(c, a, auto, ans):
  LAPathPolicySpec.ps.runs(c, a, auto, ans)
