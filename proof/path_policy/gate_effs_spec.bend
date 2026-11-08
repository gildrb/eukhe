# eukhe: the proof of LAW gate_effs_spec
#
# PROOF of LAW gate_effs_spec: case analysis on the access, the search's
# secret test and the class; each case computes to the spec's list
# (proof/path_policy/base/spec.bend).

import Base
import ../../laws/path_policy/spec.bend as PathPolicySpec
import ./base/spec.bend as LAPathPolicySpec

def PathPolicySpec.gate_effs_spec(c, a):
  LAPathPolicySpec.ps.effs(c, a)
