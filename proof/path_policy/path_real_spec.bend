# eukhe: the proof of LAW path_real_spec
#
# PROOF of LAW path_real_spec: the model's resolution, with the link the
# next name meets carried along, is the spec's walk, case by case on the
# fuel and the segments (the link lookup and the parent are the spec's:
# proof/path_policy/base/spec.bend); 40 links on both sides.

import Base
import ../../bend/path_policy.bend as Pp
import ../../laws/path_policy/spec.bend as PathPolicySpec
import ./base/spec.bend as LAPathPolicySpec

def PathPolicySpec.path_real_spec(ls, segs):
  LAPathPolicySpec.ps.go(Pp.max_links(), segs, ls, Nil{}, False{}, Pp.look.at(ls, segs, Nil{}), {==})
