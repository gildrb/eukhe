# eukhe: the proof of LAW path_class_spec
#
# PROOF of LAW path_class_spec: the model's class is its pick of three
# tests and the loop; each test is the spec's, helper by helper (a path
# under an entry is in its lineage, the names below the deepest root walk
# up to the first root, the rules cover as the spec says:
# proof/path_policy/base/spec.bend), and the pick is the spec's.

import Base
import ../../bend/path_policy.bend as Pp
import ../../laws/path_policy.bend as PathPolicy
import ./base/spec.bend as LAPathPolicySpec

def PathPolicy.path_class_spec(pol, r):
  match pol r:
    case Pp.Pol{+ro, +ru, +se} Pp.Res{+at, l}:
      LAPathPolicySpec.ps.class(ro, ru, se, at, l)
