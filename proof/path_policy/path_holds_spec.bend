# eukhe: the proof of LAW path_holds_spec
#
# PROOF of LAW path_holds_spec: the model's test is under a secret or
# above one; each half is the spec's (proof/path_policy/base/spec.bend).

import Base
import ../../bend/path_policy.bend as Pp
import ../../laws/path_policy/spec.bend as PathPolicySpec
import ./base/spec.bend as LAPathPolicySpec

def PathPolicySpec.path_holds_spec(pol, at):
  match pol:
    case Pp.Pol{ro, ru, +se}:
      LAPathPolicySpec.ps.or_eq(Pp.any_under(se, at), PathPolicySpec.pp_under_any(se, at), Pp.any_ancestor(se, at), PathPolicySpec.pp_above_any(se, at), LAPathPolicySpec.ps.any_under(se, at), LAPathPolicySpec.ps.any_ancestor(se, at))
