# eukhe: the proof of LAW path_holds_spec
#
# PROOF of LAW path_holds_spec: the model's test is under a secret or
# above one; each half is the spec's (proof/path_policy/base/spec.bend).

import Base
import ../../bend/path_policy.bend as Pp
import ../../laws/path_policy.bend as PathPolicy
import ./base/spec.bend as LAPathPolicySpec

def PathPolicy.path_holds_spec(pol, at):
  match pol:
    case Pp.Pol{ro, ru, +se}:
      LAPathPolicySpec.ps.or_eq(Pp.any_under(se, at), PathPolicy.pp_under_any(se, at), Pp.any_ancestor(se, at), PathPolicy.pp_above_any(se, at), LAPathPolicySpec.ps.any_under(se, at), LAPathPolicySpec.ps.any_ancestor(se, at))
