# eukhe: the proof of LAW path_holds_at_or_under_secret
#
# PROOF: the judgment's holds is the secret test or the ancestor test of
# the secret entries; the entry s is at or above k ++ s (pcc.under_app),
# so the secret test holds (pri.any).

import Base
import ../../bend/path_policy.bend as Pp
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base/class.bend as LAC
import ./path_root_inside.bend as PPathRootInside

def PathPolicy.path_holds_at_or_under_secret(ro, ru, se1, s, se2, k, l):
  +se = List.append(&2, List<&2, Nat>, se1, s <> se2)
  +at = List.append(&2, Nat, k, s)
  +hu = PPathRootInside.pri.any(se1, s, se2, at, LAC.pcc.under_app(s, k))
  %Equal.sym(Bool, Pp.any_under(se, at), True{}, hu) : {Bool.or(_, Pp.any_ancestor(se, at)) == True{} : Bool}
  {==}
