# eukhe: the proof of LAW path_judge_secret_under
#
# PROOF: the entry s is at or above k ++ s (pcc.under_app), so the model's
# secret test over se1 ++ s :: se2 holds (pri.any); the class picked is then
# Secret, and a loop keeps a Secret class.

import Base
import ../../bend/path_policy.bend as Pp
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base/class.bend as LAC
import ./path_root_inside.bend as PPathRootInside

def PathPolicy.path_judge_secret_under(ro, ru, se1, s, se2, k, l):
  +se = List.append(&2, List<&2, Nat>, se1, s <> se2)
  +at = List.append(&2, Nat, k, s)
  +hu = PPathRootInside.pri.any(se1, s, se2, at, LAC.pcc.under_app(s, k))
  %Equal.sym(Bool, Pp.any_under(se, at), True{}, hu) : {Pp.demote(Pp.cls.pick(_, Pp.protects(Pp.Pol{ro, ru, se}, at), Maybe.is_some(&2, List<&2, Nat>, Pp.root.of(ro, at))), l) == Pp.Secret{} : Pp.Cls}
  {==}
