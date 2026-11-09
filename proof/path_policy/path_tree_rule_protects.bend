# eukhe: the proof of LAW path_tree_rule_protects
#
# PROOF: a Tree rule on p covers every path k ++ p (pcc.under_app), so the
# rules cover it (pcc.covers_app), the policy protects it (pcc.prot_cover)
# and, not Secret, it is Protected (pcc.protects_class).

import Base
import ../../bend/path_policy.bend as Pp
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base/class.bend as LAC

def PathPolicy.path_tree_rule_protects(ro, ru1, p, ru2, se, ls, segs, k, l, res, ns):
  +at = List.append(&2, Nat, k, p)
  +ru = List.append(&2, Pp.Rule, ru1, Pp.Tree{p} <> ru2)
  +low = Pp.below(ro, at)
  +hc = LAC.pcc.covers_app(ru1, Pp.Tree{p}, ru2, at, low, LAC.pcc.under_app(p, k))
  LAC.pcc.protects_class(ro, ru, se, ls, segs, at, l, res, ns, LAC.pcc.prot_cover(ro, ru, se, at, hc))
