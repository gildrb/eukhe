# eukhe: the proof of LAW path_own_tree
#
# PROOF: the rule's path is at or above k ++ p (LAC.pcc.under_app), so the
# rule names the path.

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/path_own.bend as Po
import ../../laws/path_own.bend as PathOwn
import ../path_policy/base/class.bend as LAC

def PathOwn.path_own_tree(k, p, c):
  %Equal.sym(Bool, Pp.under(p, List.append(&2, Nat, k, p)), True{}, LAC.pcc.under_app(p, k)) : {Po.of(Po.first.pick(_, 0n, None{}), c) == Po.Own{0n} : Po.Wc}
  {==}
