# eukhe: the proof of LAW model_name_holds_cell_complete
#
# PROOF: the verdicts of one set over one group are [set_holds]; the rule
# r in the set holds for s (LH.mnh.rules_in), so the set holds for the
# name s in the group (LH.mnh.set_in).

import Base
import ../../bend/model_name.bend as M
import ../../laws/model_name.bend as ModelName
import ./base/holds.bend as LH

def ModelName.model_name_holds_cell_complete(pre, r, post, gp, s, gq, h):
  Equal.cong(Bool, List<&2, Bool>, z => z <> Nil{}, M.set_holds(List.append(&2, M.Rule, pre, r <> post), List.append(&2, String, gp, s <> gq)), True{}, LH.mnh.set_in(List.append(&2, M.Rule, pre, r <> post), gp, s, gq, LH.mnh.rules_in(pre, r, post, s, h)))
