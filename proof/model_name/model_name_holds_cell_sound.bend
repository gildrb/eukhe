# eukhe: the proof of LAW model_name_holds_cell_sound
#
# PROOF: the verdicts of one set over one group are [set_holds], so the
# premise says the set holds; a set that holds has a name for which one
# of its rules holds (LH.mnh.set_sp, LH.mnh.rules_sp).

import Base
import ../../bend/model_name.bend as M
import ../../laws/model_name.bend as ModelName
import ./base/holds.bend as LH

# the law's conclusion
def hcs.G(rs: List<&2, M.Rule>, g: List<&2, String>) -> Type:
  Sigma<&1, &1, List<&2, M.Rule>, pre => Sigma<&1, &1, M.Rule, r => Sigma<&1, &1, List<&2, M.Rule>, post => Sigma<&1, &1, List<&2, String>, gp => Sigma<&1, &1, String, s => Sigma<&1, &1, List<&2, String>, gq => {rs == List.append(&2, M.Rule, pre, r <> post) : List<&2, M.Rule>} & ({g == List.append(&2, String, gp, s <> gq) : List<&2, String>} & {M.rule(r, s) == True{} : Bool})>>>>>>

# the witnesses of a set that holds, reordered
def hcs.fin(-rs: List<&2, M.Rule>, -g: List<&2, String>, v: LH.mnh.SetP(rs, g, True{})) -> hcs.G(rs, g):
  (+gp, (+s, (+gq, (eg, (+pre, (+r, (+post, (er, ok)))))))) = v
  (pre, (r, (post, (gp, (s, (gq, (er, (eg, ok))))))))

def ModelName.model_name_holds_cell_sound(rs, g, h):
  +hh = Equal.cong(List<&2, Bool>, Bool, l => LH.mnh.head(l), M.holds([rs], [g]), [True{}], h)
  hcs.fin(rs, g, LH.mnh.set_cast(rs, g, M.set_holds(rs, g), hh, LH.mnh.set_sp(rs, g)))
