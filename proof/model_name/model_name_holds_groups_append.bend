# eukhe: the proof of LAW model_name_holds_groups_append
#
# PROOF: by induction on g1: a group's row is put before the verdicts of
# the groups after it, and what follows a row can be appended after it
# (LH.mnh.row_app).

import Base
import ../../bend/model_name.bend as M
import ../../laws/model_name.bend as ModelName
import ./base/holds.bend as LH

def ModelName.model_name_holds_groups_append(sets, g1, g2):
  match g1:
    case Nil{}:
      {==}
    case +g <> +more:
      Equal.trans(List<&2, Bool>, M.row(sets, g, M.holds(sets, List.append(&2, List<&2, String>, more, g2))), M.row(sets, g, List.append(&2, Bool, M.holds(sets, more), M.holds(sets, g2))), List.append(&2, Bool, M.row(sets, g, M.holds(sets, more)), M.holds(sets, g2)), Equal.cong(List<&2, Bool>, List<&2, Bool>, z => M.row(sets, g, z), M.holds(sets, List.append(&2, List<&2, String>, more, g2)), List.append(&2, Bool, M.holds(sets, more), M.holds(sets, g2)), ModelName.model_name_holds_groups_append(sets, more, g2)), Equal.sym(List<&2, Bool>, List.append(&2, Bool, M.row(sets, g, M.holds(sets, more)), M.holds(sets, g2)), M.row(sets, g, List.append(&2, Bool, M.holds(sets, more), M.holds(sets, g2))), LH.mnh.row_app(sets, g, M.holds(sets, more), M.holds(sets, g2))))
