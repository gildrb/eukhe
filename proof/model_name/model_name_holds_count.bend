# eukhe: the proof of LAW model_name_holds_count
#
# PROOF: by induction on the groups: each group adds a row of one verdict
# per set (LH.mnh.row_len) before the verdicts of the others.

import Base
import ../../bend/model_name.bend as M
import ../../laws/model_name.bend as ModelName
import ./base/holds.bend as LH

def ModelName.model_name_holds_count(sets, groups):
  match groups:
    case Nil{}:
      {==}
    case +g <> +more:
      Equal.trans(Nat, List.length(&2, Bool, M.row(sets, g, M.holds(sets, more))), Nat.add(List.length(&2, List<&2, M.Rule>, sets), List.length(&2, Bool, M.holds(sets, more))), Nat.add(List.length(&2, List<&2, M.Rule>, sets), Nat.mul(List.length(&2, List<&2, String>, more), List.length(&2, List<&2, M.Rule>, sets))), LH.mnh.row_len(sets, g, M.holds(sets, more)), Equal.cong(Nat, Nat, k => Nat.add(List.length(&2, List<&2, M.Rule>, sets), k), List.length(&2, Bool, M.holds(sets, more)), Nat.mul(List.length(&2, List<&2, String>, more), List.length(&2, List<&2, M.Rule>, sets)), ModelName.model_name_holds_count(sets, more)))
