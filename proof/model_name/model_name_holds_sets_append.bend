# eukhe: the proof of LAW model_name_holds_sets_append
#
# PROOF: the verdicts over one group are the row of the sets; the row of
# s1 ++ s2 is the row of s1 before the row of s2 (LH.mnh.row_split), and
# what follows a row can be appended after it (LH.mnh.row_app).

import Base
import ../../bend/model_name.bend as M
import ../../laws/model_name.bend as ModelName
import ./base/holds.bend as LH

def ModelName.model_name_holds_sets_append(s1, s2, g):
  Equal.trans(List<&2, Bool>, M.row(List.append(&2, List<&2, M.Rule>, s1, s2), g, Nil{}), M.row(s1, g, M.row(s2, g, Nil{})), List.append(&2, Bool, M.row(s1, g, Nil{}), M.row(s2, g, Nil{})), LH.mnh.row_split(s1, s2, g, Nil{}), Equal.sym(List<&2, Bool>, List.append(&2, Bool, M.row(s1, g, Nil{}), M.row(s2, g, Nil{})), M.row(s1, g, M.row(s2, g, Nil{})), LH.mnh.row_app(s1, g, Nil{}, M.row(s2, g, Nil{}))))
