# eukhe: the proof of LAW model_name_dash_split
#
# PROOF: a ++ (run ++ b) dashes as a, then the rest from the state a
# leaves (LZ.mnz.app), which is "no separator before" since a ends with
# no separator (LZ.mnz.last_f); the run's first char is a separator: one
# `-`; the rest of the run adds nothing (LZ.mnz.run_skip); b starts with
# no separator, so it dashes as alone (LZ.mnz.start_free).

import Base
import ../../bend/model_name.bend as M
import ../../laws/model_name.bend as ModelName
import ./base/dash.bend as LZ
import ./base.bend as LA

def ModelName.model_name_dash_split(a, c, r, b, ha, hr, hb):
  +hrr = hr
  +hc = Equal.trans(Bool, M.is_sep(c), ModelName.sp_sep(c), True{}, LZ.mnz.sep(c), LA.mnb.and_l(ModelName.sp_sep(c), ModelName.sp_all_sep(r), hrr))
  %Equal.sym(String, M.dash.go(String.append(a, SCon{c, String.append(r, b)}), False{}), String.append(M.dash.go(a, False{}), M.dash.go(SCon{c, String.append(r, b)}, LZ.mnz.last(a, False{}))), LZ.mnz.app(a, SCon{c, String.append(r, b)}, False{})) : {_ == String.append(M.dash(a), SCon{'-', M.dash(b)}) : String}
  %Equal.sym(Bool, LZ.mnz.last(a, False{}), False{}, LZ.mnz.last_f(a, ha)) : {String.append(M.dash.go(a, False{}), M.dash.go(SCon{c, String.append(r, b)}, _)) == String.append(M.dash(a), SCon{'-', M.dash(b)}) : String}
  %Equal.sym(Bool, M.is_sep(c), True{}, hc) : {String.append(M.dash.go(a, False{}), M.dash.at(_, False{}, c, q => M.dash.go(String.append(r, b), q))) == String.append(M.dash(a), SCon{'-', M.dash(b)}) : String}
  %Equal.sym(String, M.dash.go(String.append(r, b), True{}), M.dash.go(b, True{}), LZ.mnz.run_skip(r, b, LA.mnb.and_r(ModelName.sp_sep(c), ModelName.sp_all_sep(r), hrr))) : {String.append(M.dash.go(a, False{}), SCon{'-', _}) == String.append(M.dash(a), SCon{'-', M.dash(b)}) : String}
  %Equal.sym(String, M.dash.go(b, True{}), M.dash.go(b, False{}), LZ.mnz.start_free(b, hb)) : {String.append(M.dash.go(a, False{}), SCon{'-', _}) == String.append(M.dash(a), SCon{'-', M.dash(b)}) : String}
  {==}
