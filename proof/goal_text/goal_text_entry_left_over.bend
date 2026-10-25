# eukhe: the proof of LAW goal_text_entry_left_over
#
# PROOF: the spelled request reads back with the rest untouched (gte.req_rt); the rest is not empty, so the entry answers the error form.

import Base
import ../../bend/goal_text.bend as Gt
import ../../bend/ffi_goal_text.bend as FGt
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/goal_text.bend as GoalText
import ./base/entry.bend as LE

def GoalText.goal_text_entry_left_over(q, c, t, fit):
  %Equal.sym(Wr.Dec<FGt.Req>, FGt.get_req(GoalText.gt_w_req(q, SCon{c, t})), Wr.Got{q, SCon{c, t}}, LE.gte.req_rt(q, SCon{c, t}, fit)) : {FGt.ffi.got(_) == Wr.err("goal_text: malformed request") : String}
  {==}
