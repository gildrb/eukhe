# eukhe: the proof of LAW goal_text_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left (gte.req_rt), so the entry answers the code's answer, spelled by encoders that are the spec spellers (gte.ms, gte.host); the text laws pin the answer itself.

import Base
import ../../bend/goal_text.bend as Gt
import ../../bend/ffi_goal_text.bend as FGt
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/goal_text.bend as GoalText
import ./base/entry.bend as LE

def gta.reply(q: FGt.Req) -> {FGt.answer(q) == GoalText.gt_w_reply(q) : String}:
  match q:
    case FGt.QPrompt{+k, +g}:
      {==}
    case FGt.QUsage{+g}:
      LE.gte.ms(Gt.usage(g), "")
    case FGt.QHost{+g, +a}:
      LE.gte.host(Gt.host(g, a))

def GoalText.goal_text_entry_answers(q, fit):
  %Equal.sym(Wr.Dec<FGt.Req>, FGt.get_req(GoalText.gt_w_req(q, "")), Wr.Got{q, ""}, LE.gte.req_rt(q, "", fit)) : {FGt.ffi.got(_) == GoalText.gt_w_reply(q) : String}
  gta.reply(q)
