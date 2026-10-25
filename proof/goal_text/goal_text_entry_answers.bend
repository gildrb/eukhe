# eukhe: the proof of LAW goal_text_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left (gte.req_rt), so the entry answers the model's answer, the spec's (the model laws), spelled by encoders that are the spec spellers (gte.ms, gte.host).

import Base
import ../../bend/goal_text.bend as Gt
import ../../bend/ffi_goal_text.bend as FGt
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/goal_text.bend as GoalText
import ./base/entry.bend as LE
import ./goal_text_prompt_spec.bend as PGoalTextPromptSpec
import ./goal_text_usage_spec.bend as PGoalTextUsageSpec
import ./goal_text_host_spec.bend as PGoalTextHostSpec

def gta.reply(q: FGt.Req) -> {FGt.answer(q) == GoalText.gt_w_reply(q) : String}:
  match q:
    case FGt.QPrompt{+k, +g}:
      %GoalText.goal_text_prompt_spec(k, g) : {Wr.put_str(Gt.prompt(k, g), "") == Wr.put_str(_, "") : String}
      {==}
    case FGt.QUsage{+g}:
      %GoalText.goal_text_usage_spec(g) : {FGt.put_ms(Gt.usage(g), "") == GoalText.gt_w_ms(_, "") : String}
      LE.gte.ms(Gt.usage(g), "")
    case FGt.QHost{+g, +a}:
      %GoalText.goal_text_host_spec(g, a) : {FGt.put_host(Gt.host(g, a)) == GoalText.gt_w_host(_) : String}
      LE.gte.host(Gt.host(g, a))

def GoalText.goal_text_entry_answers(q, fit):
  %Equal.sym(Wr.Dec<FGt.Req>, FGt.get_req(GoalText.gt_w_req(q, "")), Wr.Got{q, ""}, LE.gte.req_rt(q, "", fit)) : {FGt.ffi.got(_) == GoalText.gt_w_reply(q) : String}
  gta.reply(q)
