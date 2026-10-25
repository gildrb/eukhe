# eukhe: the proof of LAW goal_text_usage_spec
#
# PROOF: case by case on the budget and the seconds (gtb.usage).

import Base
import ../../bend/goal_text.bend as Gt
import ../../bend/ffi_goal_text.bend as FGt
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/goal_text.bend as GoalText
import ./base.bend as LA

def GoalText.goal_text_usage_spec(g):
  LA.gtb.usage(g)
