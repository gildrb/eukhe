# eukhe: the proof of LAW goal_text_usage_no_time
#
# PROOF: without a budget and with "0" seconds the usage line computes to none.

import Base
import ../../bend/goal_text.bend as Gt
import ../../laws/goal_text.bend as GoalText
import ./base/text.bend as LT

def GoalText.goal_text_usage_no_time(s, o, u):
  {==}
