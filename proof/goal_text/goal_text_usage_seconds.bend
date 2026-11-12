# eukhe: the proof of LAW goal_text_usage_seconds
#
# PROOF: the seconds are not "0", so the line is the seconds.

import Base
import ../../bend/goal_text.bend as Gt
import ../../laws/goal_text.bend as GoalText
import ./base/text.bend as LT

def GoalText.goal_text_usage_seconds(s, o, u, t, nz):
  %Equal.sym(Bool, String.eq(t, "0"), False{}, nz) : {Gt.usage.seconds(_, t) == Some{String.append(t, "s")} : Maybe<&2, String>}
  {==}
