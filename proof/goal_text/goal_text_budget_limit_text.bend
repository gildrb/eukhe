# eukhe: the proof of LAW goal_text_budget_limit_text
#
# PROOF: the code fills the same format string; each placeholder's helper answers the spec's (gtt.*).

import Base
import ../../bend/goal_text.bend as Gt
import ../../laws/goal_text.bend as GoalText
import ./base/text.bend as LT

def GoalText.goal_text_budget_limit_text(s, o, b, u, t):
  %LT.gtt.obj(o) : {Gt.budget_limit.of(Gt.objective(o), u, Gt.budget_text(b), t) == Gt.budget_limit.of(_, u, GoalText.gt_budget(b), t) : String}
  %LT.gtt.bud(b) : {Gt.budget_limit.of(Gt.objective(o), u, Gt.budget_text(b), t) == Gt.budget_limit.of(Gt.objective(o), u, _, t) : String}
  {==}
