# eukhe: the proof of LAW goal_text_continuation_text
#
# PROOF: the code fills the same format string; each placeholder's helper answers the spec's (gtt.*).

import Base
import ../../bend/goal_text.bend as Gt
import ../../laws/goal_text.bend as GoalText
import ./base/text.bend as LT

def GoalText.goal_text_continuation_text(s, o, b, u, t):
  %LT.gtt.obj(o) : {Gt.continuation.of(Gt.objective(o), Gt.status_name(s), u, Gt.budget_text(b), Gt.left_text(b, u)) == Gt.continuation.of(_, GoalText.gt_status(s), u, GoalText.gt_budget(b), GoalText.gt_remaining(b, u)) : String}
  %LT.gtt.st(s) : {Gt.continuation.of(Gt.objective(o), Gt.status_name(s), u, Gt.budget_text(b), Gt.left_text(b, u)) == Gt.continuation.of(Gt.objective(o), _, u, GoalText.gt_budget(b), GoalText.gt_remaining(b, u)) : String}
  %LT.gtt.bud(b) : {Gt.continuation.of(Gt.objective(o), Gt.status_name(s), u, Gt.budget_text(b), Gt.left_text(b, u)) == Gt.continuation.of(Gt.objective(o), Gt.status_name(s), u, _, GoalText.gt_remaining(b, u)) : String}
  %LT.gtt.rem(b, u) : {Gt.continuation.of(Gt.objective(o), Gt.status_name(s), u, Gt.budget_text(b), Gt.left_text(b, u)) == Gt.continuation.of(Gt.objective(o), Gt.status_name(s), u, Gt.budget_text(b), _) : String}
  {==}
