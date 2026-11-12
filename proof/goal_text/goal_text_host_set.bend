# eukhe: the proof of LAW goal_text_host_set
#
# PROOF: a status that is not idle: the code answers the tokens left and the report of each case as the spec (gth.set); the idle status contradicts the premise.

import Base
import ../../bend/goal_text.bend as Gt
import ../../laws/goal_text.bend as GoalText
import ./base/text.bend as LT
import ../base/staging.bend as LStg

def GoalText.goal_text_host_set(s, x, b, u, t, ask, busy):
  match s:
    case Gt.SIdle{}:
      LStg.stg.absurd({Gt.host(Gt.Goal{Gt.SIdle{}, Some{x}, b, u, t}, ask) == Some{Gt.Host{GoalText.gt_left_of(b, u), GoalText.gt_report_if(Bool.and(ask, GoalText.gt_complete(Gt.SIdle{})), b, u, t)}} : Maybe<&2, Gt.Host>}, busy)
    case Gt.SActive{}:
      LT.gth.set(Gt.SActive{}, x, b, u, t, Bool.and(ask, False{}))
    case Gt.SPaused{}:
      LT.gth.set(Gt.SPaused{}, x, b, u, t, Bool.and(ask, False{}))
    case Gt.SBudgetLimited{}:
      LT.gth.set(Gt.SBudgetLimited{}, x, b, u, t, Bool.and(ask, False{}))
    case Gt.SComplete{}:
      LT.gth.set(Gt.SComplete{}, x, b, u, t, Bool.and(ask, True{}))
    case Gt.SError{}:
      LT.gth.set(Gt.SError{}, x, b, u, t, Bool.and(ask, False{}))
