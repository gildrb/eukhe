# eukhe: the proof of LAW autonomous_claim_end_stops
#
# PROOF: by cases on the label, the budget and the reading: where the
# claim does not go on, both sides compute; where it goes on (a passing
# label, the budget working, the reading missing or work left), the
# premise reads True == False.

import Base
import ../../bend/verify.bend as V
import ../../bend/autonomous.bend as Au
import ../../bend/ffi_autonomous.bend as FAu
import ../../bend/work_left.bend as Wl
import ../../bend/wire.bend as Wr
import ../../spec/autonomous/autonomous.bend as SpA
import ../../laws/autonomous.bend as Autonomous
import ./base.bend as LAAutonomous

def au.BI(x: Bool, G: Type) -> Type:
  match x:
    case True{}:
      Unit
    case False{}:
      G

def au.goes_on_false(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : au.BI(_, G)
  Unit{}

def Autonomous.autonomous_claim_end_stops(l, b, r, h):
  match l:
    case V.Verified{}:
      match b:
        case Au.Working{}:
          match r:
            case Wl.Unread{}:
              au.goes_on_false({Au.decide(Au.Facts{True{}, Au.Settled{}, Au.Ended{V.Verified{}}, Au.Working{}, Wl.Unread{}}) == Au.Stop{Au.ByChecks{V.Verified{}}} : Au.Step}, h)
            case Wl.Finished{}:
              {==}
            case Wl.Left{}:
              au.goes_on_false({Au.decide(Au.Facts{True{}, Au.Settled{}, Au.Ended{V.Verified{}}, Au.Working{}, Wl.Left{}}) == Au.Stop{Au.ByChecks{V.Verified{}}} : Au.Step}, h)
            case Wl.Unjudged{}:
              {==}
        case Au.Short{}:
          match r:
            case Wl.Unread{}:
              {==}
            case Wl.Finished{}:
              {==}
            case Wl.Left{}:
              {==}
            case Wl.Unjudged{}:
              {==}
    case V.Failed{}:
      match b:
        case Au.Working{}:
          match r:
            case Wl.Unread{}:
              {==}
            case Wl.Finished{}:
              {==}
            case Wl.Left{}:
              {==}
            case Wl.Unjudged{}:
              {==}
        case Au.Short{}:
          match r:
            case Wl.Unread{}:
              {==}
            case Wl.Finished{}:
              {==}
            case Wl.Left{}:
              {==}
            case Wl.Unjudged{}:
              {==}
    case V.Unverified{}:
      match b:
        case Au.Working{}:
          match r:
            case Wl.Unread{}:
              {==}
            case Wl.Finished{}:
              {==}
            case Wl.Left{}:
              {==}
            case Wl.Unjudged{}:
              {==}
        case Au.Short{}:
          match r:
            case Wl.Unread{}:
              {==}
            case Wl.Finished{}:
              {==}
            case Wl.Left{}:
              {==}
            case Wl.Unjudged{}:
              {==}
    case V.Passed{}:
      match b:
        case Au.Working{}:
          match r:
            case Wl.Unread{}:
              au.goes_on_false({Au.decide(Au.Facts{True{}, Au.Settled{}, Au.Ended{V.Passed{}}, Au.Working{}, Wl.Unread{}}) == Au.Stop{Au.ByChecks{V.Passed{}}} : Au.Step}, h)
            case Wl.Finished{}:
              {==}
            case Wl.Left{}:
              au.goes_on_false({Au.decide(Au.Facts{True{}, Au.Settled{}, Au.Ended{V.Passed{}}, Au.Working{}, Wl.Left{}}) == Au.Stop{Au.ByChecks{V.Passed{}}} : Au.Step}, h)
            case Wl.Unjudged{}:
              {==}
        case Au.Short{}:
          match r:
            case Wl.Unread{}:
              {==}
            case Wl.Finished{}:
              {==}
            case Wl.Left{}:
              {==}
            case Wl.Unjudged{}:
              {==}
