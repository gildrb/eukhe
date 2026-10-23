# eukhe: the proof of LAW quiet_is_unanswered

import Base
import ../../bend/approvals.bend as Am
import ../../laws/approvals.bend as Approvals
import ../base.bend as L
import ./base.bend as LA

def pa.quiet_none(+ds: List<&2, Am.Desk>, quiet: {Am.quiet(ds) == True{} : Bool}) -> {Am.Out.end(Am.route(ds)) == Am.Unanswered{} : Am.End}:
  match ds:
    case Nil{}:
      {==}
    case d <> rest:
      match d:
        case Am.Away{}:
          LA.pa.end_up_is(Am.route(rest), Am.Unanswered{}, pa.quiet_none(rest, quiet))
        case Am.Left{}:
          LA.pa.end_first_up_is(Am.route(rest), Am.Unanswered{}, pa.quiet_none(rest, quiet))
        case Am.Says{y}:
          L.approvals.pa.absurdF({Am.Out.end(Am.route(Am.Says{y} <> rest)) == Am.Unanswered{} : Am.End}, quiet)
        case Am.Phone{}:
          L.approvals.pa.absurdF({Am.Out.end(Am.route(Am.Phone{} <> rest)) == Am.Unanswered{} : Am.End}, quiet)
        case Am.PhoneLeft{}:
          L.approvals.pa.absurdF({Am.Out.end(Am.route(Am.PhoneLeft{} <> rest)) == Am.Unanswered{} : Am.End}, quiet)

def Approvals.quiet_is_unanswered(ds, quiet):
  pa.quiet_none(ds, quiet)
