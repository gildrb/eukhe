# eukhe: the proof of LAW approvals_fate_spec
# PROOF: a case per end of the question: the answer's fate is the spec's
# (a case on yes), no answer computes to unanswered, the gateway rule is
# the spec's (ap.rule).

import Base
import ../../bend/approvals.bend as Am
import ../../laws/approvals/desk.bend as ApprovalsDesk
import ./base/desk.bend as LAD

def ApprovalsDesk.approvals_fate_spec(es, e):
  match e:
    case Am.Answered{a, y}:
      match y:
        case True{}:
          {==}
        case False{}:
          {==}
    case Am.Unanswered{}:
      {==}
    case Am.Ruled{a}:
      LAD.ap.rule(es)
