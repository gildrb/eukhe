# eukhe: the proof of LAW approvals_desk_gateway_never_waits
# The session's decision with only the phone gateway ends the question by
# the gateway rule: `route([Phone])` ends Ruled, and the fate of a step
# that ends Ruled is the rule's (the law's Am.fate at Ruled computes to
# the same `rule`).

import Base
import ../../bend/approvals.bend as Am
import ../../laws/approvals/desk.bend as ApprovalsDesk

def ApprovalsDesk.approvals_desk_gateway_never_waits(d, id, es, p):
  match d:
    case Am.D{+n, +qs}:
      {==}
