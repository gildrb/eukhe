# eukhe: the proof of LAW approvals_desk_gateway_never_waits
# The session's decision with only the phone gateway ends the question by
# the gateway rule (`route([Phone])` computes to `rule`, which is the
# spec's rule: ap.rule).

import Base
import ../../bend/approvals.bend as Am
import ../../laws/approvals/desk.bend as ApprovalsDesk
import ./base/desk.bend as LAD

def ApprovalsDesk.approvals_desk_gateway_never_waits(d, id, es, p):
  match d:
    case Am.D{+n, +qs}:
      %LAD.ap.rule(es) : {(Am.D{1n+n, qs}, [Am.AWake{n, Am.rule(es)}]) == (Am.D{1n+n, qs}, [Am.AWake{n, _}]) : Am.D & List<&2, Am.Act>}
      {==}
