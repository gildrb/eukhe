# eukhe: the proof of LAW approvals_desk_answer_gone
# PROOF: the search finds nothing (LAD.ad.find_none, by induction on the
# questions), so the answer is gone and the desk kept.

import Base
import ../../bend/approvals.bend as Am
import ../../laws/approvals/desk.bend as ApprovalsDesk
import ./base/desk.bend as LAD

def ApprovalsDesk.approvals_desk_answer_gone(n, qs, id, yes, none):
  %Equal.sym(Am.QF, Am.find(qs, id), Am.QNone{}, LAD.ad.find_none(qs, id, none)) : {Am.answer.with(n, qs, yes, _) == (Am.D{n, qs}, [Am.AGone{}]) : Am.D & List<&2, Am.Act>}
  {==}
