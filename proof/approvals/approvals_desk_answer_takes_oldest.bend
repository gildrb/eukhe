# eukhe: the proof of LAW approvals_desk_answer_takes_oldest
# PROOF: the search finds q, the first question waiting on the clients
# under id, and the others in order (LAD.ad.find_hit, by induction on pre);
# the answer's fate is the clients' yes or no (LAD.ap.answered).

import Base
import ../../bend/approvals.bend as Am
import ../../laws/approvals/desk.bend as ApprovalsDesk
import ./base/desk.bend as LAD

def ApprovalsDesk.approvals_desk_answer_takes_oldest(n, pre, k, id, es, post, yes, none):
  +Q = {Am.Q{k, id, es, Am.OnClients{}} : Am.Q}
  +QS = List.append(&2, Am.Q, pre, Q <> post)
  +R = List.append(&2, Am.Q, pre, post)
  %Equal.sym(Am.QF, Am.find(QS, id), Am.QFound{Q, R}, LAD.ad.find_hit(pre, k, id, es, post, none)) : {Am.answer.with(n, QS, yes, _) == (Am.D{n, R}, [Am.ASettle{k}, Am.AWake{k, ApprovalsDesk.sp_answered(es, yes)}, Am.ATook{}]) : Am.D & List<&2, Am.Act>}
  %Equal.sym(Am.Fate, Am.answered(es, yes), ApprovalsDesk.sp_answered(es, yes), LAD.ap.answered(es, yes)) : {(Am.D{n, R}, [Am.ASettle{k}, Am.AWake{k, _}, Am.ATook{}]) == (Am.D{n, R}, [Am.ASettle{k}, Am.AWake{k, ApprovalsDesk.sp_answered(es, yes)}, Am.ATook{}]) : Am.D & List<&2, Am.Act>}
  {==}
