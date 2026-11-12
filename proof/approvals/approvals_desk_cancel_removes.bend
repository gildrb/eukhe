# eukhe: the proof of LAW approvals_desk_cancel_removes
# PROOF: the search by key finds the question, the first with key k, and
# the others in order (LAD.ad.take_hit, by induction on pre); the cancel of
# what it found then computes for each wait.

import Base
import ../../bend/approvals.bend as Am
import ../../laws/approvals/desk.bend as ApprovalsDesk
import ./base/desk.bend as LAD

# the cancel of key k is the cancel of the question the search finds
def pc.at(+n: Nat, +pre: List<&2, Am.Q>, +k: Nat, +i: String, +es: List<&2, Nat>, +w: Am.Wait, +post: List<&2, Am.Q>, none: {ApprovalsDesk.ds_no_key(pre, k) == True{} : Bool}) -> {Am.dstep(Am.D{n, List.append(&2, Am.Q, pre, Am.Q{k, i, es, w} <> post)}, Am.ECancel{k}) == Am.cancel.with(n, List.append(&2, Am.Q, pre, Am.Q{k, i, es, w} <> post), Am.QFound{Am.Q{k, i, es, w}, List.append(&2, Am.Q, pre, post)}) : Am.D & List<&2, Am.Act>}:
  +QS = List.append(&2, Am.Q, pre, Am.Q{k, i, es, w} <> post)
  +F = {Am.QFound{Am.Q{k, i, es, w}, List.append(&2, Am.Q, pre, post)} : Am.QF}
  %Equal.sym(Am.QF, Am.take(QS, k), F, LAD.ad.take_hit(pre, k, i, es, w, post, none)) : {Am.cancel.with(n, QS, _) == Am.cancel.with(n, QS, F) : Am.D & List<&2, Am.Act>}
  {==}

def ApprovalsDesk.approvals_desk_cancel_removes(n, pre, k, i, es, post, none):
  +h = none
  (pc.at(n, pre, k, i, es, Am.OnClients{}, post, h), pc.at(n, pre, k, i, es, Am.OnParent{}, post, h))
