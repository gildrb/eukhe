# eukhe: the proof of LAW approvals_desk_back_wakes
# PROOF: the search by key finds the question, the first with key k, and
# the others in order (LAD.ad.take_hit, by induction on pre); the parent's
# answer to what it found then computes for each wait.

import Base
import ../../bend/approvals.bend as Am
import ../../laws/approvals/desk.bend as ApprovalsDesk
import ./base/desk.bend as LAD

# the parent's answer to key k is its answer to the question the search
# finds
def pb.at(+n: Nat, +pre: List<&2, Am.Q>, +k: Nat, +i: String, +es: List<&2, Nat>, +w: Am.Wait, +post: List<&2, Am.Q>, +f: Am.Fate, none: {ApprovalsDesk.ds_no_key(pre, k) == True{} : Bool}) -> {Am.dstep(Am.D{n, List.append(&2, Am.Q, pre, Am.Q{k, i, es, w} <> post)}, Am.EBack{k, f}) == Am.back.with(n, List.append(&2, Am.Q, pre, Am.Q{k, i, es, w} <> post), f, Am.QFound{Am.Q{k, i, es, w}, List.append(&2, Am.Q, pre, post)}) : Am.D & List<&2, Am.Act>}:
  +QS = List.append(&2, Am.Q, pre, Am.Q{k, i, es, w} <> post)
  +F = {Am.QFound{Am.Q{k, i, es, w}, List.append(&2, Am.Q, pre, post)} : Am.QF}
  %Equal.sym(Am.QF, Am.take(QS, k), F, LAD.ad.take_hit(pre, k, i, es, w, post, none)) : {Am.back.with(n, QS, f, _) == Am.back.with(n, QS, f, F) : Am.D & List<&2, Am.Act>}
  {==}

def ApprovalsDesk.approvals_desk_back_wakes(n, pre, k, i, es, post, f, none):
  +h = none
  (pb.at(n, pre, k, i, es, Am.OnParent{}, post, f, h), pb.at(n, pre, k, i, es, Am.OnClients{}, post, f, h))
