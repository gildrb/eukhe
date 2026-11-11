# eukhe: the proof of LAW approvals_desk_unknown_key
# PROOF: the search by key finds nothing (LAD.ad.take_none, by induction
# on the questions), so neither the cancel nor the parent's answer
# changes anything.

import Base
import ../../bend/approvals.bend as Am
import ../../laws/approvals/desk.bend as ApprovalsDesk
import ./base/desk.bend as LAD

def pu.cancel(+n: Nat, +qs: List<&2, Am.Q>, +k: Nat, c: {Am.QNone{} == Am.take(qs, k) : Am.QF}) -> {Am.dstep(Am.D{n, qs}, Am.ECancel{k}) == (Am.D{n, qs}, Nil{}) : Am.D & List<&2, Am.Act>}:
  %c : {Am.cancel.with(n, qs, _) == (Am.D{n, qs}, Nil{}) : Am.D & List<&2, Am.Act>}
  {==}

def pu.back(+n: Nat, +qs: List<&2, Am.Q>, +k: Nat, +f: Am.Fate, c: {Am.QNone{} == Am.take(qs, k) : Am.QF}) -> {Am.dstep(Am.D{n, qs}, Am.EBack{k, f}) == (Am.D{n, qs}, Nil{}) : Am.D & List<&2, Am.Act>}:
  %c : {Am.back.with(n, qs, f, _) == (Am.D{n, qs}, Nil{}) : Am.D & List<&2, Am.Act>}
  {==}

def ApprovalsDesk.approvals_desk_unknown_key(n, qs, k, f, none):
  +e = LAD.ad.take_none(qs, k, none)
  +c = Equal.sym(Am.QF, Am.take(qs, k), Am.QNone{}, e)
  (pu.cancel(n, qs, k, c), pu.back(n, qs, k, f, c))
