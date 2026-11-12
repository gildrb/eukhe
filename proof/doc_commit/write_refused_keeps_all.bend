# eukhe: the proof of LAW write_refused_keeps_all
#
# PROOF: the write is refused exactly on the unseen arm, which keeps the disk and the seen versions; on the other arm the write wrote.

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit
import ./base.bend as LA

def dcf.wr_refused(b: Bool, +d: Maybe<&2, Nat>, +s: List<&2, Nat>, +c: Nat, no: {DocCommit.wrote(Cm.write.go(b, d, s, c)) == False{} : Bool}) -> {Cm.write.go(b, d, s, c) == Cm.Wt{False{}, d, s} : Cm.Wt}:
  match b:
    case True{}:
      {==}
    case False{}:
      LA.dcw.tf({Cm.write.go(False{}, d, s, c) == Cm.Wt{False{}, d, s} : Cm.Wt}, no)

def DocCommit.write_refused_keeps_all(d, s, c, no):
  dcf.wr_refused(Cm.unseen(d, s), d, s, c, no)
