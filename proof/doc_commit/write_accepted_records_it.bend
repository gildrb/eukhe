# eukhe: the proof of LAW write_accepted_records_it
#
# PROOF: a write that wrote took the seen arm: the disk holds the new content and the seen versions are saw, which on digests is the shipped seen list (dcl.seen_dg).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit
import ./base.bend as LA

def dcf.wr_yes(b: Bool, +d: Maybe<&2, Nat>, +s: List<&2, Nat>, +c: Nat, yes: {DocCommit.wrote(Cm.write.go(b, d, s, c)) == True{} : Bool}) -> {DocCommit.wt_disk(Cm.write.go(b, d, s, c)) == Some{c} : Maybe<&2, Nat>} & {DocCommit.dgs(DocCommit.wt_seen(Cm.write.go(b, d, s, c))) == Cm.seen(DocCommit.dg(c), DocCommit.dgs(s)) : List<&2, String>}:
  match b:
    case True{}:
      LA.dcw.ft({DocCommit.wt_disk(Cm.write.go(True{}, d, s, c)) == Some{c} : Maybe<&2, Nat>} & {DocCommit.dgs(DocCommit.wt_seen(Cm.write.go(True{}, d, s, c))) == Cm.seen(DocCommit.dg(c), DocCommit.dgs(s)) : List<&2, String>}, yes)
    case False{}:
      ({==}, Equal.sym(List<&2, String>, Cm.seen(DocCommit.dg(c), DocCommit.dgs(s)), DocCommit.dgs(Cm.saw(c, s)), LA.dcl.seen_dg(c, s)))

def DocCommit.write_accepted_records_it(d, s, c, yes):
  dcf.wr_yes(Cm.unseen(d, s), d, s, c, yes)
