# eukhe: the proof of LAW commit_gate_unseen_refused
#
# PROOF: the gate goes on exactly when the shipped membership finds the digest (dcf.go_m), which finds it only in a place of its own text (dcq.mem_only).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/base.bend as LawsBase
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/doc_commit/choices.bend as DocCommitChoices
import ./base.bend as LA
import ./base/choices.bend as LC

def dcf.go_m(m: Bool) -> {m == DocCommit.proceeds(Cm.gate.seen(m)) : Bool}:
  match m:
    case True{}:
      {==}
    case False{}:
      {==}

def DocCommitChoices.commit_gate_unseen_refused(s, g, e, go):
  LC.dcq.mem_only(g, s, Equal.trans(Bool, Cm.member(g, s), DocCommit.proceeds(Cm.gate.seen(Cm.member(g, s))), True{}, dcf.go_m(Cm.member(g, s)), go))
