# eukhe: the proof of LAW commit_gate_on_seen_never_stale
#
# PROOF: an absent file computes; a present one is answered by gate.seen, which is never stale (dcf.st).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/base.bend as LawsBase
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/doc_commit/choices.bend as DocCommitChoices
import ./base.bend as LA
import ./base/choices.bend as LC

def dcf.st(m: Bool) -> {DocCommitChoices.stale(Cm.gate.seen(m)) == False{} : Bool}:
  match m:
    case True{}:
      {==}
    case False{}:
      {==}

def DocCommitChoices.commit_gate_on_seen_never_stale(s, d):
  match d:
    case Cm.Absent{}:
      {==}
    case Cm.Present{+g, e}:
      dcf.st(Cm.member(g, s))
