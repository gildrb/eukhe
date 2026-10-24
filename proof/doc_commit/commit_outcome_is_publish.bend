# eukhe: the proof of LAW commit_outcome_is_publish
#
# PROOF: every operation and fault computes.

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit

def dcw.pub(k: Cm.Op, x: Cm.Fault, -c: Bool) -> {DocCommit.sp_out(Cm.outcome(DocCommit.sp_pub(k, x))) == Cm.publish(Cm.Doc{k, c, x}) : Cm.Out}:
  match k:
    case Cm.Update{}:
      match x:
        case Cm.Clean{}:
          {==}
        case Cm.Sync{}:
          {==}
        case Cm.Publish{}:
          {==}
        case Cm.Remove{}:
          {==}
    case Cm.Moving{}:
      match x:
        case Cm.Clean{}:
          {==}
        case Cm.Sync{}:
          {==}
        case Cm.Publish{}:
          {==}
        case Cm.Remove{}:
          {==}

def DocCommit.commit_outcome_is_publish(k, c, x):
  dcw.pub(k, x, c)
