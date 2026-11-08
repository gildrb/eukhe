# eukhe: the proof of LAW doc_publish_refines_spec
#
# PROOF: the three re-reads; on other bytes both sides choose on
# Nat.is_lt(n, 3n) (the code's bound and the spec's are 3), the same way
# for each answer.

import Base
import ../../bend/doc_publish.bend as Dp
import ../../laws/doc_publish.bend as DocPublish
import ../../spec/harness/doc_publish.bend as S

def dps.moved(lt: Bool) -> {Dp.step.moved(lt) == S.step.moved(lt) : Dp.Step}:
  match lt:
    case True{}:
      {==}
    case False{}:
      {==}

def DocPublish.doc_publish_refines_spec(n, s):
  match s:
    case Dp.Same{}:
      {==}
    case Dp.Gone{}:
      {==}
    case Dp.Moved{}:
      dps.moved(Nat.is_lt(n, Dp.bound()))
