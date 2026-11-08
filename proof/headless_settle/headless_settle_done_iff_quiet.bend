# eukhe: the proof of LAW headless_settle_done_iff_quiet
#
# PROOF: the decision is the spec's (headless_settle_refines_spec), and
# the spec stops exactly when quiet, whatever the limit (hs.finished_pick).

import Base
import ../../bend/headless_settle.bend as Hs
import ../../spec/durable/headless.bend as Sp
import ../../laws/headless_settle.bend as HeadlessSettle
import ./headless_settle_refines_spec.bend as PHeadlessSettleRefinesSpec

def hs.finished_pick(q: Bool, l: Bool) -> {HeadlessSettle.finished(Sp.settle_spec.pick(q, l)) == q : Bool}:
  match q:
    case True{}:
      {==}
    case False{}:
      match l:
        case True{}:
          {==}
        case False{}:
          {==}

def HeadlessSettle.headless_settle_done_iff_quiet(f):
  %Equal.sym(Hs.Settle, Hs.settle(f), Sp.settle_spec(f), HeadlessSettle.headless_settle_refines_spec(f)) : {HeadlessSettle.finished(_) == Sp.quiet(f) : Bool}
  hs.finished_pick(Sp.quiet(f), Sp.limit_hit(f))
