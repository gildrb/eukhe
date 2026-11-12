# eukhe: the proof of LAW loop_evidence_only_from_checks
#
# PROOF: lb.kept splits the event under the premise (lb.Unless): a new `/loop`
# and a judged check are excluded; a stop, an abort, a prompt and a restart
# rebuild the state with the same evidence; a settled turn keeps it through
# the gate and the advance (lb.kept_settled, lb.adv_last).

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_evidence_only_from_checks(s, e, h):
  match s:
    case Lp.St{p, i, l, d, c, b, f, x}:
      LALoopBounds.lb.unless(Bool.or(S.is_enter(e), S.is_judged(e)), LALoopBounds.lb.Kept(Lp.step(Lp.St{p, i, l, d, c, b, f, x}, e), x), h, LALoopBounds.lb.kept(e, p, i, l, d, c, b, f, x))
