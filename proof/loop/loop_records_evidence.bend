# eukhe: the proof of LAW loop_records_evidence
#
# PROOF: the event is the loop's own (lb.judging_mine); lb.records splits the
# condition and the evidence under both premises (lb.When): a confirmed and a
# broken check end with Check{i, ev}; a refuted one advances with it, and an
# advance keeps it (lb.adv_last); no condition and a cancelled check are
# excluded by the premises.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_records_evidence(i, l, d, c, b, f, x, ev, now, fu, hc, hd):
  %LALoopBounds.lb.judging_mine(i, l, d, c, b, f, x, ev, False{}, now, fu) : {S.last(S.state(_)) == Lp.Check{i, ev} : Lp.Last}
  LALoopBounds.lb.when2(S.has_cond(c), S.decides(ev), {S.last(S.state(Lp.judged.cond(c, i, l, d, b, f, x, ev, now, fu))) == Lp.Check{i, ev} : Lp.Last}, hc, hd, LALoopBounds.lb.records(c, ev, i, l, d, b, f, x, now, fu))
