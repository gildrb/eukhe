# eukhe: the proof of LAW flag_needs_reason: the code's non-empty test
# is the spec's (AgLog.ag.some_eq)

import Base
import ../../bend/autoresearch/line.bend as ArL
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../spec/autoresearch/metric_line.bend as SL
import ../../laws/autoresearch/events.bend as AutoresearchEvents
import ./base/log.bend as AgLog

def AutoresearchEvents.flag_needs_reason(s, n, reason, empty):
  +e = Equal.trans(Bool, ArL.some(reason), SL.nonempty(reason), False{}, AgLog.ag.some_eq(reason), empty)
  %Equal.sym(Bool, ArL.some(reason), False{}, e) : {ArP.flag.reason(_, s, n) == ArS.Refuse{ArP.t_reason()} : ArS.Res}
  {==}
