# eukhe: the proof of LAW gateway_report_waits
#
# PROOF: by the answer: nothing, a text and a failure compute; a stop
# contradicts ns.

import Base
import ../../bend/gateway_answer.bend as Ga
import ../../bend/gateway_report.bend as Gr
import ../../laws/gateway_report.bend as GatewayReport
import ../gateway_answer/base.bend as LA

def GatewayReport.gateway_report_waits(h, a, l, ns):
  match a:
    case Ga.ANone{}:
      {==}
    case Ga.AText{t}:
      {==}
    case Ga.AFailed{t}:
      {==}
    case Ga.AStopped{}:
      LA.gab.absurd({Gr.step(h, Ga.AStopped{}, Gr.ERun{True{}, l}) == Gr.Out{GatewayReport.gr_last(h, Ga.AStopped{}), Ga.ANone{}} : Gr.Out}, ns)
