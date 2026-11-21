# eukhe: the proof of LAW gateway_report_holds
#
# PROOF: by the answer: a text or a failure is held; nothing and a stop
# contradict k.

import Base
import ../../bend/gateway_answer.bend as Ga
import ../../bend/gateway_report.bend as Gr
import ../../laws/gateway_report.bend as GatewayReport
import ../gateway_answer/base.bend as LA

def GatewayReport.gateway_report_holds(h, a, k):
  match a:
    case Ga.ANone{}:
      LA.gab.absurd({Gr.step(h, Ga.ANone{}, Gr.ENone{}) == Gr.Out{Ga.ANone{}, Ga.ANone{}} : Gr.Out}, k)
    case Ga.AText{t}:
      {==}
    case Ga.AFailed{t}:
      {==}
    case Ga.AStopped{}:
      LA.gab.absurd({Gr.step(h, Ga.AStopped{}, Gr.ENone{}) == Gr.Out{Ga.AStopped{}, Ga.ANone{}} : Gr.Out}, k)
