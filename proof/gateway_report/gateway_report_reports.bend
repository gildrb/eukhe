# eukhe: the proof of LAW gateway_report_reports
#
# PROOF: the run end sends the report of the run's last answer
# (grb.last_end); with no left text that report is the answer as it is
# (grb.report_plain).

import Base
import ../../bend/gateway_answer.bend as Ga
import ../../bend/gateway_report.bend as Gr
import ../../laws/gateway_report.bend as GatewayReport
import ./base.bend as LR

def GatewayReport.gateway_report_reports(h, a, l, ns, none):
  +k = GatewayReport.gr_last(h, a)
  Equal.trans(Gr.Out, Gr.step(h, a, Gr.ERun{False{}, l}), Gr.Out{Ga.ANone{}, Gr.report(k, l)}, Gr.Out{Ga.ANone{}, k}, LR.grb.last_end(h, a, l, ns), Equal.cong(Ga.Answer, Gr.Out, z => Gr.Out{Ga.ANone{}, z}, Gr.report(k, l), k, LR.grb.report_plain(k, l, none)))
