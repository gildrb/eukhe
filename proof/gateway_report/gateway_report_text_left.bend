# eukhe: the proof of LAW gateway_report_text_left
#
# PROOF: by the end's answer: nothing leaves the held answer, a text is
# itself; last makes either the text t, and its report adds the left
# words on one line (grb.line). A failure or a stop is no text (last
# contradicts it).

import Base
import ../../bend/gateway_answer.bend as Ga
import ../../bend/gateway_report.bend as Gr
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_report.bend as GatewayReport
import ../gateway_answer/base.bend as LA
import ./base.bend as LR

# the report the law names: t, then what is left
def grt.R(t: String, g: GatewayAnswer.GaText) -> Gr.Out:
  Gr.Out{Ga.ANone{}, Ga.AText{String.append(t, String.append("\n\nLeft: ", String.join(GatewayAnswer.ga_words_of(g), " ")))}}

# the report of the text t
def grt.report(+t: String, +g: GatewayAnswer.GaText, +well: {GatewayAnswer.ga_well(g, True{}) == True{} : Bool}, +some: {GatewayAnswer.ga_has_word(g) == True{} : Bool}) -> {Gr.Out{Ga.ANone{}, Gr.report(Ga.AText{t}, Some{GatewayAnswer.ga_spell(g)})} == grt.R(t, g) : Gr.Out}:
  Equal.cong(String, Gr.Out, z => Gr.Out{Ga.ANone{}, Ga.AText{z}}, Gr.left(t, "\n\n", Some{GatewayAnswer.ga_spell(g)}), String.append(t, String.append("\n\nLeft: ", String.join(GatewayAnswer.ga_words_of(g), " "))), LR.grb.line(t, "\n\n", g, well, some))

# the run's last answer k is the text t: the run end reports t with what
# is left
def grt.last(+k: Ga.Answer, +t: String, +g: GatewayAnswer.GaText, last: {k == Ga.AText{t} : Ga.Answer}, +well: {GatewayAnswer.ga_well(g, True{}) == True{} : Bool}, +some: {GatewayAnswer.ga_has_word(g) == True{} : Bool}) -> {Gr.Out{Ga.ANone{}, Gr.report(k, Some{GatewayAnswer.ga_spell(g)})} == grt.R(t, g) : Gr.Out}:
  %Equal.sym(Ga.Answer, k, Ga.AText{t}, last) : {Gr.Out{Ga.ANone{}, Gr.report(_, Some{GatewayAnswer.ga_spell(g)})} == grt.R(t, g) : Gr.Out}
  grt.report(t, g, well, some)

def GatewayReport.gateway_report_text_left(h, a, t, g, last, well, some):
  match a:
    case Ga.ANone{}:
      grt.last(h, t, g, last, well, some)
    case Ga.AText{+t2}:
      grt.last(Ga.AText{t2}, t, g, last, well, some)
    case Ga.AFailed{+r}:
      LA.gab.absurd({Gr.step(h, Ga.AFailed{r}, Gr.ERun{False{}, Some{GatewayAnswer.ga_spell(g)}}) == grt.R(t, g) : Gr.Out}, Equal.cong(Ga.Answer, Bool, LR.grb.is_text, Ga.AFailed{r}, Ga.AText{t}, last))
    case Ga.AStopped{}:
      LA.gab.absurd({Gr.step(h, Ga.AStopped{}, Gr.ERun{False{}, Some{GatewayAnswer.ga_spell(g)}}) == grt.R(t, g) : Gr.Out}, Equal.cong(Ga.Answer, Bool, LR.grb.is_text, Ga.AStopped{}, Ga.AText{t}, last))
