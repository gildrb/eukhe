# eukhe: the proof of LAW gateway_report_failed_left
#
# PROOF: by the end's answer: nothing leaves the held answer, a failure
# is itself; last makes either the failure r, and its report adds the
# left words on one line (grb.line). A text or a stop is no failure (last
# contradicts it).

import Base
import ../../bend/gateway_answer.bend as Ga
import ../../bend/gateway_report.bend as Gr
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_report.bend as GatewayReport
import ../gateway_answer/base.bend as LA
import ./base.bend as LR

# the report the law names: r, then what is left
def grfl.R(r: String, g: GatewayAnswer.GaText) -> Gr.Out:
  Gr.Out{Ga.ANone{}, Ga.AFailed{String.append(r, String.append("\nLeft: ", String.join(GatewayAnswer.ga_words_of(g), " ")))}}

# the report of the failure r
def grfl.report(+r: String, +g: GatewayAnswer.GaText, +well: {GatewayAnswer.ga_well(g, True{}) == True{} : Bool}, +some: {GatewayAnswer.ga_has_word(g) == True{} : Bool}) -> {Gr.Out{Ga.ANone{}, Gr.report(Ga.AFailed{r}, Some{GatewayAnswer.ga_spell(g)})} == grfl.R(r, g) : Gr.Out}:
  Equal.cong(String, Gr.Out, z => Gr.Out{Ga.ANone{}, Ga.AFailed{z}}, Gr.left(r, "\n", Some{GatewayAnswer.ga_spell(g)}), String.append(r, String.append("\nLeft: ", String.join(GatewayAnswer.ga_words_of(g), " "))), LR.grb.line(r, "\n", g, well, some))

# the run's last answer k is the failure r: the run end reports r with
# what is left
def grfl.last(+k: Ga.Answer, +r: String, +g: GatewayAnswer.GaText, last: {k == Ga.AFailed{r} : Ga.Answer}, +well: {GatewayAnswer.ga_well(g, True{}) == True{} : Bool}, +some: {GatewayAnswer.ga_has_word(g) == True{} : Bool}) -> {Gr.Out{Ga.ANone{}, Gr.report(k, Some{GatewayAnswer.ga_spell(g)})} == grfl.R(r, g) : Gr.Out}:
  %Equal.sym(Ga.Answer, k, Ga.AFailed{r}, last) : {Gr.Out{Ga.ANone{}, Gr.report(_, Some{GatewayAnswer.ga_spell(g)})} == grfl.R(r, g) : Gr.Out}
  grfl.report(r, g, well, some)

def GatewayReport.gateway_report_failed_left(h, a, r, g, last, well, some):
  match a:
    case Ga.ANone{}:
      grfl.last(h, r, g, last, well, some)
    case Ga.AText{+t}:
      LA.gab.absurd({Gr.step(h, Ga.AText{t}, Gr.ERun{False{}, Some{GatewayAnswer.ga_spell(g)}}) == grfl.R(r, g) : Gr.Out}, Equal.cong(Ga.Answer, Bool, LR.grb.is_failed, Ga.AText{t}, Ga.AFailed{r}, last))
    case Ga.AFailed{+r2}:
      grfl.last(Ga.AFailed{r2}, r, g, last, well, some)
    case Ga.AStopped{}:
      LA.gab.absurd({Gr.step(h, Ga.AStopped{}, Gr.ERun{False{}, Some{GatewayAnswer.ga_spell(g)}}) == grfl.R(r, g) : Gr.Out}, Equal.cong(Ga.Answer, Bool, LR.grb.is_failed, Ga.AStopped{}, Ga.AFailed{r}, last))
