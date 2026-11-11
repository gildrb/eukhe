# eukhe: the proof of LAW gateway_answer_blank
#
# PROOF: the code joins the blocks as Base's join does (gab.join); that text is blank (blank, gab.blank), so nothing is sent. Other stops contradict st.

import Base
import ../../bend/gateway_answer.bend as Ga
import ../../laws/gateway_answer.bend as GatewayAnswer
import ./base.bend as LA

# the joined blocks answered, given whether they are blank
def gab2.pick(+ts: List<&2, String>, +bb: Bool, +hb: {Ga.blank(String.join(ts, "\n\n")) == bb : Bool}) -> {Ga.text(ts) == Ga.text.of(String.join(ts, "\n\n"), bb) : Ga.Answer}:
  +j = Ga.join("\n\n", ts)
  +J = String.join(ts, "\n\n")
  +e = LA.gab.join("\n\n", ts)
  %hb : {Ga.text(ts) == Ga.text.of(J, _) : Ga.Answer}
  Equal.cong(String, Ga.Answer, z => Ga.text.of(z, Ga.blank(z)), j, J, e)

def gab2.empty(+ts: List<&2, String>, +blank: {GatewayAnswer.ga_empty(String.join(ts, "\n\n")) == True{} : Bool}) -> {Ga.text(ts) == Ga.ANone{} : Ga.Answer}:
  +J = String.join(ts, "\n\n")
  gab2.pick(ts, True{}, Equal.trans(Bool, Ga.blank(J), GatewayAnswer.ga_empty(J), True{}, LA.gab.blank(J), blank))

def GatewayAnswer.gateway_answer_blank(s, ts, e, st, blank):
  match s:
    case Ga.SStop{}:
      gab2.empty(ts, blank)
    case Ga.SLength{}:
      gab2.empty(ts, blank)
    case Ga.SError{}:
      LA.gab.absurd({Ga.answer(Ga.EAssistant{Ga.SError{}, ts, e}) == Ga.ANone{} : Ga.Answer}, st)
    case Ga.SAborted{}:
      LA.gab.absurd({Ga.answer(Ga.EAssistant{Ga.SAborted{}, ts, e}) == Ga.ANone{} : Ga.Answer}, st)
    case Ga.SToolUse{}:
      LA.gab.absurd({Ga.answer(Ga.EAssistant{Ga.SToolUse{}, ts, e}) == Ga.ANone{} : Ga.Answer}, st)
