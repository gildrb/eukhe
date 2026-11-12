# eukhe: the proof of LAW gateway_answer_text
#
# PROOF: the code joins the blocks as Base's join does (gab.join); that text is not blank (full, gab.blank), so it is sent. Other stops contradict st.

import Base
import ../../bend/gateway_answer.bend as Ga
import ../../laws/gateway_answer.bend as GatewayAnswer
import ./base.bend as LA

# the joined blocks answered, given whether they are blank
def gat.pick(+ts: List<&2, String>, +bb: Bool, +hb: {Ga.blank(String.join(ts, "\n\n")) == bb : Bool}) -> {Ga.text(ts) == Ga.text.of(String.join(ts, "\n\n"), bb) : Ga.Answer}:
  +j = Ga.join("\n\n", ts)
  +J = String.join(ts, "\n\n")
  +e = LA.gab.join("\n\n", ts)
  %hb : {Ga.text(ts) == Ga.text.of(J, _) : Ga.Answer}
  Equal.cong(String, Ga.Answer, z => Ga.text.of(z, Ga.blank(z)), j, J, e)

def gat.full(+ts: List<&2, String>, +full: {GatewayAnswer.ga_empty(String.join(ts, "\n\n")) == False{} : Bool}) -> {Ga.text(ts) == Ga.AText{String.join(ts, "\n\n")} : Ga.Answer}:
  +J = String.join(ts, "\n\n")
  gat.pick(ts, False{}, Equal.trans(Bool, Ga.blank(J), GatewayAnswer.ga_empty(J), False{}, LA.gab.blank(J), full))

def GatewayAnswer.gateway_answer_text(s, ts, e, st, full):
  match s:
    case Ga.SStop{}:
      gat.full(ts, full)
    case Ga.SLength{}:
      gat.full(ts, full)
    case Ga.SError{}:
      LA.gab.absurd({Ga.answer(Ga.EAssistant{Ga.SError{}, ts, e}) == Ga.AText{String.join(ts, "\n\n")} : Ga.Answer}, st)
    case Ga.SAborted{}:
      LA.gab.absurd({Ga.answer(Ga.EAssistant{Ga.SAborted{}, ts, e}) == Ga.AText{String.join(ts, "\n\n")} : Ga.Answer}, st)
    case Ga.SToolUse{}:
      LA.gab.absurd({Ga.answer(Ga.EAssistant{Ga.SToolUse{}, ts, e}) == Ga.AText{String.join(ts, "\n\n")} : Ga.Answer}, st)
