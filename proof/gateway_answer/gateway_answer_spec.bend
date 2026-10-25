# eukhe: the proof of LAW gateway_answer_spec
#
# PROOF: case by case on the event; each text, line and blank test of the
# code is the spec's (gab.text, gab.reason).

import Base
import ../../bend/gateway_answer.bend as Ga
import ../../laws/gateway_answer.bend as GatewayAnswer
import ./base.bend as LA

def gas.failed(m: Maybe<&2, String>) -> {Ga.AFailed{Ga.reason(m)} == Ga.AFailed{GatewayAnswer.ga_line(m)} : Ga.Answer}:
  Equal.cong(String, Ga.Answer, z => Ga.AFailed{z}, Ga.reason(m), GatewayAnswer.ga_line(m), LA.gab.reason(m))

def GatewayAnswer.gateway_answer_spec(ev):
  match ev:
    case Ga.EAgentEnd{a}:
      match a:
        case True{}:
          {==}
        case False{}:
          {==}
    case Ga.EAssistant{s, ts, e}:
      match s:
        case Ga.SStop{}:
          LA.gab.text(ts)
        case Ga.SLength{}:
          LA.gab.text(ts)
        case Ga.SError{}:
          gas.failed(e)
        case Ga.SAborted{}:
          {==}
        case Ga.SToolUse{}:
          {==}
    case Ga.ETurnEnd{a, e}:
      match a:
        case True{}:
          {==}
        case False{}:
          match e:
            case None{}:
              {==}
            case Some{r}:
              gas.failed(Some{r})
    case Ga.EOther{}:
      {==}
