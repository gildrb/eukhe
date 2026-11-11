# eukhe: the proof of LAW gateway_answer_failed_blank
#
# PROOF: a missing reason names the failure; a blank one is blank for the code too (gab.blank), so it names the failure.

import Base
import ../../bend/gateway_answer.bend as Ga
import ../../laws/gateway_answer.bend as GatewayAnswer
import ./base.bend as LA

def GatewayAnswer.gateway_answer_failed_blank(ts, e, none):
  match e:
    case None{}:
      {==}
    case Some{+r}:
      +hb = Equal.trans(Bool, Ga.blank(r), GatewayAnswer.ga_empty(r), True{}, LA.gab.blank(r), none)
      %Equal.sym(Bool, Ga.blank(r), True{}, hb) : {Ga.AFailed{Ga.reason.of(r, _)} == Ga.AFailed{"the model request failed"} : Ga.Answer}
      {==}
