# eukhe: the proof of LAW gateway_commands_near
#
# PROOF: the text routes to the code's answer to an unknown name (gcb.unknown); no command starts with it (gcb.starting, pre), so the code names slash_suggest's pick j (sug), the laws' j-th name (gcb.pick).

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/gateway_answer.bend as Ga
import ../../bend/slash_suggest.bend as Ss
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_commands.bend as GatewayCommands
import ../gateway_answer/base.bend as LGa
import ./base.bend as LA

def GatewayCommands.gateway_commands_near(t, sess, c, n, j, well, ws, nm, own, none, pre, sug):
  +L = String.to_lower(SCon{c, n})
  +e1 = LA.gcb.unknown(t, sess, SCon{c, n}, [], well, ws, nm, own, none)
  +e2 = Equal.trans(List<&2, String>, Gc.starting(L, Gc.specs()), GatewayCommands.gc_starting(L, Gc.names(Gc.specs()), Gc.lines(Gc.specs(), [])), Nil{}, LA.gcb.starting(L, Gc.specs()), pre)
  %LA.gcb.pick(Gc.names(Gc.specs()), j) : {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OAnswer{String.concat(["No command /", L, ". Did you mean /", _, "?\nNot sent to the agent. Send / for all commands."])} : Gc.Out}
  %sug : {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OAnswer{Gc.suggest.far(L, _)} : Gc.Out}
  %e2 : {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OAnswer{Gc.suggest.near(L, _)} : Gc.Out}
  e1
