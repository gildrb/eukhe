# eukhe: the proof of LAW gateway_commands_far
#
# PROOF: the text routes to the code's answer to an unknown name (gcb.unknown); no command starts with it (gcb.starting, pre) and slash_suggest picks none (sug), so the code answers the miss and its help text, the laws' (gcb.help).

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/gateway_answer.bend as Ga
import ../../bend/slash_suggest.bend as Ss
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_commands.bend as GatewayCommands
import ../gateway_answer/base.bend as LGa
import ./base.bend as LA

def GatewayCommands.gateway_commands_far(t, sess, c, n, well, ws, nm, own, none, pre, sug):
  +L = String.to_lower(SCon{c, n})
  +e1 = LA.gcb.unknown(t, sess, SCon{c, n}, [], well, ws, nm, own, none)
  +e2 = Equal.trans(List<&2, String>, Gc.starting(L, Gc.specs()), GatewayCommands.gc_starting(L, Gc.names(Gc.specs()), Gc.lines(Gc.specs(), [])), Nil{}, LA.gcb.starting(L, Gc.specs()), pre)
  %sug : {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OAnswer{Gc.suggest.far(L, _)} : Gc.Out}
  %e2 : {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OAnswer{Gc.suggest.near(L, _)} : Gc.Out}
  e1
