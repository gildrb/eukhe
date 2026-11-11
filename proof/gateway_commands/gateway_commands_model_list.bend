# eukhe: the proof of LAW gateway_commands_model_list
#
# PROOF: the text routes to the code's command lookup (gcb.known); `/model` alone lists.

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/gateway_answer.bend as Ga
import ../../bend/slash_suggest.bend as Ss
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_commands.bend as GatewayCommands
import ../gateway_answer/base.bend as LGa
import ./base.bend as LA

def GatewayCommands.gateway_commands_model_list(t, sess, name, well, ws, nm, cmd, own):
  +L = String.to_lower(name)
  Equal.trans(Gc.Out, Gc.parse(GatewayAnswer.ga_spell(t), sess), Gc.known(L, [], Gc.find(L, Gc.names(Gc.specs()), 0n)), Gc.OCommand{Gc.CModel{None{}}}, LA.gcb.known(t, sess, name, [], well, ws, nm, own), Equal.cong(String, Gc.Out, z => Gc.known(z, [], Gc.find(z, Gc.names(Gc.specs()), 0n)), L, "model", cmd))
