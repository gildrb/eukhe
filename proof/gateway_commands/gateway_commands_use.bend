# eukhe: the proof of LAW gateway_commands_use
#
# PROOF: the text routes to the code's command lookup (gcb.known); the name is `use` (cmd), whose one argument the code keeps.

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/gateway_answer.bend as Ga
import ../../bend/slash_suggest.bend as Ss
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_commands.bend as GatewayCommands
import ../gateway_answer/base.bend as LGa
import ./base.bend as LA

def GatewayCommands.gateway_commands_use(t, sess, name, a, well, ws, nm, cmd, own):
  +L = String.to_lower(name)
  Equal.trans(Gc.Out, Gc.parse(GatewayAnswer.ga_spell(t), sess), Gc.known(L, [a], Gc.find(L, Gc.names(Gc.specs()), 0n)), Gc.OCommand{Gc.CUse{a}}, LA.gcb.known(t, sess, name, [a], well, ws, nm, own), Equal.cong(String, Gc.Out, z => Gc.known(z, [a], Gc.find(z, Gc.names(Gc.specs()), 0n)), L, "use", cmd))
