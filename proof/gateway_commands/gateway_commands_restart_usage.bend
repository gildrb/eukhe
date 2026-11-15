# eukhe: the proof of LAW gateway_commands_restart_usage
#
# PROOF: the text routes to the code's command lookup (gcb.known); with a word after it the code's table refuses the arguments and answers the usage line.

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/gateway_answer.bend as Ga
import ../../bend/slash_suggest.bend as Ss
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_commands.bend as GatewayCommands
import ../gateway_answer/base.bend as LGa
import ./base.bend as LA

def GatewayCommands.gateway_commands_restart_usage(t, sess, name, a, more, well, ws, nm, cmd, own):
  +L = String.to_lower(name)
  Equal.trans(Gc.Out, Gc.parse(GatewayAnswer.ga_spell(t), sess), Gc.known(L, a <> more, Gc.find(L, Gc.names(Gc.specs()), 0n)), Gc.OAnswer{"Usage: /restart - Restart the gateway on the installed eukhe version (applies a downloaded update)."}, LA.gcb.known(t, sess, name, a <> more, well, ws, nm, own), Equal.cong(String, Gc.Out, z => Gc.known(z, a <> more, Gc.find(z, Gc.names(Gc.specs()), 0n)), L, "restart", cmd))
