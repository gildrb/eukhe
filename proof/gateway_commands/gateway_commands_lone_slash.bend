# eukhe: the proof of LAW gateway_commands_lone_slash
#
# PROOF: the text routes to the code's lookup of the empty name (gcb.known), found nowhere: the code answers its help text, the laws' (gcb.help).

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/gateway_answer.bend as Ga
import ../../bend/slash_suggest.bend as Ss
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_commands.bend as GatewayCommands
import ../gateway_answer/base.bend as LGa
import ./base.bend as LA

def GatewayCommands.gateway_commands_lone_slash(t, sess, well, ws, own):
  Equal.trans(Gc.Out, Gc.parse(GatewayAnswer.ga_spell(t), sess), Gc.known("", [], Gc.find("", Gc.names(Gc.specs()), 0n)), Gc.OAnswer{GatewayCommands.gc_help()}, LA.gcb.known(t, sess, SNil{}, [], well, ws, {==}, own), {==})
