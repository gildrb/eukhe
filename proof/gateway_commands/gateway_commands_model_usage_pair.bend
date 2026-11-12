# eukhe: the proof of LAW gateway_commands_model_usage_pair
#
# PROOF: the text routes to the code's command lookup (gcb.known); two arguments not opening with `all` (other) get the usage line.

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/gateway_answer.bend as Ga
import ../../bend/slash_suggest.bend as Ss
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_commands.bend as GatewayCommands
import ../gateway_answer/base.bend as LGa
import ./base.bend as LA

def gcmp.two(+a: String, +b: String, other: {String.eq(a, "all") == False{} : Bool}) -> {Gc.known("model", [a, b], Gc.find("model", Gc.names(Gc.specs()), 0n)) == Gc.OAnswer{String.append("Usage: ", GatewayCommands.gc_at(GatewayCommands.gc_lines(), 8n))} : Gc.Out}:
  %Equal.sym(Bool, String.eq(a, "all"), False{}, other) : {Gc.exact(Gc.model.first(_, a, [b]), 8n) == Gc.OAnswer{String.append("Usage: ", GatewayCommands.gc_at(GatewayCommands.gc_lines(), 8n))} : Gc.Out}
  {==}

def GatewayCommands.gateway_commands_model_usage_pair(t, sess, name, a, b, well, ws, nm, cmd, own, other):
  +L = String.to_lower(name)
  Equal.trans(Gc.Out, Gc.parse(GatewayAnswer.ga_spell(t), sess), Gc.known(L, [a, b], Gc.find(L, Gc.names(Gc.specs()), 0n)), Gc.OAnswer{String.append("Usage: ", GatewayCommands.gc_at(GatewayCommands.gc_lines(), 8n))}, LA.gcb.known(t, sess, name, [a, b], well, ws, nm, own), Equal.trans(Gc.Out, Gc.known(L, [a, b], Gc.find(L, Gc.names(Gc.specs()), 0n)), Gc.known("model", [a, b], Gc.find("model", Gc.names(Gc.specs()), 0n)), Gc.OAnswer{String.append("Usage: ", GatewayCommands.gc_at(GatewayCommands.gc_lines(), 8n))}, Equal.cong(String, Gc.Out, z => Gc.known(z, [a, b], Gc.find(z, Gc.names(Gc.specs()), 0n)), L, "model", cmd), gcmp.two(a, b, other)))
