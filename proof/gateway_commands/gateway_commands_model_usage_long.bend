# eukhe: the proof of LAW gateway_commands_model_usage_long
#
# PROOF: the text routes to the code's command lookup (gcb.known); three arguments or more get the usage line whether or not the first is `all` (case by case).

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/gateway_answer.bend as Ga
import ../../bend/slash_suggest.bend as Ss
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_commands.bend as GatewayCommands
import ../gateway_answer/base.bend as LGa
import ./base.bend as LA

def gcml.long(e: Bool, +a: String, +b: String, +c: String, +more: List<&2, String>) -> {Gc.exact(Gc.model.first(e, a, b <> (c <> more)), 8n) == Gc.OAnswer{String.append("Usage: ", GatewayCommands.gc_at(GatewayCommands.gc_lines(), 8n))} : Gc.Out}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

def GatewayCommands.gateway_commands_model_usage_long(t, sess, name, a, b, c, more, well, ws, nm, cmd, own):
  +L = String.to_lower(name)
  Equal.trans(Gc.Out, Gc.parse(GatewayAnswer.ga_spell(t), sess), Gc.known(L, a <> (b <> (c <> more)), Gc.find(L, Gc.names(Gc.specs()), 0n)), Gc.OAnswer{String.append("Usage: ", GatewayCommands.gc_at(GatewayCommands.gc_lines(), 8n))}, LA.gcb.known(t, sess, name, a <> (b <> (c <> more)), well, ws, nm, own), Equal.trans(Gc.Out, Gc.known(L, a <> (b <> (c <> more)), Gc.find(L, Gc.names(Gc.specs()), 0n)), Gc.known("model", a <> (b <> (c <> more)), Gc.find("model", Gc.names(Gc.specs()), 0n)), Gc.OAnswer{String.append("Usage: ", GatewayCommands.gc_at(GatewayCommands.gc_lines(), 8n))}, Equal.cong(String, Gc.Out, z => Gc.known(z, a <> (b <> (c <> more)), Gc.find(z, Gc.names(Gc.specs()), 0n)), L, "model", cmd), gcml.long(String.eq(a, "all"), a, b, c, more)))
