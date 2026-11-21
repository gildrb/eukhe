# eukhe: the proof of LAW gateway_commands_diff_usage_long
#
# PROOF: the text routes to the code's command lookup (gcb.known); two words or more get the usage line, whether the first is `all` or not (case by case).

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/gateway_answer.bend as Ga
import ../../bend/slash_suggest.bend as Ss
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_commands.bend as GatewayCommands
import ../gateway_answer/base.bend as LGa
import ./base.bend as LA

def gcdl.go(all: Bool, b: String, more: List<&2, String>) -> {Gc.exact(Gc.diff.one(all, b <> more), 13n) == Gc.OAnswer{String.append("Usage: ", GatewayCommands.gc_at(GatewayCommands.gc_lines(), 13n))} : Gc.Out}:
  match all:
    case True{}:
      {==}
    case False{}:
      {==}

def GatewayCommands.gateway_commands_diff_usage_long(t, sess, name, a, b, more, well, ws, nm, cmd, own):
  +L = String.to_lower(name)
  Equal.trans(Gc.Out, Gc.parse(GatewayAnswer.ga_spell(t), sess), Gc.known(L, a <> (b <> more), Gc.find(L, Gc.names(Gc.specs()), 0n)), Gc.OAnswer{String.append("Usage: ", GatewayCommands.gc_at(GatewayCommands.gc_lines(), 13n))}, LA.gcb.known(t, sess, name, a <> (b <> more), well, ws, nm, own), Equal.trans(Gc.Out, Gc.known(L, a <> (b <> more), Gc.find(L, Gc.names(Gc.specs()), 0n)), Gc.known("diff", a <> (b <> more), Gc.find("diff", Gc.names(Gc.specs()), 0n)), Gc.OAnswer{String.append("Usage: ", GatewayCommands.gc_at(GatewayCommands.gc_lines(), 13n))}, Equal.cong(String, Gc.Out, z => Gc.known(z, a <> (b <> more), Gc.find(z, Gc.names(Gc.specs()), 0n)), L, "diff", cmd), gcdl.go(String.eq(a, "all"), b, more)))
