# eukhe: the proof of LAW gateway_commands_diff_usage_word
#
# PROOF: the text routes to the code's command lookup (gcb.known); one word other than `all` (other) gets the usage line.

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/gateway_answer.bend as Ga
import ../../bend/slash_suggest.bend as Ss
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_commands.bend as GatewayCommands
import ../gateway_answer/base.bend as LGa
import ./base.bend as LA

def gcdw.one(+a: String, other: {String.eq(a, "all") == False{} : Bool}) -> {Gc.known("diff", [a], Gc.find("diff", Gc.names(Gc.specs()), 0n)) == Gc.OAnswer{String.append("Usage: ", GatewayCommands.gc_at(GatewayCommands.gc_lines(), 13n))} : Gc.Out}:
  %Equal.sym(Bool, String.eq(a, "all"), False{}, other) : {Gc.exact(Gc.diff.one(_, []), 13n) == Gc.OAnswer{String.append("Usage: ", GatewayCommands.gc_at(GatewayCommands.gc_lines(), 13n))} : Gc.Out}
  {==}

def GatewayCommands.gateway_commands_diff_usage_word(t, sess, name, a, well, ws, nm, cmd, own, other):
  +L = String.to_lower(name)
  Equal.trans(Gc.Out, Gc.parse(GatewayAnswer.ga_spell(t), sess), Gc.known(L, [a], Gc.find(L, Gc.names(Gc.specs()), 0n)), Gc.OAnswer{String.append("Usage: ", GatewayCommands.gc_at(GatewayCommands.gc_lines(), 13n))}, LA.gcb.known(t, sess, name, [a], well, ws, nm, own), Equal.trans(Gc.Out, Gc.known(L, [a], Gc.find(L, Gc.names(Gc.specs()), 0n)), Gc.known("diff", [a], Gc.find("diff", Gc.names(Gc.specs()), 0n)), Gc.OAnswer{String.append("Usage: ", GatewayCommands.gc_at(GatewayCommands.gc_lines(), 13n))}, Equal.cong(String, Gc.Out, z => Gc.known(z, [a], Gc.find(z, Gc.names(Gc.specs()), 0n)), L, "diff", cmd), gcdw.one(a, other)))
