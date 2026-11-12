# eukhe: the proof of LAW gateway_commands_reasoning
#
# PROOF: the text routes to the code's command lookup (gcb.known); none or one argument is kept (case by case).

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/gateway_answer.bend as Ga
import ../../bend/slash_suggest.bend as Ss
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_commands.bend as GatewayCommands
import ../gateway_answer/base.bend as LGa
import ./base.bend as LA

def gcr.opt(m: Maybe<&2, String>) -> {Gc.known("reasoning", GatewayCommands.gc_opt(m), Gc.find("reasoning", Gc.names(Gc.specs()), 0n)) == Gc.OCommand{Gc.CReasoning{m}} : Gc.Out}:
  match m:
    case None{}:
      {==}
    case Some{a}:
      {==}

def GatewayCommands.gateway_commands_reasoning(t, sess, name, m, well, ws, nm, cmd, own):
  +L = String.to_lower(name)
  Equal.trans(Gc.Out, Gc.parse(GatewayAnswer.ga_spell(t), sess), Gc.known(L, GatewayCommands.gc_opt(m), Gc.find(L, Gc.names(Gc.specs()), 0n)), Gc.OCommand{Gc.CReasoning{m}}, LA.gcb.known(t, sess, name, GatewayCommands.gc_opt(m), well, ws, nm, own), Equal.trans(Gc.Out, Gc.known(L, GatewayCommands.gc_opt(m), Gc.find(L, Gc.names(Gc.specs()), 0n)), Gc.known("reasoning", GatewayCommands.gc_opt(m), Gc.find("reasoning", Gc.names(Gc.specs()), 0n)), Gc.OCommand{Gc.CReasoning{m}}, Equal.cong(String, Gc.Out, z => Gc.known(z, GatewayCommands.gc_opt(m), Gc.find(z, Gc.names(Gc.specs()), 0n)), L, "reasoning", cmd), gcr.opt(m)))
