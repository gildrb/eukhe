# eukhe: the proof of LAW gateway_commands_model_switch
#
# PROOF: the text routes to the code's command lookup (gcb.known); a one argument other than `all` (other) is a switch.

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/gateway_answer.bend as Ga
import ../../bend/slash_suggest.bend as Ss
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_commands.bend as GatewayCommands
import ../gateway_answer/base.bend as LGa
import ./base.bend as LA

def gcms.one(+a: String, other: {String.eq(a, "all") == False{} : Bool}) -> {Gc.known("model", [a], Gc.find("model", Gc.names(Gc.specs()), 0n)) == Gc.OCommand{Gc.CModel{Some{a}}} : Gc.Out}:
  %Equal.sym(Bool, String.eq(a, "all"), False{}, other) : {Gc.exact(Gc.model.first(_, a, []), 8n) == Gc.OCommand{Gc.CModel{Some{a}}} : Gc.Out}
  {==}

def GatewayCommands.gateway_commands_model_switch(t, sess, name, a, well, ws, nm, cmd, own, other):
  +L = String.to_lower(name)
  Equal.trans(Gc.Out, Gc.parse(GatewayAnswer.ga_spell(t), sess), Gc.known(L, [a], Gc.find(L, Gc.names(Gc.specs()), 0n)), Gc.OCommand{Gc.CModel{Some{a}}}, LA.gcb.known(t, sess, name, [a], well, ws, nm, own), Equal.trans(Gc.Out, Gc.known(L, [a], Gc.find(L, Gc.names(Gc.specs()), 0n)), Gc.known("model", [a], Gc.find("model", Gc.names(Gc.specs()), 0n)), Gc.OCommand{Gc.CModel{Some{a}}}, Equal.cong(String, Gc.Out, z => Gc.known(z, [a], Gc.find(z, Gc.names(Gc.specs()), 0n)), L, "model", cmd), gcms.one(a, other)))
