# eukhe: the proof of LAW gateway_commands_plain
#
# PROOF: the text routes to the code's command lookup on the lowercased name (gcb.known); that name is the k-th argument-free command's (cmd), which the code's table answers with no argument, for each k of the seven.

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/gateway_answer.bend as Ga
import ../../bend/slash_suggest.bend as Ss
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_commands.bend as GatewayCommands
import ../gateway_answer/base.bend as LGa
import ./base.bend as LA

def gcpl.at(k: Nat, -L: String, few: {GatewayCommands.gc_plain_has(k) == True{} : Bool}, cmd: {L == GatewayCommands.gc_at(GatewayCommands.gc_names(), GatewayCommands.gc_plain_at(k)) : String}) -> {Gc.known(L, [], Gc.find(L, Gc.names(Gc.specs()), 0n)) == Gc.OCommand{GatewayCommands.gc_plain_cmd(k)} : Gc.Out}:
  match k:
    case 0n:
      Equal.cong(String, Gc.Out, z => Gc.known(z, [], Gc.find(z, Gc.names(Gc.specs()), 0n)), L, GatewayCommands.gc_at(GatewayCommands.gc_names(), GatewayCommands.gc_plain_at(0n)), cmd)
    case 1n:
      Equal.cong(String, Gc.Out, z => Gc.known(z, [], Gc.find(z, Gc.names(Gc.specs()), 0n)), L, GatewayCommands.gc_at(GatewayCommands.gc_names(), GatewayCommands.gc_plain_at(1n)), cmd)
    case 2n:
      Equal.cong(String, Gc.Out, z => Gc.known(z, [], Gc.find(z, Gc.names(Gc.specs()), 0n)), L, GatewayCommands.gc_at(GatewayCommands.gc_names(), GatewayCommands.gc_plain_at(2n)), cmd)
    case 3n:
      Equal.cong(String, Gc.Out, z => Gc.known(z, [], Gc.find(z, Gc.names(Gc.specs()), 0n)), L, GatewayCommands.gc_at(GatewayCommands.gc_names(), GatewayCommands.gc_plain_at(3n)), cmd)
    case 4n:
      Equal.cong(String, Gc.Out, z => Gc.known(z, [], Gc.find(z, Gc.names(Gc.specs()), 0n)), L, GatewayCommands.gc_at(GatewayCommands.gc_names(), GatewayCommands.gc_plain_at(4n)), cmd)
    case 5n:
      Equal.cong(String, Gc.Out, z => Gc.known(z, [], Gc.find(z, Gc.names(Gc.specs()), 0n)), L, GatewayCommands.gc_at(GatewayCommands.gc_names(), GatewayCommands.gc_plain_at(5n)), cmd)
    case 6n:
      Equal.cong(String, Gc.Out, z => Gc.known(z, [], Gc.find(z, Gc.names(Gc.specs()), 0n)), L, GatewayCommands.gc_at(GatewayCommands.gc_names(), GatewayCommands.gc_plain_at(6n)), cmd)
    case 7n+u:
      LGa.gab.absurd({Gc.known(L, [], Gc.find(L, Gc.names(Gc.specs()), 0n)) == Gc.OCommand{GatewayCommands.gc_plain_cmd(7n+u)} : Gc.Out}, few)

def GatewayCommands.gateway_commands_plain(t, sess, name, k, well, ws, nm, few, cmd, own):
  +L = String.to_lower(name)
  Equal.trans(Gc.Out, Gc.parse(GatewayAnswer.ga_spell(t), sess), Gc.known(L, [], Gc.find(L, Gc.names(Gc.specs()), 0n)), Gc.OCommand{GatewayCommands.gc_plain_cmd(k)}, LA.gcb.known(t, sess, name, [], well, ws, nm, own), gcpl.at(k, L, few, cmd))
