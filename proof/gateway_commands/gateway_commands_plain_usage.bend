# eukhe: the proof of LAW gateway_commands_plain_usage
#
# PROOF: as gateway_commands_plain; with a word after it the code's table refuses the arguments and answers the usage line, for each k of the seven.

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/gateway_answer.bend as Ga
import ../../bend/slash_suggest.bend as Ss
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_commands.bend as GatewayCommands
import ../gateway_answer/base.bend as LGa
import ./base.bend as LA

def gcpu.at(k: Nat, -L: String, +a: String, +more: List<&2, String>, few: {GatewayCommands.gc_plain_has(k) == True{} : Bool}, cmd: {L == GatewayCommands.gc_at(GatewayCommands.gc_names(), GatewayCommands.gc_plain_at(k)) : String}) -> {Gc.known(L, a <> more, Gc.find(L, Gc.names(Gc.specs()), 0n)) == Gc.OAnswer{String.append("Usage: ", GatewayCommands.gc_at(GatewayCommands.gc_lines(), GatewayCommands.gc_plain_at(k)))} : Gc.Out}:
  match k:
    case 0n:
      Equal.cong(String, Gc.Out, z => Gc.known(z, a <> more, Gc.find(z, Gc.names(Gc.specs()), 0n)), L, GatewayCommands.gc_at(GatewayCommands.gc_names(), GatewayCommands.gc_plain_at(0n)), cmd)
    case 1n:
      Equal.cong(String, Gc.Out, z => Gc.known(z, a <> more, Gc.find(z, Gc.names(Gc.specs()), 0n)), L, GatewayCommands.gc_at(GatewayCommands.gc_names(), GatewayCommands.gc_plain_at(1n)), cmd)
    case 2n:
      Equal.cong(String, Gc.Out, z => Gc.known(z, a <> more, Gc.find(z, Gc.names(Gc.specs()), 0n)), L, GatewayCommands.gc_at(GatewayCommands.gc_names(), GatewayCommands.gc_plain_at(2n)), cmd)
    case 3n:
      Equal.cong(String, Gc.Out, z => Gc.known(z, a <> more, Gc.find(z, Gc.names(Gc.specs()), 0n)), L, GatewayCommands.gc_at(GatewayCommands.gc_names(), GatewayCommands.gc_plain_at(3n)), cmd)
    case 4n:
      Equal.cong(String, Gc.Out, z => Gc.known(z, a <> more, Gc.find(z, Gc.names(Gc.specs()), 0n)), L, GatewayCommands.gc_at(GatewayCommands.gc_names(), GatewayCommands.gc_plain_at(4n)), cmd)
    case 5n:
      Equal.cong(String, Gc.Out, z => Gc.known(z, a <> more, Gc.find(z, Gc.names(Gc.specs()), 0n)), L, GatewayCommands.gc_at(GatewayCommands.gc_names(), GatewayCommands.gc_plain_at(5n)), cmd)
    case 6n:
      Equal.cong(String, Gc.Out, z => Gc.known(z, a <> more, Gc.find(z, Gc.names(Gc.specs()), 0n)), L, GatewayCommands.gc_at(GatewayCommands.gc_names(), GatewayCommands.gc_plain_at(6n)), cmd)
    case 7n+u:
      LGa.gab.absurd({Gc.known(L, a <> more, Gc.find(L, Gc.names(Gc.specs()), 0n)) == Gc.OAnswer{String.append("Usage: ", GatewayCommands.gc_at(GatewayCommands.gc_lines(), GatewayCommands.gc_plain_at(7n+u)))} : Gc.Out}, few)

def GatewayCommands.gateway_commands_plain_usage(t, sess, name, k, a, more, well, ws, nm, few, cmd, own):
  +L = String.to_lower(name)
  Equal.trans(Gc.Out, Gc.parse(GatewayAnswer.ga_spell(t), sess), Gc.known(L, a <> more, Gc.find(L, Gc.names(Gc.specs()), 0n)), Gc.OAnswer{String.append("Usage: ", GatewayCommands.gc_at(GatewayCommands.gc_lines(), GatewayCommands.gc_plain_at(k)))}, LA.gcb.known(t, sess, name, a <> more, well, ws, nm, own), gcpu.at(k, L, a, more, few, cmd))
