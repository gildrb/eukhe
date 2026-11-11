# eukhe: the proof of LAW gateway_commands_use_usage
#
# PROOF: as gateway_commands_use; with no argument or two or more the code answers the usage line (one argument contradicts count).

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/gateway_answer.bend as Ga
import ../../bend/slash_suggest.bend as Ss
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_commands.bend as GatewayCommands
import ../gateway_answer/base.bend as LGa
import ./base.bend as LA

def gcuu.args(args: List<&2, String>, count: {Nat.is_eq(List.length(&2, String, args), 1n) == False{} : Bool}) -> {Gc.known("use", args, Gc.find("use", Gc.names(Gc.specs()), 0n)) == Gc.OAnswer{String.append("Usage: ", GatewayCommands.gc_at(GatewayCommands.gc_lines(), 2n))} : Gc.Out}:
  match args:
    case Nil{}:
      {==}
    case a <> rest:
      match rest:
        case Nil{}:
          LA.gcb.IfT.absurd({Gc.known("use", [a], Gc.find("use", Gc.names(Gc.specs()), 0n)) == Gc.OAnswer{String.append("Usage: ", GatewayCommands.gc_at(GatewayCommands.gc_lines(), 2n))} : Gc.Out}, count)
        case b <> more:
          {==}

def GatewayCommands.gateway_commands_use_usage(t, sess, name, args, well, ws, nm, cmd, own, count):
  +L = String.to_lower(name)
  Equal.trans(Gc.Out, Gc.parse(GatewayAnswer.ga_spell(t), sess), Gc.known(L, args, Gc.find(L, Gc.names(Gc.specs()), 0n)), Gc.OAnswer{String.append("Usage: ", GatewayCommands.gc_at(GatewayCommands.gc_lines(), 2n))}, LA.gcb.known(t, sess, name, args, well, ws, nm, own), Equal.trans(Gc.Out, Gc.known(L, args, Gc.find(L, Gc.names(Gc.specs()), 0n)), Gc.known("use", args, Gc.find("use", Gc.names(Gc.specs()), 0n)), Gc.OAnswer{String.append("Usage: ", GatewayCommands.gc_at(GatewayCommands.gc_lines(), 2n))}, Equal.cong(String, Gc.Out, z => Gc.known(z, args, Gc.find(z, Gc.names(Gc.specs()), 0n)), L, "use", cmd), gcuu.args(args, count)))
