# eukhe: the proof of LAW gateway_commands_diff
#
# PROOF: the text routes to the code's command lookup (gcb.known); no word is since the last prompt, the word `all` since the first prompt (case by case).

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/gateway_answer.bend as Ga
import ../../bend/slash_suggest.bend as Ss
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_commands.bend as GatewayCommands
import ../gateway_answer/base.bend as LGa
import ./base.bend as LA

def gcdf.words(all: Bool) -> {Gc.known("diff", GatewayCommands.gc_diff_words(all), Gc.find("diff", Gc.names(Gc.specs()), 0n)) == Gc.OCommand{Gc.CDiff{all}} : Gc.Out}:
  match all:
    case False{}:
      {==}
    case True{}:
      {==}

def GatewayCommands.gateway_commands_diff(t, sess, name, all, well, ws, nm, cmd, own):
  +L = String.to_lower(name)
  Equal.trans(Gc.Out, Gc.parse(GatewayAnswer.ga_spell(t), sess), Gc.known(L, GatewayCommands.gc_diff_words(all), Gc.find(L, Gc.names(Gc.specs()), 0n)), Gc.OCommand{Gc.CDiff{all}}, LA.gcb.known(t, sess, name, GatewayCommands.gc_diff_words(all), well, ws, nm, own), Equal.trans(Gc.Out, Gc.known(L, GatewayCommands.gc_diff_words(all), Gc.find(L, Gc.names(Gc.specs()), 0n)), Gc.known("diff", GatewayCommands.gc_diff_words(all), Gc.find("diff", Gc.names(Gc.specs()), 0n)), Gc.OCommand{Gc.CDiff{all}}, Equal.cong(String, Gc.Out, z => Gc.known(z, GatewayCommands.gc_diff_words(all), Gc.find(z, Gc.names(Gc.specs()), 0n)), L, "diff", cmd), gcdf.words(all)))
