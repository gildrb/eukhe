# eukhe: the proof of LAW gateway_commands_listing
#
# PROOF: the text routes to the code's answer to an unknown name (gcb.unknown); the code's starting commands are the laws' (gcb.starting), l and ls by pre, joined as the laws' listing (gcb.listing).

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/gateway_answer.bend as Ga
import ../../bend/slash_suggest.bend as Ss
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_commands.bend as GatewayCommands
import ../gateway_answer/base.bend as LGa
import ./base.bend as LA

def GatewayCommands.gateway_commands_listing(t, sess, c, n, l, ls, well, ws, nm, own, none, pre):
  +L = String.to_lower(SCon{c, n})
  +e1 = LA.gcb.unknown(t, sess, SCon{c, n}, [], well, ws, nm, own, none)
  +e2 = Equal.trans(List<&2, String>, Gc.starting(L, Gc.specs()), GatewayCommands.gc_starting(L, Gc.names(Gc.specs()), Gc.lines(Gc.specs(), [])), l <> ls, LA.gcb.starting(L, Gc.specs()), pre)
  %LA.gcb.listing(ls) : {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OAnswer{String.append(l, _)} : Gc.Out}
  %e2 : {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OAnswer{Gc.suggest.near(L, _)} : Gc.Out}
  e1
