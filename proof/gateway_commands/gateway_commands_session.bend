# eukhe: the proof of LAW gateway_commands_session
#
# PROOF: the text routes to the code's session test on the lowercased name (gcb.route); the code's test is the laws' (gcb.member), true by ses.

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/gateway_answer.bend as Ga
import ../../bend/slash_suggest.bend as Ss
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_commands.bend as GatewayCommands
import ../gateway_answer/base.bend as LGa
import ./base.bend as LA

def GatewayCommands.gateway_commands_session(t, sess, name, args, well, ws, nm, ses):
  +L = String.to_lower(name)
  +hm = Equal.trans(Bool, Gc.member(L, sess), GatewayCommands.gc_in(L, sess), True{}, LA.gcb.member(L, sess), ses)
  %hm : {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.session(_, L, args) : Gc.Out}
  LA.gcb.route(t, sess, name, args, well, ws, nm)
