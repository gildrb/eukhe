# eukhe: the proof of LAW gateway_commands_unknown_words
#
# PROOF: the text routes to the code's answer to an unknown name (gcb.unknown), which with words after it is a prompt.

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/gateway_answer.bend as Ga
import ../../bend/slash_suggest.bend as Ss
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_commands.bend as GatewayCommands
import ../gateway_answer/base.bend as LGa
import ./base.bend as LA

def GatewayCommands.gateway_commands_unknown_words(t, sess, name, a, more, well, ws, nm, own, none):
  LA.gcb.unknown(t, sess, name, a <> more, well, ws, nm, own, none)
