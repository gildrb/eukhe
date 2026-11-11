# eukhe: the proof of LAW gateway_answer_aborted
#
# PROOF: an abort is a stop, whatever the blocks and the error.

import Base
import ../../bend/gateway_answer.bend as Ga
import ../../laws/gateway_answer.bend as GatewayAnswer
import ./base.bend as LA

def GatewayAnswer.gateway_answer_aborted(ts, e):
  {==}
