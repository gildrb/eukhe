# eukhe: the proof of LAW optchat_msg_spec
#
# PROOF: the batch test, T + 1, the fits and the compaction sawtooth are the spec's (ob.msg).

import Base
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/fit.bend as OFit
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/step.bend as OStep
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat/queries.bend as OptchatQueries
import ./base/batch.bend as LB

def OptchatQueries.optchat_msg_spec(cfg, s):
  LB.ob.msg(cfg, s)
