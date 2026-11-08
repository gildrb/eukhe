# eukhe: the proof of LAW optchat_batch_spec
#
# PROOF: the shipped over-budget test is the spec's size above ceil (ob.batch).

import Base
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/fit.bend as OFit
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/step.bend as OStep
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat/queries.bend as OptchatQueries
import ./base/batch.bend as LB

def OptchatQueries.optchat_batch_spec(cfg, s):
  LB.ob.batch(cfg, s)
