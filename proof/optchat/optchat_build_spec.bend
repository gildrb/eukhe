# eukhe: the proof of LAW optchat_build_spec
#
# PROOF: the compaction sawtooth, the ready note (sibling, parent, sorted insert) and the deletes are the spec's (ob.build).

import Base
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/fit.bend as OFit
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/step.bend as OStep
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat/queries.bend as OptchatQueries
import ./base/batch.bend as LB

def OptchatQueries.optchat_build_spec(cfg, s, n, size):
  Equal.cong(OState.St, OState.St & List<&2, ONode.Node>, x => (x, Nil{}), OStep.build(cfg, s, n, size), S.build(cfg, s, n, size), LB.ob.build(cfg, s, n, size))
