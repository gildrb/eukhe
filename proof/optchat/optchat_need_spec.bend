# eukhe: the proof of LAW optchat_need_spec
#
# PROOF: the view's lines that start are the spec's within the room (oq.view).

import Base
import ../../bend/optchat/bits.bend as OBits
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/step.bend as OStep
import ../../bend/optchat/queue.bend as OQueue
import ../../bend/optchat/ctx.bend as OCtx
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat/queries.bend as OptchatQueries
import ./base/queries.bend as LQ

def OptchatQueries.optchat_need_spec(cfg, s):
  LQ.oq.view(OState.St.view(s), Nat.sub(OState.Cfg.jobs(cfg), List.length(&2, ONode.Node, OState.St.busy(s))), OState.St.info(s), OState.St.busy(s), OState.Cfg.jobs(cfg), 0n)
