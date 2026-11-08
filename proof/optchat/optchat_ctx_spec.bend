# eukhe: the proof of LAW optchat_ctx_spec
#
# PROOF: the bound in bits is worth the spec's bound (oq.bound), and the lines kept by their ends in bits are those kept by their ends in numbers (oq.ctx_go).

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

def OptchatQueries.optchat_ctx_spec(s, n):
  %LQ.oq.bound(n) : {OCtx.ctx.go(OState.St.cview(s), OState.St.info(s), OCtx.ctx.bound(n)) == S.upto(OState.St.cview(s), OState.St.info(s), _) : List<&2, ONode.Node>}
  LQ.oq.ctx_go(OState.St.cview(s), OState.St.info(s), OCtx.ctx.bound(n))
