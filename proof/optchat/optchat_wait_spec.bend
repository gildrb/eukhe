# eukhe: the proof of LAW optchat_wait_spec
#
# PROOF: a wait changes only the busy nodes, to those the model's filter keeps, which are the spec's (oq.need).

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

def OptchatQueries.optchat_wait_spec(s):
  match s:
    case OState.St{t, +info, +view, shrink, cview, ready, busy}:
      Equal.cong(List<&2, ONode.Node>, OState.St, x => OState.St{t, info, view, shrink, cview, ready, x}, OQueue.busy.need(info, view, busy), S.needed(info, view, busy), LQ.oq.need(info, view, busy))
