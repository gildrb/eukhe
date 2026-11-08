# eukhe: the proof of LAW optchat_free_spec
#
# PROOF: a free sets the busy nodes (oq.busy_set) to the model's delete, which is the spec's (oq.del).

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

def OptchatQueries.optchat_free_spec(cfg, s, n):
  %Equal.sym(OState.St, OStep.busy.set(s, ONode.Nodes.del(OState.St.busy(s), n)), S.with_busy(s, ONode.Nodes.del(OState.St.busy(s), n)), LQ.oq.busy_set(s, ONode.Nodes.del(OState.St.busy(s), n))) : {(_, Nil{}) == (S.with_busy(s, S.busy_del(OState.St.busy(s), n)), Nil{}) : OState.St & List<&2, ONode.Node>}
  %Equal.sym(List<&2, ONode.Node>, ONode.Nodes.del(OState.St.busy(s), n), S.busy_del(OState.St.busy(s), n), LQ.oq.del(OState.St.busy(s), n)) : {(S.with_busy(s, _), Nil{}) == (S.with_busy(s, S.busy_del(OState.St.busy(s), n)), Nil{}) : OState.St & List<&2, ONode.Node>}
  {==}
