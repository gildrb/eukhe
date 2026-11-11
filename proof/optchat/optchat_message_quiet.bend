# eukhe: the proof of LAW optchat_message_quiet
# With no batch (the model's batch test is the spec's: LB.ob.batch), a
# message takes msg.go's quiet arm: no merge, the grown view, shrink off,
# and the compaction view's sawtooth step (LAC.ch.saw).

import Base
import ../../bend/optchat/bits.bend as OBits
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/step.bend as OStep
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat/queries.bend as OptchatQueries
import ./base/step.bend as LA
import ./base/batch.bend as LB
import ./base/chain.bend as LAC

# what a quiet message's result r holds, from the view and compaction view it had
def mq.Q(r: OState.St & List<&2, ONode.Node>, +cfg: OState.Cfg, +info: OInfo.Info, +view: List<&2, ONode.Node>, +cv: List<&2, ONode.Node>) -> Type:
  {Pair.snd(OState.St, List<&2, ONode.Node>, r) == Nil{} : List<&2, ONode.Node>} & ({OState.St.view(Pair.fst(OState.St, List<&2, ONode.Node>, r)) == view : List<&2, ONode.Node>} & ({OState.St.shrink(Pair.fst(OState.St, List<&2, ONode.Node>, r)) == False{} : Bool} & S.Saw(cfg, OState.St.t(Pair.fst(OState.St, List<&2, ONode.Node>, r)), info, cv, OState.St.cview(Pair.fst(OState.St, List<&2, ONode.Node>, r)))))

def mq.go(grow: Bool, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, +cv: List<&2, ONode.Node>, +ready: List<&2, ONode.Node>, +busy: List<&2, ONode.Node>, eg: {grow == False{} : Bool})
  -> mq.Q(OStep.msg.go(grow, cfg, t, info, view, cv, ready, busy), cfg, info, view, cv):
  match grow:
    case True{}:
      LA.cover.absurd(mq.Q(OStep.msg.go(True{}, cfg, t, info, view, cv, ready, busy), cfg, info, view, cv), Equal.sym(Bool, True{}, False{}, eg))
    case False{}:
      ({==}, ({==}, ({==}, LAC.ch.saw(cfg, t, info, cv))))

def OptchatQueries.optchat_message_quiet(cfg, s, quiet):
  mq.go(OStep.St.batch(cfg, s), cfg, OBits.Bits.inc(OState.St.t(s)), OState.St.info(s), OStep.St.grown(s), List.append(&2, ONode.Node, OState.St.cview(s), [ONode.Node.leaf(OState.St.t(s))]), OState.St.ready(s), OState.St.busy(s), Equal.trans(Bool, OStep.St.batch(cfg, s), S.batch(cfg, s), False{}, LB.ob.batch(cfg, s), quiet))
