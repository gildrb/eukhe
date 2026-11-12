# eukhe: the proof of LAW optchat_message_batch
# With a batch (the model's test is the spec's: LB.ob.batch), a message
# fits the grown view to floor: a chain (LAC.ch.fit); shrink is the
# model's over test, the spec's size test (LB.ob.over); after merges the
# compaction view is the new view fitted to cfloor (LAC.ch.fitted), after
# none it takes its sawtooth step (LAC.ch.saw).

import Base
import ../../bend/optchat/bits.bend as OBits
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/fit.bend as OFit
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/step.bend as OStep
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat/queries.bend as OptchatQueries
import ./base/step.bend as LA
import ./base/batch.bend as LB
import ./base/chain.bend as LAC

# what a batch's result r holds, from the view and compaction view it had
def mb.Q(r: OState.St & List<&2, ONode.Node>, +cfg: OState.Cfg, +info: OInfo.Info, +view: List<&2, ONode.Node>, +cv: List<&2, ONode.Node>) -> Type:
  S.Chain(OFit.Last{}, OState.St.t(Pair.fst(OState.St, List<&2, ONode.Node>, r)), info, OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), view, Pair.snd(OState.St, List<&2, ONode.Node>, r), OState.St.view(Pair.fst(OState.St, List<&2, ONode.Node>, r))) & ({OState.St.shrink(Pair.fst(OState.St, List<&2, ONode.Node>, r)) == Nat.is_gt(S.vsize(OState.Cfg.ph(cfg), info, OState.St.view(Pair.fst(OState.St, List<&2, ONode.Node>, r))), OState.Cfg.floor(cfg)) : Bool} & S.Restart(Pair.snd(OState.St, List<&2, ONode.Node>, r), cfg, OState.St.t(Pair.fst(OState.St, List<&2, ONode.Node>, r)), info, OState.St.view(Pair.fst(OState.St, List<&2, ONode.Node>, r)), cv, OState.St.cview(Pair.fst(OState.St, List<&2, ONode.Node>, r))))

def mb.restart(merged: List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, +cv: List<&2, ONode.Node>) -> S.Restart(merged, cfg, t, info, view, cv, OStep.msg.cview(merged, cfg, t, info, view, cv)):
  match merged:
    case Nil{}:
      LAC.ch.saw(cfg, t, info, cv)
    case h <> rest:
      LAC.ch.fitted(OFit.Last{}, t, OState.Cfg.cfloor(cfg), OState.Cfg.ph(cfg), info, view)

def mb.batch(r: List<&2, ONode.Node> & List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, +cv: List<&2, ONode.Node>, +ready: List<&2, ONode.Node>, +busy: List<&2, ONode.Node>,
  ch: S.Chain(OFit.Last{}, t, info, OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), view, Pair.fst(List<&2, ONode.Node>, List<&2, ONode.Node>, r), Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, r)))
  -> mb.Q(OStep.msg.batch(r, cfg, t, info, cv, ready, busy), cfg, info, view, cv):
  (merged, w) = r
  +mg = merged
  +nv = w
  (ch, (LB.ob.over(OState.Cfg.ph(cfg), info, nv, OState.Cfg.floor(cfg)), mb.restart(mg, cfg, t, info, nv, cv)))

def mb.go(grow: Bool, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, +cv: List<&2, ONode.Node>, +ready: List<&2, ONode.Node>, +busy: List<&2, ONode.Node>, eg: {grow == True{} : Bool})
  -> mb.Q(OStep.msg.go(grow, cfg, t, info, view, cv, ready, busy), cfg, info, view, cv):
  match grow:
    case False{}:
      LA.cover.absurd(mb.Q(OStep.msg.go(False{}, cfg, t, info, view, cv, ready, busy), cfg, info, view, cv), eg)
    case True{}:
      mb.batch(OFit.fit(OFit.Last{}, t, OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), info, view), cfg, t, info, view, cv, ready, busy, LAC.ch.fit(OFit.Last{}, t, OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), info, view))

def OptchatQueries.optchat_message_batch(cfg, s, runs):
  mb.go(OStep.St.batch(cfg, s), cfg, OBits.Bits.inc(OState.St.t(s)), OState.St.info(s), OStep.St.grown(s), List.append(&2, ONode.Node, OState.St.cview(s), [ONode.Node.leaf(OState.St.t(s))]), OState.St.ready(s), OState.St.busy(s), Equal.trans(Bool, OStep.St.batch(cfg, s), S.batch(cfg, s), True{}, LB.ob.batch(cfg, s), runs))
