# eukhe: the proof of LAW optchat_message_counts
# Both arms of a message (a batch or none) keep the T they are given, the
# sizes, the ready merges and the busy calls (mc.go); the message gives
# them T + 1 (LAS.cover.val_inc).

import Base
import ../../bend/optchat/bits.bend as OBits
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/fit.bend as OFit
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/step.bend as OStep
import ../../laws/optchat/queries.bend as OptchatQueries
import ./base/step.bend as LAS

def mc.Kept(r: OState.St & List<&2, ONode.Node>, +t: List<&2, Bool>, +info: OInfo.Info, +ready: List<&2, ONode.Node>, +busy: List<&2, ONode.Node>) -> Type:
  {OState.St.t(Pair.fst(OState.St, List<&2, ONode.Node>, r)) == t : List<&2, Bool>} & ({OState.St.info(Pair.fst(OState.St, List<&2, ONode.Node>, r)) == info : OInfo.Info} & ({OState.St.ready(Pair.fst(OState.St, List<&2, ONode.Node>, r)) == ready : List<&2, ONode.Node>} & {OState.St.busy(Pair.fst(OState.St, List<&2, ONode.Node>, r)) == busy : List<&2, ONode.Node>}))

def mc.batch(r: List<&2, ONode.Node> & List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>, +ready: List<&2, ONode.Node>, +busy: List<&2, ONode.Node>) -> mc.Kept(OStep.msg.batch(r, cfg, t, info, cv, ready, busy), t, info, ready, busy):
  (merged, view) = r
  ({==}, ({==}, ({==}, {==})))

def mc.go(grow: Bool, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, +cv: List<&2, ONode.Node>, +ready: List<&2, ONode.Node>, +busy: List<&2, ONode.Node>) -> mc.Kept(OStep.msg.go(grow, cfg, t, info, view, cv, ready, busy), t, info, ready, busy):
  match grow:
    case False{}:
      ({==}, ({==}, ({==}, {==})))
    case True{}:
      mc.batch(OFit.fit(OFit.Last{}, t, OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), info, view), cfg, t, info, cv, ready, busy)

def mc.t(-x: List<&2, Bool>, +t: List<&2, Bool>, e: {x == OBits.Bits.inc(t) : List<&2, Bool>}) -> {OBits.Bits.val(x) == 1n+OBits.Bits.val(t) : Nat}:
  %Equal.sym(List<&2, Bool>, x, OBits.Bits.inc(t), e) : {OBits.Bits.val(_) == 1n+OBits.Bits.val(t) : Nat}
  Equal.sym(Nat, 1n+OBits.Bits.val(t), OBits.Bits.val(OBits.Bits.inc(t)), LAS.cover.val_inc(t))

def mc.all(+t: List<&2, Bool>, -r: OState.St & List<&2, ONode.Node>, +info: OInfo.Info, +ready: List<&2, ONode.Node>, +busy: List<&2, ONode.Node>, k: mc.Kept(r, OBits.Bits.inc(t), info, ready, busy)) -> ({OBits.Bits.val(OState.St.t(Pair.fst(OState.St, List<&2, ONode.Node>, r))) == 1n+OBits.Bits.val(t) : Nat} & ({OState.St.info(Pair.fst(OState.St, List<&2, ONode.Node>, r)) == info : OInfo.Info} & ({OState.St.ready(Pair.fst(OState.St, List<&2, ONode.Node>, r)) == ready : List<&2, ONode.Node>} & {OState.St.busy(Pair.fst(OState.St, List<&2, ONode.Node>, r)) == busy : List<&2, ONode.Node>}))):
  (et, rest) = k
  (mc.t(OState.St.t(Pair.fst(OState.St, List<&2, ONode.Node>, r)), t, et), rest)

def OptchatQueries.optchat_message_counts(cfg, s):
  +t = OState.St.t(s)
  +info = OState.St.info(s)
  +ready = OState.St.ready(s)
  +busy = OState.St.busy(s)
  mc.all(t, OStep.msg(cfg, s), info, ready, busy, mc.go(OStep.St.batch(cfg, s), cfg, OBits.Bits.inc(t), info, OStep.St.grown(s), List.append(&2, ONode.Node, OState.St.cview(s), [ONode.Node.leaf(t)]), ready, busy))
