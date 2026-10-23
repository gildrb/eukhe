# optchat: the shipped step: step with the fast batch

import Base
import ./bits.bend as OBits
import ./node.bend as ONode
import ./info.bend as OInfo
import ./fit.bend as OFit
import ./state.bend as OState
import ./step.bend as OStep
import ./batch.bend as OBatch

# The shipped step
# ----------------
# step with the fast batch: on a state whose two views tile the messages it
# is step itself (law stepx_is_step); the message's grown view is built
# once.

def fitcx.if(over: Bool, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match over:
    case False{}:
      cv
    case True{}:
      OBatch.fitx.view(t, OState.Cfg.cfloor(cfg), OState.Cfg.ph(cfg), info, cv)

def fitcx(+cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  fitcx.if(Nat.is_gt(OFit.view_size(OState.Cfg.ph(cfg), info, cv), OState.Cfg.cceil(cfg)), cfg, t, info, cv)

def msgx.cview(merged: List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, +cv: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match merged:
    case Nil{}:
      fitcx(cfg, t, info, cv)
    case h <> rest:
      OBatch.fitx.view(t, OState.Cfg.cfloor(cfg), OState.Cfg.ph(cfg), info, view)

def msgx.after(+merged: List<&2, ONode.Node>, +view: List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>, ready: List<&2, ONode.Node>, busy: List<&2, ONode.Node>) -> OState.St & List<&2, ONode.Node>:
  (OState.St{t, info, view, Nat.is_gt(OFit.view_size(OState.Cfg.ph(cfg), info, view), OState.Cfg.floor(cfg)), msgx.cview(merged, cfg, t, info, view, cv), ready, busy}, merged)

def msgx.batch(r: List<&2, ONode.Node> & List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>, ready: List<&2, ONode.Node>, busy: List<&2, ONode.Node>) -> OState.St & List<&2, ONode.Node>:
  (merged, view) = r
  msgx.after(merged, view, cfg, t, info, cv, ready, busy)

def msgx.go(grow: Bool, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, +cv: List<&2, ONode.Node>, ready: List<&2, ONode.Node>, busy: List<&2, ONode.Node>) -> OState.St & List<&2, ONode.Node>:
  match grow:
    case False{}:
      (OState.St{t, info, view, False{}, fitcx(cfg, t, info, cv), ready, busy}, Nil{})
    case True{}:
      msgx.batch(OBatch.fitx(t, OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), info, view), cfg, t, info, cv, ready, busy)

def msgx(+cfg: OState.Cfg, s: OState.St) -> OState.St & List<&2, ONode.Node>:
  match s:
    case OState.St{+t, +info, view, shrink, cview, ready, busy}:
      +leaf = ONode.Node.leaf(t)
      +g = List.append(&2, ONode.Node, view, [leaf])
      msgx.go(Bool.or(shrink, Nat.is_gt(OFit.view_size(OState.Cfg.ph(cfg), info, g), OState.Cfg.ceil(cfg))), cfg, OBits.Bits.inc(t), info, g, List.append(&2, ONode.Node, cview, [leaf]), ready, busy)

def buildx.go(+cfg: OState.Cfg, +n: ONode.Node, +info: OInfo.Info, s: OState.St) -> OState.St:
  match s:
    case OState.St{+t, i0, view, shrink, cview, ready, busy}:
      OState.St{t, info, view, shrink, fitcx(cfg, t, info, cview), OStep.ready.note(info, n, ONode.Nodes.del(ready, n)), ONode.Nodes.del(busy, n)}

def buildx(+cfg: OState.Cfg, +s: OState.St, +n: ONode.Node, +size: Nat) -> OState.St:
  buildx.go(cfg, n, OInfo.Info.set(OState.St.info(s), n, size), s)

def stepx(+cfg: OState.Cfg, +s: OState.St, e: OState.Ev) -> OState.St & List<&2, ONode.Node>:
  match e:
    case OState.Msg{}:
      msgx(cfg, s)
    case OState.Build{n, size}:
      (buildx(cfg, s, n, size), Nil{})
    case OState.Start{n}:
      (OStep.busy.set(s, ONode.Nodes.add(OState.St.busy(s), n)), Nil{})
    case OState.Free{n}:
      (OStep.busy.set(s, ONode.Nodes.del(OState.St.busy(s), n)), Nil{})
