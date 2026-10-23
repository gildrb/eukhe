# optchat: the reference step: compaction sawtooth, a message's batch, a built node, events, run

import Base
import ./bits.bend as OBits
import ./node.bend as ONode
import ./info.bend as OInfo
import ./fit.bend as OFit
import ./state.bend as OState

# The compaction view: past cceil, it merges down to cfloor
def fitc.if(over: Bool, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match over:
    case False{}:
      cv
    case True{}:
      OFit.fit.view(OFit.Last{}, t, OState.Cfg.cfloor(cfg), OState.Cfg.ph(cfg), info, cv)

def fitc(+cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  fitc.if(Nat.is_gt(OFit.view_size(OState.Cfg.ph(cfg), info, cv), OState.Cfg.cceil(cfg)), cfg, t, info, cv)

# A message
# ---------
# Its line is appended to both views. Once the view passes ceil, a batch
# merges it down to floor; while unbuilt parents keep it above floor, each
# new message merges what it can. When the view merges, the compaction
# view starts again from it, merged down to cfloor; else it keeps its own
# sawtooth.

def msg.cview(merged: List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, +cv: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match merged:
    case Nil{}:
      fitc(cfg, t, info, cv)
    case h <> rest:
      OFit.fit.view(OFit.Last{}, t, OState.Cfg.cfloor(cfg), OState.Cfg.ph(cfg), info, view)

def msg.after(+merged: List<&2, ONode.Node>, +view: List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>, ready: List<&2, ONode.Node>, busy: List<&2, ONode.Node>) -> OState.St & List<&2, ONode.Node>:
  (OState.St{t, info, view, Nat.is_gt(OFit.view_size(OState.Cfg.ph(cfg), info, view), OState.Cfg.floor(cfg)), msg.cview(merged, cfg, t, info, view, cv), ready, busy}, merged)

def msg.batch(r: List<&2, ONode.Node> & List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>, ready: List<&2, ONode.Node>, busy: List<&2, ONode.Node>) -> OState.St & List<&2, ONode.Node>:
  (merged, view) = r
  msg.after(merged, view, cfg, t, info, cv, ready, busy)

def msg.go(grow: Bool, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, +cv: List<&2, ONode.Node>, ready: List<&2, ONode.Node>, busy: List<&2, ONode.Node>) -> OState.St & List<&2, ONode.Node>:
  match grow:
    case False{}:
      (OState.St{t, info, view, False{}, fitc(cfg, t, info, cv), ready, busy}, Nil{})
    case True{}:
      msg.batch(OFit.fit(OFit.Last{}, t, OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), info, view), cfg, t, info, cv, ready, busy)

# the view with message t's line
def St.grown(+s: OState.St) -> List<&2, ONode.Node>:
  List.append(&2, ONode.Node, OState.St.view(s), [ONode.Node.leaf(OState.St.t(s))])

# a batch runs (or goes on) at this message
def St.batch(+cfg: OState.Cfg, +s: OState.St) -> Bool:
  Bool.or(OState.St.shrink(s), Nat.is_gt(OFit.view_size(OState.Cfg.ph(cfg), OState.St.info(s), St.grown(s)), OState.Cfg.ceil(cfg)))

# message T arrives: the state after it, and the batch it set off (the
# merged parents, in order; empty when none)
def msg(+cfg: OState.Cfg, +s: OState.St) -> OState.St & List<&2, ONode.Node>:
  msg.go(St.batch(cfg, s), cfg, OBits.Bits.inc(OState.St.t(s)), OState.St.info(s), St.grown(s), List.append(&2, ONode.Node, OState.St.cview(s), [ONode.Node.leaf(OState.St.t(s))]), OState.St.ready(s), OState.St.busy(s))

# A built node
# ------------
# It is logged; its parent becomes ready once its sibling is built too
# (a queue, never a scan of the tree: gist §4); the compaction view keeps
# its sawtooth. The view never merges here: only a message merges it.

def ready.if(go: Bool, +p: ONode.Node, rs: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match go:
    case False{}:
      rs
    case True{}:
      ONode.Nodes.ins(rs, p)

def ready.note(+info: OInfo.Info, +n: ONode.Node, rs: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  ready.if(Bool.and(OInfo.Info.built(info, ONode.Node.sibling(n)), Bool.not(OInfo.Info.built(info, ONode.Node.parent(n)))), ONode.Node.parent(n), rs)

def build.go(+cfg: OState.Cfg, +n: ONode.Node, +info: OInfo.Info, s: OState.St) -> OState.St:
  match s:
    case OState.St{+t, i0, view, shrink, cview, ready, busy}:
      OState.St{t, info, view, shrink, fitc(cfg, t, info, cview), ready.note(info, n, ONode.Nodes.del(ready, n)), ONode.Nodes.del(busy, n)}

def build(+cfg: OState.Cfg, +s: OState.St, +n: ONode.Node, +size: Nat) -> OState.St:
  build.go(cfg, n, OInfo.Info.set(OState.St.info(s), n, size), s)

def busy.set(s: OState.St, bs: List<&2, ONode.Node>) -> OState.St:
  match s:
    case OState.St{t, info, view, shrink, cview, ready, busy}:
      OState.St{t, info, view, shrink, cview, ready, bs}

# one event: the state after it, and the batch it set off
def step(+cfg: OState.Cfg, +s: OState.St, e: OState.Ev) -> OState.St & List<&2, ONode.Node>:
  match e:
    case OState.Msg{}:
      msg(cfg, s)
    case OState.Build{n, size}:
      (build(cfg, s, n, size), Nil{})
    case OState.Start{n}:
      (busy.set(s, ONode.Nodes.add(OState.St.busy(s), n)), Nil{})
    case OState.Free{n}:
      (busy.set(s, ONode.Nodes.del(OState.St.busy(s), n)), Nil{})

def run.go(evs: List<&2, OState.Ev>, +cfg: OState.Cfg, +s: OState.St) -> OState.St:
  match evs:
    case Nil{}:
      s
    case e <> rest:
      run.go(rest, cfg, Pair.fst(OState.St, List<&2, ONode.Node>, step(cfg, s, e)))

# the chat after evs, from an empty one
def run(+cfg: OState.Cfg, evs: List<&2, OState.Ev>) -> OState.St:
  run.go(evs, cfg, OState.St.empty())
