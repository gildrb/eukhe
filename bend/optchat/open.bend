# optchat: the open of a loaded chat: the built nodes, the ready merges,
# the missed batch, the compaction view

import Base
import ./node.bend as ONode
import ./info.bend as OInfo
import ./fit.bend as OFit
import ./state.bend as OState
import ./step.bend as OStep

# A loaded chat
# -------------
# What the log holds: T (in binary), every built node with its size, the
# view folded from the merge batches, whether the last batch left it over
# its floor (shrink), and whether that batch is missing: the owner died
# between a message and its batch line (missed).

type Built is Data:
  Built{n: ONode.Node, size: Nat}

# every built node, with its size (a later copy of a node wins)
def info.of(bs: List<&2, Built>, info: OInfo.Info) -> OInfo.Info:
  match bs:
    case Nil{}:
      info
    case Built{n, z} <> rest:
      info.of(rest, OInfo.Info.set(info, n, z))

# the ready merges: each parent of a built pair that is not built itself,
# once, by level then index (as a built node notes it: OStep.ready.note)
def ready.of(bs: List<&2, Built>, +info: OInfo.Info, rs: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match bs:
    case Nil{}:
      rs
    case Built{n, z} <> rest:
      ready.of(rest, info, OStep.ready.note(info, n, rs))

# the opened chat from the view after the missed batch (if any) and
# whether it is still shrinking: the compaction view is that view merged
# down to its floor; no call runs
def open.at(+cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, shrink: Bool, ready: List<&2, ONode.Node>) -> OState.St:
  OState.St{t, info, view, shrink, OFit.fit.view(OFit.Last{}, t, OState.Cfg.cfloor(cfg), OState.Cfg.ph(cfg), info, view), ready, Nil{}}

def open.batch(r: List<&2, ONode.Node> & List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, ready: List<&2, ONode.Node>) -> OState.St & Maybe<&2, List<&2, ONode.Node>>:
  (merged, view0) = r
  +view = view0
  (open.at(cfg, t, info, view, Nat.is_gt(OFit.view_size(OState.Cfg.ph(cfg), info, view), OState.Cfg.floor(cfg)), ready), Some{merged})

def open.go(missed: Bool, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, shrink: Bool, ready: List<&2, ONode.Node>) -> OState.St & Maybe<&2, List<&2, ONode.Node>>:
  match missed:
    case False{}:
      (open.at(cfg, t, info, view, shrink, ready), None{})
    case True{}:
      open.batch(OFit.fit(OFit.Last{}, t, OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), info, view), cfg, t, info, ready)

# the chat as loaded, and the missed batch when there is one (the merges
# the last message's batch makes, as OStep.msg makes them: down to the
# floor, as far as built parents allow)
def open(+cfg: OState.Cfg, +t: List<&2, Bool>, +bs: List<&2, Built>, +view: List<&2, ONode.Node>, shrink: Bool, missed: Bool) -> OState.St & Maybe<&2, List<&2, ONode.Node>>:
  +info = info.of(bs, OInfo.Info.empty())
  open.go(missed, cfg, t, info, view, shrink, ready.of(bs, info, Nil{}))
