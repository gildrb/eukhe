# optchat: the chat's configuration, state and events (Cfg, St, Ev)

import Base
import ./node.bend as ONode
import ./info.bend as OInfo

# The chat
# --------
# The sizes: ph bytes for a line not summarized yet; the view's sawtooth
# from ceil down to floor (gist §3.2); the compaction view's from cceil
# down to cfloor (gist §4); jobs calls at once (gist §4).

type Cfg is Data:
  Cfg{ph: Nat, ceil: Nat, floor: Nat, cceil: Nat, cfloor: Nat, jobs: Nat}

def Cfg.ph(c: Cfg) -> Nat:
  match c:
    case Cfg{ph, ce, fl, cc, cf, j}:
      ph

def Cfg.ceil(c: Cfg) -> Nat:
  match c:
    case Cfg{ph, ce, fl, cc, cf, j}:
      ce

def Cfg.floor(c: Cfg) -> Nat:
  match c:
    case Cfg{ph, ce, fl, cc, cf, j}:
      fl

def Cfg.cceil(c: Cfg) -> Nat:
  match c:
    case Cfg{ph, ce, fl, cc, cf, j}:
      cc

def Cfg.cfloor(c: Cfg) -> Nat:
  match c:
    case Cfg{ph, ce, fl, cc, cf, j}:
      cf

def Cfg.jobs(c: Cfg) -> Nat:
  match c:
    case Cfg{ph, ce, fl, cc, cf, j}:
      j

# the gist's sizes; the placeholder is "(not summarized yet: zoom it)"
def Cfg.gist() -> Cfg:
  Cfg{29n, 128000n, 64000n, 32000n, 16000n, 8n}

# T (in binary), the built nodes, the view, whether a batch is still
# shrinking it, the compaction view, the ready merges (by level, then
# index) and the nodes being built
type St is Data:
  St{t: List<&2, Bool>, info: OInfo.Info, view: List<&2, ONode.Node>, shrink: Bool, cview: List<&2, ONode.Node>, ready: List<&2, ONode.Node>, busy: List<&2, ONode.Node>}

def St.empty() -> St:
  St{Nil{}, OInfo.Info.empty(), Nil{}, False{}, Nil{}, Nil{}, Nil{}}

def St.t(s: St) -> List<&2, Bool>:
  match s:
    case St{t, info, view, shrink, cview, ready, busy}:
      t

def St.info(s: St) -> OInfo.Info:
  match s:
    case St{t, info, view, shrink, cview, ready, busy}:
      info

def St.view(s: St) -> List<&2, ONode.Node>:
  match s:
    case St{t, info, view, shrink, cview, ready, busy}:
      view

def St.shrink(s: St) -> Bool:
  match s:
    case St{t, info, view, shrink, cview, ready, busy}:
      shrink

def St.cview(s: St) -> List<&2, ONode.Node>:
  match s:
    case St{t, info, view, shrink, cview, ready, busy}:
      cview

def St.ready(s: St) -> List<&2, ONode.Node>:
  match s:
    case St{t, info, view, shrink, cview, ready, busy}:
      ready

def St.busy(s: St) -> List<&2, ONode.Node>:
  match s:
    case St{t, info, view, shrink, cview, ready, busy}:
      busy

# What happens to the chat: a message is logged; a node is built (s
# bytes); a node's call starts; a call fails (its node may start again).
type Ev is Data:
  Msg{}
  Build{n: ONode.Node, size: Nat}
  Start{n: ONode.Node}
  Free{n: ONode.Node}
