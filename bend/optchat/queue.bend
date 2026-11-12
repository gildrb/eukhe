# optchat: the work queue: which nodes start now, under the due mark, and what a waiting turn keeps

import Base
import ./bits.bend as OBits
import ./node.bend as ONode
import ./info.bend as OInfo
import ./state.bend as OState

# The work queue
# --------------
# A message's node starts once fewer than jobs lines before it are still
# unbuilt; a merge starts once both its halves are built (it is ready).
# At most jobs calls run at once (gist §4).

def cand.emit(stop: Bool, built: Bool, free: Bool, +h: ONode.Node, rec: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match stop built free:
    case True{} _ _:
      Nil{}
    case False{} True{} _:
      rec
    case False{} False{} True{}:
      h <> rec
    case False{} False{} False{}:
      rec

# the view's unbuilt lines that may start: unb unbuilt lines seen, room
# free slots left
def cand.view(v: List<&2, ONode.Node>, +info: OInfo.Info, +busy: List<&2, ONode.Node>, +jobs: Nat, +unb: Nat, room: Nat) -> List<&2, ONode.Node>:
  match v room:
    case Nil{} _:
      Nil{}
    case h <> rest 0n:
      Nil{}
    case +h <> rest 1n+r:
      +built = OInfo.Info.built(info, h)
      +free = Bool.not(ONode.Nodes.has(busy, h))
      cand.emit(Nat.is_ge(unb, jobs), built, free, h, cand.view(rest, info, busy, jobs, Nat.add(unb, OBits.bit(Bool.not(built), 0n)), Nat.sub(1n+r, OBits.bit(Bool.and(Bool.not(built), free), 0n))))

def cand.ready(rs: List<&2, ONode.Node>, +busy: List<&2, ONode.Node>, room: Nat) -> List<&2, ONode.Node>:
  match rs room:
    case Nil{} _:
      Nil{}
    case h <> rest 0n:
      Nil{}
    case +h <> rest 1n+r:
      +free = Bool.not(ONode.Nodes.has(busy, h))
      ONode.Nodes.keep(free, h, cand.ready(rest, busy, Nat.sub(1n+r, OBits.bit(free, 0n))))

def cands.with(+s: OState.St, +room: Nat, c0: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  +c = c0
  List.append(&2, ONode.Node, c, cand.ready(OState.St.ready(s), OState.St.busy(s), Nat.sub(room, List.length(&2, ONode.Node, c))))

# the nodes to start now, oldest message first, then the ready merges
def cands(+cfg: OState.Cfg, +s: OState.St) -> List<&2, ONode.Node>:
  +room = Nat.sub(OState.Cfg.jobs(cfg), List.length(&2, ONode.Node, OState.St.busy(s)))
  cands.with(s, room, cand.view(OState.St.view(s), OState.St.info(s), OState.St.busy(s), OState.Cfg.jobs(cfg), 0n, room))

# the nodes to start while a turn waits for the view: the view's unbuilt
# lines only, oldest first; the ready merges wait (laws/compactor.bend H2.1, R14)
def cands.need(+cfg: OState.Cfg, +s: OState.St) -> List<&2, ONode.Node>:
  cand.view(OState.St.view(s), OState.St.info(s), OState.St.busy(s), OState.Cfg.jobs(cfg), 0n, Nat.sub(OState.Cfg.jobs(cfg), List.length(&2, ONode.Node, OState.St.busy(s))))

# The due mark
# ------------
# A line is built once a request may show it, never before: a root turn's
# request shows the view lines that start before end = T - V (the history
# that scrolled out of its transcript, bend/thread.bend), a subagent's the
# whole view. The chat keeps the largest end a request asked for, its due
# mark, and the queue reads the chat cut to it: the view's leading lines
# that start before the mark and the ready merges that start before it.
# While everything still fits in the transcript, the mark stays 0 and no
# call runs.

def lines.keep(go: Bool, +h: ONode.Node, rec: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match go:
    case False{}:
      Nil{}
    case True{}:
      h <> rec

# the leading lines of v that start before due
def lines.before(+due: Nat, v: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match v:
    case Nil{}:
      Nil{}
    case +h <> rest:
      lines.keep(Nat.is_lt(ONode.Node.start(h), due), h, lines.before(due, rest))

# the nodes of ns that start before due, in their order
def nodes.before(+due: Nat, ns: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match ns:
    case Nil{}:
      Nil{}
    case +h <> rest:
      ONode.Nodes.keep(Nat.is_lt(ONode.Node.start(h), due), h, nodes.before(due, rest))

# the chat as the queue reads it under the due mark
def St.due(+due: Nat, s: OState.St) -> OState.St:
  match s:
    case OState.St{t, info, view, shrink, cview, ready, busy}:
      OState.St{t, info, lines.before(due, view), shrink, cview, nodes.before(due, ready), busy}

# the nodes to start now under the due mark
def cands.due(+cfg: OState.Cfg, +s: OState.St, +due: Nat) -> List<&2, ONode.Node>:
  cands(cfg, St.due(due, s))

# the nodes to start while a turn waits, under the due mark
def cands.need.due(+cfg: OState.Cfg, +s: OState.St, +due: Nat) -> List<&2, ONode.Node>:
  cands.need(cfg, St.due(due, s))

# the busy nodes that are view lines still unbuilt
def busy.need(+info: OInfo.Info, +v: List<&2, ONode.Node>, bs: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> rest:
      ONode.Nodes.keep(Bool.and(ONode.Nodes.has(v, b), Bool.not(OInfo.Info.built(info, b))), b, busy.need(info, v, rest))

# a turn starts to wait: every call of a node it does not need stops, and
# the node goes back to the queue (laws/compactor.bend H2.1, R14)
def St.wait(s: OState.St) -> OState.St:
  match s:
    case OState.St{t, +info, +view, shrink, cview, ready, busy}:
      OState.St{t, info, view, shrink, cview, ready, busy.need(info, view, busy)}

# the busy nodes that are not view lines still unbuilt: the calls a
# waiting turn stops
def busy.held(+info: OInfo.Info, +v: List<&2, ONode.Node>, bs: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> rest:
      ONode.Nodes.keep(Bool.not(Bool.and(ONode.Nodes.has(v, b), Bool.not(OInfo.Info.built(info, b)))), b, busy.held(info, v, rest))

# the calls St.wait stops
def St.held(s: OState.St) -> List<&2, ONode.Node>:
  match s:
    case OState.St{t, +info, +view, shrink, cview, ready, busy}:
      busy.held(info, view, busy)
