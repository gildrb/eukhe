# ffi_optchat: the stepper of the compiled Bend core for the chat's
# planner (crates/eukhe-core/src/memory/chat.rs): its state is the chat of
# bend/optchat/ (the sizes Cfg and the state St), kept in the Bend heap.
# The chat opens it from the loaded log, sends each event as it comes (a
# message, a node built, a call started or freed, a turn that starts to
# wait) and each query it needs (the nodes to start, a compaction's view,
# how many calls run), and does what each reply says. The codec is the
# wire format of bend/wire.bend (crates/eukhe-bend/WIRE.md):
#
#   open    Cfg (ph ceil floor cceil cfloor jobs), T, the built nodes
#           (List of l, k, size), the view (List of l, k), shrink: Bool,
#           missed: Bool                                 reply: Batch
#   step    Ev                                           reply: per event
#   Ev      0 a message                                  Batch
#           1 l, k, size: node built                     0,
#           2 l, k: its call started                     0,
#           3 l, k: its call is freed                    0,
#           4 a turn starts to wait                      the held nodes
#           5 the nodes to start                         nodes
#           6 the nodes to start while a turn waits      nodes
#           7 l, k: a compaction's view of the node      nodes
#           8 how many calls run                         Nat
#   Batch   0 none | 1 merged nodes, the view after, shrink: Bool
#   a node  l, k: node(l, k), k its index (bits of bend/optchat/ in
#           the model, a Nat on the wire)
#
# A malformed event, or one with input left over, answers the error form
# and keeps the chat; a malformed open opens the refused state, which
# answers every step with the error form. laws/optchat.bend pins the
# entry. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./optchat/bits.bend as OBits
import ./optchat/node.bend as ONode
import ./optchat/state.bend as OState
import ./optchat/step.bend as OStep
import ./optchat/queue.bend as OQueue
import ./optchat/ctx.bend as OCtx
import ./optchat/open.bend as OOpen

# The requests
# ------------

# an event or a query; a node is its level and its index
type Q is Data:
  QMsg{}
  QBuilt{l: Nat, k: Nat, size: Nat}
  QStart{l: Nat, k: Nat}
  QFree{l: Nat, k: Nat}
  QWait{}
  QCands{}
  QNeed{}
  QCtx{l: Nat, k: Nat}
  QBusy{}

# a built node of the open
type Got is Data:
  Got{l: Nat, k: Nat, size: Nat}

# a view line of the open
type Line is Data:
  Line{l: Nat, k: Nat}

# the open: the sizes, T, the built nodes, the view, shrink, missed
type Open is Data:
  Open{cfg: OState.Cfg, t: Nat, built: List<&2, Got>, view: List<&2, Line>, shrink: Bool, missed: Bool}

# the node a level and an index name
def node(l: Nat, k: Nat) -> ONode.Node:
  ONode.Node{l, OBits.Bits.of(k)}

# Decoders
# --------

def get_line.k(l: Nat, r: W.Dec<Nat>) -> W.Dec<Line>:
  match r:
    case W.Got{k, s}:
      W.Got{Line{l, k}, s}
    case W.Bad{}:
      W.Bad{}

def get_line.l(r: W.Dec<Nat>) -> W.Dec<Line>:
  match r:
    case W.Got{l, s}:
      get_line.k(l, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

# a node: l, k
def get_line(s: String) -> W.Dec<Line>:
  get_line.l(W.get_nat(s))

def get_got.size(n: Line, r: W.Dec<Nat>) -> W.Dec<Got>:
  match n r:
    case Line{l, k} W.Got{z, s}:
      W.Got{Got{l, k, z}, s}
    case Line{l, k} W.Bad{}:
      W.Bad{}

def get_got.node(r: W.Dec<Line>) -> W.Dec<Got>:
  match r:
    case W.Got{n, s}:
      get_got.size(n, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

# a built node: l, k, size
def get_got(s: String) -> W.Dec<Got>:
  get_got.node(get_line(s))

def get_ev.built(r: W.Dec<Got>) -> W.Dec<Q>:
  match r:
    case W.Got{g, s}:
      match g:
        case Got{l, k, z}:
          W.Got{QBuilt{l, k, z}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.start(r: W.Dec<Line>) -> W.Dec<Q>:
  match r:
    case W.Got{n, s}:
      match n:
        case Line{l, k}:
          W.Got{QStart{l, k}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.free(r: W.Dec<Line>) -> W.Dec<Q>:
  match r:
    case W.Got{n, s}:
      match n:
        case Line{l, k}:
          W.Got{QFree{l, k}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.ctx(r: W.Dec<Line>) -> W.Dec<Q>:
  match r:
    case W.Got{n, s}:
      match n:
        case Line{l, k}:
          W.Got{QCtx{l, k}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.tag(n: Nat, s: String) -> W.Dec<Q>:
  match n:
    case 0n:
      W.Got{QMsg{}, s}
    case 1n:
      get_ev.built(get_got(s))
    case 2n:
      get_ev.start(get_line(s))
    case 3n:
      get_ev.free(get_line(s))
    case 4n:
      W.Got{QWait{}, s}
    case 5n:
      W.Got{QCands{}, s}
    case 6n:
      W.Got{QNeed{}, s}
    case 7n:
      get_ev.ctx(get_line(s))
    case 8n:
      W.Got{QBusy{}, s}
    case 9n+p:
      W.Bad{}

def get_ev.go(r: W.Dec<Nat>) -> W.Dec<Q>:
  match r:
    case W.Got{n, s}:
      get_ev.tag(n, s)
    case W.Bad{}:
      W.Bad{}

# the event or query at the start of s
def get_ev(s: String) -> W.Dec<Q>:
  get_ev.go(W.get_nat(s))

def get_open.missed(c: OState.Cfg, t: Nat, bs: List<&2, Got>, vs: List<&2, Line>, sh: Bool, r: W.Dec<Bool>) -> W.Dec<Open>:
  match r:
    case W.Got{m, s}:
      W.Got{Open{c, t, bs, vs, sh, m}, s}
    case W.Bad{}:
      W.Bad{}

def get_open.shrink(c: OState.Cfg, t: Nat, bs: List<&2, Got>, vs: List<&2, Line>, r: W.Dec<Bool>) -> W.Dec<Open>:
  match r:
    case W.Got{sh, s}:
      get_open.missed(c, t, bs, vs, sh, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_open.view(c: OState.Cfg, t: Nat, bs: List<&2, Got>, r: W.Dec<List<&2, Line>>) -> W.Dec<Open>:
  match r:
    case W.Got{vs, s}:
      get_open.shrink(c, t, bs, vs, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_open.built(c: OState.Cfg, t: Nat, r: W.Dec<List<&2, Got>>) -> W.Dec<Open>:
  match r:
    case W.Got{bs, s}:
      get_open.view(c, t, bs, W.get_list(~Line, ~get_line, s))
    case W.Bad{}:
      W.Bad{}

def get_open.t(c: OState.Cfg, r: W.Dec<Nat>) -> W.Dec<Open>:
  match r:
    case W.Got{t, s}:
      get_open.built(c, t, W.get_list(~Got, ~get_got, s))
    case W.Bad{}:
      W.Bad{}

def get_cfg.jobs(a: Nat, b: Nat, c: Nat, d: Nat, e: Nat, r: W.Dec<Nat>) -> W.Dec<OState.Cfg>:
  match r:
    case W.Got{f, s}:
      W.Got{OState.Cfg{a, b, c, d, e, f}, s}
    case W.Bad{}:
      W.Bad{}

def get_cfg.cfloor(a: Nat, b: Nat, c: Nat, d: Nat, r: W.Dec<Nat>) -> W.Dec<OState.Cfg>:
  match r:
    case W.Got{e, s}:
      get_cfg.jobs(a, b, c, d, e, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_cfg.cceil(a: Nat, b: Nat, c: Nat, r: W.Dec<Nat>) -> W.Dec<OState.Cfg>:
  match r:
    case W.Got{d, s}:
      get_cfg.cfloor(a, b, c, d, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_cfg.floor(a: Nat, b: Nat, r: W.Dec<Nat>) -> W.Dec<OState.Cfg>:
  match r:
    case W.Got{c, s}:
      get_cfg.cceil(a, b, c, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_cfg.ceil(a: Nat, r: W.Dec<Nat>) -> W.Dec<OState.Cfg>:
  match r:
    case W.Got{b, s}:
      get_cfg.floor(a, b, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_cfg.ph(r: W.Dec<Nat>) -> W.Dec<OState.Cfg>:
  match r:
    case W.Got{a, s}:
      get_cfg.ceil(a, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

# the sizes: ph, ceil, floor, cceil, cfloor, jobs
def get_cfg(s: String) -> W.Dec<OState.Cfg>:
  get_cfg.ph(W.get_nat(s))

def get_open.cfg(r: W.Dec<OState.Cfg>) -> W.Dec<Open>:
  match r:
    case W.Got{c, s}:
      get_open.t(c, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

# the open at the start of s
def get_open(s: String) -> W.Dec<Open>:
  get_open.cfg(get_cfg(s))

# Encoders
# --------

# a node: its level, then its index
def put_node(n: ONode.Node, rest: String) -> String:
  match n:
    case ONode.Node{l, i}:
      W.put_nat(l, W.put_nat(OBits.Bits.val(i), rest))

def put_nodes(ns: List<&2, ONode.Node>, rest: String) -> String:
  W.put_list(~ONode.Node, ~put_node, ns, rest)

# a batch that ran: the merged nodes, the view after it, and whether it
# is still over its floor
def put_batch(merged: List<&2, ONode.Node>, +s: OState.St) -> String:
  W.put_nat(1n, put_nodes(merged, put_nodes(OState.St.view(s), W.put_bool(OState.St.shrink(s), ""))))

def put_none() -> String:
  W.put_nat(0n, "")

# The stepper
# -----------

# the chat with its sizes, or a refused open
type St is Data:
  Live{cfg: OState.Cfg, s: OState.St}
  Refused{}

def lines(vs: List<&2, Line>) -> List<&2, ONode.Node>:
  match vs:
    case Nil{}:
      Nil{}
    case Line{l, k} <> rest:
      node(l, k) <> lines(rest)

def gots(bs: List<&2, Got>) -> List<&2, OOpen.Built>:
  match bs:
    case Nil{}:
      Nil{}
    case Got{l, k, z} <> rest:
      OOpen.Built{node(l, k), z} <> gots(rest)

def open.answer(b: Maybe<&2, List<&2, ONode.Node>>, +s: OState.St) -> String:
  match b:
    case None{}:
      put_none()
    case Some{merged}:
      put_batch(merged, s)

def open.reply(+cfg: OState.Cfg, r: OState.St & Maybe<&2, List<&2, ONode.Node>>) -> St & String:
  (s0, b) = r
  +s = s0
  (Live{cfg, s}, open.answer(b, s))

def open.run(o: Open) -> St & String:
  match o:
    case Open{+cfg, t, bs, vs, sh, m}:
      open.reply(cfg, OOpen.open(cfg, OBits.Bits.of(t), gots(bs), lines(vs), sh, m))

def open.end(done: Bool, o: Open) -> St & String:
  match done:
    case True{}:
      open.run(o)
    case False{}:
      (Refused{}, W.err("optchat: malformed open"))

def open.go(d: W.Dec<Open>) -> St & String:
  match d:
    case W.Got{o, rest}:
      open.end(W.end(rest), o)
    case W.Bad{}:
      (Refused{}, W.err("optchat: malformed open"))

# open: the chat as loaded, and the missed batch, if one runs now
def open(input: String) -> St & String:
  open.go(get_open(input))

def fail() -> String:
  W.err("optchat: malformed event")

# a message: the batch it ran, if one ran (OStep.msg, its batch decided
# once)
def msg.answer(grow: Bool, merged: List<&2, ONode.Node>, +s: OState.St) -> String:
  match grow:
    case False{}:
      put_none()
    case True{}:
      put_batch(merged, s)

def msg.reply(grow: Bool, r: OState.St & List<&2, ONode.Node>, +cfg: OState.Cfg) -> St & String:
  (s0, merged) = r
  +s = s0
  (Live{cfg, s}, msg.answer(grow, merged, s))

def msg.go(+grow: Bool, +cfg: OState.Cfg, +s: OState.St) -> St & String:
  msg.reply(grow, OStep.msg.go(grow, cfg, OBits.Bits.inc(OState.St.t(s)), OState.St.info(s), OStep.St.grown(s), List.append(&2, ONode.Node, OState.St.cview(s), [ONode.Node.leaf(OState.St.t(s))]), OState.St.ready(s), OState.St.busy(s)), cfg)

def done(+cfg: OState.Cfg, r: OState.St & List<&2, ONode.Node>) -> St & String:
  (s, b) = r
  (Live{cfg, s}, put_none())

# one event or query, whole: the chat after it and the reply
def serve(+cfg: OState.Cfg, +s: OState.St, q: Q) -> St & String:
  match q:
    case QMsg{}:
      msg.go(OStep.St.batch(cfg, s), cfg, s)
    case QBuilt{l, k, z}:
      done(cfg, OStep.step(cfg, s, OState.Build{node(l, k), z}))
    case QStart{l, k}:
      done(cfg, OStep.step(cfg, s, OState.Start{node(l, k)}))
    case QFree{l, k}:
      done(cfg, OStep.step(cfg, s, OState.Free{node(l, k)}))
    case QWait{}:
      (Live{cfg, OQueue.St.wait(s)}, put_nodes(OQueue.St.held(s), ""))
    case QCands{}:
      (Live{cfg, s}, put_nodes(OQueue.cands(cfg, s), ""))
    case QNeed{}:
      (Live{cfg, s}, put_nodes(OQueue.cands.need(cfg, s), ""))
    case QCtx{l, k}:
      (Live{cfg, s}, put_nodes(OCtx.ctx(s, node(l, k)), ""))
    case QBusy{}:
      (Live{cfg, s}, W.put_nat(List.length(&2, ONode.Node, OState.St.busy(s)), ""))

def step.end(done: Bool, +cfg: OState.Cfg, +s: OState.St, q: Q) -> St & String:
  match done:
    case True{}:
      serve(cfg, s, q)
    case False{}:
      (Live{cfg, s}, fail())

def step.ev(+cfg: OState.Cfg, +s: OState.St, d: W.Dec<Q>) -> St & String:
  match d:
    case W.Got{q, rest}:
      step.end(W.end(rest), cfg, s, q)
    case W.Bad{}:
      (Live{cfg, s}, fail())

# step: one event or query; the reply says what the chat does
def step(st: St, input: String) -> St & String:
  match st:
    case Live{cfg, s}:
      step.ev(cfg, s, get_ev(input))
    case Refused{}:
      (Refused{}, W.err("optchat: the open was refused"))
